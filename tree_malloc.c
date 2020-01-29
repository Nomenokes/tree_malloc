#include <stdlib.h>
#include <time.h>
#include <stdio.h>
#include <stdbool.h>
#include <string.h>
#include <assert.h>
#include <pthread.h>
#include <sys/mman.h>
#include <math.h>


//
// Constants and structs
//

// Locking rules to prevent deadlocks: 
// - Cannot hold more than 1 bucket lock at a time
// - Cannot attempt to take a bucket lock if holding the free-list lock
//	 - Can attempt to take the free-list lock if holding a bucket lock
// - Can attempt to take the free-list lock if holding no locks
// - Can attempt to take a bucket lock if holding no locks
static const size_t PAGE_SIZE = 4096;
static const char PAGE_BSIZE = 12;
static const char MEM_PAGE_PAGES = 5;
static const char MEM_PAGE_TREE_DEF_SIZE = PAGE_BSIZE + 2;//PAGE_SIZE * (MEM_PAGE_PAGES - 1)
static const size_t MEM_PAGE_HEADER_SIZE = 2 * sizeof(void*);
#define NUM_BUCKETS 64 //static const size_t NUM_BUCKETS

typedef struct mem_tree {
	char bsize;//actual size 2^size - sizeof(mem_tree) bytes
	char bucket;
	bool used;
	bool left;
} mem_tree;

typedef struct mem_page {//unsorted
	struct mem_page* next;
	struct mem_page* prev;
	mem_tree tree;
} mem_page;

typedef struct free_page {
	struct free_page* next;
	struct free_page* prev;
	char pages;//num pages
} free_page;

typedef struct global_freelist {
	free_page* head;
	pthread_mutex_t mutex;
	bool sorted;//sorts if a memory > 1 page is requested
	long allocated;
	long large_allocated;
	long freed;
} global_freelist;

typedef struct bucket {
	pthread_mutex_t mutex;
	mem_page* head;
} bucket;

//
// Global vars
//

static bucket buckets[NUM_BUCKETS];
static global_freelist free_pages;

static __thread char preferred_bucket = -1; // initialized to -1 to make sure it is randomly assigned on first malloc 

//
// Utility functions
//

static void* shift_ptr(void* ptr, size_t size){
	return ((char*)ptr) + size;
}
static size_t div_up(size_t xx, size_t yy) {
    // This is useful to calculate # of pages
    // for large allocations.
    size_t zz = xx / yy;

    if (zz * yy == xx) {
        return zz;
    }
    else {
        return zz + 1;
    }
}
//how much memory you need to request from the bucket if the user wants size
static char tree_size(size_t size){
	size += sizeof(mem_tree);
	return (char)ceil(log2(size));
}
//how much memory you need to request from the global freelist, if you want to put a header in front
static char page_size(size_t size, size_t header){
	size += header;
	size_t ret = div_up(size, PAGE_SIZE);
	if(ret > 127) abort();//too many pages requested for this model, have to redesign memory data storage. Probably just shift around mem_tree fields and use bucket to flag if multiple pages.
	return ret;
}

//
// Global freelist functions and helpers
//

static void shave_free_page(free_page* page, size_t pages){
	free_page* temp = page->next;
	page->next = (free_page*)shift_ptr(page, pages * PAGE_SIZE);
	page->next->next = temp;
	page->next->prev = page;
	if(temp) temp->prev = page->next;
	page->next->pages = page->pages - pages;
	page->pages = pages;
}
static void remove_free_page(free_page* page){
	if(page->prev) page->prev->next = page->next;
	else free_pages.head = page->next;
	if(page->next) page->next->prev = page->prev;
}
static free_page* search_free_list_r(free_page* head, size_t pages){
	if(!head) return 0;
	if(head->pages >= pages) return head;
	return search_free_list_r(head->next, pages);
}
//For now, this does not sort for performance, opting to mmap more pages for huge allocations
static void sort_free_list(){
}
static free_page* map_pages(size_t pages){
	free_page* ret = (free_page*)mmap(0, pages * PAGE_SIZE, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANONYMOUS, -1, 0);
	assert(ret);
	return ret;
}
static mem_page* global_request_page(){//initializes all values except for bucket
	assert(! pthread_mutex_lock(&(free_pages.mutex)) );
	
	free_page* fret;
	if(free_pages.head){
		assert(free_pages.head->pages >= MEM_PAGE_PAGES);//should only have large free pages on the list
		if(free_pages.head->pages > MEM_PAGE_PAGES){
			shave_free_page(free_pages.head, MEM_PAGE_PAGES);
		}
		fret = free_pages.head;
		remove_free_page(fret);
	} else {
		fret = map_pages(MEM_PAGE_PAGES);
	}
	assert(! pthread_mutex_unlock(&(free_pages.mutex)) );
	
	mem_page* ret = (mem_page*)fret;
	ret->next = 0;
	ret->prev = 0;
	ret->tree.bsize = MEM_PAGE_TREE_DEF_SIZE;
	ret->tree.used = false;
	ret->tree.left = true;
	free_pages.allocated++;
	
	return ret;
}
static free_page* global_request_pages(size_t pages){
	assert(! pthread_mutex_lock(&(free_pages.mutex)) );
	
	free_page* ret = 0;
	if(free_pages.head){
		if(free_pages.head->pages >= pages){
			if(free_pages.head->pages > pages){
				shave_free_page(free_pages.head, pages);
			}
			ret = free_pages.head;
			remove_free_page(ret);
		}else{
			if(!free_pages.sorted){
				sort_free_list();
			}
			ret = search_free_list_r(free_pages.head, pages);
			if(!ret) ret = map_pages(pages);
			ret->pages = pages;
		}
	}
	free_pages.large_allocated++;
	
	assert(! pthread_mutex_unlock(&(free_pages.mutex)) );
	return ret;
}
static void global_return_page(void* element, size_t pages){
	assert(! pthread_mutex_lock(&(free_pages.mutex)) );

	free_page* fp = (free_page*)element;
	fp->pages = pages;
	fp->next = free_pages.head;
	if(free_pages.head) free_pages.head->prev = fp;
	fp->prev = 0;
	free_pages.head = fp->next;
	free_pages.sorted = false;
	free_pages.freed++;
	
	assert(! pthread_mutex_unlock(&(free_pages.mutex)) );
}

//
// Bucket functions and helpers
//

//also sets the preferred bucket number
static void bucket_lock(){
	const int TRYNUM = 3;
	if(preferred_bucket == -1){
		srand(time(0));
		preferred_bucket = rand() % NUM_BUCKETS; 
	}
	
	int stop = (preferred_bucket + TRYNUM) % NUM_BUCKETS;
	for(int i = preferred_bucket; i != stop; i = (i + 1) % NUM_BUCKETS){
		if(!pthread_mutex_trylock(&(buckets[i].mutex))){
			preferred_bucket = i;
			return;
		}
	}
	
	preferred_bucket = stop;
	assert(! pthread_mutex_lock(&(buckets[stop].mutex)) );
}
static void bucket_unlock(){
	assert(! pthread_mutex_unlock(&(buckets[preferred_bucket].mutex)) );
}
static void split_tree_r(mem_tree* tree, char splits){
	if(splits <= 0) return;
	
	tree->bsize--;
	tree->left = true;
	
	mem_tree* right = (mem_tree*)shift_ptr(tree, 1 << (tree->bsize));
	right->bsize = tree->bsize;
	right->bucket = tree->bucket;
	right->used = false;
	right->left = false;
	
	split_tree_r(tree, splits - 1);
	//split_tree_r(ret, splits - 1);
}
//requires that preferred_bucket is locked
static mem_tree* bucket_get(char bsize){
	mem_page* working = buckets[preferred_bucket].head;
	if(!working){//get a new mem_page if bucket is empty
		working = global_request_page();
		working->tree.bucket = preferred_bucket;
		buckets[preferred_bucket].head = working;
	}
	size_t size = 1 << bsize;
	while(true){
		mem_tree* working_tree = &(working->tree);
		void* stop = shift_ptr(working_tree, (1 << MEM_PAGE_TREE_DEF_SIZE) - size);
		while((void*)working_tree <= stop){//loop until tree pointer exceeds page size
			if(working_tree->bsize < bsize){//if tree is too small, increase by goal size
				working_tree = (mem_tree*)shift_ptr(working_tree, size);
			} 
			else if(working_tree->used){//else if tree is used, increase by tree size
				working_tree = (mem_tree*)shift_ptr(working_tree, 1 << working_tree->bsize);
			}
			else{//else split tree into size chunks, take the first, return
				split_tree_r(working_tree, working_tree->bsize - bsize);
				assert(working_tree->bsize == bsize);
				working_tree->used = true;
				return working_tree;
			}
		}
		
		if(!working->next){//get a new mem_page if previous one is full
			working->next = global_request_page();
			working->next->tree.bucket = preferred_bucket;
			working->next->prev = working;
		}
		working = working->next;
	}
}
//requires that elt's bucket is locked
static void bucket_return(mem_tree* elt){
	elt->used = false;
	if(elt->bsize >= MEM_PAGE_TREE_DEF_SIZE){
		global_return_page(shift_ptr(elt, -MEM_PAGE_HEADER_SIZE), MEM_PAGE_PAGES);
	}
	else if(elt->left){
		mem_tree* right = (mem_tree*)shift_ptr(elt, 1 << (elt->bsize));
		if(!right->used && right->bsize == elt->bsize){
			elt->bsize++;//absorb right
			bucket_return(elt);//coalesce next level
		}
	}
	else{
		mem_tree* left = (mem_tree*)shift_ptr(elt, -(1 << (elt->bsize)));
		if(left->bsize == elt->bsize){
			left->bsize++;//merge into left
			if(!left->used) bucket_return(left);//coalesce next level
		}
	}
}

//
// Internal malloc/free
//

static void* internal_malloc(size_t size){
	char tsize = tree_size(size);
	mem_tree* element;
	if(tsize > MEM_PAGE_TREE_DEF_SIZE){
		free_page* page = global_request_pages(page_size(size, sizeof(mem_tree)));
		element = (mem_tree*)page; 
		element->bsize = -page->pages;
		element->bucket = preferred_bucket;
		element->used = true;
		element->left = true;
	}else{
		element = bucket_get(tsize);
	}
	return shift_ptr(element, sizeof(mem_tree));
}
static void internal_free(void* p){
	mem_tree* element = (mem_tree*)shift_ptr(p, -sizeof(mem_tree));
	if(element->bsize > MEM_PAGE_TREE_DEF_SIZE){
		global_return_page(shift_ptr(element, -MEM_PAGE_HEADER_SIZE), -element->bsize);
	}else{
		assert(! pthread_mutex_lock(&(buckets[element->bucket].mutex)) );
		bucket_return(element);
		assert(! pthread_mutex_unlock(&(buckets[element->bucket].mutex)) );
	}
}

//
// Public malloc/free
//

void* tree_malloc(size_t size){
	bucket_lock();
	void* ret = internal_malloc(size);
	bucket_unlock();
	return ret;
}
void tree_free(void* p){
	assert(p);
	internal_free(p);
}
