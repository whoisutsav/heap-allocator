#include <stdio.h>
#include <stdlib.h>
#include <limits.h>
#include "allocator.h"

#define HEAP_SIZE 4096 

typedef struct {
  size_t info;
  void * empty; // Used to align header to 16 bytes
} header_t;

char * heap_start = NULL;

int is_allocated(header_t * h) {
	return h->info & 1;	
}

void mark_allocated(header_t * h) {
	h->info = h->info | 1;
}

void mark_free(header_t * h) {
	size_t mask = 0;
	h->info = (~mask ^ 1) & h->info;   
}

unsigned long get_size(header_t * h) {
	size_t mask = 0;
	return ((~mask ^ 15) & h->info);
}

void mark_size(header_t * h, size_t size) {
	size_t mask = 0;
	h->info = size | (15 & h->info);
}

// Returns pointer to newly created block
void * split_block(header_t * h, size_t size) {
	size_t new_size = get_size(h) - size - 16;
	h->info = size | 1;
	(h + 1 + (size/16))->info = new_size;
	return h+1;
}

int terminating_block(header_t * h) {
	return is_allocated(h) && get_size(h) == 0;
}

int valid_heap(char * heap_start) {
	return 1;
}

void * vmalloc(char * heap_start, size_t size) { // Assume size is multiple of 16 bytes, for ease of verification 
	if (size <= 0) return NULL;
	header_t * h = (header_t *) heap_start;
	while (!terminating_block(h)) {
		if(!is_allocated(h) && get_size(h) > size) 
			return split_block(h, size);
		else
		   	h += (1 + (get_size(h)/16));
	}
	
	return NULL;
}

// No coalescing as of now
void vfree(void * ptr) {
	mark_free(ptr);
}

void init() {
	if (heap_start != NULL) //already initialized?
		return;		

   	heap_start = malloc(sizeof(char) * HEAP_SIZE); 
	mark_size((header_t *) heap_start, HEAP_SIZE - 32);
	mark_free((header_t *) heap_start);

	// Mark terminating block
	mark_size((header_t *) (heap_start + (HEAP_SIZE - 16)), 0);
	mark_allocated((header_t *) (heap_start + (HEAP_SIZE - 16)));
}

void print_debug(header_t * start) {
	printf("-----------Traversing Free List-----------\n");
	header_t * h = (header_t *) heap_start;
	int i=0;
	while(!(is_allocated(h) && get_size(h) ==0)) { // Need to account for terminating block
		printf("Block %d at location %p\n", i, h);
		printf("Block size: %lu\n", get_size(h));
		printf("Allocated: %d\n\n", is_allocated(h));
		i++;
		h += (1 + (get_size(h)/16));
	}	
	// print terminating block
	printf("Block %d at location %p\n", i, h);
	printf("Block size: %lu\n", get_size(h));
	printf("Allocated: %d\n\n", is_allocated(h));
}

int main(int argc, char * argv[]) {
	init();
	int block_size;
	for (int i=0; i<10; i++) {
		block_size = ((rand() % 9) + 1) * 16;	
		//vmalloc(heap_start, block_size);
		printf("Allocated %d bytes\n", block_size);
	}
	//vfree(heap_start);
	//print_debug((header_t *) heap_start);
	return 0;
}

