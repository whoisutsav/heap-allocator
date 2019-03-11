#include <stdlib.h>
#include <stdint.h>

unsigned int heap_size, offset;
char * heap_start = NULL;

/*@ requires \valid((char *) heap_start+ (0..(heap_size-1)));
	requires 0 < offset < heap_size;
	requires offset + size <= UINT_MAX; // Proof will fail without this 
	behavior fits:
		assumes (offset + size) >= heap_size; // Based on real arithmetic (i.e. not machine arithmetic)   
		ensures \result == \null;
		assigns \nothing;
	behavior does_not_fit:
		assumes (offset + size) < heap_size;
		assigns offset;
		ensures \result == (char *) heap_start + \old(offset);
	complete behaviors fits, does_not_fit;
	disjoint behaviors fits, does_not_fit;
 */
char * vmalloc(size_t size) { 
	if ((offset + size) >= heap_size) {
		return NULL;
	} else {
		offset += size;
		return heap_start + (offset - size);
	}
}

void vfree(void * ptr) {
	// Do nothing.
}

void init(size_t size) {
	heap_start = malloc(size);	
	heap_size = size;
	offset = 0;
}
