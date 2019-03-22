#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

// Global variable is used instead of define, which allows value to be used in annotations 
const int HEAP_SIZE = 4096;

typedef struct {
  unsigned int info;
  void * empty; // Used to align header to 16 bytes
} header_t;

header_t * heap_start = NULL;

/*@ logic integer _get_size(header_t * h) =
	((h->info >> 4) << 4);	
*/

// TODO - remove?
/*@
	inductive valid{L} (header_t * start) {
	case initial_valid{L}:
	\forall header_t * start; valid(start);
	case next_reachable{L}:
	\forall header_t * h;
	valid(h) ==>
	valid((header_t *) (h + (_get_size(h)/16)));
}
*/

/*@ predicate _lsb_set(unsigned int i) = 
	(unsigned int) (i & ((unsigned int) 1)) > (unsigned int) 0;		
*/

/*@ lemma _lsb_not_set:
	\forall unsigned int x; !_lsb_set((unsigned int) (((unsigned int) (~0 ^ 1)) & x)); 
*/

/*@ lemma bit_or_rshift_dist:
        \forall unsigned int x, y; \forall unsigned int a; (((x|y)>>a) == ((x>>a)|(y>>a)));
    lemma bit_or_lshift_dist:
        \forall unsigned int x, y; \forall integer a; ((x|y)<<a) == ((x<<a)|(y<<a));
    lemma bit_shift_unshift:
        \forall unsigned int x; \forall integer a; (((x>>a)<<a)>>a) == (x>>a);
    lemma bit_successive_shift:
        \forall unsigned int x; \forall integer a, b; (((x>>a)>>b) == (x>>(a + b)));
    lemma bit_total_shift:
        \forall unsigned int x; (x >> 32) ==  0;
*/

/*@ requires \valid(h);
	behavior allocated:
		assumes _lsb_set(h->info);
		ensures \result > 0;
		ensures \valid(h);
	behavior not_allocated:
		assumes !_lsb_set(h->info);
		ensures \result == 0;
		ensures \valid(h);
	disjoint behaviors;
	complete behaviors;
*/
unsigned int is_allocated(header_t * h) {
	return h->info & (unsigned int) 1;	
}

/*@ requires \valid(h);
	ensures _lsb_set(h->info);
	ensures \valid(h);
*/
void mark_allocated(header_t * h) {
	h->info = h->info | 1;
}

/*@ requires \valid(h);
	ensures !_lsb_set(h->info);
	ensures \valid(h);
*/
void mark_free(header_t * h) {
	h->info = (~0 ^ 1) & h->info;   
}

/*@ requires \valid(h);
	ensures \result == (unsigned int) _get_size(h);
	ensures \valid(h);
*/
unsigned int get_size(header_t * h) {
	return (h->info >> 4) << 4;
}

/*@ requires \valid(h);
	requires h->info % 16 == 0;
	ensures _get_size(h) == size;
	ensures \valid(h);
*/
void mark_size(header_t * h, unsigned int size) {
	h->info = ((h->info << 28) >> 28) | ((size >> 4) << 4);
}

/*@ requires \valid(h+ (0..((size/16)+1)));
	requires size > 0;
	requires size <= _get_size(h);
	behavior fills_entire_block:
		assumes _get_size(h) == size;
	behavior splits_block:
		assumes _get_size(h) < size;
		assigns ((header_t*) (h + 1 + (size/16)))->info; 
	ensures _lsb_set(h->info);
	ensures _get_size(h) == size;
	ensures \valid(h + 1 + (size/16));
	ensures \result == (header_t *) h + 1;
	ensures \valid(\result);
*/
header_t * split_block(header_t * h, unsigned int size) {
	if (get_size(h) > size) (h + 1 + (size/16))->info = get_size(h) - size - 16;
	h->info = size;
	mark_allocated(h);
	return h+1;
}

/*@ requires \valid(h);
 	ensures \result <==> _lsb_set(h->info) && (_get_size(h) == 0); 
	ensures \valid(h);
*/
int terminating_block(header_t * h) {
	return is_allocated(h) && (get_size(h) == 0);
}

/*@ requires \valid(heap_start+ (0..(HEAP_SIZE/16)));
	requires size % 16 == 0;
 */
void * vmalloc(header_t * heap_start, unsigned int size) { // Size required to be multiple of 16 
	if (size <= 0) return NULL;
	header_t * h = heap_start;
	/*@ loop invariant \valid(h);
		loop invariant size > 0;
	*/
	while (!terminating_block(h)) {
		if(!is_allocated(h) && get_size(h) > size) 
			return split_block(h, size);
		else
		   	h += (1 + (get_size(h)/16));
	}
	
	return NULL;
}

/*@ requires \valid(ptr);
	ensures \valid(ptr);
*/
void vfree(header_t * ptr) {
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
	//printf("-----------Traversing Free List-----------\n");
	header_t * h = (header_t *) heap_start;
	int i=0;
	while(!(is_allocated(h) && get_size(h) ==0)) { // Need to account for terminating block
		//printf("Block %d at location %p\n", i, h);
		//printf("Block size: %lu\n", get_size(h));
		//printf("Allocated: %d\n\n", is_allocated(h));
		i++;
		h += (1 + (get_size(h)/16));
	}	
	// print terminating block
	//printf("Block %d at location %p\n", i, h);
	//printf("Block size: %lu\n", get_size(h));
	//printf("Allocated: %d\n\n", is_allocated(h));
}

int main(int argc, char * argv[]) {
	init();
	unsigned int block_size;
	for (int i=0; i<10; i++) {
		block_size = ((rand() % 9) + 1) * 16;	
		vmalloc(heap_start, block_size);
		printf("Allocated %u bytes\n", block_size);
	}
	printf("\n");
	vfree(heap_start);
	printf("\n");
	print_debug((header_t *) heap_start);
	return 0;
}

