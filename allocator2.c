#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

// Using global value (instead of #define) allows value to be used in logical annotations 
// Sizes are in 16-byte chunks for simplicity (so true size is HEAP_SIZE * 16 bytes)
const int HEAP_SIZE = 256;

typedef struct {
  unsigned int info;
  void * empty; // Unused, pads header_t to size of 16 bytes
} header_t;

header_t * heap_start = NULL;

/*@ lemma bit_shift_bounded:
		\forall unsigned int x; (0 <= x < UINT_MAX/16) ==>
			(((x << 4) >> 4) == x);
*/

/*@ logic integer _get_size(unsigned int x) =
		(x >> 4);	
*/

/*@ requires \valid(h);
	ensures \result == _get_size(h->info);
	assigns \nothing;
*/
unsigned int get_size(header_t * h) {
	return (h->info >> 4);
}


/*@ predicate _lsb_set(unsigned int i) = 
	(i & 1) == 1;		
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



/*@ predicate _terminating(header_t * h) = 
		_lsb_set(h->info) && !_get_size(h->info);
*/

/*@
	inductive reachable{L} (header_t* start, header_t* h) {
	case start_reachable{L}:
		\forall header_t* start; reachable(start,start);
	case next_reachable{L}:
		\forall header_t* start, *h; reachable((header_t *) (start + 1 + _get_size(start->info)), h) ==>
		reachable(start,h);
}
*/

/*@	lemma reachable_trans:
	\forall header_t *start, *h;
	reachable(start, h) && \valid(h) ==> reachable(start, (h + 1 + _get_size(h->info)));	
*/ 

/*@	lemma reachable_size_gt:
	\forall header_t *start, *h;
	reachable(start, h) && \valid(h) ==> 
		_get_size(h->info) > 0 || _terminating(h);	
*/ 

/*@ predicate finite{L}(header_t * start) = 
		\forall header_t * start; \exists header_t * h; reachable(start, h) && _terminating(h);
*/

/*@ predicate well_formed{L}(header_t * start) =
		\forall header_t *start, *h; reachable(start, h) ==>
			\valid(h) && h \in (start+ (0..HEAP_SIZE));
*/

/*@ lemma size_gt:
	\forall header_t * h; \forall unsigned int size; (_get_size(h->info) > size) ==>
		\valid(h+ (0..(size+1)));
*/

/*@ lemma non_terminating_block:
		\forall header_t *start, *h; (reachable(start, h) && !_terminating(h)) ==> \valid(h + 1 + _get_size(h->info));
*/

/*@ requires \valid(h);
	assigns \nothing;
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
	assigns h->info;
*/
void mark_allocated(header_t * h) {
	h->info = h->info | 1;
}

/*@ requires \valid(h);
	ensures !_lsb_set(h->info);
	ensures \valid(h);
	ensures h == \old(h);
*/
void mark_free(header_t * h) {
	h->info = (~0 ^ 1) & h->info;   
}

/*@ requires \valid(h);
	requires 0 < size < UINT_MAX/16;
	ensures (unsigned int) (h->info >> 4) == size;
	ensures \valid(h);
	ensures h == \old(h);
*/
void mark_size(header_t * h, unsigned int size) {
	h->info = (size << 4);
	//h->info = ((h->info << 28) >> 28) | (size << 4);
}

/*@ 
	requires size > 0;
	requires size < _get_size(h->info) <= UINT_MAX/16; 
	requires \valid(h+ (0..(size+1)));
	assigns (h + 1 + size)->info; 
	assigns h->info;
	ensures _lsb_set(h->info);
	ensures _get_size(h->info) == size;
	ensures (_get_size(\old(h->info)) - (size + 1)) == _get_size((h + 1 + size)->info);
	ensures \valid(h + 1 + size);
	ensures \result == (header_t *) h + 1;
	ensures \valid(\result);
*/
header_t * split_block(header_t * h, unsigned int size) {
	unsigned int next_size = get_size(h) - (size + 1);
	(h + 1 + size)->info = next_size;
	h->info = (size << 4);
	mark_allocated(h);
	return h+1;
}


/*@ requires \valid(h);
	assigns \nothing;
 	ensures \result <==> _terminating(h); 
	ensures \valid(h);
	ensures h == \old(h);
*/
int terminating_block(header_t * h) {
	return is_allocated(h) && !get_size(h);
}


/*@ requires HEAP_SIZE > 0; 
 	requires \valid(start+ (0..(HEAP_SIZE-1)));
	requires finite(start);
	requires well_formed(start);
	ensures \valid((header_t *) \result) || (\result == \null);
 */
void * vmalloc(header_t * start, unsigned int size) {  
	if (size <= 0) return NULL;
	header_t * h = start;
	/*@ 
		loop invariant \valid(h);
		loop invariant reachable(start, h);
		loop invariant well_formed(h);
		loop invariant size > 0;
	*/
	while(!terminating_block(h)) {
		if(!is_allocated(h) && (get_size(h) > size)) {
			return split_block(h, size);
		} else if (!is_allocated(h) && (get_size(h) == size)) {
			mark_allocated(h);
			return h+1;
		} else {
			h += (1 + get_size(h));
		}
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
		h += (1 + get_size(h));
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

