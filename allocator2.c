#include <stdio.h>
#include <stdlib.h>
#include <limits.h>

#define HEAP_SIZE 4096 

typedef struct {
  unsigned int info;
  void * empty; // Used to align header to 16 bytes
} header_t;

header_t * heap_start = NULL;

/*@ predicate _lsb_set(unsigned int i) = 
	(unsigned int) (i & ((unsigned int) 1)) > (unsigned int) 0;		
*/

/*@ logic integer _get_size(unsigned int i) =
	((i >> 4) << 4);	
*/

/*@ predicate _eq_size(unsigned int x, unsigned int y) =
		((x>>4)<<4) == ((y>>4)<<4);
*/

/*@ lemma lsb_off:
	\forall unsigned int x; !_lsb_set((unsigned int) (((unsigned int) (~0 ^ 1)) & x)); 
*/

/*@ lemma bit_or_rshift_dist:
		\forall unsigned int x, y; \forall integer a; (0 <= a <= 32) ==> (((x|y)>>a) == ((x>>a)|(y>>a))); 
	lemma bit_or_lshift_dist:
		\forall unsigned int x, y; \forall integer a; ((x|y)<<a) == ((x<<a)|(y<<a)); 
	lemma bit_shift_unshift:
		\forall unsigned int x; \forall integer a; (((x>>a)<<a)>>a) == (x>>a); 
	lemma bit_successive_shift:
		\forall unsigned int x; \forall integer a, b; (0 <= a <= 32) ==> (((x>>a)>>b) == (x>>(a + b)));
	lemma bit_total_shift:
		\forall unsigned int x; (x >> 32) ==  0;
	lemma bit_total_shift_temp:
		\forall unsigned int x,y; ((x >> 32)|y) ==  (0|y);
	lemma bit_zero_or:
		\forall unsigned int x;  (((unsigned int) 0) | x) == x;
	lemma bit_or_commute:
		\forall unsigned int x, y;  (y | x) == (x | y);
	lemma rshift_zero:
		\forall integer a; (((unsigned int) 0) >> a) == ((unsigned int) 0);
	lemma lshift_zero:
		\forall integer a; (((unsigned int) 0) << a) == ((unsigned int) 0);
*/

/* lemma test:
	\forall unsigned int x, y; (((((x << 28) >> 28) | ((y >> 4) << 4)) >> 4) << 4) == ((y >> 4) << 4);
 */

/*@ lemma test2:
	\forall unsigned int x,y; ((x|y)>>4) == ((x>>4)|(y>>4));
 */


/*@ ensures \result == (0|y);
 */
unsigned int temp(unsigned int x, unsigned int y) {
	return (((x>>28)>>4)|y);
}

/*@ requires \valid(h);
	ensures (h->info>>4) == (0|(size>>4));
	ensures \valid(h);
*/
void mark_size(header_t * h, unsigned int size) {
	unsigned int a = (h->info<<28)>>28;
	unsigned int b = size;
	h->info = a|b;
	//h->info = ((h->info << 28) >> 28) | ((size >> 4) << 4);
}

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
	ensures \result == (unsigned int) _get_size(h->info);
	ensures \valid(h);
*/
unsigned int get_size(header_t * h) {
	return (h->info >> 4) << 4;
}

/*@ requires \valid(h+ (0..((size/16)+1)));
	requires size > 0;
	ensures _lsb_set(h->info);
	ensures \result == (header_t *) h + 1;
*/
header_t * split_block(header_t * h, unsigned int size) {
	unsigned int new_size = get_size(h) - size - 16;
	h->info = size;
	//@ assert \valid(h);
	mark_allocated(h);
	(h + 1 + (size/16))->info = new_size;
	return h+1;
}

/*
int terminating_block(header_t * h) {
	return is_allocated(h) && get_size(h) == 0;
}
*/

/*
int valid_heap(char * heap_start) {
	return 1;
}
*/

/*
void * vmalloc(char * heap_start, unsigned int size) { // Size required to be multiple of 16 
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
*/


/*
void vfree(header_t * ptr) {
	mark_free(ptr);
}
*/

/*
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

//assumes little endian
void printBits(size_t const size, void const * const ptr)
{
    unsigned char *b = (unsigned char*) ptr;
    unsigned char byte;
    int i, j;

    for (i=size-1;i>=0;i--)
    {
        for (j=7;j>=0;j--)
        {
            byte = (b[i] >> j) & 1;
            printf("%u", byte);
        }
    }
    puts("");
}


int main(int argc, char * argv[]) {
	init();
	unsigned int block_size;
	for (int i=0; i<10; i++) {
		block_size = ((rand() % 9) + 1) * 16;	
		vmalloc(heap_start, block_size);
		printf("Allocated %d bytes\n", block_size);
	}
	printBits(4, heap_start);
	printf("\n");
	vfree(heap_start);
	printBits(4, heap_start);
	printf("\n");
	print_debug((header_t *) heap_start);
	return 0;
}
*/

