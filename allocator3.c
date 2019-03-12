#include <stdlib.h>

typedef struct _list { 
	int size; 
	void* ptr;
	struct _list* next; 
} list;

/*@
	inductive reachable{L} (list* root, list* node) {
	case root_reachable{L}:
	\forall list* root; reachable(root,root);
	case next_reachable{L}:
	\forall list* root, *node;
	reachable(root->next, node) ==>
	reachable(root,node);
}
*/

// May not be necessary
/*@	lemma reachable_trans:
	\forall list *root, *node;
	reachable(root, node) && \valid(node) ==> reachable(root, node->next);	
*/ 

/*@ predicate well_formed{L}(list * root) = 
	\forall list* node; reachable(root, node) ==>
	\valid(node) || node == (list*) 0;	
  */

/*@ predicate finite{L}(list* root) = reachable(root,\null); */

/*@ predicate has_block{L}(list* root, size_t size) =
		\valid(root) &&
		\exists list* node; \valid(node) && reachable(root, node) && node->size >= size;
*/

/* @ lemma reachable_choice{L}:
  \forall list *root, *node;
  \valid(root) && \valid(node) && well_formed(root) && reachable(rootl,node) ==>
  root == node || reachable(root->next, node);
*/

/*@ lemma has_block_choice{L}:
	\forall list* node; \forall size_t size;
	\valid(node) && has_block(node, size) ==>
	node->size >= size || has_block(node->next, size); 
*/

/*@
	//requires \valid(root);
	requires well_formed(root);
	requires finite(root);
	assigns \nothing;
	behavior find:
		assumes has_block(root, size);
		ensures \valid(\result);
		ensures \result->size >= size;
	behavior not_find:
		assumes !has_block(root, size);
		ensures \result == \null;
	complete behaviors find, not_find;
	disjoint behaviors find, not_find;
*/
list* find_block(list* root, size_t size) {
	list* current = root;
	/*@
	  loop invariant reachable(root, current);
	  loop invariant well_formed(current);
	  loop invariant has_block(root,size) <==> has_block(current, size); 
	  loop assigns current;
	*/
	while(current) {
		//@assert \valid(current);
		if (current->size >= size) return current;
		else 
			current = current->next;
	}
	return current;
}
