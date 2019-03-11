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

/*@	lemma reachable_trans:
	\forall list *root, *node;
	reachable(root, node) && \valid(node) ==> reachable(root, node->next);	
*/ 

/*@ predicate well_formed{L}(list * root) = 
	\forall list* node; reachable(root, node) ==>
	\valid(node) || node == (list*) 0;	
  */

/*@ predicate finite{L}(list* root) = reachable(root,\null); */

/*@
	requires \valid(root);
	requires well_formed(root);
	requires finite(root);
	assigns \nothing;
	ensures
	\forall list* l;
	\valid(l) && reachable(root,l) ==>
	\result >= l->size;
	ensures
	\exists list* l;
	\valid(l) && reachable(root,l) && \result == l->size;
*/
int max_list(list* root, size_t size) {
	list* current = root;
	int max = current->size;
	/*@
	  loop invariant reachable(root, current);
	  loop invariant well_formed(current);
	  loop assigns current;
	*/
	while(current->next) {
		//@assert \valid(current->next);
		current = current->next;
		if (current->size > max) max = current->size;
	}
	return max;
}
