#include "verification_stdlib.h"
#include "verification_list.h"
#include "sll_def.h"

/*@ Import Coq Require Import PL.Assignment.sll_hw_lib */
/*@ Extern Coq (max : {A} -> list A -> A) 
               (has_zero : {A} -> list A -> Z)
*/

void tranverse (struct list * p)
/*@ With l
    Require sll(p,l)
    Ensure sll(p,l)
*/
{
  struct list * q = p;
  /*@ Inv exists l1 l2, l == app(l1,l2) && sllseg(p@pre, q, l1) * sll(q, l2) */
  while (q) {
    q = q->next;
  }
  return;
}

int list_max(struct list * p)
/*@ With l
    Require sll(p,l)
    Ensure __return == max(l) && sll(p,l)
*/
{
  struct list * q = p;
  int n = 0;
  /*@ Inv exists l1 l2, l == app(l1,l2) && n == max(l1) && sllseg(p@pre, q, l1) * sll(q, l2) */
  while (q) {
    if (q->data > n) {
      n = q->data;
    }
    q = q->next;
  }
  return n;
}

int no_zero (struct list * p)
/*@ With l
    Require sll(p,l)
    Ensure __return == has_zero(l) && sll(p,l)
*/
{
  struct list * q = p;
  while (q) {
    if (q->data == 0) {
      return 1;
    }
    q = q->next;
  }
  return 0;
}