#include "verification_stdlib.h"
#include "verification_list.h"
#include "hashtbl_def.h"
#include "int_array_def.h"
#include "ptr_array_def.h"

struct blist ** malloc_blist_array()
/*@ Require emp
    Ensure __return != 0 &&
      exists content, PtrArray::full(__return, 211, content)
*/;

struct hashtbl * malloc_hashtbl()
/*@ Require emp
    Ensure __return != 0 &&
            exists bucks_ph top_ph,
              data_at(&(__return -> bucks), bucks_ph) *
              data_at(&(__return -> top), top_ph)
*/;

struct blist * malloc_blist()
/*@ Require emp
    Ensure __return != 0 &&
           data_at(&(__return -> key), 0) *
           data_at(&(__return -> val), 0) *
           data_at(&(__return -> next), 0) *
           data_at(&(__return -> down), 0) *
           data_at(&(__return -> up), 0)
*/;

unsigned int hash_string(char *str)
/*@ With k
    Require store_string(str, k)
    Ensure 0 <= __return && __return <= 4294967295 &&
           __return == hash_string_k(k) &&
           store_string(str, k)
*/;

int string_equal(char *s1, char *s2)
/*@
  With k1 k2
  Require store_string(s1, k1) *
          store_string(s2, k2)
  Ensure store_string(s1, k1) *
         store_string(s2, k2) *
         ((__return == 1 && k1 == k2) ||
          (__return == 0 && k1 != k2))
*/;

void create_bucks(struct hashtbl *h) 
/*@ With bucks_random
    Require data_at(&(h->bucks), bucks_random)
    Ensure exists bucks_base,
           data_at(&(h->bucks), bucks_base) *
           PtrArray::full(bucks_base, 211, zeros(211))
*/
{
  int i;
  h->bucks = malloc_blist_array();
  /*@ Inv exists content bucks_base,
          0 <= i && i <= 211 &&
          data_at(&(h@pre->bucks), bucks_base) *
          PtrArray::full(bucks_base, 211, content) *
          (sublist(0, i, content) == zeros(i))          
*/
  for (i = 0; i < 211; i++) {
    h->bucks[i] = 0;
  }
}

void init_hashtbl(struct hashtbl *h) 
/*@ With bucks_ph top_ph
    Require data_at(&(h->bucks), bucks_ph) *
            data_at(&(h->top), top_ph)
    Ensure store_hash_skeleton(h, empty_map)
*/
{
  h->bucks = 0;
  h->top = 0;
  create_bucks(h);
}

struct hashtbl *create_hashtbl() 
/*@
  Require emp
  Ensure store_hash_skeleton(__return, empty_map) *
         store_map(store_val, empty_map)
*/
{
  struct hashtbl *h;
  h = malloc_hashtbl();
  /*@ exists bucks_ph top_ph,
        data_at(&(h->bucks), bucks_ph) *
        data_at(&(h->top), top_ph) */
  init_hashtbl(h);
  return h;
}

void hashtbl_add(struct hashtbl *h, char *key, unsigned int val) 
/*@
  With m1 m2 k
  Require m1(k) == None &&
          store_hash_skeleton(h, m1) *
          store_map(store_val, m2) *
          store_string(key, k)
  Ensure exists p,
           store_hash_skeleton(h, KP::insert_map(m1, k, p)) *
           store_map(store_val, PV::insert_map(m2, p, val))
*/
{
  /*@ store_hash_skeleton(h, m1)
        which implies
        exists top_ph bucks_ph l lh b,
          contain_all_addrs(m1, l) *
          repr_all_heads(lh, b) *
          contain_all_correct_addrs(m1, b) *
          data_at(&(h->top), top_ph) *
          data_at(&(h->bucks), bucks_ph) *
          dll(top_ph, 0, l) *
          PtrArray::full(bucks_ph, 211, lh) *
          store_map(store_sll, b) *
          store_map(store_name, m1) *
          TT
  */
  unsigned int ind;
  struct blist *buc;
  ind = hash_string(key) % 211; /*@ 0 <= ind && ind < 211 */
  // ind = 0;
  buc = malloc_blist();

  buc->key = key;
  buc->val = val;
  buc->up = 0;
  buc->down = h->top;

  if (h->top != 0){
    /*@ exists top_ph l, 
        top_ph != 0 &&
        data_at(&(h->top), top_ph) * 
        dll(top_ph, 0, l)
        which implies
        exists top_down top_up l_tail,
          l == cons(top_ph, l_tail) && 
          data_at(&(h->top), top_ph) *
          data_at(&(top_ph->down), top_down) *
          data_at(&(top_ph->up), top_up) *
          TT
    */
    h->top->up = buc;
  }
  h->top = buc;
 
  buc->next = h->bucks[ind];
  h->bucks[ind] = buc;
}

unsigned int hashtbl_find(struct hashtbl *h, char *key, int *valid) 
/*@
  With m1 m2 k
  Require map_composable(m1, m2) &&
          store_hash_skeleton(h, m1) *
          store_map(store_uint, m2) *
          store_string(key, k) *
          has_int_permission(valid)
  Ensure store_hash_skeleton(h, m1) *
         store_map(store_uint, m2) *
         store_string(key, k) *
         ((exists p v, store_int(valid, 1) && m1(k) == Some(p) &&
                       m2(p) == Some(v) && __return == v) ||
          (store_int(valid, 0) && m1(k) == None && __return == 0))
*/
{
  unsigned int ind;
  struct blist **i;
    /*@ store_hash_skeleton(h, m1)
        which implies
        exists top_ph bucks_ph l lh b,
          data_at(&(h->top), top_ph) *
          data_at(&(h->bucks), bucks_ph) *
          dll(top_ph, 0, l) *
          contain_all_addrs(m1, l) *
          repr_all_heads(lh, b) *
          contain_all_correct_addrs(m1, b) *
          PtrArray::full(bucks_ph, 211, lh) *
          store_map(store_sll, b) *
          store_map(store_name, m1)
  */
  ind = hash_string(key) % 211;/*@ 0 <= ind && ind < 211 */

/*@ Inv Assert exists l1 l2 top_ph bucks_ph l lh b,
        0 <= ind && ind < 211 &&
        ind == hash_string_k(k) % 211 &&
        data_at(&(h->top), top_ph) *
        data_at(&(h->bucks), bucks_ph) *
        dll(top_ph, 0, l) *
        PtrArray::missing_i(bucks_ph, ind, Znth(ind, lh, 0), 211, lh) *
        store_map_missing_i(store_sll, b, ind) *
        store_map(store_name, m1) *
        (b(ind) == Some(pair(Znth(ind, lh, 0), app(l1, l2)))) *
        sllbseg (&(h->bucks[ind]), i, l1) *
        sll(*i, l2) *
        contain_all_addrs(m1, l) *
        repr_all_heads(lh, b) *
        contain_all_correct_addrs(m1, b) *
        (forall x, !(In(x, l1) && m1(k) == Some(x))) *
        store_map(store_uint, m2) *
        store_string(key, k) *
        has_int_permission(valid) 
*/
  for (i = &h->bucks[ind]; *i != 0; i = &(*i)->next){
    /*@ Assert
          exists l1 l2 top_ph bucks_ph l lh b kp vp p_next k_cur l_tail,
            0 <= ind && ind < 211 &&
            ind == hash_string_k(k) % 211 &&
            l2 == cons(*i, l_tail) &&
            m1(k_cur) == Some(&((*i) -> key)) &&
            data_at(&(h->top), top_ph) *
            data_at(&(h->bucks), bucks_ph) *
            dll(top_ph, 0, l) *
            PtrArray::missing_i(bucks_ph, ind, Znth(ind, lh, 0), 211, lh) *
            store_map_missing_i(store_sll, b, ind) *
            store_map(store_name, m1) *
            (b(ind) == Some(pair(Znth(ind, lh, 0), app(l1, l2)))) *
             ((l1 == nil && i == &(h->bucks[ind]) && sllbseg(&(h->bucks[ind]), i, l1)) ||
             (l1 != nil && exists h_val t_l1, l1 == cons(h_val, t_l1) &&
              h_val == Znth(ind, lh, 0) &&
              data_at(&(h->bucks[ind]), h_val) *
              sllbseg(&(h_val->next), i, t_l1))) *
            contain_all_addrs(m1, l) *
            repr_all_heads(lh, b) *
            contain_all_correct_addrs(m1, b) *
            (forall x, !(In(x, l1) && m1(k) == Some(x))) *
            store_map(store_uint, m2) *
            store_string(key, k) *
            has_int_permission(valid) *
            data_at(&(*i)->key, kp) *
            data_at(&(*i)->val, vp) *
            data_at(&(*i)->next, p_next) *
            store_string(kp, k_cur) *
            sll(p_next, l_tail)
    */
    if (string_equal(key, (*i)->key)) {
      struct blist *b = *i;

      *i = b->next;
      b->next = h->bucks[ind];
      h->bucks[ind] = b;

      *valid = 1;
      return b->val;
    }
  }
  *valid = 0;
  return 0;
// /*@ 
//   Assert exists kp k_cur vp p_next,
//     i == &(h->bucks[ind]) &&
//     store_string(key, k) *
//     data_at(&(*i)->key, kp) *
//     data_at(&(*i)->val, vp) *
//     data_at(&(*i)->next, p_next) *
//     store_string(kp, k_cur) *
//     has_int_permission(valid)
// */
  // /*@ exists top_ph bucks_ph l lh b,
  //       data_at(&(h->top), top_ph) *
  //       data_at(&(h->bucks), bucks_ph) *
  //       dll(top_ph, 0, l) *
  //       PtrArray::full(bucks_ph, 211, lh) *
  //       store_map(store_sll, b) *
  //       store_map(store_name, m1)
  //       which implies
  //       store_hash_skeleton(h, m1)
  // */
}