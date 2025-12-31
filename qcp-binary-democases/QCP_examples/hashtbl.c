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
         store_map(store_uint, empty_map)
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
          store_map(store_uint, m2) *
          store_string(key, k)
  Ensure exists p,
           store_hash_skeleton(h, KP::insert_map(m1, k, p)) *
           store_map(store_uint, PV::insert_map(m2, p, val))
*/
{
  /*@ store_hash_skeleton(h, m1)
        which implies
        exists top_ph bucks_ph l lh b,
          data_at(&(h->top), top_ph) *
          data_at(&(h->bucks), bucks_ph) *
          dll(top_ph, 0, l) *
          PtrArray::full(bucks_ph, 211, lh) *
          store_map(store_sll, b) *
          store_map(store_name, m1)
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
        data_at(&(h->top), top_ph) * 
        dll(top_ph, 0, l)
        which implies
        exists top_down top_up l_tail,
          l == cons(h->top, l_tail) && 
          data_at(&(h->top->down), top_down) *
          data_at(&(h->top->up), top_up)
    */
    h->top->up = buc;
  }
  h->top = buc;
 
  buc->next = h->bucks[ind];
  h->bucks[ind] = buc;
}

// unsigned int hashtbl_find(struct hashtbl *h, char *key, int *valid) 
// /*@
//   With m1 m2 k
//   Require map_composable(m1, m2) &&
//           store_hash_skeleton(h, m1) *
//           store_map(store_uint, m2) *
//           store_string(key, k) *
//           has_int_permission(valid)
//   Ensure store_hash_skeleton(h, m1) *
//          store_map(store_uint, m2) *
//          store_string(key, k) *
//          ((exists p v, store_int(valid, 1) && m1(k) == Some(p) &&
//                        m2(p) == Some(v) && __return == v) ||
//           (store_int(valid, 0) && m1(k) == None && __return == 0))
// */
// {
//   unsigned int ind;
//   struct blist **i;

//   ind = hash_string(key) % 211;
//     /*@ Inv
//       exists top_ph bucks_ph l lh b l_visited l_remaining head,
//       0 <= ind && ind < 211 &&
//       b(ind)== Some(pair(head, l_visited ++ l_remaining)) &&
//       head == Znth(ind, lh, 0)&&
//       contain_all_addrs(m1, l)&&
//       repr_all_heads(lh, b)&&
//       contain_all_correct_addrs(m1, b)&&
//       data_at(&(h->top), top_ph)*
//       data_at(&(h->bucks), bucks_ph)*
//       dll(top_ph, 0, l)*
//       PtrArray::missing_i(bucks_ph, 211, ind, head, lh)*
//       sllbseg(&h->bucks[ind],i,l_visited)*
//       sll(*i, l_remaining)*
//       store_map_missing_i(store_sll, b, ind)*
//       store_map(store_name, m1)*
//       store_map(store_uint, m2)
//   */
//   for (i = &h->bucks[ind]; *i != 0; i = &(*i)->next)
//     if (string_equal(key, (*i)->key)) {
//       struct blist *b = *i;

//       *i = b->next;
//       b->next = h->bucks[ind];
//       h->bucks[ind] = b;

//       *valid = 1;
//       return b->val;
//     }
//   *valid = 0;
//   return 0;
// }

// unsigned int *hashtbl_findref(struct hashtbl *h, char *key) 
// /*@
//   With m k
//   Require store_hash_skeleton(h, m) *
//           store_string(key, k)
//   Ensure store_hash_skeleton(h, m) *
//          store_string(key, k) *
//          ((exists p, m(k) == Some(p) && __return == p) ||
//           (m(k) == None && __return == 0))
// */
// {
//   unsigned int ind;
//   struct blist **i;

//   ind = hash_string(key) % 211;
//   for (i = &h->bucks[ind]; *i != 0; i = &(*i)->next)
//     if (string_equal(key, (*i)->key)) {
//       struct blist *b = *i;
//       // LRU
//       *i = b->next;
//       b->next = h->bucks[ind];
//       h->bucks[ind] = b;

//       return &b->val;
//     }
//   return 0;
// }


// unsigned int hashtbl_remove(struct hashtbl *h, char *key, int *removed) 
// /*@
//   With m1 m2 k
//   Require map_composable(m1, m2) &&
//           store_hash_skeleton(h, m1) *
//           store_map(store_uint, m2) *
//           store_string(key, k) *
//           has_int_permission(removed)
//   Ensure store_hash_skeleton(h, KP::remove_map(m1, k)) *
//          store_string(key, k) *
//          ((exists p v key0,
//              m1(k) == Some(&(p -> val)) &&
//              m2(&(p -> val)) == Some(v) && __return == v &&
//              store_int(removed, 1) *
//              store_map(store_uint, PV::remove_map(m2, p)) *
//              store_ptr(&(p -> key), key0) * store_string(key0, k) *
//              has_ptr_permission(&(p -> up)) *
//              has_ptr_permission(&(p -> down)) *
//              has_ptr_permission(&(p -> next)) *
//              store_uint(&(p -> val), v)) ||
//           (m1(k) == None && __return == 0 &&
//            store_int(removed, 0) * store_map(store_uint, m2)))
// */
// {
//   unsigned int ind;
//   struct blist **it;

//   ind = hash_string(key) % 211;
//   for (it = &h->bucks[ind]; *it != 0; it = &(*it)->next) {
//     struct blist *b = *it;
//     if (string_equal(key, b->key)) {
//       if (h->top == b)
//         h->top = b->down;

//       if (b->up != 0)
//         b->up->down = b->down;
//       if (b->down != 0)
//         b->down->up = b->up;

//       *it = b->next;
//       unsigned int res = b->val;
//       free_blist(b);
//       *removed = 1;
//       return res;
//     }
//   }
//   *removed = 0;
//   return 0;
// }

// void hashtbl_free_blist(struct blist *bl) {
//   if (bl != 0) {
//     hashtbl_free_blist(bl->next);
//     free_string(bl -> key);
//     free_blist(bl);
//   }
// }

// void hashtbl_clear(struct hashtbl *h) {
//   int i;

//   for (i = 0; i < 211; i++) {
//     hashtbl_free_blist(h->bucks[i]);
//     h->bucks[i] = 0;
//   }

//   free_blist_array(h->bucks);
//   h->bucks = 0;
//   h->top = 0;
// }

// void free_hashtbl(struct hashtbl *h) 
// /*@
//   With m1 m2
//   Require map_composable(m1, m2) &&
//           store_hash_skeleton(h, m1) *
//           store_map(store_uint, m2)
//   Ensure emp
// */
// {
//   hashtbl_clear(h);
//   free_hashtbl(h);
// }
