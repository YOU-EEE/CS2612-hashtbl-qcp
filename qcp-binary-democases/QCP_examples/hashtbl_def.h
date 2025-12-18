// #ifndef HASHTBL_H
// #define HASHTBL_H

// #define NBUCK 211

struct blist {
  char *key;
  unsigned int val;
  /* for elements with the same hash */
  struct blist *next;
  /* for traversing the whole table */
  struct blist *down;
  struct blist *up;
};

struct hashtbl {
  struct blist **bucks;
  struct blist *top;
};

/*@ Extern Coq (sll : Z -> list Z -> Assertion)
               (sllseg: Z -> Z -> list Z -> Assertion)
               (sllbseg: Z -> Z -> list Z -> Assertion)
               (dll: Z -> Z -> list Z -> Assertion)
               (dllseg: Z -> Z -> Z -> Z -> list Z -> Assertion)
               (store_string: Z -> list Z -> Assertion)
               (hash_string_k: list Z -> Z)
               (store_sll: Z -> (Z * list Z) -> Assertion)
               (store_name: list Z -> Z -> Assertion)
               (contain_all_addrs: (list Z -> option Z) -> list Z -> Prop)
               (repr_all_heads: list Z -> (Z -> option (Z * list Z)) -> Prop)
               (contain_all_correct_addrs: (list Z -> option Z) -> (Z -> option (Z * list Z)) -> Prop)
               (store_hash_skeleton: Z -> (list Z -> option Z) -> Assertion)
               (map_compose: (list Z -> option Z) -> (Z -> option Z) -> (Z -> option Z) -> Prop)
               (map_composable: (list Z -> option Z) -> (Z -> option Z) -> Prop)
               (empty_map: {A} {B} -> A -> option B)
               (KP::insert_map: (list Z -> option Z) -> list Z -> Z -> (list Z -> option Z))
               (KP::remove_map: (list Z -> option Z) -> list Z -> (list Z -> option Z))
               (PV::insert_map: (Z -> option Z) -> Z -> Z -> (Z -> option Z))
               (PV::remove_map: (Z -> option Z) -> Z -> (Z -> option Z))
               (store_map: {A} {B} -> (A -> B -> Assertion) -> (A -> option B) -> Assertion)
               (store_hashtbl: Z -> (list Z -> option Z) -> Assertion)
 */

/*@ Import Coq Require Import hashtbl_lib */

struct hashtbl *create_hashtbl();
void hashtbl_add(struct hashtbl *h, char * key, unsigned int val);
unsigned int hashtbl_find(struct hashtbl *h, char * key, int *valid);
unsigned int *hashtbl_findref(struct hashtbl *h, char * key);

/* do not free anything */
unsigned int hashtbl_remove(struct hashtbl *h, char * key, int *removed);
void free_hashtbl(struct hashtbl *h);


void free_string(char *);
void free_blist_array(struct blist **);
void free_blist(struct blist *);
void free_hashtbl(struct hashtbl *);
int string_equal(char *, char *);

// #endif
