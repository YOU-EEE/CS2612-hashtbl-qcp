#ifndef HASHTBL_H
#define HASHTBL_H

#define NBUCK 211

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

struct hashtbl *create_hashtbl();
void hashtbl_add(struct hashtbl *h, char * key, unsigned int val);

unsigned int hashtbl_find(struct hashtbl *h, char * key, int *valid);

unsigned int *hashtbl_findref(struct hashtbl *h, char * key);
/* do not free anything */
unsigned int hashtbl_remove(struct hashtbl *h, char * key, int *removed);
void free_hashtbl(struct hashtbl *h);

struct blist ** malloc_blist_array();
struct blist * malloc_blist();
struct hashtbl * malloc_hashtbl();
void free_blist_array(struct blist **);
void free_blist(struct blist *);
void free_hashtbl(struct hashtbl *);
unsigned int hash_string(char *);
int string_equal(char *, char *);

#endif
