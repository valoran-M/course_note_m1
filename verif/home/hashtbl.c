#include "limits.h"

/* -------------------------------------------------------------------------- */
/*
  This file provides a simplified hash tables library: they are not dynamic and
  thus cannot be resized.

  Your goal is to:
  1. write the ACSL specification for the provided functions from their informal
     specification.
  2. prove that each function conforms to its specification
  3. prove the absence of runtime errors with the option -wp-rte
*/
/* -------------------------------------------------------------------------- */

/* -------------------------------------------------------------------------- */
/*
  Simplified strings:
  all strings in this file are assumed to have size STRING_LEN.
  The eq_string function is provided with its formal specification so you do
  not have anything to do for this function.
*/
/* -------------------------------------------------------------------------- */

#define STRING_LEN 20

/* The EqString predicate can be useful, don't hesitate to use it. */
/*@ predicate EqString(char *s1, char *s2) =
      \forall integer i; 0 <= i < STRING_LEN ==> s1[i] == s2[i];
*/

/*@ requires \valid_read(s1 + (0 .. STRING_LEN - 1));
    requires \valid_read(s2 + (0 .. STRING_LEN - 1));
    assigns \nothing;

    behavior eq:
      assumes EqString(s1, s2);
      ensures \result == 1;

    behavior not_eq:
      assumes ! EqString(s1, s2);
      ensures \result == 0;

    complete behaviors;
    disjoint behaviors;
*/
int eq_string(const char *s1, const char *s2) {
  int i;
  /*@ loop invariant 0 <= i <= STRING_LEN;
      loop invariant \forall integer j; 0 <= j < i ==> s1[j] == s2[j];
      loop assigns i;
      loop variant STRING_LEN - i;
  */
  for(i = 0; i < STRING_LEN; i++)
    if (s1[i] != s2[i]) return 0;
  return 1;
}

/* -------------------------------------------------------------------------- */
/*
  Data structures

  Our hash tables map string keys to integer values. The hash function for
  strings is provided.

  Hash tables are represented by their number of element and an array of
  "buckets" of length HASHTBL_LEN.

  The "buckets" are themselves arrays of pairs (key, value) (individually called
  "bucket") where all keys have the same hash. Each array is of fixed length
  BUCKET_LEN, but the number of stored elements can change.
*/
/* -------------------------------------------------------------------------- */

#define BUCKET_LEN 10
#define HASHTBL_LEN 17

typedef struct {
  char *key; // key, as (simplified) strings
  int value; // value associated to the key
} Bucket;

typedef struct {
  Bucket buckets[BUCKET_LEN]; // array of pairs (key, value)
  int size;                   // number of elements actually stored in the array
} Buckets;

typedef struct {
  Buckets data[HASHTBL_LEN];  // array of buckets
  int size;                   // number of buckets actually stored in the array
} Hashtbl;

/* -------------------------------------------------------------------------- */
/*
  The hash function is provided: nothing to do.

  The postcondition of the hash function cannot be proved without a logic
  definition for Hash. You do not have to do it, this postcondition will
  remain assumed.
*/
/* -------------------------------------------------------------------------- */

/*
  The logic function HashIndex in the axiomatic definition Hash might be useful.
*/
/*@ axiomatic Hash {
      logic unsigned long Hash(char *s) reads(s + (0 .. ));
      // Hash is an abstract model for the hash function

      logic integer HashIndex(Hashtbl *tbl, char *k) = Hash(k) % HASHTBL_LEN;
    }
*/

/*@ requires \valid_read(s + (0 .. STRING_LEN - 1));
    assigns \nothing;
    ensures left_unproved: \result == Hash(s); // do not try to prove this
*/
unsigned long hash(const char *s) {
  unsigned long h = 5381;
  int i;
  /*@ loop invariant 0 <= i <= STRING_LEN;
      loop assigns h, i;
      loop variant STRING_LEN - i;
  */
  for(i = 0; i < STRING_LEN; i++) {
    if (s[i]) break;
    h = ((h << 5) + h) + s[i];
  }
  return h;
}

/*
  You can add your own logic function and predicate definitions for simplifying
  your annotations.
*/

/*@
  logic Bucket last_bucket(Hashtbl *tbl, char *k) =
    tbl->data[HashIndex(tbl, k)].buckets[tbl->data[HashIndex(tbl, k)].size - 1] ;
*/

/* -------------------------------------------------------------------------- */
/*
  Exercise 0

  The size function returns the number of element in a given hash table.
*/
/* -------------------------------------------------------------------------- */

/*@ requires \valid_read(tbl);
    ensures \result == tbl->size;
 */
int size(const Hashtbl *tbl) {
  return tbl->size;
}

/* -------------------------------------------------------------------------- */
/*
  Exercise 1:

  The init function initialize a hash table with 0 elements, in particular, each
  bucket contains 0 elements.
*/
/* -------------------------------------------------------------------------- */

/*@ requires \valid(tbl);
    ensures tbl->size == 0;
    ensures \forall integer i; 0 <= i < HASHTBL_LEN ==> tbl->data[i].size == 0;
*/
void init(Hashtbl *tbl){
  int i;
  tbl->size = 0;
  /*@
    loop invariant 0 <= i <= HASHTBL_LEN ;
    loop invariant
      \forall integer j ; 0 <= j < i ==>  tbl->data[j].size == 0 ;
    loop assigns i, tbl->data[(0 .. HASHTBL_LEN - 1)].size;
    loop variant HASHTBL_LEN - i ;
  */
  for(i = 0; i < HASHTBL_LEN; i++)
    tbl->data[i].size = 0;
}

/* -------------------------------------------------------------------------- */
/*
  Exercise 2:

  The add function adds a pair (key, value) in the hash table if it is not full.
  In this case, it returns 0.

  If the table is full, the function does not do anything and returns -1.

  (When the table is modifiied, do not forget to specify the new sizes and the
  added pair)
*/
/* -------------------------------------------------------------------------- */

/*@ requires \valid(tbl) ;
    requires \valid_read(k + (0 .. STRING_LEN - 1)) ;
    requires \valid(&tbl->data[HashIndex(tbl, k)]) ;

    behavior not_full:
      assumes tbl->data[HashIndex(tbl, k)].size < BUCKET_LEN ;

      requires tbl->data[HashIndex(tbl, k)].size >= 0 ;
      requires tbl->size + 1 <= INT_MAX ;
      assigns tbl->size,
              tbl->data[HashIndex(tbl, k)] ;

      ensures last_bucket(tbl, k).key   == k ;
      ensures last_bucket(tbl, k).value == d ;

      ensures tbl->data[HashIndex(tbl, k)].size ==
              \old(tbl->data[HashIndex(tbl, k)].size) + 1 ;
      ensures tbl->size == \old(tbl->size) + 1 ;
      ensures \result == 0 ;

    behavior full:
      assumes tbl->data[HashIndex(tbl, k)].size >= BUCKET_LEN ;
      ensures tbl->size == \old(tbl->size) ;
      ensures \result == -1 ;

    complete behaviors;
    disjoint behaviors;
*/
int add(Hashtbl *tbl, char *k, int d) {
  Bucket new_entry;
  unsigned int h = hash(k) % HASHTBL_LEN;
  if (tbl->data[h].size >= BUCKET_LEN)
    return -1;
  new_entry.key = k;
  new_entry.value = d;
  tbl->data[h].buckets[tbl->data[h].size] = new_entry;
  tbl->data[h].size++;
  tbl->size++;
  return 0;
}

/* -------------------------------------------------------------------------- */
/*
  Exercise 3:

  The mem_binding function returns 1 if the pair (key, value) in input appears
  in the hash table. Else, it returns 0.
*/
/* -------------------------------------------------------------------------- */

/*@ requires \valid_read(tbl) ;
    requires \valid_read(&tbl->data[HashIndex(tbl, k)]) ;
    requires \valid_read(k + (0 .. STRING_LEN - 1)) ;
    requires \forall integer i; 0 <= i < tbl->data[HashIndex(tbl, k)].size ==>
      \valid_read(tbl->data[HashIndex(tbl, k)].buckets[i].key +
        (0 .. STRING_LEN - 1)) ;
    requires 0 <= tbl->data[HashIndex(tbl, k)].size < BUCKET_LEN ;

    behavior in:
      assumes \exists integer i; 0 <= i < tbl->data[HashIndex(tbl, k)].size &&
        tbl->data[HashIndex(tbl, k)].buckets[i].value == v &&
        EqString(k, tbl->data[HashIndex(tbl, k)].buckets[i].key) ;
      ensures \result == 1 ;

    behavior not_in:
      assumes \forall integer i; 0 <= i < tbl->data[HashIndex(tbl, k)].size ==>
        tbl->data[HashIndex(tbl, k)].buckets[i].value != v ||
        ! EqString(k, tbl->data[HashIndex(tbl, k)].buckets[i].key) ;
      ensures \result == 0 ;

    complete behaviors;
    disjoint behaviors;
*/
int mem_binding(const Hashtbl *tbl, const char *k, int v) {
  int i, h = hash(k) % HASHTBL_LEN;
  /*@ loop invariant 0 <= i <= tbl->data[h].size ;
      loop invariant \forall integer j; 0 <= j < i ==>
        tbl->data[HashIndex(tbl, k)].buckets[j].value != v ||
        ! EqString(k, tbl->data[HashIndex(tbl, k)].buckets[j].key) ;
      loop assigns i ;
      loop variant tbl->data[h].size - i ;
  */
  for(i = 0; i < tbl->data[h].size; i++) {
    if (eq_string(k, tbl->data[h].buckets[i].key)
        && tbl->data[h].buckets[i].value == v)
      return 1;
  }
  return 0;
}
