#ifndef VFSTUFF_BI_BIG_INT_H
#define VFSTUFF_BI_BIG_INT_H

#include <string.h>
#include <limits.h>
#include "b64.h"
/*@ #include "util.gh" @*/
/*@ #include "poly.gh" @*/

#define CACHE_LINE 64
// fill out a 64-byte cache line
//#define N_INTS ((CACHE_LINE-2*sizeof(void*))/(sizeof(uint32_t)))
#define N_INTS 12
// number of bits to reserve for carries
#define CARRY_BITS 4
#define CHUNK_BITS ((int)32-(int)CARRY_BITS)
#define CHUNK_BASE (pow_nat(2,nat_of_int(CHUNK_BITS)))

typedef struct big_int_block {
    struct big_int_block* prev;
    struct big_int_block* next;
    uint32_t chunks[N_INTS];
} big_int_block;

typedef big_int_block* big_int_block_ptr;

typedef struct big_int {
    struct big_int_block *first;
    struct big_int_block *last;
    bool is_pos;
} big_int;

/*@

predicate bi_block_opt
        (big_int_block* first,
         big_int_block* last;
         big_int_block* first_prev,
         big_int_block* last_next,
         list<big_int_block*> ptrs,
         list<uint32_t> chunks) =
    first == 0
    ? last == 0 &*& first_prev == 0 &*& last_next == 0
    &*& ptrs == nil &*& chunks == nil
    : bi_block(first,last,first_prev,last_next,ptrs,chunks)
    ;

predicate bi_block(big_int_block* first,
                   big_int_block* last;
                   big_int_block* first_prev,
                   big_int_block* last_next,
                   list<big_int_block*> ptrs,
                   list<uint32_t> chunks) =
        malloc_block_big_int_block(first)
        //struct_big_int_block_padding(first)
    &*& first > 0
    &*& first->next   |-> ?next
    &*& first->prev   |-> first_prev
    &*& first->chunks[..N_INTS] |-> ?my_chunks
    &*& first == last
    ?       last_next == next &*& chunks == my_chunks
        &*& ptrs == cons(first,nil)
    :       bi_block(next, last, first, last_next, ?more_ptrs, ?more_chunks)
        &*& !mem(first,more_ptrs)
        &*& chunks == append(my_chunks, more_chunks)
        &*& ptrs == cons(first,more_ptrs)
    ;

lemma_auto void bi_block_inv();
    requires [?f]bi_block(?b, ?last, ?fprev, ?lnext, ?ptrs, ?chunks);
    ensures  [ f]bi_block( b,  last,  fprev,  lnext,  ptrs,  chunks)
        &*&  b > 0 &*& last > 0
        &*&  !!forall(chunks, (bounded)(0,pow_nat(2,N32)-1))
        &*&  length(chunks) >= N_INTS
        &*&  length(ptrs)*N_INTS == length(chunks)
        &*&  (length(ptrs) == 1) == ( b == last)
        &*&  length(ptrs) >= 1
        &*&  (length(chunks) == N_INTS) == (b == last)
        &*&  !!mem(b,ptrs) &*& !!mem(last,ptrs)
        &*&  poly_eval(chunks,CHUNK_BASE) >= 0
        ;

lemma_auto void bi_block_opt_inv();
    requires [?f]bi_block_opt(?b, ?last, ?fprev, ?lnext, ?ptrs, ?chunks);
    ensures  [ f]bi_block_opt( b,  last,  fprev,  lnext,  ptrs,  chunks)
        &*&  !!forall(chunks, (bounded)(0,pow_nat(2,N32)-1))
        &*&  length(ptrs)*N_INTS == length(chunks)
        &*&  (length(chunks) == 0) == (b == 0)
        ;

predicate bi_big_int(big_int* b, int free_carries; int i)
    = malloc_block_big_int(b)
    &*& b->first |-> ?first
    &*& b->last |-> ?last
    &*& b->is_pos |-> ?is_pos
    &*& free_carries >= 0 &*& free_carries <= CARRY_BITS
    &*& bi_block(first,last,0,0,_,?chunks)
    &*& !!forall(chunks,
        (bounded)(0,
                  pow_nat(2,nat_of_int(32-free_carries))-1))
    &*& let(poly_eval(chunks,
                CHUNK_BASE),
            ?abs_i)
    &*& is_pos ? i == abs_i : i == -abs_i;

lemma void bi_block_disjoint(big_int_block* a,big_int_block* b);
    requires [?f1]bi_block(a,?alast, ?afprev, ?alnext,?aptrs,?achunks)
        &*&  [?f2]bi_block(b,?blast, ?bfprev, ?blnext,?bptrs,?bchunks)
        &*&  f1 + f2 > 1;
    ensures  [ f1]bi_block(a, alast,  afprev,  alnext, aptrs, achunks)
        &*&  [ f2]bi_block(b, blast,  bfprev,  blnext, bptrs, bchunks)
        &*&  !!disjoint(aptrs,bptrs);

lemma void bi_block_extend(big_int_block* b);
    requires [?f]bi_block(b,?last1, ?fprev, ?lnext, ?ptrs1,?chunks)
        &*&  [ f]bi_block(lnext,?last,last1,?lnext2,?ptrs2,?chunks2)
        &*&  !!disjoint(ptrs1,ptrs2);
    ensures  [ f]bi_block(b,  last,  fprev,  lnext2,
            append(ptrs1,ptrs2), append(chunks,chunks2));

@*/

big_int_block* new_block();
    /*@ requires true; @*/
    /*@ ensures  bi_block(result, result, 0,0,
                    _,
                    repeat(0,nat_of_int(N_INTS))); @*/
    /*@ terminates; @*/

big_int* new_big_int_zero();
    /*@ requires true; @*/
    /*@ ensures  bi_big_int(result, CARRY_BITS, 0); @*/
    /*@ terminates; @*/

big_int* big_int_from_hex(const char* s);
    /*@ requires [?f]string(s,?cs)
            &*&  base_n(hex_chars(),reverse(cs),_,?val)
            ; @*/
    /*@ ensures  [ f]string(s, cs)
            &*&  bi_big_int(result, CARRY_BITS, val); @*/
    /*@ terminates; @*/

void free_big_int_inner(big_int* p);
    /*@ requires bi_big_int(p, CARRY_BITS, _); @*/
    /*@ ensures  true; @*/
    /*@ terminates; @*/

char* big_int_to_hex(const big_int* s);
    /*@ requires [?f]bi_big_int(s, CARRY_BITS, ?val); @*/
    /*@ ensures  [ f]bi_big_int(s, CARRY_BITS, val)
            &*&  malloced_string(result,?cs)
            &*&  base_n(hex_chars(),reverse(cs),?cs_seq,val)
            // minimality
            &*&  val == 0 ? cs == "0"
            :    !!minimal(cs_seq); @*/
    /*@ terminates; @*/

void big_int_reduce(big_int* p);
    /*@ requires bi_big_int(p,?carry_bits,?v)
            &*&  carry_bits >= 1
            &*&  v >= 0; @*/
    /*@ ensures  bi_big_int(p,CARRY_BITS,v); @*/
    /*@ terminates; @*/

void big_int_pluseq(big_int* a,const big_int* b);
    /*@ requires     bi_big_int(a,?a_carry,?av)
            &*&  [?f]bi_big_int(b,?b_carry,?bv)
            &*&  a_carry > 0 &*& b_carry > 0
            ; @*/
    /*@ ensures      bi_big_int(a,min_of(a_carry,b_carry)-1,av+bv)
            &*&  [ f]bi_big_int(b, b_carry, bv); @*/
    /*@ terminates; @*/

#endif

