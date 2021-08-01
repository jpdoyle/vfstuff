#ifndef VFSTUFF_BI_BIG_INT_H
#define VFSTUFF_BI_BIG_INT_H

#include <string.h>
#include <limits.h>
#include "../b64.h"
/*@ #include "../div.gh" @*/
/*@ #include "../util.gh" @*/
/*@ #include "../poly.gh" @*/

#define CACHE_LINE 64
// fill out a 64-byte cache line
//#define N_INTS ((CACHE_LINE-2*sizeof(void*))/(sizeof(uint32_t)))
//#define N_INTS 12
#define N_INTS 44
// number of bits to reserve for carries
//#define CARRY_BITS 3
#define CARRY_BITS 7
#define CHUNK_BITS ((int)31-(int)CARRY_BITS)
#define CHUNK_BASE (pow_nat(2,nat_of_int(CHUNK_BITS)))

typedef struct big_int_block {
    struct big_int_block* prev;
    struct big_int_block* next;
    int32_t chunks[N_INTS];
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
         list<int32_t> chunks) =
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
                   list<int32_t> chunks) =
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
        &*&  f > 0 &*& f <= 1
        &*&  b > 0 &*& last > 0
        &*&  !!forall(chunks, (bounded)(-pow_nat(2,N31),pow_nat(2,N31)-1))
        &*&  length(chunks) >= N_INTS
        &*&  length(ptrs)*N_INTS == length(chunks)
        &*&  (length(ptrs) == 1) == ( b == last)
        &*&  length(ptrs) >= 1
        &*&  (length(chunks) == N_INTS) == (b == last)
        &*&  !!mem(b,ptrs) &*& !!mem(last,ptrs)
        ;

lemma_auto void bi_block_opt_inv();
    requires [?f]bi_block_opt(?b, ?last, ?fprev, ?lnext, ?ptrs, ?chunks);
    ensures  [ f]bi_block_opt( b,  last,  fprev,  lnext,  ptrs,  chunks)
        &*&  !!forall(chunks, (bounded)(-pow_nat(2,N31),pow_nat(2,N31)-1))
        &*&  length(ptrs)*N_INTS == length(chunks)
        &*&  (length(chunks) == 0) == (b == 0)
        &*&  (length(ptrs) == 0) == (b == 0)
        &*&  (length(ptrs) <= 1) == (b == last)
        &*&  (b == 0) == (last == 0)
        ;

//fixpoint int signed_center(nat bits,int thresh,int x) {
//    return x < thresh ? x : x-pow_nat(2,bits);
//}
//
//lemma void signed_center_eq(nat nbits,int thresh,int x,int y)
//    requires thresh >= 0 &*& thresh < pow_nat(2,nbits)
//        &*&  x >= 0 &*& x < pow_nat(2,nbits)
//        &*&  y >= 0 &*& y < pow_nat(2,nbits)
//        &*&  signed_center(nbits,thresh,x)
//            == signed_center(nbits,thresh,y);
//    ensures  x == y;
//{ }

//lemma void signed_center_plus(nat nbits,int thresh,int x,int y)
//    requires thresh >= 0 &*& 2*thresh < pow_nat(2,nbits)
//        &*&  abs(signed_center(nbits,thresh,x)) < thresh
//        &*&  abs(signed_center(nbits,thresh,y)) < thresh;
//    ensures  euclid_div_sol(x+y,pow_nat(2,nbits),_,?xpy)
//        &*& signed_center(nbits,2*thresh,xpy)
//        ==   signed_center(nbits,thresh,x)
//            +signed_center(nbits,thresh,y);
//{
//    if(x < thresh && y < thresh) {
//        euclid
//    }
//}

predicate bi_big_int(big_int* b, int free_carries, bool underflow; int i)
    = malloc_block_big_int(b)
    &*& b > 0
    &*& b->first |-> ?first
    &*& b->last |-> ?last
    &*& b->is_pos |-> ?is_pos
    &*& free_carries >= 0
    &*& bi_block(first,last,0,0,_,?chunks)
    &*& let(pow_nat(2,nat_of_int(31-free_carries))-1,?upper)
    &*& !!forall(chunks, (bounded)(-upper,upper))
    &*& let(underflow ? -upper : 0,?lower)
    &*& free_carries <= CARRY_BITS
    &*& !!forall(chunks, (bounded)(lower,upper))
    &*& let(poly_eval(chunks, CHUNK_BASE), ?abs_i)
    &*& is_pos ? i == abs_i : i == -abs_i;

lemma_auto void bi_big_int_inv();
    requires [?f1]bi_big_int(?p, ?carry1, ?und1, ?i1);
    ensures  [ f1]bi_big_int( p,  carry1,  und1,  i1)
        &*&  f1 > 0 &*& f1 <= 1 &*& p > 0;

lemma void bi_big_int_val(big_int* p);
    requires [?f1]bi_big_int(p, ?carry1, ?und1, ?i1)
        &*&  [?f2]bi_big_int(p, ?carry2, ?und2, ?i2);
    ensures  [ f1]bi_big_int(p,  carry1,  und1,  i1)
        &*&  [ f2]bi_big_int(p,  carry2,  und2,  i2)
        &*&  i1 == i2;

lemma void bi_big_int_unique(big_int* p, big_int* q);
    requires [?f1]bi_big_int(p, ?carry1, ?und1, ?i1)
        &*&  [?f2]bi_big_int(q, ?carry2, ?und2, ?i2)
        &*&  f1+f2 > 1;
    ensures  [ f1]bi_big_int(p,  carry1,  und1,  i1)
        &*&  [ f2]bi_big_int(q,  carry2,  und2,  i2)
        &*&  p != q;

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

lemma void bi_block_rend(big_int_block* b, big_int_block* i);
    requires [?f]bi_block(b, ?last, ?fprev, ?lnext, ?ptrs, ?chunks)
        &*&  !!mem(i,ptrs) &*& b != i;
    ensures  [ f]bi_block(b,?last1,  fprev, i, ?ptrs1,?chunks1)
        &*&  [ f]bi_block(i,last,last1,lnext,?ptrs2,?chunks2)
        &*&  !!disjoint(ptrs1,ptrs2)
        &*&  chunks == append(chunks1,chunks2)
        &*&  ptrs == append(ptrs1,ptrs2);

@*/

big_int_block* new_block();
    /*@ requires true; @*/
    /*@ ensures  bi_block(result, result, 0,0,
                    _, repeat(0,nat_of_int(N_INTS))); @*/
    /*@ terminates; @*/

big_int* new_big_int_zero();
    /*@ requires true; @*/
    /*@ ensures  bi_big_int(result, CARRY_BITS, false, 0); @*/
    /*@ terminates; @*/

big_int* new_big_int_from(int32_t v);
    /*@ requires true; @*/
    /*@ ensures  bi_big_int(result, CARRY_BITS, false, v); @*/
    /*@ terminates; @*/

void big_int_set(big_int* x,int32_t v);
    /*@ requires bi_big_int(x, _,_,_); @*/
    /*@ ensures  bi_big_int(x, CARRY_BITS, false, v); @*/
    /*@ terminates; @*/

INLINE void big_int_negate(big_int* x)
    /*@ requires bi_big_int(x,?carry,?und,?v); @*/
    /*@ ensures  bi_big_int(x, carry, und,-v); @*/
    /*@ terminates; @*/
{ x->is_pos = !x->is_pos; }

big_int* big_int_clone(const big_int* x);
    /*@ requires [?f]bi_big_int(x,?carry,?under,?v); @*/
    /*@ ensures  [ f]bi_big_int(x, carry, under, v)
            &*&  bi_big_int(result,carry, under, v); @*/
    /*@ terminates; @*/

big_int* big_int_clone_into(big_int* ret,const big_int* x);
    /*@ requires [?f]bi_big_int(x,?carry,?under,?v)
            &*&  bi_big_int(ret,_,_,_); @*/
    /*@ ensures  [ f]bi_big_int(x, carry, under, v)
            &*&  bi_big_int(result,carry, under, v)
            &*&  result == ret; @*/
    /*@ terminates; @*/

big_int* big_int_from_hex(const char* s);
    /*@ requires [?f]string(s,?cs)
            &*&  (safe_head(cs) == some('-')
            ?    base_n(hex_chars(),reverse(tail(cs)),_,?val)
            &*& ensures [ f]string(s, cs)
                   &*&  bi_big_int(result, CARRY_BITS, false, -val)
            :    base_n(hex_chars(),reverse(cs),_,?val)
            &*& ensures [ f]string(s, cs)
                   &*&  bi_big_int(result, CARRY_BITS, false,  val)
            ); @*/
    /*@ ensures  true; @*/
    /*@ terminates; @*/

void free_big_int_inner(big_int* p);
    /*@ requires bi_big_int(p, _, _, _); @*/
    /*@ ensures  true; @*/
    /*@ terminates; @*/

char* big_int_to_hex(const big_int* s);
    /*@ requires [?f]bi_big_int(s, CARRY_BITS, false, ?val); @*/
    /*@ ensures  [ f]bi_big_int(s, CARRY_BITS, false,  val)
            &*&  malloced_string(result,?cs)
            &*&  val == 0
            ?    cs == "0"
            &*&  base_n(hex_chars(),cs,_,val)
            :    val > 0
            ?    base_n(hex_chars(),reverse(cs),?cs_seq,val)
            &*&  !!minimal(cs_seq)
            :    val < 0 &*& safe_head(cs) == some('-')
            &*&  base_n(hex_chars(),reverse(tail(cs)),?cs_seq,-val)
            &*&  !!minimal(cs_seq)
            ; @*/
    /*@ terminates; @*/

void big_int_reduce(big_int* p);
    /*@ requires bi_big_int(p,?carry_bits,?underflow,?v)
            &*&  carry_bits >= 1; @*/
    /*@ ensures  bi_big_int(p,CARRY_BITS,false,v); @*/
    /*@ terminates; @*/

void big_int_pluseq(big_int* a,const big_int* b);
    /*@ requires [?af]bi_big_int(a,?a_carry, ?a_under,?av)
            &*&  [?bf]bi_big_int(b,?b_carry, ?b_under,?bv)
            &*&  a_carry > 1 &*& b_carry > 1
            &*&  a != b
            ?    af == 1 &*& bf > 0
            :    af + bf == 1 &*& af > 0 &*& bf > 0
            ; @*/
    /*@ ensures      bi_big_int(a,min_of(a_carry,b_carry)-1,
                        true, av+bv)
            &*&  a == b ? emp
            :    [ bf]bi_big_int(b, b_carry, b_under, bv); @*/
    /*@ terminates; @*/

big_int* big_int_small_mul(big_int* dst,big_int* scratch,int32_t s,
                           const big_int* x);
    /*@ requires [?f]bi_big_int(x,CARRY_BITS,false,?v)
            &*&  (dst != 0 ? bi_big_int(dst,CARRY_BITS,false,0) : emp)
            &*&  (scratch != 0 ? bi_big_int(scratch,_,_,_) : emp)
            ; @*/
    /*@ ensures  [ f]bi_big_int(x,CARRY_BITS,false, v)
            &*&  bi_big_int(result,CARRY_BITS,false,s*v)
            &*&  (scratch != 0 ? bi_big_int(scratch,_,_,_) : emp)
            ; @*/
    /*@ terminates; @*/

//big_int* big_int_small_mul(/*big_int* dst,*/int32_t s,const big_int* x);
//    /*@ requires [?f]bi_big_int(x,CARRY_BITS,false,?v); @*/
//    /*@ ensures  [ f]bi_big_int(x,CARRY_BITS,false, v)
//            &*&  bi_big_int(result,CARRY_BITS,false,s*v); @*/
//    /*@ terminates; @*/

big_int* big_int_mul(const big_int* x,const big_int* y);
    /*@ requires [?xf]bi_big_int(x,CARRY_BITS,false,?xv)
            &*&  [?yf]bi_big_int(y,CARRY_BITS,false,?yv); @*/
    /*@ ensures  [ xf]bi_big_int(x,CARRY_BITS,false, xv)
            &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
            &*&  bi_big_int(result,CARRY_BITS,false,xv*yv)
            &*&  result != x &*& result != y; @*/
    /*@ terminates; @*/


#endif

