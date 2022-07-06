#ifndef VFSTUFF_LORGINT_H
#define VFSTUFF_LORGINT_H

#include <stdint.h>
#include <stdlib.h>

/*@ #include "../util.gh" @*/
/*@ #include "../poly.gh" @*/
/*@ #include "../div.gh" @*/

typedef struct lorgint_t {
    bool    is_negative;
    int32_t base;
    int32_t minval;
    int32_t maxval;
    /* needed because verifast doesn't support subtracting pointers */
    /*@ int  size; @*/
    /*@ int  capacity; @*/
    int32_t *start;
    int32_t *end;
    int32_t *cap;
} lorgint;

/*@

predicate lorgint_view(lorgint* li;
        int base, bool is_negative, int minval, int maxval,
        int32_t* start, int capacity,
        list<int> limbs, int val)
    =   li->base |-> base &*& li->minval |-> minval
    &*& li->maxval |-> maxval
    &*& li->start |-> start &*& li->end |-> ?end &*& li->cap |-> ?cap
    &*& li->is_negative |-> is_negative
    &*& li->size |-> ?size
    &*& li->capacity |-> capacity
    &*& start > 0 &*& start <= end &*& end <= cap
    &*& start + size == end &*& start+capacity == cap
    &*& start[..size] |-> limbs
    &*& end[..capacity-size] |-> _
    &*& base > 2 &*& minval >= -(1<<31) &*& maxval < (1<<31)
    &*& 2*base < (1<<31)
    &*& minval <= maxval
    &*& !!forall(limbs,(bounded)(minval,maxval))
    &*& val == (is_negative
            ? -poly_eval(limbs,base) : poly_eval(limbs,base))
    ;

predicate lorgint_malloced(lorgint* li;
        int base, bool is_negative, int minval, int maxval,
        int32_t* start, int cap,
        list<int> limbs, int val)
    =   lorgint_view(li,base,is_negative,minval,maxval,start,cap,limbs,val)
    &*& malloc_block_ints(start,cap)
    ;

  @*/

lorgint* lorgint_new(int32_t base, int32_t orig_base, int32_t* arr,
        size_t n);
    /*@ requires base > 2 &*&  [?f]arr[..n] |-> ?orig_limbs; @*/
    /*@ ensures  lorgint_malloced(result, base, ?neg, 0, base-1, _, _,
                    ?limbs, ?val)
            &*&  val == poly_eval(orig_limbs, orig_base)
            &*&  neg == (val < 0)
            &*&  [f]arr[..n] |-> orig_limbs
            &*&  !!minimal(limbs); @*/
    /*@ terminates; @*/

void lorgint_add_internal(lorgint* dst, lorgint* src);
    /*@ requires     lorgint_view(dst, ?base, ?dst_neg,
                             ?dst_min, ?dst_max, ?dst_start, ?dst_cap, _,
                             ?dst_v)
            &*&  [?f]lorgint_view(src,  base, ?src_neg, ?src_min, ?src_max,
                             ?src_start, ?src_cap, ?src_limbs, ?src_v)
            &*&  dst_cap >= length(src_limbs)
            &*&  let(max_of(0,dst_max), ?tweaked_max)
            &*&  let(min_of(0,dst_min), ?tweaked_min)
            &*&  let(dst_neg == src_neg ? tweaked_max + src_max
                                        : tweaked_max - src_min,
                     ?combined_max)
            &*&  let(dst_neg == src_neg ? tweaked_min + src_min
                                        : tweaked_min - src_max,
                     ?combined_min)
            &*&  let(max_of(combined_max,tweaked_max),?new_max)
            &*&  let(min_of(combined_min,tweaked_min),?new_min)
            &*&  new_max < (1<<31) &*& new_min > -(1<<31)
            ; @*/
    /*@ ensures      lorgint_view(dst,  base, dst_neg, new_min, new_max,
                              dst_start,  dst_cap, _,
                              src_v+dst_v)
            &*&  [ f]lorgint_view(src,  base,  src_neg,  src_min,  src_max,
                              src_start,  src_cap,  src_limbs,  src_v)
            ; @*/
    /*@ terminates; @*/

void lorgint_reduce_inplace(lorgint* li);
    /*@ requires lorgint_view(li, ?base, ?neg, ?min, ?max, ?start, ?cap, _,
                              ?v)
            &*&  abs_of(v) < pow_nat(base,nat_of_int(cap))
            ; @*/
    /*@ ensures  lorgint_view(li,  base, (v < 0), 0, base-1, start,  cap,
                     ?limbs, v)
            &*&  !!minimal(limbs)
            ; @*/
    /*@ terminates; @*/


#endif
