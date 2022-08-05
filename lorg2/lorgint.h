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

// B*(1 + a/b + ... + (a/b)^n)
// B*(1/(1-(a/b))-((a/b)^n/(1-(a/b))))
// B*((1-(a/b)^n)/(1-(a/b)))

lemma void base_conversion(nat m1, nat m2, int b_orig, int b, list<int> limbs, int lo,
        int hi)
    requires !!forall(limbs,(bounded)(lo,hi))
        &*&  b_orig > 1 &*& b > 1
        &*&   pow_nat(b,m1) >= hi
        &*&  -pow_nat(b,m1) <= lo
        &*&  pow_nat(b,m2) >= b_orig
        &*&  hi > 0
        &*&  lo < 0
        ;
    ensures  abs_of(poly_eval(limbs,b_orig))
        <    pow_nat(b,noi(ion(m1) + ion(m2)*length(limbs)));
{
    if(abs_of(poly_eval(limbs,b_orig))
            >= pow_nat(b,noi(ion(m1) + ion(m2)*length(limbs)))) {

        poly_eval_bounded(limbs,lo,hi,b_orig);

        if(poly_eval(repeat(1,noi(length(limbs))),b_orig)
                < 0) {
            int coeff = poly_negative_coeff(repeat(1,
                            noi(length(limbs))), b_orig);
            assert false;
        }

        if(poly_eval(limbs,b_orig)
                >= pow_nat(b,noi(ion(m1)+ion(m2)*length(limbs)))) {



            // <= hi

            assert poly_eval(limbs,b_orig)
                <= poly_eval(repeat(hi,noi(length(limbs))),b_orig);

            poly_eval_repeat_mul(hi,1,noi(length(limbs)),b_orig);

            assert poly_eval(limbs,b_orig)
                <= hi*poly_eval(repeat(1,noi(length(limbs))),b_orig);

            my_mul_mono_l(1,b_orig-1,
                    poly_eval(repeat(1,noi(length(limbs))),b_orig));

            my_mul_mono_r(hi,
                poly_eval(repeat(1,noi(length(limbs))),b_orig),
                (b_orig-1)*
                    poly_eval(repeat(1,noi(length(limbs))),b_orig));

            assert poly_eval(limbs,b_orig)
                <= hi*((b_orig-1)*poly_eval(repeat(1,noi(length(limbs))),b_orig));

            assert poly_eval(limbs,b_orig)
                <= hi*(pow_nat(b_orig,noi(length(limbs)))-1);

            my_mul_strict_mono_r(hi,pow_nat(b_orig,noi(length(limbs)))-1,
                    pow_nat(b_orig,noi(length(limbs))));

            assert poly_eval(limbs,b_orig)
                <  hi*(pow_nat(b_orig,noi(length(limbs))));

            my_mul_mono_l(hi,pow_nat(b,m1),
                    pow_nat(b_orig,noi(length(limbs))));

            assert poly_eval(limbs,b_orig)
                <  pow_nat(b,m1)*(pow_nat(b_orig,noi(length(limbs))));

            pow_base_soft_monotonic(b_orig,pow_nat(b,m2),noi(length(limbs)));
            my_mul_mono_r(pow_nat(b,m1),
                    pow_nat(b_orig,noi(length(limbs))),
                    pow_nat(pow_nat(b,m2),noi(length(limbs))));

            assert poly_eval(limbs,b_orig)
                <  pow_nat(b,m1)*pow_nat(pow_nat(b,m2),noi(length(limbs)));

            pow_times2(b,m2,length(limbs));

            assert poly_eval(limbs,b_orig)
                <  pow_nat(b,m1)*pow_nat(b,noi(ion(m2)*length(limbs)));

            my_mul_mono_l(0,ion(m2),length(limbs));
            pow_plus(b,m1,ion(m2)*length(limbs));

            assert poly_eval(limbs,b_orig)
                <  pow_nat(b,noi(ion(m1)+ion(m2)*length(limbs)));

            assert false;

        } else if(poly_eval(limbs,b_orig)
                <= -pow_nat(b,noi(ion(m1)+ion(m2)*length(limbs)))) {

            // >= lo

            assert poly_eval(limbs,b_orig)
                >= poly_eval(repeat(lo,noi(length(limbs))),b_orig);

            poly_eval_repeat_mul(lo,1,noi(length(limbs)),b_orig);

            assert poly_eval(limbs,b_orig)
                >= lo*poly_eval(repeat(1,noi(length(limbs))),b_orig);

            assert -poly_eval(limbs,b_orig)
                <= (-lo)*poly_eval(repeat(1,noi(length(limbs))),b_orig);

            my_mul_mono_l(1,b_orig-1,
                    poly_eval(repeat(1,noi(length(limbs))),b_orig));

            my_mul_mono_r(-lo,
                poly_eval(repeat(1,noi(length(limbs))),b_orig),
                (b_orig-1)*
                    poly_eval(repeat(1,noi(length(limbs))),b_orig));

            assert -poly_eval(limbs,b_orig)
                <= (-lo)*((b_orig-1)
                        *poly_eval(repeat(1,noi(length(limbs))),b_orig));

            assert -poly_eval(limbs,b_orig)
                <= (-lo)*(pow_nat(b_orig,noi(length(limbs)))-1);

            my_mul_strict_mono_r(-lo,pow_nat(b_orig,noi(length(limbs)))-1,
                    pow_nat(b_orig,noi(length(limbs))));

            assert -poly_eval(limbs,b_orig)
                <  (-lo)*pow_nat(b_orig,noi(length(limbs)));

            my_mul_mono_l(-lo,pow_nat(b,m1),
                    pow_nat(b_orig,noi(length(limbs))));

            assert -poly_eval(limbs,b_orig)
                <  pow_nat(b,m1)*pow_nat(b_orig,noi(length(limbs)));

            pow_base_soft_monotonic(b_orig,pow_nat(b,m2),noi(length(limbs)));
            my_mul_mono_r(pow_nat(b,m1),
                    pow_nat(b_orig,noi(length(limbs))),
                    pow_nat(pow_nat(b,m2),noi(length(limbs))));

            assert -poly_eval(limbs,b_orig)
                <  pow_nat(b,m1)*pow_nat(pow_nat(b,m2),noi(length(limbs)));

            pow_times2(b,m2,length(limbs));

            assert -poly_eval(limbs,b_orig)
                <  pow_nat(b,m1)*pow_nat(b,noi(ion(m2)*length(limbs)));

            my_mul_mono_l(0,ion(m2),length(limbs));
            pow_plus(b,m1,ion(m2)*length(limbs));

            assert -poly_eval(limbs,b_orig)
                <  pow_nat(b,noi(ion(m1)+ion(m2)*length(limbs)));


            assert false;
        }

        assert false;
    }
}

    // poly_eval(limbs,b_orig)
    //  <= hi*poly_eval(repeat(1,noi(length(limbs))),b_orig)
    // (b_orig-1)*poly_eval(repeat(1,noi(length(limbs))),b_orig)
    //  == pow_nat(b_orig,noi(length(limbs))) - 1
    // poly_eval(limbs,b_orig)
    //  <= hi*poly_eval(repeat(1,noi(length(limbs))),b_orig)
    //  <= hi*(b_orig-1)*poly_eval(repeat(1,noi(length(limbs))),b_orig)
    //  <= hi*(pow_nat(b_orig,noi(length(limbs)))-1)
    //  <= hi*(pow_nat(pow_nat(b,m1),noi(length(limbs)))-1)
    //  <= pow_nat(b,m2)*(pow_nat(pow_nat(b,m1),noi(length(limbs)))-1)
    //  <= pow_nat(b,m2)*pow_nat(pow_nat(b,m1),noi(length(limbs)))
    //  <= pow_nat(b,m2)*pow_nat(b,noi(ion(m1)*length(limbs)))
    //  <= pow_nat(b,noi(ion(m2) + ion(m1)*length(limbs)))

    // want m s.t. abs_of(poly_eval(limbs,b_orig))  
    //              <  pow_nat(b,m)

  @*/

lorgint* lorgint_new(int32_t base, int32_t orig_base, int32_t* arr,
        size_t n);
    /*@ requires base > 1 &*&  [?f]arr[..n] |-> ?orig_limbs
            &*&  orig_base > 1; @*/
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
