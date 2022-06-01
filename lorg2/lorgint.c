#include "lorgint.h"
/*@ #include <arrays.gh> @*/
/*@ #include "../div.gh" @*/

#if 0
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() { assume(false); }
#endif

#if 1
#define SKIP_PROOF() {}
#else
#define SKIP_PROOF() { assume(false); }
#endif

static int32_t max32(int32_t x, int32_t y)
    /*@ requires true; @*/
    /*@ ensures  result == max_of(x,y); @*/
    /*@ terminates; @*/
{
    return x > y ? x : y;
}

static int32_t min32(int32_t x, int32_t y)
    /*@ requires true; @*/
    /*@ ensures  result == min_of(x,y); @*/
    /*@ terminates; @*/
{
    return x < y ? x : y;
}

static void euclid_divide(int32_t D, int32_t d, int32_t* q, int32_t* r)
    /*@ requires d > 0 &*& *q |-> _ &*& *r |-> _
            &*&  (euclid_div(D,d) >= -(1<<31) || D/d-1 >= -(1<<31)); @*/
    /*@ ensures  [_]euclid_div_sol(D,d,euclid_div(D,d),euclid_mod(D,d))
            &*&  *q |-> euclid_div(D,d) &*& *r |-> euclid_mod(D,d); @*/
    /*@ terminates; @*/
{
    /*@ {
        div_rem(D,d);
        euclid_div_intro(D,d);
        euclid_div_equiv(D,d);
        div_shrinks(D,d);
    } @*/

    int32_t div = D/d;
    int32_t rem = D%d;
    if(rem < 0) {
        rem += d;
        div -= 1;
    }
    *q = div;
    *r = rem;
}

void lorgint_add_internal(lorgint* dst, lorgint* src)
    /*@ requires     lorgint_view(dst, ?base, ?dst_neg,
                             ?dst_min, ?dst_max, ?dst_start, ?dst_cap,
                             ?dst_limbs, ?dst_v)
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
{
    /*@ ALREADY_PROVEN() @*/

    int32_t* dst_p;
    int32_t* src_p;
    bool subtract = (src->is_negative != dst->is_negative);

    /*@ if(!forall(dst_limbs, (bounded)(tweaked_min,tweaked_max))) {
        int cx = not_forall(dst_limbs, (bounded)(tweaked_min,tweaked_max));
        forall_elim(dst_limbs,(bounded)(dst_min,dst_max),cx);
        assert false;
    } @*/

    /*@ if(!forall(dst_limbs, (bounded)(new_min,new_max))) {
        int cx = not_forall(dst_limbs, (bounded)(new_min,new_max));
        forall_elim(dst_limbs,(bounded)(tweaked_min,tweaked_max),cx);
        assert false;
    } @*/

    int32_t dst_minval = min32(dst->minval,0);
    int32_t dst_maxval = max32(dst->maxval,0);
    /*@ assert dst_minval == tweaked_min; @*/
    /*@ assert dst_maxval == tweaked_max; @*/

    if(subtract) {
        dst->minval = dst_minval - src->maxval;
        dst->maxval = dst_maxval - src->minval;
    } else {
        dst->minval = dst_minval + src->minval;
        dst->maxval = dst_maxval + src->maxval;
    }
    /*@ assert dst->minval |-> combined_min; @*/
    /*@ assert dst->maxval |-> combined_max; @*/

    dst->minval = min32(dst_minval,dst->minval);
    dst->maxval = max32(dst_maxval,dst->maxval);

    /*@ assert dst->minval |-> new_min; @*/
    /*@ assert dst->maxval |-> new_max; @*/

    /*@ int n = 0; @*/

    for(dst_p = dst->start, src_p = src->start;
                src_p < src->end; ++dst_p, ++src_p)
        /*@ requires dst->end |-> ?dst_end
                &*&  dst->size |-> ?dst_size
                &*&  dst_p + dst_size - n == dst_end
                &*&  dst_size <= dst_cap
                &*&  dst_p[..(dst_size-n)] |-> ?l_dst_limbs
                &*&  dst_end[..dst_cap-dst_size] |-> _
                &*&  !!forall(l_dst_limbs,
                        (bounded)(tweaked_min,tweaked_max))
                &*&  !!forall(l_dst_limbs,
                        (bounded)(new_min,new_max))

                &*&  [f]src->end |-> ?src_end
                &*&  [f]src->size |-> ?src_size
                &*&  src_p + src_size - n == src_end
                &*&  [f]src_p[..(src_size-n)] |-> ?l_src_limbs
                &*&  !!forall(l_src_limbs, (bounded)(src_min,src_max))

                &*&  src_size <= dst_cap
                &*&  n >= 0 &*& n <= src_size
                ; @*/
        /*@ ensures  dst->end |-> ?new_end
                &*&  dst->size |-> ?new_size
                &*&  new_size <= dst_cap
                &*&  dst_end + (new_size-dst_size) == new_end
                &*&  old_dst_p[..(new_size-old_n)] |-> ?new_dst_limbs
                &*&  new_end[..dst_cap-new_size] |-> _
                &*&  !!forall(new_dst_limbs,
                        (bounded)(new_min,new_max))

                &*&  [f]src->end |-> src_end
                &*&  [f]src->size |-> src_size
                &*&  [f]old_src_p[..(src_size-old_n)] |-> l_src_limbs

                &*&  subtract
                ?    poly_eval(new_dst_limbs,base)
                     == poly_eval(l_dst_limbs,base)
                        -poly_eval(l_src_limbs,base)
                :    poly_eval(new_dst_limbs,base)
                     == poly_eval(l_dst_limbs,base)
                        +poly_eval(l_src_limbs,base)
                ; @*/
        /*@ decreases src_size - n; @*/
    {
        if(dst_p == dst->end) {
            /*@ assert dst_size - n == 0; @*/
            /*@ assert dst_size < dst_cap; @*/
            /*@ assert dst_end == dst_p; @*/
            /*@ open ints(dst_p,0,nil); @*/
            /*@ ints_limits(dst_end); @*/
            /*@ open ints(dst_end,_,_); @*/
            *dst_p = 0;
            ++dst->end;
            /*@ ++dst->size; @*/

            /*@ note_eq(l_dst_limbs,nil); @*/
            /*@ note_eq(poly_eval(l_dst_limbs,base),poly_eval({0},base)); @*/
        }
        /*@ assert *dst_p |-> ?dst_x; @*/
        /*@ assert [f]*src_p |-> ?src_x; @*/

        if(subtract) {
            *dst_p -= *src_p;
            /*@ assert dst_x - src_x >= new_min; @*/
            /*@ assert dst_x - src_x <= new_max; @*/
        } else {
            *dst_p += *src_p;
            /*@ assert dst_x + src_x >= new_min; @*/
            /*@ assert dst_x + src_x <= new_max; @*/
        }
        /*@ ++n; @*/


        /*@ assert dst->size |-> ?next_size; @*/
        /*@ assert (dst_p+1)[..(next_size-n)] |-> ?next_dst_limbs; @*/
        /*@ assert [f](src_p+1)[..(src_size-n)] |-> ?next_src_limbs; @*/

        /*@ {
            if(!subtract) {
                note_eq( poly_eval(l_src_limbs,base) + poly_eval(l_dst_limbs,base)
                    ,  (dst_x + src_x)
                    +  base*(poly_eval(next_dst_limbs,base)
                            +  poly_eval(next_src_limbs,base)));
            } else {
                note_eq( poly_eval(l_dst_limbs,base) - poly_eval(l_src_limbs,base)
                    ,  (dst_x - src_x)
                    +  base*(poly_eval(next_dst_limbs,base)
                            -  poly_eval(next_src_limbs,base)));
            }
        } @*/
    }
}

/*@
predicate lorgint_reduce_inplace_internal_args(int bound;
    int mmin, int mmax) = bound > 0 &*& mmin == -bound &*& mmax == bound;
@*/

void lorgint_reduce_inplace_internal(lorgint* li)
    /*@ requires lorgint_view(li, ?base, ?neg, ?min, ?max, ?start, ?cap,
                              ?limbs, ?v)
            &*&  lorgint_reduce_inplace_internal_args(?bound,?mmin,?mmax)
            &*&  bound >= base-1
            &*&  mmin <= 0 &*& mmin <= min
            &*&  mmax >= 0 &*& mmax >= max
            &*&  2*mmax + base <  (1<<31)
            &*&  2*mmin - base > -(1<<31)
            &*&  abs_of(v) < pow_nat(base,noi(cap))
            ; @*/
    /*@ ensures  lorgint_view(li,  base, (v < 0), 0, base-1, start,  cap,
                              ?new_limbs, v)
            &*&  !!minimal(new_limbs)
            ; @*/
    /*@ terminates; @*/
{
    /*@ open lorgint_reduce_inplace_internal_args(_,_,_); @*/
    int32_t *p;
    int32_t carry = 0;
    int32_t *non_zero_end = li->start;
    /*@ int minimized_len = 0; @*/
    /*@ list<int> minimized_limbs = nil; @*/
    /*@ list<int> zero_limbs = nil; @*/
    bool negative = false;

    /*@ int len = li->size; @*/
    /*@ int extra_cap = li->capacity - len; @*/
    /*@ int n = 0; @*/
    /*@ euclid_div_sign(1<<31,base); @*/
    /*@ euclid_div_sign(-(1<<31),base); @*/
    /* @ if(2*mmin < -(1<<31)+base) {
        assert false;
    } @*/
    /*@ if(!forall(limbs,(bounded)(mmin,mmax))) {
        int cx = not_forall(limbs,(bounded)(mmin,mmax));
        forall_elim(limbs,(bounded)(min,max),cx);
        assert false;
    } @*/

    li->minval = 0;
    li->maxval = li->base - 1;

    /*@ assert li->start |-> ?orig_p; @*/

    for(p = li->start; p < li->end || carry > 0; ++p)
        /*@ requires p[..len-n] |-> ?l_limbs
                &*&  li->end |-> ?end
                &*&  end[..extra_cap] |-> _
                &*&  li->size |-> len
                &*&  end + extra_cap <= (int32_t*)UINTPTR_MAX
                &*&  len + extra_cap == cap
                &*&  li->base |-> base
                &*&  p + len-n == end
                &*&  0 <= n &*& n <= len
                &*&  carry >= mmin
                &*&  carry <= mmax
                &*&  !!forall(l_limbs,(bounded)(mmin,mmax))
                &*&  !!forall(minimized_limbs,(bounded)(0,base-1))

                &*&  minimized_len == length(minimized_limbs)
                &*&  minimized_len + length(zero_limbs) == n
                &*&  !!poly_is_zero(zero_limbs)
                &*&  !!minimal(minimized_limbs)

                &*&  poly_eval(l_limbs,base) + carry
                <    pow_nat(base,noi(len-n+extra_cap))
                &*&  poly_eval(l_limbs,base) + carry
                >=   -pow_nat(base,noi(len-n+extra_cap))

                &*&  non_zero_end == p + minimized_len-n
                ; @*/
        /*@ ensures  old_p[..(len-old_n)] |-> ?new_limbs
                &*&  li->end |-> ?new_end
                &*&  li->base |-> base
                &*&  old_p + len - old_n == new_end
                &*&  len + extra_cap == cap
                &*&  li->size |-> len
                &*&  new_end[..extra_cap] |-> _

                &*&  minimized_limbs
                == append(old_minimized_limbs,
                minimize(append(old_zero_limbs,new_limbs)))

                &*&  minimized_limbs
                == append(old_minimized_limbs,
                minimize(append(old_zero_limbs,new_limbs)))

                &*&  minimized_len == length(minimized_limbs)

                &*&  non_zero_end == old_p + minimized_len-old_n

                &*&  carry >= mmin
                &*&  carry <= mmax

                &*&  !!forall(new_limbs,(bounded)(0,base-1))
                &*&  !!forall(minimized_limbs,(bounded)(0,base-1))
                &*&  poly_eval(l_limbs,base) + old_carry
                ==   poly_eval(new_limbs,base)
                    + pow_nat(base,noi(length(new_limbs)))*carry

                &*&  (!(l_limbs == nil && old_carry == 0) || carry == 0)
                &*&  length(l_limbs) <= length(new_limbs)
                ; @*/
        /*@ decreases (len+extra_cap)-n; @*/
    {
        int32_t q,r;

        if(p == li->end) {
            /*@ if(extra_cap <= 0) {
                SKIP_PROOF()
                assert len == n;
                assert l_limbs == nil;
                assert len-n+extra_cap == 0;
                note_eq(noi(len-n+extra_cap), zero);
                assert poly_eval(l_limbs,base) + carry == carry;
                assert poly_eval(l_limbs,base) + carry <
                    pow_nat(base,noi(len-n+extra_cap));
                assert poly_eval(l_limbs,base) + carry < pow_nat(base,zero);
                assert poly_eval(l_limbs,base) + carry >= -pow_nat(base,zero);
                assert carry <= 0;
                assert false;
            } @*/
            /*@ --extra_cap; @*/
            /*@ ++len; @*/
            /*@ ++li->size; @*/
            ++li->end;
            *p = 0;
        }

        /*@ int orig_carry = carry; @*/
        /*@ list<int> orig_minimized_limbs = minimized_limbs; @*/
        /*@ list<int> orig_zero_limbs = zero_limbs; @*/
        /*@ assert *p |-> ?val; @*/

        int32_t res = *p + carry;
        carry = 0;

        /*@ {
            int div = res/base;
            assert val >= mmin &*& val <= mmax;
            assert res <  (1<<32);
            assert res > -(1<<32);

            int ediv = euclid_div(res,base);

            if(ediv > mmax || ediv < mmin) {
                    SKIP_PROOF()
                div_rem(res,base);
                euclid_div_equiv(res,base);
                if(res%base < 0) {}

                div_sign(res,base);
                div_negate(res,base);
                div_sign(val+orig_carry,base);

                if(ediv > mmax) {
                    if(val+orig_carry >= 0) {
                        division_unique(2*mmax,2,mmax,0);
                        assert val+orig_carry <= 2*mmax;
                        div_monotonic_numerator(val+orig_carry,2*mmax,base);
                        div_monotonic_denominator(2*mmax,2,base);
                        assert div <= mmax;
                        assert div <= mmax;

                        assert false;
                    }

                    euclid_div_mono_denominator(val+orig_carry,2,base);
                    assert false;
                }

                if(ediv < mmin) {

                    euclid_div_intro(val+orig_carry,base);
                    euclid_div_sign(val+orig_carry,base);

                    euclid_div_intro(val+orig_carry,2);
                    euclid_div_sign(val+orig_carry,2);

                    note_eq(ediv, euclid_div(val+orig_carry,base));
                    note_eq(abs_of(val+orig_carry),-(val+orig_carry));
                    euclid_div_mono_denominator(val+orig_carry,2,base);

                    assert false;
                }

                assert false;
            }

        } @*/

        euclid_divide(res,li->base,&q,&r);
        int32_t div = q;
        int32_t rem = r;

        /*@ {
            if(rem < 0 || rem >= base) assert false;
            if(!bounded(0,base-1,rem)) assert false;
        } @*/

        if(rem != 0) {
            non_zero_end = p+1;
            /*@ {
                minimal_append(zero_limbs,{rem});
                minimal_append(minimized_limbs,append(zero_limbs,{rem}));
                minimized_limbs = append(minimized_limbs,
                    append(zero_limbs,{rem}));
                minimized_len = n+1;
                zero_limbs = nil;

                if(!forall(minimized_limbs,(bounded)(0,base-1))) {
                    SKIP_PROOF()
                    int cx = not_forall(minimized_limbs,
                        (bounded)(0,base-1));
                    if(mem(cx,orig_minimized_limbs)) {
                        forall_elim(orig_minimized_limbs,
                            (bounded)(0,base-1), cx);
                    } else if(mem(cx,orig_zero_limbs)) {
                        all_eq_elim(orig_zero_limbs,0,cx);
                    } else {
                        assert cx == rem;
                    }
                    assert false;
                }
            } @*/
        } else {
            /*@ zero_limbs = append(zero_limbs,{0}); @*/
        }


        *p = rem;
        carry = div;
        /*@ ++n; @*/

        /*@ assert (p+1)[..len-n] |-> ?next_limbs; @*/

        /*@ if(poly_eval(next_limbs,base) + carry
                >= pow_nat(base,noi(len-n+extra_cap))) {
                    SKIP_PROOF()

            if(l_limbs == nil) {
                my_inv_mul_strict_mono_r(base,carry,pow_nat(base,noi(len-n+extra_cap)));

                assert false;
            }

            assert l_limbs == cons(val,next_limbs);

            assert noi(len-n+1+extra_cap) == succ(noi(len-n+extra_cap));

            my_inv_mul_strict_mono_r(base,
                carry + poly_eval(next_limbs,base),
                pow_nat(base,noi(len-n+extra_cap)));

            assert false;
        } @*/

        /*@ if(poly_eval(next_limbs,base) + carry
                < -pow_nat(base,noi(len-n+extra_cap))) {
                    SKIP_PROOF()

            if(l_limbs == nil) {
                my_inv_mul_strict_mono_r(base,-pow_nat(base,noi(len-n+extra_cap))-1,carry);

                assert false;
            }

            assert l_limbs == cons(val,next_limbs);

            assert noi(len-n+1+extra_cap) == succ(noi(len-n+extra_cap));

            my_inv_mul_strict_mono_r(base,
                -pow_nat(base,noi(len-n+extra_cap))-1,
                carry + poly_eval(next_limbs,base));


            assert false;
        } @*/

        /*@ list<int> next_minimized_limbs = minimized_limbs; @*/
        /*@ list<int> next_zero_limbs = zero_limbs; @*/

        /*@ recursive_call(); @*/

        /*@ {

            assert (old_p+1)[..len-old_n-1] |-> ?rest_limbs;
            assert old_p[..len-old_n] |-> ?new_limbs;
            assert length(new_limbs) == 1 + length(rest_limbs);
            assert noi(length(new_limbs)) == succ(noi(length(rest_limbs)));
            note_eq( poly_eval(l_limbs,base) + old_carry
                ,  rem + base*(div + poly_eval(next_limbs,base)));

            note_eq( poly_eval(l_limbs,base) + old_carry
                ,  rem + base*(poly_eval(rest_limbs,base)
                + pow_nat(base,noi(length(rest_limbs)))*carry));

            assert poly_eval(l_limbs,base) + old_carry
                == rem + base*poly_eval(rest_limbs,base)
                + base*(pow_nat(base,noi(length(rest_limbs)))*carry);

            mul_3var(base,pow_nat(base,noi(length(rest_limbs))),carry);

            if(minimized_limbs
                    != append(orig_minimized_limbs,
                        minimize(append(orig_zero_limbs,new_limbs)))) {
                    SKIP_PROOF()
                assert minimized_limbs
                    == append(next_minimized_limbs,
                        minimize(append(next_zero_limbs,rest_limbs)));
                if(rem != 0) {
                    append_assoc(orig_minimized_limbs,
                        append(orig_zero_limbs,{rem}),
                        minimize(rest_limbs));

                    assert minimized_limbs
                        == append(orig_minimized_limbs,
                            append(append(orig_zero_limbs,{rem}),
                                minimize(rest_limbs)));

                    append_assoc(orig_zero_limbs,{rem},minimize(rest_limbs));

                    minimize_append_l({rem}, rest_limbs);
                    minimize_append_r(orig_zero_limbs,
                        cons(rem,rest_limbs));

                    append_assoc(orig_zero_limbs, {rem}, rest_limbs);

                    assert false;

                } else {
                    append_assoc(orig_zero_limbs,{rem},rest_limbs);
                    assert false;
                }
                assert false;
            }

            if(!forall(minimized_limbs,(bounded)(0,base-1))) {
                    SKIP_PROOF()
                int cx = not_forall(minimized_limbs,(bounded)(0,base-1));
                assert !!mem(cx,
                    append(orig_minimized_limbs,
                        minimize(append(orig_zero_limbs,new_limbs))));
                if(mem(cx,orig_minimized_limbs)) {
                    forall_elim(orig_minimized_limbs,(bounded)(0,base-1),cx);
                } else if(mem(cx,orig_zero_limbs)) {
                    all_eq_elim(orig_zero_limbs,0,cx);
                } else {
                    assert !!mem(cx,new_limbs);
                    forall_elim(new_limbs,(bounded)(0,base-1),cx);
                }
                assert false;
            }

        } @*/
    }

    /*@ if(neg && !(v < 0) || !neg && v < 0) {
        if(v == 0) {
            assert start[..len] |-> ?new_limbs;
            assert !!forall(new_limbs,(bounded)(0,base-1));
            poly_eval_bounded_pos(new_limbs,base-1,base);
            assert poly_eval(new_limbs,base) <
                pow_nat(base,noi(length(new_limbs)));
            assert v ==
                poly_eval(new_limbs,base)
                + pow_nat(base,noi(length(new_limbs)))*carry;
            division_zero_unique(
                pow_nat(base,noi(length(new_limbs))),
                carry,
                poly_eval(new_limbs,base));

            assert carry == 0;
        } else if(carry >= 0) {
            assert carry == 0;
            assert start[..len] |-> ?new_limbs;
            assert !!forall(new_limbs,(bounded)(0,base-1));
            poly_eval_bounded_pos(new_limbs,base-1,base);
            assert poly_eval(new_limbs,base) >= 0;
            if(neg) { assert false; } else { assert false; }

            assert false;
        }
        note((v == 0 && carry == 0) || carry < 0);
    } @*/

    if(carry < 0) {
        /*@ {
            n = 0;
            minimized_limbs = nil;
            zero_limbs = nil;
            minimized_len = 0;

            assert start[..len-n] |-> ?init_limbs;

            if(poly_eval(init_limbs,base)
                    + pow_nat(base,noi(length(init_limbs)))
                        *carry >= 0) {
                neg_most_sig(init_limbs,base,{carry});
                assert false;
            }

            if(init_limbs == nil) {
                assert limbs == nil;
                assert carry == 0;
                assert false;
            }
        } @*/

        int32_t final_carry = -carry;
        carry = 0;
        li->is_negative = !li->is_negative;
        non_zero_end = li->start;

        for(p = li->start; p < li->end || carry > 0; ++p)
            /*@ requires p[..len-n] |-> ?l_limbs
                    &*&  li->end |-> ?end
                    &*&  end[..extra_cap] |-> _
                    &*&  li->size |-> len
                    &*&  end + extra_cap <= (int32_t*)UINTPTR_MAX
                    &*&  len + extra_cap == cap
                    &*&  li->base |-> base
                    &*&  p + len-n == end
                    &*&  0 <= n &*& n <= len
                    &*&  (carry + final_carry) >= -1
                    &*&  (carry + final_carry) <= -mmin
                    &*&  !!forall(l_limbs,(bounded)(0,base-1))
                    &*&  !!forall(minimized_limbs,(bounded)(0,base-1))
                    &*&  (final_carry == 0 || (-1 <= carry && carry <= 0))
                    &*&  final_carry >= 0
                    &*&  final_carry <= -mmin

                    &*&  minimized_len == length(minimized_limbs)
                    &*&  minimized_len + length(zero_limbs) == n
                    &*&  !!poly_is_zero(zero_limbs)
                    &*&  !!minimal(minimized_limbs)

                    &*&  -poly_eval(l_limbs,base) + carry
                         + pow_nat(base,noi(length(l_limbs)))*final_carry
                    <    pow_nat(base,noi(len-n+extra_cap))
                    &*&  -poly_eval(l_limbs,base) + carry
                         + pow_nat(base,noi(length(l_limbs)))*final_carry
                    >=   0

                    &*&  (l_limbs != nil || final_carry == 0)

                    &*&  non_zero_end == p + minimized_len-n
                    ; @*/
            /*@ ensures  old_p[..(len-old_n)] |-> ?new_limbs
                    &*&  li->end |-> ?new_end
                    &*&  li->base |-> base
                    &*&  old_p + len - old_n == new_end
                    &*&  len + extra_cap == cap
                    &*&  li->size |-> len
                    &*&  new_end[..extra_cap] |-> _

                    &*&  minimized_limbs
                    == append(old_minimized_limbs,
                    minimize(append(old_zero_limbs,new_limbs)))

                    &*&  minimized_len == length(minimized_limbs)

                    &*&  non_zero_end == old_p + minimized_len-old_n

                    &*&  carry == 0

                    &*&  !!forall(new_limbs,(bounded)(0,base-1))
                    &*&  !!forall(minimized_limbs,(bounded)(0,base-1))
                    &*&  -poly_eval(l_limbs,base) + old_carry
                         + pow_nat(base,noi(length(l_limbs)))*old_final_carry
                    ==   poly_eval(new_limbs,base)
                    ; @*/
            /*@ decreases len+extra_cap-n; @*/
        {
            int32_t q,r;

            if(p == li->end) {
                /*@ if(extra_cap <= 0) {
                    SKIP_PROOF()
                    assert len == n;
                    assert l_limbs == nil;
                    assert len-n+extra_cap == 0;
                    note_eq(noi(len-n+extra_cap), zero);
                    assert poly_eval(l_limbs,base) + carry == carry;
                    assert poly_eval(l_limbs,base) + carry <
                        pow_nat(base,noi(len-n+extra_cap));
                    assert poly_eval(l_limbs,base) + carry < pow_nat(base,zero);
                    assert poly_eval(l_limbs,base) + carry >= -pow_nat(base,zero);
                    assert carry <= 0;
                    assert false;
                } @*/
                /*@ --extra_cap; @*/
                /*@ ++len; @*/
                /*@ ++li->size; @*/
                ++li->end;
                *p = 0;
            }

            /*@ int orig_carry = carry; @*/
            /*@ int orig_final_carry = final_carry; @*/
            /*@ list<int> orig_minimized_limbs = minimized_limbs; @*/
            /*@ list<int> orig_zero_limbs = zero_limbs; @*/
            /*@ assert *p |-> ?val; @*/

            /*@ {
                if(-val + carry > 2*bound) {
                    SKIP_PROOF()
                    assert -val <= 0;
                    assert -val + carry <= carry;
                    assert -val + carry <= -mmin - final_carry;
                    assert -val + carry <= -mmin + mmax;
                    assert false;
                }

                if(-val + carry < -bound - base) {
                    SKIP_PROOF()
                    assert -val >= -base+1;
                    assert -val + carry >= carry-base+1;
                    assert -val + carry >= -bound - 1 - base + 1;
                    assert -val + carry >= -bound - 1 - base + 1;
                    assert -val + carry >= -bound - base;

                    assert -val + carry > -(1<<31);
                    assert false;
                }
            } @*/

            int32_t res = -(*p) + carry;
            carry = 0;

            /*@ {
                int ediv = euclid_div(res,base);
                int emod = euclid_mod(res,base);
                euclid_div_intro(res,base);
                assert val >= 0 &*& val <= base-1;

                if(!(final_carry == 0 || (-1 <= ediv && ediv <= 0))) {
                    SKIP_PROOF()
                    assert final_carry != 0;
                    assert -1 <= orig_carry &*& orig_carry <= 0;
                    assert res >= -base &*& res <= 0;
                    euclid_div_sign(res,base);
                    assert base*ediv < res;
                    assert base*ediv < res;
                    if(ediv < -1) {
                        my_mul_strict_mono_r(base,ediv,-1);
                        assert base*ediv < -base;
                        assert false;
                    } else if(ediv > 0) {
                        my_mul_strict_mono_r(base,0,ediv);
                    }
                    assert false;
                }

                if(ediv > mmax || ediv < -1) {
                    SKIP_PROOF()
                    div_rem(res,base);
                    euclid_div_equiv(res,base);
                    if(res%base < 0) {}

                    div_sign(res,base);
                    div_negate(res,base);
                    div_sign(val+orig_carry,base);

                    if(ediv > mmax) {
                        if(-val+orig_carry >= 0) {
                            division_unique(2*mmax,2,mmax,0);
                            assert -val+orig_carry <= 2*mmax;
                            div_monotonic_numerator(-val+orig_carry,2*mmax,base);
                            div_monotonic_denominator(2*mmax,2,base);
                            assert div <= mmax;
                            assert div <= mmax;

                            assert false;
                        }

                        euclid_div_mono_denominator(-val+orig_carry,2,base);
                        assert false;
                    }

                    if(ediv < -1) {
                        assert -val + orig_carry >= -base;

                        assert base*ediv + emod == -val + orig_carry;

                        assert base*ediv + emod >= -base;
                        my_mul_mono_r(base,ediv,-2);
                        assert false;
                    }

                    assert false;
                }
            } @*/

            euclid_divide(res,li->base,&q,&r);
            int32_t div = q;
            int32_t rem = r;

            /*@ {
                if(rem < 0 || rem >= base) assert false;
                assume(bounded(0,base-1,rem));
                if(!bounded(0,base-1,rem)) assert false;
            } @*/

            if(rem != 0) {
                non_zero_end = p+1;
                /*@ {
                    minimal_append(zero_limbs,{rem});
                    minimal_append(minimized_limbs,append(zero_limbs,{rem}));
                    minimized_limbs = append(minimized_limbs,
                        append(zero_limbs,{rem}));
                    minimized_len = n+1;
                    zero_limbs = nil;

                    if(!forall(minimized_limbs,(bounded)(0,base-1))) {
                        SKIP_PROOF()
                        int cx = not_forall(minimized_limbs,
                            (bounded)(0,base-1));
                        if(mem(cx,orig_minimized_limbs)) {
                            forall_elim(orig_minimized_limbs,
                                (bounded)(0,base-1), cx);
                        } else if(mem(cx,orig_zero_limbs)) {
                            all_eq_elim(orig_zero_limbs,0,cx);
                        } else {
                            assert cx == rem;
                        }
                        assert false;
                    }
                } @*/
            } else {
                /*@ zero_limbs = append(zero_limbs,{0}); @*/
            }

            *p = rem;
            carry = div;

            if(p+1 == li->end) {
                /*@ {
                    note(length(l_limbs) <= 1);
                    note_eq(poly_eval(l_limbs,base), val);
                    assert (p+1)[..len-(n+1)] |-> ?rest_limbs;
                    assert rest_limbs == nil;
                    if(div + final_carry
                            >= pow_nat(base,noi(len-(n+1)+extra_cap))) {
                SKIP_PROOF()
                        assert -poly_eval(l_limbs,base) + orig_carry
                            +  pow_nat(base,noi(1))*final_carry
                            <  pow_nat(base,noi(len-n+extra_cap));
                        assert rem + base*div + base*final_carry
                            <  pow_nat(base,noi(len-n+extra_cap));
                        assert rem + base*(div + final_carry)
                            <  pow_nat(base,noi(len-n+extra_cap));
                        assert noi(len-n+extra_cap)
                            == succ(noi(len-n-1+extra_cap));
                        assert rem + base*(div + final_carry)
                            <  base*pow_nat(base,noi(len-(n+1)+extra_cap));
                        assert base*(div + final_carry)
                            <  base*pow_nat(base,noi(len-(n+1)+extra_cap));
                        my_inv_mul_strict_mono_r(base,div+final_carry,
                            pow_nat(base,noi(len-(n+1)+extra_cap)));
                        assert false;
                    }

                    if(div + final_carry < 0) {
                SKIP_PROOF()
                        assert len-(n+1) == 0;

                        assert rem + base*(div + final_carry) >= 0;
                        my_mul_mono_r(base,div+final_carry,-1);
                        assert false;
                    }

                } @*/

                /*@ if(final_carry == 0) {
                    assert final_carry + carry == carry;
                } else {
                    assert carry >= -1;
                    assert carry <= 0;
                } @*/

                carry += final_carry;
                final_carry = 0;
            } else {
                /*@ if(length(l_limbs) <= 1) {
                    assert false;
                } @*/
            }

            /*@ ++n; @*/

            /*@ assert (p+1)[..len-n] |-> ?next_limbs; @*/

            /*@ if(-poly_eval(next_limbs,base) + carry
                         + pow_nat(base,noi(length(next_limbs)))*final_carry
                    >=   pow_nat(base,noi(len-n+extra_cap))) {
                SKIP_PROOF()

                if(l_limbs == nil) {
                    my_inv_mul_strict_mono_r(base,carry + final_carry,
                        pow_nat(base,noi(len-n+extra_cap)));

                    assert false;
                }

                assert l_limbs == cons(val,next_limbs);

                assert noi(len-n+1+extra_cap) == succ(noi(len-n+extra_cap));
                assert noi(length(l_limbs)) == succ(noi(length(next_limbs)));

                my_inv_mul_strict_mono_r(base,
                    carry - poly_eval(next_limbs,base)
                    + pow_nat(base,noi(length(next_limbs)))*final_carry,
                    pow_nat(base,noi(len-n+extra_cap)));

                assert false;
            } @*/

            /*@ if(-poly_eval(next_limbs,base) + carry
                         + pow_nat(base,noi(length(next_limbs)))*final_carry
                    < 0) {
                SKIP_PROOF()

                if(l_limbs == nil) {
                    my_inv_mul_strict_mono_r(base,0,carry + final_carry);

                    assert false;
                }

                assert l_limbs == cons(val,next_limbs);

                assert noi(len-n+1+extra_cap) == succ(noi(len-n+extra_cap));
                assert noi(length(l_limbs)) == succ(noi(length(next_limbs)));

                assert -poly_eval(l_limbs,base) + orig_carry
                         + pow_nat(base,noi(length(l_limbs)))*final_carry
                    >= 0;

                assert rem + base*carry
                         + pow_nat(base,noi(length(l_limbs)))*final_carry
                    >= 0;
                assert rem + base*carry
                    - base*poly_eval(next_limbs,base)
                         + pow_nat(base,noi(length(l_limbs)))*final_carry
                    >= 0;

                assert base*(1 + carry
                    - poly_eval(next_limbs,base)
                         +
                         pow_nat(base,noi(length(next_limbs)))*final_carry)
                    > 0;

                my_inv_mul_strict_mono_r(base,
                    0,
                    1+carry - poly_eval(next_limbs,base)
                    + pow_nat(base,noi(length(next_limbs)))*final_carry);


                assert false;
            } @*/


            /*@ list<int> next_minimized_limbs = minimized_limbs; @*/
            /*@ list<int> next_zero_limbs = zero_limbs; @*/
            /*@ int next_final_carry = final_carry; @*/
            /*@ int next_carry = carry; @*/

            /*@ recursive_call(); @*/

            /*@ {

                assert (old_p+1)[..len-old_n-1] |-> ?rest_limbs;
                assert old_p[..len-old_n] |-> ?new_limbs;
                assert length(new_limbs) == 1 + length(rest_limbs);
                assert noi(length(new_limbs)) == succ(noi(length(rest_limbs)));
                mul_3var(base,pow_nat(base,noi(length(next_limbs))),next_final_carry);

                assert -poly_eval(next_limbs,base) + next_carry
                    + pow_nat(base,noi(length(next_limbs)))
                        *next_final_carry
                    == poly_eval(rest_limbs,base);

                if(-poly_eval(l_limbs,base) + orig_carry
                    +  pow_nat(base,noi(length(l_limbs)))*orig_final_carry
                    !=  rem + base*(next_carry - poly_eval(next_limbs,base)
                    +  pow_nat(base,noi(length(next_limbs)))*next_final_carry
                        )) {
                    SKIP_PROOF()

                    if(length(l_limbs) <= 1) {
                        assert next_final_carry == 0;
                        assert next_carry == div + orig_final_carry;
                        assert -poly_eval(l_limbs,base) + orig_carry
                            + pow_nat(base,noi(length(l_limbs)))
                                *orig_final_carry
                            == rem + base*div + base*orig_final_carry;
                        assert next_limbs == nil;
                        assert false;
                    } else {
                        assert next_final_carry == orig_final_carry;
                        assert next_carry == div;
                        assert succ(noi(length(next_limbs)))
                            == noi(length(l_limbs));
                        mul_3var(base,
                            pow_nat(base,noi(length(next_limbs))),
                            orig_final_carry);
                        assert -poly_eval(l_limbs,base) + orig_carry
                            + pow_nat(base,noi(length(l_limbs)))
                                *orig_final_carry
                            == rem + base*div
                            - base*poly_eval(next_limbs,base)
                            + base*(pow_nat(base,noi(length(next_limbs)))
                                    *orig_final_carry);
                        assert false;
                    }

                    assert false;
                }

                note_eq(-poly_eval(l_limbs,base) + orig_carry
                    +  pow_nat(base,noi(length(l_limbs)))*orig_final_carry
                    ,  rem + base*(next_carry - poly_eval(next_limbs,base)
                    +  pow_nat(base,noi(length(next_limbs)))*next_final_carry
                    ));

                note_eq(-poly_eval(l_limbs,base) + orig_carry
                    +  pow_nat(base,noi(length(l_limbs)))*orig_final_carry
                    ,  rem + base*poly_eval(rest_limbs,base)
                    );

                if(minimized_limbs
                        != append(orig_minimized_limbs,
                            minimize(append(orig_zero_limbs,new_limbs)))) {
                    SKIP_PROOF()
                    assert minimized_limbs
                        == append(next_minimized_limbs,
                            minimize(append(next_zero_limbs,rest_limbs)));
                    if(rem != 0) {
                        append_assoc(orig_minimized_limbs,
                            append(orig_zero_limbs,{rem}),
                            minimize(rest_limbs));

                        assert minimized_limbs
                            == append(orig_minimized_limbs,
                                append(append(orig_zero_limbs,{rem}),
                                    minimize(rest_limbs)));

                        append_assoc(orig_zero_limbs,{rem},minimize(rest_limbs));

                        minimize_append_l({rem}, rest_limbs);
                        minimize_append_r(orig_zero_limbs,
                            cons(rem,rest_limbs));

                        append_assoc(orig_zero_limbs, {rem}, rest_limbs);

                        assert false;

                    } else {
                        append_assoc(orig_zero_limbs,{rem},rest_limbs);
                        assert false;
                    }
                    assert false;
                }

                if(!forall(minimized_limbs,(bounded)(0,base-1))) {
                    SKIP_PROOF()
                    int cx = not_forall(minimized_limbs,(bounded)(0,base-1));
                    assert !!mem(cx,
                        append(orig_minimized_limbs,
                            minimize(append(orig_zero_limbs,new_limbs))));
                    if(mem(cx,orig_minimized_limbs)) {
                        forall_elim(orig_minimized_limbs,(bounded)(0,base-1),cx);
                    } else if(mem(cx,orig_zero_limbs)) {
                        all_eq_elim(orig_zero_limbs,0,cx);
                    } else {
                        assert !!mem(cx,new_limbs);
                        forall_elim(new_limbs,(bounded)(0,base-1),cx);
                    }
                    assert false;
                }

            } @*/
        }
    }

    li->end = non_zero_end;
    /*@ li->size = minimized_len; @*/
    /*@ assert start[..len] |-> ?new_limbs; @*/
    /*@ ints_split(start,minimized_len); @*/
    /*@ minimize_is_prefix(new_limbs); @*/
    /*@ assert start[..minimized_len] |-> minimized_limbs; @*/
    /*@ assert start+minimized_len == non_zero_end; @*/
    /*@ ints_join(non_zero_end); @*/

    /*@ if(v == 0 && non_zero_end != start) {
        assert poly_eval(new_limbs,base) == 0;
        assert minimize(new_limbs) != nil;
        int cx = poly_positive_zero(new_limbs,base);
        forall_elim(new_limbs,(bounded)(0,base-1),cx);
        assert false;
    } @*/

    if(non_zero_end == li->start) {
        /*@ assert v == 0; @*/
        li->is_negative = false;
    }

}

