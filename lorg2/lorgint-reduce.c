#include "lorgint.h"
#include "common.h"
/*@ #include "../bitops.gh" @*/

void lorgint_reduce_inplace(lorgint* li)
    /*@ requires lorgint_view(li, ?base, ?neg, ?min, ?max, ?start, ?cap,
                              ?limbs, ?v)
            &*&  abs_of(v) < pow_nat(base,noi(cap))
            ; @*/
    /*@ ensures  lorgint_view(li,  base, (v < 0), 0, base-1, start,  cap,
                              ?new_limbs, v)
            &*&  !!minimal(new_limbs)
            ; @*/
    /*@ terminates; @*/
{
    int32_t *p;
    int64_t carry = 0;
    int32_t *non_zero_end = li->start;

    /*@ int len = li->size; @*/
    /*@ int extra_cap = li->capacity - len; @*/
    /*@ int n = 0; @*/
    /*@ int minimized_len = 0; @*/
    /*@ list<int> minimized_limbs = nil; @*/
    /*@ list<int> zero_limbs = nil; @*/

    li->minval = 0;
    li->maxval = li->base - 1;

    for(p = li->start; p < li->end || carry > 0; ++p)
        /*@ invariant start[..n] |-> ?pref_limbs
                &*&   pref_limbs == append(minimized_limbs,zero_limbs)
                &*&   start[n..len] |-> ?l_limbs
                &*&   start+n == p
                &*&   li->end |-> ?end
                &*&   end[..extra_cap] |-> _
                &*&   li->size |-> len
                &*&   end + extra_cap <= (int32_t*)UINTPTR_MAX

                &*&   len + extra_cap == cap
                &*&   li->base |-> base
                &*&   p + len-n == end
                &*&   0 <= n &*& n <= len

                &*&   !!forall(minimized_limbs,(bounded)(0,base-1))
                &*&   !!forall(pref_limbs,(bounded)(0,base-1))

                &*&   minimized_len == length(minimized_limbs)
                &*&   minimized_len + length(zero_limbs) == n
                &*&   !!poly_is_zero(zero_limbs)
                &*&   !!minimal(minimized_limbs)

                &*&   poly_eval(l_limbs,base) + carry
                <     pow_nat(base,noi(len-n+extra_cap))
                &*&   poly_eval(l_limbs,base) + carry
                >=    -pow_nat(base,noi(len-n+extra_cap))

                &*&   poly_eval(limbs,base)
                ==    poly_eval(
                        append(append(minimized_limbs,zero_limbs),l_limbs),
                        base)
                    + pow_nat(base,noi(n))*carry

                &*&   non_zero_end == p + minimized_len-n

                &*&   carry <=  (1<<32)
                &*&   carry >= -(1<<32)

                &*&   length(pref_limbs) + length(l_limbs) >= length(limbs)
                ; @*/
        /*@ decreases (len+extra_cap)-n; @*/
    {
        /*@ if(n == len) open ints(start+n,len-n,_); @*/
        /*@ open ints(p,_,_); @*/
        int64_t q;
        int32_t r;

        if(p == li->end) {
            /*@ if(extra_cap <= 0) { assert false; } @*/
            /*@ --extra_cap; @*/
            /*@ ++len; @*/
            /*@ ++li->size; @*/
            ++li->end;
            *p = 0;
        }

        /*@ int orig_carry = carry; @*/
        /*@ list<int> orig_minimized_limbs = minimized_limbs; @*/
        /*@ list<int> orig_zero_limbs = zero_limbs; @*/
        /*@ int orig_n = n; @*/
        /*@ assert *p |-> ?val; @*/
        /*@ {
            if(val > (1<<31) || val < -(1<<31)) {
                integer_limits(p);
                assert false;
            }
        } @*/

        int64_t res = *p + carry;
        carry = 0;

        euclid_divide_64_32(res,li->base,&q,&r);
        int64_t div = q;
        int32_t rem = r;

        *p = rem;
        carry = div;
        /*@ ++n; @*/

        /*@ assert (p+1)[..len-n] |-> ?next_limbs; @*/

        /*@ if(carry > (1<<32) || carry < -(1<<32)) {
            assert base*carry + rem == val + orig_carry;
            if(carry > (1<<32)) {
                my_mul_mono_l(2,base,carry);
                assert false;
            } else {
                my_mul_mono_l(2,base,-carry);
                assert false;
            }
            assert false;
        } @*/

        /*@ if(poly_eval(next_limbs,base) + carry
                >= pow_nat(base,noi(len-n+extra_cap))) {

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


        if(rem != 0) {
            non_zero_end = p+1;

            /*@ {
                minimal_append(zero_limbs,{rem});
                minimal_append(minimized_limbs,append(zero_limbs,{rem}));
                minimized_limbs = append(minimized_limbs,
                    append(zero_limbs,{rem}));
                minimized_len = n;
                zero_limbs = nil;

                if(!forall(minimized_limbs,(bounded)(0,base-1))) {
                    int cx = not_forall(minimized_limbs,
                        (bounded)(0,base-1));
                    if(mem(cx,orig_minimized_limbs)) {
                        forall_elim(orig_minimized_limbs,
                            (bounded)(0,base-1), cx);
                    } else if(mem(cx,orig_zero_limbs)) {
                        all_eq_elim(orig_zero_limbs,0,cx);
                    }
                    assert false;
                }

            } @*/
        } else {
            /*@ zero_limbs = append(zero_limbs,{0}); @*/
            /*@ forall_append(append(orig_minimized_limbs,orig_zero_limbs),{0},
                    (bounded)(0,base-1)); @*/
        }
        /*@ append_assoc(orig_minimized_limbs,orig_zero_limbs,{rem}); @*/

        /*@ close ints(p,1,_); @*/
        /*@ ints_join(start); @*/

        /*@ {

            note_eq( poly_eval(limbs,base)
                ,  poly_eval(
                    append(orig_minimized_limbs,orig_zero_limbs),base)
                + pow_nat(base,noi(orig_n))
                    *(poly_eval(l_limbs, base) + orig_carry));

            note_eq( poly_eval(limbs,base)
                ,  poly_eval(
                    append(orig_minimized_limbs,orig_zero_limbs),base)
                +  pow_nat(base,noi(orig_n))
                    *(rem + base*div + base*poly_eval(next_limbs, base)));

            mul_3var(pow_nat(base, noi(orig_n)), base,
                div+poly_eval(next_limbs, base));

            note_eq(pow_nat(base,noi(orig_n))
                    *(rem + base*div + base*poly_eval(next_limbs, base))
                ,  pow_nat(base,noi(orig_n))
                    *(rem + base*(div + poly_eval(next_limbs, base))));

        } @*/

    }

    /*@ assert n == len; @*/
    /*@ open ints(start+n,0,_); @*/

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

            if(v == 0) assert false;

            if(init_limbs == nil) assert false;
        } @*/

        int64_t final_carry = -carry;
        carry = 0;
        li->is_negative = !li->is_negative;
        non_zero_end = li->start;

        for(p = li->start; p < li->end || carry > 0; ++p)
            /*@ invariant start[..n] |-> ?pref_limbs
                    &*&   pref_limbs == append(minimized_limbs,zero_limbs)
                    &*&   start[n..len] |-> ?l_limbs
                    &*&   start+n == p
                    &*&   li->end |-> ?end
                    &*&   end[..extra_cap] |-> _
                    &*&   li->size |-> len
                    &*&   end + extra_cap <= (int32_t*)UINTPTR_MAX

                    &*&   len + extra_cap == cap
                    &*&   li->base |-> base
                    &*&   p + len-n == end
                    &*&   0 <= n &*& n <= len

                    &*&   !!forall(l_limbs,(bounded)(0,base-1))
                    &*&   !!forall(minimized_limbs,(bounded)(0,base-1))

                    &*&   minimized_len == length(minimized_limbs)
                    &*&   minimized_len + length(zero_limbs) == n
                    &*&   !!poly_is_zero(zero_limbs)
                    &*&   !!minimal(minimized_limbs)

                    &*&  -poly_eval(l_limbs,base) + carry
                         + pow_nat(base,noi(length(l_limbs)))*final_carry
                    <    pow_nat(base,noi(len-n+extra_cap))
                    &*&  -poly_eval(l_limbs,base) + carry
                         + pow_nat(base,noi(length(l_limbs)))*final_carry
                    >=   0

                    &*&   non_zero_end == p + minimized_len-n

                    &*&  poly_eval(pref_limbs,base)
                         + pow_nat(base,noi(n))
                            *(-poly_eval(l_limbs,base) + carry)
                         + pow_nat(base,noi(len))*final_carry
                    ==   -poly_eval(limbs,base)

                    &*&  (l_limbs != nil || final_carry == 0)
                    &*&  (p == end || final_carry != 0)
                    &*&  (p < end || carry > 0 || final_carry == 0)

                    &*&  carry >= -1
                    &*&  (carry + final_carry) <= (1<<32)
                    &*&  final_carry <= (1<<32)
                    &*&  final_carry >= 0
                    &*&  (final_carry != 0 || carry >= 0)
                    &*&  (final_carry == 0 || -1 <= carry)
                    &*&  (final_carry == 0 || carry <= 0)

                    &*&   length(pref_limbs) + length(l_limbs) >= length(limbs)
                    ; @*/

            /*@ decreases len+extra_cap-n; @*/
        {
            /*@ if(n == len) open ints(start+n,len-n,_); @*/
            /*@ open ints(p,_,_); @*/
            int64_t q;
            int32_t r;

            if(p == li->end) {
                /*@ if(extra_cap <= 0) { assert false; } @*/
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
            /*@ int orig_n = n; @*/
            /*@ assert *p |-> ?val; @*/

            int64_t res = -(int64_t)(*p) + carry;
            carry = 0;

            /*@ {
                int ediv = euclid_div(res,base);
                int emod = euclid_mod(res,base);
                euclid_div_intro(res,base);
                assert val >= 0 &*& val <= base-1;

                if(!(final_carry == 0 || (-1 <= ediv && ediv <= 0))) {
                    euclid_div_sign(res,base);
                    if(ediv < -1) {
                        my_mul_mono_r(base,ediv,-2);
                        assert false;
                    }
                    assert false;
                }

                if(ediv > (1<<32) || ediv < -1) {
                    assert res == -val + orig_carry;

                    assert res <= (1<<32);
                    assert base*ediv + emod <= (1<<32);

                    if(ediv > (1<<32)) {
                        my_mul_strict_mono_l(1,base,(1<<32));
                        my_mul_strict_mono_r(base,(1<<32),ediv);

                        assert false;
                    }

                    if(ediv < -1) {
                        assert base*ediv + emod >= -base;
                        assert base*ediv > -2*base;
                        my_mul_mono_r(base,ediv,-2);
                        assert false;
                    }

                    assert false;
                }
            } @*/

            euclid_divide_64_32(res,li->base,&q,&r);
            int64_t div = q;
            int32_t rem = r;

            *p = rem;
            carry = div;


            if(p+1 == li->end && final_carry > 0) {
                /*@ {
                    note(length(l_limbs) <= 1);
                    note_eq(poly_eval(l_limbs,base), val);



                    assert (p+1)[..len-(n+1)] |-> ?rest_limbs;
                    assert rest_limbs == nil;
                    if(div + final_carry
                            >= pow_nat(base,noi(len-(n+1)+extra_cap))) {
                        assert noi(len-n+extra_cap)
                            == succ(noi(len-n-1+extra_cap));
                        my_inv_mul_strict_mono_r(base,div+final_carry,
                            pow_nat(base,noi(len-(n+1)+extra_cap)));
                        assert false;
                    }

                    if(div + final_carry < 0) {
                        assert false;
                    }

                } @*/

                carry += final_carry;
                final_carry = 0;
            }

            /*@ ++n; @*/

            /*@ assert (p+1)[..len-n] |-> ?next_limbs; @*/

            /*@ if(carry > (1<<32) || carry < -(1<<32)) {
                assert false;
            } @*/

            /*@ if(-poly_eval(next_limbs,base) + carry
                    + pow_nat(base,noi(length(next_limbs)))*final_carry
                    >= pow_nat(base,noi(len-n+extra_cap))) {

                if(l_limbs == nil) {
                    my_inv_mul_strict_mono_r(base, carry, pow_nat(base,
                        noi(len-n+extra_cap)));

                    assert false;
                }

                assert l_limbs == cons(val,next_limbs);

                assert noi(len-n+1+extra_cap) == succ(noi(len-n+extra_cap));

                mul_3var(base, pow_nat(base,noi(length(next_limbs))),
                    final_carry);

                my_inv_mul_strict_mono_r(base,
                    carry + -poly_eval(next_limbs,base)
                    + pow_nat(base,noi(length(next_limbs)))*final_carry,
                    pow_nat(base,noi(len-n+extra_cap)));

                assert false;
            } @*/

            /*@ if(-poly_eval(next_limbs,base) + carry
                    + pow_nat(base,noi(length(next_limbs)))*final_carry
                    < 0) {

                if(l_limbs == nil) {

                    assert false;
                }

                assert l_limbs == cons(val,next_limbs);

                assert noi(len-n+1+extra_cap) == succ(noi(len-n+extra_cap));

                mul_3var(base, pow_nat(base,noi(length(next_limbs))),
                    final_carry);

                my_inv_mul_strict_mono_r(base,
                    0,
                    1+carry - poly_eval(next_limbs,base)
                    + pow_nat(base,noi(length(next_limbs)))*final_carry);

                assert false;
            } @*/

            if(rem != 0) {
                non_zero_end = p+1;

                /*@ {
                    minimal_append(zero_limbs,{rem});
                    minimal_append(minimized_limbs,append(zero_limbs,{rem}));
                    minimized_limbs = append(minimized_limbs,
                        append(zero_limbs,{rem}));
                    minimized_len = n;
                    zero_limbs = nil;

                    if(!forall(minimized_limbs,(bounded)(0,base-1))) {
                        int cx = not_forall(minimized_limbs,
                            (bounded)(0,base-1));
                        if(mem(cx,orig_minimized_limbs)) {
                            forall_elim(orig_minimized_limbs,
                                (bounded)(0,base-1), cx);
                        } else if(mem(cx,orig_zero_limbs)) {
                            all_eq_elim(orig_zero_limbs,0,cx);
                        }
                        assert false;
                    }
                } @*/

            } else {
                /*@ zero_limbs = append(zero_limbs,{0}); @*/
                /*@ forall_append(append(orig_minimized_limbs,orig_zero_limbs),{0},
                        (bounded)(0,base-1)); @*/
            }
            /*@ append_assoc(orig_minimized_limbs,orig_zero_limbs,{rem}); @*/

            /*@ close ints(p,1,_); @*/
            /*@ ints_join(start); @*/

            /*@ {

                note_eq( -poly_eval(limbs,base)
                    ,  poly_eval(
                        append(orig_minimized_limbs,orig_zero_limbs),base)
                    + pow_nat(base,noi(orig_n))
                        *(-poly_eval(l_limbs, base) + orig_carry)
                    + pow_nat(base,noi(len))*orig_final_carry);


                assert -poly_eval(limbs,base)
                    == poly_eval(
                        append(orig_minimized_limbs,orig_zero_limbs),base)
                    + pow_nat(base,noi(orig_n))
                        *(-val + orig_carry + base*-poly_eval(next_limbs, base))
                    + pow_nat(base,noi(len))*orig_final_carry;

                note_eq(-poly_eval(limbs,base)
                    ,  poly_eval(
                        append(orig_minimized_limbs,orig_zero_limbs),base)
                    +  pow_nat(base,noi(orig_n))
                        *(rem + base*div + base*-poly_eval(next_limbs, base))
                    + pow_nat(base,noi(len))*orig_final_carry);

                mul_3var(pow_nat(base, noi(orig_n)), base,
                    div-poly_eval(next_limbs, base));

                note_eq(pow_nat(base,noi(orig_n))
                        *(rem + base*div + base*-poly_eval(next_limbs, base))
                        + pow_nat(base,noi(len))*orig_final_carry
                    ,  pow_nat(base,noi(orig_n))
                        *(rem + base*(div + -poly_eval(next_limbs, base)))
                    + pow_nat(base,noi(len))*orig_final_carry);

            } @*/

        }

        /*@ if(neg == (v < 0)) {
            assert false;
        } @*/

        /*@ assert n == len; @*/
        /*@ open ints(start+n,0,_); @*/

    } else {
        /*@ {
            if(neg && !(v < 0) || !neg && v < 0) {
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

                    assert false;
                }
            }
        } @*/
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

