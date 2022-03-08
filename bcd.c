#include "bcd.h"
/*@ #include "div.gh" @*/
/*@ #include "bitops.gh" @*/

#if 1
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif


/*@

lemma void dec_9876543210()
    requires true;
    ensures  dec_num({0,1,2,3,4,5,6,7,8,9}, 9876543210);
{
    close dec_num({0,1,2,3,4,5,6,7,8,9}, 9876543210);
}

lemma
void digit_rep_zero_unique(int b, list<int> le)
    requires b > 0
        &*&  !!forall(le,(bounded)(0,b-1))
        &*&  poly_eval(le,b) == 0
        ;
    ensures  minimize(le) == nil;
{
    switch(le) {
    case nil:
    case cons(x,xs):
        division_zero_unique(b,poly_eval(xs,b),x);
        digit_rep_zero_unique(b,xs);
    }
}

lemma
void digit_rep_unique(int b, list<int> le1, list<int> le2)
    requires b > 0
        &*&  !!forall(le1,(bounded)(0,b-1))
        &*&  !!forall(le2,(bounded)(0,b-1))
        &*&  !!minimal(le1) &*& !!minimal(le2)
        &*&  poly_eval(le1,b) == poly_eval(le2,b)
        ;
    ensures  le1 == le2;
{
    switch(le1) {
    case nil:
        digit_rep_zero_unique(b,le2);
    case cons(x,xs):
        switch(le2) {
        case nil:
            digit_rep_zero_unique(b,le1);
            assert false;
        case cons(y,ys):
            division_zero_unique(b,poly_eval(xs,b)-poly_eval(ys,b),x-y);
            digit_rep_unique(b,xs,ys);
        }
    }
}

lemma void dec_unique(list<int> le1, list<int> le2, int v)
    requires [?f1]dec_num(le1,v) &*& [?f2]dec_num(le2,v);
    ensures  [ f1]dec_num(le1,v) &*& [ f2]dec_num(le2,v)
        &*&  minimize(le1) == minimize(le2);
{
    if(minimize(le1) != minimize(le2)) {
        open dec_num(le1,v);
        open dec_num(le2,v);
        minimize_forall((bounded)(0,9),le1);
        minimize_forall((bounded)(0,9),le2);
        digit_rep_unique(10,minimize(le1),minimize(le2));
        assert false;
    }
}

lemma void bcd_exact(list<int> le_digits, int value, int bcd_value)
    requires !!forall(le_digits,(bounded)(0,9))
        &*&  poly_eval(le_digits,10) == value
        &*&  poly_eval(le_digits,16) == bcd_value;
    ensures  bcd_int(bcd_value,noi(length(le_digits)),le_digits,value);
{
    switch(le_digits) {
    case nil:
        close bcd_int(0,zero,le_digits,0);
    case cons(x,xs):
        if(poly_eval(xs,10) < 0) {
            int cx = poly_negative_coeff(xs,10);
            forall_elim(xs,(bounded)(0,9),cx);

            assert false;
        }

        if(poly_eval(xs,16) < 0) {
            int cx = poly_negative_coeff(xs,16);
            forall_elim(xs,(bounded)(0,9),cx);

            assert false;
        }

        division_unique_nonneg(value,10,poly_eval(xs,10),x);
        division_unique_nonneg(bcd_value,16,poly_eval(xs,16),x);
        bcd_exact(xs,value/10,bcd_value/16);
        close bcd_int(bcd_value,succ(noi(length(xs))),le_digits,value);
    }
}

lemma_auto void bcd_inv()
    requires [?f]bcd_int(?bcd,?n,?le,?v);
    ensures  [ f]bcd_int(bcd, n, le, v)
        &*&  v >= 0 &*& bcd >= 0 &*& (v == 0) == (bcd == 0)
        &*&  (v == 0) == poly_is_zero(le)
        &*&  bcd < pow_nat(16, n)
        &*&  v < pow_nat(10, n)
        &*&  !!forall(le,(bounded)(0,9))
        &*&  bcd == poly_eval(le,16)
        &*&  v   == poly_eval(le,10)
        &*&  ion(n) == length(le)
        ;
{
    if(v < 0 || bcd < 0 || (v == 0) != (bcd == 0) ||
            (v == 0) != poly_is_zero(le) ||
            bcd >= pow_nat(16,n) ||
            v   >= pow_nat(10,n) ||
            !forall(le,(bounded)(0,9)) ||
            bcd != poly_eval(le,16) ||
            v   != poly_eval(le,10) ||
            ion(n) != length(le)
            ) {

        open bcd_int(bcd,n,le,v);

        switch(n) {
        case zero:
        case succ(n0):
            bcd_inv();
        }

        if(v < 0) assert false;
        if(bcd < 0) assert false;
        if(!forall(le,(bounded)(0,9))) assert false;
        if(bcd != poly_eval(le,16)) {
            div_rem(bcd,16);
            assert false;
        }
        if(v   != poly_eval(le,10)) assert false;


        if((v == 0) || (bcd == 0)) {}

        assert false;
    }
}

lemma void bcd_join(int bcd1, nat n, int bcd2)
    requires [?f]bcd_int(bcd1, n,?le1,?v1)
        &*&  [ f]bcd_int(bcd2,?m,?le2,?v2);
    ensures  [f]bcd_int(
        bcd1 + pow_nat(16,n)*bcd2,
        nat_plus(n,m),
        append(le1,le2),
        v1 + pow_nat(10,n)*v2);
{
    open bcd_int(bcd1,n,le1,v1);
    switch(n) {
    case zero:
    case succ(n0):
        switch(le1) {
        case nil: assert false;
        case cons(x,xs):
            assert [f]bcd_int(bcd1/16,n0,xs,?v1_rest);
            division_unique_nonneg(v1,10,v1_rest,x);
            bcd_join(bcd1/16,n0,bcd2);
            assert [f]bcd_int(
                bcd1/16 + pow_nat(16,n0)*bcd2,
                nat_plus(n0,m),
                append(xs,le2),
                v1/10 + pow_nat(10,n0)*v2);

            mul_3var(16,pow_nat(16,n0),bcd2);
            mul_3var(10,pow_nat(10,n0),v2);
            division_unique_nonneg(
                    bcd1 + pow_nat(16,n)*bcd2,16,
                    bcd1/16 + pow_nat(16,n0)*bcd2,x);
            division_unique_nonneg(
                    v1 + pow_nat(10,n)*v2,10,
                    v1/10 + pow_nat(10,n0)*v2,x);

            close [f]bcd_int(
                bcd1 + pow_nat(16,n)*bcd2,
                nat_plus(n,m),
                append(le1,le2),
                v1 + pow_nat(10,n)*v2);
        }
    }
}

lemma void bcd_resize(int bcd, nat n)
    requires [?f]bcd_int(bcd,?m,?le,?v)
        &*&  (bcd < pow_nat(16,n) || v < pow_nat(10,n));
    ensures  [ f]bcd_int(bcd, n,?le_final, v)
        &*&  minimize(le) == minimize(le_final);
{
    switch(n) {
    case zero:
        assert bcd == 0;
        assert v == 0;
        leak [f]bcd_int(bcd,m,le,v);
        close [f]bcd_int(bcd,n,nil,v);
        return;

    case succ(n0):
        switch(le) {
        case nil:
            assert bcd == 0;
            assert v == 0;
            bcd_resize(0, n0);

            assert [f]bcd_int(0,n0,?rest,0);
            close [f]bcd_int(0,n,cons(0,rest),0);
            return;

        case cons(x,xs):
            open [f]bcd_int(bcd,m,cons(x,xs),v);
            assert [f]bcd_int(bcd/16,_,xs,?v_rest);
            division_unique_nonneg(v,10,v_rest,x);
            bcd_resize(bcd/16, n0);

            assert [f]bcd_int(bcd/16,n0,?rest,v/10);
            close [f]bcd_int(bcd,n,cons(x,rest),v);
            return;
        }
    }
}

  @*/

uint32_t bcd_add_u32(uint32_t x,uint32_t y)
    /*@ requires [?f1]bcd_int(x,?xn,?x_le,?xv)
            &*&  [?f2]bcd_int(y,?yn,?y_le,?yv)
            &*&  xv+yv < pow_nat(10,N8)
            ; @*/
    /*@ ensures  bcd_int(result,?rn,_,xv+yv)
            &*&  ion(rn) <= 8; @*/
    /*@ terminates; @*/
{
    uint32_t carry = 0;
    uint32_t shift = 0;
    uint32_t ret = 0;

    /*@ {
      produce_limits(x);
      produce_limits(y);
      pow_times2(2,N4,8);
      bcd_resize(x,N8);
      bcd_resize(y,N8);
    } @*/

    /*@ nat n = zero; @*/
    /*@ nat m = N8; @*/

    while(shift < 32)
        /*@ requires [f1]bcd_int(x,m,?loop_x_le,?loop_xv)
                &*&  [f2]bcd_int(y,m,?loop_y_le,?loop_yv)
                &*&  bcd_int(ret,n,?ret_le,?retv)
                &*&  carry <= 1
                &*&  nat_plus(n,m) == N8
                &*&  shift == 4*ion(n)
                &*&  (shift > 28
                     ? shift == 32 &*& x <= 0 &*& y <= 0 &*& carry <= 0
                     : true)
                &*&  ret < pow_nat(16,n)
                &*&  retv
                    + (loop_xv+loop_yv+carry)*pow_nat(10,n)
                    == xv + yv;
                @*/
        /*@ ensures [f1]bcd_int(x,_,_,_)
                &*& [f2]bcd_int(y,_,_,_)
                &*& bcd_int(ret,N8,_,xv+yv); @*/
        /*@ decreases 32-shift; @*/
    {
        /*@ { ALREADY_PROVEN() } @*/
        /*@ open bcd_int(x,m,_,_); @*/
        /*@ open bcd_int(y,m,_,_); @*/

        /*@ {
            div_rem(x,16);
            div_rem(loop_xv,10);
            div_rem(y,16);
            div_rem(loop_yv,10);
        } @*/

        uint32_t x_digit = x%16;
        uint32_t y_digit = y%16;
        uint32_t ret_digit = x_digit + y_digit + carry;

        /*@ {
            assert [f1]bcd_int(x/16,?n0,?x_rest,?xv_rest);
            assert [f2]bcd_int(y/16, n0,?y_rest,?yv_rest);
            division_unique_nonneg(loop_xv,10,xv_rest,x_digit);
            division_unique_nonneg(loop_yv,10,yv_rest,y_digit);
            note_eq(x_digit,loop_xv%10);
            note_eq(y_digit,loop_yv%10);

            assert x/16 >= 0;
            assert y/16 >= 0;

            assert ret_digit >= 0 &*& ret_digit <= 19;
            if(ret_digit < 0) assert false;
            if(ret_digit > 19) assert false;

            assert shift <= 28;

            if(shift + 4 > 28) {
                if(shift < 28) {
                    division_unique_nonneg(shift,4,length(ret_le),0);
                    division_unique_nonneg(shift,4,6,shift-24);
                    assert false;
                }

                if(x/16 > 0 || y/16 > 0 || ret_digit >= 10) assert false;
            }

            if(ret_digit >= 10) {
                division_unique_nonneg(ret_digit,10,(uint32_t)1,ret_digit-10);

                assert (ret_digit-10) + 10 + 10*(loop_xv/10) + 10*(loop_yv/10)
                    == loop_xv + loop_yv + carry;
            } else {
                division_unique_nonneg(ret_digit,10,(uint32_t)0,ret_digit);
                assert ret_digit == ret_digit%10;
                assert ret_digit + 10*(loop_xv/10) + 10*(loop_yv/10)
                    == loop_xv + loop_yv + carry;

            }
        } @*/

        /* carry = ((ret_digit >= 10) ? (uint32_t)1 : (uint32_t)0); */
        /* ret_digit -= carry*10; */
        if(ret_digit >= 10) {
            carry = 1;
            ret_digit -= 10;
        } else {
            carry = 0;
        }

        /*@ {
            if(ret_digit < 0) assert false;
            if(ret_digit > 9) assert false;
            if(!(ret_digit >= 0 && ret_digit <= 9)) assert false;
            if(!bounded(0,9,ret_digit)) assert false;

            shiftleft_def(ret_digit,noi(shift));
            my_mul_mono_l(0,ret_digit,pow_nat(2,noi(shift)));

            pow_times2(2,N4,ion(n));
            assert ret < pow_nat(2,noi(shift));
            assert ret + 10*pow_nat(2,noi(shift)) < 11*pow_nat(2,noi(shift));
            my_mul_strict_mono_l(11,pow_nat(2,N4),pow_nat(2,noi(shift)));
            assert ret + 10*pow_nat(2,noi(shift)) < pow_nat(2,N4)*pow_nat(2,noi(shift));
            my_mul_mono_l(ret_digit,10,pow_nat(2,noi(shift)));
            assert ret + ret_digit*pow_nat(2,noi(shift))
                <  pow_nat(2,N4)*pow_nat(2,noi(shift));
            pow_soft_monotonic(2,noi(shift),noi(28));
            pow_plus(2,N4,28);
            assert ret + ret_digit*pow_nat(2,noi(shift)) < pow_nat(2,N32);

            pow_times2(2,N4,length(ret_le));
            pow_times2(2,N4,length(ret_le)+1);

            note(bounded(0,9,ret_digit));
            bcd_exact({ret_digit},ret_digit,ret_digit);
            bcd_join(ret,n,ret_digit);

            note_eq(xv + yv,  retv
                + (ret_digit + 10*carry + 10*(loop_xv/10)
                    + 10*(loop_yv/10))*pow_nat(10,n));

            note_eq(xv + yv ,  retv
                + ret_digit*pow_nat(10,n)
                + (carry + loop_xv/10
                    + loop_yv/10)*(10*pow_nat(10,n)));

            n = succ(n);
            m = nat_predecessor(m);
        } @*/

        ret += (ret_digit<<shift);
        x /= 16;
        y /= 16;
        shift += 4;
    }

    /*@ leak [f1]bcd_int(x,_,_,_); @*/
    /*@ leak [f2]bcd_int(y,_,_,_); @*/

    return ret;
}

