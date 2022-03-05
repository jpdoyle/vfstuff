/*@ #include "poly.gh" @*/
/*@ #include "div.gh" @*/
/*@ #include "bitops.gh" @*/

#if 1
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif


/*@

predicate dec_num(list<int> le_digits; int value)
    =   !!forall(le_digits, (bounded)(0,9))
    &*& value == poly_eval(le_digits,10);

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

predicate bcd_int(list<int> le_digits; int value, int bcd_value)
    =   dec_num(le_digits,value)
    &*& bcd_value == poly_eval(le_digits,16);

lemma_auto void bcd_inv()
    requires [?f]bcd_int(?le,?v,?bcd);
    ensures  [ f]bcd_int( le, v, bcd)
        &*&  v >= 0 &*& bcd >= 0 &*& (v == 0) == (bcd == 0)
        &*&  bcd < pow_nat(16, noi(length(le)))
        &*&  v < pow_nat(10, noi(length(le)))
        ;
{
    if(v < 0 || bcd < 0 || (v == 0) != (bcd == 0) ||
            bcd >= pow_nat(16,noi(length(le))) ||
            v   >= pow_nat(10,noi(length(le)))) {
        open bcd_int(le,v,bcd);
        open dec_num(le,v);
        if(v < 0) {
            int cx = poly_negative_coeff(le,10);
            forall_elim(le,(bounded)(0,9),cx);
            assert false;
        }
        if(bcd < 0) {
            int cx = poly_negative_coeff(le,16);
            forall_elim(le,(bounded)(0,9),cx);
            assert false;
        }

        if((v == 0) != (bcd == 0)) {
            if(v == 0 && bcd != 0) {
                if(!poly_is_zero(le)) {
                    int cx = poly_positive_zero(le,10);
                    forall_elim(le,(bounded)(0,9),cx);
                    assert false;
                }
                poly_eval_zero(le,16);
                assert false;
            }

            if(v != 0 && bcd == 0) {
                if(!poly_is_zero(le)) {
                    int cx = poly_positive_zero(le,16);
                    forall_elim(le,(bounded)(0,9),cx);
                    assert false;
                }
                poly_eval_zero(le,10);
                assert false;
            }
            assert false;
        }

        if(bcd >= pow_nat(16, noi(length(le)))) {
            poly_eval_bounded_pos(le,9,16);
            assert false;
        }

        if(v >= pow_nat(10, noi(length(le)))) {
            poly_eval_bounded_pos(le,9,10);
            assert false;
        }

        assert false;
    }
}

lemma void bcd_join(list<int> le1,list<int> le2)
    requires [?f]bcd_int(le1,?v1,?bcd1)
        &*&  [ f]bcd_int(le2,?v2,?bcd2);
    ensures  [f]bcd_int(append(le1,le2),
                v1 + pow_nat(10,noi(length(le1)))*v2,
                bcd1 + pow_nat(16,noi(length(le1)))*bcd2);
{
    switch(le1) {
    case nil:
        if(v1 != 0 || bcd1 != 0) {
            assert false;
        }
        leak [f]bcd_int(le1,v1,bcd1);
    case cons(x,xs):
        open [f]bcd_int(cons(x,xs),v1,bcd1);
        open [f]dec_num(cons(x,xs),v1);

        if(poly_eval(xs,10) < 0) {
            assert false;
        }
        if(poly_eval(xs,16) < 0) {
            assert false;
        }

        division_unique_nonneg(v1,10,poly_eval(xs,10),x);
        division_unique_nonneg(bcd1,16,poly_eval(xs,16),x);

        close [f]dec_num(xs,v1/10);
        close [f]bcd_int(xs,v1/10,bcd1/16);
        bcd_join(xs,le2);
        open bcd_int(append(xs,le2),
                (v1/10 + pow_nat(10,noi(length(xs)))*v2),
                (bcd1/16 + pow_nat(16,noi(length(xs)))*bcd2));

        open dec_num(append(xs,le2),
                (v1/10 + pow_nat(10,noi(length(xs)))*v2));

        mul_3var(10,pow_nat(10,noi(length(xs))),v2);
        mul_3var(16,pow_nat(16,noi(length(xs))),bcd2);

        close [f]dec_num(cons(x,append(xs,le2)),
                (v1 + pow_nat(10,succ(noi(length(xs))))*v2));

        close [f]bcd_int(cons(x,append(xs,le2)),
                v1+ pow_nat(10,succ(noi(length(xs))))*v2,
                bcd1 + pow_nat(16,succ(noi(length(xs))))*bcd2);
    }
}


  @*/

unsigned long bcd_add_long(unsigned long x,unsigned long y)
    /*@ requires bcd_int(?x_le,?xv,x) &*& bcd_int(?y_le,?yv,y)
            &*&  xv+yv < pow_nat(10,N8)
            ;
      @*/
    /*@ ensures  bcd_int(_,xv+yv,result); @*/
    /*@ terminates; @*/
{
    /*@ {
      produce_limits(x);
      produce_limits(y);
    } @*/

    unsigned long carry = 0;
    unsigned long shift = 0;
    unsigned long ret = 0;

    /*@ list<int> loop_x_le = x_le; @*/
    /*@ list<int> loop_y_le = y_le; @*/
    /*@ list<int> ret_le = nil; @*/
    /*@ close bcd_int(ret_le,0,ret); @*/

    while(x > 0 || y > 0 || carry > 0)
        /*@ requires bcd_int(loop_x_le,?loop_xv,x)
                &*&  bcd_int(loop_y_le,?loop_yv,y)
                &*&  bcd_int(ret_le,?retv,ret)
                &*&  carry <= 1
                &*&  (shift <= 28 || (x <= 0 && y <= 0 && carry <= 0))
                &*&  ret < pow_nat(2,noi(shift))
                &*&  length(ret_le)*4 == shift
                &*&  retv
                    + (loop_xv+loop_yv+carry)*pow_nat(10,noi(length(ret_le)))
                    == xv + yv;
                @*/
        /*@ ensures bcd_int(loop_x_le,_,x)
                &*& bcd_int(loop_y_le,_,y)
                &*& bcd_int(ret_le,xv+yv,ret); @*/
        /*@ decreases 32-shift; @*/
    {
        /*@ { ALREADY_PROVEN() } @*/
        /*@ open bcd_int(loop_x_le,_,_); @*/
        /*@ open dec_num(loop_x_le,_); @*/
        /*@ open bcd_int(loop_y_le,_,_); @*/
        /*@ open dec_num(loop_y_le,_); @*/

        /*@ int x_place; @*/ /*@ list<int> x_rest; @*/
        /*@ int y_place; @*/ /*@ list<int> y_rest; @*/

        /*@ {
            switch(loop_x_le) {
            case nil:
                x_place = 0; x_rest = nil;
            case cons(xd,xds):
                x_place = xd; x_rest = xds;
            }
            switch(loop_y_le) {
            case nil:
                y_place = 0; y_rest = nil;
            case cons(yd,yds):
                y_place = yd; y_rest = yds;
            }

            assert !!bounded(0,9,x_place);

            if(poly_eval(x_rest,10) < 0) {
                assert false;
            }

            if(poly_eval(y_rest,10) < 0) {
                assert false;
            }

            div_rem(x,16);
            division_unique_nonneg(x,16,poly_eval(x_rest,16),x_place);
            division_unique_nonneg(loop_xv,10,poly_eval(x_rest,10),x_place);
            div_rem(y,16);
            division_unique_nonneg(y,16,poly_eval(y_rest,16),y_place);
            division_unique_nonneg(loop_yv,10,poly_eval(y_rest,10),y_place);

            loop_x_le = x_rest;
            loop_y_le = y_rest;

            close dec_num(loop_x_le,loop_xv/10);
            close bcd_int(loop_x_le,loop_xv/10,x/16);
            bcd_inv();
            close dec_num(loop_y_le,loop_yv/10);
            close bcd_int(loop_y_le,loop_yv/10,y/16);
            bcd_inv();
            assert x/16 >= 0;
            assert y/16 >= 0;
        } @*/

        unsigned long x_digit = x%16;
        unsigned long y_digit = y%16;
        unsigned long ret_digit = x_digit + y_digit + carry;
        /*@ assert ret_digit >= 0 &*& ret_digit <= 19; @*/

        /*@ {
            assert shift <= 28;

            if((loop_xv/10 == 0) != (x/16 == 0)) {
                assert false;
            }

            if((loop_yv/10 == 0) != (y/16 == 0)) {
                assert false;
            }

            if(shift + 4 > 28) {
                if(x/16 > 0 || y/16 > 0 || ret_digit >= 10) {
                    assert xv + yv < pow_nat(10,N8);
                    assert retv + (loop_xv + loop_yv +
                            carry)*pow_nat(10,noi(length(ret_le)))
                        < pow_nat(10,N8);
                    assert loop_xv%10 == x_digit;
                    assert loop_yv%10 == y_digit;
                    div_rem(ret_digit,10);
                    assert retv + ((x_digit + 10*(loop_xv/10))
                                    + (y_digit + 10*(loop_yv/10))
                                    + carry
                                    )*pow_nat(10,noi(length(ret_le)))
                        < pow_nat(10,N8);

                    assert retv + ((x_digit + 10*(loop_xv/10))
                                    + (y_digit + 10*(loop_yv/10))
                                    + carry
                                   )*pow_nat(10,noi(length(ret_le)))
                        < pow_nat(10,N8);

                    if((x_digit + 10*(loop_xv/10))
                            + (y_digit + 10*(loop_yv/10))
                            + carry
                            < 10) {
                        if(x/16 > 0) {
                            my_mul_mono_r(10,1,loop_xv/10);
                        } else if(y/16 > 0) {
                            my_mul_mono_r(10,1,loop_yv/10);
                        }
                        assert false;
                    }

                    my_mul_mono_l(10,
                        (x_digit + 10*(loop_xv/10))
                            + (y_digit + 10*(loop_yv/10))
                            + carry,
                        pow_nat(10,noi(length(ret_le))));

                    if(length(ret_le)+1 >= 8) {
                        assert false;
                    }

                    assert false;
                }
            }
        } @*/

        carry = ret_digit / 10;
        /*@ div_rem(ret_digit,10); @*/
        ret_digit %= 10;

        /*@ {
            shiftleft_def(ret_digit,noi(shift));
            my_mul_mono_l(0,ret_digit,pow_nat(2,noi(shift)));
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

            if(pow_nat(2,noi(shift)) != pow_nat(16,noi(length(ret_le)))) {
                pow_times2(2,N4,length(ret_le));
                assert false;
            }

            if(pow_nat(2,noi(shift+4)) != pow_nat(16,noi(length(ret_le)+1))) {
                pow_times2(2,N4,length(ret_le)+1);
                assert false;
            }

            close bcd_int({ret_digit},ret_digit,ret_digit);
            bcd_join(ret_le,{ret_digit});

            note_eq(xv + yv,  retv
                + (ret_digit + 10*carry + 10*(loop_xv/10)
                    + 10*(loop_yv/10))*pow_nat(10,noi(length(ret_le))));

            assert xv + yv == retv
                + ret_digit*pow_nat(10,noi(length(ret_le)))
                + (10*carry + 10*(loop_xv/10) + 10*(loop_yv/10))*pow_nat(10,noi(length(ret_le)));

            assert xv + yv == retv
                + ret_digit*pow_nat(10,noi(length(ret_le)))
                + (10*(carry + loop_xv/10 + loop_yv/10))*pow_nat(10,noi(length(ret_le)));

            note_eq(xv + yv ,  retv
                + ret_digit*pow_nat(10,noi(length(ret_le)))
                + (carry + loop_xv/10
                    + loop_yv/10)*(10*pow_nat(10,noi(length(ret_le)))));


            assert xv + yv == retv
                + ret_digit*pow_nat(10,noi(length(ret_le)))
                + (carry + loop_xv/10
                    + loop_yv/10)*pow_nat(10,succ(noi(length(ret_le))));

            ret_le = append(ret_le,{ret_digit});
        } @*/

        ret += (ret_digit<<shift);
        x /= 16;
        y /= 16;
        shift += 4;
    }

    /*@ leak bcd_int(loop_x_le,_,x); @*/
    /*@ leak bcd_int(loop_y_le,_,y); @*/
    /*@ open bcd_int(ret_le,xv+yv,ret); @*/
    /*@ close bcd_int(ret_le,xv+yv,ret); @*/

    return ret;
}

