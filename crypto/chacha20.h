
/*@ #include "../util.gh" @*/
/*@ #include "../poly.gh" @*/

/*@

inductive fourple<t> = fourple(t,t,t,t);

fixpoint list<t> fourple_list<t>(fourple<t> ple) {
    switch(ple) {
    case fourple(a,b,c,d):
        return {a,b,c,d};
    }
}

inductive chacha_state
    = chacha_state(int x0,  int x1,  int x2,  int x3,
                   int x4,  int x5,  int x6,  int x7,
                   int x8,  int x9,  int x10, int x11,
                   int x12, int x13, int x14, int x15);

fixpoint bool valid_chachastate(chacha_state cs) {
    switch(cs) {
    case chacha_state(x0,  x1,  x2,  x3,
                      x4,  x5,  x6,  x7,
                      x8,  x9,  x10, x11,
                      x12, x13, x14, x15):
        return x0 >= 0  && x0 < pow_nat(2,N32)
            && x1 >= 0  && x1 < pow_nat(2,N32)
            && x2 >= 0  && x2 < pow_nat(2,N32)
            && x3 >= 0  && x3 < pow_nat(2,N32)
            && x4 >= 0  && x4 < pow_nat(2,N32)
            && x5 >= 0  && x5 < pow_nat(2,N32)
            && x6 >= 0  && x6 < pow_nat(2,N32)
            && x7 >= 0  && x7 < pow_nat(2,N32)
            && x8 >= 0  && x8 < pow_nat(2,N32)
            && x9 >= 0  && x9 < pow_nat(2,N32)
            && x10 >= 0 && x10 < pow_nat(2,N32)
            && x11 >= 0 && x11 < pow_nat(2,N32)
            && x12 >= 0 && x12 < pow_nat(2,N32)
            && x13 >= 0 && x13 < pow_nat(2,N32)
            && x14 >= 0 && x14 < pow_nat(2,N32)
            && x15 >= 0 && x15 < pow_nat(2,N32)
            ;
    }
}

fixpoint fourple<int> chacha_constants() {
    return fourple(0x61707865, 0x3320646e,
                   0x79622d32, 0x6b206574);
}

lemma void chacha_constants_are_a_string()
    requires true;
    ensures  poly_eval(fourple_list(chacha_constants()),pow_nat(2,N32))
        ==   poly_eval("expand 32-byte k",pow_nat(2,N8));
{}

fixpoint int rotl1(nat pred_b, int x) {
    return (x*2 + x/pow_nat(2,pred_b))%pow_nat(2,succ(pred_b));
}

fixpoint int rotr1(nat pred_b, int x) {
    return (x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,succ(pred_b));
}

lemma void mod_div_factor(int x, int d1, int d2)
    requires d1 > 0 &*& x >= 0 &*& d2 > 0 &*& d1%d2 == 0;
    ensures  (x%d1)/d2 == (x/d2) - (d1/d2)*(x/d1);
{
    div_rem(x,d1);
    div_rem(d1,d2);
    div_rem(x,d2);
    assert d2*(x/d2) + x%d2 == x;
    div_rem(x%d1,d2);
    assert d2*((x%d1)/d2) + (x%d1)%d2 == x%d1;
    mod_twice(x,d1,d2);
    assert d2*((x%d1)/d2) + x%d2 == x%d1;
    assert d2*((x%d1)/d2) + x%d2 == x%d1;
    assert d2*((x%d1)/d2) + x%d2 == x - d1*(x/d1);
    assert d2*((x%d1)/d2) + x%d2 == (d2*(x/d2) + x%d2) - d1*(x/d1);
    assert d2*((x%d1)/d2) == d2*(x/d2) - d1*(x/d1);
    assert d2*((x%d1)/d2) == d2*(x/d2) - (d2*(d1/d2))*(x/d1);

    mul_assoc(d2,(d1/d2),(x/d1));

    assert d2*((x%d1)/d2) == d2*(x/d2) - d2*((d1/d2)*(x/d1));
    assert d2*((x%d1)/d2 - x/d2 + (d1/d2)*(x/d1)) == 0;
    mul_to_zero(d2,((x%d1)/d2 - x/d2 + (d1/d2)*(x/d1)));

    assert (x%d1)/d2 == (x/d2) - (d1/d2)*(x/d1);
}

lemma void rotl_r_inv(nat pred_b, int x)
    requires x >= 0 &*& x < pow_nat(2,succ(pred_b));
    ensures  rotl1(pred_b,rotr1(pred_b,x)) == x
        &*&  rotr1(pred_b,rotl1(pred_b,x)) == x;
{
    nat b = succ(pred_b);
    if(rotl1(pred_b,rotr1(pred_b,x)) != x) {
        div_rem(x,2);
        assert rotl1(pred_b,
            (x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
            != x;
        assert (
            ((x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
             *2 +
            ((x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
             /pow_nat(2,pred_b))%pow_nat(2,b)
            != x;

        my_mul_mono_r(x%2,1,pow_nat(2,pred_b));
        mod_sign(x/2 + (x%2)*pow_nat(2,pred_b),pow_nat(2,b));
        div_sign((x/2 +
                (x%2)*pow_nat(2,pred_b))%pow_nat(2,b),
            pow_nat(2,pred_b));
        my_mul_mono_r((x/2 +
                    (x%2)*pow_nat(2,pred_b))%pow_nat(2,b),1,2);

        mod_plus(
            ((x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
                *2,
            ((x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
             /pow_nat(2,pred_b),
            pow_nat(2,b));

        assert (
            ((((x/2 + (x%2)*pow_nat(2,pred_b)))%pow_nat(2,b))*2)
                %pow_nat(2,b) +
            ((x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
             /pow_nat(2,pred_b))%pow_nat(2,b)
            != x;

        mod_times((x/2 + (x%2)*pow_nat(2,pred_b)),2,pow_nat(2,b));
        assert (
            ((x/2 + (x%2)*pow_nat(2,pred_b))*2) %pow_nat(2,b) +
            ((x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
             /pow_nat(2,pred_b))%pow_nat(2,b)
            != x;

        assert (
            ((x/2 + (x%2)*pow_nat(2,pred_b))*2)%pow_nat(2,b) +
            ((x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
             /pow_nat(2,pred_b))%pow_nat(2,b)
            != x;

        assert (
            (2*(x/2 + (x%2)*pow_nat(2,pred_b)))%pow_nat(2,b) +
            ((x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
             /pow_nat(2,pred_b))%pow_nat(2,b)
            != x;
        assert (
            (2*(x/2) + 2*((x%2)*pow_nat(2,pred_b)))%pow_nat(2,b) +
            ((x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
             /pow_nat(2,pred_b))%pow_nat(2,b)
            != x;

        mul_3var(2,(x%2),pow_nat(2,pred_b));

        assert (
            (2*(x/2) + (x%2)*pow_nat(2,b))%pow_nat(2,b) +
            ((x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
             /pow_nat(2,pred_b))%pow_nat(2,b)
            != x;
        mod_times_d(2*(x/2),x%2,pow_nat(2,b));
        assert (
            (2*(x/2))%pow_nat(2,b) +
            ((x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
             /pow_nat(2,pred_b))%pow_nat(2,b)
            != x;

        division_unique(2*(x/2),pow_nat(2,b),0,2*(x/2));

        assert (
            2*(x/2) +
            ((x/2 + (x%2)*pow_nat(2,pred_b))%pow_nat(2,b))
             /pow_nat(2,pred_b))%pow_nat(2,b)
            != x;

        assert x/2 < pow_nat(2,pred_b);
        assert x%2 <= 1;
        my_mul_mono_l(x%2,1,pow_nat(2,pred_b));
        assert (x%2)*pow_nat(2,pred_b) <= pow_nat(2,pred_b);
        assert x/2 + (x%2)*pow_nat(2,pred_b) < 2*pow_nat(2,pred_b);
        assert x/2 + (x%2)*pow_nat(2,pred_b) < pow_nat(2,b);
        division_unique(x/2 + (x%2)*pow_nat(2,pred_b),pow_nat(2,b),0,
                x/2 + (x%2)*pow_nat(2,pred_b));

        assert (
            2*(x/2) +
            (x/2 + (x%2)*pow_nat(2,pred_b))
             /pow_nat(2,pred_b))%pow_nat(2,b)
            != x;

        division_unique(x/2 + (x%2)*pow_nat(2,pred_b),
                pow_nat(2,pred_b),
                x%2, x/2);

        assert (2*(x/2) + (x%2))%pow_nat(2,b)
            != x;

        division_unique(x,pow_nat(2,b),0,x);

        assert false;
    }

    if(rotr1(pred_b,rotl1(pred_b,x)) != x) {
        assert rotr1(pred_b,
            (x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))
            != x;
        assert (
            ((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))
             /2 +
            (((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))%2)
             *pow_nat(2,pred_b))%pow_nat(2,b)
            != x;

        div_sign(x,pow_nat(2,pred_b));
        my_mul_mono_r(x,1,2);
        division_unique(pow_nat(2,b),2,pow_nat(2,pred_b),0);

        mod_twice(x*2 + x/pow_nat(2,pred_b),pow_nat(2,b),2);

        assert (
            ((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))
             /2 +
            ((x*2 + x/pow_nat(2,pred_b))%2)
             *pow_nat(2,pred_b))%pow_nat(2,b)
            != x;

        mod_times_d(x/pow_nat(2,pred_b),x,2);

        assert (
            ((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))
             /2 +
            ((x/pow_nat(2,pred_b))%2)
             *pow_nat(2,pred_b))%pow_nat(2,b)
            != x;

        assert (x*2 + x/pow_nat(2,pred_b)) >= 0;
        div_rem((x*2 + x/pow_nat(2,pred_b)),pow_nat(2,b));
        mod_sign((x*2 + x/pow_nat(2,pred_b)),pow_nat(2,b));
        assert (x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b) >= 0;
        div_rem(((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b)),2);

        assert 2*(((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))/2)
            <= (x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b);
        assert 2*(((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))/2)
            <  pow_nat(2,b);
        assert 2*(((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))/2)
            <  2*pow_nat(2,pred_b);

        my_inv_mul_strict_mono_r(2,
            (((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))/2),
            pow_nat(2,pred_b));

        assert ((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))/2
            < pow_nat(2,pred_b);

        my_mul_mono_l(((x/pow_nat(2,pred_b))%2),1,
             pow_nat(2,pred_b));
        assert ((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))
                /2 +
            ((x/pow_nat(2,pred_b))%2)
             *pow_nat(2,pred_b)
            < 2*pow_nat(2,pred_b);
        assert ((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))
                /2 +
            ((x/pow_nat(2,pred_b))%2)
             *pow_nat(2,pred_b)
            < pow_nat(2,b);

        assert ((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))
                /2 >= 0;
        my_mul_mono_l(0,(x/pow_nat(2,pred_b))%2,pow_nat(2,pred_b));
        assert ((x/pow_nat(2,pred_b))%2)*pow_nat(2,pred_b) >= 0;

        assert ((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))
                /2 +
            ((x/pow_nat(2,pred_b))%2)
             *pow_nat(2,pred_b)
            >= 0;


        division_unique(((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))
             /2 +
            ((x/pow_nat(2,pred_b))%2)
             *pow_nat(2,pred_b),
            pow_nat(2,b),0,
            ((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))
             /2 +
            ((x/pow_nat(2,pred_b))%2)
             *pow_nat(2,pred_b));

        assert ((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))
                /2 +
            ((x/pow_nat(2,pred_b))%2)
                *pow_nat(2,pred_b)
            != x;

        if(x/pow_nat(2,pred_b) >= 2) {
            div_rem(x,pow_nat(2,pred_b));
            assert pow_nat(2,pred_b)*(x/pow_nat(2,pred_b)) <= x;
            my_mul_mono_r(pow_nat(2,pred_b),2,x/pow_nat(2,pred_b));
            assert pow_nat(2,pred_b)*2 <= x;
            assert pow_nat(2,b)*2 <= x;
            assert false;
        }

        assert x/pow_nat(2,pred_b) < 2;
        division_unique(x/pow_nat(2,pred_b),2,0,x/pow_nat(2,pred_b));
        assert (x/pow_nat(2,pred_b))%2 == x/pow_nat(2,pred_b);

        assert ((x*2 + x/pow_nat(2,pred_b))%pow_nat(2,b))
                /2 +
            (x/pow_nat(2,pred_b))*pow_nat(2,pred_b)
            != x;

        if(x >= pow_nat(2,pred_b)) {
            if(x/pow_nat(2,pred_b) <= 0) {
                div_rem(x,pow_nat(2,pred_b));
                assert x%pow_nat(2,pred_b) < pow_nat(2,pred_b);
                assert false;
            }
            assert x/pow_nat(2,pred_b) == 1;

            assert ((x*2 + 1)%pow_nat(2,b))
                    /2 +
                (1)*pow_nat(2,pred_b)
                != x;

            assert ((x*2 + 1)%pow_nat(2,b))/2 + pow_nat(2,pred_b)
                != x;

            mod_div_factor(x*2 + 1, pow_nat(2,b),2);

            division_unique(pow_nat(2,b),2,pow_nat(2,pred_b),0);

            assert ((x*2 + 1)%pow_nat(2,b))/2
                == ((x*2 + 1)/2) - (pow_nat(2,b)/2)*((x*2 + 1)/pow_nat(2,b));

            assert ((x*2 + 1)/2) - pow_nat(2,pred_b)*((x*2 + 1)/pow_nat(2,b)) + pow_nat(2,pred_b)
                != x;

            div_nudge(x,1,2);

            assert (x
                    + pow_nat(2,pred_b)*(1 - (x*2 + 1)/pow_nat(2,b)))
                != x;
            assert pow_nat(2,pred_b)*(1 - (x*2 + 1)/pow_nat(2,b)) != 0;

            div_rem(x*2 + 1, pow_nat(2,b));
            assert 1 != (x*2 + 1)/pow_nat(2,b);
            assert 2*x >= pow_nat(2,b);
            assert 2*x + 1 >= pow_nat(2,b) + 1;
            assert 2*x + 1 - pow_nat(2,b) >= 1;

            if((x*2 + 1)/pow_nat(2,b) < 2) {
                if((x*2 + 1)/pow_nat(2,b) >= 1) {
                    assert false;
                }
                div_sign(x*2+1,pow_nat(2,b));

                assert (x*2 + 1)/pow_nat(2,b) == 0;
                assert false;
            }

            assert (x*2 + 1)/pow_nat(2,b) >= 2;
            my_mul_mono_r(pow_nat(2,b),2,(x*2 + 1)/pow_nat(2,b));
            assert pow_nat(2,b)*((x*2 + 1)/pow_nat(2,b)) >=
                pow_nat(2,succ(b));

            assert x <= pow_nat(2,b) - 1;
            assert 2*x <= pow_nat(2,succ(b)) - 2;
            assert 2*x + 1 <= pow_nat(2,succ(b)) - 1;

            assert false;
        } else {
            division_unique(x,pow_nat(2,pred_b),0,x);
            assert x/pow_nat(2,pred_b) == 0;

            assert ((x*2)%pow_nat(2,b))/2 != x;
            assert x*2 < 2*pow_nat(2,pred_b);
            division_unique(x*2,pow_nat(2,b),0,x*2);
            assert (x*2)%pow_nat(2,b) == x;

            assert false;
        }

        assert false;
    }
}

fixpoint int rot(nat b, int x, nat n) {
    return (x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b,n)))%pow_nat(2,b);
}

fixpoint int rot32(int x, nat n) {
    return rot(N32, x, n);
}

//lemma void mod_minus(int x, int y, int d)
//    requires d > 0 &*& x >= 0 &*& y >= 0;
//    ensures  x%d - y%d == (x-y)%d;
//{
//    div_rem(x,d);
//    div_rem(y,d);
//    assert x == d*(x/d) + x%d;
//    assert y == d*(y/d) + y%d;
//    if(x >= y) {
//        div_monotonic_numerator(y,x,d);
//        division_unique(x-y,d,x/d - y/d,x%d - y%d);
//    } else {
//        div_monotonic_numerator(x,y,d);
//        division_unique(x-y,d,x/d - y/d,x%d - y%d);
//    }
//    //note_eq( x-y ,  d*(x/d - y/d) + x%d - y%d);
//    //note( abs_of(d*(x/d - y/d) + x%d - y%d)
//    //    <= abs_of(d*(x/d - y/d)) + abs_of(x%d - y%d));
//    //assert abs(x%d - y%d) < d;
//    //division_unique(x-y,d,x/d - y/d,x%d - y%d);
//}

lemma void rot_bound(nat b, int x, nat n)
    requires x >= 0;
    ensures  rot(b,x,n) >= 0 &*& rot(b,x,n) < pow_nat(2,b);
{
    div_sign(x,pow_nat(2,nat_minus(b,n)));
    my_mul_mono_r(x,1,pow_nat(2,n));
    mod_sign(x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b,n)),pow_nat(2,b));
    div_rem(x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b,n)), pow_nat(2,b));
}

lemma void rot_succ(nat b, int x, nat n)
    requires x >= 0 &*& x < pow_nat(2,succ(b))
        &*&  ion(n) + 1 < ion(succ(b));
    ensures  rotl1(b,rot(succ(b),x,n)) == rot(succ(b),x,succ(n));
{
    nat b1 = succ(b);
    assert rot(b1,x,n)
        == (x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))%pow_nat(2,b1);
    assert rotl1(b,rot(b1,x,n))
        == (((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))%pow_nat(2,b1))*2
            + ((x*pow_nat(2,n) +
                    x/pow_nat(2,nat_minus(b1,n)))%pow_nat(2,b1))/pow_nat(2,b))%pow_nat(2,b1);
    div_rem(x,pow_nat(2,nat_minus(b1,n)));
    my_mul_mono_l(0,x,pow_nat(2,n));
    mod_sign((x*pow_nat(2,n) +
              x/pow_nat(2,nat_minus(b1,n))),pow_nat(2,b1));
    div_sign(((x*pow_nat(2,n) +
                    x/pow_nat(2,nat_minus(b1,n)))%pow_nat(2,b1)), pow_nat(2,b));
    mod_plus(
            ((x*pow_nat(2,n) +
              x/pow_nat(2,nat_minus(b1,n)))%pow_nat(2,b1))*2,
            ((x*pow_nat(2,n) +
                    x/pow_nat(2,nat_minus(b1,n)))%pow_nat(2,b1))/pow_nat(2,b),
            pow_nat(2,b1));
    assert rotl1(b,rot(b1,x,n))
        == ((((x*pow_nat(2,n) +
                            x/pow_nat(2,nat_minus(b1,n)))%pow_nat(2,b1))*2)%pow_nat(2,b1)
            + ((x*pow_nat(2,n) +
                    x/pow_nat(2,nat_minus(b1,n)))%pow_nat(2,b1))/pow_nat(2,b))%pow_nat(2,b1);

    mod_times(x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)),2,pow_nat(2,b1));

    assert rotl1(b,rot(b1,x,n))
        == (((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))*2)%pow_nat(2,b1)
            + ((x*pow_nat(2,n) +
                    x/pow_nat(2,nat_minus(b1,n)))%pow_nat(2,b1))/pow_nat(2,b))%pow_nat(2,b1);

    mul_commutes(x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)),2);
    mul_3var(x,2,pow_nat(2,n));

    assert rotl1(b,rot(b1,x,n))
        == ((x*pow_nat(2,succ(n)) + 2*(x/pow_nat(2,nat_minus(b1,n))))%pow_nat(2,b1)
            + ((x*pow_nat(2,n) +
                    x/pow_nat(2,nat_minus(b1,n)))%pow_nat(2,b1))/pow_nat(2,b))%pow_nat(2,b1);

    division_unique(pow_nat(2,b1),pow_nat(2,b),2,0);

    mod_div_factor(x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)),
            pow_nat(2,b1), pow_nat(2,b));

    assert ((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))%pow_nat(2,b1))/pow_nat(2,b)
        == (x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b)
        -  2*((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b1));

    assert rotl1(b,rot(b1,x,n))
        == ((x*pow_nat(2,succ(n)) + 2*(x/pow_nat(2,nat_minus(b1,n))))%pow_nat(2,b1)
            + (x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b)
            -  2*((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b1)))%pow_nat(2,b1);

    mod_plus((x*pow_nat(2,succ(n)) + 2*(x/pow_nat(2,nat_minus(b1,n)))),
        (x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b)
            -  2*((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b1)),
        pow_nat(2,b1));

    assert rotl1(b,rot(b1,x,n))
        == (x*pow_nat(2,succ(n)) + 2*(x/pow_nat(2,nat_minus(b1,n)))
            + (x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b)
            -  2*((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b1)))%pow_nat(2,b1);

    assert rotl1(b,rot(b1,x,n))
        == (2*(x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n))
              - ((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b1)))
            + (x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b))%pow_nat(2,b1);

    assert rot(b1,x,succ(n))
        == (x*(2*pow_nat(2,n)) + x/(pow_nat(2,nat_minus(b1,succ(n)))))%pow_nat(2,b1);

    if(rotl1(b,rot(b1,x,n)) != rot(b1,x,succ(n))) {
        assert (2*(x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n))
              - ((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b1)))
                + (x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b))%pow_nat(2,b1)
            != (x*(2*pow_nat(2,n)) +
                    x/(pow_nat(2,nat_minus(b1,succ(n)))))%pow_nat(2,b1);

        assert 2*(x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n))
                - ((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b1)))
            + (x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b)
            != x*(2*pow_nat(2,n)) + x/(pow_nat(2,nat_minus(b1,succ(n))));

        assert 2*(x/pow_nat(2,nat_minus(b1,n))
                - ((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b1)))
            + (x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b)
            != x/(pow_nat(2,nat_minus(b1,succ(n))));

        assert nat_minus(b1,succ(n)) == nat_minus(b,n);

        assert 2*(x/pow_nat(2,nat_minus(b1,n))
                - ((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b1)))
            + (x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b)
            != x/(pow_nat(2,nat_minus(b,n)));

        if(n == zero) {
            note_eq(nat_minus(b1,n),b1);
            note_eq(nat_minus(b,n),b);
            note_eq(pow_nat(2,n),1);
            assert 2*(x/pow_nat(2,b1)
                    - ((x + x/pow_nat(2,b1))/pow_nat(2,b1)))
                + (x + x/pow_nat(2,b1))/pow_nat(2,b)
                != x/(pow_nat(2,b));

            division_unique(x,pow_nat(2,b1),0,x);

            assert (x)/pow_nat(2,b)
                != x/(pow_nat(2,b));
            assert false;
        }

        if(x == 0) {
            division_zero_unique(pow_nat(2,nat_minus(b1,n)),0,0);
            division_zero_unique(pow_nat(2,nat_minus(b,n)),0,0);
            division_zero_unique(pow_nat(2,b),0,0);
            division_zero_unique(pow_nat(2,b1),0,0);
            note_eq(x/pow_nat(2,nat_minus(b1,n)),0);
            note_eq(x/pow_nat(2,nat_minus(b,n)),0);
            note_eq(x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)),0);
            note_eq((x*pow_nat(2,n) +
                        x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b),0);
            note_eq((x*pow_nat(2,n) +
                        x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b1),0);
            assert false;
        }

        assert x < pow_nat(2,b1);
        assert x*pow_nat(2,n) < pow_nat(2,nat_plus(b1,n));
        assert x*pow_nat(2,n) >= pow_nat(2,n);

        assert false;
    }

    assert rotl1(b,rot(b1,x,n)) - rot(b1,x,succ(n))
        == (2*(x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n))
              - ((x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b1)))
            + (x*pow_nat(2,n) + x/pow_nat(2,nat_minus(b1,n)))/pow_nat(2,b))%pow_nat(2,b1)
        - (x*(2*pow_nat(2,n)) +
                x/(pow_nat(2,nat_minus(b1,succ(n)))))%pow_nat(2,b1);
}

lemma void rot_plus(nat b, int x, nat n, nat m)
    requires x >= 0 &*& x < pow_nat(2,b)
        &*&  ion(n) + ion(m) < ion(b);
    ensures  rot(b,rot(b,x,n),m) == rot(b,x,nat_plus(n,m));
{
    rot_bound(b,x,n);
    rot_bound(b,rot(b,x,n),m);

    assert rot(b,rot(b,x,n),m)
        == (rot(b,x,n)*pow_nat(2,m) + rot(b,x,n)/pow_nat(2,m))
            %pow_nat(2,b);

    assert rot(b,rot(b,x,n),m)
        == (((x*pow_nat(2,n) + x/pow_nat(2,n))%pow_nat(2,b))*pow_nat(2,m)
            + ((x*pow_nat(2,n) + x/pow_nat(2,n))%pow_nat(2,b))/pow_nat(2,m))
            %pow_nat(2,b);

    mod_plus(rot(b,x,n)*pow_nat(2,m),rot(b,x,n)/pow_nat(2,m),pow_nat(2,b));

    assert rot(b,rot(b,x,n),m)
        == ((((x*pow_nat(2,n) +
                            x/pow_nat(2,n))%pow_nat(2,b))*pow_nat(2,m))%pow_nat(2,b)
            + ((x*pow_nat(2,n) + x/pow_nat(2,n))%pow_nat(2,b))/pow_nat(2,m))
            %pow_nat(2,b);

    mod_times((x*pow_nat(2,n) +
                x/pow_nat(2,n)),pow_nat(2,m),pow_nat(2,b));

    assert rot(b,rot(b,x,n),m)
        == (((x*pow_nat(2,n) +
                    x/pow_nat(2,n))*pow_nat(2,m))%pow_nat(2,b)
            + ((x*pow_nat(2,n) + x/pow_nat(2,n))%pow_nat(2,b))/pow_nat(2,m))
            %pow_nat(2,b);

    assert rot(b,rot(b,x,n),m)
        == (((x*pow_nat(2,pow_plus(n,m)) +
                    (x/pow_nat(2,n))*pow_nat(2,m)))%pow_nat(2,b)
            + ((x*pow_nat(2,n) + x/pow_nat(2,n))%pow_nat(2,b))/pow_nat(2,m))
            %pow_nat(2,b);

    assert rot(b,rot(b,x,n),m)
        == (x*pow_nat(2,pow_plus(n,m)) +
            (x/pow_nat(2,n))*pow_nat(2,m)
            + ((x*pow_nat(2,n) + x/pow_nat(2,n))%pow_nat(2,b))/pow_nat(2,m))
            %pow_nat(2,b);

    mod_plus(x*pow_nat(2,n), x/pow_nat(2,n), pow_nat(2,b));
    assert rot(b,x,n)
        == ((x*pow_nat(2,n))%pow_nat(2,b)
        +  x/pow_nat(2,n))%pow_nat(2,b);

    mod_plus(rot(b,x,n)%pow_nat(2,m), rot(b,x,n)*pow_nat(2,m), pow_nat(2,b));
    assert rot(b,x,n)
        == (x*pow_nat(2,n))%pow_nat(2,b)
        +  (x/pow_nat(2,n))%pow_nat(2,b);
    div_rem(x,pow_nat(2,n));
    division_unique(x/pow_nat(2,n),pow_nat(2,b),0,x/pow_nat(2,n));
    assert rot(b,x,n)
        == (x*pow_nat(2,n))%pow_nat(2,b)
        +  x/pow_nat(2,n);
}

lemma void rot_rotates(nat b, int x, nat n, nat m)
    requires x >= 0 &*& x < pow_nat(2,b)
        &*&  ion(n) + ion(m) == ion(b);
    ensures  rot(b,rot(b,x,n),m) == x;
{ }

lemma void chachastate_0_valid()
    requires true;
    ensures  !!valid_chachastate(
        chacha_state(0,0,0,0,
                     0,0,0,0,
                     0,0,0,0,
                     0,0,0,0));
{}

fixpoint fourple<int> qround1(fourple<int> vals) {
    switch(vals) {
    case fourple(a,b,c,d):
        return fourple(a+b,b,c,rot32(d^(a+b),N16));
    }
}

fixpoint fourple<int> qround2(fourple<int> vals) {
    switch(vals) {
    case fourple(a,b,c,d):
        return fourple(a,rot32(b^(c+d),N12),c+d,d);
    }
}

fixpoint fourple<int> qround3(fourple<int> vals) {
    switch(vals) {
    case fourple(a,b,c,d):
        return fourple(a+b,b,c,rot32(d^(a+b),N8));
    }
}

fixpoint fourple<int> qround4(fourple<int> vals) {
    switch(vals) {
    case fourple(a,b,c,d):
        return fourple(a,rot32(b^(c+d),N7),c+d,d);
    }
}

fixpoint list<int> chacha_list(chacha_state cs) {
    switch(cs) {
    case chacha_state(x0,  x1,  x2,  x3,
                      x4,  x5,  x6,  x7,
                      x8,  x9,  x10, x11,
                      x12, x13, x14, x15):
        return { x0,  x1,  x2,  x3,
                 x4,  x5,  x6,  x7,
                 x8,  x9,  x10, x11,
                 x12, x13, x14, x15 };
    }
}

fixpoint fourple<int> chacha_get4(int i, int j, int k, int l,
                           chacha_state cs) {
    return fourple(nth(i,chacha_list(cs)),
                   nth(j,chacha_list(cs)),
                   nth(k,chacha_list(cs)),
                   nth(l,chacha_list(cs)));
}

fixpoint chacha_state chacha_apply4(fixpoint(fourple<int>,fourple<int>) f,
                             int i, int j, int k, int l,
                             chacha_state cs) {
    switch(cs) {
    case chacha_state(x0,  x1,  x2,  x3,
                      x4,  x5,  x6,  x7,
                      x8,  x9,  x10, x11,
                      x12, x13, x14, x15):
        return switch(f(chacha_get4(i,j,k,l,cs))) {
        case fourple(a,b,c,d):
            return chacha_state(
            i == 0 ? a : j == 0 ? b : k == 0 ? c : l == 0 ? d : x0,
            i == 1 ? a : j == 1 ? b : k == 1 ? c : l == 1 ? d : x1,
            i == 2 ? a : j == 2 ? b : k == 2 ? c : l == 2 ? d : x2,
            i == 3 ? a : j == 3 ? b : k == 3 ? c : l == 3 ? d : x3,
            i == 4 ? a : j == 4 ? b : k == 4 ? c : l == 4 ? d : x4,
            i == 5 ? a : j == 5 ? b : k == 5 ? c : l == 5 ? d : x5,
            i == 6 ? a : j == 6 ? b : k == 6 ? c : l == 6 ? d : x6,
            i == 7 ? a : j == 7 ? b : k == 7 ? c : l == 7 ? d : x7,
            i == 8 ? a : j == 8 ? b : k == 8 ? c : l == 8 ? d : x8,
            i == 9 ? a : j == 9 ? b : k == 9 ? c : l == 9 ? d : x9,
            i == 10 ? a : j == 10 ? b : k == 10 ? c : l == 10 ? d : x10,
            i == 11 ? a : j == 11 ? b : k == 11 ? c : l == 11 ? d : x11,
            i == 12 ? a : j == 12 ? b : k == 12 ? c : l == 12 ? d : x12,
            i == 13 ? a : j == 13 ? b : k == 13 ? c : l == 13 ? d : x13,
            i == 14 ? a : j == 14 ? b : k == 14 ? c : l == 14 ? d : x14,
            i == 15 ? a : j == 15 ? b : k == 15 ? c : l == 15 ? d : x15);
        };
    }
}

lemma void chacha_apply4_indep(int i, int j, int k, int l, int x,
        fixpoint(fourple<int>,fourple<int>) f, chacha_state cs)
    requires i >= 0 &*& i < 16 &*&  j >= 0 &*& j < 16
        &*&  k >= 0 &*& k < 16 &*&  x >= 0 &*& x < 16
        &*&  !mem(x,{i,j,k,l});
    ensures  nth(x,chacha_list(cs))
        ==   nth(x,chacha_list(chacha_apply4(f,i,j,k,l,cs)));
{}

fixpoint chacha_state chacha_qround(int a, int b, int c, int d,
                             chacha_state cs) {
    return chacha_apply4(qround4,a,b,c,d,
           chacha_apply4(qround3,a,b,c,d,
           chacha_apply4(qround2,a,b,c,d,
           chacha_apply4(qround1,a,b,c,d,
            cs))));
}


//// key, counter, nonce
//fixpoint chacha_state chacha_init(int k0, int k1, int k2, int k3,
//                                  int c0, int c1, int n0, int n1) {
//
//}

  @*/


