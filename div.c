/*@ #include "div.gh" @*/

#if 1
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif

/*@

lemma void division_zero_unique(int d, int q, int r)
    requires d != 0 &*& abs(r) < abs(d) &*& 0 == d*q + r;
    ensures  q == (0/d) &*& q == 0 &*& r == (0%d) &*& r == 0;
{
ALREADY_PROVEN()
    div_rem(0,d);
    assert abs(0/d*d) == 0;
    assert 0/d*d == 0;
    zero_mul_unique(0/d,d);

    assert 0/d == 0;
    assert 0%d == 0;

    if(r != 0) {
        if(q == 0) {
            assert false;
        }

        assert r == -d*q;
        assert abs(r) == abs(d*q);
        mul_abs_commute(d,q);
        assert abs(r) == abs(d)*abs(q);
        my_mul_mono_r(abs(d),1,abs(q));

        assert false;
    } else {
        zero_mul_unique(q,d);
    }
}

lemma void division_unique(int D, int d, int q, int r)
    requires d != 0 &*& abs(r) < abs(d) &*& abs(d*q) <= abs(D)
        &*&   D == d*q + r;
    ensures  q == (D/d) &*& r == (D%d);
{
ALREADY_PROVEN()
    div_rem(D,d);

    assert D == d*q + r;
    assert D == d*(D/d) + (D%d);

    assert 0 == d*q - d*(D/d) + r - (D%d);
    assert 0 == d*(q - (D/d)) + (r - (D%d));
    division_zero_unique(d,(q-(D/d)),(r-(D%d)));
}

lemma void division_unique_nonneg(int D, int d, int q, int r)
    requires d > 0 &*& r < d
        &*&  q >= 0 &*& D >= 0 &*& r >= 0
        &*&  D == d*q + r;
    ensures  q == (D/d) &*& r == (D%d);
{
    my_mul_mono_l(1,d,q);
    division_unique(D,d,q,r);
}


lemma void mod_sign(int x, int d)
    requires d > 0;
    ensures  x >= 0 ? x%d >= 0 : x%d <= 0;
{ div_rem(x,d); }

lemma void mod_abs(int x, int d)
    requires d > 0;
    ensures  abs(x%d) == abs(x)%d;
{
ALREADY_PROVEN()
    div_rem(x,d);
    if(x < 0) {
        division_unique(-x,d,-(x/d),-(x%d));
    }
}

lemma void mod_plus(int x, int y, int d)
    requires d > 0 &*& x >= 0 &*& y >= 0;
    ensures  (x%d + y)%d == (x+y)%d;
{
ALREADY_PROVEN()
    div_rem(x,d);
    div_rem(x+y,d);

    div_rem(x%d+y,d);

    assert x%d + y == (x%d+y)/d*d + (x%d+y)%d;
    assert x + y == (x+y)/d*d + (x+y)%d;

    assert x - x%d == (x+y)/d*d - (x%d+y)/d*d + (x+y)%d - (x%d+y)%d;

    assert x/d*d == (x+y)/d*d - (x%d+y)/d*d + (x+y)%d - (x%d+y)%d;
    assert x/d*d - (x+y)/d*d + (x%d + y)/d*d == (x+y)%d - (x%d+y)%d;
    assert (x/d - (x+y)/d + (x%d + y)/d)*d == (x+y)%d - (x%d+y)%d;
    mod_sign(x+y,d);
    mod_sign(x,d);
    mod_sign(x%d+y,d);

    assert (x+y)%d >= 0 && (x+y)%d < d;
    assert (x+y)%d >= 0 && (x+y)%d <= d-1;
    assert (x%d+y)%d >= 0 && (x%d+y)%d < d;
    assert -((x%d+y)%d) <= 0 && -((x%d+y)%d) > -d;
    assert -((x%d+y)%d) <= 0 && -((x%d+y)%d) >= -d+1;

    assert (x+y)%d - (x%d+y)%d >= -d+1;
    assert (x+y)%d - (x%d+y)%d <= d-1;

    assert abs((x+y)%d - (x%d+y)%d) < abs(d);

    if(x/d - (x+y)/d + (x%d + y)/d != 0) {
        assert abs(x/d - (x+y)/d + (x%d + y)/d) > 0;
        my_mul_mono_l(1, abs(x/d - (x+y)/d + (x%d + y)/d),d);
        assert abs(x/d - (x+y)/d + (x%d + y)/d)*d >= d;
        mul_abs_commute(x/d - (x+y)/d + (x%d + y)/d,d);

        assert false;
    }

    if((x/d - (x+y)/d + (x%d + y)/d)*d != 0) {
        my_mul_mono_l(0,x/d - (x+y)/d + (x%d + y)/d,d);
        my_mul_mono_l(x/d - (x+y)/d + (x%d + y)/d,0,d);

        assert false;
    }

}

lemma void mod_shrinks(int x, int d)
    requires d != 0;
    ensures  abs(x%d) <= abs(x);
{
    if(abs(x) < abs(x%d)) {
        div_rem(x,d);
        division_unique(x,d,0,x);
        assert false;
    }
}


lemma void mod_times(int x, int y, int d)
    requires d > 0 &*& x >= 0 &*& y >= 0;
    ensures  (x%d * y)%d == (x*y)%d;
{
    ALREADY_PROVEN()
    div_rem(x,d);
    div_rem((x%d)*y,d);
    note_eq(x*y , (d*(x/d) + x%d)*y);
    assert x*y == (d*(x/d))*y + (x%d)*y;
    assert x*y == (d*(x/d))*y + d*(((x%d)*y)/d) + ((x%d)*y)%d;
    mul_3var(d,x/d,y);
    assert x*y == d*((x/d)*y + ((x%d)*y)/d) + ((x%d)*y)%d;
    my_mul_mono_l(0,x,y);
    my_mul_mono_l(0,x%d,y);
    mod_shrinks(x,d);
    my_mul_mono_l(x%d,x,y);
    mod_sign((x%d)*y,d);
    assert ((x%d)*y)%d >= 0;
    assert x*y >= 0;
    division_unique(x*y,d,(x/d)*y + ((x%d)*y)/d,((x%d)*y)%d);
}

lemma void mod_times_d(int x, int y, int d)
    requires d > 0 &*& x >= 0 &*& y >= 0;
    ensures  (x + y*d)%d == x%d;
{
    ALREADY_PROVEN()
    div_rem(x,d);
    mod_sign(x,d);
    mod_shrinks(x,d);
    assert x%d <= x;
    my_mul_mono_l(0,y,d);
    division_unique(x+y*d,d,x/d+y,x%d);
}

lemma void mod_twice(int x, int d1, int d2)
    requires d1 > 0 &*& x >= 0 &*& d2 > 0 &*& d1%d2 == 0;
    ensures  (x%d1)%d2 == x%d2;
{
    ALREADY_PROVEN()
    div_rem(x,d1);
    assert x == d1*(x/d1) + x%d1;
    div_rem(x%d1,d2);
    assert x%d1 == d2*((x%d1)/d2) + (x%d1)%d2;
    div_rem(d1,d2);
    assert d1 == d2*(d1/d2);

    assert x == (d2*(d1/d2))*(x/d1) + d2*((x%d1)/d2) + (x%d1)%d2;
    mul_3var(d2,d1/d2,x/d1);
    assert x == d2*((d1/d2)*(x/d1) + (x%d1)/d2) + (x%d1)%d2;

    mod_sign(x,d1);
    mod_shrinks(x,d1);
    assert x%d1 >= 0 &*& x%d1 <= x;
    mod_sign(x%d1,d2);
    mod_shrinks(x%d1,d2);
    assert (x%d1)%d2 >= 0 &*& (x%d1)%d2 <= x;

    division_unique(x,d2,(d1/d2)*(x/d1) + (x%d1)/d2,(x%d1)%d2);
}

lemma void mod_2(int x)
    requires x >= 0;
    ensures  x%2 == 0 ? true : x%2 == 1;
{
    div_rem(x,2);
    mod_sign(x,2);
    if(x%2 <= 0) {}
    else if(x%2 <= 1) {}
    else { assert false; }
}


lemma void euclid_div_zero(int d, int q, int r)
    requires d > 0 &*& r >= 0 &*& r < d &*& 0 == q*d + r;
    ensures  q == 0 &*& r == 0;
{
    ALREADY_PROVEN()
    if(q > 0) {
        my_mul_mono_l(1,q,d);
        assert false;
    }
    if(q < 0) {
        my_mul_mono_l(q,-1,d);
        assert false;
    }
    if(r > 0) {
        assert false;
    }
}

lemma void euclid_div_unique(int D, int d, int q1, int r1,
                                           int q2, int r2)
    requires d > 0 &*& r1 >= 0 &*& r1 < d &*& D == q1*d + r1
        &*&  r2 >= 0 &*& r2 < d &*& D == q2*d + r2;
    ensures  q1 == q2 &*& r1 == r2;
{
    ALREADY_PROVEN()
    if(r2 >= r1) {
        euclid_div_zero(d,q2-q1,r2-r1);
    } else {
        euclid_div_zero(d,q1-q2,r1-r2);
    }
}

lemma void euclid_div_intro(int D, int d)
    requires d > 0;
    ensures [_]euclid_div_sol(D, d, fst(euclid_divmod(D, d)),
                snd(euclid_divmod(D, d)));
{
    euclid_div_correct(noi(abs(D)),D,d,0);
    close euclid_div_sol(D,d,_,_);
    leak euclid_div_sol(D,d,_,_);
}

lemma_auto void euclid_div_auto()
    requires [?f]euclid_div_sol(?D,?d,?q,?r);
    ensures  [ f]euclid_div_sol( D, d, q, r)
        &*&  r >= 0 &*& r < d &*& d > 0 &*& D == q*d + r;
{
    ALREADY_PROVEN()
    if(!(r >= 0 && r < d && d > 0 && D == q*d + r)) {
        open euclid_div_sol(_,_,_,_);
        assert false;
    }
}

lemma void euclid_div_unique_intro(int D, int d, int q, int r)
    requires d > 0 &*& r >= 0 &*& r < d &*& D == q*d + r;
    ensures  [_]euclid_div_sol(D,d,q,r)
        &*&  euclid_divmod(D,d) == pair(q,r);
{
    ALREADY_PROVEN()
    nat f = noi(abs_of(D));
    int_of_nat_of_int(abs_of(D));
    euclid_div_correct(f,D,d,0);
    switch(euclid_div_inner(f,D,d,0)) {
    case pair(q1,r1):
        close euclid_div_sol(D,d,q1,r1);
        leak euclid_div_sol(D,d,q1,r1);
        euclid_div_unique(D,d,q,r,q1,r1);
    }
}

lemma void euclid_mod_correct(int D, int d)
    requires d > 0;
    ensures  [_]euclid_div_sol(D,d,_,euclid_mod(D,d));
{
    ALREADY_PROVEN()
    int_of_nat_of_int(abs_of(D));
    euclid_div_correct(noi(abs_of(D)),D,d,0);
    switch(euclid_divmod(D,d)) {
    case pair(q,r):
        euclid_div_unique_intro(D,d,q,r);
    }
}

lemma void euclid_div_exact(int D, int d, int q, int r)
    requires d > 0 &*& r >= 0 &*& r < d &*& D == q*d + r;
    ensures  euclid_divmod(D,d) == pair(q,r);
{
    ALREADY_PROVEN()
    if(euclid_divmod(D,d) != pair(q,r)) {
        euclid_div_unique_intro(D,d,q,r);
        assert false;
    }
}

lemma void euclid_div_sign(int D, int d)
    requires d > 0;
    ensures  (fst(euclid_divmod(D,d)) <  0) == (D < 0)
        &*&  (fst(euclid_divmod(D,d)) == 0) == (D >= 0 && D < d)
        &*&  (fst(euclid_divmod(D,d)) >  0) == (D >= d)
        ;
{
    ALREADY_PROVEN()
    euclid_div_intro(D,d);
    assert [_]euclid_div_sol(D,d,?q,?r);
    euclid_div_exact(D,d,q,r);
    assert euclid_divmod(D,d) == pair(q,r);
    assert d*q + r == D;
    if(D < 0) {
        if(q >= 0) {
            my_mul_mono_r(d,0,q);
            assert false;
        }
    } else {
        if(q < 0) {
            my_mul_mono_r(d,q,-1);
            assert false;
        }

        if(D < d) {
            euclid_div_exact(D,d,0,D);
        }
    }

}

lemma_auto(euclid_mod(D,d))
void euclid_mod_auto(int D, int d)
    requires d > 0;
    ensures euclid_mod(D, d) == (D % d + d) % d;

{
    ALREADY_PROVEN()
    euclid_mod_correct(D,d);
    open [_]euclid_div_sol(D,d,?q, euclid_mod(D, d));
    div_rem(D,d);
    if(D%d >= 0) {
        euclid_div_unique(D,d, q, euclid_mod(D,d), D/d, D%d);
        division_unique( D%d + d, d, 1, D%d);
    } else {
        euclid_div_unique(D, d, q, euclid_mod(D, d), D/d-1,
                D%d + d);
        division_unique(D%d + d, d, 0, D%d + d);
    }
}

lemma
void euclid_div_equiv(int D, int d)
    requires d > 0;
    ensures  D%d >= 0
        ? euclid_divmod(D,d) == pair(D/d,D%d)
        : euclid_divmod(D,d) == pair(D/d-1,D%d+d)
        ;
{
    ALREADY_PROVEN()
    div_rem(D,d);
    if(D%d >= 0) {
        euclid_div_exact(D,d,D/d,D%d);
    } else {
        euclid_div_exact(D,d,D/d-1,D%d+d);
    }
}

lemma_auto(euclid_divmod(D,d))
void euclid_div_equiv_pos(int D, int d)
    requires d > 0;
    ensures  (D%d >= 0) == (euclid_divmod(D,d) == pair(D/d,D%d));
{ euclid_div_equiv(D,d); }

lemma_auto(euclid_divmod(D,d))
void euclid_div_equiv_neg(int D, int d)
    requires d > 0;
    ensures  (D%d < 0) == (euclid_divmod(D,d) == pair(D/d-1,D%d+d));
{ euclid_div_equiv(D,d); }

lemma void euclid_div_mono_numerator(int x, int y, int d)
    requires d > 0 &*& y >= x;
    ensures  fst(euclid_divmod(x,d)) <= fst(euclid_divmod(y,d));
{
    euclid_div_intro(x,d);
    assert [_]euclid_div_sol(x,d,?xq,?xr);
    euclid_div_intro(y,d);
    assert [_]euclid_div_sol(y,d,?yq,?yr);

    if(xq > yq) {
        assert d*xq + xr <= d*yq + yr;
        assert d*xq + xr <= d*(yq + 1);

        my_mul_mono_r(d,yq+1,xq);

        assert false;
    }
}

lemma_auto(euclid_div(D,d))
void euclid_div_more_neg(int D, int d)
    requires d > 0;
    ensures  euclid_div(D,d) <= D/d;
{
    euclid_div_intro(D,d);
    euclid_div_equiv(D,d);
}

lemma void euclid_div_mono_denominator(int D, int x, int y)
    requires x > 0 &*& y >= x;
    ensures  D >= 0
        ?    fst(euclid_divmod(D,y)) <= fst(euclid_divmod(D,x))
        :    fst(euclid_divmod(D,y)) >= fst(euclid_divmod(D,x))
        ;
{
    euclid_div_intro(D,x);
    assert [_]euclid_div_sol(D,x,?xq,?xr);
    euclid_div_intro(D,y);
    assert [_]euclid_div_sol(D,y,?yq,?yr);
    euclid_div_sign(D,x);
    euclid_div_sign(D,y);

    if(D >= 0) {
        if(yq > xq) {
            my_mul_mono_r(x,xq+1,yq);
            my_mul_mono_l(x,y,yq);

            assert false;
        }
    } else {
        assert yq <= 0;
        assert xq <= 0;
        if(-yq > -xq) {
            assert x*xq + xr <= y*yq + yr;
            assert -xq+1 <= -yq;
            my_mul_mono_r(y,-xq+1,-yq);
            assert y*(-xq+1) <= -y*yq;
            my_mul_mono_l(x,y,-xq);

            assert false;
        }
    }
}


lemma_auto(euclid_mod(D,d))
void euclid_mod_nonneg_auto(int D, int d)
    requires d > 0;
    ensures (D >= 0 || D%d == 0) == (euclid_mod(D, d) == D%d);
{
    ALREADY_PROVEN()
    div_rem(D,d);
    mod_sign(D,d);
    if(D < 0 && D%d != 0 && euclid_mod(D,d) == D%d) {
        assert false;
    }

    if(D%d == 0 && euclid_mod(D,d) != D%d) {
        assert false;
    }

    if(D >= 0 && euclid_mod(D,d) != D%d) {
        assert false;
    }
}

lemma_auto(euclid_mod(euclid_mod(D,d),d))
void euclid_mod_mod(int D, int d)
    requires d > 0;
    ensures euclid_mod(euclid_mod(D,d), d) == euclid_mod(D,d);
{
    ALREADY_PROVEN()
    euclid_mod_correct(D,d);
    euclid_mod_correct(euclid_mod(D,d),d);
    open [_]euclid_div_sol(euclid_mod(D, d),d,?q, ?r);
    euclid_div_unique(euclid_mod(D,d),d,q,r,0,euclid_mod(D,d));
}

lemma_auto(euclid_mod(d,d))
void euclid_mod_self(int D, int d)
    requires d > 0;
    ensures euclid_mod(d,d) == 0;
{
    ALREADY_PROVEN()
    euclid_div_unique_intro(d,d,1,0);
}

lemma_auto(euclid_mod(D,d))
void euclid_mod_small(int D, int d)
    requires D >= 0 && D < d  && d > 0;
    ensures euclid_mod(D,d) == D;
{
    ALREADY_PROVEN()
    euclid_div_unique_intro(D,d,0,D);
}

lemma_auto(euclid_mod(D,d))
void euclid_mod_nonneg(int D, int d)
    requires d > 0;
    ensures euclid_mod(D,d) >= 0;
{
    ALREADY_PROVEN()
    euclid_mod_correct(D,d);
}

lemma_auto(euclid_mod(D,d))
void euclid_mod_below_d(int D, int d)
    requires d > 0;
    ensures euclid_mod(D,d) < d;
{
    ALREADY_PROVEN()
    euclid_mod_correct(D,d);
}

lemma void div_monotonic_numerator(int x, int y, int d)
    requires d > 0 &*& x >= 0 &*& y >= x;
    ensures  x/d <= y/d;
{
    ALREADY_PROVEN()
    div_rem(x,d);
    div_rem(y,d);

    if(y/d < x/d) {
        my_mul_mono_r(d,y/d+1,x/d);
        assert false;
    }
}

lemma void div_negate(int D, int d)
    requires d > 0;
    ensures  (-D)/d == -(D/d);
{
    ALREADY_PROVEN()
    div_rem(D,d);
    division_unique(-D,d,-(D/d),-(D%d));
}

lemma void into_numerator(int x, int y, int d)
    requires d > 0 &*& x >= 0 &*& y >= 0;
    ensures  x + (y/d) == (d*x + y)/d;
{
    ALREADY_PROVEN()
    division_unique(x*d,d,x,0);
    div_rem(d*x + y,d);

    division_unique(d*x,d,x,0);
    assert (d*x)/d == x;

    my_mul_mono_r(d,0,x);

    assert d*((d*x+y)/d) + (d*x + y)%d == d*x + y;
    assert d*((d*x+y)/d) - d*x + (d*x + y)%d == y;
    assert d*((d*x+y)/d - x) + (d*x + y)%d == y;
    div_monotonic_numerator(y,d*x+y,d);
    div_monotonic_numerator(d*x,d*x+y,d);

    assert ((d*x+y)/d - x) >= 0;
    assert (d*x + y)%d >= 0;
    assert d*((d*x+y)/d - x) <= y;
    my_mul_mono_r(d,0,((d*x+y)/d - x));
    assert d*((d*x+y)/d - x) >= 0;

    //assert (d*x+y)/d >= x;

    division_unique(y,d,(d*x+y)/d - x,(d*x + y)%d);
    (d*x + y)/d - x == y/d;
}

lemma void div_sign(int x, int d)
    requires d > 0;
    ensures  x >= 0 ? x/d >= 0 : x/d <= 0;
{
    ALREADY_PROVEN()
    div_rem(x,d);
    if(x >= 0 && x/d < 0) {
        mul_mono_l(x/d,-1,d);
        assert false;
    }

    if(x < 0 && x/d > 0) {
        mul_mono_l(1,x/d,d);
        assert false;
    }
}

lemma void div_monotonic_denominator(int D, int x, int y)
    requires D > 0 &*& x > 0 &*& y >= x;
    ensures  D/y <= D/x;
{
    ALREADY_PROVEN()
    div_rem(D,x); div_rem(D,y);
    div_sign(D,y);

    if(D/x < D/y) {
        my_mul_mono_r(x,D/x+1,D/y);
        my_mul_mono_l(x,y,D/y);

        assert false;
    }
}

lemma void div_shrinks(int x, int d)
    requires d > 0;
    ensures  abs_of(x/d) <= abs_of(x);
{
    if(abs_of(x/d) > abs_of(x)) {
        div_rem(x,d);
        assert abs_of(d*(x/d)) <= abs_of(x);
        mul_abs_commute(d,x/d);
        my_mul_strict_mono_l(1,d,abs_of(x/d));
        assert false;
    }
}

lemma void div_twice(int x, int y, int z)
    requires y != 0 &*& z != 0;
    ensures  (x/y)/z == x/(y*z);

{
    ALREADY_PROVEN()
    if(y*z == 0) mul_to_zero(y,z);
    div_rem(x,y);
    div_rem(x/y,z);
    div_rem(x%y,z);
    div_rem(x,y*z);
    mul_3var(y,z,(x/y)/z);

    assert x == y*(x/y) + x%y;
    assert x/y == z*((x/y)/z) + (x/y)%z;
    note_eq( x ,  y*(z*((x/y)/z) + (x/y)%z) + x%y);
    assert x == y*(z*((x/y)/z)) + y*((x/y)%z) + x%y;
    assert x == (y*z)*((x/y)/z) + y*((x/y)%z) + x%y;
    assert x == (y*z)*((x/y)/z) + y*((x/y)%z) + z*((x%y)/z) + (x%y)%z;

    if(abs_of((y*z)*((x/y)/z)) > abs(x)) {
        assert abs_of(z*((x/y)/z)) <= abs_of(x/y);
        mul_abs_commute(y,x/y);
        assert abs_of(y*(x/y)) <= abs_of(x);
        assert abs_of(y)*abs_of(x/y) <= abs_of(x);
        my_mul_mono_r(abs_of(y),abs_of(z*((x/y)/z)),abs_of(x/y));
        assert abs_of(y)*abs_of(z*((x/y)/z)) <= abs_of(x);
        mul_abs_commute(z,(x/y)/z);
        assert abs_of(y)*(abs_of(z)*abs_of((x/y)/z)) <= abs_of(x);
        mul_assoc(abs_of(y),abs_of(z),abs_of((x/y)/z));
        assert (abs_of(y)*abs_of(z))*abs_of((x/y)/z) <= abs_of(x);
        mul_abs_commute(y,z);
        assert abs_of(y*z)*abs_of((x/y)/z) <= abs_of(x);
        mul_abs_commute(y*z,(x/y)/z);
        assert false;
    }

    if(abs_of(y*((x/y)%z) + x%y) >= abs_of(y*z)) {
        assert abs((x/y)%z) <= abs(z)-1;
        my_mul_mono_r(abs_of(y),abs_of((x/y)%z),abs_of(z)-1);
        mul_abs_commute(y,(x/y)%z);
        mul_abs_commute(y,z);
        assert false;
    }

    division_unique(x,y*z,(x/y)/z,y*((x/y)%z) + x%y);
}



  @*/

