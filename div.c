/*@ #include "div.gh" @*/

/*@

lemma void division_zero_unique(int d, int q, int r)
    requires d != 0 &*& abs(r) < abs(d) &*& 0 == d*q + r;
    ensures  q == (0/d) &*& q == 0 &*& r == (0%d) &*& r == 0;
{
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
    div_rem(D,d);

    assert D == d*q + r;
    assert D == d*(D/d) + (D%d);

    assert 0 == d*q - d*(D/d) + r - (D%d);
    assert 0 == d*(q - (D/d)) + (r - (D%d));
    division_zero_unique(d,(q-(D/d)),(r-(D%d)));
}

lemma void mod_sign(int x, int d)
    requires d > 0;
    ensures  x >= 0 ? x%d >= 0 : x%d <= 0;
{ div_rem(x,d); }

lemma void mod_abs(int x, int d)
    requires d > 0;
    ensures  abs(x%d) == abs(x)%d;
{
    div_rem(x,d);
    if(x < 0) {
        division_unique(-x,d,-(x/d),-(x%d));
    }
}

lemma void mod_plus(int x, int y, int d)
    requires d > 0 &*& x >= 0 &*& y >= 0;
    ensures  (x%d + y)%d == (x+y)%d;
{
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

lemma void euclid_div_zero(int d, int q, int r)
    requires d > 0 &*& r >= 0 &*& r < d &*& 0 == q*d + r;
    ensures  q == 0 &*& r == 0;
{
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
    if(r2 >= r1) {
        euclid_div_zero(d,q2-q1,r2-r1);
    } else {
        euclid_div_zero(d,q1-q2,r1-r2);
    }
}

lemma void euclid_div_intro(int D, int d)
    requires d > 0;
    ensures  [_]euclid_div_sol(D,d,_,_);
{
    euclid_div_correct(nat_of_int(abs(D)),D,d,0);
    close euclid_div_sol(D,d,_,_);
    leak euclid_div_sol(D,d,_,_);
}

lemma_auto void euclid_div_auto()
    requires [?f]euclid_div_sol(?D,?d,?q,?r);
    ensures  [ f]euclid_div_sol( D, d, q, r)
        &*&  r >= 0 &*& r < d &*& d > 0 &*& D == q*d + r;
{
    if(!(r >= 0 && r < d && d > 0 && D == q*d + r)) {
        open euclid_div_sol(_,_,_,_);
        assert false;
    }
}

lemma void euclid_div_unique_intro(int D, int d, int q, int r)
    requires d > 0 &*& r >= 0 &*& r < d &*& D == q*d + r;
    ensures  [_]euclid_div_sol(D,d,q,r)
        &*&  euclid_div(D,d) == pair(q,r);
{
    nat f = nat_of_int(abs_of(D));
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
    int_of_nat_of_int(abs_of(D));
    euclid_div_correct(nat_of_int(abs_of(D)),D,d,0);
    switch(euclid_div(D,d)) {
    case pair(q,r):
        euclid_div_unique_intro(D,d,q,r);
    }
}

lemma_auto(euclid_mod(D,d))
void euclid_mod_auto(int D, int d)
    requires d > 0;
    ensures euclid_mod(D, d) == (D % d + d) % d;

{
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

lemma_auto(euclid_mod(euclid_mod(D,d),d))
void euclid_mod_mod(int D, int d)
    requires d > 0;
    ensures euclid_mod(euclid_mod(D,d), d) == euclid_mod(D,d);
{
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
    euclid_div_unique_intro(d,d,1,0);
}

lemma_auto(euclid_mod(D,d))
void euclid_mod_small(int D, int d)
    requires D >= 0 && D < d  && d > 0;
    ensures euclid_mod(D,d) == D;
{
    euclid_div_unique_intro(D,d,0,D);
}

lemma_auto(euclid_mod(D,d))
void euclid_mod_nonneg(int D, int d)
    requires d > 0;
    ensures euclid_mod(D,d) >= 0;
{
    euclid_mod_correct(D,d);
}

lemma_auto(euclid_mod(D,d))
void euclid_mod_below_d(int D, int d)
    requires d > 0;
    ensures euclid_mod(D,d) < d;
{
    euclid_mod_correct(D,d);
}

lemma void div_monotonic_numerator(int x, int y, int d)
    requires d > 0 &*& x >= 0 &*& y >= x;
    ensures  x/d <= y/d;
{
    div_rem(x,d);
    div_rem(y,d);

    if(y/d < x/d) {
        my_mul_mono_r(d,y/d+1,x/d);
        assert false;
    }
}

lemma void into_numerator(int x, int y, int d)
    requires d > 0 &*& x >= 0 &*& y >= 0;
    ensures  x + (y/d) == (d*x + y)/d;
{
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
    div_rem(D,x); div_rem(D,y);
    div_sign(D,y);

    if(D/x < D/y) {
        my_mul_mono_r(x,D/x+1,D/y);
        my_mul_mono_l(x,y,D/y);

        assert false;
    }
}

lemma void div_shrinks(int x, int d)
    requires d > 0 &*& x >= 0;
    ensures  x/d <= x;
{
    if(x/d > x) {
        div_sign(x,d);
        mod_sign(x,d);
        div_rem(x,d);

        my_mul_mono_l(1,d,x);
        my_mul_strict_mono_r(d,x,x/d);

        assert false;
    }
}

lemma void div_twice(int x, int y, int z)
    requires y != 0 &*& z != 0;
    ensures  (x/y)/z == x/(y*z);

{
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

