/*@ #include "mul.gh" @*/

/*@

// mul_mono_r/l from verifast's test/longlong.c, renamed because a later
// version of verifast has these in its prelude
lemma void my_mul_mono_l(int a1, int a2, int b)
    requires a1 <= a2 &*& 0 <= b;
    ensures a1 * b <= a2 * b;
{
    for (int i = 0; i < b; i++)
        invariant i <= b &*& a1 * i <= a2 * i;
        decreases b - i;
    {}
}

lemma void my_mul_mono_r(int a, int b1, int b2)
    requires 0 <= a &*& b1 <= b2;
    ensures a * b1 <= a * b2;
{
    for (int i = 0; i < a; i++)
        invariant i <= a &*& i * b1 <= i * b2;
        decreases a - i;
    {}
}

lemma void my_mul_strict_mono_l(int a1, int a2, int b)
    requires a1 < a2 &*& 0 < b;
    ensures a1 * b < a2 * b;
{
    for (int i = 1; i < b; i++)
        invariant i <= b &*& a1 * i < a2 * i;
        decreases b - i;
    {}
}

lemma void my_mul_strict_mono_r(int a, int b1, int b2)
    requires 0 < a &*& b1 < b2;
    ensures a * b1 < a * b2;
{
    for (int i = 1; i < a; i++)
        invariant i <= a &*& i * b1 < i * b2;
        decreases a - i;
    {}
}

lemma void my_inv_mul_strict_mono_r(int a, int b1, int b2)
    requires 0 < a &*& a*b1 < a*b2;
    ensures b1 < b2;
{
    if(b1 >= b2) {
        my_mul_mono_r(a,b2,b1);
        assert false;
    }
}

lemma void mul_assoc(int x, int y, int z)
    requires true;
    ensures x*(y*z) == (x*y)*z;
{
    if(x == 0) { return; }
    if(x > 0) {
        for(int i =  1; i < x; ++i)
            invariant i >=  1 &*& i <= x &*& i*(y*z) == (i*y)*z;
            decreases x-i;
        { note_eq(((i+1)*y)*z, (i*y+y)*z); }
    } else { assert x < 0;
        for(int i = -1; i > x; --i)
            invariant i <= -1 &*& i >= x &*& i*(y*z) == (i*y)*z;
            decreases i-x;
        { note_eq(((i-1)*y)*z, (i*y-y)*z); }
    }
}

lemma void mul_commutes(int a, int b)
    requires true;
    ensures  a*b == b*a;
{
    if(a >= 0) {
        for(int i = 0; i < a; ++i)
            invariant i*b == b*i
                &*&   0 <= i &*& i <= a;
            decreases a-i;
        { }
    } else {
        for(int i = 0; i > a; --i)
            invariant i*b == b*i
                &*&   0 >= i &*& i >= a;
            decreases i-a;
        { }
    }
}

lemma void mul_3var(int x,int y,int z)
    requires true;
    ensures  x*(y*z) == (x*y)*z
        &*&  x*(y*z) == x*(z*y)
        &*&  x*(y*z) == (x*z)*y
        &*&  x*(y*z) == (y*x)*z
        &*&  x*(y*z) == y*(x*z)
        &*&  x*(y*z) == y*(z*x);
{
    mul_assoc(x,y,z);
    mul_assoc(x,z,y);
    mul_assoc(y,x,z);
    mul_assoc(y,z,x);
    mul_assoc(z,x,y);
    mul_assoc(z,y,x);
    mul_commutes(x,y);
    mul_commutes(x,z);
    mul_commutes(y,z);
}

lemma void mul_abs_commute(int x, int y)
    requires true;
    ensures  abs(x)*abs(y) == abs(x*y);
{
    if(y >= 0) {
        assert abs(y) == y;
        if(x >= 0) {
            assert abs(x) == x;
            my_mul_mono_r(x,0,y);
            assert x*y >= 0; assert abs(x*y) == x*y;
            assert abs(x*y) == abs(x)*abs(y);

        } else {
            my_mul_mono_l(x,-1,y);
            assert x*y <= -y;
            assert x*y <= 0;
            assert abs(x*y) == -(x*y);
            assert abs(x) == -x;
            as_mul(-x,y);
            assert abs(x*y) == (-x)*y;
            assert abs(x*y) == abs(x)*y;
            assert abs(x*y) == abs(x)*abs(y);
        }

    } else {
        assert y < 0;
        assert abs(y) == -y;
        assert y <= -1;

        if(x >= 0) {
            my_mul_mono_r(x,y,-1);
            assert x*y <= -x;
            assert x*y <= 0;
            assert abs(x*y) == -(x*y);
            assert abs(x*y) == x*(-y);
            as_mul(x,-y);
            assert abs(x*y) == x*abs(y);

            assert abs(x*y) == abs(x)*abs(y);

        } else {
            assert x < 0;
            assert abs(x) == -x;
            assert x*y == (-x)*(-y);
            my_mul_mono_l(1,-x,-y);
            assert -y <= (-x)*(-y);
            assert abs(x*y) == x*y;
            as_mul(-x,-y);

            assert abs(x*y) == abs(x)*abs(y);
        }


    }
}

lemma void zero_mul_unique(int x, int y)
    requires y != 0;
    ensures  (x*y == 0) == (x == 0);
{
    if(x == 0) {
        assert x*y == 0;
    } else if(x*y == 0) {
        assert abs(x*y) == 0;
        assert abs(y) != 0;
        assert abs(x) != 0;
        assert abs(x) > 0;
        assert abs(x) >= 1;
        mul_abs_commute(x,y);
        assert abs(x*y) == abs(x)*abs(y);
        my_mul_mono_l(1,abs(x),abs(y));
        assert false;
    }
}

lemma void mul_to_zero(int x, int y)
    requires x*y == 0;
    ensures  x == 0 || y == 0;
{
    assert abs_of(x*y) == 0;
    mul_abs_commute(x,y);
    note_eq(abs_of(x)*abs_of(y),0);
    if(abs_of(x) > 0 && abs_of(y) > 0) {
        my_mul_mono_l(1,abs_of(x),abs_of(y));
        assert false;
    }
}

lemma_auto(pow_nat(x,n))
void pow_nat_pos(int x, nat n)
    requires x >= 1;
    ensures  pow_nat(x,n) >= 1;
{
    switch(n) {
    case zero:
    case succ(n0):
        pow_nat_pos(x,n0);
        my_mul_mono_l(1,x,pow_nat(x,n0));
    }
}

lemma_auto(pow_nat(x,nat_of_int(n)))
void pow_nat_int_pos(int x, int n)
    requires x >= 1;
    ensures  pow_nat(x,nat_of_int(n)) >= 1;
{ pow_nat_pos(x,nat_of_int(n)); }

lemma_auto(pow_nat(x,nat_of_int(n)))
void pow_nat_hard_pos(int x, int n)
    requires x > 1 && n > 0;
    ensures  pow_nat(x,nat_of_int(n)) > 1;
{
    pow_nat_pos(x,nat_of_int(n-1));
    assert nat_of_int(n) == succ(nat_of_int(n-1));
    my_mul_strict_mono_l(1,x,pow_nat(x,nat_of_int(n-1)));
}

lemma void pow_plus(int x,nat y,int z)
    requires z >= 0;
    ensures  pow_nat(x,nat_of_int(int_of_nat(y)+z))
        ==   pow_nat(x,y)*pow_nat(x,nat_of_int(z));
{
    switch(y) {
    case zero:
    case succ(y0):
        pow_plus(x,y0,z);
        mul_assoc(x,pow_nat(x,y0),pow_nat(x,nat_of_int(z)));
        assert nat_of_int(int_of_nat(y)+z)
            == succ(nat_of_int(int_of_nat(y0)+z));
    }
}

lemma void pow_times1(int x,int y,nat z)
    requires true;
    ensures  pow_nat(x,z)*pow_nat(y,z)
        ==   pow_nat(x*y,z);
{
    switch(z) {
    case zero:
    case succ(z0):
        pow_times1(x,y,z0);
        mul_3var(x,pow_nat(x,z0),y*pow_nat(y,z0));
        mul_3var(pow_nat(x,z0),y,pow_nat(y,z0));
        mul_3var(x,y,pow_nat(x,z0)*pow_nat(y,z0));
        assert pow_nat(x,z)*pow_nat(y,z)
            == (x*pow_nat(x,z0))*(y*pow_nat(y,z0));
        assert pow_nat(x,z)*pow_nat(y,z)
            == x*(pow_nat(x,z0)*(y*pow_nat(y,z0)));
        assert pow_nat(x,z)*pow_nat(y,z)
            == x*(y*(pow_nat(x,z0)*pow_nat(y,z0)));
    }
}

lemma void pow_times2(int x,nat y,int z)
    requires z >= 0;
    ensures  pow_nat(x,nat_of_int(int_of_nat(y)*z))
        ==   pow_nat(pow_nat(x,y),nat_of_int(z));
{
    switch(y) {
    case zero:
    case succ(y0):
        assert nat_of_int(int_of_nat(y))
            == succ(nat_of_int(int_of_nat(y0)));
        note_eq( int_of_nat(y) , 1+int_of_nat(y0));
        note_eq((1+int_of_nat(y0))*z,z + int_of_nat(y0)*z);

        assert pow_nat(x,nat_of_int(int_of_nat(y)*z))
            == pow_nat(x,nat_of_int((1+int_of_nat(y0))*z));
        assert pow_nat(x,nat_of_int(int_of_nat(y)*z))
            == pow_nat(x,nat_of_int(z + int_of_nat(y0)*z));
        my_mul_mono_r(int_of_nat(y0),0,z);
        pow_plus(x,nat_of_int(z),int_of_nat(y0)*z);
        assert pow_nat(x,nat_of_int(int_of_nat(y)*z))
            == pow_nat(x,nat_of_int(z))
              *pow_nat(x,nat_of_int(int_of_nat(y0)*z));
        pow_times2(x,y0,z);
        pow_times1(x,pow_nat(x,y0),nat_of_int(z));
    }
}

lemma void pow_monotonic(int x,nat y,nat z)
    requires x > 1 &*& int_of_nat(y) < int_of_nat(z);
    ensures  pow_nat(x,y) < pow_nat(x,z);
{
    switch(y) {
    case zero:
        switch(z) {
        case zero: assert false;
        case succ(z0):
            pow_nat_pos(x,z0);
            my_mul_mono_r(x,1,pow_nat(x,z0));
        }
    case succ(y0):
        switch(z) {
        case zero: assert false;
        case succ(z0):
            pow_monotonic(x,y0,z0);
            my_mul_strict_mono_r(x,pow_nat(x,y0),pow_nat(x,z0));
        }
    }
}

lemma void pow_soft_monotonic(int x,nat y,nat z)
    requires x >= 1 &*& int_of_nat(y) <= int_of_nat(z);
    ensures  pow_nat(x,y) <= pow_nat(x,z);
{
    if(x > 1 && int_of_nat(y) != int_of_nat(z)) pow_monotonic(x,y,z);
    else if(int_of_nat(y) == int_of_nat(z)) {
        assert nat_of_int(int_of_nat(y)) == y;
        assert nat_of_int(int_of_nat(z)) == z;
        assert pow_nat(x,y) == pow_nat(x,z);
    } else { assert x == 1;
        assert pow_nat(x,y) == 1;
        assert pow_nat(x,z) == 1;
    }
}

lemma_auto(factorial(n))
void factorial_positive(nat n)
    requires true;
    ensures factorial(n) >= 1;
{
    switch(n) {
    case zero:
    case succ(n0):
        factorial_positive(n0);
        my_mul_mono_r(int_of_nat(n),1,factorial(n0));
    }
}


  @*/

