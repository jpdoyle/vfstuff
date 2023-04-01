/*@ #include "bitops.gh" @*/
#include "bitops.h"

#if 1
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif

/*@

lemma void truncate_unsigned_def2(int x, nat n)
    requires true;
    ensures  euclid_mod(x,pow_nat(2,n))
        ==   truncate_unsigned(x, ion(n));
{
    truncate_unsigned_def(x,n);
    assert [_]divrem(x,pow_nat(2,n),?q,?r);
    divrem_elim();
    euclid_div_exact(x,pow_nat(2,n),q,r);
}

lemma_auto(truncate_unsigned(x,nb)) void truncate_unsigned_def2_auto(int x, int nb)
    requires nb >= 0;
    ensures truncate_unsigned(x, nb)
        == (x % pow_nat(2, noi(nb)) + pow_nat(2,noi(nb))) % pow_nat(2, noi(nb));
{
    truncate_unsigned_def2(x,noi(nb));
    euclid_mod_auto(x, pow_nat(2, noi(nb)));
    int_of_nat_of_int(nb);
}

lemma_auto(Z_size(z))
void Z_size_nonneg(Z z)
    requires true;
    ensures  Z_size(z) >= 0;
{
    ALREADY_PROVEN()
    switch(z) {
    case Zsign(b):
    case Zdigit(z0,b0): Z_size_nonneg(z0);
    }
}

lemma_auto(Z_is_neg(z))
void Z_neg_auto(Z z)
    requires true;
    ensures  Z_is_neg(z) == (int_of_Z(z) < 0);
{
    ALREADY_PROVEN()
    switch(z) {
    case Zsign(b):
    case Zdigit(z0,b0): Z_neg_auto(z0);
    }
}

lemma_auto(Z_size(z))
void Z_size_bound_pos(Z z)
    requires !Z_is_neg(z);
    ensures  int_of_Z(z) < pow_nat(2,noi(Z_size(z)));
{
    ALREADY_PROVEN()
    switch(z) {
    case Zsign(b):
    case Zdigit(z0,b0):
        Z_size_bound_pos(z0);
        assert noi(Z_size(z)) == succ(noi(Z_size(z0)));
    }
}

lemma_auto(Z_size(z))
void Z_size_bound_neg(Z z)
    requires !!Z_is_neg(z);
    ensures  -int_of_Z(z) <= pow_nat(2,noi(Z_size(z)));
{
    ALREADY_PROVEN()
    switch(z) {
    case Zsign(b):
    case Zdigit(z0,b0):
        Z_size_bound_neg(z0);
        assert noi(Z_size(z)) == succ(noi(Z_size(z0)));
    }
}

lemma_auto(Z_or(x_Z,y_Z))
void Z_or_commutes(Z x_Z, Z y_Z)
    requires true;
    ensures  Z_or(x_Z,y_Z) == Z_or(y_Z,x_Z);
{
    ALREADY_PROVEN()
    switch(y_Z) {
    case Zsign(sy):
        switch(x_Z) {
        case Zsign(sx):
        case Zdigit(x_z0,xb):
        }
    case Zdigit(y_z0,yb):
        switch(x_Z) {
        case Zsign(sx):
        case Zdigit(x_z0,xb):
            Z_or_commutes(x_z0,y_z0);
            note_eq( xb || yb , yb || xb);
        }
    }
}


lemma void Z_or_zero(Z x_Z, Z y_Z)
    requires int_of_Z(y_Z) == 0;
    ensures  int_of_Z(Z_or(x_Z,y_Z)) == int_of_Z(x_Z);
{
        ALREADY_PROVEN()
    switch(y_Z) {
    case Zsign(sy):
        switch(x_Z) {
        case Zsign(sx):
        case Zdigit(x_z0,xb):
        }
    case Zdigit(y_z0,yb):
        switch(x_Z) {
        case Zsign(sx):
        case Zdigit(x_z0,xb):
            division_zero_unique(2,int_of_Z(y_z0),((yb) ? 1 : 0));
            Z_or_zero(x_z0,y_z0);
        }
    }
}


lemma void bitor_no_overlap_inner(int x, Z x_Z, int y, Z y_Z, nat n)
    requires x >= 0 &*& y >= 0 &*& y < pow_nat(2,n)
        &*&  int_of_Z(x_Z) == x*pow_nat(2,n) &*& int_of_Z(y_Z) == y
        ;
    ensures  (x*pow_nat(2,n) | y) == x*pow_nat(2,n) + y;
{
        ALREADY_PROVEN()
    switch(n) {
    case zero:
        bitor_def(x*pow_nat(2,n), x_Z, y, y_Z);
        Z_or_zero(x_Z,y_Z);
    case succ(n0):
        bitor_def(x*pow_nat(2,n), x_Z, y, y_Z);
        mul_3var(2,x,pow_nat(2,n0));
        division_unique(x*pow_nat(2,n),2,x*pow_nat(2,n0),0);

        switch(y_Z) {
        case Zsign(s):
            Z_or_zero(x_Z,y_Z);
        case Zdigit(y_z0,yb):
            switch(x_Z) {
            case Zsign(s):
                if(!s) {
                    Z_or_zero(y_Z,x_Z);
                } else {
                    assert int_of_Z(x_Z) == x*pow_nat(2,n);
                    assert int_of_Z(x_Z) == -1;
                    division_unique(x*pow_nat(2,n),2,0,-1);
                    assert false;
                }
            case Zdigit(x_z0,xb):
                assert (x*pow_nat(2,n))%2 == 0;
                div_rem(y,2);

                assert (xb?1:0) >= 0;
                assert (xb?1:0) <= 1;

                if(int_of_Z(x_z0) < 0) {
                    assert x >= 0;
                    assert pow_nat(2,n) >= 0;
                    my_mul_mono_l(0,x,pow_nat(2,n));
                    assert false;
                }

                if(int_of_Z(y_z0) < 0) {
                    assert false;
                }

                mul_abs_commute(2,int_of_Z(x_z0));
                division_unique(x*pow_nat(2,n),2,int_of_Z(x_z0),
                        xb ? 1 : 0);
                assert xb == false;

                assert Z_or(x_Z,y_Z)
                    == Zdigit(Z_or(x_z0,y_z0),
                                (xb) || (yb));

                division_unique(y,2,int_of_Z(y_z0),yb?1:0);
                assert int_of_Z(y_z0) == y/2;

                bitor_no_overlap_inner(x, x_z0, (y/2),
                        y_z0, n0);
                bitor_def(x*pow_nat(2,n0), x_z0, y/2, y_z0);

                assert Z_or(x_Z,y_Z)
                    == Zdigit(Z_or(x_z0,y_z0), yb);
                assert int_of_Z(Z_or(x_Z,y_Z))
                    == y%2 + 2*(x*pow_nat(2,n0) + y/2);
                assert int_of_Z(Z_or(x_Z,y_Z))
                    == (y%2 + 2*(y/2)) + 2*(x*pow_nat(2,n0));
                assert int_of_Z(Z_or(x_Z,y_Z))
                    == y + x*pow_nat(2,n);
            }
        }
    }
}


lemma_auto(npow2_inner(x,n))
void npow2_prop_inner(int x, nat n)
    requires abs(x) <= ion(n);
    ensures  pow_nat(2,npow2_inner(x,n)) > abs(x);
{
        ALREADY_PROVEN()
    switch(n) {
    case zero:
    case succ(n0):
        if(x != 0) {
            div_rem(x,2);
            npow2_prop_inner(x/2,n0);
            assert abs(x/2) < pow_nat(2,npow2_inner(x,n));
            my_mul_mono_r(2,abs(x/2)+1,pow_nat(2,npow2_inner(x,n)));
        }
    }
}


lemma_auto(npow2(x))
void npow2_prop(int x)
    requires true;
    ensures  pow_nat(2,npow2(x)) > abs(x);
{ npow2_prop_inner(x,noi(abs(x))); }

lemma void npow2_minimal_inner(int x,nat n, nat m)
    requires pow_nat(2,n) > abs(x);
    ensures  ion(n) >= ion(npow2_inner(x,m));
{
    switch(m) {
    case zero:
    case succ(m0):
        switch(n) {
        case zero:
        case succ(n0):
            div_rem(x,2);
            my_inv_mul_strict_mono_r(2,abs(x/2),pow_nat(2,n0));
            npow2_minimal_inner(x/2,n0,m0);
        }
    }
}

lemma void npow2_minimal(int x,nat n)
    requires pow_nat(2,n) > abs(x);
    ensures  ion(n) >= ion(npow2(x));
{ npow2_minimal_inner(x,n,noi(abs(x))); }



lemma
void log_ceil_prop_inner(int x, nat n, nat sofar)
    requires abs(x)-pow_nat(2,sofar) <= ion(n);
    ensures  pow_nat(2,log_ceil_inner(x,n,sofar)) >= abs(x);
{
    switch(n) {
    case zero:
    case succ(n0):
        if(!(x >= -pow_nat(2,sofar) && x <= pow_nat(2,sofar))) {
            log_ceil_prop_inner(x,n0,succ(sofar));
        }
    }
}


lemma_auto(log_ceil(x))
void log_ceil_prop(int x)
    requires true;
    ensures  pow_nat(2,log_ceil(x)) >= abs(x);
{ log_ceil_prop_inner(x,noi(abs(x)),zero); }

lemma void log_ceil_minimal_inner(int x,nat n, nat m, nat sofar)
    requires pow_nat(2,n)*pow_nat(2,sofar) >= abs(x);
    ensures  ion(n) + ion(sofar)
        >= ion(log_ceil_inner(x,m,sofar));
{
    switch(m) {
    case zero:
    case succ(m0):
        switch(n) {
        case zero:
        case succ(n0):
            mul_3var(pow_nat(2,n0),2,pow_nat(2,sofar));
            log_ceil_minimal_inner(x,n0,m0,succ(sofar));
        }
    }
}

lemma void log_ceil_minimal(int x,nat n)
    requires pow_nat(2,n) >= abs(x);
    ensures  ion(n) >= ion(log_ceil(x));
{ log_ceil_minimal_inner(x,n,noi(abs(x)),zero); }

lemma_auto(x|y)
void bitor_commutes(int x, int y)
    requires x >= 0 && y >= 0;
    ensures  (x | y) == (y|x);
{
        ALREADY_PROVEN()
    Z x_Z = Z_of_uintN(x,npow2(x));
    Z y_Z = Z_of_uintN(y,npow2(y));
    bitor_def(x,x_Z,y,y_Z);
    bitor_def(y,y_Z,x,x_Z);
    Z_or_commutes(x_Z,y_Z);
}


lemma void bitor_no_overlap(int x, int y, nat n)
    requires x >= 0 &*& y >= 0 &*& y < pow_nat(2,n);
    ensures  (x*pow_nat(2,n) | y) == x*pow_nat(2,n) + y;
{
        ALREADY_PROVEN()
    nat lgY = npow2(y);
    my_mul_mono_l(0,x,pow_nat(2,n));
    Z x_Z = Z_of_uintN(x*pow_nat(2,n),npow2(x*pow_nat(2,n)));
    Z y_Z = Z_of_uintN(y,lgY);
    bitor_no_overlap_inner(x, x_Z, y, y_Z, n);
}


lemma void Z_and_zero(Z x_Z, Z y_Z)
    requires int_of_Z(y_Z) == 0;
    ensures  int_of_Z(Z_and(x_Z,y_Z)) == 0;
{
        ALREADY_PROVEN()
    switch(y_Z) {
    case Zsign(sy):
        switch(x_Z) {
        case Zsign(sx):
        case Zdigit(x_z0,xb):
        }
    case Zdigit(y_z0,yb):
        switch(x_Z) {
        case Zsign(sx):
        case Zdigit(x_z0,xb):
            division_zero_unique(2,int_of_Z(y_z0),((yb) ? 1 : 0));
            Z_and_zero(x_z0,y_z0);
        }
    }
}

lemma_auto(int_of_Z(Z_and(x_Z,y_Z)))
void Z_and_commutes(Z x_Z, Z y_Z)
    requires true;
    ensures  int_of_Z(Z_and(x_Z,y_Z)) == int_of_Z(Z_and(y_Z,x_Z));
{
    switch(y_Z) {
    case Zsign(sy):
        switch(x_Z) {
        case Zsign(sx):
        case Zdigit(x_z0,xb):
        }
    case Zdigit(y_z0,yb):
        switch(x_Z) {
        case Zsign(sx):
        case Zdigit(x_z0,xb):
            Z_and_commutes(x_z0,y_z0);
        }
    }
}

lemma void bitand_pow_2_inner(int x, Z x_Z, Z y_Z, nat n)
    requires x >= 0 &*& int_of_Z(x_Z) == x
        &*& int_of_Z(y_Z) == pow_nat(2,n)-1;
    ensures  (x & (pow_nat(2,n)-1)) == x%pow_nat(2,n);
{
        ALREADY_PROVEN()
    switch(n) {
    case zero:
        bitand_def(x,x_Z,pow_nat(2,n)-1,y_Z);
        Z_and_zero(x_Z,y_Z);
        division_unique(x,pow_nat(2,n),x,0);
    case succ(n0):
        bitand_def(x,x_Z,pow_nat(2,n)-1,y_Z);
        if(n0 != zero) {
            switch(y_Z) {
            case Zsign(sy):
                assert false;
            case Zdigit(y_z0,yb):
                division_unique(pow_nat(2,n)-1,2,pow_nat(2,n0)-1,1);
                division_unique(pow_nat(2,n)-1,2,int_of_Z(y_z0),yb?1:0);
                assert !!yb;
                switch(x_Z) {
                case Zsign(sx):
                    assert !sx;
                    assert int_of_Z(Z_and(x_Z,y_Z)) == 0;
                    assert (x&(pow_nat(2,n)-1)) == 0;
                    division_zero_unique(pow_nat(2,n),0,0);
                case Zdigit(x_z0,xb):
                    div_rem(x,2);
                    div_rem(x/2,pow_nat(2,n0));
                    assert x/2 >= 0;

                    if(int_of_Z(x_z0) < 0) {
                        assert false;
                    }

                    division_unique(x,2,int_of_Z(x_z0),xb?1:0);
                    bitand_pow_2_inner(x/2,x_z0,y_z0,n0);
                    bitand_def(x/2,x_z0,pow_nat(2,n0)-1,y_z0);

                    assert (x/2)%pow_nat(2,n0)
                        == int_of_Z(Z_and(x_z0,y_z0));
                    my_mul_mono_r(2,int_of_Z(Z_and(x_z0,y_z0)),pow_nat(2,n0)-1);

                    assert pow_nat(2,n)*((x/2)/pow_nat(2,n0))
                        == (2*pow_nat(2,n0))*((x/2)/pow_nat(2,n0));
                    mul_assoc(2,pow_nat(2,n0),(x/2)/pow_nat(2,n0));
                    my_mul_mono_r(2,pow_nat(2,n0)*((x/2)/pow_nat(2,n0)),x/2);
                    assert pow_nat(2,n)*((x/2)/pow_nat(2,n0)) <= x;

                    division_unique(x,pow_nat(2,n),(x/2)/pow_nat(2,n0),
                        2*int_of_Z(Z_and(x_z0,y_z0)) + (xb?1:0));
                }
            }
        } else {
            assert int_of_Z(y_Z) == 1;
            division_unique(1,2,0,1);
            switch(y_Z) {
            case Zsign(ys):
            case Zdigit(y_z0,yb):
                division_unique(1,2,int_of_Z(y_z0),yb?1:0);
                switch(x_Z) {
                case Zsign(sx):
                    assert !sx;
                    division_unique(x,2,0,0);
                case Zdigit(x_z0,xb):
                    Z_and_zero(x_z0,y_z0);
                    div_rem(x,2);

                    if(int_of_Z(x_z0) < 0) {
                        assert false;
                    }

                    division_unique(x,2,int_of_Z(x_z0),xb?1:0);
                }
            }
        }
    }
}


lemma void bitand_pow_2(int x, nat n)
    requires x >= 0;
    ensures  (x & (pow_nat(2,n)-1)) == x%pow_nat(2,n);
{ bitand_pow_2_inner(x,Z_of_uintN(x,npow2(x)),
                     Z_of_uintN(pow_nat(2,n)-1,n),n); }

lemma void bitand_flag_inner(int x, Z x_Z, Z y_Z, nat n)
    requires x >= 0 &*& x == int_of_Z(x_Z)
        &*&  int_of_Z(y_Z) == pow_nat(2,n);
    ensures  (x & (pow_nat(2,n)))
        ==   x%pow_nat(2,succ(n)) - x%(pow_nat(2,n));
{
    ALREADY_PROVEN()
    switch(n) {
    case zero:
        switch(y_Z) {
        case Zsign(sy): assert false;
        case Zdigit(y_z0,yb):
            division_unique(1,2,0,1);
            division_unique(1,2,int_of_Z(y_z0),yb?1:0);
            assert !!yb;
            switch(x_Z) {
            case Zsign(sx):
                division_zero_unique(pow_nat(2,succ(n)),0,0);
                division_zero_unique(pow_nat(2,n),0,0);
                Z_and_zero(y_Z,x_Z);
                bitand_def(x,x_Z,pow_nat(2,n),y_Z);
                assert (x&pow_nat(2,n)) == 0;
                assert x%pow_nat(2,n) == 0;
                assert x%pow_nat(2,succ(n)) == 0;
            case Zdigit(x_z0,xb):
                bitand_def(x,x_Z,pow_nat(2,n),y_Z);
                bitand_def(int_of_Z(x_z0),x_z0,0,y_z0);
                Z_and_zero(x_z0,y_z0);
                int xv = (xb ? 1 : 0);
                assert (x&pow_nat(2,n)) == xv;
                assert x == 2*int_of_Z(x_z0) + xv;
                assert pow_nat(2,succ(n)) == 2;
                assert x >= 2*int_of_Z(x_z0);
                assert abs(x) >= 0;
                if(2*int_of_Z(x_z0) < 0) {
                    my_inv_mul_strict_mono_r(2,int_of_Z(x_z0), 0);
                    assert false;
                }
                division_unique(x,pow_nat(2,succ(n)),
                        int_of_Z(x_z0), xv);
                division_unique(x,pow_nat(2,n),
                        x, 0);
            }
        }
    case succ(n0):
        bitand_def(x,x_Z,pow_nat(2,n),y_Z);
        switch(y_Z) {
        case Zsign(sy):
        case Zdigit(y_z0,yb):
            division_unique(pow_nat(2,n),2,pow_nat(2,n0),0);
            division_unique(pow_nat(2,n),2,int_of_Z(y_z0),yb?1:0);
            assert !yb;
            switch(x_Z) {
            case Zsign(sx):
                assert !sx;
                assert int_of_Z(Z_and(x_Z,y_Z)) == 0;
                division_zero_unique(pow_nat(2,succ(n)),0,0);
                division_zero_unique(pow_nat(2,n),0,0);
            case Zdigit(x_z0,xb):
                div_rem(x,2);
                div_rem(x/2,pow_nat(2,n0));
                assert x/2 >= 0;

                if(int_of_Z(x_z0) < 0) { assert false; }

                division_unique(x,2,int_of_Z(x_z0),xb?1:0);
                bitand_flag_inner(x/2,x_z0,y_z0,n0);
                bitand_def(x/2,x_z0,pow_nat(2,n0),y_z0);
                assert (x/2 & pow_nat(2,n0))
                    == (x/2)%pow_nat(2,n) - (x/2)%pow_nat(2,n0);
                assert (x & pow_nat(2,n))
                    == 2*((x/2)%pow_nat(2,n) -
                            (x/2)%pow_nat(2,n0));
                div_rem(x/2,pow_nat(2,n));

                my_mul_mono_r(2,(x/2)%pow_nat(2,n),
                        pow_nat(2,n));
                my_mul_mono_r(2,(x/2)%pow_nat(2,n0),pow_nat(2,n0));

                my_mul_mono_r(2,pow_nat(2,n)*((x/2)/pow_nat(2,n)),
                        x/2);
                mul_3var(2,pow_nat(2,n),((x/2)/pow_nat(2,n)));
                my_mul_mono_r(2,pow_nat(2,n0)*((x/2)/pow_nat(2,n0)),
                        x/2);
                mul_3var(2,pow_nat(2,n0),((x/2)/pow_nat(2,n0)));

                division_unique(x,pow_nat(2,succ(n)),
                    (x/2)/pow_nat(2,n),
                    2*((x/2)%pow_nat(2,n)) + (xb?1:0));
                division_unique(x,pow_nat(2,n),
                    (x/2)/pow_nat(2,n0),
                    2*((x/2)%pow_nat(2,n0)) + (xb?1:0));
            }
        }
    }
}

lemma void bitand_flag(int x, nat n)
    requires x >= 0;
    ensures  (x & (pow_nat(2,n))) + x%pow_nat(2,n)
        ==   x%pow_nat(2,succ(n));
{
    nat lgX = npow2(x);
    my_mul_mono_l(0,x,pow_nat(2,n));
    Z x_Z = Z_of_uintN(x,succ(lgX));
    Z y_Z = Z_of_uintN(pow_nat(2,n),succ(n));
    bitand_flag_inner(x,x_Z,y_Z,n);
}

lemma void bitand_cases_inner(int x, Z x_Z, Z y_Z, nat n)
    requires x >= 0 &*& x == int_of_Z(x_Z)
        &*&  int_of_Z(y_Z) == pow_nat(2,n);
    ensures  (x & (pow_nat(2,n))) == 0
        ||   (x & (pow_nat(2,n))) == pow_nat(2,n);
{
    switch(n) {
    case zero:
        switch(y_Z) {
        case Zsign(sy): assert false;
        case Zdigit(y_z0,yb):
            division_unique(1,2,0,1);
            division_unique(1,2,int_of_Z(y_z0),yb?1:0);
            assert !!yb;
            switch(x_Z) {
            case Zsign(sx):
                bitand_def(x,x_Z,pow_nat(2,n),y_Z);
            case Zdigit(x_z0,xb):
                bitand_def(x,x_Z,pow_nat(2,n),y_Z);
                Z_and_zero(x_z0,y_z0);
            }
        }
    case succ(n0):
        bitand_def(x,x_Z,pow_nat(2,n),y_Z);
        switch(y_Z) {
        case Zsign(sy):
        case Zdigit(y_z0,yb):
            division_unique(pow_nat(2,n),2,pow_nat(2,n0),0);
            division_unique(pow_nat(2,n),2,int_of_Z(y_z0),yb?1:0);
            assert !yb;
            switch(x_Z) {
            case Zsign(sx):
            case Zdigit(x_z0,xb):
                bitand_cases_inner(int_of_Z(x_z0),x_z0,y_z0,n0);
                bitand_def(int_of_Z(x_z0),x_z0,pow_nat(2,n0),y_z0);
            }
        }
    }
}

lemma void bitand_cases(int x, nat n)
    requires x >= 0;
    ensures  (x & (pow_nat(2,n))) == 0
        ||   (x & (pow_nat(2,n))) == pow_nat(2,n);
{
    nat lgX = npow2(x);
    my_mul_mono_l(0,x,pow_nat(2,n));
    Z x_Z = Z_of_uintN(x,succ(lgX));
    Z y_Z = Z_of_uintN(pow_nat(2,n),succ(n));
    bitand_cases_inner(x,x_Z,y_Z,n);
}


lemma void shiftright_div_inner(Z x_Z, nat n)
    requires int_of_Z(x_Z) >= 0;
    ensures  int_of_Z(Z_shiftright(x_Z,n))
        ==   int_of_Z(x_Z)/pow_nat(2,n);
{
        ALREADY_PROVEN()
    switch(n) {
    case zero:
        division_unique(int_of_Z(x_Z),1,int_of_Z(x_Z),0);
    case succ(n0):
        switch(x_Z) {
        case Zsign(b):
            division_unique(0,pow_nat(2,n),0,0);
        case Zdigit(x_z0,xb):
            shiftright_div_inner(x_z0,n0);

            if(int_of_Z(x_z0) < 0) {
                assert false;
            }

            int x = int_of_Z(x_Z);
            div_rem(x,2);
            div_rem(x/2,pow_nat(2,n0));
            division_unique(x,2,int_of_Z(x_z0),xb?1:0);
            mul_assoc(2,pow_nat(2,n0),(x/2)/pow_nat(2,n0));
            my_mul_mono_r(2,pow_nat(2,n0)*((x/2)/pow_nat(2,n0)),x/2);
            div_rem(int_of_Z(x_z0),pow_nat(2,n0));

            division_unique(x,pow_nat(2,n),
                    (int_of_Z(x_z0))/pow_nat(2,n0),
                    2*(int_of_Z(x_z0)%pow_nat(2,n0)) + (xb?1:0));
        }
    }
}


lemma void shiftright_div(int x, nat n)
    requires x >= 0;
    ensures  x>>ion(n) == x/pow_nat(2,n);
{
        ALREADY_PROVEN()
    Z x_Z = Z_of_uintN(x,npow2(x));
    shiftright_def(x,x_Z,n);
    shiftright_div_inner(x_Z,n);
}

lemma void ashr_euclid(int x,nat n)
    requires true;
    ensures  [_]euclid_div_sol(x,pow_nat(2,n),ASHR(x,ion(n)),_);
{
        ALREADY_PROVEN()
    if(x >= 0) {
        shiftright_div(x,n);
        div_rem(x,pow_nat(2,n));
        euclid_div_unique_intro(x,pow_nat(2,n),x>>ion(n),x%pow_nat(2,n));
    } else {
        shiftright_div(-(x+1),n);
        div_rem(-(x+1),pow_nat(2,n));

        euclid_div_unique_intro(x,pow_nat(2,n),
                -((-(x+1))>>ion(n))-1,
                -((-(x+1))%pow_nat(2,n)) + pow_nat(2,n) - 1);
    }
}


@*/

