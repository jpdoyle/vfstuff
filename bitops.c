/*@ #include "bitops.gh" @*/
#include "bitops.h"

/*@

lemma_auto(Z_size(z))
void Z_size_nonneg(Z z)
    requires true;
    ensures  Z_size(z) >= 0;
{
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
    switch(z) {
    case Zsign(b):
    case Zdigit(z0,b0): Z_neg_auto(z0);
    }
}

lemma_auto(Z_size(z))
void Z_size_bound_pos(Z z)
    requires !Z_is_neg(z);
    ensures  int_of_Z(z) < pow_nat(2,nat_of_int(Z_size(z)));
{
    switch(z) {
    case Zsign(b):
    case Zdigit(z0,b0):
        Z_size_bound_pos(z0);
        assert nat_of_int(Z_size(z)) == succ(nat_of_int(Z_size(z0)));
    }
}

lemma_auto(Z_size(z))
void Z_size_bound_neg(Z z)
    requires !!Z_is_neg(z);
    ensures  -int_of_Z(z) <= pow_nat(2,nat_of_int(Z_size(z)));
{
    switch(z) {
    case Zsign(b):
    case Zdigit(z0,b0):
        Z_size_bound_neg(z0);
        assert nat_of_int(Z_size(z)) == succ(nat_of_int(Z_size(z0)));
    }
}

lemma_auto(Z_or(x_Z,y_Z))
void Z_or_commutes(Z x_Z, Z y_Z)
    requires true;
    ensures  Z_or(x_Z,y_Z) == Z_or(y_Z,x_Z);
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
            Z_or_commutes(x_z0,y_z0);
            note_eq( xb || yb , yb || xb);
        }
    }
}


lemma void Z_or_zero(Z x_Z, Z y_Z)
    requires int_of_Z(y_Z) == 0;
    ensures  int_of_Z(Z_or(x_Z,y_Z)) == int_of_Z(x_Z);
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
                    assert x*pow_nat(2,n) >= 0;
                    my_mul_mono_r(2,int_of_Z(x_z0),1);
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


lemma_auto(log_nat_inner(x,n))
void log_nat_prop_inner(int x, nat n)
    requires abs(x) <= int_of_nat(n);
    ensures  pow_nat(2,log_nat_inner(x,n)) > abs(x);
{
    switch(n) {
    case zero:
    case succ(n0):
        if(x != 0) {
            div_rem(x,2);
            log_nat_prop_inner(x/2,n0);
            assert abs(x/2) < pow_nat(2,log_nat_inner(x,n));
            my_mul_mono_r(2,abs(x/2)+1,pow_nat(2,log_nat_inner(x,n)));
        }
    }
}


lemma_auto(log_nat(x))
void log_nat_prop(int x)
    requires true;
    ensures  pow_nat(2,log_nat(x)) > abs(x);
{ log_nat_prop_inner(x,nat_of_int(abs(x))); }


lemma_auto(x|y)
void bitor_commutes(int x, int y)
    requires x >= 0 && y >= 0;
    ensures  (x | y) == (y|x);
{
    Z x_Z = Z_of_uintN(x,log_nat(x));
    Z y_Z = Z_of_uintN(y,log_nat(y));
    bitor_def(x,x_Z,y,y_Z);
    bitor_def(y,y_Z,x,x_Z);
    Z_or_commutes(x_Z,y_Z);
}


lemma void bitor_no_overlap(int x, int y, nat n)
    requires x >= 0 &*& y >= 0 &*& y < pow_nat(2,n);
    ensures  (x*pow_nat(2,n) | y) == x*pow_nat(2,n) + y;
{
    nat lgY = log_nat(y);
    my_mul_mono_l(0,x,pow_nat(2,n));
    Z x_Z = Z_of_uintN(x*pow_nat(2,n),log_nat(x*pow_nat(2,n)));
    Z y_Z = Z_of_uintN(y,lgY);
    bitor_no_overlap_inner(x, x_Z, y, y_Z, n);
}


lemma void Z_and_zero(Z x_Z, Z y_Z)
    requires int_of_Z(y_Z) == 0;
    ensures  int_of_Z(Z_and(x_Z,y_Z)) == 0;
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
            division_zero_unique(2,int_of_Z(y_z0),((yb) ? 1 : 0));
            Z_and_zero(x_z0,y_z0);
        }
    }
}


lemma void bitand_pow_2_inner(int x, Z x_Z, Z y_Z, nat n)
    requires x >= 0 &*& int_of_Z(x_Z) == x
        &*& int_of_Z(y_Z) == pow_nat(2,n)-1
        &*& n != zero;
    ensures  (x & (pow_nat(2,n)-1)) == x%pow_nat(2,n);
{
    switch(n) {
    case zero:
    case succ(n0):
        bitand_def(x,x_Z,pow_nat(2,n)-1,y_Z);
        if(n0 != zero) {
            switch(y_Z) {
            case Zsign(sy):
                switch(x_Z) {
                case Zsign(sx): assert !sx;
                case Zdigit(x_z0,xb):
                }
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
    requires x >= 0 &*& n != zero;
    ensures  (x & (pow_nat(2,n)-1)) == x%pow_nat(2,n);
{ bitand_pow_2_inner(x,Z_of_uintN(x,log_nat(x)),
                     Z_of_uintN(pow_nat(2,n)-1,n),n); }


lemma void shiftright_div_inner(Z x_Z, nat n)
    requires int_of_Z(x_Z) >= 0;
    ensures  int_of_Z(Z_shiftright(x_Z,n))
        ==   int_of_Z(x_Z)/pow_nat(2,n);
{
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
    ensures  x>>int_of_nat(n) == x/pow_nat(2,n);
{
    Z x_Z = Z_of_uintN(x,log_nat(x));
    shiftright_def(x,x_Z,n);
    shiftright_div_inner(x_Z,n);
}

lemma void ashr_euclid(int x,nat n)
    requires true;
    ensures  euclid_div_sol(x,pow_nat(2,n),ASHR(x,int_of_nat(n)),_);
{
    if(x >= 0) {
        shiftright_div(x,n);
        div_rem(x,pow_nat(2,n));
        euclid_div_unique_intro(x,pow_nat(2,n),x>>int_of_nat(n),x%pow_nat(2,n));
    } else {
        shiftright_div(-(x+1),n);
        div_rem(-(x+1),pow_nat(2,n));

        euclid_div_unique_intro(x,pow_nat(2,n),
                -((-(x+1))>>int_of_nat(n))-1,
                -((-(x+1))%pow_nat(2,n)) + pow_nat(2,n) - 1);
    }
}


@*/

