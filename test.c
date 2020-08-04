/*@ #include "bitops.gh" @*/
/*@ #include "util.gh" @*/

/* @

lemma void division_unique(int D, int d, int q, int r);
    requires d != 0 &*& abs(r) < abs(d) &*& abs(d*q) <= abs(D)
        &*&  D == d*q + r;
    ensures  q == (D/d) &*& r == (D%d);

  @*/

void foo()
    /*@ requires true; @*/
    /*@ ensures true; @*/
    /*@ terminates; @*/
{
    unsigned x = /*@ truncating @*/ -(unsigned)1;
    /*@ truncate_unsigned_def(-1,N32); @*/
    /*@ open euclid_div_sol(-1,pow_nat(2,N32),?q,x); @*/
    /*@ euclid_div_unique(-1,pow_nat(2,N32),q,x,-1,pow_nat(2,N32)-1); @*/
    /*@ assert x == pow_nat(2,N32) - 1; @*/
}

/* :@

  inductive opt<t> = non | som(t);
  inductive par<s,t> = par(s,t);
  inductive optlst<t> = lst(opt<par<t,optlst<t> > >);

  @*/

#if 0
int foo()
    /*@ requires true; @*/
    /*@ ensures  result == 3*42; @*/
    /*@ terminates; @*/
{
    int x = 0;
    int i,j,k;

    for(i = 0; i < 6; ++i)
        /*@ requires i >= 0 &*& i <= 6 &*& x + 3*7*(6-i) < 100000; @*/
        /*@ ensures  old_x + (6-old_i)*7*3 == x; @*/
        /*@ decreases 6-i; @*/
    {
        for(j = 0; j < 7; ++j)
            /*@ requires j >= 0 &*& j <= 7 &*& x + 3*(7-j) < 100000; @*/
            /*@ ensures  old_x + (7-old_j)*3 == x; @*/
            /*@ decreases 7-j; @*/
        {
#if 1
            x += 3;
#else
            for(k = 0; k < 3; ++k)
                /*@ requires k >= 0 &*& k <= 3 &*& x + (3-k) < 100000; @*/
                /*@ ensures  old_x + (3-old_k) == x; @*/
                /*@ decreases 3-k; @*/
            {
                ++x;
                /*@ recursive_call(); @*/
            }
#endif
            /*@ recursive_call(); @*/
            /*@ {
                assert old_x + 3 + (7-(old_j+1))*3 == x; 
                assert old_x + (7-old_j)*3 == x; 
            } @*/
        }
        /*@ recursive_call(); @*/
    }
    return x;
}
#endif


