#ifndef VFSTUFF_BITOPS_H
#define VFSTUFF_BITOPS_H

/*@ #include "bitops.gh" @*/

#define ASHR(x,n) ((x) < 0 ? -((-(x+1))>>(n))-1 : (x)>>(n))

/*@

lemma void ashr_euclid(int x,nat n);
    requires true;
    ensures  euclid_div_sol(x,pow_nat(2,n),ASHR(x,int_of_nat(n)),_);

  @*/

#endif

