#ifndef VFSTUFF_BITOPS_H
#define VFSTUFF_BITOPS_H

/*@ #include "bitops.gh" @*/

#define ASHR(x,n) ((x) < 0 ? -((-(x+1))>>(n))-1 : (x)>>(n))

/*@

lemma void ashr_euclid(int x,nat n);
    requires true;
    ensures  [_]euclid_div_sol(x,pow_nat(2,n),ASHR(x,ion(n)),_);

  @*/

#endif

