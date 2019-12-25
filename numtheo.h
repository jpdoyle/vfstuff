#ifndef VFUTIL_NUMTHEO_H
#define VFUTIL_NUMTHEO_H

/*@ #include "numtheo.gh" @*/
#include <stddef.h>

int prime_sieve(int* buff, int n);
    /*@ requires buff[..n] |-> _ &*& n > 0 &*& n+n <= INT_MAX; @*/
    /*@ ensures  int_buffer(buff, result, n,
                    reverse(primes_below(nat_of_int(n-1))));
      @*/
    /*@ terminates; @*/

size_t euclid_gcd(size_t a,size_t b);
    /*@ requires a > 0 &*& b > 0; @*/
    /*@ ensures  result == gcd(a,b); @*/
    /*@ terminates; @*/

#endif

