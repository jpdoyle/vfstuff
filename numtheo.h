#ifndef VFUTIL_NUMTHEO_H
#define VFUTIL_NUMTHEO_H

/*@ #include "numtheo.gh" @*/
#include <stddef.h>
#include <stdint.h>

size_t prime_sieve(size_t* buff, size_t n);
    /*@ requires buff[..n] |-> _ &*& n > 0 &*& n+n <= SIZE_MAX; @*/
    /*@ ensures  u_llong_buffer(buff, result, n,
                    reverse(primes_below(noi(n-1))));
      @*/
    /*@ terminates; @*/

size_t euclid_gcd(size_t a,size_t b);
    /*@ requires a > 0 &*& b > 0; @*/
    /*@ ensures  result == gcd(a,b); @*/
    /*@ terminates; @*/

size_t abs_diff(size_t x, size_t y);
    /*@ requires true; @*/
    /*@ ensures  result == abs(x-y); @*/
    /*@ terminates; @*/

size_t int_sqrt(size_t n);
    /*@ requires n >= 0; @*/
    /*@ ensures  result >= 0 &*& result*result <= n
            &*&  (result+1)*(result+1) > n; @*/
    /*@ terminates; @*/

#endif

