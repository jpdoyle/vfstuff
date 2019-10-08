#ifndef VFUTIL_NUMTHEO_H
#define VFUTIL_NUMTHEO_H

/*@ #include "numtheo.gh" @*/
#include <stddef.h>

size_t prime_sieve(int* buff, size_t n);
    /*@ requires buff[..n] |-> _ &*& n > 0 &*& n+n <= UINTPTR_MAX; @*/
    /*@ ensures  int_buffer(buff, result, n,
                    reverse(primes_below(nat_of_int(n))));
      @*/
    /*@ terminates; @*/

#endif

