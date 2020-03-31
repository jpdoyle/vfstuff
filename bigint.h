#ifndef VFSTUFF_BIGINT_H
#define VFSTUFF_BIGINT_H

#include <stdint.h>

struct big_int;
typedef struct big_int big_int;

/*@

predicate bigint(big_int* b; int val);


lemma void bigint_inv();
    requires [?f]bigint(?b,?val);
    ensures  [ f]bigint( b, val)
        &*&  b > 0;

  @*/


/* NOTE: this implementation aborts if allocation fails
 *
 */

big_int* new_big_int(int64_t value);
    /*@ requires emp; @*/
    /*@ ensures  bigint(result, value); @*/
    /*@ terminates; @*/

void free_big_int(big_int* b);
    /*@ requires bigint(b,_); @*/
    /*@ ensures  emp; @*/
    /*@ terminates; @*/

void bigint_set(big_int* dst, big_int* src);
    /*@ requires bigint(dst,_)   &*& [?f]bigint(src,?val); @*/
    /*@ ensures  bigint(dst,val) &*& [ f]bigint(src, val); @*/
    /*@ terminates; @*/

void bigint_set64(big_int* dst, int64_t x);
    /*@ requires bigint(dst,_); @*/
    /*@ ensures  bigint(dst,x); @*/
    /*@ terminates; @*/

big_int* bigint_clone(big_int* x);
    /*@ requires [?f]bigint(x,?val); @*/
    /*@ ensures  [ f]bigint(x, val) &*& bigint(result,val); @*/
    /*@ terminates; @*/

void bigint_add(big_int* a, big_int* b);
    /*@ requires bigint(a,?va)   &*& [?f]bigint(b,?vb); @*/
    /*@ ensures  bigint(a,va+vb) &*& [ f]bigint(b, vb); @*/
    /*@ terminates; @*/

void bigint_mul(big_int* a, big_int* b);
    /*@ requires bigint(a,?va)   &*& [?f]bigint(b,?vb); @*/
    /*@ ensures  bigint(a,va*vb) &*& [ f]bigint(b, vb); @*/
    /*@ terminates; @*/

void bigint_negate(big_int* x);
    /*@ requires bigint(x,?v); @*/
    /*@ ensures  bigint(x,-v); @*/
    /*@ terminates; @*/

void bigint_subtract(big_int* a, big_int* b);
    /*@ requires bigint(a,?va)   &*& [?f]bigint(b,?vb); @*/
    /*@ ensures  bigint(a,va-vb) &*& [ f]bigint(b, vb); @*/
    /*@ terminates; @*/

big_int* bigint_plus(big_int* a, big_int* b);
    /*@ requires [?fa]bigint(a,?va) &*& [?fb]bigint(b,?vb); @*/
    /*@ ensures  [ fa]bigint(a, va) &*& [ fb]bigint(b, vb)
            &*&  bigint(result,va+vb); @*/
    /*@ terminates; @*/

big_int* bigint_times(big_int* a, big_int* b);
    /*@ requires [?fa]bigint(a,?va) &*& [?fb]bigint(b,?vb); @*/
    /*@ ensures  [ fa]bigint(a, va) &*& [ fb]bigint(b, vb)
            &*&  bigint(result,va*vb); @*/
    /*@ terminates; @*/

big_int* bigint_negative(big_int* x);
    /*@ requires [?f]bigint(x,?v); @*/
    /*@ ensures  [ f]bigint(x, v) &*& bigint(result,-v); @*/
    /*@ terminates; @*/

big_int* bigint_minus(big_int* a, big_int* b);
    /*@ requires [?fa]bigint(a,?va) &*& [?fb]bigint(b,?vb); @*/
    /*@ ensures  [ fa]bigint(a, va) &*& [ fb]bigint(b, vb)
            &*&  bigint(result,va-vb); @*/
    /*@ terminates; @*/

void bigint_euclid_div(big_int* q, big_int* r, big_int* a, big_int* b);
    /*@ requires bigint(q,_) &*& bigint(r,_)
             &*& [?fa]bigint(a,?va) &*& [?fb]bigint(b,?vb); @*/
    /*@ ensures  bigint(q,?qv) &*& bigint(r,?rv)
             &*& [ fa]bigint(a, va) &*& [ fb]bigint(b, vb)
             &*& va == qv*vb + rv &*& 0 <= rv &*& rv < vb
             ; @*/
    /*@ terminates; @*/

#endif

