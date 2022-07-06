#ifndef LORG2_COMMON_H
#define LORG2_COMMON_H

#include <stdint.h>
/*@ #include <arrays.gh> @*/
/*@ #include "../div.gh" @*/

static int32_t max32(int32_t x, int32_t y)
    /*@ requires true; @*/
    /*@ ensures  result == max_of(x,y); @*/
    /*@ terminates; @*/
{
    return x > y ? x : y;
}

static int32_t min32(int32_t x, int32_t y)
    /*@ requires true; @*/
    /*@ ensures  result == min_of(x,y); @*/
    /*@ terminates; @*/
{
    return x < y ? x : y;
}

static void euclid_divide(int32_t D, int32_t d, int32_t* q, int32_t* r)
    /*@ requires d > 0 &*& *q |-> _ &*& *r |-> _; @*/
    /*@ ensures  [_]euclid_div_sol(D,d,euclid_div(D,d),euclid_mod(D,d))
            &*&  *q |-> euclid_div(D,d) &*& *r |-> euclid_mod(D,d); @*/
    /*@ terminates; @*/
{
    /*@ {
        div_rem(D,d);
        euclid_div_intro(D,d);
        euclid_div_equiv(D,d);
        div_shrinks(D,d);
    } @*/

    int32_t div = D/d;
    int32_t rem = D%d;
    if(rem < 0) {
        rem += d;
        div -= 1;
    }
    *q = div;
    *r = rem;
}

static void euclid_divide_64_32(int64_t D, int32_t d, int64_t* q, int32_t* r)
    /*@ requires d > 0 &*& *q |-> _ &*& *r |-> _; @*/
    /*@ ensures  [_]euclid_div_sol(D,d,euclid_div(D,d),euclid_mod(D,d))
            &*&  *q |-> euclid_div(D,d) &*& *r |-> euclid_mod(D,d); @*/
    /*@ terminates; @*/
{
    /*@ {
        div_rem(D,d);
        euclid_div_intro(D,d);
        euclid_div_equiv(D,d);
        div_shrinks(D,d);
    } @*/

    int64_t div = D/d;
    int32_t rem = (int32_t)(D%d);
    if(rem < 0) {
        rem += d;
        div -= 1;
    }
    *q = div;
    *r = rem;
}

#endif

