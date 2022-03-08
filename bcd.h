#include <stdint.h>
/*@ #include "poly.gh" @*/

/*@

predicate dec_num(list<int> le_digits; int value)
    =   !!forall(le_digits, (bounded)(0,9))
    &*& value == poly_eval(le_digits,10);

lemma void dec_9876543210();
    requires true;
    ensures  dec_num({0,1,2,3,4,5,6,7,8,9}, 9876543210);

lemma
void digit_rep_zero_unique(int b, list<int> le);
    requires b > 0
        &*&  !!forall(le,(bounded)(0,b-1))
        &*&  poly_eval(le,b) == 0
        ;
    ensures  minimize(le) == nil;

lemma
void digit_rep_unique(int b, list<int> le1, list<int> le2);
    requires b > 0
        &*&  !!forall(le1,(bounded)(0,b-1))
        &*&  !!forall(le2,(bounded)(0,b-1))
        &*&  !!minimal(le1) &*& !!minimal(le2)
        &*&  poly_eval(le1,b) == poly_eval(le2,b)
        ;
    ensures  le1 == le2;

lemma void dec_unique(list<int> le1, list<int> le2, int v);
    requires [?f1]dec_num(le1,v) &*& [?f2]dec_num(le2,v);
    ensures  [ f1]dec_num(le1,v) &*& [ f2]dec_num(le2,v)
        &*&  minimize(le1) == minimize(le2);

predicate bcd_int(int bcd_value, nat n; list<int> le_digits, int value)
    =   switch(n) {
    case zero:
        return bcd_value == 0 &*& le_digits == nil &*& value == 0;
    case succ(n0):
        return  bcd_value >= 0
            &*& bcd_int(bcd_value/16,n0,?le_rest,?v_rest)
            &*& let(bcd_value%16,?le_digit)
            &*& 0 <= le_digit &*& le_digit < 10
            &*& le_digits == cons(le_digit,le_rest)
            &*& value == le_digit + 10*v_rest;
    };

lemma void bcd_exact(list<int> le_digits, int value, int bcd_value);
    requires !!forall(le_digits,(bounded)(0,9))
        &*&  poly_eval(le_digits,10) == value
        &*&  poly_eval(le_digits,16) == bcd_value;
    ensures  bcd_int(bcd_value,noi(length(le_digits)),le_digits,value);

lemma_auto void bcd_inv();
    requires [?f]bcd_int(?bcd,?n,?le,?v);
    ensures  [ f]bcd_int(bcd, n, le, v)
        &*&  v >= 0 &*& bcd >= 0 &*& (v == 0) == (bcd == 0)
        &*&  bcd < pow_nat(16, noi(length(le)))
        &*&  v < pow_nat(10, noi(length(le)))
        &*&  !!forall(le,(bounded)(0,9))
        &*&  bcd == poly_eval(le,16)
        &*&  v   == poly_eval(le,10)
        ;

lemma void bcd_join(int bcd1, nat n, int bcd2);
    requires [?f]bcd_int(bcd1, n,?le1,?v1)
        &*&  [ f]bcd_int(bcd2,?m,?le2,?v2);
    ensures  [f]bcd_int(
        bcd1 + pow_nat(16,n)*bcd2, nat_plus(n,m),
        append(le1,le2), v1 + pow_nat(10,n)*v2);

  @*/

uint32_t bcd_add_u32(uint32_t x,uint32_t y);
    /*@ requires [?f1]bcd_int(x,?xn,?x_le,?xv)
            &*&  [?f2]bcd_int(y,?yn,?y_le,?yv)
            &*&  xv+yv < pow_nat(10,N8)
            ; @*/
    /*@ ensures  bcd_int(result,?rn,_,xv+yv)
            &*&  ion(rn) <= 8; @*/
    /*@ terminates; @*/

