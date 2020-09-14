#include <string.h>
#include <stdio.h>
#include <limits.h>
#include "../bi_big_int.h"
/*@ #include "../util.gh" @*/
/*@ #include "../poly.gh" @*/

/*@

fixpoint int fib(nat n) {
    switch(n) {
    case zero: return 0;
    case succ(n0):
        return switch(n0) {
        case zero: return 1;
        case succ(n1): return fib(n0) + fib(n1);
        };
    }
}

lemma_auto(fib(n))
void fib_nonneg(nat n)
    requires true;
    ensures  fib(n) >= 0;
{
    switch(n) {
    case zero:
    case succ(n0):
        switch(n0) {
        case zero:
        case succ(n1):
            fib_nonneg(n0);
            fib_nonneg(n1);
        }
    }
}

  @*/

#ifndef __FILE__
int test_main(void)
#else
int main(void)
#endif
    /*@ requires true; @*/
    /*@ ensures  result == 0; @*/
{
    int n;
    big_int* f_n = new_big_int_from(0);
    big_int* f_n_1 = new_big_int_from(1);
    /*@ if(f_n == f_n_1) {
      bi_big_int_unique(f_n,f_n_1);
      assert false;
    } @*/

    do
        /*@ requires n |-> _; @*/
        /*@ ensures  n |-> ?n_v &*& n_v >= 0; @*/
    {
        int n_read;
        printf("n? "); fflush(stdout);
        n_read = scanf("%d",&n);
        if(n_read < 1) n = -1;
        getchar(); // \n
    } while(n < 0);

    /*@ int orig_n = n; @*/

    for(int i=0; i<n; ++i)
        /*@ invariant bi_big_int(f_n,?carry_n,_,
                        fib(nat_of_int(i)))
                &*&   bi_big_int(f_n_1,?carry_n_1,_,
                        fib(nat_of_int(i+1)))
                //&*&   carry_n == CARRY_BITS
                //&*&   carry_n_1 == CARRY_BITS
                &*&   carry_n >= CARRY_BITS - (i%(CARRY_BITS-1))
                &*&   carry_n >= 1
                &*&   carry_n_1 >= CARRY_BITS - (i%(CARRY_BITS-1))
                &*&   f_n != f_n_1
                &*&   n |-> orig_n &*& i >= 0 &*& i <= orig_n
                ; @*/
        /*@ decreases n-i; @*/
    {
        /*@ div_rem(i,CARRY_BITS-1); @*/
        /*@ div_rem(i+1,CARRY_BITS-1); @*/
        big_int* tmp = f_n_1;
        big_int_pluseq(f_n,f_n_1);
        /* big_int_reduce(f_n); */
        f_n_1 = f_n;
        f_n = tmp;
        if(i%(CARRY_BITS-1) == CARRY_BITS-2) {
            big_int_reduce(f_n);
            big_int_reduce(f_n_1);
        } else {
            /*@ {
                division_unique(i+1,CARRY_BITS-1,
                    i/(CARRY_BITS-1), i%(CARRY_BITS-1) + 1);
            } @*/
        }
        /*@ assert nat_of_int(i+2) == succ(succ(nat_of_int(i))); @*/
    }

    big_int_reduce(f_n);

    {
        char* x_hex = big_int_to_hex(f_n);
         /*@ assert string(x_hex,?cs)
            &*& base_n(hex_chars(),reverse(cs),_,fib(nat_of_int(orig_n))); @*/
        printf("%s\n",x_hex);
        free(x_hex);
        /*@ leak base_n(_,_,_,_); @*/
    }

    ///*@ open bi_big_int(x,?car,?und,_); @*/
    //printf("%p\n",(void*)x->first);
    ///*@ close bi_big_int(x,car,und,_); @*/

    free_big_int_inner(f_n);
    free_big_int_inner(f_n_1);

    return 0;
}


