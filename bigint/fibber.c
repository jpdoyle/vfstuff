#include <string.h>
#include <stdio.h>
#include <limits.h>
#include "../bi_big_int.h"
/*@ #include "../util.gh" @*/
/*@ #include "../poly.gh" @*/

/*@
#if 1
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() assume(false);
#endif
@*/

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

lemma void fib_fast(nat n)
    requires true;
    ensures  fib(nat_of_int(2*int_of_nat(n)))
                == fib(n)*(2*fib(succ(n)) - fib(n))
        &*&  fib(nat_of_int(2*int_of_nat(n)+1))
                == fib(n)*fib(n) + fib(succ(n))*fib(succ(n));
{
    switch(n) {
    case zero:
    case succ(n0):
        fib_fast(n0);
        assert fib(nat_of_int(2*int_of_nat(n0)))
                    == fib(n0)*(2*fib(succ(n0)) - fib(n0))
            &*&  fib(nat_of_int(2*int_of_nat(n0)+1))
                    == fib(n0)*fib(n0) + fib(n)*fib(n);
        assert fib(nat_of_int(2*int_of_nat(n0)))
                    == fib(n0)*(2*fib(succ(n0)) - fib(n0))
            &*&  fib(nat_of_int(2*int_of_nat(n0)+1))
                    == fib(n0)*fib(n0) + fib(n)*fib(n);
        assert fib(nat_of_int(2*int_of_nat(n)))
            == fib(nat_of_int(2*int_of_nat(n0)+2));
        assert fib(nat_of_int(2*int_of_nat(n)))
            == fib(succ(succ(nat_of_int(2*int_of_nat(n0)))));
        assert fib(nat_of_int(2*int_of_nat(n)+1))
            == fib(succ(succ(nat_of_int(2*int_of_nat(n0)+1))));

        assert fib(nat_of_int(2*int_of_nat(n)))
            == fib(nat_of_int(2*int_of_nat(n0)))
            +  fib(nat_of_int(2*int_of_nat(n0)+1));
        assert fib(nat_of_int(2*int_of_nat(n)))
            == fib(n0)*(2*fib(n) - fib(n0))
            +  fib(n0)*fib(n0) + fib(n)*fib(n);
        assert fib(nat_of_int(2*int_of_nat(n)))
            == 2*fib(n0)*fib(n) - fib(n0)*fib(n0)
            +  fib(n0)*fib(n0) + fib(n)*fib(n);
        assert fib(nat_of_int(2*int_of_nat(n)))
            == 2*fib(n0)*fib(n) + fib(n)*fib(n);
        note_eq( fib(nat_of_int(2*int_of_nat(n)))
            ,  fib(n)*(2*fib(n0) + fib(n)));
        assert fib(nat_of_int(2*int_of_nat(n)))
            == fib(n)*(fib(n0) + fib(succ(n)));
        assert fib(nat_of_int(2*int_of_nat(n)))
            == fib(n)*(fib(succ(n)) - fib(n) + fib(succ(n)));
        assert fib(nat_of_int(2*int_of_nat(n)))
            == fib(n)*(2*fib(succ(n)) - fib(n));

        assert fib(nat_of_int(2*int_of_nat(n)+1))
            == fib(nat_of_int(2*int_of_nat(n0)+1))
            +  fib(nat_of_int(2*int_of_nat(n)));
        note_eq( fib(nat_of_int(2*int_of_nat(n)+1))
            ,  fib(n0)*fib(n0) + fib(n)*fib(n)
            +  fib(n)*(2*fib(succ(n)) - fib(n)));
        assert fib(nat_of_int(2*int_of_nat(n)+1))
            == fib(n0)*fib(n0) + fib(n)*fib(n)
            +  2*fib(n)*fib(succ(n)) - fib(n)*fib(n);
        assert fib(nat_of_int(2*int_of_nat(n)+1))
            == fib(n0)*fib(n0) + 2*fib(n)*fib(succ(n));
        assert fib(nat_of_int(2*int_of_nat(n)+1))
            == fib(n0)*fib(n0) + 2*fib(n)*(fib(n0) + fib(n));
        assert fib(nat_of_int(2*int_of_nat(n)+1))
            == fib(n0)*fib(n0) + 2*fib(n)*fib(n0) + 2*fib(n)*fib(n);
        assert fib(nat_of_int(2*int_of_nat(n)+1))
            == (fib(n0) + fib(n))*fib(n0)
            +  (fib(n0) + fib(n))*fib(n) + fib(n)*fib(n);
        note_eq( fib(nat_of_int(2*int_of_nat(n)+1))
            ,  (fib(n0) + fib(n))*(fib(n0)+fib(n))
            +  fib(n)*fib(n));
        assert fib(nat_of_int(2*int_of_nat(n)+1))
            == fib(succ(n))*fib(succ(n)) + fib(n)*fib(n);
    }
}

  @*/

int fib_linear(void)
    /*@ requires true; @*/
    /*@ ensures  result == 0; @*/
{
    /*@ ALREADY_PROVEN() @*/
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
                &*&   carry_n_1 >= 1
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
    big_int_reduce(f_n_1);

    {
        big_int* res = big_int_mul(f_n,f_n_1);
        //char* x_hex = big_int_to_hex(f_n);
        // /*@ assert string(x_hex,?cs)
        //    &*& base_n(hex_chars(),reverse(cs),_,fib(nat_of_int(orig_n))); @*/


    /*@ my_mul_mono_r(fib(nat_of_int(orig_n))
                    ,0,fib(nat_of_int(orig_n+1))); @*/
        char* x_hex = big_int_to_hex(res);
         /*@ assert string(x_hex,?cs)
            &*& base_n(hex_chars(),reverse(cs),_,
                    fib(nat_of_int(orig_n))
                    *fib(nat_of_int(orig_n+1))); @*/
        printf("%s\n",x_hex);
        free(x_hex);
        /*@ leak base_n(_,_,_,_); @*/
        free_big_int_inner(res);
    }

    ///*@ open bi_big_int(x,?car,?und,_); @*/
    //printf("%p\n",(void*)x->first);
    ///*@ close bi_big_int(x,car,und,_); @*/

    free_big_int_inner(f_n);
    free_big_int_inner(f_n_1);

    return 0;
}

#ifndef __FILE__
int fib_log(void)
#else
int main(void)
#endif
    /*@ requires true; @*/
    /*@ ensures  result == 0; @*/
{
    int n_inp;
    big_int* f_n = new_big_int_from(0);
    big_int* f_n_1 = new_big_int_from(1);
    /*@ if(f_n == f_n_1) {
      bi_big_int_unique(f_n,f_n_1);
      assert false;
    } @*/

    do
        /*@ requires n_inp |-> _; @*/
        /*@ ensures  n_inp |-> ?n_v &*& n_v >= 0; @*/
    {
        int n_read;
        printf("n? "); fflush(stdout);
        n_read = scanf("%d",&n_inp);
        if(n_read < 1) n_inp = -1;
        getchar(); // \n
    } while(n_inp < 0);

    uint64_t n = (uint64_t)n_inp;

    /*@ shiftleft_def(1,N31); @*/
    /*@ division_unique(pow_nat(2,N32),2,pow_nat(2,N31),0); @*/
    /*@ division_unique(n,pow_nat(2,N32),0,n); @*/
    uint64_t mask  = ((uint64_t)1)<<31;
    /*@ nat lg2 = N32; @*/
    /*@ int sofar = 0; @*/

    for(; mask > n; mask >>= 1)
        /*@ invariant int_of_nat(lg2) <= 32
                &*&   mask == pow_nat(2,lg2)/2
                &*&   mask <  pow_nat(2,lg2)
                &*&   0 == (n/pow_nat(2,lg2))
                ; @*/
        /*@ decreases mask; @*/
    {
        /*@ {
            shiftright_div(mask,N1);
            assert mask >= 0;
            div_rem(mask,2);
            switch(lg2) {
            case zero: assert false;
            case succ(n0):
                division_unique(pow_nat(2,lg2),2,pow_nat(2,n0),0);
                lg2 = n0;
            }
            division_unique(n,pow_nat(2,lg2), 0,n);
        } @*/
    }

    for(; mask; mask >>= 1)
        /*@ invariant bi_big_int(f_n,CARRY_BITS,false,
                        fib(nat_of_int(sofar)))
                &*&   bi_big_int(f_n_1,CARRY_BITS,false,
                        fib(nat_of_int(sofar+1)))
                &*&   f_n != f_n_1
                &*&   int_of_nat(lg2) <= 32
                &*&   mask == pow_nat(2,lg2)/2
                &*&   mask <  pow_nat(2,lg2)
                &*&   sofar == (n/pow_nat(2,lg2))
                &*&   sofar >= 0
                ; @*/
        /*@ decreases mask; @*/
    {
        /*@ {
            shiftright_div(mask,N1);
            assert mask >= 0;
            div_rem(mask,2);
            switch(lg2) {
            case zero: assert false;
            case succ(n0):
                division_unique(pow_nat(2,lg2),2,pow_nat(2,n0),0);
                lg2 = n0;
            }
        } @*/

        /*@ fib_fast(nat_of_int(sofar)); @*/
        /*@ my_mul_mono_r(2,0,sofar); @*/
        /*@ assert succ(nat_of_int(2*sofar)) == nat_of_int(2*sofar+1); @*/
        /*@ assert succ(nat_of_int(2*sofar+1)) == nat_of_int(2*sofar+2); @*/

        // -2*fib(n+1)
        big_int* f_2n_r = big_int_small_mul(NULL, -2, f_n_1);
        // -2*fib(n+1) + fib(n)
        /*@ bi_big_int_unique(f_2n_r,f_n); @*/
        big_int_pluseq(f_2n_r,f_n);
        // 2*fib(n+1) - fib(n)
        big_int_negate(f_2n_r);
        big_int_reduce(f_2n_r);
        big_int* f_2n = big_int_mul(f_n,f_2n_r);
        free_big_int_inner(f_2n_r);

        // fib(n)*fib(n)
        /*@ split_fraction bi_big_int(f_n,_,_,_) by (1/2); @*/
        big_int* f_2n_1 = big_int_mul(f_n, f_n);
        // fib(n+1)*fib(n+1)
        /*@ split_fraction bi_big_int(f_n_1,_,_,_) by (1/2); @*/
        big_int* f_2n_1_r = big_int_mul(f_n_1, f_n_1);
        // -2*fib(n+1) + fib(n)
        /*@ bi_big_int_unique(f_2n_1,f_2n_1_r); @*/
        big_int_pluseq(f_2n_1,f_2n_1_r);
        big_int_reduce(f_2n_1);
        free_big_int_inner(f_2n_1_r);

        free_big_int_inner(f_n);
        free_big_int_inner(f_n_1);
        /*@ assert bi_big_int(f_2n,_,_,fib(nat_of_int(2*sofar))); @*/
        /*@ assert bi_big_int(f_2n_1,_,_,fib(nat_of_int(2*sofar+1))); @*/
        /*@ bi_big_int_unique(f_2n,f_2n_1); @*/

        if(n&mask) {
            /*@ sofar = 2*sofar + 1; @*/
            f_n = f_2n_1;
            f_n_1 = f_2n;
            big_int_pluseq(f_n_1,f_n);
            big_int_reduce(f_n_1);
        } else {
            /*@ sofar = 2*sofar; @*/
            f_n = f_2n;
            f_n_1 = f_2n_1;
        }

        /*@ {
            bitand_flag(n,lg2);
            bitand_cases(n,lg2);
            div_rem(n,pow_nat(2,lg2));
            div_rem(n,pow_nat(2,succ(lg2)));
            note_eq( n
                ,  pow_nat(2,succ(lg2))*(n/pow_nat(2,succ(lg2)))
                + (n&mask) + n%pow_nat(2,lg2));
            if((n&mask) != 0) {
                assert (n&mask) == pow_nat(2,lg2);
                division_unique(n&mask,pow_nat(2,lg2),1,0);
            } else {
                division_unique(n&mask,pow_nat(2,lg2),0,0);
            }
            note_eq( (n&mask)
                ,  pow_nat(2,lg2)
                    *((n&mask)/pow_nat(2,lg2)));

            mul_3var(pow_nat(2,lg2),2,n/pow_nat(2,succ(lg2)));

            ////////

            division_unique(n,pow_nat(2,lg2),
                (2*(n/pow_nat(2,succ(lg2))))
                + ((n&mask)/pow_nat(2,lg2)),
                n%pow_nat(2,lg2));

            note_eq( (n/pow_nat(2,lg2))
                ,  2*(n/pow_nat(2,succ(lg2)))
                + ((n&mask)/pow_nat(2,lg2)));

        } @*/
    }
    /*@ if(lg2 != zero) {
        pow_monotonic(2,zero,lg2);
        assert mask == 0;
        assert pow_nat(2,lg2)/2 == 0;
        div_rem(pow_nat(2,lg2),2);
        assert false;
    } @*/
    /*@ division_unique(n,pow_nat(2,lg2),n,0); @*/

    big_int_reduce(f_n);
    big_int_reduce(f_n_1);

    {
        char* x_hex = big_int_to_hex(f_n);
        /*@ assert string(x_hex,?cs)
            &*& base_n(hex_chars(),reverse(cs),_,fib(nat_of_int(n))); @*/


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

