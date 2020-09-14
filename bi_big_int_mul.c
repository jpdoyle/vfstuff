#include "bi_big_int.h"
#include "bitops.h"

#if 0
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() assume(false);
#endif


big_int* big_int_small_mul(big_int* dst,int32_t s,const big_int* x)
    /*@ requires [?f]bi_big_int(x,CARRY_BITS,false,?v)
            &*&  dst == 0 ? emp
            :    bi_big_int(dst,CARRY_BITS,false,0); @*/
    /*@ ensures  [ f]bi_big_int(x,CARRY_BITS,false, v)
            &*&  bi_big_int(result,CARRY_BITS,false,s*v); @*/
    /*@ terminates; @*/
{
    big_int* ret = dst ? dst : new_big_int_zero();
    uint64_t abs_s = s < 0 ? (uint64_t)-(int64_t)s : (uint64_t)s;
    /*@ shiftleft_def(1,N31); @*/
    /*@ division_unique(pow_nat(2,N32),2,pow_nat(2,N31),0); @*/
    /*@ division_unique(abs_s,pow_nat(2,N32),0,abs_s); @*/
    /*@ bi_big_int_unique(ret,x); @*/
    uint64_t mask  = ((uint64_t)1)<<31;
    /*@ nat lg2 = N32; @*/

    for(; mask; mask >>= 1)
        /*@ invariant bi_big_int(ret,CARRY_BITS,false,?retv)
                &*&   [ f]bi_big_int(x,CARRY_BITS,false, v)
                &*&   ret != x
                &*&   int_of_nat(lg2) <= 32
                &*&   mask == pow_nat(2,lg2)/2
                &*&   mask <  pow_nat(2,lg2)
                &*&   retv == (abs_s/pow_nat(2,lg2))*v
                ; @*/
        /*@ decreases mask; @*/
    {
        /*@ {
            split_fraction bi_big_int(ret,_,_,_) by (1/2);
            shiftright_div(mask,N1);
            assert mask >= 0;
            div_rem(mask,2);
            switch(lg2) {
            case zero: assert false;
            case succ(n):
                division_unique(pow_nat(2,lg2),2,pow_nat(2,n),0);
                lg2 = n;
            }
        } @*/
        big_int_pluseq(ret,ret);
        if(abs_s&mask) {
            /*@ {


            } @*/
            big_int_pluseq(ret,x);
        }
        /*@ {
            assert bi_big_int(ret,_,_,?retv1);
            bitand_flag(abs_s,lg2);
            assert retv == (abs_s/pow_nat(2,succ(lg2)))*v;
            assert retv1 == 2*retv + ((abs_s&mask) ? v : 0);
            assert retv1 == 2*(abs_s/pow_nat(2,succ(lg2)))*v
                + ((abs_s&mask) ? v : 0);
            bitand_cases(abs_s,lg2);
            assert (abs_s&mask)
                == abs_s%pow_nat(2,succ(lg2)) - abs_s%pow_nat(2,lg2);
            assert retv1 == 2*(abs_s/pow_nat(2,succ(lg2)))*v
                + ((abs_s&mask) ? v : 0);
            div_rem(abs_s,pow_nat(2,lg2));
            div_rem(abs_s,pow_nat(2,succ(lg2)));
            assert abs_s
                == pow_nat(2,lg2)*(abs_s/pow_nat(2,lg2))
                + abs_s%pow_nat(2,lg2);
            assert abs_s
                == pow_nat(2,succ(lg2))*(abs_s/pow_nat(2,succ(lg2)))
                + abs_s%pow_nat(2,succ(lg2));
            note_eq( abs_s
                ,  pow_nat(2,succ(lg2))*(abs_s/pow_nat(2,succ(lg2)))
                + (abs_s&mask) + abs_s%pow_nat(2,lg2));

            if((abs_s&mask) != 0) {
                assert (abs_s&mask) == pow_nat(2,lg2);
                division_unique(abs_s&mask,pow_nat(2,lg2),1,0);
            } else {
                division_unique(abs_s&mask,pow_nat(2,lg2),0,0);
            }
            note_eq( (abs_s&mask)
                ,  pow_nat(2,lg2)
                    *((abs_s&mask)/pow_nat(2,lg2)));

            mul_3var(pow_nat(2,lg2),2,abs_s/pow_nat(2,succ(lg2)));
            assert abs_s
                == pow_nat(2,lg2)*(2*(abs_s/pow_nat(2,succ(lg2))))
                + (abs_s&mask)
                + abs_s%pow_nat(2,lg2);
            assert abs_s
                == pow_nat(2,lg2)*(2*(abs_s/pow_nat(2,succ(lg2))))
                + pow_nat(2,lg2)*((abs_s&mask)/pow_nat(2,lg2))
                + abs_s%pow_nat(2,lg2);
            note_eq( abs_s
                ,  pow_nat(2,lg2)*((2*(abs_s/pow_nat(2,succ(lg2))))
                                 +(abs_s&mask)/pow_nat(2,lg2))
                + abs_s%pow_nat(2,lg2));
            mod_sign(abs_s,pow_nat(2,lg2));
            if((2*(abs_s/pow_nat(2,succ(lg2))))
                    + ((abs_s&mask)/pow_nat(2,lg2)) > abs_s) {
                my_mul_mono_l(1,pow_nat(2,lg2),
                    (2*(abs_s/pow_nat(2,succ(lg2))))
                        + ((abs_s&mask)/pow_nat(2,lg2)));
                assert false;
            }
            division_unique(abs_s,pow_nat(2,lg2),
                (2*(abs_s/pow_nat(2,succ(lg2))))
                + ((abs_s&mask)/pow_nat(2,lg2)),
                abs_s%pow_nat(2,lg2));

            note_eq( (abs_s/pow_nat(2,lg2))
                ,  2*(abs_s/pow_nat(2,succ(lg2)))
                + ((abs_s&mask)/pow_nat(2,lg2)));
            note_eq( (abs_s/pow_nat(2,lg2))*v
                ,  (2*(abs_s/pow_nat(2,succ(lg2)))
                + (abs_s&mask)/pow_nat(2,lg2))*v);
            assert (abs_s/pow_nat(2,lg2))*v
                == (2*(abs_s/pow_nat(2,succ(lg2))))*v
                + ((abs_s&mask)/pow_nat(2,lg2))*v;
            assert (abs_s/pow_nat(2,lg2))*v
                == 2*(abs_s/pow_nat(2,succ(lg2)))*v
                + ((abs_s&mask)/pow_nat(2,lg2))*v;
            assert (abs_s/pow_nat(2,lg2))*v
                == 2*retv
                + ((abs_s&mask)/pow_nat(2,lg2))*v;
            assert (abs_s/pow_nat(2,lg2))*v
                == retv1;
        } @*/
        big_int_reduce(ret);
    }

    /*@ if(lg2 != zero) {
        pow_monotonic(2,zero,lg2);
        assert mask == 0;
        assert pow_nat(2,lg2)/2 == 0;
        div_rem(pow_nat(2,lg2),2);
        assert false;
    } @*/
    /*@ division_unique(abs_s,pow_nat(2,lg2),abs_s,0); @*/

    if(s < 0) big_int_negate(ret);
    return ret;
}

big_int* big_int_mul(const big_int* x,const big_int* y)
    /*@ requires [?xf]bi_big_int(x,CARRY_BITS,false,?xv)
            &*&  [?yf]bi_big_int(y,CARRY_BITS,false,?yv); @*/
    /*@ ensures  [ xf]bi_big_int(x,CARRY_BITS,false, xv)
            &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
            &*&  bi_big_int(result,CARRY_BITS,false,xv*yv); @*/
    /*@ terminates; @*/
{
    big_int* ret = new_big_int_zero();
    big_int* scratch = new_big_int_zero();
    int32_t chunk_base = (1<<CHUNK_BITS);

    big_int* i;
    /*@ assert x->first |-> ?first; @*/
    /*@ assert x->is_pos |-> ?is_pos; @*/
    /*@ assert [ xf]bi_block_opt(first,?xlast,0,0,?xptrs,?xchunks);
      @*/
    for(i = x->last; i; i = i->prev)
        /*@ requires [ xf]bi_block(first, i, 0, ?inext, ?loop_ptrs,
                                   ?loop_chunks)
                &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
                &*&  bi_big_int(ret,CARRY_BITS,false,?retv)
                &*&  bi_big_int(scratch, CARRY_BITS,false,0)
                ; @*/
        /*@ ensures  [ xf]bi_block(first, ole_i, 0,  inext,  loop_ptrs,
                                    loop_chunks)
                &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
                &*&  bi_big_int(ret,CARRY_BITS,false,
                        poly_eval(loop_chunks,CHUNK_BASE)*yv
                        + pow_nat(CHUNK_BASE,length(loop_chunks))*retv)
                &*&  bi_big_int(scratch, _,_,_)
                ; @*/
        /*@ decreases length(loop_ptrs); @*/
    {
        size_t block_i;
        for(block_i = N_INTS; block_i > 0; --block_i)
        {
            int32_t v = i->chunks[block_i-1];
            big_int* new_ret = big_int_small_mul(scratch, chunk_base,
                    v, ret);
            bigi_int_set(ret,0);
            ret = big_int_small_mul(ret,v,y);
            big_int_pluseq(new_ret,ret);
            big_int_reduce(new_ret);
            big_int_set(ret,0);
            scratch = ret;
            ret = new_ret;
        }
    }
    free_big_int_inner(scratch);
    if(!ret->is_pos) big_int_negate(ret);
    return ret;
}

