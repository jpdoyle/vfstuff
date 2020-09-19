#include "bi_big_int.h"
#include "bitops.h"
/*@ #include <arrays.gh> @*/

/*@
#if 1
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() assume(false);
#endif
@*/


void big_int_tiny_mul(int32_t s, big_int* x)
    /*@ requires bi_big_int(x,?carry,?und,?v)
            &*&  exists<nat>(?lg2)
            &*&  abs(s) <= pow_nat(2,lg2)
            &*&  carry >= int_of_nat(lg2); @*/
    /*@ ensures  bi_big_int(x,carry-int_of_nat(lg2), und||(s<0), s*v);
      @*/
    /*@ terminates; @*/
{
    big_int_block* i = x->first;

    /* for(; i; i = i->next) */
    do
        /*@ requires bi_block(i, ?ilast, ?iprev, 0, ?loop_ptrs,
                                   ?loop_chunks)
                &*&  let(pow_nat(2,nat_of_int(31-carry))-1,?upper)
                &*&  let(und ? -upper : 0,?lower)
                &*&  !!forall(loop_chunks, (bounded)(-upper,upper))
                &*&  !!forall(loop_chunks, (bounded)(lower,upper))
                &*&  let(pow_nat(2,
                            nat_of_int(31-(carry-int_of_nat(lg2))))-1,
                         ?upper2)
                &*&  let((und||(s<0)) ? -upper2 : 0,?lower2)
                ; @*/
        /*@ ensures  bi_block(old_i, ilast,  iprev, 0, loop_ptrs,
                                   ?new_chunks)
                &*&  !!forall(new_chunks, (bounded)(-upper2,upper2))
                &*&  !!forall(new_chunks, (bounded)(lower2,upper2))
                &*&  poly_eval(new_chunks,CHUNK_BASE)
                    == s*poly_eval(loop_chunks,CHUNK_BASE)
                ; @*/
        /*@ decreases length(loop_ptrs); @*/
    {
        /*@ open bi_block(_,_,_,_,_,_); @*/
        /*@ assert i->chunks[..N_INTS] |-> ?i_blk_chunks; @*/
        /*@ if(i != ilast) {
            assert bi_block(_,_,_,_,_,?rest_chunks);
            forall_append_exact(i_blk_chunks,rest_chunks,
                (bounded)(-upper,upper));
            forall_append_exact(i_blk_chunks,rest_chunks,
                (bounded)(lower,upper));
        } @*/
        for(size_t block_i = 0; block_i < N_INTS; ++block_i)
            /*@ requires i->chunks[block_i..N_INTS] |-> ?blk_chunks
                    &*&  !!forall(blk_chunks, (bounded)(-upper,upper))
                    &*&  !!forall(blk_chunks, (bounded)(lower,upper))
                    ; @*/
            /*@ ensures  i->chunks[old_block_i..N_INTS] |-> ?new_blk_chunks
                    &*&  !!forall(new_blk_chunks, (bounded)(-upper2,upper2))
                    &*&  !!forall(new_blk_chunks, (bounded)(lower2,upper2))
                    &*&  poly_eval(new_blk_chunks,CHUNK_BASE)
                        == s*poly_eval(blk_chunks,CHUNK_BASE)
                    ; @*/
            /*@ decreases N_INTS-block_i; @*/
        {
            /*@ {
                open ints(&i->chunks[0]+block_i,_,_);
                integer_limits(&i->chunks[0]+block_i);
            } @*/
            /*@ assert *(&i->chunks[0]+block_i) |-> ?i_v; @*/
            /*@ {

                my_mul_mono_r((pow_nat(2,lg2)-1),upper,
                    pow_nat(2,nat_of_int(31-carry)));
                pow_plus(2,lg2,31-carry);

                pow_soft_monotonic(2,
                    nat_of_int(31-(carry-int_of_nat(lg2))),N31);
                if(s*i_v > upper2) {
                    if(s < 0) {
                        my_mul_mono_r(-s,-i_v,upper);
                        my_mul_mono_l(-s,pow_nat(2,lg2),upper);
                    } else {
                        my_mul_mono_r(s,i_v,upper);
                        my_mul_mono_l(s,pow_nat(2,lg2),upper);
                    }

                    assert false;
                }

                if(s*i_v < 0 && !(und||(s < 0))) {
                    my_mul_mono_l(0,s,i_v);
                    assert false;
                }

                if(s*i_v < lower2) {
                    assert lower2 == -upper2;
                    if(s >= 0) {
                        my_mul_mono_r(s,-upper,i_v);
                        my_mul_mono_l((-pow_nat(2,lg2)),-s,upper);
                    } else {
                        my_mul_mono_r(-s,-upper,-i_v);
                        my_mul_mono_l(-pow_nat(2,lg2),s,upper);
                    }

                    assert false;
                }

            } @*/
            *(&i->chunks[0] + block_i) *= s;
            /*@ assert i->chunks[block_i+1..N_INTS] |->
                    ?rest_chunks; @*/

            /*@ recursive_call(); @*/

            /*@ {
                assert i->chunks[old_block_i+1..N_INTS] |->
                    ?new_chunks;
                note_eq( poly_eval(cons(s*i_v,new_chunks),CHUNK_BASE)
                    ,  s*(i_v
                    + CHUNK_BASE
                        *poly_eval(rest_chunks,CHUNK_BASE)));
            } @*/
        }

        /*@ assert i->chunks[..N_INTS] |-> ?final_chunks; @*/

    /* } */
        i = i->next;
        /*@ assert let(i,?next); @*/
        /*@ list<int> loop_rest_chunks; @*/

        /*@ if(i) {
            assert bi_block(i,_,_,0,_,?rest_blocks);
            loop_rest_chunks = rest_blocks;
        } @*/

        /*@ recursive_call(); @*/

        /*@ {
            assert bi_block(next,_,_,_,_,?rest_chunks);
            forall_append_exact(final_chunks,rest_chunks,
                (bounded)(-upper2,upper2));
            forall_append_exact(final_chunks,rest_chunks,
                (bounded)(lower2,upper2));

            mul_3var(pow_nat(CHUNK_BASE,nat_of_int(N_INTS)),s,
                poly_eval(loop_rest_chunks,CHUNK_BASE));

            note_eq( poly_eval(append(final_chunks,rest_chunks),CHUNK_BASE)
                ,  s*(poly_eval(i_blk_chunks,CHUNK_BASE)
                + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                    *poly_eval(loop_rest_chunks,CHUNK_BASE)));
        } @*/

    } while(i);
    /*@ note_eq(-(s*v),s*(-v)); @*/
}

big_int* big_int_small_mul(big_int* dst,int32_t s,const big_int* x)
    /*@ requires [?f]bi_big_int(x,CARRY_BITS,false,?v)
            &*&  dst == 0 ? emp
            :    bi_big_int(dst,CARRY_BITS,false,0); @*/
    /*@ ensures  [ f]bi_big_int(x,CARRY_BITS,false, v)
            &*&  bi_big_int(result,CARRY_BITS,false,s*v); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    big_int* ret = dst ? dst : new_big_int_zero();
    uint64_t abs_s = s < 0 ? (uint64_t)-(int64_t)s : (uint64_t)s;
    /*@ shiftleft_def(1,N31); @*/
    /*@ division_unique(pow_nat(2,N32),2,pow_nat(2,N31),0); @*/
    /*@ division_unique(abs_s,pow_nat(2,N32),0,abs_s); @*/
    /*@ bi_big_int_unique(ret,x); @*/
    uint64_t mask  = ((uint64_t)1)<<31;
    uint64_t carries = 0;
    /*@ nat lg2 = N32; @*/
    for(; mask > abs_s; mask >>= 1)
        /*@ invariant int_of_nat(lg2) <= 32
                &*&   mask == pow_nat(2,lg2)/2
                &*&   mask <  pow_nat(2,lg2)
                &*&   0 == (abs_s/pow_nat(2,lg2))
                ; @*/
        /*@ decreases mask; @*/
    {
        /*@ {
            shiftright_div(mask,N1);
            assert mask >= 0;
            div_rem(mask,2);
            switch(lg2) {
            case zero: assert false;
            case succ(n):
                division_unique(pow_nat(2,lg2),2,pow_nat(2,n),0);
                lg2 = n;
            }
            division_unique(abs_s,pow_nat(2,lg2), 0,abs_s);
        } @*/
    }

    for(; mask; mask >>= 1)
        /*@ invariant bi_big_int(ret,CARRY_BITS-carries,_,?retv)
                &*&   [ f]bi_big_int(x,CARRY_BITS,false, v)
                &*&   carries < CARRY_BITS-2
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
        ++carries;
        if(abs_s&mask) {
            ++carries;
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
        if(carries >= (uint64_t)(CARRY_BITS-2)) {
            carries = 0;
            big_int_reduce(ret);
        }
    }
    big_int_reduce(ret);

    /*@ if(lg2 != zero) {
        pow_monotonic(2,zero,lg2);
        assert mask == 0;
        assert pow_nat(2,lg2)/2 == 0;
        div_rem(pow_nat(2,lg2),2);
        assert false;
    } @*/
    /*@ division_unique(abs_s,pow_nat(2,lg2),abs_s,0); @*/

    if(s < 0) {
        /*@ note_eq(s*v,-((-s)*v)); @*/
        big_int_negate(ret);
    }
    return ret;
}

big_int* big_int_mul(const big_int* x,const big_int* y)
    /*@ requires [?xf]bi_big_int(x,CARRY_BITS,false,?xv)
            &*&  [?yf]bi_big_int(y,CARRY_BITS,false,?yv); @*/
    /*@ ensures  [ xf]bi_big_int(x,CARRY_BITS,false, xv)
            &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
            &*&  bi_big_int(result,CARRY_BITS,false,xv*yv)
            &*&  result != x &*& result != y; @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    big_int* ret = new_big_int_zero();
    big_int* scratch = new_big_int_zero();
    /*@ shiftleft_def(1,nat_of_int(CHUNK_BITS)); @*/
    /*@ pow_monotonic(2,nat_of_int(CHUNK_BITS),N31); @*/
    int32_t chunk_base = (1<<CHUNK_BITS);

    big_int_block* i;
    /*@ open bi_big_int(x,_,_,_); @*/
    /*@ assert [xf]x->first |-> ?first; @*/
    /*@ assert [xf]x->is_pos |-> ?is_pos; @*/
    /*@ assert [xf]bi_block(first,?xlast,0,0,?xptrs,?xchunks);
      @*/
    /*@ bi_big_int_unique(ret,scratch); @*/
    for(i = x->last; i; i = i->prev)
        /*@ requires [ xf]bi_block(first, i, 0, ?inext, ?loop_ptrs,
                                   ?loop_chunks)
                &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
                &*&  bi_big_int(ret,CARRY_BITS,false,?retv)
                &*&  bi_big_int(scratch, CARRY_BITS,false,0)
                &*&  ret != scratch
                ; @*/
        /*@ ensures  [ xf]bi_block(first, old_i, 0,  inext,  loop_ptrs,
                                    loop_chunks)
                &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
                &*&  bi_big_int(ret,CARRY_BITS,false,
                        poly_eval(loop_chunks,CHUNK_BASE)*yv
                        + pow_nat(CHUNK_BASE,
                                nat_of_int(length(loop_chunks)))
                            *retv)
                &*&  bi_big_int(scratch, _,_,_)
                ; @*/
        /*@ decreases length(loop_ptrs); @*/
    {
        /*@ bi_block_rend(first,i); @*/
        /*@ assert [xf]i->chunks[..N_INTS] |-> ?i_chunks; @*/
        for(size_t block_i = N_INTS; block_i > 0; --block_i)
            /*@ requires [xf]i->chunks[..block_i] |-> ?blk_chunks
                    &*&  block_i >= 0
                    &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
                    &*&  bi_big_int(ret,CARRY_BITS,false,?blk_retv)
                    &*&  bi_big_int(scratch, CARRY_BITS,false,0)
                    &*&  ret != scratch
                    ; @*/
            /*@ ensures  [xf]old_i->chunks[..old_block_i] |-> blk_chunks
                    &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
                    &*&  bi_big_int(ret,CARRY_BITS,false,
                            poly_eval(blk_chunks,CHUNK_BASE)*yv
                            + pow_nat(CHUNK_BASE,
                                    nat_of_int(length(blk_chunks)))
                            *blk_retv)
                    &*&  bi_big_int(scratch, CARRY_BITS,false,0)
                    &*&  ret != scratch
                    ; @*/
            /*@ decreases block_i; @*/
        {
            /*@ ints_split(&i->chunks[0],block_i-1); @*/
            /*@ open ints((&i->chunks[0]) + block_i-1,_,_); @*/
            int32_t v = i->chunks[block_i-1];
            big_int* new_ret = big_int_small_mul(scratch, chunk_base,
                    ret);
            /*@ bi_big_int_unique(ret,new_ret); @*/
            free_big_int_inner(ret);
            ret = big_int_small_mul(NULL,v,y);

            //big_int_set(ret,0);
            //ret = big_int_small_mul(ret,v,y);

            /*@ bi_big_int_unique(ret,new_ret); @*/
            big_int_pluseq(new_ret,ret);
            big_int_reduce(new_ret);

            free_big_int_inner(ret);
            scratch = new_big_int_zero();
            /*@ bi_big_int_unique(new_ret,scratch); @*/


            //big_int_set(ret,0);
            //scratch = ret;

            ret = new_ret;
            /*@ assert [xf]i->chunks[..block_i-1] |-> ?rest; @*/
            /*@ assert bi_big_int(ret,CARRY_BITS,false,
                    v*yv + CHUNK_BASE*blk_retv); @*/


            /*@ recursive_call(); @*/
            /*@ {
                close [xf]ints((&i->chunks[0]) + old_block_i-1,1,_);
                ints_join(&i->chunks[0]);
                assert bi_big_int(ret,CARRY_BITS,false, ?final_retv);
                assert final_retv
                    == poly_eval(rest,CHUNK_BASE)*yv
                    + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                        *(v*yv + CHUNK_BASE*blk_retv);
                mul_3var(
                    pow_nat(CHUNK_BASE, nat_of_int(length(rest))),v,yv);
                note_eq( final_retv
                    ,  poly_eval(rest,CHUNK_BASE)*yv
                    + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                        *(v*yv)
                    + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                        *(CHUNK_BASE*blk_retv));
                assert final_retv
                    == (poly_eval(rest,CHUNK_BASE)
                    + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                        *v)*yv
                    + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                        *(CHUNK_BASE*blk_retv);
                assert final_retv
                    == (poly_eval(rest,CHUNK_BASE)
                    + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                        *v)*yv
                    + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                        *CHUNK_BASE*blk_retv;
                note_eq( final_retv
                    ,  (poly_eval(rest,CHUNK_BASE)
                    + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                        *v)*yv
                    + (CHUNK_BASE
                        *pow_nat(CHUNK_BASE,
                            nat_of_int(length(rest))))
                      *blk_retv);
                assert final_retv
                    == poly_eval(append(rest,{v}),CHUNK_BASE)*yv
                    + (CHUNK_BASE
                        *pow_nat(CHUNK_BASE,
                            nat_of_int(length(rest))))
                      *blk_retv;
                assert final_retv
                    == poly_eval(append(rest,{v}),CHUNK_BASE)*yv
                    + (pow_nat(CHUNK_BASE,
                            nat_of_int(length(rest)+1)))
                      *blk_retv;
                assert final_retv
                    == poly_eval(append(rest,{v}),CHUNK_BASE)*yv
                    + pow_nat(CHUNK_BASE,
                            nat_of_int(length(blk_chunks)))
                      *blk_retv;
            } @*/
        }

        /*@ assert [xf]bi_block(first,_,_,i,_,?rest); @*/

        /*@ recursive_call(); @*/

        /*@ {
            close [xf]bi_block(old_i,old_i,_,_,_,_);
            bi_block_extend(first);

            assert bi_big_int(ret,CARRY_BITS,false, ?final_retv);
            assert final_retv
                == poly_eval(rest,CHUNK_BASE)*yv
                + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                    *(poly_eval(i_chunks,CHUNK_BASE)*yv
                            + pow_nat(CHUNK_BASE, nat_of_int(N_INTS))
                            *retv);

            note_eq( final_retv
                ,  poly_eval(rest,CHUNK_BASE)*yv
                + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                    *(poly_eval(i_chunks,CHUNK_BASE)*yv)
                + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                    *(pow_nat(CHUNK_BASE, nat_of_int(N_INTS))*retv));

            mul_3var(pow_nat(CHUNK_BASE, nat_of_int(length(rest))),
                    poly_eval(i_chunks,CHUNK_BASE),yv);

            assert final_retv
                == (poly_eval(rest,CHUNK_BASE)
                + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                    *poly_eval(i_chunks,CHUNK_BASE))*yv
                + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                    *(pow_nat(CHUNK_BASE, nat_of_int(N_INTS))*retv);
            assert final_retv
                == (poly_eval(rest,CHUNK_BASE)
                + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                    *poly_eval(i_chunks,CHUNK_BASE))*yv
                + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                    *pow_nat(CHUNK_BASE, nat_of_int(N_INTS))*retv;
            mul_3var(pow_nat(CHUNK_BASE, nat_of_int(length(rest))),
                    pow_nat(CHUNK_BASE, nat_of_int(N_INTS)),retv);
            pow_plus(2,nat_of_int(length(rest)),N_INTS);
            note_eq( final_retv
                ,  (poly_eval(rest,CHUNK_BASE)
                + pow_nat(CHUNK_BASE, nat_of_int(length(rest)))
                    *poly_eval(i_chunks,CHUNK_BASE))*yv
                + (pow_nat(CHUNK_BASE, nat_of_int(length(rest)+N_INTS)))
                    *retv);
            assert final_retv
                == poly_eval(append(rest,i_chunks),CHUNK_BASE)*yv
                + (pow_nat(CHUNK_BASE, nat_of_int(length(rest)+N_INTS)))
                    *retv;
            assert final_retv
                == poly_eval(append(rest,i_chunks),CHUNK_BASE)*yv
                + (pow_nat(CHUNK_BASE, nat_of_int(length(loop_chunks))))
                    *retv;
        } @*/
    }
    free_big_int_inner(scratch);
    if(!ret->is_pos) big_int_negate(ret);
    return ret;
}

