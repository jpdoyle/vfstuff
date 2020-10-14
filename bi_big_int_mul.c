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

/*@

lemma void div_shift(int x,int b, nat n)
    requires b > 1 &*& x >= 0;
    ensures  (x/pow_nat(b,n))/b
        ==   (x/pow_nat(b,succ(n)))
        &*&  x%pow_nat(b,succ(n))
        ==   pow_nat(b,n)*((x/pow_nat(b,n))%b)
             +(x%pow_nat(b,n));
{
    div_rem(x,pow_nat(b,n));
    div_rem(x,pow_nat(b,succ(n)));
    div_rem((x/pow_nat(b,n)),b);
    div_sign(x,pow_nat(b,n));
    mod_sign(x,pow_nat(b,n));
    mod_sign(x/pow_nat(b,n),b);
    div_sign(x/pow_nat(b,n),b);

    my_mul_mono_r(pow_nat(b,n),0,((x/pow_nat(b,n))%b));
    my_mul_mono_r(pow_nat(b,n),((x/pow_nat(b,n))%b),b-1);
    assert pow_nat(b,n)*((x/pow_nat(b,n))%b)
        <= pow_nat(b,succ(n)) - pow_nat(b,n);
    note( pow_nat(b,n)*((x/pow_nat(b,n))%b) + (x%pow_nat(b,n))
        <  pow_nat(b,succ(n)));
    assert pow_nat(b,n)*((x/pow_nat(b,n))%b) + (x%pow_nat(b,n))
        >= 0;
    assert b*((x/pow_nat(b,n))/b) <= x/pow_nat(b,n);

    my_mul_mono_r(pow_nat(b,succ(n)),0,(x/pow_nat(b,n))/b);

    mul_3var(pow_nat(b,n),b,((x/pow_nat(b,n))/b));
    my_mul_mono_r(pow_nat(b,n),
        b*((x/pow_nat(b,n))/b),
        x/pow_nat(b,n));
    assert pow_nat(b,succ(n))*((x/pow_nat(b,n))/b)
        <= (pow_nat(b,n))*(x/pow_nat(b,n));
    assert pow_nat(b,succ(n))*((x/pow_nat(b,n))/b)
        <= x;

    note_eq( pow_nat(b,succ(n))*((x/pow_nat(b,n))/b)
        +  pow_nat(b,n)*((x/pow_nat(b,n))%b)
        +  (x%pow_nat(b,n))
        ,  pow_nat(b,n)
                *(b*((x/pow_nat(b,n))/b)
                  +((x/pow_nat(b,n))%b))
        +  (x%pow_nat(b,n)));
    assert pow_nat(b,succ(n))*((x/pow_nat(b,n))/b)
        +  pow_nat(b,n)*((x/pow_nat(b,n))%b)
        +  (x%pow_nat(b,n))
        == pow_nat(b,n)*(x/pow_nat(b,n))
        +  (x%pow_nat(b,n));

    assert pow_nat(b,succ(n))*((x/pow_nat(b,n))/b)
        +  pow_nat(b,n)*((x/pow_nat(b,n))%b)
        +  (x%pow_nat(b,n))
        == x;

    division_unique(x,pow_nat(b,succ(n)),
        (x/pow_nat(b,n))/b,
        pow_nat(b,n)*((x/pow_nat(b,n))%b)
        +(x%pow_nat(b,n)));
}

  @*/

void big_int_tiny_mul(int32_t s, big_int* x)
    /*@ requires bi_big_int(x,?carry,?und,?v)
            &*&  let(log_ceil(abs(s)),?lg2)
            &*&  carry >= int_of_nat(lg2); @*/
    /*@ ensures  bi_big_int(x,carry-int_of_nat(lg2), und||(s<0), s*v);
      @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
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

big_int* big_int_small_mul(big_int* dst,big_int* scratch,int32_t s,const big_int* x)
    /*@ requires [?f]bi_big_int(x,CARRY_BITS,false,?v)
            &*&  (dst != 0 ? bi_big_int(dst,CARRY_BITS,false,0) : emp)
            &*&  (scratch != 0 ? bi_big_int(scratch,_,_,_) : emp)
            ; @*/
    /*@ ensures  [ f]bi_big_int(x,CARRY_BITS,false, v)
            &*&  bi_big_int(result,CARRY_BITS,false,s*v)
            &*&  (scratch != 0 ? bi_big_int(scratch,_,_,_) : emp)
            ; @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    big_int* ret = dst ? dst : new_big_int_zero();
    bool free_scratch = !scratch;
    scratch = scratch ? scratch : new_big_int_zero();
    uint64_t abs_s = s < 0 ? (uint64_t)-(int64_t)s : (uint64_t)s;
    /*@ {
        shiftleft_def(1,nat_of_int(CARRY_BITS-2));
        division_unique(pow_nat(2,N32),2,pow_nat(2,N31),0);
        pow_times2(2,nat_of_int(CARRY_BITS-2),32/(CARRY_BITS-2)+1);
        pow_soft_monotonic(2,
            N32,
            nat_of_int((CARRY_BITS-2)*(32/(CARRY_BITS-2)+1)));
        division_unique(abs_s,
            pow_nat(2,nat_of_int((CARRY_BITS-2)*(32/(CARRY_BITS-2)+1))),
            0,abs_s);
        bi_big_int_unique(ret,x);
        bi_big_int_unique(ret,scratch);
        bi_big_int_unique(x,scratch);


    } @*/
    uint64_t mask  = (((uint64_t)1)<<(CARRY_BITS-2))-1;

    for(size_t shift = (size_t)(32/(CARRY_BITS-2))+1; shift > 0; --shift)
        /*@ invariant bi_big_int(ret,CARRY_BITS,false,?retv)
                &*&   [ f]bi_big_int(x,CARRY_BITS,false, v)
                &*&   shift >= 0
                &*&   (shift-1)*(CARRY_BITS-2) <= 32
                &*&   ret != x &*& ret != scratch &*& x != scratch
                &*&   retv == (abs_s/pow_nat(mask+1,nat_of_int(shift)))*v
                &*&   bi_big_int(scratch,_,_,_)
                ; @*/
        /*@ decreases shift; @*/
    {
        /*@ {
            shiftright_div(abs_s,
                nat_of_int((shift-1)*(CARRY_BITS-2)));
            div_rem(abs_s, pow_nat(2,nat_of_int((shift-1)*(CARRY_BITS-2))));
            div_sign(abs_s, pow_nat(2,nat_of_int((shift-1)*(CARRY_BITS-2))));
        } @*/
        uint64_t shifted = (abs_s>>((shift-1)*(uint64_t)(CARRY_BITS-2)));
        /*@ {
            bitand_pow_2(shifted,nat_of_int(CARRY_BITS-2));
            mod_sign(shifted,pow_nat(2,nat_of_int(CARRY_BITS-2)));
            div_rem(shifted,pow_nat(2,nat_of_int(CARRY_BITS-2)));
            assert (shifted&mask)
                == shifted%pow_nat(2,nat_of_int(CARRY_BITS-2));
            pow_monotonic(2,nat_of_int(CARRY_BITS-2),N31);

            assert (shifted&mask)
                < pow_nat(2,nat_of_int(CARRY_BITS-2));
            assert (shifted&mask) < pow_nat(2,N31);
            log_ceil_minimal(shifted&mask,nat_of_int(CARRY_BITS-2));

            pow_times2(2,nat_of_int(CARRY_BITS-2),shift-1);
            note_eq(shifted, abs_s/pow_nat(mask+1,nat_of_int(shift-1)));
        } @*/

        int32_t coeff = (int32_t)(shifted&mask);
        big_int* term = big_int_clone_into(scratch,x);
        /*@ bi_big_int_unique(term,ret); @*/
        big_int_tiny_mul(1<<(CARRY_BITS-2),ret);
        big_int_tiny_mul(coeff,term);
        big_int_pluseq(ret,term);
        big_int_reduce(ret);

        /*@ {
            assert bi_big_int(ret,_,_,?retv1);
            assert retv1 == (mask+1)*retv + (shifted%(mask+1))*v;
            assert retv1
                == (mask+1)
                    *((abs_s/pow_nat(mask+1,nat_of_int(shift)))*v)
                + (shifted%(mask+1))*v;
            note_eq( retv1
                ,  ((mask+1)
                    *(abs_s/pow_nat(mask+1,nat_of_int(shift)))
                    + shifted%(mask+1))*v);
            assert retv1
                == ((mask+1)
                    *(abs_s/pow_nat(mask+1,nat_of_int(shift)))
                    + (abs_s/pow_nat(mask+1,nat_of_int(shift-1)))%(mask+1))*v;
            div_shift(abs_s,mask+1,nat_of_int(shift-1));
            assert retv1
                == (abs_s/pow_nat(mask+1,nat_of_int(shift-1)))*v;
        } @*/
        /* @ {

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
    }

    /*@ division_unique(abs_s,pow_nat(2,N0),abs_s,0); @*/

    if(s < 0) {
        /*@ note_eq(s*v,-((-s)*v)); @*/
        big_int_negate(ret);
    }
    if(free_scratch) free_big_int_inner(scratch);
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
    big_int* ret = new_big_int_zero();
    big_int* scratch0 = new_big_int_zero();
    big_int* scratch1 = new_big_int_zero();
    /*@ shiftleft_def(1,nat_of_int(CHUNK_BITS)); @*/
    /*@ pow_monotonic(2,nat_of_int(CHUNK_BITS),N31); @*/
    int32_t chunk_base = (1<<CHUNK_BITS);

    /*@ open bi_big_int(x,_,_,_); @*/
    /*@ assert [xf]x->first |-> ?first; @*/
    /*@ assert [xf]x->is_pos |-> ?is_pos; @*/
    /*@ assert [xf]bi_block(first,?xlast,0,0,?xptrs,?xchunks);
      @*/
    /*@ poly_eval_bounded_pos(xchunks,
      pow_nat(2,nat_of_int(31-CARRY_BITS))-1, CHUNK_BASE); @*/
    /*@ if(is_pos) {
      assert abs_of(xv) == xv;
      assert xv == poly_eval(xchunks,CHUNK_BASE);
    } else {
      assert abs_of(xv) == -xv;
      assert -xv == poly_eval(xchunks,CHUNK_BASE);
    } @*/
    /*@ assert poly_eval(xchunks,CHUNK_BASE) == abs_of(xv); @*/

    big_int_block* i = x->last;

    /* for(i = x->last; i; i = i->prev) */
    do
        /*@ requires [ xf]bi_block(first, i, 0, ?inext, ?loop_ptrs,
                                   ?loop_chunks)
                &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
                &*&  bi_big_int(ret,CARRY_BITS,false,?retv)
                &*&  bi_big_int(scratch0,CARRY_BITS,false,0)
                &*&  bi_big_int(scratch1,_,_,_)
                ; @*/
        /*@ ensures  [ xf]bi_block(first, old_i, 0,  inext,  loop_ptrs,
                                    loop_chunks)
                &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
                &*&  bi_big_int(ret,CARRY_BITS,false,
                        poly_eval(loop_chunks,CHUNK_BASE)*yv
                        + pow_nat(CHUNK_BASE,
                                nat_of_int(length(loop_chunks)))
                            *retv)
                &*&  bi_big_int(scratch0,CARRY_BITS,false,0)
                &*&  bi_big_int(scratch1,_,_,_)
                ; @*/
        /*@ decreases length(loop_ptrs); @*/
    {
        /*@ if(first != i) bi_block_rend(first,i); @*/
        /*@ assert [xf]i->chunks[..N_INTS] |-> ?i_chunks; @*/
        for(size_t block_i = N_INTS; block_i > 0; --block_i)
            /*@ requires [xf]i->chunks[..block_i] |-> ?blk_chunks
                    &*&  block_i >= 0
                    &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
                    &*&  bi_big_int(ret,CARRY_BITS,false,?blk_retv)
                    &*&  bi_big_int(scratch0,CARRY_BITS,false,0)
                    &*&  bi_big_int(scratch1,_,_,_)
                    ; @*/
            /*@ ensures  [xf]old_i->chunks[..old_block_i] |-> blk_chunks
                    &*&  [ yf]bi_big_int(y,CARRY_BITS,false, yv)
                    &*&  bi_big_int(scratch0,CARRY_BITS,false,0)
                    &*&  bi_big_int(scratch1,_,_,_)
                    &*&  bi_big_int(ret,CARRY_BITS,false,
                            poly_eval(blk_chunks,CHUNK_BASE)*yv
                            + pow_nat(CHUNK_BASE,
                                    nat_of_int(length(blk_chunks)))
                            *blk_retv)
                    ; @*/
            /*@ decreases block_i; @*/
        {
            /*@ ints_split(&i->chunks[0],block_i-1); @*/
            /*@ open ints((&i->chunks[0]) + block_i-1,_,_); @*/
            int32_t v = i->chunks[block_i-1];
            big_int* new_ret = big_int_small_mul(scratch0,scratch1,
                    chunk_base, ret);
            /*@ bi_big_int_unique(ret,new_ret); @*/
            big_int_set(ret,0);
            ret = big_int_small_mul(ret,scratch1,v,y);

            /*@ bi_big_int_unique(ret,new_ret); @*/
            big_int_pluseq(new_ret,ret);
            big_int_reduce(new_ret);

            big_int_set(ret,0);
            scratch0 = ret;

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

        /*@ list<int> rest = nil; @*/
        /*@ if(first != i) {
          assert [xf]bi_block(first,_,_,i,_,?pref);
          rest = pref;
        } @*/

        i = i->prev;

        /*@ recursive_call(); @*/

        /*@ {
            close [xf]bi_block(old_i,old_i,_,_,_,_);
            if(first != old_i) {
                bi_block_extend(first);
            }

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
            mul_3var(pow_nat(CHUNK_BASE, nat_of_int(length(rest))),
                    pow_nat(CHUNK_BASE, nat_of_int(N_INTS)),retv);

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
            pow_plus(CHUNK_BASE,nat_of_int(length(rest)),N_INTS);
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
    } while(i);
    /*@ assert bi_big_int(ret,CARRY_BITS,false,abs_of(xv)*yv); @*/

    bool needs_flip = !x->is_pos;
    /*@ close [xf]bi_big_int(x,CARRY_BITS,false,_); @*/

    if(needs_flip) {
        big_int_negate(ret);
        /*@ assert bi_big_int(ret,CARRY_BITS,false,-(abs_of(xv)*yv)); @*/
        /*@ note_eq(-(abs_of(xv)*yv),(-abs_of(xv))*yv); @*/
        /*@ note_eq(-(abs_of(xv)*yv),xv*yv); @*/
    }

    /*@ bi_big_int_unique(ret,x); @*/
    /*@ bi_big_int_unique(ret,y); @*/
    free_big_int_inner(scratch0);
    free_big_int_inner(scratch1);

    return ret;
}

