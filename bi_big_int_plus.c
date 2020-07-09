#include "bi_big_int.h"

#if 1
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() assume(false);
#endif

void big_int_reduce(big_int* p)
    /*@ requires bi_big_int(p,?carry_bits,?v)
            &*&  carry_bits >= 1
            &*&  v >= 0; @*/
    /*@ ensures  bi_big_int(p,CARRY_BITS,v); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    /*@ open bi_big_int(_,_,_); @*/
    big_int_block* i = p->first;
    big_int_block* last = p->last;
    uint32_t carry = 0;

    /*@ assert bi_block(i,last,0,0,_,?chunks); @*/
    /*@ nat len_bits = log_nat(length(chunks)); @*/
    /*@ assert carry_bits >= 1; @*/
    /*@ assert carry_bits <= CARRY_BITS; @*/
    /*@ int extra_blocks = 1; @*/

    do
        /*@ requires bi_block(i, last,?bprev, 0, _,
                        ?loop_chunks)
                &*&  !!forall(loop_chunks,
                        (bounded)(0,pow_nat(2,nat_of_int(32-carry_bits))-1))
                &*&  carry >= 0
                &*&  carry < pow_nat(2,nat_of_int(CARRY_BITS))
                &*&  length(loop_chunks) < pow_nat(2,len_bits)
                &*&  extra_blocks == 0
                ?    !!poly_is_zero(loop_chunks)
                :    extra_blocks == 1
                ; @*/
        /*@ ensures  bi_block(old_i, last,bprev, 0, _,
                        ?new_chunks)
                &*&  !!forall(new_chunks,
                        (bounded)(0,pow_nat(2,nat_of_int(32-CARRY_BITS))-1))
                &*&  poly_eval(new_chunks,CHUNK_BASE)
                    == poly_eval(loop_chunks,CHUNK_BASE) + old_carry
                &*&  carry == 0
                ; @*/
        /*@ decreases extra_blocks + length(loop_chunks); @*/
    {
        size_t chunk_i;
        /*@ int block_carry = carry; @*/
        /*@ open bi_block(_,_,_,_,_,_); @*/
        /*@ assert i->chunks[..N_INTS] |-> ?i_blk_chunks; @*/
        /*@ if(i != last) {
            assert bi_block(_,_,_,_,_,?rest_chunks);
            forall_append_exact(i_blk_chunks,rest_chunks,
                (bounded)(0,pow_nat(2,nat_of_int(32-carry_bits))-1));
        } @*/
        /*@ if(poly_eval(i_blk_chunks,CHUNK_BASE) < 0) {
            int neg_x = poly_eval_neg(i_blk_chunks,CHUNK_BASE);
            forall_elim(i_blk_chunks,
                (bounded)(0,pow_nat(2,nat_of_int(32-carry_bits))-1),
                neg_x);
            assert false;
        } @*/

        for(chunk_i = 0; chunk_i <  N_INTS; ++chunk_i)
            /*@ requires i->chunks[chunk_i..N_INTS] |-> ?blk_chunks
                    &*&  !!forall(blk_chunks,
                            (bounded)(0,pow_nat(2,nat_of_int(32-carry_bits))-1))
                    &*&  poly_eval(blk_chunks,CHUNK_BASE) >= 0
                    &*&  carry >= 0
                    &*&  carry < pow_nat(2,nat_of_int(CARRY_BITS))
                    &*&  chunk_i >= 0 &*& chunk_i <= N_INTS
                    ; @*/
            /*@ ensures  i->chunks[old_chunk_i..N_INTS] |-> ?new_blk_chunks
                    &*&  !!forall(new_blk_chunks,
                            (bounded)(0,pow_nat(2,nat_of_int(32-CARRY_BITS))-1))
                    &*&  poly_eval(new_blk_chunks,CHUNK_BASE) >= 0
                    &*&  poly_eval(new_blk_chunks,CHUNK_BASE)
                         + carry
                            *pow_nat(CHUNK_BASE,
                                nat_of_int(length(new_blk_chunks)))
                        == poly_eval(blk_chunks,CHUNK_BASE) + old_carry
                    &*&  carry >= 0
                    &*&  carry < pow_nat(2,nat_of_int(CARRY_BITS))
                    ; @*/
            /*@ decreases length(blk_chunks); @*/
        {
            /*@ open uints(&i->chunks[0]+chunk_i,_,_); @*/
            /*@ u_integer_limits(&i->chunks[0]+chunk_i); @*/
            uint32_t new_chunk = *(&i->chunks[0]+chunk_i);
            /*@ int orig_chunk = new_chunk; @*/
            /*@ {
                assert new_chunk
                    < pow_nat(2,nat_of_int(32-carry_bits));
                assert carry < pow_nat(2,nat_of_int(CARRY_BITS));
                pow_monotonic(2,nat_of_int(CARRY_BITS),
                    nat_of_int(32-carry_bits));
                pow_soft_monotonic(2, nat_of_int(32-carry_bits+1),
                    nat_of_int(32));
                assert carry
                    < pow_nat(2,nat_of_int(32-carry_bits));
                note( new_chunk+carry
                    < 2*pow_nat(2,nat_of_int(32-carry_bits)));
                assert new_chunk+carry
                    < pow_nat(2,succ(nat_of_int(32-carry_bits)));
                assert new_chunk+carry
                    < pow_nat(2,nat_of_int(32-(carry_bits-1)));
                assert new_chunk+carry < pow_nat(2,nat_of_int(32));
            } @*/
            new_chunk += carry;
            /*@ {
                shiftleft_def(1,nat_of_int(32-CARRY_BITS));
                shiftright_div(new_chunk,nat_of_int(32-CARRY_BITS));
                bitand_pow_2(new_chunk,nat_of_int(32-CARRY_BITS));
                div_rem(new_chunk,pow_nat(2,nat_of_int(32-CARRY_BITS)));
                assert new_chunk < pow_nat(2,N32);
                assert pow_nat(2,nat_of_int(32-CARRY_BITS))
                        *(new_chunk>>(32-CARRY_BITS))
                    <= new_chunk;
                assert pow_nat(2,nat_of_int(32-CARRY_BITS))
                        *(new_chunk>>(32-CARRY_BITS))
                    < pow_nat(2,N32);
                assert pow_nat(2,N32)
                    == pow_nat(2,nat_of_int(32-CARRY_BITS))
                        *pow_nat(2,nat_of_int(CARRY_BITS));
                my_inv_mul_strict_mono_r(
                    pow_nat(2,nat_of_int(32-CARRY_BITS)),
                    (new_chunk>>(32-CARRY_BITS)),
                    pow_nat(2,nat_of_int(CARRY_BITS)));
            } @*/
            /*@ int orig_carry = carry; @*/
            *(&i->chunks[0]+chunk_i) =
                new_chunk&((1U<<(32-CARRY_BITS))-1U);
            carry = new_chunk>>(32-CARRY_BITS);

            /*@ int next_carry = carry; @*/
            /*@ assert *(&i->chunks[0]+chunk_i)|-> ?final_chunk; @*/
            /*@ assert i->chunks[chunk_i+1..N_INTS] |-> ?rest_chunks; @*/

            /*@ {
                if(poly_eval(rest_chunks,CHUNK_BASE) < 0) {
                    int neg_x = poly_eval_neg(rest_chunks,CHUNK_BASE);
                    forall_elim(rest_chunks,
                        (bounded)(0,pow_nat(2,
                            nat_of_int(32-carry_bits))-1),
                        neg_x);
                    assert false;
                }
                assert poly_eval(blk_chunks,CHUNK_BASE) + orig_carry
                    == orig_chunk + orig_carry
                    + CHUNK_BASE*poly_eval(rest_chunks,CHUNK_BASE);

                assert poly_eval(blk_chunks,CHUNK_BASE) + orig_carry
                    == final_chunk + carry*CHUNK_BASE
                    + CHUNK_BASE*poly_eval(rest_chunks,CHUNK_BASE);
                assert poly_eval(blk_chunks,CHUNK_BASE) + orig_carry
                    == final_chunk
                    + CHUNK_BASE*(poly_eval(rest_chunks,CHUNK_BASE)
                                 +carry);
            } @*/

            /*@ recursive_call(); @*/

            /*@ {
                assert old_i->chunks[old_chunk_i+1..N_INTS] |-> ?new_rest_chunks;
                assert  poly_eval(new_rest_chunks,CHUNK_BASE)
                        + carry
                            *pow_nat(CHUNK_BASE,
                                nat_of_int(length(new_rest_chunks)))
                    == poly_eval(rest_chunks,CHUNK_BASE) + next_carry;
                mul_3var(carry,CHUNK_BASE,
                    pow_nat(CHUNK_BASE,
                        nat_of_int(length(new_rest_chunks))));
                assert poly_eval(cons(final_chunk,new_rest_chunks),CHUNK_BASE)
                        + carry*pow_nat(CHUNK_BASE,
                                    nat_of_int(length(new_rest_chunks)+1))
                    == final_chunk
                        + CHUNK_BASE*poly_eval(new_rest_chunks,CHUNK_BASE) 
                        + CHUNK_BASE
                            *(carry*pow_nat(CHUNK_BASE,
                                nat_of_int(length(new_rest_chunks))))
                        ;
                assert poly_eval(cons(final_chunk,new_rest_chunks),CHUNK_BASE)
                        + carry*pow_nat(CHUNK_BASE,
                                    nat_of_int(length(new_rest_chunks)+1))
                    == final_chunk
                        + CHUNK_BASE
                            *(poly_eval(new_rest_chunks,CHUNK_BASE) 
                             +carry*pow_nat(CHUNK_BASE,
                                nat_of_int(length(new_rest_chunks))))
                        ;
                assert poly_eval(cons(final_chunk,new_rest_chunks),CHUNK_BASE)
                        + carry*pow_nat(CHUNK_BASE,
                                    nat_of_int(length(new_rest_chunks)+1))
                    == final_chunk
                        + CHUNK_BASE
                            *(poly_eval(rest_chunks,CHUNK_BASE) 
                             + next_carry)
                        ;
                assert poly_eval(cons(final_chunk,new_rest_chunks),CHUNK_BASE)
                        + carry*pow_nat(CHUNK_BASE,
                                    nat_of_int(length(new_rest_chunks)+1))
                    == final_chunk
                        + CHUNK_BASE
                            *(poly_eval(rest_chunks,CHUNK_BASE) 
                             + next_carry)
                        ;
                assert poly_eval(cons(final_chunk,new_rest_chunks),CHUNK_BASE)
                        + carry*pow_nat(CHUNK_BASE,
                                nat_of_int(length(blk_chunks)))
                    == poly_eval(blk_chunks,CHUNK_BASE) + orig_carry
                        ;
            } @*/
        }

        /*@ assert i->chunks[..N_INTS] |-> ?final_chunks; @*/
        if(carry && i == last) {
            /*@ if(extra_blocks == 0) {
                note(!!poly_is_zero(loop_chunks));
                poly_eval_zero(loop_chunks,CHUNK_BASE);
                assert poly_eval(loop_chunks,CHUNK_BASE) == 0;
                assert poly_eval(final_chunks,CHUNK_BASE)
                        + carry
                            *pow_nat(CHUNK_BASE,
                                nat_of_int(length(final_chunks)))
                    == poly_eval(loop_chunks,CHUNK_BASE) + block_carry;
                assert poly_eval(final_chunks,CHUNK_BASE) >= 0;
                assert poly_eval(final_chunks,CHUNK_BASE)
                        + carry
                            *pow_nat(CHUNK_BASE,
                                nat_of_int(length(final_chunks)))
                    == block_carry;
                assert carry
                            *pow_nat(CHUNK_BASE,
                                nat_of_int(length(final_chunks)))
                    <= block_carry;
                assert carry
                            *pow_nat(CHUNK_BASE,
                                nat_of_int(length(final_chunks)))
                    <  pow_nat(2,nat_of_int(CARRY_BITS));
                my_mul_mono_l(1,carry,
                    pow_nat(CHUNK_BASE,
                            nat_of_int(length(final_chunks))));
                assert pow_nat(CHUNK_BASE, nat_of_int(N_INTS))
                    <  pow_nat(2,nat_of_int(CARRY_BITS));
                pow_times2(2,nat_of_int(CHUNK_BITS), N_INTS);
                assert pow_nat(2, nat_of_int(CHUNK_BITS*N_INTS))
                    <  pow_nat(2,nat_of_int(CARRY_BITS));
                pow_monotonic(2,nat_of_int(CARRY_BITS),
                    nat_of_int(CHUNK_BITS*N_INTS));
                assert false;
            } @*/

            last = new_block();
            i->next = last;
            last->prev = i;
            /*@ --extra_blocks; @*/
            /*@ assert last != i; @*/
        }
        i = i->next;

        /*@ big_int_block* next_i = i; @*/
        /*@ int next_carry = carry; @*/
        /*@ list<int> loop_rest_chunks; @*/

        /*@ if(i) {
            assert bi_block(i,last,_,0,_,?rest_blocks);
            loop_rest_chunks = rest_blocks;
        } @*/

        /*@ recursive_call(); @*/

        /*@ {
            assert bi_block(next_i, last,old_i, 0, ?rest_ptrs,
                        ?new_chunks)
                &*&  !!forall(new_chunks,
                        (bounded)(0,pow_nat(2,nat_of_int(32-CARRY_BITS))-1))
                &*&  poly_eval(new_chunks,CHUNK_BASE)
                    == poly_eval(loop_rest_chunks,CHUNK_BASE) + next_carry
                &*&  carry == 0;
            forall_append(final_chunks,new_chunks,
                (bounded)(0,pow_nat(2,nat_of_int(32-CARRY_BITS))-1));
            if(mem(old_i,rest_ptrs)) {
                close bi_block(old_i,old_i,_,_,{old_i},_);
                bi_block_disjoint(old_i,next_i);
                assert false;
            }
            assert poly_eval(append(final_chunks,new_chunks),
                    CHUNK_BASE)
                == poly_eval(final_chunks,CHUNK_BASE)
                + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                    *poly_eval(new_chunks,CHUNK_BASE);
            note_eq( poly_eval(append(final_chunks,new_chunks),
                    CHUNK_BASE)
                ,  poly_eval(final_chunks,CHUNK_BASE)
                + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                    *(poly_eval(loop_rest_chunks,CHUNK_BASE)
                     +next_carry));
            assert poly_eval(append(final_chunks,new_chunks),
                    CHUNK_BASE)
                == poly_eval(final_chunks,CHUNK_BASE)
                + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))*next_carry
                + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                    *poly_eval(loop_rest_chunks,CHUNK_BASE);
            assert poly_eval(append(final_chunks,new_chunks),
                    CHUNK_BASE)
                == poly_eval(i_blk_chunks,CHUNK_BASE) + old_carry
                + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                    *poly_eval(loop_rest_chunks,CHUNK_BASE);
            assert poly_eval(append(final_chunks,new_chunks),
                    CHUNK_BASE)
                == poly_eval(loop_chunks,CHUNK_BASE) + old_carry;
        } @*/
    } while(i);
    p->last = last;
}

void big_int_pluseq(big_int* a,const big_int* b)
    /*@ requires     bi_big_int(a,?a_carry,?av)
            &*&  [?f]bi_big_int(b,?b_carry,?bv)
            &*&  a_carry > 0 &*& b_carry > 0
            ; @*/
    /*@ ensures      bi_big_int(a,min_of(a_carry,b_carry)-1,av+bv)
            &*&  [ f]bi_big_int(b, b_carry, bv); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    /*@ open bi_big_int(a,_,av); @*/
    /*@ open bi_big_int(b,_,bv); @*/
    big_int_block* a_i    = a->first;
    big_int_block* a_last = a->last;
    big_int_block* b_i    = b->first;
    big_int_block* b_last = b->last;
    if(!a->is_pos || !b->is_pos) abort(); // TODO

    /*@ { assert      bi_block(a_i,a_last,?a_prev,0,_,?a_chunks)
              &*&  [f]bi_block(b_i,b_last,?b_prev,0,?bptrs,?b_chunks)
              &*&  av == poly_eval(a_chunks,CHUNK_BASE)
              &*&  bv == poly_eval(b_chunks,CHUNK_BASE)
              ;
    } @*/

    while(true)
        /*@ requires    bi_block(a_i,a_last,?a_prev,0,_,?a_chunks)
                &*&  [f]bi_block(b_i,b_last,?b_prev,0,?bptrs,?b_chunks)
                &*&  !!forall(a_chunks,
                        (bounded)(0,
                            pow_nat(2,nat_of_int(32-a_carry))-1))
                &*&  !!forall(b_chunks,
                        (bounded)(0,
                            pow_nat(2,nat_of_int(32-b_carry))-1))
                ; @*/
        /*@ ensures     bi_block(old_a_i,a_last, a_prev,0,_,?new_chunks)
                &*&  [f]bi_block(old_b_i,b_last,b_prev,0,bptrs,b_chunks)
                &*&  !!forall(new_chunks,
                        (bounded)(0,
                            pow_nat(2,
                                nat_of_int(32-min_of(a_carry,b_carry)+1))-1))
                &*&  poly_eval(new_chunks,CHUNK_BASE)
                    == poly_eval(a_chunks,CHUNK_BASE)
                     + poly_eval(b_chunks,CHUNK_BASE)
                ; @*/
        /*@ decreases length(b_chunks); @*/
    {
        size_t chunk_i;

        /*@ open bi_block(a_i,_,_,_,_,_); @*/
        /*@ open bi_block(b_i,_,_,_,_,_); @*/
        /*@ assert  a_i->chunks[..N_INTS] |-> ?a_i_chunks
                &*& a_i->next |-> ?a_i_next; @*/
        /*@ assert  [f]b_i->chunks[..N_INTS] |-> ?b_i_chunks
                &*& [f]b_i->next |-> ?b_i_next; @*/
        /*@ {
            if(a_i != a_last) {
                assert bi_block(a_i_next,a_last,_,_,_,?rest_chunks);
                forall_append_exact(a_i_chunks,rest_chunks,
                        (bounded)(0,
                            pow_nat(2,nat_of_int(32-a_carry))-1));
            }
            if(b_i != b_last) {
                assert [f]bi_block(b_i_next,b_last,_,_,_,?rest_chunks);
                forall_append_exact(b_i_chunks,rest_chunks,
                        (bounded)(0,
                            pow_nat(2,nat_of_int(32-b_carry))-1));
            }
        } @*/

        for(chunk_i=0;chunk_i < N_INTS; ++chunk_i)
            /*@ requires    a_i->chunks[chunk_i..N_INTS]
                                |-> ?a_i_loop_chunks
                    &*&  [f]b_i->chunks[chunk_i..N_INTS]
                                |-> ?b_i_loop_chunks
                    &*&  !!forall(a_i_loop_chunks,
                            (bounded)(0,
                                pow_nat(2,nat_of_int(32-a_carry))-1))
                    &*&  !!forall(b_i_loop_chunks,
                            (bounded)(0,
                                pow_nat(2,nat_of_int(32-b_carry))-1))
                    ; @*/
            /*@ ensures     a_i->chunks[old_chunk_i..N_INTS]
                                |-> ?new_chunks
                    &*&  [f]b_i->chunks[old_chunk_i..N_INTS]
                                |->  b_i_loop_chunks
                    &*&  !!forall(new_chunks,
                            (bounded)(0,
                                pow_nat(2,
                                    nat_of_int(32-min_of(a_carry,b_carry)+1))-1))
                    &*&  poly_eval(new_chunks,CHUNK_BASE)
                        == poly_eval(a_i_loop_chunks,CHUNK_BASE)
                        + poly_eval(b_i_loop_chunks,CHUNK_BASE)
                    ; @*/
            /*@ decreases length(b_i_loop_chunks); @*/
        {
            /*@ {
                open uints(&a_i->chunks[0]+chunk_i,_,_);
                u_integer_limits(&a_i->chunks[0]+chunk_i);
                open [f]uints(&b_i->chunks[0]+chunk_i,_,_);
                assert *(&a_i->chunks[0]+chunk_i) |-> ?a_chunk;
                assert [f]*(&b_i->chunks[0]+chunk_i) |-> ?b_chunk;
                pow_soft_monotonic(2,
                    nat_of_int(32-a_carry),
                    nat_of_int(32-min_of(a_carry,b_carry)));
                pow_soft_monotonic(2,
                    nat_of_int(32-b_carry),
                    nat_of_int(32-min_of(a_carry,b_carry)));
                assert a_chunk >= 0;
                assert b_chunk >= 0;
                assert a_chunk
                    <  pow_nat(2,
                        nat_of_int(32-min_of(a_carry,b_carry)));
                assert b_chunk
                    <  pow_nat(2,
                        nat_of_int(32-min_of(a_carry,b_carry)));
                assert a_chunk+b_chunk
                    <  2*pow_nat(2,
                        nat_of_int(32-min_of(a_carry,b_carry)));
                note_eq(
                    succ(nat_of_int(32-min_of(a_carry,b_carry))),
                    nat_of_int(33-min_of(a_carry,b_carry)));
                assert a_chunk+b_chunk
                    <  pow_nat(2,
                        nat_of_int(33-min_of(a_carry,b_carry)));
                pow_soft_monotonic(2,
                    nat_of_int(33-min_of(a_carry,b_carry)),
                    nat_of_int(32));
            } @*/

            *(&a_i->chunks[0]+chunk_i) += b_i->chunks[chunk_i];
        }
        if(b_i == b_last) {
            /*@ {
                assert  a_i->chunks[..N_INTS] |-> ?new_a_i_chunks
                    &*& a_i->next |-> ?next;
                if(next) {
                    assert bi_block(next,a_last,_,_,_,?rest_chunks);

                    if(!forall(append(new_a_i_chunks,rest_chunks),
                        (bounded)(0,
                            pow_nat(2,
                                nat_of_int(32-min_of(a_carry,b_carry)+1))-1))) {
                        int cx = not_forall(append(new_a_i_chunks,rest_chunks),
                            (bounded)(0,
                                pow_nat(2,
                                    nat_of_int(32-min_of(a_carry,b_carry)+1))-1));
                        assert 32-min_of(a_carry,b_carry)
                            >= 32-a_carry;
                        assert int_of_nat(nat_of_int(32-a_carry))
                            == 32-a_carry;
                        int_of_nat_of_int(32-min_of(a_carry,b_carry)+1);
                        pow_soft_monotonic(2,nat_of_int(32-a_carry),
                            nat_of_int(32-min_of(a_carry,b_carry)+1));
                        if(mem(cx,new_a_i_chunks)) {
                            forall_elim(new_a_i_chunks,
                                (bounded)(0, pow_nat(2,
                                    nat_of_int(32-min_of(a_carry,b_carry)+1))-1),
                                    cx);
                            assert false;
                        } else { assert !!mem(cx,rest_chunks);
                            forall_elim(rest_chunks,
                                (bounded)(0, pow_nat(2,
                                    nat_of_int(32-a_carry))-1),
                                    cx);
                            assert false;
                        }
                        assert false;
                    }
                }
            } @*/
            break;
        }
        if(a_i == a_last) {
            a_last = new_block();
            a_i->next = a_last;
            a_last->prev = a_i;

            /*@ close bi_block(a_last,a_last,_,_,_,_); @*/
        }
        a_i = a_i->next;
        b_i = b_i->next;

        /*@ big_int_block* next_a_i = a_i; @*/ 
        /*@ big_int_block* next_b_i = b_i; @*/ 
        /*@ list<int> rest_a_chunks = nil; @*/
        /*@ list<int> rest_b_chunks = nil; @*/

        /*@ {
            if(a_i) {
                assert bi_block(a_i,_,_,_,_,?a_rest);
                rest_a_chunks = a_rest;
            }
            if(b_i) {
                assert [f]bi_block(b_i,_,_,_,_,?b_rest);
                rest_b_chunks = b_rest;
            }
        } @*/

        /*@ recursive_call(); @*/

        /*@ {
            assert old_a_i->chunks[..N_INTS] |-> ?old_a_i_chunks;
            assert bi_block(next_a_i,_,_,_,?next_a_ptrs,?next_a_chunks);
            if(mem(old_a_i,next_a_ptrs)) {
                close bi_block(old_a_i,old_a_i,_,_,{old_a_i},_);
                bi_block_disjoint(old_a_i,next_a_i);
                assert false;
            }

            forall_append(old_a_i_chunks,next_a_chunks,
                (bounded)(0,
                    pow_nat(2,
                        nat_of_int(32-min_of(a_carry,b_carry)+1))-1)
                );

            assert poly_eval(old_a_i_chunks,CHUNK_BASE)
                == poly_eval(a_i_chunks,CHUNK_BASE)
                 + poly_eval(b_i_chunks,CHUNK_BASE);
            assert poly_eval(next_a_chunks,CHUNK_BASE)
                == poly_eval(rest_a_chunks,CHUNK_BASE)
                 + poly_eval(rest_b_chunks,CHUNK_BASE);

            assert poly_eval(append(old_a_i_chunks,next_a_chunks),
                    CHUNK_BASE)
                == poly_eval(old_a_i_chunks,CHUNK_BASE)
                 + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                    *poly_eval(next_a_chunks,CHUNK_BASE);
            note_eq( poly_eval(append(old_a_i_chunks,next_a_chunks),
                    CHUNK_BASE)
                ,  poly_eval(a_i_chunks,CHUNK_BASE)
                 + poly_eval(b_i_chunks,CHUNK_BASE)
                 + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                    *(poly_eval(rest_a_chunks,CHUNK_BASE)
                     + poly_eval(rest_b_chunks,CHUNK_BASE)));

            assert poly_eval(append(old_a_i_chunks,next_a_chunks),
                    CHUNK_BASE)
                == poly_eval(a_i_chunks,CHUNK_BASE)
                 + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                    *poly_eval(rest_a_chunks,CHUNK_BASE)
                 + poly_eval(b_i_chunks,CHUNK_BASE)
                 + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                     *poly_eval(rest_b_chunks,CHUNK_BASE);

            assert poly_eval(append(old_a_i_chunks,next_a_chunks),
                    CHUNK_BASE)
                == poly_eval(a_chunks,CHUNK_BASE)
                 + poly_eval(b_chunks,CHUNK_BASE);

        } @*/
    }
    a->last = a_last;
}

