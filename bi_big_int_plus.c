#include "bi_big_int.h"
#include "bitops.h"

/*@ #define N30 (nat_predecessor(N31))
  @*/

#if 1
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() assume(false);
#endif

INLINE big_int_block*
bi_block_reduce(big_int_block* first, big_int_block* last,
        bool flip_sign, int32_t* final_carry)
    /*@ requires bi_block(first, last,?bprev, 0, _,
                    ?chunks)
            &*&  !!forall(chunks,
                    (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1))
            &*&  *final_carry |-> ?upper_carry
            &*&  abs(upper_carry) < pow_nat(2,nat_of_int(CARRY_BITS))
            &*&  let(flip_sign
                    ? -poly_eval(append(chunks,{upper_carry}),CHUNK_BASE)
                    :  poly_eval(append(chunks,{upper_carry}),CHUNK_BASE),
                    ?target_val)
            ; @*/
    /*@ ensures  bi_block(first, result,bprev, 0, _,
                    ?new_chunks)
            &*&  *final_carry |-> ?last_carry
            &*&  abs(last_carry) < abs(upper_carry)+pow_nat(2,nat_of_int(CARRY_BITS))
            &*&  !!forall(new_chunks,
                (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1))
            &*&  !!forall(new_chunks, (bounded)(0,CHUNK_BASE-1))
            &*&  !!forall(new_chunks, (bounded)(-CHUNK_BASE+1,CHUNK_BASE-1))
            &*&  poly_eval(new_chunks,CHUNK_BASE) >= 0
            &*&  last_carry <= 0
            &*&  let(poly_eval(append(new_chunks,{last_carry}),
                              CHUNK_BASE),
                    ?new_val)
            &*&  new_val == target_val
            ; @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    /*@ note(CHUNK_BASE > 1); @*/
    big_int_block* i = first;
    int32_t carry = 0;

    /*@ nat len_bits = npow2(length(chunks)); @*/
    /*@ int extra_blocks = 1; @*/

    do
        /*@ requires bi_block(i, last,?loop_bprev, 0, _,
                        ?loop_chunks)
                &*&  *final_carry |-> ?loop_upper_carry
                &*&  !!forall(loop_chunks,
                        (bounded)(-pow_nat(2,N30)+1,
                                  pow_nat(2,N30)-1))
                &*&  abs(loop_upper_carry) < pow_nat(2,nat_of_int(CARRY_BITS))
                &*&  length(loop_chunks) < pow_nat(2,len_bits)
                &*&  let(flip_sign
                        ? -poly_eval(append(loop_chunks,{loop_upper_carry}),
                                     CHUNK_BASE)
                            + carry
                        :  poly_eval(append(loop_chunks,{loop_upper_carry}),
                                     CHUNK_BASE)
                            + carry,
                        ?loop_target_val)
                &*&  extra_blocks == 0
                ?    !!poly_is_zero(loop_chunks)
                &*&  loop_upper_carry == 0
                &*&  abs(carry) < 2*pow_nat(2,nat_of_int(CARRY_BITS))
                :    extra_blocks == 1
                &*& loop_upper_carry == upper_carry
                &*&  abs(carry) < pow_nat(2,nat_of_int(CARRY_BITS))
                ; @*/
        /*@ ensures  bi_block(old_i, last,loop_bprev, 0, _,
                        ?new_chunks)
                &*&  *final_carry |-> carry
                &*&  carry <= 0
                &*&  abs(carry) < abs(loop_upper_carry) + pow_nat(2,nat_of_int(CARRY_BITS))
                &*&  let(CHUNK_BASE-1,?upper)
                &*&  !!forall(new_chunks, (bounded)(-upper,upper))
                &*&  !!forall(new_chunks,
                    (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1))
                &*&  !!forall(new_chunks, (bounded)(0,upper))
                &*&  poly_eval(new_chunks,CHUNK_BASE) >= 0

                &*&  let(poly_eval(append(new_chunks,{carry}),CHUNK_BASE),
                        ?new_val)
                &*&  new_val == loop_target_val
                ; @*/
        /*@ decreases extra_blocks + length(loop_chunks); @*/
    {
        size_t chunk_i;
        /*@ int block_carry = carry; @*/
        /*@ open bi_block(_,_,_,_,_,_); @*/
        /*@ assert i->chunks[..N_INTS] |-> ?i_blk_chunks; @*/
        /* @ if(!flip_sign) ALREADY_PROVEN() @*/
        /*@ if(i != last) {
            assert bi_block(_,_,_,_,_,?rest_chunks);
            forall_append_exact(i_blk_chunks,rest_chunks,
                (bounded)(-pow_nat(2,N30)+1,
                          pow_nat(2,N30)-1));
        } @*/

        for(chunk_i = 0; chunk_i <  N_INTS; ++chunk_i)
            /*@ requires i->chunks[chunk_i..N_INTS] |-> ?blk_chunks
                    &*&  !!forall(blk_chunks,
                            (bounded)(-pow_nat(2,N30)+1,
                                  pow_nat(2,N30)-1))
                    &*&  let(flip_sign
                            ? -poly_eval(blk_chunks,CHUNK_BASE) + carry
                            :  poly_eval(blk_chunks,CHUNK_BASE) + carry,
                            ?blk_target_val)
                    &*&  abs(carry) < 2*pow_nat(2,nat_of_int(CARRY_BITS))
                    &*&  chunk_i == 0 || abs(carry) < pow_nat(2,nat_of_int(CARRY_BITS))
                    &*&  chunk_i >= 0 &*& chunk_i <= N_INTS
                    ; @*/
            /*@ ensures  i->chunks[old_chunk_i..N_INTS] |-> ?new_blk_chunks
                    &*&  let(CHUNK_BASE-1,?upper)
                    &*&  !!forall(new_blk_chunks, (bounded)(-upper,upper))
                    &*&  !!forall(new_blk_chunks, (bounded)(0,upper))
                    &*&  !!forall(new_blk_chunks,
                            (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1))
                    &*&  abs(carry) < pow_nat(2,nat_of_int(CARRY_BITS))
                    &*&  poly_eval(new_blk_chunks,CHUNK_BASE) >= 0
                    &*&  flip_sign
                    ?    poly_eval(append(new_blk_chunks,{carry}),CHUNK_BASE)
                        == -poly_eval(blk_chunks,CHUNK_BASE) + old_carry
                    :    poly_eval(append(new_blk_chunks,{carry}),CHUNK_BASE)
                        == poly_eval(blk_chunks,CHUNK_BASE) + old_carry
                    ; @*/
            /*@ decreases length(blk_chunks); @*/
        {
            /* @ ALREADY_PROVEN() @*/
            /*@ open ints(&i->chunks[0]+chunk_i,_,_); @*/
            /*@ integer_limits(&i->chunks[0]+chunk_i); @*/
            int32_t new_chunk = *(&i->chunks[0]+chunk_i);
            if(flip_sign) new_chunk = -new_chunk;
            /*@ int orig_chunk = new_chunk; @*/
            /*@ {
                assert abs(new_chunk) < pow_nat(2,N30);
                assert abs(carry) < 2*pow_nat(2,nat_of_int(CARRY_BITS));
                pow_monotonic(2,succ(nat_of_int(CARRY_BITS)), N30);
                pow_soft_monotonic(2, N30, N31);
                assert abs(carry) < pow_nat(2,N30);
                assert abs(new_chunk+carry) < 2*pow_nat(2,N30);
                assert abs(new_chunk+carry) < pow_nat(2,succ(N30));
                assert abs(new_chunk+carry) < pow_nat(2,nat_of_int(31));
            } @*/
            new_chunk += carry;
            /*@ int orig_carry = carry; @*/
            /*@ ashr_euclid(new_chunk,nat_of_int(CHUNK_BITS)); @*/
            carry = ASHR(new_chunk,CHUNK_BITS);
            /*@ open euclid_div_sol(_,_,carry,?chunk_mod); @*/
            /*@ {
                shiftleft_def(1,nat_of_int(CHUNK_BITS));
                assert carry*(1<<CHUNK_BITS) + chunk_mod == new_chunk;
                assert chunk_mod < pow_nat(2,nat_of_int(CHUNK_BITS));
                assert abs(new_chunk) < pow_nat(2,N30)
                    + 2*pow_nat(2,nat_of_int(CARRY_BITS));
                assert abs(new_chunk-chunk_mod) < pow_nat(2,N30)
                    + 2*pow_nat(2,nat_of_int(CARRY_BITS))
                    + pow_nat(2,nat_of_int(CHUNK_BITS));
                assert abs(new_chunk-chunk_mod) < pow_nat(2,N31);
            } @*/
            new_chunk -= (carry*(1<<CHUNK_BITS));
            *(&i->chunks[0]+chunk_i) = new_chunk;

            /*@ int next_carry = carry; @*/
            /*@ assert *(&i->chunks[0]+chunk_i)|-> ?final_chunk; @*/
            /*@ assert i->chunks[chunk_i+1..N_INTS] |-> ?rest_chunks; @*/

            /*@ if(flip_sign) {
                assert -poly_eval(blk_chunks,CHUNK_BASE) + orig_carry
                    == orig_chunk + orig_carry
                    + -(CHUNK_BASE*poly_eval(rest_chunks,CHUNK_BASE));

                assert -poly_eval(blk_chunks,CHUNK_BASE) + orig_carry
                    == final_chunk + carry*CHUNK_BASE
                    + -(CHUNK_BASE*poly_eval(rest_chunks,CHUNK_BASE));
                assert -poly_eval(blk_chunks,CHUNK_BASE) + orig_carry
                    == final_chunk
                    + CHUNK_BASE*(-poly_eval(rest_chunks,CHUNK_BASE)
                                 +carry);
            } else {
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
                if(!flip_sign) {
                    assert  poly_eval(append(new_rest_chunks,{carry}),CHUNK_BASE)
                        == poly_eval(rest_chunks,CHUNK_BASE) + next_carry;
                } else {
                    assert  poly_eval(append(new_rest_chunks,{carry}),CHUNK_BASE)
                        == -poly_eval(rest_chunks,CHUNK_BASE) + next_carry;
                }
                mul_3var(carry,CHUNK_BASE,
                    pow_nat(CHUNK_BASE,
                        nat_of_int(length(new_rest_chunks))));
            } @*/
        }

        /*@ assert i->chunks[..N_INTS] |-> ?final_chunks; @*/
        /*@ int offset = 0; @*/
        /*@ int final_chunk_carry = carry; @*/
        if(i == last) {
            int32_t outer_carry = (flip_sign ? -(*final_carry)
                                             : *final_carry);
            /*@ offset = outer_carry; @*/
            carry += outer_carry;
            *final_carry = 0;

            /*@ if(flip_sign) {
                assert loop_target_val
                    == -poly_eval(
                            append(loop_chunks,{loop_upper_carry}),
                            CHUNK_BASE)
                    +   block_carry;
                assert loop_target_val
                    == -poly_eval(loop_chunks, CHUNK_BASE)
                    -  loop_upper_carry*pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                    +   block_carry;
                assert loop_target_val
                    == poly_eval(
                            append(final_chunks,{final_chunk_carry}),
                            CHUNK_BASE)
                    -  loop_upper_carry*pow_nat(CHUNK_BASE,nat_of_int(N_INTS));
                assert loop_target_val
                    == poly_eval(final_chunks, CHUNK_BASE)
                    +  final_chunk_carry*pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                    -  loop_upper_carry*pow_nat(CHUNK_BASE,nat_of_int(N_INTS));
                note_eq( loop_target_val
                    ,  poly_eval(final_chunks, CHUNK_BASE)
                    +  (final_chunk_carry-loop_upper_carry)
                        *pow_nat(CHUNK_BASE,nat_of_int(N_INTS)));
                assert loop_target_val
                    == poly_eval(
                            append(final_chunks,{final_chunk_carry-loop_upper_carry}),
                            CHUNK_BASE);
            } else {
                assert loop_target_val
                    == poly_eval(
                            append(loop_chunks,{loop_upper_carry}),
                            CHUNK_BASE)
                    +   block_carry;
                note_eq( loop_target_val
                    ,  poly_eval(final_chunks, CHUNK_BASE)
                    +  (final_chunk_carry+loop_upper_carry)
                        *pow_nat(CHUNK_BASE,nat_of_int(N_INTS)));
                assert loop_target_val
                    == poly_eval(
                            append(final_chunks,{final_chunk_carry+loop_upper_carry}),
                            CHUNK_BASE);

            } @*/

            if(carry > 0) {

                /* @ if(flip_sign && carry < 0) {
                    assert poly_eval(append(final_chunks,{carry}),
                            CHUNK_BASE)
                        ==  -poly_eval(loop_chunks,CHUNK_BASE) + block_carry;
                    neg_most_sig(final_chunks,CHUNK_BASE,{carry});
                    assert poly_eval(append(final_chunks,{carry}),
                            CHUNK_BASE)
                        <  (carry+1)*pow_nat(CHUNK_BASE,
                                    nat_of_int(length(final_chunks)));
                    my_mul_mono_l(carry+1,-1,
                        pow_nat(CHUNK_BASE,
                                    nat_of_int(length(final_chunks))));
                    assert -poly_eval(loop_chunks,CHUNK_BASE) + block_carry
                        <  -pow_nat(CHUNK_BASE,
                                    nat_of_int(length(final_chunks)));
                    assert -poly_eval(loop_chunks,CHUNK_BASE) + block_carry
                        <  -pow_nat(CHUNK_BASE, nat_of_int(N_INTS));
                    poly_eval_bounded_pos(loop_chunks,CHUNK_BASE-1,CHUNK_BASE);
                    assert -poly_eval(loop_chunks,CHUNK_BASE) + block_carry
                        >= -pow_nat(CHUNK_BASE,nat_of_int(N_INTS)) + 1
                        + block_carry;
                    assert false;
                } @*/

                /*@ if(extra_blocks == 0) {
                    note(!!poly_is_zero(loop_chunks));
                    poly_eval_zero(loop_chunks,CHUNK_BASE);
                    assert poly_eval(loop_chunks,CHUNK_BASE) == 0;
                    assert poly_eval(final_chunks,CHUNK_BASE)
                            + carry
                                *pow_nat(CHUNK_BASE,
                                    nat_of_int(length(final_chunks)))
                        == poly_eval(loop_chunks,CHUNK_BASE) + block_carry;
                    assert poly_eval(final_chunks,CHUNK_BASE)
                            + carry
                                *pow_nat(CHUNK_BASE,
                                    nat_of_int(length(final_chunks)))
                        == block_carry;
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
                        <  2*pow_nat(2,nat_of_int(CARRY_BITS));
                    if(carry > 0) {
                        my_mul_mono_l(1,carry,
                            pow_nat(CHUNK_BASE,
                                    nat_of_int(length(final_chunks))));
                        assert pow_nat(CHUNK_BASE, nat_of_int(N_INTS))
                            <  2*pow_nat(2,nat_of_int(CARRY_BITS));
                        pow_times2(2,nat_of_int(CHUNK_BITS), N_INTS);
                        assert pow_nat(2, nat_of_int(CHUNK_BITS*N_INTS))
                            <  2*pow_nat(2,nat_of_int(CARRY_BITS));
                        pow_monotonic(2,succ(nat_of_int(CARRY_BITS)),
                            nat_of_int(CHUNK_BITS*N_INTS));
                    } else {
                        neg_most_sig(final_chunks,CHUNK_BASE,{carry});
                        assert carry <= -2;

                        assert poly_eval(append(final_chunks,{carry}),CHUNK_BASE)
                            <  (carry+1)*pow_nat(CHUNK_BASE,nat_of_int(N_INTS));
                        my_mul_mono_l(carry+1,-1,
                            pow_nat(CHUNK_BASE,nat_of_int(N_INTS)));
                        assert poly_eval(append(final_chunks,{carry}),CHUNK_BASE)
                            <  -pow_nat(CHUNK_BASE,nat_of_int(N_INTS));
                        assert poly_eval(append(final_chunks,{carry}),CHUNK_BASE)
                            == block_carry;
                        assert block_carry
                            <  -pow_nat(CHUNK_BASE,nat_of_int(N_INTS));
                        if(block_carry >= 0) assert false;
                        assert abs_of(block_carry) == -block_carry;
                        assert -block_carry
                            >  pow_nat(CHUNK_BASE,nat_of_int(N_INTS));
                        assert pow_nat(2,nat_of_int(CARRY_BITS))
                            >  pow_nat(CHUNK_BASE,nat_of_int(N_INTS));

                        pow_times2(2,nat_of_int(CHUNK_BITS), N_INTS);
                        assert pow_nat(2, nat_of_int(CHUNK_BITS*N_INTS))
                            <  pow_nat(2,nat_of_int(CARRY_BITS));
                        pow_monotonic(2,nat_of_int(CARRY_BITS),
                            nat_of_int(CHUNK_BITS*N_INTS));
                    }
                    assert false;
                } @*/

                last = new_block();
                i->next = last;
                last->prev = i;
                /*@ --extra_blocks; @*/
                /*@ assert last != i; @*/
            } else {
                *final_carry = carry;
            }
        }
        i = i->next;

        /*@ big_int_block* next_i = i; @*/
        /*@ assert *final_carry |-> ?next_upper_carry; @*/
        /*@ int next_carry = carry; @*/
        /*@ int next_extras = extra_blocks; @*/
        /*@ list<int> loop_rest_chunks; @*/

        /*@ if(i) {
            assert bi_block(i,last,_,0,_,?rest_blocks);
            loop_rest_chunks = rest_blocks;

            //if(flip_sign) {
            //    assert loop_target_val
            //        == -poly_eval(append(i_blk_chunks,loop_rest_chunks),CHUNK_BASE)
            //        +  block_carry;
            //    assert loop_target_val
            //        == -poly_eval(i_blk_chunks,CHUNK_BASE)
            //        +  -poly_eval(loop_rest_chunks,CHUNK_BASE)
            //            *pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
            //        +  block_carry;
            //    assert loop_target_val
            //        == poly_eval(append(final_chunks,{carry}),CHUNK_BASE)
            //        +  -poly_eval(loop_rest_chunks,CHUNK_BASE)
            //            *pow_nat(CHUNK_BASE,nat_of_int(N_INTS));
            //    assert loop_target_val
            //        == poly_eval(final_chunks,CHUNK_BASE)
            //        +  (carry-poly_eval(loop_rest_chunks,CHUNK_BASE))
            //            *pow_nat(CHUNK_BASE,nat_of_int(N_INTS));
            //    if(carry-poly_eval(loop_rest_chunks,CHUNK_BASE) < 0) {
            //        pow_monotonic(2,N2,nat_of_int(CHUNK_BITS));
            //        poly_eval_bounded_pos(final_chunks,CHUNK_BASE-1,CHUNK_BASE);
            //        my_mul_mono_l(carry-poly_eval(loop_rest_chunks,CHUNK_BASE),
            //            -1, pow_nat(CHUNK_BASE,nat_of_int(N_INTS)));
            //        assert false;
            //    }
            //}
        }@*/

        /*@ recursive_call(); @*/

        /*@ {
            assert bi_block(next_i, last,old_i, 0, ?rest_ptrs,
                        ?new_chunks);
            //assert length(new_chunks) + extra_blocks
            //    == length(loop_rest_chunks) + next_extras;
            //assert length(append(final_chunks,new_chunks)) + extra_blocks
            //    == length(i_blk_chunks) + length(new_chunks) +
            //    extra_blocks;
            //assert length(append(final_chunks,new_chunks)) + extra_blocks
            //    == length(i_blk_chunks) + length(loop_rest_chunks) + next_extras;
            //assert length(append(final_chunks,new_chunks)) + extra_blocks
            //    == length(loop_chunks) + old_extra_blocks;
            forall_append(final_chunks,new_chunks,
                (bounded)(0,pow_nat(2,nat_of_int(31-CARRY_BITS))-1));
            forall_append(final_chunks,new_chunks,
                (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1));
            forall_append(final_chunks,new_chunks,
            (bounded)(0,CHUNK_BASE-1));
            forall_append(final_chunks,new_chunks,
            (bounded)(-CHUNK_BASE+1,CHUNK_BASE-1));
            if(mem(old_i,rest_ptrs)) {
                close bi_block(old_i,old_i,_,_,{old_i},_);
                bi_block_disjoint(old_i,next_i);
                assert false;
            }
            append_assoc(i_blk_chunks,loop_rest_chunks,{next_upper_carry});
            if(!flip_sign) {
                assert poly_eval(append(final_chunks,new_chunks),
                        CHUNK_BASE)
                    == poly_eval(final_chunks,CHUNK_BASE)
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                        *poly_eval(new_chunks,CHUNK_BASE);
                note_eq( poly_eval(
                        append(final_chunks,append(new_chunks,{carry})),
                        CHUNK_BASE)
                    ,  poly_eval(final_chunks,CHUNK_BASE)
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                        *(poly_eval(append(loop_rest_chunks,{next_upper_carry}),
                                    CHUNK_BASE)
                        +next_carry));
                assert poly_eval(
                        append(final_chunks,append(new_chunks,{carry})),
                        CHUNK_BASE)
                    == poly_eval(final_chunks,CHUNK_BASE)
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))*next_carry
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                        *poly_eval(append(loop_rest_chunks,{next_upper_carry}),
                                   CHUNK_BASE);
                assert poly_eval(
                        append(final_chunks,append(new_chunks,{carry})),
                        CHUNK_BASE)
                    == poly_eval(i_blk_chunks,CHUNK_BASE) + old_carry
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))*offset
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                        *poly_eval(append(loop_rest_chunks,{next_upper_carry}),
                                   CHUNK_BASE);
                assert poly_eval(
                        append(final_chunks,append(new_chunks,{carry})),
                        CHUNK_BASE)
                    == poly_eval(append(loop_chunks,{loop_upper_carry}),
                                 CHUNK_BASE) + old_carry;
            } else {
                assert poly_eval(append(final_chunks,new_chunks),
                        CHUNK_BASE)
                    == poly_eval(final_chunks,CHUNK_BASE)
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                        *poly_eval(new_chunks,CHUNK_BASE);
                note_eq( poly_eval(
                        append(final_chunks,append(new_chunks,{carry})),
                        CHUNK_BASE)
                    ,  poly_eval(final_chunks,CHUNK_BASE)
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                        *(-poly_eval(append(loop_rest_chunks,{next_upper_carry}),
                                    CHUNK_BASE)
                        +next_carry));
                assert poly_eval(
                        append(final_chunks,append(new_chunks,{carry})),
                        CHUNK_BASE)
                    == poly_eval(final_chunks,CHUNK_BASE)
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))*next_carry
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                        *(-poly_eval(append(loop_rest_chunks,{next_upper_carry}),
                                    CHUNK_BASE));
                note_eq( poly_eval(
                        append(final_chunks,append(new_chunks,{carry})),
                        CHUNK_BASE)
                    ,  -poly_eval(i_blk_chunks,CHUNK_BASE) + old_carry
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))*offset
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                        *-poly_eval(append(loop_rest_chunks,{next_upper_carry}),
                                    CHUNK_BASE));
                assert poly_eval(
                        append(final_chunks,append(new_chunks,{carry})),
                        CHUNK_BASE)
                    == -poly_eval(
                            append(loop_chunks,{loop_upper_carry}),
                            CHUNK_BASE)
                    + old_carry;
            }
            assert poly_eval(
                    append(final_chunks,append(new_chunks,{carry})),
                    CHUNK_BASE)
                == loop_target_val;

            append_assoc(final_chunks,new_chunks,{carry});
            assert poly_eval(
                    append(append(final_chunks,new_chunks),{carry}),
                    CHUNK_BASE)
                == loop_target_val;

            assert loop_target_val
                == poly_eval(final_chunks,CHUNK_BASE)
                + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                    *poly_eval(append(new_chunks,{carry}),CHUNK_BASE);
            assert poly_eval(final_chunks,CHUNK_BASE) >= 0;
            assert poly_eval(new_chunks, CHUNK_BASE)
                >= 0;
            my_mul_mono_l(1,
                    pow_nat(CHUNK_BASE,nat_of_int(N_INTS)),
                    poly_eval(new_chunks, CHUNK_BASE));
            assert poly_eval(append(final_chunks,new_chunks), CHUNK_BASE)
                >= 0;
        } @*/
    } while(i);

    return last;
}

void big_int_reduce(big_int* p)
    /*@ requires bi_big_int(p,?carry_bits,?underflow,?v)
            &*&  carry_bits >= 1; @*/
    /*@ ensures  bi_big_int(p,CARRY_BITS,false,v); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    int32_t carry_over = 0;

    /*@ open bi_big_int(_,_,_,_); @*/
    /*@ assert bi_block(_,_,0,0,_,?chunks); @*/
    /*@ if(!forall(chunks,
            (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1))) {
        int cx = not_forall(chunks,
            (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1));
        forall_elim(chunks,
            (bounded)(-pow_nat(2,nat_of_int(31-carry_bits))+1,
                      pow_nat(2,nat_of_int(31-carry_bits))-1),
            cx);
        pow_soft_monotonic(2,nat_of_int(31-carry_bits),N30);
        assert false;
    } @*/

    p->last = bi_block_reduce(p->first,p->last,false,&carry_over);
    if(carry_over < 0) {
        /*@ assert bi_block(_,_,0,0,_,?chunks1); @*/
        /*@ assert carry_over |-> ?carry1; @*/
        /*@ {
            assert poly_eval(chunks, CHUNK_BASE)
                == poly_eval(append(chunks1,{carry1}), CHUNK_BASE);
            neg_most_sig(chunks1,CHUNK_BASE,{carry1});
            assert poly_eval(chunks, CHUNK_BASE) < 0;
        } @*/
        p->last = bi_block_reduce(p->first,p->last,true,&carry_over);
        p->is_pos = !p->is_pos;
        /*@ assert bi_block(_,_,0,0,_,?chunks2); @*/
        /*@ assert carry_over |-> ?carry2; @*/
        /*@ {
            assert -poly_eval(append(chunks1,{carry1}), CHUNK_BASE)
                == poly_eval(append(chunks2,{carry2}), CHUNK_BASE);
            assert -poly_eval(chunks, CHUNK_BASE)
                == poly_eval(append(chunks2,{carry2}), CHUNK_BASE);
            if(carry2 < 0) {
                neg_most_sig(chunks2,CHUNK_BASE,{carry2});
                assert -poly_eval(chunks, CHUNK_BASE) < 0;
                assert false;
            }
            assert carry2 == 0;
        } @*/
    }
}

void big_int_pluseq(big_int* a,const big_int* b)
    /*@ requires [?af]bi_big_int(a,?a_carry, ?a_under,?av)
            &*&  [?bf]bi_big_int(b,?b_carry, ?b_under,?bv)
            &*&  a_carry > 1 &*& b_carry > 1
            &*&  a != b
            ?    af == 1 &*& bf > 0
            :    af + bf == 1 &*& af > 0 &*& bf > 0
            ; @*/
    /*@ ensures      bi_big_int(a,min_of(a_carry,b_carry)-1,
                        true, av+bv)
            &*&  a == b ? emp
            :    [ bf]bi_big_int(b, b_carry, b_under, bv); @*/
    /*@ terminates; @*/
{
    /* @ ALREADY_PROVEN() @*/
    /*@ bool doubling = (a == b); @*/

    /*@ open [bf]bi_big_int(b,_,_,bv); @*/
    /*@ open [af]bi_big_int(a,_,_,av); @*/
    big_int_block* a_i    = a->first;
    big_int_block* a_last = a->last;
    big_int_block* b_i    = b->first;
    big_int_block* b_last = b->last;
    bool subtract = (a->is_pos != b->is_pos);
    /*@ int result_carries = min_of(a_carry,b_carry)-1; @*/
    /*@ assert   let(pow_nat(2,nat_of_int(31-result_carries))-1,?upper)
    &*&   let(pow_nat(2,nat_of_int(31-a_carry))-1,?a_upper)
                &*&  let(-a_upper,?a_lower)
                &*&  let(pow_nat(2,nat_of_int(31-b_carry))-1,?b_upper)
                &*&  let(-b_upper,?b_lower)
            ; @*/

    /*@ { assert   [af]bi_block(a_i,a_last,?a_prev,0,_,?a_chunks)
              &*&  [bf]bi_block(b_i,b_last,?b_prev,0,?bptrs,?b_chunks)
              ;
        pow_monotonic(2,N2,nat_of_int(31-a_carry));
        pow_monotonic(2,N2,nat_of_int(31-b_carry));
        assert result_carries > 0;
        assert result_carries < a_carry;
        assert result_carries < b_carry;
        assert 31-result_carries > 31-a_carry;
        int_of_nat_of_int(31-result_carries);
        int_of_nat_of_int(31-a_carry);
        int_of_nat_of_int(31-b_carry);
        pow_monotonic(2,nat_of_int(31-a_carry),nat_of_int(31-result_carries));
        pow_soft_monotonic(2,nat_of_int(31-result_carries),N30);
        pow_monotonic(2,nat_of_int(31-b_carry),nat_of_int(31-result_carries));
        if(!forall(a_chunks, (bounded)(-upper,upper))) {
            int cx = not_forall(a_chunks, (bounded)(-upper,upper));
            forall_elim(a_chunks, (bounded)(-a_upper,a_upper),cx);
            assert false;
        }
        if(!forall(a_chunks, (bounded)(-upper,upper))) {
            int cx = not_forall(a_chunks, (bounded)(-upper,upper));
            forall_elim(a_chunks, (bounded)(a_lower,a_upper),cx);
            assert false;
        }
        if(!forall(a_chunks, (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1))) {
            int cx = not_forall(a_chunks, (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1));
            forall_elim(a_chunks, (bounded)(-a_upper,a_upper),cx);
            assert false;
        }
    } @*/

    while(true)
        /*@ requires [af]bi_block(a_i,a_last,?a_prev,0,_,?a_chunks)
                &*&  [bf]bi_block(b_i,b_last,?b_prev,0,?bptrs,?b_chunks)
                &*&  !doubling || (a_i == b_i)

                &*&  !!forall(a_chunks, (bounded)(-a_upper,a_upper))
                &*&  !!forall(a_chunks, (bounded)(a_lower,a_upper))
                &*&  !!forall(a_chunks, (bounded)(-upper,upper))
                &*&  !!forall(a_chunks,
                        (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1))

                &*&  !!forall(b_chunks, (bounded)(-b_upper,b_upper))
                &*&  !!forall(b_chunks, (bounded)(b_lower,b_upper))

                &*&  a_upper >= 4 &*& b_upper >= 4 &*& upper > a_upper
                &*&  upper > b_upper
                ; @*/
        /*@ ensures     bi_block(old_a_i,a_last, a_prev,0,_,?new_chunks)
                &*&  (doubling ? emp
                    : [bf]bi_block(old_b_i,b_last,b_prev,0,bptrs,b_chunks))

                &*&  !!forall(new_chunks, (bounded)(-upper,upper))
                &*&  !!forall(new_chunks,
                        (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1))
                &*&  subtract
                ?   poly_eval(new_chunks,CHUNK_BASE)
                    == poly_eval(a_chunks,CHUNK_BASE)
                    - poly_eval(b_chunks,CHUNK_BASE)
                :   poly_eval(new_chunks,CHUNK_BASE)
                    == poly_eval(a_chunks,CHUNK_BASE)
                    + poly_eval(b_chunks,CHUNK_BASE)
                ; @*/
        /*@ decreases length(b_chunks); @*/
    {
        size_t chunk_i;

        /*@ open [bf]bi_block(b_i,_,_,_,_,_); @*/
        /*@ open [af]bi_block(a_i,_,_,_,_,_); @*/
        /*@ assert  [af]a_i->chunks[..N_INTS] |-> ?a_i_chunks
                &*& [af]a_i->next |-> ?a_i_next; @*/
        /*@ assert  [bf]b_i->chunks[..N_INTS] |-> ?b_i_chunks
                &*& [bf]b_i->next |-> ?b_i_next; @*/
        /*@ {
            if(a_i != a_last) {
                assert [af]bi_block(a_i_next,a_last,_,_,_,?rest_chunks);
                forall_append(a_i_chunks, rest_chunks,
                    (bounded)(-a_upper,a_upper));
                forall_append(a_i_chunks, rest_chunks,
                    (bounded)(a_lower,a_upper));
                forall_append(a_i_chunks, rest_chunks,
                    (bounded)(-upper,upper));
                forall_append(a_i_chunks, rest_chunks,
                    (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1));
            }
            if(b_i != b_last) {
                assert [bf]bi_block(b_i_next,b_last,_,_,_,?rest_chunks);

                forall_append(b_i_chunks, rest_chunks,
                (bounded)(-b_upper,b_upper));
                forall_append(b_i_chunks, rest_chunks,
                (bounded)(b_lower,b_upper));
            }
        } @*/

        for(chunk_i=0;chunk_i < N_INTS; ++chunk_i)
            /*@ requires [af]a_i->chunks[chunk_i..N_INTS]
                                |-> ?a_i_loop_chunks
                    &*&  [bf]b_i->chunks[chunk_i..N_INTS]
                                |-> ?b_i_loop_chunks
                    &*&  !!forall(a_i_loop_chunks, (bounded)(-a_upper,a_upper))
                    &*&  !!forall(a_i_loop_chunks, (bounded)(a_lower,a_upper))
                    &*&  !!forall(a_i_loop_chunks, (bounded)(-upper,upper))

                    &*&  !!forall(b_i_loop_chunks, (bounded)(-b_upper,b_upper))
                    &*&  !!forall(b_i_loop_chunks, (bounded)(b_lower,b_upper))
                    ; @*/
            /*@ ensures     a_i->chunks[old_chunk_i..N_INTS]
                                |-> ?new_chunks
                    &*&  (doubling ? emp
                         : [bf]b_i->chunks[old_chunk_i..N_INTS]
                                |->  b_i_loop_chunks)
                    &*&  !!forall(new_chunks, (bounded)(-upper,upper))
                    &*&  !!forall(new_chunks,
                            (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1))
                    &*&  subtract
                    ?   poly_eval(new_chunks,CHUNK_BASE)
                        == poly_eval(a_i_loop_chunks,CHUNK_BASE)
                        - poly_eval(b_i_loop_chunks,CHUNK_BASE)
                    :   poly_eval(new_chunks,CHUNK_BASE)
                        == poly_eval(a_i_loop_chunks,CHUNK_BASE)
                        + poly_eval(b_i_loop_chunks,CHUNK_BASE)
                    ; @*/
            /*@ decreases length(b_i_loop_chunks); @*/
        {
            /*@ {
                open [bf]ints(&b_i->chunks[0]+chunk_i,_,_);
                open [af]ints(&a_i->chunks[0]+chunk_i,_,_);
                integer_limits(&a_i->chunks[0]+chunk_i);

                assert [af]*(&a_i->chunks[0]+chunk_i) |-> ?a_chunk;
                assert [bf]*(&b_i->chunks[0]+chunk_i) |-> ?b_chunk;
                pow_soft_monotonic(2,
                    nat_of_int(31-a_carry),
                    nat_of_int(31-(result_carries+1)));
                pow_soft_monotonic(2,
                    nat_of_int(31-b_carry),
                    nat_of_int(31-(result_carries+1)));
                note( a_chunk
                    <  pow_nat(2,
                        nat_of_int(31-(result_carries+1))));
                note( a_chunk
                    >  -pow_nat(2,
                        nat_of_int(31-(result_carries+1))));
                note( b_chunk
                    <  pow_nat(2,
                        nat_of_int(31-(result_carries+1))));
                note( b_chunk
                    > -pow_nat(2,
                        nat_of_int(31-(result_carries+1))));
                note_eq(
                    succ(nat_of_int(31-(result_carries+1))),
                    nat_of_int(31-result_carries));
                pow_soft_monotonic(2,
                    nat_of_int(31-result_carries),
                    nat_of_int(30));
                pow_soft_monotonic(2,
                    nat_of_int(31-result_carries),
                    nat_of_int(31));
                if(!subtract) {
                    note( a_chunk+b_chunk >  -upper);
                    note( a_chunk+b_chunk <   upper);
                    note(bounded(-upper,upper,a_chunk+b_chunk));
                    note(bounded(-(pow_nat(2,N30)-1),(pow_nat(2,N30)-1),a_chunk+b_chunk));
                } else {
                    note( a_chunk-b_chunk >  -upper);
                    note( a_chunk-b_chunk <   upper);
                    note(bounded(-upper,upper,a_chunk-b_chunk));
                    note(bounded(-(pow_nat(2,N30)-1),(pow_nat(2,N30)-1),a_chunk-b_chunk));
                }
            } @*/

            if(subtract) {
                *(&a_i->chunks[0]+chunk_i) -= b_i->chunks[chunk_i];
            } else {
                *(&a_i->chunks[0]+chunk_i) += b_i->chunks[chunk_i];
            }

        }
        if(b_i == b_last) {
            /*@ {
                assert  a_i->chunks[..N_INTS] |-> ?new_a_i_chunks
                    &*& a_i->next |-> ?next;
                if(next) {
                    assert bi_block(next,a_last,_,_,_,?rest_chunks);
                    forall_append(new_a_i_chunks,rest_chunks,
                    (bounded)(-upper,upper));
                    forall_append(new_a_i_chunks,rest_chunks,
                    (bounded)(-upper,upper));
                    forall_append(new_a_i_chunks,rest_chunks,
                    (bounded)(-(pow_nat(2,N30)-1),(pow_nat(2,N30)-1)));

                    //if(!forall(append(new_a_i_chunks,rest_chunks),
                    //    (bounded)(0,
                    //        pow_nat(2,
                    //            nat_of_int(32-min_of(a_carry,b_carry)+1))-1))) {
                    //    int cx = not_forall(append(new_a_i_chunks,rest_chunks),
                    //        (bounded)(0,
                    //            pow_nat(2,
                    //                nat_of_int(32-min_of(a_carry,b_carry)+1))-1));
                    //    assert 32-min_of(a_carry,b_carry)
                    //        >= 32-a_carry;
                    //    assert int_of_nat(nat_of_int(32-a_carry))
                    //        == 32-a_carry;
                    //    int_of_nat_of_int(32-min_of(a_carry,b_carry)+1);
                    //    pow_soft_monotonic(2,nat_of_int(32-a_carry),
                    //        nat_of_int(32-min_of(a_carry,b_carry)+1));
                    //    if(mem(cx,new_a_i_chunks)) {
                    //        forall_elim(new_a_i_chunks,
                    //            (bounded)(0, pow_nat(2,
                    //                nat_of_int(32-min_of(a_carry,b_carry)+1))-1),
                    //                cx);
                    //        assert false;
                    //    } else { assert !!mem(cx,rest_chunks);
                    //        forall_elim(rest_chunks,
                    //            (bounded)(0, pow_nat(2,
                    //                nat_of_int(32-a_carry))-1),
                    //                cx);
                    //        assert false;
                    //    }
                    //    assert false;
                    //}
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
                assert [af]bi_block(a_i,_,_,_,_,?a_rest);
                rest_a_chunks = a_rest;
            }
            if(b_i) {
                assert [bf]bi_block(b_i,_,_,_,_,?b_rest);
                rest_b_chunks = b_rest;
            }
        } @*/

        /*@ recursive_call(); @*/

        /*@ {
            assert [af]old_a_i->chunks[..N_INTS] |-> ?old_a_i_chunks;
            assert [af]bi_block(next_a_i,_,_,_,?next_a_ptrs,?next_a_chunks);
            if(mem(old_a_i,next_a_ptrs)) {
                close [af]bi_block(old_a_i,old_a_i,_,_,{old_a_i},_);
                bi_block_disjoint(old_a_i,next_a_i);
                assert false;
            }

            assert !!forall(old_a_i_chunks,
                (bounded)(-upper,upper));
            assert !!forall(next_a_chunks,
                (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1));
            assert !!forall(old_a_i_chunks,
                (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1));
            assert !!forall(next_a_chunks,
                (bounded)(-upper,upper));
            forall_append(old_a_i_chunks,next_a_chunks,
                (bounded)(-upper,upper));
            forall_append(old_a_i_chunks,next_a_chunks,
                (bounded)(-pow_nat(2,N30)+1, pow_nat(2,N30)-1));

            if(!subtract) {
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
            } else {
                assert poly_eval(old_a_i_chunks,CHUNK_BASE)
                    == poly_eval(a_i_chunks,CHUNK_BASE)
                    - poly_eval(b_i_chunks,CHUNK_BASE);
                assert poly_eval(next_a_chunks,CHUNK_BASE)
                    == poly_eval(rest_a_chunks,CHUNK_BASE)
                    - poly_eval(rest_b_chunks,CHUNK_BASE);

                assert poly_eval(append(old_a_i_chunks,next_a_chunks),
                        CHUNK_BASE)
                    == poly_eval(old_a_i_chunks,CHUNK_BASE)
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                        *poly_eval(next_a_chunks,CHUNK_BASE);
                note_eq( poly_eval(append(old_a_i_chunks,next_a_chunks),
                        CHUNK_BASE)
                    ,  poly_eval(a_i_chunks,CHUNK_BASE)
                    - poly_eval(b_i_chunks,CHUNK_BASE)
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                        *(poly_eval(rest_a_chunks,CHUNK_BASE)
                        - poly_eval(rest_b_chunks,CHUNK_BASE)));

                assert poly_eval(append(old_a_i_chunks,next_a_chunks),
                        CHUNK_BASE)
                    == poly_eval(a_i_chunks,CHUNK_BASE)
                    + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                        *poly_eval(rest_a_chunks,CHUNK_BASE)
                    - poly_eval(b_i_chunks,CHUNK_BASE)
                    - pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                        *poly_eval(rest_b_chunks,CHUNK_BASE);

                assert poly_eval(append(old_a_i_chunks,next_a_chunks),
                        CHUNK_BASE)
                    == poly_eval(a_chunks,CHUNK_BASE)
                    - poly_eval(b_chunks,CHUNK_BASE);
            }

        } @*/
    }
    a->last = a_last;
}

