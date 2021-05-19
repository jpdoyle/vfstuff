#include "bi_big_int.h"
/*@ #include "../lists.gh" @*/
/*@ #include <arrays.gh> @*/

#if 1
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() assume(false);
#endif

#ifndef __FILE__
#ifndef INLINE
#define INLINE
#endif
#else
#ifndef INLINE
#define INLINE static inline
#endif
#endif

/*@ 
lemma_auto(reverse(l))
void reverse_1<t>(list<t> l)
    requires length(l) <= 1;
    ensures  reverse(l) == l;
{ TRIVIAL_LIST2(l) }
@*/

big_int* big_int_from_hex(const char* s)
    /*@ requires [?f]string(s,?cs)
            &*&  (safe_head(cs) == some('-')
            ?    base_n(hex_chars(),reverse(tail(cs)),_,?val)
            &*& ensures [ f]string(s, cs)
                   &*&  bi_big_int(result, CARRY_BITS, false, -val)
            :    base_n(hex_chars(),reverse(cs),_,?val)
            &*& ensures [ f]string(s, cs)
                   &*&  bi_big_int(result, CARRY_BITS, false,  val)
            ); @*/
    /*@ ensures  true; @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    size_t s_i;
    size_t block_i;
    size_t block_shift;
    big_int* ret = malloc(sizeof(big_int));
    if(!ret) { abort(); }

    ret->is_pos = true;
    /*@ string_limits(s); @*/
    /*@ open string(s,_); @*/
    /*@ assert [f]*s |-> ?c0; @*/
    if(*s == '-') {
        ++s;
        ret->is_pos = false;
    }
    ret->last = new_block();
    ret->first = ret->last;

    /*@ close exists<list<int32_t> >(nil); @*/
    /*@ close exists<int32_t>(0); @*/
    /*@ int32_t ghost_block_shift = 0; @*/
    /*@ note_eq(nat_of_int(N_INTS),succ(nat_of_int(N_INTS-1))); @*/

    for(s_i = strlen(s),block_i = 0,block_shift = 0; s_i > 0; --s_i)
        /*@ requires [?lf]ret->first |-> ?first
                &*&  [f]s[..s_i] |-> ?loop_cs
                &*&  ret->last |-> ?last
                &*&  bi_block(last,last,?l_prev,0,_,?chunks)
                &*&  let(pow_nat(2,nat_of_int(CHUNK_BITS))-1, ?upper)
                &*&  !!forall(chunks, (bounded)(0,upper))
                &*&  !!forall(chunks, (bounded)(-upper,upper))

                &*&  base_n(hex_chars(),reverse(loop_cs),_,?loop_val)

                &*&  exists<list<int32_t> >(?pref)
                &*&  exists<int32_t>(?blk)
                &*&  let(repeat(0,nat_of_int(N_INTS-1-block_i)),?suff)
                &*&  chunks
                    == append(pref, cons(blk,suff))
                &*&  block_i == length(pref)
                &*&  0 <= block_shift &*& block_shift <= CHUNK_BITS-4
                &*&  block_shift == ghost_block_shift*4
                &*&  blk >= 0
                &*&  blk < pow_nat(2,nat_of_int(block_shift))
                ; @*/
        /*@ ensures  [ lf]ret->first |->  first
                &*&  [f]s[..old_s_i] |-> loop_cs
                &*&  ret->last |-> ?new_last
                &*&  bi_block(last,new_last,l_prev,0,_,
                        ?new_chunks)
                &*&  !!forall(new_chunks, (bounded)(0,upper))
                &*&  !!forall(new_chunks, (bounded)(-upper,upper))
                &*&  poly_eval(new_chunks,
                        CHUNK_BASE)
                    == poly_eval(chunks,
                            CHUNK_BASE)
                        + loop_val*pow_nat(2,
                            nat_of_int(old_block_i*CHUNK_BITS
                                +old_block_shift))
                ; @*/
        /*@ decreases s_i; @*/
    {
        /*@ char c; @*/
        /*@ {
            switch(reverse(loop_cs)) {
            case nil: assert false;
            case cons(rc,rcs):
                c = rc;
                assert reverse(reverse(loop_cs))
                    == reverse(append(cons(rc,nil),rcs));
                assert loop_cs == append(reverse(rcs),cons(rc,nil));
                assert length(reverse(rcs)) == s_i-1;
                chars_split_as(s,reverse(rcs),cons(c,nil));
                open [f]chars(s+s_i-1,_,_);
            }
            open exists(blk);
            open bi_block(last,_,_,_,_,_);
            open base_n(_,reverse(loop_cs),_,_);
        } @*/
        /*@ assert [f]s[s_i-1] |->  c; @*/
        /*@ assert [f]s[..s_i-1] |-> ?cs_pref; @*/
        /*@ assert base_n(hex_chars(), reverse(cs_pref), _,
                          ?rest_val); @*/
        /*@ {
            assert loop_val == index_of(c,hex_chars()) + 16*rest_val;

            assert loop_cs == append(cs_pref,cons(c,nil));
            assert reverse(loop_cs) == cons(c,reverse(cs_pref));
            assert !!mem(c,hex_chars());
        } @*/
        /* @ int32_t *block = &ret->last->chunks[0]; @*/
        /* @ ints_split(block,block_i); @*/
        int32_t nib = nib_of_hex(s[s_i-1]);
        /*@ close [f]chars(s+s_i-1,1,_); @*/

        /*@ {
            assert N_INTS-block_i >= 1;
            assert block_i >= 0;
            assert nib >= 0 &*& nib < pow_nat(2,nat_of_int(4));
            pow_plus(2,nat_of_int(4),block_shift);
            assert pow_nat(2,nat_of_int(4))
                    *pow_nat(2,nat_of_int(block_shift))
                == pow_nat(2,nat_of_int(4+block_shift));
            my_mul_mono_r(nib,0,pow_nat(2,nat_of_int(block_shift)));
            assert nib*pow_nat(2,nat_of_int(block_shift)) >= 0;
            my_mul_strict_mono_l(nib,pow_nat(2,nat_of_int(4)),pow_nat(2,nat_of_int(block_shift)));
            assert nib*pow_nat(2,nat_of_int(block_shift))
                <  pow_nat(2,nat_of_int(4+block_shift));

            shiftleft_def(nib,nat_of_int(block_shift));
            bitor_no_overlap(nib,blk,nat_of_int(block_shift));

            ints_split_as(&last->chunks[0],pref,cons(blk,suff));
            ints_limits2((&last->chunks[0]) + block_i);
            assert (&last->chunks[0])[block_i] |-> blk;
            pow_monotonic(2,nat_of_int(4+block_shift),
                N32);
            pow_monotonic(2,nat_of_int(4+block_shift),
                nat_of_int(30));
            pow_monotonic(2,nat_of_int(block_shift),
                nat_of_int(30));

            note( blk+nib*pow_nat(2,nat_of_int(block_shift))
                >= 0);

            //assert blk+nib*pow_nat(2,nat_of_int(block_shift))
            //    <= pow_nat(2,nat_of_int(30)) +
            //    pow_nat(2,nat_of_int(30));
            //assert blk+nib*pow_nat(2,nat_of_int(block_shift))
            //    <= pow_nat(2,nat_of_int(31));

            assert blk < pow_nat(2,nat_of_int(block_shift));
            assert nib < pow_nat(2,nat_of_int(4));
            note( nib <= pow_nat(2,nat_of_int(4))-1);
            my_mul_mono_l(nib, pow_nat(2,nat_of_int(4))-1,
                pow_nat(2,nat_of_int(4)));
            assert nib*pow_nat(2,nat_of_int(block_shift))
                <= pow_nat(2,nat_of_int(block_shift+4))
                - pow_nat(2,nat_of_int(block_shift));

            pow_soft_monotonic(2,nat_of_int(block_shift+4),nat_of_int(CHUNK_BITS));
            assert pow_nat(2,nat_of_int(block_shift+4))
                <= pow_nat(2,nat_of_int(CHUNK_BITS));

            assert blk+nib*pow_nat(2,nat_of_int(block_shift))
                < pow_nat(2,nat_of_int(CHUNK_BITS));

            assert blk+nib*pow_nat(2,nat_of_int(block_shift))
                <  pow_nat(2,N32);
            assert (nib<<block_shift)
                == nib*pow_nat(2,nat_of_int(block_shift));
            bitor_commutes(blk,(nib<<block_shift));
            assert (blk|(nib<<block_shift))
                == ((nib<<block_shift)|blk);
            assert (blk|(nib<<block_shift))
                == ((nib*pow_nat(2,nat_of_int(block_shift)))|blk);
            assert (blk|(nib<<block_shift))
                == blk+nib*pow_nat(2,nat_of_int(block_shift));
            note( (blk|(nib<<block_shift)) >= 0);
            close exists<int32_t>(blk|(nib<<block_shift));
        } @*/

        *(&ret->last->chunks[0]+block_i) |= (nib<<block_shift);
        /*@ close ints(&last->chunks[0]+block_i,N_INTS-block_i,_); @*/
        /*@ ints_join(&last->chunks[0]); @*/
        /*@ assert last->chunks[..N_INTS] |-> ?next_chunks; @*/

        /*@ {
            assert next_chunks
                == append(pref,cons(blk|(nib<<block_shift),suff));

            if(!forall(next_chunks,
                (bounded)(0, upper))) {
                int32_t cx = not_forall(next_chunks,
                    (bounded)(0,upper));
                if(mem(cx,pref) || mem(cx,suff)) {
                    forall_elim(chunks,
                        (bounded)(0,upper),
                        cx);
                }
                assert false;
            }
            assert !!forall(next_chunks, (bounded)(0,upper));
            if(!forall(next_chunks, (bounded)(-upper, upper))) {
                int32_t cx = not_forall(next_chunks,
                    (bounded)(-upper,upper));
                forall_elim(next_chunks,
                        (bounded)(0,upper),
                        cx);
                assert false;
            }

            assert poly_eval(next_chunks,CHUNK_BASE)
                == poly_eval(pref,CHUNK_BASE)
                +  pow_nat(CHUNK_BASE,nat_of_int(block_i))
                    *poly_eval(cons(blk|(nib<<block_shift),suff),
                        CHUNK_BASE);

            assert !!poly_is_zero(suff);

            assert poly_eval(suff,CHUNK_BASE)
                == poly_eval(minimize(suff),CHUNK_BASE);

            assert poly_eval(suff,CHUNK_BASE)
                == poly_eval(nil,CHUNK_BASE);

            assert poly_eval(suff,CHUNK_BASE) == 0;

            assert poly_eval(next_chunks,CHUNK_BASE)
                == poly_eval(pref,CHUNK_BASE)
                +  pow_nat(CHUNK_BASE,nat_of_int(block_i))
                    *(blk|(nib<<block_shift));

            pow_times2(2,nat_of_int(CHUNK_BITS),block_i);
            mul_commutes(CHUNK_BITS,block_i);

            assert poly_eval(next_chunks,CHUNK_BASE)
                == poly_eval(pref,CHUNK_BASE)
                +  pow_nat(2,nat_of_int(block_i*CHUNK_BITS))
                    *(blk|(nib<<block_shift));

            note_eq( poly_eval(next_chunks,CHUNK_BASE)
                ,  poly_eval(pref,CHUNK_BASE)
                +  pow_nat(2,nat_of_int(block_i*CHUNK_BITS))
                    *(blk+(nib*pow_nat(2,nat_of_int(block_shift)))));

            assert poly_eval(next_chunks,CHUNK_BASE)
                == poly_eval(pref,CHUNK_BASE)
                +  pow_nat(2,nat_of_int(block_i*CHUNK_BITS))*blk
                +  pow_nat(2,nat_of_int(block_i*CHUNK_BITS))
                    *(nib*pow_nat(2,nat_of_int(block_shift)));

            assert poly_eval(next_chunks,CHUNK_BASE)
                == poly_eval(pref,CHUNK_BASE)
                + pow_nat(2,nat_of_int(block_i*CHUNK_BITS))
                    *poly_eval(cons(blk,suff),CHUNK_BASE)
                +  pow_nat(2,nat_of_int(block_i*CHUNK_BITS))
                    *(nib*pow_nat(2,nat_of_int(block_shift)));

            mul_3var(pow_nat(2,nat_of_int(block_i*CHUNK_BITS)),
                    nib,pow_nat(2,nat_of_int(block_shift)));
            pow_plus(2,nat_of_int(block_i*CHUNK_BITS),block_shift);

            assert poly_eval(next_chunks,CHUNK_BASE)
                == poly_eval(chunks,CHUNK_BASE)
                +  pow_nat(2,nat_of_int(block_i*CHUNK_BITS))
                    *(nib*pow_nat(2,nat_of_int(block_shift)));

            assert poly_eval(next_chunks,CHUNK_BASE)
                == poly_eval(chunks,CHUNK_BASE)
                +  pow_nat(2,nat_of_int(block_i*CHUNK_BITS+block_shift))
                    *nib;

            assert poly_eval(next_chunks, CHUNK_BASE)
                == poly_eval(chunks, CHUNK_BASE)
                    + nib*pow_nat(2,
                        nat_of_int(block_i*CHUNK_BITS
                            +block_shift));
            note_eq(loop_val , nib + 16*rest_val);
        } @*/

        block_shift += 4;
        /*@ ghost_block_shift += 1; @*/
        /*@ if(block_shift > CHUNK_BITS-4 && block_shift != CHUNK_BITS) {
            assert block_shift - 4 < CHUNK_BITS-4;
            assert block_shift > CHUNK_BITS-4;
            int x = block_shift - CHUNK_BITS+4;
            note( x > 0);
            note( x < 4);
            assert 4*(CHUNK_BITS/4) == CHUNK_BITS;
            assert x
                == 4*ghost_block_shift - 4*(CHUNK_BITS/4)+4;
            assert x
                == 4*(ghost_block_shift - (CHUNK_BITS/4)+1);
            div_rem(x,4);
            division_unique(x,4,
                ghost_block_shift - (CHUNK_BITS/4)+1,0);
            division_unique(2,4,0,2);
            division_unique(3,4,0,3);
                 if(x <= 0) { assert false; }
            else if(x <= 1) { division_unique(x,4,0,1); }
            else if(x <= 2) { division_unique(x,4,0,2); }
            else if(x <= 3) { division_unique(x,4,0,3); }
            //else if(x <= 4) { assert false; }
            assert false;
        } @*/


        /*@ big_int_block* fresh_block = 0; @*/
        /*@ bool fresh_chunk = false; @*/
        if(block_shift == (size_t)CHUNK_BITS) {
            /*@ open exists<int32_t>(?v); @*/
            /*@ {
                fresh_chunk = true;
                close exists<int32_t>(0);
                open exists(pref);
            } @*/
            ++block_i;
            block_shift = 0;
            /*@ ghost_block_shift = 0; @*/
            if(block_i == N_INTS) {
                block_i = 0;
                ret->last->next = new_block();
                ret->last->next->prev = ret->last;
                ret->last = ret->last->next;
                /*@ {
                    assert ret->last |-> ?next;
                    fresh_block = next;
                    close bi_block(next,next,last,_,_,_);
                    close exists<list<int32_t> >(nil);
                } @*/
            } else { /*@ {
                cons_head_tail(suff);
                close exists(append(pref,cons(v,nil)));
                append_assoc(pref,cons(v,nil),suff);
                assert append(pref,cons(v,
                              cons(0,tail(suff))))
                    == next_chunks;
                assert append(append(pref,cons(v,nil)),
                              cons(0,tail(suff)))
                    == next_chunks;
                assert append(append(pref,cons(v,nil)),
                              cons(0,repeat(0,
                                nat_of_int(N_INTS-1-block_i))))
                    == next_chunks;
            } @*/ }
        }
        /*@ close bi_block(last,last,l_prev,_,_,_); @*/
        /*@ int next_block_i = block_i; @*/
        /*@ int next_block_shift = block_shift; @*/

        /*@ recursive_call(); @*/
        /*@ {
            chars_join(s);
            if(fresh_block) {
                assert old_block_shift == CHUNK_BITS-4;
                assert old_block_i == N_INTS-1;
                assert next_block_shift == 0;
                assert next_block_i == 0;

                bi_block_disjoint(last,fresh_block);
                assert bi_block(last,last,_,fresh_block,_,
                    next_chunks);
                assert bi_block(fresh_block,_,last,0,_,
                    ?rest_chunks);
                assert !!forall(next_chunks,
                    (bounded)(0,upper));
                assert !!forall(rest_chunks,
                    (bounded)(0,upper));
                forall_append(next_chunks,rest_chunks,
                    (bounded)(0,upper));
                forall_append(next_chunks,rest_chunks,
                    (bounded)(-upper,upper));
                bi_block_extend(last);
                assert poly_eval(rest_chunks, CHUNK_BASE)
                    == rest_val*pow_nat(2,
                            nat_of_int(next_block_i*CHUNK_BITS
                                +next_block_shift));
                assert poly_eval(rest_chunks, CHUNK_BASE)
                    == rest_val*pow_nat(2, nat_of_int(0));
                note_eq( poly_eval(rest_chunks, CHUNK_BASE)
                    ,  rest_val);

                assert poly_eval(append(next_chunks,rest_chunks),
                        CHUNK_BASE)
                    == poly_eval(next_chunks, CHUNK_BASE)
                        + rest_val*pow_nat(CHUNK_BASE,
                            nat_of_int(N_INTS));

                assert poly_eval(append(next_chunks,rest_chunks),
                        CHUNK_BASE)
                    == poly_eval(next_chunks, CHUNK_BASE)
                        + rest_val*pow_nat(pow_nat(2,nat_of_int(CHUNK_BITS)),
                            nat_of_int(N_INTS));

                pow_times2(2,nat_of_int(CHUNK_BITS),N_INTS);

                assert poly_eval(append(next_chunks,rest_chunks),
                        CHUNK_BASE)
                    == poly_eval(next_chunks, CHUNK_BASE)
                        + rest_val*pow_nat(2,
                            nat_of_int(N_INTS*CHUNK_BITS));

                assert poly_eval(append(next_chunks,rest_chunks),
                        CHUNK_BASE)
                    == poly_eval(chunks, CHUNK_BASE)
                        + nib*pow_nat(2,
                            nat_of_int(old_block_i*CHUNK_BITS
                                +old_block_shift))
                        + rest_val*pow_nat(2,
                            nat_of_int(N_INTS*CHUNK_BITS));

                assert poly_eval(append(next_chunks,rest_chunks),
                        CHUNK_BASE)
                    == poly_eval(chunks, CHUNK_BASE)
                        + nib*pow_nat(2,
                            nat_of_int((N_INTS-1)*CHUNK_BITS
                                +(CHUNK_BITS-4)))
                        + rest_val*pow_nat(2,
                            nat_of_int(N_INTS*CHUNK_BITS));

                assert poly_eval(append(next_chunks,rest_chunks),
                        CHUNK_BASE)
                    == poly_eval(chunks, CHUNK_BASE)
                        + nib*pow_nat(2,
                            nat_of_int((N_INTS-1)*CHUNK_BITS
                                +(CHUNK_BITS-4)))
                        + rest_val
                            *(pow_nat(2,
                                nat_of_int((N_INTS-1)*CHUNK_BITS
                                    +(CHUNK_BITS-4)))
                                *pow_nat(2, nat_of_int(4)));

                mul_commutes(nib,pow_nat(2,
                            nat_of_int((N_INTS-1)*CHUNK_BITS
                                +(CHUNK_BITS-4))));
                mul_3var(rest_val,
                    pow_nat(2,
                        nat_of_int((N_INTS-1)*CHUNK_BITS
                            +(CHUNK_BITS-4))),
                    pow_nat(2, nat_of_int(4)));

                note_eq( poly_eval(append(next_chunks,rest_chunks),
                        CHUNK_BASE)
                    ,  poly_eval(chunks, CHUNK_BASE)
                        + pow_nat(2,
                            nat_of_int((N_INTS-1)*CHUNK_BITS
                                +(CHUNK_BITS-4)))
                            *(nib + rest_val*pow_nat(2,
                                    nat_of_int(4))));
                note_eq(pow_nat(2, nat_of_int(4)), 16);
                note_eq(nib + rest_val*pow_nat(2,
                            nat_of_int(4)), loop_val);

                assert poly_eval(append(next_chunks,rest_chunks),
                        CHUNK_BASE)
                    == poly_eval(chunks, CHUNK_BASE)
                        + pow_nat(2,
                            nat_of_int((N_INTS-1)*CHUNK_BITS
                                +(CHUNK_BITS-4)))
                            *(loop_val);

                assert poly_eval(append(next_chunks,rest_chunks),
                        CHUNK_BASE)
                    == poly_eval(chunks, CHUNK_BASE)
                        + loop_val*pow_nat(2,
                            nat_of_int((N_INTS-1)*CHUNK_BITS
                                +(CHUNK_BITS-4)));

            } else {
                assert ret->last |-> ?new_last;
                assert bi_block(last,new_last,l_prev,0,_,
                    ?new_chunks);

                if(fresh_chunk) {
                    assert  poly_eval(new_chunks,
                            CHUNK_BASE)
                        == poly_eval(next_chunks,
                                CHUNK_BASE)
                            + rest_val*pow_nat(2,
                                nat_of_int((old_block_i+1)*CHUNK_BITS));
                    assert  poly_eval(new_chunks,
                            CHUNK_BASE)
                        == poly_eval(chunks, CHUNK_BASE)
                            + nib*pow_nat(2,
                                nat_of_int(old_block_i*CHUNK_BITS
                                    +old_block_shift))
                            + rest_val*pow_nat(2,
                                nat_of_int((old_block_i+1)*CHUNK_BITS));
                    assert  poly_eval(new_chunks,
                            CHUNK_BASE)
                        == poly_eval(chunks, CHUNK_BASE)
                            + nib*pow_nat(2,
                                nat_of_int(old_block_i*CHUNK_BITS
                                    +old_block_shift))
                            + rest_val*pow_nat(2,
                                nat_of_int(old_block_i*CHUNK_BITS
                                            + CHUNK_BITS));
                } else {
                    assert  poly_eval(new_chunks,
                            CHUNK_BASE)
                        == poly_eval(next_chunks,
                                CHUNK_BASE)
                            + rest_val*pow_nat(2,
                                nat_of_int(old_block_i*CHUNK_BITS
                                    + old_block_shift + 4));
                }
                assert  poly_eval(new_chunks,
                        CHUNK_BASE)
                    == poly_eval(chunks, CHUNK_BASE)
                        + nib*pow_nat(2,
                            nat_of_int(old_block_i*CHUNK_BITS
                                +old_block_shift))
                        + rest_val*pow_nat(2,
                            nat_of_int(old_block_i*CHUNK_BITS
                                        + old_block_shift+4));
                pow_plus(2,nat_of_int(4),
                    old_block_i*CHUNK_BITS +old_block_shift);
                assert  poly_eval(new_chunks,
                        CHUNK_BASE)
                    == poly_eval(chunks, CHUNK_BASE)
                        + nib*pow_nat(2,
                            nat_of_int(old_block_i*CHUNK_BITS
                                +old_block_shift))
                        + rest_val*(pow_nat(2,nat_of_int(4))
                            *pow_nat(2,nat_of_int(old_block_i*CHUNK_BITS
                                    + old_block_shift)));
                mul_assoc(rest_val,pow_nat(2,nat_of_int(4)),
                    pow_nat(2,nat_of_int(old_block_i*CHUNK_BITS
                                + old_block_shift)));
                assert  poly_eval(new_chunks,
                        CHUNK_BASE)
                    == poly_eval(chunks, CHUNK_BASE)
                        + (nib+16*rest_val)*pow_nat(2,
                            nat_of_int(old_block_i*CHUNK_BITS
                                +old_block_shift));
                note_eq((nib+16*rest_val)*pow_nat(2,
                            nat_of_int(old_block_i*CHUNK_BITS
                                +old_block_shift)),
                        loop_val*pow_nat(2,
                            nat_of_int(old_block_i*CHUNK_BITS
                                +old_block_shift)));

                assert  poly_eval(new_chunks,
                        CHUNK_BASE)
                    == poly_eval(chunks, CHUNK_BASE)
                        + loop_val*pow_nat(2,
                            nat_of_int(old_block_i*CHUNK_BITS
                                +old_block_shift));
                assert poly_eval(next_chunks, CHUNK_BASE)
                    == poly_eval(chunks, CHUNK_BASE)
                        + nib*pow_nat(2,
                            nat_of_int(old_block_i*CHUNK_BITS
                                +old_block_shift));
            }
        } @*/
    }

    return ret;
}


