#include <string.h>
#include "bigint.h"
#include "b64.h"
/*@ #include "util.gh" @*/
/*@ #include "poly.gh" @*/

// fill out a 64-byte cache line
#define N_INTS 12
// number of bits to reserve for carries
#define CARRY_BITS 4
#define CHUNK_BITS ((int)32-(int)CARRY_BITS)
#define CHUNK_BASE (pow_nat(2,nat_of_int(CHUNK_BITS)))

typedef struct big_int_block {
    struct big_int_block* prev;
    struct big_int_block* next;
    uint32_t chunks[N_INTS];
} big_int_block;

typedef big_int_block* big_int_block_ptr;

typedef struct big_int {
    struct big_int_block *first;
    struct big_int_block *last;
    bool is_pos;
} big_int;

/*@

predicate bi_block(big_int_block* first,
                   big_int_block* last;
                   big_int_block* first_prev,
                   big_int_block* last_next,
                   list<big_int_block*> ptrs,
                   list<uint32_t> chunks) =
        malloc_block_big_int_block(first)
        //struct_big_int_block_padding(first)
    &*& first > 0
    &*& first->next   |-> ?next
    &*& first->prev   |-> first_prev
    &*& first->chunks[..N_INTS] |-> ?my_chunks
    &*& first == last
    ?       last_next == next &*& chunks == my_chunks
        &*& ptrs == cons(first,nil)
    :       bi_block(next, last, first, last_next, ?more_ptrs, ?more_chunks)
        &*& !mem(first,more_ptrs)
        &*& chunks == append(my_chunks, more_chunks)
        &*& ptrs == cons(first,more_ptrs)
    ;

lemma_auto void bi_block_inv()
    requires [?f]bi_block(?b, ?last, ?fprev, ?lnext, ?ptrs, ?chunks);
    ensures  [ f]bi_block( b,  last,  fprev,  lnext,  ptrs,  chunks)
        &*&  b > 0 &*& last > 0
        &*&  !!forall(chunks, (bounded)(0,pow_nat(2,N32)-1))
        &*&  length(chunks) >= N_INTS
        &*& length(ptrs)*N_INTS == length(chunks)
        &*&  (length(chunks) == N_INTS) == (b == last)
        &*&  !!mem(b,ptrs) &*& !!mem(last,ptrs)
        ;
{
    open bi_block(_,_,_,_,_,_);
    assert [f]b->next |-> ?next;
    assert [f]b->chunks[..N_INTS] |-> ?my_chunks;

    if(!forall(my_chunks,(bounded)(0,pow_nat(2,N32)-1))) {
        int i;
        for(i=0; i < N_INTS; ++i)
            invariant [f]b->chunks[i..N_INTS] |-> ?loop_chunks
                &*&   !forall(loop_chunks,(bounded)(0,pow_nat(2,N32)-1))
                &*&   i >= 0 &*& i <= N_INTS
                ;
            decreases length(loop_chunks);
        {
            open uints(_,_,_);
            assert [f]u_integer(_,?v);

            u_integer_limits(&b->chunks[i]);

            leak [f]u_integer(_,v);

        }
        open uints(_,_,_);
        assert false;
    }

    if(b != last) {
        bi_block_inv();
        assert [f]bi_block(_,_,_,_,_,?rest_chunks);
        forall_append_exact(my_chunks,rest_chunks,(bounded)(0,pow_nat(2,N32)-1));
    }
}

predicate bi_big_int(big_int* b, int free_carries; int i)
    = malloc_block_big_int(b)
    &*& b->first |-> ?first
    &*& b->last |-> ?last
    &*& b->is_pos |-> ?is_pos
    &*& free_carries >= 0 &*& free_carries <= CARRY_BITS
    &*& bi_block(first,last,0,0,_,?chunks)
    &*& !!forall(chunks,
        (bounded)(0,
                  pow_nat(2,nat_of_int(32-free_carries))-1))
    &*& let(poly_eval(chunks,
                CHUNK_BASE),
            ?abs_i)
    &*& is_pos ? i == abs_i : i == -abs_i;

lemma void bi_block_disjoint(big_int_block* a,big_int_block* b)
    requires [?f1]bi_block(a,?alast, ?afprev, ?alnext,?aptrs,?achunks)
        &*&  [?f2]bi_block(b,?blast, ?bfprev, ?blnext,?bptrs,?bchunks)
        &*&  f1 + f2 > 1;
    ensures  [ f1]bi_block(a, alast,  afprev,  alnext, aptrs, achunks)
        &*&  [ f2]bi_block(b, blast,  bfprev,  blnext, bptrs, bchunks)
        &*&  !!disjoint(aptrs,bptrs);
{
    if(!disjoint(aptrs,bptrs)) {
        open bi_block(a,_,_,_,_,_);
        if(mem(a,bptrs)) {

            list<big_int_block_ptr> bptrs_left = bptrs;
            big_int_block* b_left = b;
            while(bptrs_left != nil)
                invariant !!mem(a,bptrs_left)
                    &*&   [f1]a->next |-> _
                    &*&   [f2]bi_block(b_left,?bl_last,_,_,bptrs_left,_);
                decreases length(bptrs_left);
            {
                open [f2]bi_block(b_left,bl_last,_,_,bptrs_left,_);
                assert [f2]b_left->next |-> ?bl_next;
                if(b_left == a) {
                    open big_int_block_next(a,_);
                    open big_int_block_next(b_left,_);
                    //merge_fractions pointer(&a->next,_);
                    pointer_unique(&a->next);
                    assert false;
                }
                cons_head_tail(bptrs_left);
                if(b_left != bl_last) {
                    close [f2]bi_block(b_left,b_left,_,_,_,_);
                    leak [f2]bi_block(b_left,b_left,_,_,_,_);
                    b_left = bl_next;
                    bptrs_left = tail(bptrs_left);
                }
            }
            assert false;
        } else {
            assert a != alast;
            assert [f1]a->next |-> ?anext;
            bi_block_disjoint(anext,b);
            assert false;
        }
    }
}

lemma void bi_block_extend(big_int_block* b)
    requires [?f]bi_block(b,?last1, ?fprev, ?lnext, ?ptrs1,?chunks)
        &*&  [ f]bi_block(lnext,?last,last1,?lnext2,?ptrs2,?chunks2)
        &*&  !!disjoint(ptrs1,ptrs2);
    ensures  [ f]bi_block(b,  last,  fprev,  lnext2,
            append(ptrs1,ptrs2), append(chunks,chunks2));
{
    if(b == lnext || b == last) {
        forall_elim(ptrs1,(notf)((flip)(mem,ptrs2)),b);
        assert false;
    }
    assert b != lnext;
    assert b != last;

    open bi_block(b,_,_,_,_,_);
    assert [f]b->chunks[..N_INTS] |-> ?bchunks;
    if(b != last1) {
        assert [f]b->next |-> ?next;
        assert [f]bi_block(next,_,_,_,_,?nchunks);
        assert chunks == append(bchunks,nchunks);
        bi_block_extend(next);
        append_assoc(bchunks,nchunks,chunks2);
        assert [f]bi_block(next,last,_,_,_,append(nchunks,chunks2));
        assert append(bchunks,append(nchunks,chunks2))
            == append(append(bchunks,nchunks),chunks2);
        assert chunks == append(bchunks,nchunks);
        assert append(bchunks,append(nchunks,chunks2))
            == append(chunks,chunks2);
    }
    close [ f]bi_block(b,  last,  fprev,  lnext2,_,
            append(chunks,chunks2));
}

  @*/

big_int_block* new_block()
    /*@ requires true; @*/
    /*@ ensures  bi_block(result, result, 0,0,
                    _,
                    repeat(0,nat_of_int(N_INTS))); @*/
    /*@ terminates; @*/
{
    size_t i;
    big_int_block* ret = malloc(sizeof(big_int_block));
    if(!ret) { abort(); }
    ret->next = NULL;
    ret->prev = NULL;
    for(i=0;i < N_INTS; ++i)
        /*@ requires i >= 0 &*& ret->chunks[i..N_INTS] |-> _; @*/
        /*@ ensures  ret->chunks[old_i..N_INTS] |->
                        repeat(0,nat_of_int(N_INTS-old_i)); @*/
        /*@ decreases N_INTS-i; @*/
    {
        ret->chunks[i] = 0;
    }
    return ret;
}

big_int* new_big_int_zero()
    /*@ requires true; @*/
    /*@ ensures  bi_big_int(result, CARRY_BITS, 0); @*/
    /*@ terminates; @*/
{
    big_int* ret = malloc(sizeof(big_int));
    if(!ret) { abort(); }
    ret->is_pos = true;
    ret->first = new_block();
    ret->last  = ret->first;
    return ret;
}

big_int* big_int_from_hex(const char* s)
    /*@ requires [?f]string(s,?cs)
            &*&  base_n(hex_chars(),reverse(cs),_,?val)
            ; @*/
    /*@ ensures  [ f]string(s, cs)
            &*&  bi_big_int(result, CARRY_BITS, val); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    size_t s_i;
    size_t block_i;
    size_t block_shift;
    big_int* ret = malloc(sizeof(big_int));
    if(!ret) { abort(); }

    ret->is_pos = true;
    ret->last = new_block();
    ret->first = ret->last;

    /*@ close exists<list<uint32_t> >(nil); @*/
    /*@ close exists<uint32_t>(0); @*/
    /*@ uint32_t ghost_block_shift = 0; @*/

    for(s_i = strlen(s),block_i = 0,block_shift = 0; s_i > 0; --s_i)
        /*@ requires [?lf]ret->first |-> ?first
                &*&  [f]s[..s_i] |-> ?loop_cs
                &*&  ret->last |-> ?last
                &*&  bi_block(last,last,?l_prev,0,_,?chunks)
                &*&  !!forall(chunks,
                        (bounded)(0,
                            pow_nat(2,nat_of_int(CHUNK_BITS))-1))

                &*&  base_n(hex_chars(),reverse(loop_cs),_,?loop_val)

                &*&  exists<list<uint32_t> >(?pref)
                &*&  exists<uint32_t>(?blk)
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
                &*&  !!forall(new_chunks,
                        (bounded)(0,
                            pow_nat(2,nat_of_int(CHUNK_BITS))-1))
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
        /* @ uint32_t *block = &ret->last->chunks[0]; @*/
        /* @ uints_split(block,block_i); @*/
        uint32_t nib = nib_of_hex(s[s_i-1]);
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

            uints_split_as(&last->chunks[0],pref,cons(blk,suff));
            uints_limits((&last->chunks[0]) + block_i);
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
            assert nib <= pow_nat(2,nat_of_int(4))-1;
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
            close exists<uint32_t>(blk|(nib<<block_shift));
        } @*/

        *(&ret->last->chunks[0]+block_i) |= (nib<<block_shift);
        /*@ close uints(&last->chunks[0]+block_i,N_INTS-block_i,_); @*/
        /*@ uints_join(&last->chunks[0]); @*/
        /*@ assert last->chunks[..N_INTS] |-> ?next_chunks; @*/

        /*@ {
            assert next_chunks
                == append(pref,cons(blk|(nib<<block_shift),suff));

            if(!forall(next_chunks,
                (bounded)(0,
                        pow_nat(2,nat_of_int(CHUNK_BITS))-1))) {
                uint32_t cx = not_forall(next_chunks,
                    (bounded)(0,
                            pow_nat(2,nat_of_int(CHUNK_BITS))-1));
                if(mem(cx,pref) || mem(cx,suff)) {
                    forall_elim(chunks,
                        (bounded)(0,
                            pow_nat(2,nat_of_int(CHUNK_BITS))-1),
                        cx);
                } else {
                    assert cx == blk+nib*pow_nat(2,nat_of_int(block_shift));
                }
                assert false;
            }
            assert !!forall(next_chunks,
                (bounded)(0,
                        pow_nat(2,nat_of_int(CHUNK_BITS))-1));

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
            else if(x <= 4) { assert false; }
            assert false;
        } @*/


        /*@ big_int_block* fresh_block = 0; @*/
        /*@ bool fresh_chunk = false; @*/
        if(block_shift == (uint32_t)CHUNK_BITS) {
            /*@ open exists<uint32_t>(?v); @*/
            /*@ {
                fresh_chunk = true;
                close exists<uint32_t>(0);
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
                    close exists<list<uint32_t> >(nil);
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

        /*@ recursive_call(); @*/
        /*@ {
            chars_join(s);
            if(fresh_block) {
                bi_block_disjoint(last,fresh_block);
                assert bi_block(last,last,_,fresh_block,_,
                    next_chunks);
                assert bi_block(fresh_block,_,last,0,_,
                    ?rest_chunks);
                assert !!forall(next_chunks,
                    (bounded)(0,
                            pow_nat(2,nat_of_int(CHUNK_BITS))-1));
                assert !!forall(rest_chunks,
                    (bounded)(0,
                            pow_nat(2,nat_of_int(CHUNK_BITS))-1));
                forall_append(next_chunks,rest_chunks,
                    (bounded)(0,
                            pow_nat(2,nat_of_int(CHUNK_BITS))-1));
                bi_block_extend(last);
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

void free_big_int_inner(big_int* p)
    /*@ requires bi_big_int(p, CARRY_BITS, _); @*/
    /*@ ensures  true; @*/
    /*@ terminates; @*/
{
    big_int_block* blk = p->first;
    do
        /*@ requires bi_block(blk,_,_,0,_,?chunks); @*/
        /*@ ensures  true; @*/
        /*@ decreases length(chunks); @*/
    {
        big_int_block* next = blk->next;
        free(blk);
        blk = next;
    } while(blk);
    free(p);
}

void test1(void)
    /*@ requires true; @*/
    /*@ ensures  true; @*/
    /*@ terminates; @*/
{
    const char* s = "ff";
    /*@ close base_n(hex_chars(),"f",_,15); @*/
    /*@ close base_n(hex_chars(),"ff",_,255); @*/
    big_int* p = big_int_from_hex(s);
    /*@ assert bi_big_int(p,_,255); @*/
    free_big_int_inner(p);

    /* @ assert x < 2; @*/
}

