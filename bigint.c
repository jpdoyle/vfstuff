#include <string.h>
#include <limits.h>
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

predicate bi_block_opt
        (big_int_block* first,
         big_int_block* last;
         big_int_block* first_prev,
         big_int_block* last_next,
         list<big_int_block*> ptrs,
         list<uint32_t> chunks) =
    first == 0
    ? last == 0 &*& first_prev == 0 &*& last_next == 0
    &*& ptrs == nil &*& chunks == nil
    : bi_block(first,last,first_prev,last_next,ptrs,chunks)
    ;

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
        &*&  length(ptrs)*N_INTS == length(chunks)
        &*&  (length(ptrs) == 1) == ( b == last)
        &*&  length(ptrs) >= 1
        &*&  (length(chunks) == N_INTS) == (b == last)
        &*&  !!mem(b,ptrs) &*& !!mem(last,ptrs)
        ;
{
    ALREADY_PROVEN()
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

lemma_auto void bi_block_opt_inv()
    requires [?f]bi_block_opt(?b, ?last, ?fprev, ?lnext, ?ptrs, ?chunks);
    ensures  [ f]bi_block_opt( b,  last,  fprev,  lnext,  ptrs,  chunks)
        &*&  !!forall(chunks, (bounded)(0,pow_nat(2,N32)-1))
        &*&  length(ptrs)*N_INTS == length(chunks)
        &*&  (length(chunks) == 0) == (b == 0)
        ;
{
        ALREADY_PROVEN()
    if(!(true
            &&  !!forall(chunks, (bounded)(0,pow_nat(2,N32)-1))
            &&  length(ptrs)*N_INTS == length(chunks)
            &&  (length(chunks) == 0) == (b == 0))) {
        open bi_block_opt(_,_,_,_,_,_);
        if(b) bi_block_inv();
        assert false;
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
        ALREADY_PROVEN()
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
        ALREADY_PROVEN()
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
    /*@ ALREADY_PROVEN() @*/
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
    /*@ ALREADY_PROVEN() @*/
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
    /*@ ALREADY_PROVEN() @*/
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

/*@

lemma_auto(reverse(l))
void reverse_1<t>(list<t> l)
    requires length(l) <= 1;
    ensures  reverse(l) == l;
{ TRIVIAL_LIST2(l) }

lemma void base_n_nonzero(char p0, list<char> ps, list<char> symbs,
                       char witness)
    requires [?f]base_n(cons(p0,ps),symbs,?seq,?val)
        &*&  !!mem(witness,symbs)
        &*&  witness != p0
        ;
    ensures  [ f]base_n(cons(p0,ps),symbs, seq, val)
        &*&  val != 0;
{
    ALREADY_PROVEN()
    if(val == 0) {
        open base_n(_,_,_,_);
        switch(symbs) {
        case nil: assert false;
        case cons(x,xs):
            assert [f]base_n(_,xs,_,?rest_v);
            cons_head_tail(seq);
            assert val == head(seq) + (length(ps)+1)*rest_v;
            my_mul_mono_r(length(ps)+1,0,rest_v);
            if(x == witness) {
                assert head(seq) > 0;
                assert false;
            } else {
                base_n_nonzero(p0,ps,xs,witness);
            }
        }
        assert false;
    }
}

lemma void base_n_trim(char p0, list<char> ps, list<char> symbs,
                       int suff_len)
    requires base_n(cons(p0,ps),symbs,?seq,?val)
        &*&  val != 0
        &*&  suff_len >= 0 &*& suff_len < length(symbs)
        &*&  !!all_eq(take(suff_len,reverse(symbs)),p0)
        &*&  nth_of(suff_len,reverse(symbs)) != some(p0)
        ;
    ensures  base_n(cons(p0,ps),
                    take(length(symbs)-suff_len,symbs),
                    ?trimmed,val)
        &*&  trimmed == minimize(seq)
        ;
{
    ALREADY_PROVEN()
    switch(symbs) {
    case nil: assert false;
    case cons(c,cs):
        open base_n(_,_,seq,_);
        cons_head_tail(seq);
        if(suff_len + 1 == length(symbs)) {
            assert c != p0;
            assert head(seq) != 0;
            assert !!all_eq(take(suff_len,reverse(symbs)),p0);
            assert take(suff_len,reverse(symbs))
                == reverse(drop(1,symbs));
            assert !!all_eq(reverse(cs),p0);
            assert !!all_eq(reverse(cs),p0);
            assert !!all_eq(cs,p0);
            assert base_n(cons(p0,ps),cs,?cs_seq,0);
            all_eq_map(cs,p0,(flip)(index_of,cons(p0,ps)));
            assert !!all_eq(cs_seq,0);
            assert !!poly_is_zero(cs_seq);
            leak base_n(cons(p0,ps),cs,_,0);
            close base_n(cons(p0,ps),{c},?pol,_);
            assert !!minimal(pol);
        } else {
            assert suff_len < length(symbs)-1;
            assert suff_len < length(cs);
            nth_of_reverse(suff_len,symbs);
            assert nth_of(suff_len,reverse(symbs))
                == nth_of(length(symbs)-2-suff_len, cs);
            switch(nth_of(suff_len,reverse(symbs))) {
            case none:
                nth_of_bounds(suff_len,reverse(symbs));
                assert false;
            case some(w):
                nth_of_mem(length(symbs)-2-suff_len, cs, w);
                base_n_nonzero(p0,ps,cs,w);
                nth_of_map(length(symbs)-2-suff_len, cs,
                        some);
                nth_of_map(length(symbs)-2-suff_len, tail(seq),
                        (flip)(nth_of,cons(p0,ps)));
                switch(nth_of(length(symbs)-2-suff_len,tail(seq))) {
                case none:
                    assert false;
                case some(ix):
                    if(ix == 0) {
                        assert false;
                    }
                    nth_of_mem(length(symbs)-2-suff_len,tail(seq),ix);
                    if(poly_is_zero(tail(seq))) {
                        all_eq_elim(tail(seq),0,ix);
                        assert false;
                    }
                }
            }
            base_n_trim(p0,ps,cs,suff_len);
            assert base_n(cons(p0,ps),
                take(length(symbs)-1-suff_len,cs),?cs_pol,_);
            assert minimize(tail(seq)) == cs_pol;
            assert !!minimal(cs_pol);
            close base_n(cons(p0,ps),
                take(length(symbs)-suff_len,symbs),?pol,_);
            assert minimize(seq) == pol;
            assert !!minimal(pol);
        }
    }
}

@*/


void chars_reverse(char* p,size_t n)
    /*@ requires p[..n] |-> ?cs; @*/
    /*@ ensures  p[..n] |-> reverse(cs); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    if(n > 1) {
        size_t lo = 0,hi = n;
        for(lo=0,hi=n;hi > lo && hi-1 > lo;++lo,--hi)
            /*@ requires p[lo..hi] |-> ?loop_cs
                    &*&  lo >= 0 &*& hi <= n
                    &*&  hi >= lo;
              @*/
            /*@ ensures  p[old_lo..old_hi] |-> reverse(loop_cs); @*/
            /*@ decreases hi-lo; @*/
        {
            /*@ open chars(p+lo,_,_); @*/
            /*@ chars_split(p+lo+1,hi-1-lo-1); @*/
            /*@ open chars(p+hi-1,1,_); @*/
            /*@ assert p[lo]   |-> ?x; @*/
            /*@ assert p[hi-1] |-> ?y; @*/
            /*@ assert p[lo+1..hi-1] |-> ?l; @*/
            char tmp = p[hi-1];
            p[hi-1] = p[lo];
            p[lo] = tmp;

            /*@ recursive_call(); @*/
            /*@ {
                reverse_ends(x,l,y);
                close chars(p+old_hi-1,1,cons(x,nil));
                chars_join(p+old_lo+1);
                close chars(p+old_lo,old_hi-old_lo,
                    cons(y,append(reverse(l),cons(x,nil))));
            } @*/
        }
    }
}

char* reverse_and_dup(char* s,size_t len)
    /*@ requires malloc_block_chars(s,?cap)
            &*&  0 <= len &*& len < cap
            &*&  s[..len] |-> ?cs
            &*&  s[len] |-> _
            &*&  s[len+1..cap] |-> _
            &*&  !mem('\0',cs)
            ; @*/
    /*@ ensures  malloced_string(result,reverse(cs)); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    s[len] = '\0';
    chars_reverse(s,len);
    {
        char* orig_s = s;
        /*@ body_chars_to_string(s); @*/
        s = strdup(s);
        if(!s) abort();
        free(orig_s);
    }
    return s;
}

char* big_int_to_hex(const big_int* s)
    /*@ requires [?f]bi_big_int(s, CARRY_BITS, ?val); @*/
    /*@ ensures  [ f]bi_big_int(s, CARRY_BITS, val)
            &*&  malloced_string(result,?cs)
            &*&  base_n(hex_chars(),reverse(cs),?cs_seq,val)
            // minimality
            &*&  val == 0 ? cs == "0"
            :    !!minimal(cs_seq); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    size_t cap = (size_t)(N_INTS*(CHUNK_BITS/4)) + (size_t)1;
    size_t len = 0, zeroes = 0;
    big_int_block* b = s->first;
    char* ret = malloc(cap);
    if(!ret) abort();
    if(!s->is_pos) abort(); // TODO

    /*@ {
      assert [f]s->first |-> ?first;
      assert [ f]bi_block(first,
        ?last,?bprev,0,?ptrs,?loop_chunks);
      close [ f]bi_block_opt(first,
        last,_,0,_,_);
    } @*/

    for(b=s->first; b; b = b->next)
        /*@ requires malloc_block(ret,cap)
                &*&  ret[..len] |-> ?cs
                &*&  ret[len..cap] |-> _
                &*&  [ f]bi_block_opt(b, ?last,?bprev,0,?ptrs,?loop_chunks)
                &*&  len >= 0 &*& len < cap
                &*&  len+((uint32_t)N_INTS)*((uint32_t)CHUNK_BITS/4)
                    < 2*cap
                &*&  !!forall(loop_chunks,(bounded)(0,CHUNK_BASE-1))
                &*&  zeroes >= 0 &*& zeroes <= len
                ;
          @*/
        /*@ ensures  malloc_block(ret,cap)
                &*&  ret[..old_len] |-> cs
                &*&  ret[old_len..len] |-> ?new_cs
                &*&  !mem('\0',new_cs)
                &*&  len < cap
                &*&  ret[len..cap] |-> _
                &*&  old_len + length(ptrs)*N_INTS*(CHUNK_BITS/4)
                    == len
                &*&  base_n(hex_chars(),new_cs,?cs_seq,
                        poly_eval(loop_chunks,CHUNK_BASE))
                &*&  zeroes >= 0
                &*&  zeroes <= length(append(cs,new_cs))
                &*&  nth_of(zeroes, reverse(new_cs)) != some('0')
                &*&  !!all_eq(take(zeroes, reverse(new_cs)),
                            '0')
                &*&  (zeroes < len-old_len ||
                     zeroes - old_zeroes == len-old_len)
                &*&  old_b == 0
                ? [ f]bi_block_opt(old_b, last,_,_,_, _)
                : [ f]bi_block(old_b, last,bprev,0,ptrs, loop_chunks)
                ;
          @*/
        /*@ decreases length(loop_chunks); @*/
    {
        /*@ int orig_len =len; @*/
        size_t block_i;
        if(cap >= UINT_MAX/2) abort();
        if(len+((uint32_t)N_INTS)*((uint32_t)CHUNK_BITS/4) >= cap) {
            /*@ assert chars(ret,len,cs); @*/
            /*@ assert chars(ret,cap,?realloc_cs); @*/
            /*@ int prev_cap = cap; @*/
            cap *= 2;
            ret = realloc(ret,cap);
            if(!ret) abort();
            /*@ note_eq(take(2*prev_cap,realloc_cs),realloc_cs); @*/
            /*@ note_eq(take(len,realloc_cs),cs); @*/
            /*@ assert chars(ret,prev_cap,realloc_cs); @*/
            /*@ assert  ret[..prev_cap] |-> realloc_cs
                    &*& ret[prev_cap..cap] |-> ?rest_cs
              ; @*/
            /*@ chars_join(ret); @*/
            /*@ assert ret[..cap] |-> ?new_cs; @*/
            /*@ {
              take_append(len,realloc_cs,rest_cs);
              assert take(len,new_cs) == cs;
            } @*/
        }
        /*@ chars_split(ret,len); @*/
        /*@ open bi_block_opt(b,_,_,_,_,_); @*/
        /*@ open bi_block(b,_,_,_,_,_); @*/
        /*@ assert [f]b->next |-> ?b_next; @*/
        /*@ assert [f]b->chunks[..N_INTS] |-> ?block_chunks; @*/
        /*@ if(!forall(block_chunks,(bounded)(0,CHUNK_BASE-1))) {
            int cx = not_forall(block_chunks,(bounded)(0,CHUNK_BASE-1));
            forall_elim(loop_chunks,(bounded)(0,CHUNK_BASE-1),cx);
            assert false;
        } @*/

        /*@ int orig_block = poly_eval(block_chunks,CHUNK_BASE); @*/

        for(block_i = 0; block_i < N_INTS; ++block_i)
            /*@ requires ret[len..cap] |-> _
                    &*&  [f]b->chunks[block_i..N_INTS] |-> ?chk
                    &*&  block_i >= 0 &*& block_i <= N_INTS
                    &*&  !!forall(chk,(bounded)(0,CHUNK_BASE-1))
                    &*&  len + (N_INTS-block_i)*(CHUNK_BITS/4) < cap
                    &*&  block_i >= 0 &*& block_i <= N_INTS
                    &*&  len >= 0
                    &*&  zeroes >= 0 &*& zeroes <= len
                    ;
              @*/
            /*@ ensures  ret[old_len..len] |-> ?new_cs
                    &*&  !mem('\0',new_cs)
                    &*&  ret[len..cap] |-> _
                    &*&  [f]b->chunks[old_block_i..N_INTS] |-> chk
                    &*&  old_len + (N_INTS-old_block_i)*(CHUNK_BITS/4)
                        == len
                    &*&  base_n(hex_chars(),new_cs, _,
                            poly_eval(chk, CHUNK_BASE))
                    &*&  !!all_eq(take(zeroes, reverse(new_cs)), '0')
                    &*&  nth_of(zeroes, reverse(new_cs)) != some('0')
                    &*&  (zeroes < len-old_len ||
                         zeroes - old_zeroes == len-old_len)
                    ;
              @*/
            /*@ decreases length(chk); @*/
        {
            /*@ uints_limits((&b->chunks[0])+block_i); @*/
            /*@ int chunk_chars_left = CHUNK_BITS/4; @*/
            /*@ int prev_len = len; @*/
            /*@ division_unique(CHUNK_BITS,4,CHUNK_BITS/4,0); @*/
            uint32_t chunk_bits_left = (uint32_t)(int)CHUNK_BITS;
            uint32_t chunk = *((&b->chunks[0])+block_i);
            /*@ int orig_chunk = chunk; @*/
            for(; chunk_bits_left; chunk_bits_left -= 4, chunk >>= 4)
                /*@ requires chunk
                            < pow_nat(2,nat_of_int(chunk_bits_left))
                        &*&  ret[len..cap] |-> _
                        &*&  chunk_bits_left >= 0
                        &*&  4*chunk_chars_left == chunk_bits_left
                        &*&  len+chunk_chars_left < cap
                        &*&  chunk_bits_left >= 0
                        &*&  base_n(hex_chars(),nil,nil,0)
                        &*&  zeroes >= 0 &*& zeroes <= len
                        ; @*/
                /*@ ensures  ret[old_len..len] |-> ?new_cs
                        &*&  !mem('\0',new_cs)
                        &*&  ret[len..cap] |-> _
                        &*&  base_n(hex_chars(),new_cs, _, old_chunk)
                        &*&  old_len + old_chunk_chars_left == len
                        &*&  !!all_eq(take(zeroes, reverse(new_cs)), '0')
                        &*&  nth_of(zeroes, reverse(new_cs)) != some('0')
                        &*&  (zeroes < len-old_len ||
                             zeroes - old_zeroes == len-old_len)
                        ; @*/
                /*@ decreases chunk_bits_left; @*/
            {
                /*@ open chars(ret+len,_,_); @*/
                /*@ bitand_pow_2(chunk,N4); @*/
                /*@ div_rem(chunk,pow_nat(2,N4)); @*/
                uint8_t nib = (uint8_t)(chunk&0xf);
                ret[len] = hex_of_nib(nib);
                /*@ assert ret[len] |-> ?c; @*/
                ++len;
                if(nib) {
                    zeroes = 0;
                } else {
                    ++zeroes;
                }
                /*@ int next_zeroes = zeroes; @*/
                /*@ {
                    if(chunk_bits_left < 4) {
                        assert chunk_chars_left >= 1;
                        my_mul_mono_r(4,1,chunk_chars_left);
                        assert false;
                    }
                    --chunk_chars_left;
                    assert chunk >= 0;
                    shiftright_div(chunk,N4);
                    div_rem(chunk,pow_nat(2,N4));
                    assert (chunk>>4) >= 0;
                    mul_abs_commute(pow_nat(2,N4),(chunk>>4));
                    assert abs(pow_nat(2,N4)*(chunk>>4))
                        == pow_nat(2,N4)*(chunk>>4);
                    assert abs(chunk) == chunk;
                    assert pow_nat(2,N4)*(chunk>>4) <= chunk;
                    assert pow_nat(2,N4)*(chunk>>4)
                        <  pow_nat(2,nat_of_int(chunk_bits_left));
                    pow_plus(2,N4,chunk_bits_left-4);
                    assert pow_nat(2,N4)*(chunk>>4)
                        < pow_nat(2,N4)
                            *pow_nat(2,nat_of_int(chunk_bits_left-4));
                    my_inv_mul_strict_mono_r(pow_nat(2,N4), chunk>>4,
                        pow_nat(2,nat_of_int(chunk_bits_left-4)));
                    assert (chunk>>4)
                        < pow_nat(2,nat_of_int(chunk_bits_left-4));

                } @*/

                /*@ recursive_call(); @*/

                /*@ {
                    assert ret[old_len+1..len] |-> ?rest_cs;
                    assert ret[old_len] |-> c;
                    assert reverse(cons(c,rest_cs)) ==
                        append(reverse(rest_cs),{c});
                    nth_of_append(zeroes,reverse(rest_cs),{c});
                    if(zeroes < length(rest_cs)) {
                        take_append(zeroes,reverse(rest_cs),{c});
                        assert take(zeroes,reverse(cons(c,rest_cs)))
                            == take(zeroes,reverse(rest_cs));
                        assert !!all_eq(
                            take(zeroes, reverse(cons(c,rest_cs))),
                            '0');
                    } else {
                        assert zeroes == next_zeroes + length(rest_cs);
                        take_more(zeroes,reverse(rest_cs));
                        assert !!all_eq(reverse(rest_cs),'0');
                        if(!nib) {
                            assert c == '0';
                            assert zeroes >= length(cons(c,rest_cs));
                            assert !!all_eq(reverse(cons(c,rest_cs)),
                                '0');
                        } else {
                            assert zeroes == length(rest_cs);
                            assert nth_of(zeroes,reverse(cons(c,rest_cs)))
                                == some(c);
                        }
                        //take_of_append_r(zeroes,reverse(rest_cs),{c});
                    }
                    assert !!all_eq(
                        take(zeroes, reverse(cons(c,rest_cs))),
                        '0');
                    assert nth_of(zeroes, reverse(cons(c,rest_cs)))
                        != some('0');

                    assert base_n(hex_chars(), rest_cs, ?rest_nibs,
                        old_chunk>>4);
                    close base_n(hex_chars(), cons(c,rest_cs),
                        cons(nib,rest_nibs), old_chunk);
                } @*/
            }
            
            /*@ assert ret[prev_len..len] |-> ?chk_cs; @*/
            /*@ assert [f]b->chunks[old_block_i+1..N_INTS] |->
                 ?chk_rest; @*/
            /*@ assert prev_len + CHUNK_BITS/4 == len; @*/
            /*@ int next_len = len; @*/
            /*@ int next_zeroes = zeroes; @*/

            /*@ recursive_call(); @*/

            /*@ {
                assert ret[next_len..len] |-> ?rest_cs;
                assert length(chk_cs) == CHUNK_BITS/4;
                assert base_n(hex_chars(), chk_cs, _,
                    orig_chunk);
                assert base_n(hex_chars(), rest_cs, _,
                    poly_eval(chk_rest,CHUNK_BASE));
                base_n_append(chk_cs,rest_cs);
                assert base_n(hex_chars(), append(chk_cs,rest_cs), _,
                    ?final_val);
                assert final_val ==
                    orig_chunk
                    + poly_eval(chk_rest,CHUNK_BASE)
                        *pow_nat(16,nat_of_int(length(chk_cs)));
                assert final_val ==
                    orig_chunk
                    + poly_eval(chk_rest,CHUNK_BASE)
                        *pow_nat(16,nat_of_int(CHUNK_BITS/4));
                assert final_val ==
                    orig_chunk
                    + poly_eval(chk_rest,CHUNK_BASE)
                        *pow_nat(pow_nat(2,N4),nat_of_int(CHUNK_BITS/4));
                pow_times2(2,N4,CHUNK_BITS/4);
                assert final_val ==
                    orig_chunk
                    + poly_eval(chk_rest,CHUNK_BASE)
                        *pow_nat(2,nat_of_int(CHUNK_BITS));
                note_eq( final_val ,
                    poly_eval(cons(orig_chunk,chk_rest),
                        CHUNK_BASE));
                assert cons(orig_chunk,chk_rest) == chk;

                chars_join(ret+old_len);
                assert ret[old_len..len] |-> append(chk_cs,rest_cs);

                assert reverse(append(chk_cs,rest_cs)) ==
                    append(reverse(rest_cs),reverse(chk_cs));
                nth_of_append(zeroes,reverse(rest_cs),reverse(chk_cs));
                if(zeroes < length(rest_cs)) {
                    take_append(zeroes,reverse(rest_cs),reverse(chk_cs));
                    assert take(zeroes,reverse(append(chk_cs,rest_cs)))
                        == take(zeroes,reverse(rest_cs));
                    assert !!all_eq(
                        take(zeroes, reverse(append(chk_cs,rest_cs))),
                        '0');
                } else {
                    assert zeroes == next_zeroes + length(rest_cs);
                    take_more(zeroes,reverse(rest_cs));
                    assert !!all_eq(
                        take(next_zeroes,reverse(chk_cs)),
                        '0');
                    assert !!all_eq(reverse(rest_cs), '0');
                    assert !!all_eq(
                        take(zeroes,reverse(append(chk_cs,rest_cs))),
                        '0');
                    //take_of_append_r(zeroes,reverse(rest_cs),{c});
                }
                assert !!all_eq(
                    take(zeroes, reverse(append(chk_cs,rest_cs))),
                    '0');
                assert nth_of(zeroes, reverse(append(chk_cs,rest_cs)))
                    != some('0');

                assert old_len == prev_len;
                assert old_len + (CHUNK_BITS/4) 
                    + (N_INTS-(old_block_i+1))*(CHUNK_BITS/4)
                        == len;
            } @*/
        }
        /*@ list<int> rest_chunks; @*/
        /*@ if(!b_next) {
            close [ f]bi_block_opt(b_next, 0,_,0,_,nil);
            rest_chunks = nil;
        } else {
            close [ f]bi_block_opt(b_next, last,_,0,_,?rest);
            rest_chunks = rest;
        } @*/
        /*@ if(!forall(rest_chunks,(bounded)(0,CHUNK_BASE-1))) {
            int cx = not_forall(rest_chunks,(bounded)(0,CHUNK_BASE-1));
            forall_elim(loop_chunks,(bounded)(0,CHUNK_BASE-1),cx);
            assert false;
        } @*/
        /*@ int next_len = len; @*/
        /*@ int next_zeroes = zeroes; @*/
        /*@ assert ret[orig_len..next_len] |-> ?block_cs; @*/

        /*@ recursive_call(); @*/

        /*@ {
            
        } @*/

        /*@ {
            chars_split(ret,old_len);
            assert ret[..old_len] |-> cs;
            assert ret[old_len..next_len] |-> block_cs;
            assert ret[next_len..len] |-> ?rest_cs;

            assert length(block_cs) == N_INTS*(CHUNK_BITS/4);
            assert base_n(hex_chars(), block_cs, _,
                orig_block);
            assert base_n(hex_chars(), rest_cs, _,
                poly_eval(rest_chunks,CHUNK_BASE));
            base_n_append(block_cs,rest_cs);
            assert base_n(hex_chars(), append(block_cs,rest_cs), _,
                ?final_val);
            assert final_val ==
                orig_block
                + poly_eval(rest_chunks,CHUNK_BASE)
                    *pow_nat(16,nat_of_int(length(block_cs)));
            assert final_val ==
                orig_block
                + poly_eval(rest_chunks,CHUNK_BASE)
                    *pow_nat(16,nat_of_int(N_INTS*(CHUNK_BITS/4)));
            assert final_val ==
                orig_block
                + poly_eval(rest_chunks,CHUNK_BASE)
                    *pow_nat(pow_nat(2,N4),nat_of_int(N_INTS*(CHUNK_BITS/4)));
            pow_times2(2,N4,N_INTS*(CHUNK_BITS/4));
            assert final_val ==
                orig_block
                + poly_eval(rest_chunks,CHUNK_BASE)
                    *pow_nat(2,nat_of_int(N_INTS*CHUNK_BITS));
            pow_times2(2,nat_of_int(CHUNK_BITS),N_INTS);
            assert final_val ==
                orig_block
                + poly_eval(rest_chunks,CHUNK_BASE)
                    *pow_nat(CHUNK_BASE,nat_of_int(N_INTS));
            note_eq( final_val ,
                poly_eval(append(block_chunks,rest_chunks),
                    CHUNK_BASE));
            assert append(block_chunks,rest_chunks) == loop_chunks;

            chars_join(ret+old_len);
            assert ret[old_len..len] |-> append(block_cs,rest_cs);

            assert reverse(append(block_cs,rest_cs)) ==
                append(reverse(rest_cs),reverse(block_cs));
            nth_of_append(zeroes,reverse(rest_cs),reverse(block_cs));
            if(zeroes < length(rest_cs)) {
                take_append(zeroes,reverse(rest_cs),reverse(block_cs));
                assert take(zeroes,reverse(append(block_cs,rest_cs)))
                    == take(zeroes,reverse(rest_cs));
                assert !!all_eq(
                    take(zeroes, reverse(append(block_cs,rest_cs))),
                    '0');
            } else {
                assert zeroes == next_zeroes + length(rest_cs);
                take_more(zeroes,reverse(rest_cs));
                assert !!all_eq(
                    take(next_zeroes,reverse(block_cs)),
                    '0');
                assert !!all_eq(reverse(rest_cs), '0');
                assert !!all_eq(
                    take(zeroes,reverse(append(block_cs,rest_cs))),
                    '0');
            }
            assert !!all_eq(
                take(zeroes, reverse(append(block_cs,rest_cs))),
                '0');
            assert nth_of(zeroes, reverse(append(block_cs,rest_cs)))
                != some('0');

            assert  old_len + N_INTS*(CHUNK_BITS/4)
                    + (length(ptrs)-1)*N_INTS*(CHUNK_BITS/4)
                == len;
        } @*/
    }

    /*@ assert ret[..len] |-> ?final_cs; @*/
    if(len == zeroes) {
        /*@ take_more(zeroes,reverse(final_cs));@*/
        /*@ assert take(zeroes,reverse(final_cs)) == reverse(final_cs);@*/
        /*@ assert !!all_eq(reverse(final_cs),'0');@*/
        /*@ assert !!all_eq(final_cs,'0');@*/
        free(ret);
        /*@ leak base_n(_,final_cs,_,0); @*/
        /*@ close base_n(hex_chars(),"0",_,0); @*/
        ret = strdup("0");
        if(!ret) abort();
        return ret;
    } else {
        /*@ {
            assert zeroes < len;
            if(all_eq(final_cs,'0')) {
                assert !!all_eq(reverse(final_cs),'0');
                switch(nth_of(zeroes,reverse(final_cs))) {
                case none: nth_of_bounds(zeroes,reverse(final_cs));
                    assert false;
                case some(c):
                    nth_of_mem(zeroes,reverse(final_cs),c);
                    assert c != '0';
                    all_eq_elim(reverse(final_cs),'0',c);
                    assert false;
                }
                assert false;
            }
            assert val != 0;
            chars_split(ret,len-zeroes);
            open chars(ret+len-zeroes,_,_);
            base_n_trim('0',tail(hex_chars()),final_cs,zeroes);
        } @*/

        return reverse_and_dup(ret,len-zeroes);
    }

}


/* void test1(void) */
int main(void)
    /*@ requires true; @*/
    /*@ ensures  result == 0; @*/
{
    const char* s = "ff";
    /*@ close base_n(hex_chars(),"f",_,15); @*/
    /*@ close base_n(hex_chars(),"ff",_,255); @*/
    big_int* p = big_int_from_hex(s);
    /*@ assert bi_big_int(p,_,255); @*/
    char* s2 = big_int_to_hex(p);
    printf("%s\n",s);
    printf("%s\n",s2);
    free_big_int_inner(p);
    free(s2);
    /*@ leak base_n(_,_,_,_); @*/

    return 0;
}

