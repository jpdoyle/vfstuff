#include "bi_big_int.h"

#if 1
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() assume(false);
#endif

/*@

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
        &*&  poly_eval(chunks,CHUNK_BASE) >= 0
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

    if(poly_eval(my_chunks,CHUNK_BASE) < 0) {
        int neg_x = poly_eval_neg(my_chunks,CHUNK_BASE);
        forall_elim(my_chunks,(bounded)(0,pow_nat(2,N32)-1),neg_x);
        assert false;
    }

    if(b != last) {
        bi_block_inv();
        assert [f]bi_block(_,_,_,_,_,?rest_chunks);
        forall_append_exact(my_chunks,rest_chunks,(bounded)(0,pow_nat(2,N32)-1));

        assert poly_eval(rest_chunks,CHUNK_BASE) >= 0;
        assert poly_eval(chunks,CHUNK_BASE)
            == poly_eval(my_chunks,CHUNK_BASE)
                + pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                    *poly_eval(rest_chunks,CHUNK_BASE)
            ;
        my_mul_mono_r(pow_nat(CHUNK_BASE,nat_of_int(N_INTS)),
                0,poly_eval(rest_chunks,CHUNK_BASE));
        assert pow_nat(CHUNK_BASE,nat_of_int(N_INTS))
                *poly_eval(rest_chunks,CHUNK_BASE) >= 0;
        assert poly_eval(chunks,CHUNK_BASE) >= 0;
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
    /*@ ensures  bi_big_int(result, CARRY_BITS, false, 0); @*/
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

void free_big_int_inner(big_int* p)
    /*@ requires bi_big_int(p, CARRY_BITS, false, _); @*/
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


