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
        &*&  f > 0 &*& f <= 1
        &*&  b > 0 &*& last > 0
        &*&  !!forall(chunks, (bounded)(-pow_nat(2,N31),pow_nat(2,N31)-1))
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
    if(f > 1) {
        open integers_(b->chunks,_,_,_,_);
        integer__unique(b->chunks);
        assert false;
    }

    if(!forall(my_chunks,(bounded)(-pow_nat(2,N31),pow_nat(2,N31)-1))) {
        int i;
        for(i=0; i < N_INTS; ++i)
            invariant [f]b->chunks[i..N_INTS] |-> ?loop_chunks
                &*&   !forall(loop_chunks,(bounded)(-pow_nat(2,N31),pow_nat(2,N31)-1))
                &*&   i >= 0 &*& i <= N_INTS
                ;
            decreases length(loop_chunks);
        {
            open integers_(_,_,_,_,_);
            assert [f]integer_(_,_,_,?v);

            integer__limits(&b->chunks[i]);
            shiftleft_def(1,N31);

            leak [f]integer_(_,_,_,v);

        }
        assert false;
    }

    if(b != last) {
        bi_block_inv();
        assert [f]bi_block(_,_,_,_,_,?rest_chunks);
        forall_append_exact(my_chunks,rest_chunks,(bounded)(-pow_nat(2,N31),pow_nat(2,N31)-1));
    }
}

lemma_auto void bi_block_opt_inv()
    requires [?f]bi_block_opt(?b, ?last, ?fprev, ?lnext, ?ptrs, ?chunks);
    ensures  [ f]bi_block_opt( b,  last,  fprev,  lnext,  ptrs,  chunks)
        &*&  !!forall(chunks, (bounded)(-pow_nat(2,N31),pow_nat(2,N31)-1))
        &*&  length(ptrs)*N_INTS == length(chunks)
        &*&  (length(chunks) == 0) == (b == 0)
        &*&  (length(ptrs) == 0) == (b == 0)
        &*&  (length(ptrs) <= 1) == (b == last)
        &*&  (b == 0) == (last == 0)
        ;
{
        ALREADY_PROVEN()
    if(!(true
            &&  !!forall(chunks, (bounded)(-pow_nat(2,N31),pow_nat(2,N31)-1))
            &&  length(ptrs)*N_INTS == length(chunks)
            &&  (length(chunks) == 0) == (b == 0)
            &&  (length(ptrs) == 0) == (b == 0)
            &&  (length(ptrs) <= 1) == (b == last)
            &&  (b == 0) == (last == 0)
            )) {
        open bi_block_opt(_,_,_,_,_,_);
        if(length(ptrs) < 1 && b) assert false;
        if(b) {
            bi_block_inv();
            if(last == 0) assert false;
            note( last != 0);
            if(b == last) {
                assert length(ptrs) == 1;
                if(length(ptrs) > 1) assert false;
                note_weird(!(length(ptrs) <= 1));
                true_fact(length(ptrs) <= 1);
                true_fact(b == last);
                equal_facts((length(ptrs) <= 1), (b == last));
            } else {
                assert length(ptrs) > 1;
                note_weird((length(ptrs) <= 1));
                note( !(b == last));
                if((b == last) != (length(ptrs) <= 1))
                    nonequal_facts((length(ptrs) <= 1), (b == last));
            }
        } else {
            if(last != 0) assert false;
            note_eq(b,last);
            note_eq(ptrs,nil);
            note_eq(length(ptrs),0);
            TRIVIAL_LIST(ptrs)
            if(length(ptrs) > 1) assert false;
            if(!(length(ptrs) <= 1)) assert false;
            if(0 > 1) assert false;
            if(0 <= 1) {} else { assert false; }
            if((0 <= 1) == true) {
            } else {
                note_weird(length(ptrs) <= 1);
                assert false;
            }
        }
        assert false;
    }
}

lemma void bi_big_int_inv()
    requires [?f]bi_big_int(?p, ?carry1, ?und1, ?i1);
    ensures  [ f]bi_big_int( p,  carry1,  und1,  i1)
        &*&  f > 0 &*& f <= 1 &*& p > 0;
{
        ALREADY_PROVEN()
    if(f <= 0 || f > 1 || p <= 0) {
        open bi_big_int(_,_,_,_);
        assert false;
    }
}


lemma void bi_big_int_val(big_int* p)
    requires [?f1]bi_big_int(p, ?carry1, ?und1, ?i1)
        &*&  [?f2]bi_big_int(p, ?carry2, ?und2, ?i2);
    ensures  [ f1]bi_big_int(p,  carry1,  und1,  i1)
        &*&  [ f2]bi_big_int(p,  carry2,  und2,  i2)
        &*&  i1 == i2;
{
        ALREADY_PROVEN()
    if(i1 != i2) {
        open [f2]bi_big_int(_,_,_,i2);
        open [f1]bi_big_int(_,_,_,i1);
        assert false;
    }
}

lemma void bi_big_int_unique(big_int* p, big_int* q)
    requires [?f1]bi_big_int(p, ?carry1, ?und1, ?i1)
        &*&  [?f2]bi_big_int(q, ?carry2, ?und2, ?i2)
        &*&  f1+f2 > 1;
    ensures  [ f1]bi_big_int(p,  carry1,  und1,  i1)
        &*&  [ f2]bi_big_int(q,  carry2,  und2,  i2)
        &*&  p != q;
{
        ALREADY_PROVEN()
    if(p == q) {
        open [f2]bi_big_int(_,_,_,i2);
        open [f1]bi_big_int(_,_,_,i1);
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
                    &*&   [f1]a->next |-> ?_
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

lemma void bi_block_rend(big_int_block* b, big_int_block* i)
    requires [?f]bi_block(b, ?last, ?fprev, ?lnext, ?ptrs, ?chunks)
        &*&  !!mem(i,ptrs) &*& b != i;
    ensures  [ f]bi_block(b,?last1,  fprev, i, ?ptrs1,?chunks1)
        &*&  [ f]bi_block(i,last,last1,lnext,?ptrs2,?chunks2)
        &*&  !!disjoint(ptrs1,ptrs2)
        &*&  chunks == append(chunks1,chunks2)
        &*&  ptrs == append(ptrs1,ptrs2);
{
    open bi_block(b,_,_,_,_,_);
    assert [f]b->next |-> ?next;
    if(i == next) {
        close [f]bi_block(b,b,fprev,i,_,_);
    } else {
        assert [f]b->chunks[..N_INTS] |-> ?bchunks;
        assert [f]bi_block(next,_,_,_,_,?rest);
        assert chunks == append(bchunks,rest);

        bi_block_rend(next,i);

        assert  [ f]bi_block(next,?nlast, b, i, ?ptrs1,?chunks1)
            &*& [ f]bi_block(i,last,nlast,lnext,?ptrs2,?chunks2);

        assert tail(ptrs) == append(ptrs1,ptrs2);
        assert rest == append(chunks1,chunks2);
        append_assoc(bchunks,chunks1,chunks2);
        assert append(bchunks,rest) == append(append(bchunks,chunks1),chunks2);

        close [f]bi_block(b,nlast,fprev,i,cons(b,ptrs1),append(bchunks,chunks1));
    }
}

  @*/

big_int_block* new_block()
    /*@ requires true; @*/
    /*@ ensures  bi_block(result, result, 0,0,
                    _,
                    repeat(0,noi(N_INTS))); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    size_t i;
    big_int_block* ret = malloc(sizeof(big_int_block));
    if(!ret) { abort(); }
    ret->next = NULL;
    ret->prev = NULL;
    for(i=0;i < N_INTS; ++i)
        /*@ requires i >= 0 &*& i <= N_INTS &*& ret->chunks[i..N_INTS] |-> _; @*/
        /*@ ensures  ret->chunks[old_i..N_INTS] |->
                        repeat(0,noi(N_INTS-old_i)); @*/
        /*@ decreases N_INTS-i; @*/
    {
        /*@ assert noi(N_INTS-i) == succ(noi(N_INTS-(i+1))); @*/
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

void big_int_set(big_int* x,int32_t v)
    /*@ requires bi_big_int(x, _,_,_); @*/
    /*@ ensures  bi_big_int(x, CARRY_BITS, false, v); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    uint64_t abs_v = v < 0 ? (uint64_t)-(int64_t)v : (uint64_t)(int64_t)v;
    /*@ {
        shiftleft_def(1,noi(CHUNK_BITS));
        shiftright_div(abs_v,noi(CHUNK_BITS));
        pow_monotonic(2,noi(CHUNK_BITS),N31);
        bitand_pow_2(abs_v,noi(CHUNK_BITS));
        div_rem(abs_v,pow_nat(2,noi(CHUNK_BITS)));
    } @*/
    int32_t v1 = (int32_t)(abs_v&((((uint64_t)1)<<CHUNK_BITS)-1));
    int32_t v2 = (int32_t)(abs_v >> CHUNK_BITS);
    /*@ assert abs_v == v1 + CHUNK_BASE*v2; @*/
    /*@ assert !!bounded(0,CHUNK_BASE-1,v1); @*/
    /*@ assert !!bounded(0,CHUNK_BASE-1,v2); @*/

    big_int_block* i;
    x->is_pos = (v >= 0);
    /*@ assert x->first |-> ?first; @*/
    /*@ assert x->last |-> ?last; @*/
    /*@ close bi_block_opt(first,last,0,0,_,_); @*/
    for(i=x->first; i; i = i->next)
        /*@ requires bi_block_opt(i,?loop_last,?iprev,0,?ptrs,_)
                &*&  i != 0 || (v1 ==0 && v2 == 0)
                &*& !!bounded(0,CHUNK_BASE-1,v1)
                &*& !!bounded(0,CHUNK_BASE-1,v2)
                ; @*/
        /*@ ensures  bi_block_opt(old_i,loop_last,iprev,0,ptrs,
                        ?final_chunks)
                &*&  poly_eval(final_chunks, CHUNK_BASE)
                        == old_v1 + CHUNK_BASE*old_v2
                &*&  !!forall(final_chunks,(bounded)(0,CHUNK_BASE-1))
                &*&  !!forall(final_chunks,
                        (bounded)(-CHUNK_BASE+1,CHUNK_BASE-1))
                ; @*/
        /*@ decreases length(ptrs); @*/

    {
        size_t block_i;
        i->chunks[0] = v1;
        i->chunks[1] = v2;

        for(block_i=2; block_i<N_INTS; ++block_i)
            /*@ requires i->chunks[block_i..N_INTS] |-> ?_
                    &*&  block_i >= 2 &*& block_i <= N_INTS; @*/
            /*@ ensures  i->chunks[old_block_i..N_INTS]
                            |-> repeat(0,noi(N_INTS-old_block_i)); @*/
            /*@ decreases N_INTS-block_i; @*/
        {
            i->chunks[block_i] = 0;
        }
        v1 = 0;
        v2 = 0;

        /*@ assert i->next |-> ?next; @*/
        /*@ if(next) {
            close bi_block_opt(next,loop_last,_,_,_,_);
        } else {
            close bi_block_opt(next,0,_,_,_,_);
        } @*/

        /*@ recursive_call(); @*/

        /*@ {
            assert  bi_block(old_i,old_i,_,next,_,?final_chunks)
                &*& bi_block_opt(next,_,_,_,_,?rest_chunks);
            forall_append(final_chunks,rest_chunks,(bounded)(0,CHUNK_BASE-1));
            forall_append(final_chunks,rest_chunks,
                        (bounded)(-CHUNK_BASE+1,CHUNK_BASE-1));

        } @*/
    }
}

big_int* new_big_int_from(int32_t v)
    /*@ requires true; @*/
    /*@ ensures  bi_big_int(result, CARRY_BITS, false, v); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    uint64_t abs_v = v < 0 ? (uint64_t)-(int64_t)v : (uint64_t)(int64_t)v;
    /*@ {
        shiftleft_def(1,noi(CHUNK_BITS));
        shiftright_div(abs_v,noi(CHUNK_BITS));
        pow_monotonic(2,noi(CHUNK_BITS),N31);
        bitand_pow_2(abs_v,noi(CHUNK_BITS));
        div_rem(abs_v,pow_nat(2,noi(CHUNK_BITS)));
    } @*/
    int32_t v1 = (int32_t)(abs_v&((((uint64_t)1)<<CHUNK_BITS)-1));
    int32_t v2 = (int32_t)(abs_v >> CHUNK_BITS);
    /*@ assert abs_v == v1 + CHUNK_BASE*v2; @*/

    big_int* ret = malloc(sizeof(big_int));
    if(!ret) { abort(); }
    ret->is_pos = (v >= 0);
    ret->first = new_block();
    ret->last  = ret->first;
    ret->first->chunks[0] = v1;
    ret->first->chunks[1] = v2;
    return ret;
}

big_int* big_int_clone_into(big_int* ret,const big_int* x)
    /*@ requires [?f]bi_big_int(x,?carry,?under,?v)
            &*&  bi_big_int(ret,_,_,_); @*/
    /*@ ensures  [ f]bi_big_int(x, carry, under, v)
            &*&  bi_big_int(result,carry, under, v)
            &*&  result == ret; @*/
    /*@ terminates; @*/
{
    /*@ open bi_big_int(x,_,_,_); @*/
    big_int_block* i = ret->first;
    big_int_block* x_i = x->first;
    ret->is_pos = x->is_pos;
    /*@ close [f]bi_block_opt(x_i,?xlast,?prev,0,?xptrs,
                                ?chunks); @*/
    /*@ assert let(pow_nat(2,noi(31-carry))-1,?upper); @*/
    /*@ assert let(under ? -upper : 0, ?lower); @*/

    do
        /*@ requires bi_block(i,?ilast,?iprev,0,?iptrs,_)
                &*&  [f]bi_block_opt(x_i,?loop_xlast,?xprev,0,?loop_xptrs,
                                ?loop_chunks)
                &*&  !!forall(loop_chunks,(bounded)(-upper,upper))
                &*&  !!forall(loop_chunks,(bounded)(lower,upper))
                &*&  ret->last |-> ilast
                ; @*/
        /*@ ensures  bi_block(old_i,?new_ilast,iprev,0,_,?ichunks)
                &*&  [f]bi_block_opt(old_x_i,loop_xlast,xprev,0,loop_xptrs,
                                loop_chunks)
                &*&  poly_eval(ichunks,CHUNK_BASE)
                    == poly_eval(loop_chunks,CHUNK_BASE)
                &*&  !!forall(ichunks,(bounded)(-upper,upper))
                &*&  !!forall(ichunks,(bounded)(lower,upper))
                &*&  ret->last |-> new_ilast
                ; @*/
        /*@ decreases max_of(length(iptrs),length(loop_xptrs)); @*/
    {
        size_t block_i;
        if(x_i) {
            for(block_i = 0; block_i < N_INTS; ++block_i)
                /*@ requires block_i >= 0 &*& block_i <= N_INTS
                        &*&  i->chunks[block_i..N_INTS] |-> ?_
                        &*&  [f]x_i->chunks[block_i..N_INTS] |-> ?block
                        ; @*/
                /*@ ensures  i->chunks[old_block_i..N_INTS] |-> block
                        &*&  [f]x_i->chunks[old_block_i..N_INTS] |-> block
                        ; @*/
                /*@ decreases N_INTS-block_i; @*/
            {
                /*@ {
                  integers__limits2(&x_i->chunks[block_i]);
                } @*/
                i->chunks[block_i] = *(&x_i->chunks[block_i]);
            }
        } else {
            for(block_i = 0; block_i < N_INTS; ++block_i)
                /*@ requires block_i >= 0 &*& block_i <= N_INTS
                        &*&  i->chunks[block_i..N_INTS] |-> ?_
                        ; @*/
                /*@ ensures  i->chunks[old_block_i..N_INTS] |-> ?block
                        &*&  !!all_eq(block,0)
                        &*&  !!forall(block,(bounded)(-upper,upper))
                        &*&  !!forall(block,(bounded)(lower,upper))
                        ; @*/
                /*@ decreases N_INTS-block_i; @*/
            {
                i->chunks[block_i] = 0;
            }
        }
        /*@ assert let(x_i,?orig_x_i); @*/
        if(x_i) x_i = x_i->next;

        /*@ if(!x_i) {
          close [f]bi_block_opt(x_i,x_i,0,0,nil, _);
        } else {
            assert [f]orig_x_i->chunks[..N_INTS] |-> ?this_chunk;
            assert [f]bi_block(x_i,loop_xlast,_,_,_,?rest);
            assert loop_chunks == append(this_chunk,rest);
            forall_append(this_chunk,rest,(bounded)(-upper,upper));
            forall_append(this_chunk,rest,(bounded)(lower,upper));

            close [f]bi_block_opt(x_i,loop_xlast,_,_,_, _);
        }@*/

        if(x_i && !i->next) {
            big_int_block* last = new_block();
            i->next = last;
            last->prev = i;
            ret->last = last;
            /*@ note(last != 0); @*/
            /*@ note(last != i); @*/
            /*@ assert last->next |-> 0; @*/
            /*@ close bi_block(last,last,i,0,_,_); @*/
        }
        /*@ assert let(i,?orig_i); @*/
        i = i->next;
        /*@ assert let(x_i,?next_x_i); @*/
        /*@ assert let(i,?next_i); @*/

        /*@ if(!i && !x_i) {
          close bi_block(orig_i,orig_i,iprev,0,_,_);
        } @*/

        /*@ recursive_call(); @*/

        /*@ {
            assert  ret->last |-> ?final_ilast;
            assert old_i->chunks[..N_INTS] |-> ?old_i_chunks;
            assert bi_block(next_i,final_ilast,_,_,?ptrs,?rest);
            forall_append(old_i_chunks,rest,(bounded)(-upper,upper));
            forall_append(old_i_chunks,rest,(bounded)(lower,upper));
            if(mem(old_i,ptrs)) {
                close bi_block(old_i,old_i,_,_,_,_);
                bi_block_disjoint(old_i,next_i);
                assert false;
            }


            close bi_block(old_i,final_ilast,_,_,cons(old_i,ptrs),_);

        } @*/
    } while(i || x_i);

    return ret;
}

big_int* big_int_clone(const big_int* x)
    /*@ requires [?f]bi_big_int(x,?carry,?under,?v); @*/
    /*@ ensures  [ f]bi_big_int(x, carry, under, v)
            &*&  bi_big_int(result,carry, under, v); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    big_int* ret = malloc(sizeof(big_int));
    if(!ret) { abort(); }
    ret->first = new_block();
    ret->last  = ret->first;
    /*@ open bi_big_int(x,_,_,_); @*/
    big_int_block* i = ret->first;
    big_int_block* x_i = x->first;
    ret->is_pos = x->is_pos;
    do
        /*@ requires [f]bi_block(x_i,?xlast,?xprev,0,?xptrs,?chunks)
                &*&  bi_block(i,i,?iprev,0,_,_)
                &*&  ret->last |-> i
                &*&  [f]x->last |-> xlast
                ; @*/
        /*@ ensures  ret->last |-> ?ilast
                &*&  [f]x->last |-> xlast
                &*&  [f]bi_block(old_x_i, xlast, xprev,0, xptrs, chunks)
                &*&  bi_block(old_i,ilast, iprev,0,?ptrs,chunks)
                ; @*/
        /*@ decreases length(chunks); @*/
    {
        size_t block_i;
        for(block_i = 0; block_i < N_INTS; ++block_i)
            /*@ requires block_i >= 0 &*& block_i <= N_INTS
                    &*&  i->chunks[block_i..N_INTS] |-> ?_
                    &*&  [f]x_i->chunks[block_i..N_INTS] |-> ?block
                    ; @*/
            /*@ ensures  i->chunks[old_block_i..N_INTS] |-> block
                    &*&  [f]x_i->chunks[old_block_i..N_INTS] |-> block
                    ; @*/
            /*@ decreases N_INTS-block_i; @*/
        {
            /*@ integers__limits2(&x_i->chunks[block_i]); @*/
            i->chunks[block_i] = *(&x_i->chunks[block_i]);
        }
        if(x_i != x->last) {
            big_int_block* last = new_block();
            i->next = last;
            last->prev = i;
            ret->last = last;
            /*@ note(last != 0); @*/
            /*@ note(last != i); @*/
            /*@ assert last->next |-> 0; @*/
        } else {
            /*@ {
              assert [f]x_i->next |-> 0;
            } @*/
        }
        x_i = x_i->next;
        i = i->next;
        /*@ assert let(x_i,?next_x_i); @*/
        /*@ assert let(i,?next_i); @*/

        /*@ recursive_call(); @*/

        /*@ {
            assert  ret->last |-> ?ilast;
            assert bi_block(next_i,ilast,_,_,?ptrs,_);
            if(mem(old_i,ptrs)) {
                close bi_block(old_i,old_i,_,_,_,_);
                bi_block_disjoint(old_i,next_i);
                assert false;
            }
        } @*/
    } while(x_i);
    return ret;
}


void free_big_int_inner(big_int* p)
    /*@ requires bi_big_int(p, _, _, _); @*/
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


