#include "bigint.h"
/*@ #include "util.gh" @*/

// fill out a 64-bytee cache line
#define N_INTS 14

typedef struct big_int_block {
    struct big_int_block* next;
    uint32_t chunks[N_INTS];
} big_int_block;

struct big_int {
    struct big_int_block *first;
    struct big_int_block *last;
    bool sign;
};

/*@

predicate bi_block(big_int_block* b;
            big_int_block* last, list<int> chunks) =
        struct_big_int_block_padding(b)
    &*& b > 0
    &*& b->next   |-> ?next
    &*& b->chunks[..N_INTS] |-> ?my_chunks
    &*& next == 0
    ?       last == b &*& chunks == my_chunks
    :       bi_block(next, last, ?more_chunks)
        &*& chunks == append(my_chunks, more_chunks)
    ;

lemma_auto void bi_block_inv()
    requires [?f]bi_block(?b, ?last, ?chunks);
    ensures  [ f]bi_block( b,  last,  chunks)
        &*&  b > 0 &*& last > 0 &*& length(chunks)%N_INTS == 0
        &*&  !!forall(chunks, (bounded)(0,pow_nat(2,N32)))
        ;
{
    open bi_block(_,_,_);
    assert [f]b->next |-> ?next;
    assert [f]b->chunks[..N_INTS] |-> ?my_chunks;

    if(!forall(my_chunks,(bounded)(0,pow_nat(2,N32)))) {
        int i;
        for(i=0; i < N_INTS; ++i)
            invariant [f]b->chunks[i..N_INTS] |-> ?loop_chunks
                &*&   !forall(loop_chunks,(bounded)(0,pow_nat(2,N32)))
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

    if(next) {
        bi_block_inv();
        assert [f]bi_block(_,_,?rest_chunks);
        div_rem(length(rest_chunks),N_INTS);
        division_unique(length(chunks),N_INTS,1+length(rest_chunks)/N_INTS,0);
        forall_append_exact(my_chunks,rest_chunks,(bounded)(0,pow_nat(2,N32)));
    } else {
        division_unique(length(chunks),N_INTS,1,0);
    }
}

  @*/

void test1(void)
    /*@ requires true; @*/
    /*@ ensures  true; @*/
    /*@ terminates; @*/
{
    int x = 3;
    big_int_block* p = malloc(sizeof(big_int_block));
    /* @ assert x < 2; @*/
}

