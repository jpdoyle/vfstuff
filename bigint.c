#include "bigint.h"
/*@ #include "util.gh" @*/

// fill out a 64-byte cache line
#define N_INTS 12
// number of bits to reserve for carries
#define CARRY_BITS 4

typedef struct big_int_block {
    struct big_int_block* prev;
    struct big_int_block* next;
    uint32_t chunks[N_INTS];
} big_int_block;

struct big_int {
    struct big_int_block *first;
    struct big_int_block *last;
    bool is_pos;
};

/*@

predicate bi_block(big_int_block* first,
                   big_int_block* last;
                   big_int_block* first_prev;
                   big_int_block* last_next;
                   list<int> chunks) =
        malloc_struct_big_int(first)
        //struct_big_int_block_padding(first)
    &*& first > 0
    &*& first->next   |-> ?next
    &*& first->prev   |-> first_prev
    &*& first->chunks[..N_INTS] |-> ?my_chunks
    &*& first == last
    ?       last_next == next &*& chunks == my_chunks
    :       bi_block(next, first, last, ?more_chunks)
        &*& chunks == append(my_chunks, more_chunks)
    ;

lemma_auto void bi_block_inv()
    requires [?f]bi_block(?b, ?last, ?fprev, ?lnext, ?chunks);
    ensures  [ f]bi_block( b,  last,  fprev,  lnext,  chunks)
        &*&  b > 0 &*& last > 0 &*& length(chunks)%N_INTS == 0
        &*&  !!forall(chunks, (bounded)(0,pow_nat(2,N32)-1))
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

predicate bi_big_int(big_int* b, int free_carries; int i)
    = malloc_big_int(b)
    &*& b->first |-> ?first
    &*& b->last |-> ?last
    &*& b->is_pos |-> ?is_pos
    &*& free_carries >= 0 &*& free_carries <= CARRY_BITS
    &*& bi_block(first,last,0,0,?chunks)
    &*& forall(chunks,
        (bounded)(0,
                  pow_nat(2,nat_of_int(32-free_carries)-1)))
    &*& let(poly_eval(chunks,
                pow_nat(2,nat_of_int(32-CARRY_BITS))),
            ?abs_i)
    &*& is_pos ? i == abs_i : i == -abs_i;

  @*/

big_int* big_int_from_hex(const char* s)
    /*@ requires [?f]string(s,?cs)
            &*&  base_n(hex_chars(),reverse(cs),_,?val)
            ; @*/
    /*@ ensures  [ f]string(s, cs)
            &*&  bi_big_int(result, CARRY_BITS, val); @*/
    /*@ terminates; @*/
{

}

void test1(void)
    /*@ requires true; @*/
    /*@ ensures  true; @*/
    /*@ terminates; @*/
{
    int x = 3;
    big_int_block* p = malloc(sizeof(big_int_block));
    /* @ assert x < 2; @*/
}

