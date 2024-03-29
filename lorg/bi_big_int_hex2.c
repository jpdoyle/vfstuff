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

INLINE void chars_reverse(char* p,size_t n)
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

INLINE char* reverse_and_dup(char* s,size_t len)
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
    /*@ requires [?f]bi_big_int(s, CARRY_BITS, false, ?val); @*/
    /*@ ensures  [ f]bi_big_int(s, CARRY_BITS, false,  val)
            &*&  malloced_string(result,?cs)
            &*&  val == 0
            ?    cs == "0"
            &*&  base_n(hex_chars(),cs,_,val)
            :    val > 0
            ?    base_n(hex_chars(),reverse(cs),?cs_seq,val)
            &*&  !!minimal(cs_seq)
            :    val < 0 &*& safe_head(cs) == some('-')
            &*&  base_n(hex_chars(),reverse(tail(cs)),?cs_seq,-val)
            &*&  !!minimal(cs_seq)
            ; @*/
    /*@ terminates; @*/
{
    /* @ ALREADY_PROVEN() @*/
    size_t cap = (size_t)(N_INTS*(CHUNK_BITS/4)) + (size_t)1;
    size_t len = 0, zeroes = 0;
    big_int_block* b = s->first;
    char* ret = malloc(cap);
    if(!ret) abort();

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
                &*&  len >= 0 &*& len+1 < cap
                &*&  len+((size_t)N_INTS)*((size_t)CHUNK_BITS/4)+1
                    < 2*cap
                &*&  !!forall(loop_chunks,(bounded)(0,CHUNK_BASE-1))
                &*&  zeroes >= 0 &*& zeroes <= len
                ;
          @*/
        /*@ ensures  malloc_block(ret,cap)
                &*&  ret[..old_len] |-> cs
                &*&  ret[old_len..len] |-> ?new_cs
                &*&  !mem('\0',new_cs)
                &*&  len+1 < cap
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
        if(len+((size_t)N_INTS)*((size_t)CHUNK_BITS/4)+1 >= cap) {
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
                    &*&  len + (N_INTS-block_i)*(CHUNK_BITS/4)+1 < cap
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
            /*@ ints_limits2((&b->chunks[0])+block_i); @*/
            /*@ int chunk_chars_left = CHUNK_BITS/4; @*/
            /*@ int prev_len = len; @*/
            /*@ division_unique(CHUNK_BITS,4,CHUNK_BITS/4,0); @*/
            int32_t chunk_bits_left = (int32_t)(int)CHUNK_BITS;
            int32_t chunk = *((&b->chunks[0])+block_i);
            /*@ int orig_chunk = chunk; @*/
            for(; chunk_bits_left; chunk_bits_left -= 4, chunk >>= 4)
                /*@ requires chunk >= 0
                        &*&  chunk
                            < pow_nat(2,noi(chunk_bits_left))
                        &*&  ret[len..cap] |-> _
                        &*&  chunk_bits_left >= 0
                        &*&  4*chunk_chars_left == chunk_bits_left
                        &*&  len+chunk_chars_left+1 < cap
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
                        <  pow_nat(2,noi(chunk_bits_left));
                    pow_plus(2,N4,chunk_bits_left-4);
                    assert pow_nat(2,N4)*(chunk>>4)
                        < pow_nat(2,N4)
                            *pow_nat(2,noi(chunk_bits_left-4));
                    my_inv_mul_strict_mono_r(pow_nat(2,N4), chunk>>4,
                        pow_nat(2,noi(chunk_bits_left-4)));
                    assert (chunk>>4)
                        < pow_nat(2,noi(chunk_bits_left-4));

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
                        take_of_append_r(zeroes,reverse(rest_cs),{c});
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
                        *pow_nat(16,noi(length(chk_cs)));
                assert final_val ==
                    orig_chunk
                    + poly_eval(chk_rest,CHUNK_BASE)
                        *pow_nat(16,noi(CHUNK_BITS/4));
                assert final_val ==
                    orig_chunk
                    + poly_eval(chk_rest,CHUNK_BASE)
                        *pow_nat(pow_nat(2,N4),noi(CHUNK_BITS/4));
                pow_times2(2,N4,CHUNK_BITS/4);
                assert final_val ==
                    orig_chunk
                    + poly_eval(chk_rest,CHUNK_BASE)
                        *pow_nat(2,noi(CHUNK_BITS));
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
                    assert reverse(append(chk_cs,rest_cs))
                        == append(reverse(rest_cs), reverse(chk_cs));
                    take_of_append_r(zeroes, reverse(rest_cs),
                        reverse(chk_cs));
                    assert !!all_eq(
                        take(zeroes,reverse(append(chk_cs,rest_cs))),
                        '0');
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
                    *pow_nat(16,noi(length(block_cs)));
            assert final_val ==
                orig_block
                + poly_eval(rest_chunks,CHUNK_BASE)
                    *pow_nat(16,noi(N_INTS*(CHUNK_BITS/4)));
            assert final_val ==
                orig_block
                + poly_eval(rest_chunks,CHUNK_BASE)
                    *pow_nat(pow_nat(2,N4),noi(N_INTS*(CHUNK_BITS/4)));
            pow_times2(2,N4,N_INTS*(CHUNK_BITS/4));
            assert final_val ==
                orig_block
                + poly_eval(rest_chunks,CHUNK_BASE)
                    *pow_nat(2,noi(N_INTS*CHUNK_BITS));
            pow_times2(2,noi(CHUNK_BITS),N_INTS);
            assert final_val ==
                orig_block
                + poly_eval(rest_chunks,CHUNK_BASE)
                    *pow_nat(CHUNK_BASE,noi(N_INTS));
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
                take_of_append_r(zeroes, reverse(rest_cs),
                    reverse(block_cs));
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

        if(s->is_pos) {
            return reverse_and_dup(ret,len-zeroes);
        } else {
            ret[len-zeroes] = '-';
            /*@ close chars(ret+len-zeroes,1,{'-'}); @*/
            /*@ chars_join(ret); @*/
            /*@ open chars(ret+len-zeroes+1,_,_); @*/
            return reverse_and_dup(ret,len-zeroes+1);
        }
    }

}

