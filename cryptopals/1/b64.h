#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <malloc.h>
#include <stdbool.h>
/*@ #include "../../lists.gh" @*/
/*@ #include "../../poly.gh" @*/
/*@ #include "../../bitops.gh" @*/

#ifndef CRYPTOPALS_B64_H
#define CRYPTOPALS_B64_H

#if 1
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() { assume(false); }
#endif

#ifndef __FILE__
#define calloc(a,b) malloc((a)*b)
#endif

/*@

fixpoint list<char> hex_chars() {
    return "0123456789abcdef";
}

lemma void in_range1_hex_chars(char c)
    requires (c >= 'a' && c <= 'f');
    ensures  !!mem(c,hex_chars());
{
         if(c < 'b') {}
    else if(c < 'c') {}
    else if(c < 'd') {}
    else if(c < 'e') {}
    else if(c < 'f') {}
}

lemma void in_range2_hex_chars(char c)
    requires (c >= '0' && c <= '9');
    ensures  !!mem(c,hex_chars());
{
    ALREADY_PROVEN()
         if(c < '1') {}
    else if(c < '2') {}
    else if(c < '3') {}
    else if(c < '4') {}
    else if(c < '5') {}
    else if(c < '6') {}
    else if(c < '7') {}
    else if(c < '8') {}
    else if(c < '9') {}
}

lemma_auto(mem(c,hex_chars()))
void hex_chars_range(char c)
    requires true;
    ensures  mem(c,hex_chars())
        ==   ((c >= 'a' && c <= 'f') || (c >= '0' && c <= '9'));
{
    ALREADY_PROVEN()
    if(c >= 'a' && c <= 'f') {
        in_range1_hex_chars(c);
    } else if(c >= '0' && c <= '9') {
        in_range2_hex_chars(c);
    }
}

  @*/

bool is_hex(char c)
    /*@ requires true; @*/
    /*@ ensures  result == mem(c,hex_chars()); @*/
    /*@ terminates; @*/
{
    return (c >= 'a' && c <= 'f') || (c >= '0' && c <= '9');
}

char hex_of_nib(uint8_t c)
    /*@ requires c >= 0 &*& c < 16; @*/
    /*@ ensures  some(result) == nth_of(c,hex_chars()); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    if(c < 10)      { return (char)('0'+c);      }
    else if(c < 16) { return (char)('a'+(c-10)); }
    else { /*@ assert false; @*/ abort(); }
}

uint8_t nib_of_hex(char c)
    /*@ requires !!mem(c,hex_chars()); @*/
    /*@ ensures  some(c) == nth_of(result,hex_chars()); @*/
    /*@ terminates; @*/
{
    if(c >= 'a' && c <= 'f') {
        return (uint8_t)(10 + (c-'a'));
    } else if(c >= '0' && c <= '9') {
        return (uint8_t)(c-'0');
    } else { abort(); }
}

/*@

fixpoint list<char> b64_chars() {
    return "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
           "0123456789+/";
}

lemma void in_range1_b64_chars(char c)
    requires (c >= 'a' && c <= 'f');
    ensures  !!mem(c,b64_chars());
{
    ALREADY_PROVEN()
         if(c < 'b') {}
    else if(c < 'c') {}
    else if(c < 'd') {}
    else if(c < 'e') {}
    else if(c < 'f') {}
    else if(c < 'g') {}
    else if(c < 'h') {}
    else if(c < 'i') {}
    else if(c < 'j') {}
    else if(c < 'k') {}
    else if(c < 'l') {}
    else if(c < 'm') {}
    else if(c < 'n') {}
    else if(c < 'o') {}
    else if(c < 'p') {}
    else if(c < 'q') {}
    else if(c < 'r') {}
    else if(c < 's') {}
    else if(c < 't') {}
    else if(c < 'u') {}
    else if(c < 'v') {}
    else if(c < 'w') {}
    else if(c < 'x') {}
    else if(c < 'y') {}
    else if(c < 'z') {}
}

lemma void in_range2_b64_chars(char c)
    requires (c >= 'A' && c <= 'Z');
    ensures  !!mem(c,b64_chars());
{
    ALREADY_PROVEN()
         if(c < 'B') {}
    else if(c < 'C') {}
    else if(c < 'D') {}
    else if(c < 'E') {}
    else if(c < 'F') {}
    else if(c < 'G') {}
    else if(c < 'H') {}
    else if(c < 'I') {}
    else if(c < 'J') {}
    else if(c < 'K') {}
    else if(c < 'L') {}
    else if(c < 'M') {}
    else if(c < 'N') {}
    else if(c < 'O') {}
    else if(c < 'P') {}
    else if(c < 'Q') {}
    else if(c < 'R') {}
    else if(c < 'S') {}
    else if(c < 'T') {}
    else if(c < 'U') {}
    else if(c < 'V') {}
    else if(c < 'W') {}
    else if(c < 'X') {}
    else if(c < 'Y') {}
    else if(c < 'Z') {}
}

lemma void b64_cases(int n)
    requires true;
    ensures (n < 0) ? nth_of(n,b64_chars()) == none
        :   (n < 26)
            ? nth_of(n,b64_chars()) == some('A'+n)
        :   (n-26 < 26)
            ? nth_of(n,b64_chars()) == some('a'+(n-26))
        :   (n-52 < 10)
            ? nth_of(n,b64_chars()) == some('0'+(n-52))
        :   (n <= 62)
            ? (n == 62 &*& nth_of(n,b64_chars()) == some('+'))
        :   (n <= 63)
            ? (n == 63 &*& nth_of(n,b64_chars()) == some('/'))
        :   nth_of(n,b64_chars()) == none;
{ ALREADY_PROVEN() }

  @*/


char b64_of_byte(uint8_t n)
    /*@ requires 0 <= n &*& n < 64; @*/
    /*@ ensures  some(result) == nth_of(n,b64_chars()); @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    /*@ b64_cases(n); @*/
    uint8_t thresh0 = (uint8_t)('Z'-'A');
    uint8_t thresh1 = (uint8_t)('z'-'a' + thresh0 + 1);
    uint8_t thresh2 = (uint8_t)('9'-'0' + thresh1 + 1);

    if(n >= 64)             { /*@ assert false; @*/ abort();      }
    else if(n <= thresh0)   { return (char)('A' + n);             }
    else if(n <= thresh1)   { return (char)('a' + (n-thresh0-1)); }
    else if(n <= thresh2)   { return (char)('0' + (n-thresh1-1)); }
    else if(n <= thresh2+1) { return (char)('+');                 }
    else if(n <= thresh2+2) { return (char)('/');                 }
    else                    { /*@ assert false; @*/ abort();      }
}

/*@

// in little-endian order
predicate base_n(list<char> place_vals, list<char> symbs;
                 list<int>  seq, int val) =
         place_vals != nil
    &*&  !!distinct(place_vals)
    &*& switch(symbs) {
    case nil: return seq == {} &*& val == 0;
    case cons(s,ss):
        return  base_n(place_vals,ss,?rest,?rest_val)
            &*& !!mem(s,place_vals)
            &*& let(index_of(s,place_vals),?v)
            &*& seq == cons(v,rest)
            &*& val == v + length(place_vals)*rest_val
            ;
    };

lemma_auto void base_n_inv()
    requires [?f]base_n(?place_vals,?symbs,?seq,?val);
    ensures  [ f]base_n( place_vals, symbs, seq, val)
        &*&  place_vals != nil
        &*&  !!distinct(place_vals)
        &*&  length(seq) == length(symbs)
        &*&  !!forall(symbs,(flip)(mem,place_vals))
        &*&  !!forall(seq,(bounded)(0,length(place_vals)-1))
        &*&  poly_eval(seq,length(place_vals)) == val;
{
    if(!(place_vals != nil
        &&  distinct(place_vals)
        &&  length(seq) == length(symbs)
        &&  !!forall(symbs,(flip)(mem,place_vals))
        &&  !!forall(seq,(bounded)(0,length(place_vals)-1))
        &&  poly_eval(seq,length(place_vals)) == val)) {
        open base_n(_,_,_,_);
        switch(symbs) {
        case nil:
        case cons(s,ss):
            base_n_inv();
        }
        assert false;
    }
}

lemma void base_n_dup()
    requires [?f]base_n(?place_vals,?symbs,?seq,?val);
    ensures  [ f]base_n( place_vals, symbs, seq, val)
        &*&      base_n( place_vals, symbs, seq, val);
{
    switch(symbs) {
    case nil:
    case cons(s,ss):
        open base_n(_,_,_,_);
        base_n_dup();
        close [f]base_n( place_vals, symbs, seq, val);
        close    base_n( place_vals, symbs, seq, val);
    }
}

lemma void base_n_split(list<char> symbs_l,list<char> symbs_r)
    requires [?f1]base_n(?place_vals,append(symbs_l,symbs_r),?seq,?val);
    ensures  [ f1]base_n( place_vals,symbs_l, ?seq_l,?v_l)
        &*&  [ f1]base_n( place_vals,symbs_r, ?seq_r,?v_r)
        &*&  seq == append(seq_l,seq_r)
        &*&  val == v_l
                    + pow_nat(length(place_vals),
                              nat_of_int(length(symbs_l)))*v_r;
{
    switch(symbs_l) {
    case nil:
        close [f1]base_n(place_vals,nil,nil,0);
    case cons(x,xs):
        open base_n(_,_,_,_);
        assert [f1]base_n(_,_,_,?v_suff);
        base_n_split(xs,symbs_r);

        assert [f1]base_n(place_vals,xs,_,?v_xs);
        assert [f1]let(index_of(x,place_vals),?v);

        close [f1]base_n(place_vals,symbs_l,_,?v_l);
        assert [f1]base_n(place_vals,symbs_r,_,?v_r);

        assert val == v + length(place_vals)*v_suff;

        assert v_suff == v_xs
                       + pow_nat(length(place_vals),
                                 nat_of_int(length(xs)))*v_r;

        assert val == v
                + length(place_vals)*(v_xs
                    + pow_nat(length(place_vals),
                                 nat_of_int(length(xs)))*v_r);
        note_eq( length(place_vals)*(v_xs
                    + pow_nat(length(place_vals),
                                 nat_of_int(length(xs)))*v_r)
            ,  length(place_vals)*v_xs
                    + length(place_vals)*(pow_nat(length(place_vals),
                                 nat_of_int(length(xs)))*v_r));

        assert val == (v + length(place_vals)*v_xs)
                    + length(place_vals)*(pow_nat(length(place_vals),
                                 nat_of_int(length(xs)))*v_r);

        mul_assoc(length(place_vals),pow_nat(length(place_vals),
                                 nat_of_int(length(xs))),v_r);

        assert val == v_l
                    + (pow_nat(length(place_vals),
                               nat_of_int(length(symbs_l)))*v_r);

    }
}

lemma void base_n_append(list<char> symbs_l,list<char> symbs_r)
    requires [?f1]base_n(?place_vals,symbs_l,?seq_l,?val_l)
        &*&  [?f2]base_n( place_vals,symbs_r,?seq_r,?val_r);
    ensures  [f2]base_n(place_vals,append(symbs_l,symbs_r),
                    append(seq_l,seq_r),
                    val_l
                    + val_r*pow_nat(length(place_vals),
                                    nat_of_int(length(symbs_l))));
{
    switch(symbs_l) {
    case nil:
        open base_n(_,symbs_l,_,_);
    case cons(s,ss):
        open base_n(_,symbs_l,_,_);
        assert [f1]base_n(_,ss,?seq_ss,?val_ss);
        base_n_append(ss,symbs_r);
        assert [f2]base_n(_,append(ss,symbs_r),?seq_rest,?val_res);

        assert nat_of_int(length(symbs_l))
            == succ(nat_of_int(length(ss)));

        assert [f1]let(index_of(s,place_vals),?v);

        assert val_l == v + length(place_vals)*val_ss;

        assert val_res == val_ss
            + val_r*pow_nat(length(place_vals),
                                    nat_of_int(length(ss)));

        close [f2]base_n(place_vals,append(symbs_l,symbs_r),
                    append(seq_l,seq_r),
                    ?val_final);

        assert val_final == v
            + length(place_vals)*(val_ss
                    + val_r*pow_nat(length(place_vals),
                                    nat_of_int(length(ss))));

        mul_3var(val_r,length(place_vals),
                pow_nat(length(place_vals), nat_of_int(length(ss))));

    }
}

  @*/

uint8_t* bytes_of_hex(size_t len, char* s, size_t* outlen)
    /*@ requires [?f]s[..len] |-> ?hex_str &*& *outlen |-> _
            &*&  base_n(hex_chars(),reverse(hex_str),?hexits,?val)
            &*&  len%2 == 0
            ; @*/
    /*@ ensures  [ f]s[..len] |->  hex_str &*& *outlen |-> ?len_out
            &*&  base_n(hex_chars(),reverse(hex_str), hexits, val)
            &*&  result[..len_out] |-> ?out_bytes
            &*&  malloc_block_uchars(result,len_out)
            &*&  poly_eval(reverse(out_bytes),256) == val
            ; @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    uint8_t* ret;
    uint8_t* p;
    size_t i;
    *outlen = len/2;

    /*@ assert *outlen |-> ?len_out; @*/
    /*@ div_rem(len,2); @*/

    ret = calloc(*outlen,sizeof(uint8_t));
    if(!ret) { abort(); }

    /*@ base_n_dup(); @*/

    for(i = 0,p = ret; i < len; i+=2,++p)
        /*@ requires [f]s[i..len] |-> ?loop_hex
                &*&  ret[i/2..len_out] |-> _
                &*&  p == ret+(i/2)
                &*&  i%2 == 0
                &*&  i >= 0 &*& i <= len
                &*&  base_n(hex_chars(),reverse(loop_hex),
                        ?loop_hexits,?loop_val)
                ; @*/
        /*@ ensures  [f]s[old_i..len] |-> loop_hex
                &*&  ret[old_i/2..len_out] |-> ?bytes
                &*&  poly_eval(reverse(bytes),pow_nat(2,N8))
                        == loop_val
                ; @*/
        /*@ decreases len-i; @*/
    {
        /*@ {
            div_rem(i,2);
            if(i+1 >= len) {
                division_unique(i+1,2,i/2,1);
                assert false;
            }
            division_unique(i+2,2,i/2+1,0);
        } @*/

        /*@ open chars(s+i,_,_); @*/
        /*@ assert [f]s[i]        |-> ?x1; @*/
        /*@ assert [f]s[i+1..len] |-> ?xs1; @*/
        /*@ base_n_split(reverse(xs1),{x1}); @*/
        /*@ open chars(s+i+1,_,_); @*/
        /*@ assert [f]s[i+1]      |-> ?x2; @*/
        /*@ assert [f]s[i+2..len] |-> ?xs2; @*/
        /*@ base_n_split(reverse(xs2),{x2}); @*/
        /*@ open base_n(_,{x1},_,_); @*/
        /*@ open base_n(_,{x2},_,_); @*/

        uint8_t h = nib_of_hex(s[i  ]);
        uint8_t l = nib_of_hex(s[i+1]);

        /*@ assert base_n(hex_chars(),
                reverse(xs2), ?rest_hexits,
                ?rest_val); @*/
        /*@ {
            index_of_witness(h,x1,hex_chars());
            index_of_witness(l,x2,hex_chars());

            shiftleft_def(h,N4);
            bitor_no_overlap(h,l,N4);
            open uchars(ret+(i/2),_,_);
            div_monotonic_numerator(i,len-1,2);
            assert i/2 <= (len-1)/2;

            if(!((len-1)/2 < len/2)) {
                div_monotonic_numerator(len-1,len,2);
                assert (len-1)/2 == len/2;
                div_rem(len-1,2);
                assert false;
            }

            assert i/2 <  len/2;
        } @*/

        *p = (uint8_t)((h<<4) | l);

        /*@ assert *p |-> ?v; @*/
        /*@ {
            assert v == h*16+l;
            assert loop_val
                == rest_val
                + pow_nat(16,nat_of_int(length(rest_hexits)))
                    *v;

            note_eq(length(rest_hexits),len-2-i);

            assert loop_val
                == rest_val
                + pow_nat(16,nat_of_int(len-2-i))
                    *(h*16 + l);

            division_unique(len-2-i,2,len/2-1-i/2,0);
            assert 2*((len-2-i)/2) == len-2-i;

            assert loop_val
                == rest_val
                + pow_nat(16,nat_of_int(2*((len-2-i)/2)))
                    *(h*16 + l);
            pow_times2(16,N2,(len-2-i)/2);
            assert loop_val
                == rest_val
                + pow_nat(16*16,nat_of_int(((len-2-i)/2)))
                    *v;
        } @*/
    }

    return ret;
}

char* hex_of_bytes(size_t len, uint8_t* b)
    /*@ requires [?f]b[..len] |-> ?bytes
            &*&  2*len+1 <= ULONG_MAX
            ; @*/
    /*@ ensures  [ f]b[..len] |->  bytes
            &*&  string(result,?hex_str)
            &*&  length(hex_str) == 2*len
            &*&  base_n(hex_chars(),reverse(hex_str),_,?val)
            &*&  malloc_block_chars(result,_)
            &*&  poly_eval(reverse(bytes),256) == val
            ; @*/
    /*@ terminates; @*/
{
    char* ret;
    char* p;
    size_t i;
    ret = calloc(2*len+1,sizeof(char));
    if(!ret) { abort(); }

    for(i = 0,p = ret; i < len; ++i,p+=2)
        /*@ requires [f]b[i..len] |-> ?loop_bytes
                &*&  ret[2*i..2*len+1] |-> _
                &*&  i >= 0 &*& i <= len
                &*&  p == ret+2*i
                ; @*/
        /*@ ensures  [f]b[old_i..len]    |->  loop_bytes
                &*&  ret[2*old_i..2*len] |-> ?loop_hex
                &*&  !mem('\0',loop_hex)
                &*&  ret[2*len] |-> _
                &*&  base_n(hex_chars(),reverse(loop_hex),_,?loop_val)
                &*&  poly_eval(reverse(loop_bytes),256) == loop_val
                ; @*/
        /*@ decreases len-i; @*/
    {
        /*@ open uchars(b+i,_,_); @*/
        /*@ open  chars(p,_,_); @*/
        /*@ open  chars(p+1,_,_); @*/
        /*@ assert [f]b[i]        |-> ?x; @*/
        /*@ assert [f]b[i+1..len] |-> ?xs; @*/
        /*@ {
            u_character_limits(b+i);
            shiftright_div(x,N4);
            bitand_pow_2(x,N4);
            div_rem(x,16);
        } @*/
        p[0] = hex_of_nib((uint8_t)(b[i]>>4));
        p[1] = hex_of_nib((uint8_t)(b[i]&0xf));

        /*@ assert p[0] |-> ?c1; @*/
        /*@ assert p[1] |-> ?c2; @*/
        /*@ {
            index_of_witness(x/16,c1,hex_chars());
            index_of_witness(x%16,c2,hex_chars());
        } @*/

        /*@ recursive_call(); @*/

        /*@ {
            assert ret[2*(old_i+1)..2*len] |-> ?rest_hex;
            assert base_n(hex_chars(),reverse(rest_hex),_,?rest_val);
            close base_n(hex_chars(),{c1},{x/16},x/16);
            close base_n(hex_chars(),{c2,c1},{x%16,x/16},x);
            base_n_append(reverse(rest_hex),{c2,c1});
            append_assoc(reverse(rest_hex),{c2},{c1});
            assert base_n(hex_chars(),
                reverse(cons(c1,cons(c2,rest_hex))),_,?final_val);
            assert final_val == rest_val +
                pow_nat(16,nat_of_int(length(rest_hex)))*x;
            pow_times2(16,N2,len-1-old_i);
        } @*/
    }
    ret[2*len] = '\0';

    return ret;
}

char* b64_of_bytes(size_t len, uint8_t *b)
{
    // not a fan of this expression but it's correct
    size_t n_padding = (3-len%3)%3;
    size_t out_len = ((len+n_padding)/3)*4;
    size_t i;
    char* p;
    char* ret = calloc(out_len+1,sizeof(char));

    if(!ret) { abort(); }

    for(i = 0,p = ret; i < len; p+=4,i+=3) {
        p[0] = b64_of_byte(b[i]>>2);

        if(i+1 >= len) {
            p[1] = b64_of_byte((b[i  ]&0x03)<<4);
            break;
        } else {
            p[1] = b64_of_byte((b[i  ]&0x03)<<4 | b[i+1]>>4);
        }

        if(i+2 >= len) {
            p[2] = b64_of_byte((b[i+1]&0x0f)<<2);
            break;
        } else {
            p[2] = b64_of_byte((b[i+1]&0x0f)<<2 | b[i+2]>>6);
        }

        p[3] = b64_of_byte((b[i+2]&0x3f));
    }

    // Coincidentally, there will be exactly n_padding padding bytes
    // to output, even though the calculation mod 3 and the number
    // left in the group of 4 seem unrelated at first glance (check
    // the cases).

    for(i = 0; i < n_padding; ++i) {
        p[3-n_padding+i] = '=';
    }

    return ret;
}

#endif

