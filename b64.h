#ifndef VFSTUFF_B64_H
#define VFSTUFF_B64_H

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <malloc.h>
#include <stdbool.h>
/*@ #include "lists.gh" @*/
/*@ #include "poly.gh" @*/
/*@ #include "bitops.gh" @*/

#ifndef __FILE__
#define calloc(a,b) malloc((a)*b)
#ifndef INLINE
#define INLINE static inline
#endif
#else
#ifndef INLINE
#define INLINE static inline
#endif
#endif

/*@
#if 1
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() assume(false);
#endif
@*/

/*@

fixpoint list<char> hex_chars() {
    return "0123456789abcdef";
}

lemma void in_range1_hex_chars(char c);
    requires (c >= 'a' && c <= 'f');
    ensures  !!mem(c,hex_chars());

lemma void in_range2_hex_chars(char c);
    requires (c >= '0' && c <= '9');
    ensures  !!mem(c,hex_chars());

lemma_auto(mem(c,hex_chars()))
void hex_chars_range(char c);
    requires true;
    ensures  mem(c,hex_chars())
        ==   ((c >= 'a' && c <= 'f') || (c >= '0' && c <= '9'));

  @*/

bool is_hex(char c);
    /*@ requires true; @*/
    /*@ ensures  result == mem(c,hex_chars()); @*/
    /*@ terminates; @*/

char hex_of_nib(uint8_t c);
    /*@ requires c >= 0 &*& c < 16; @*/
    /*@ ensures  some(result) == nth_of(c,hex_chars())
            &*&  !!mem(result,hex_chars())
            &*&  index_of(result,hex_chars()) == c
            ; @*/
    /*@ terminates; @*/

uint8_t nib_of_hex(char c);
    /*@ requires !!mem(c,hex_chars()); @*/
    /*@ ensures  some(c) == nth_of(result,hex_chars())
            &*&  index_of(c,hex_chars()) == result
            &*&  0 <= result &*& result < length(hex_chars())
            ; @*/
    /*@ terminates; @*/

/*@

fixpoint list<char> b64_chars() {
    return "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz"
           "0123456789+/";
}

lemma void in_range1_b64_chars(char c);
    requires (c >= 'a' && c <= 'f');
    ensures  !!mem(c,b64_chars());

lemma void in_range2_b64_chars(char c);
    requires (c >= 'A' && c <= 'Z');
    ensures  !!mem(c,b64_chars());

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


char b64_of_byte(uint8_t n);
    /*@ requires 0 <= n &*& n < 64; @*/
    /*@ ensures  some(result) == nth_of(n,b64_chars()); @*/
    /*@ terminates; @*/

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

lemma_auto void base_n_inv();
    requires [?f]base_n(?place_vals,?symbs,?seq,?val);
    ensures  [ f]base_n( place_vals, symbs, seq, val)
        &*&  val >= 0
        &*&  place_vals != nil
        &*&  !!distinct(place_vals)
        &*&  length(seq) == length(symbs)
        &*&  !!forall(symbs,(flip)(mem,place_vals))
        &*&  !!forall(seq,(bounded)(0,length(place_vals)-1))
        &*&  all_eq(symbs,head(place_vals)) == (val == 0)
        &*&  poly_eval(seq,length(place_vals)) == val
        &*&  map(some,symbs) == map((flip)(nth_of,place_vals),seq)
        &*&  seq == map((flip)(index_of,place_vals),symbs)
        ;

lemma void base_n_dup();
    requires [?f]base_n(?place_vals,?symbs,?seq,?val);
    ensures  [ f]base_n( place_vals, symbs, seq, val)
        &*&      base_n( place_vals, symbs, seq, val);

lemma void base_n_split(list<char> symbs_l,list<char> symbs_r);
    requires [?f1]base_n(?place_vals,append(symbs_l,symbs_r),?seq,?val);
    ensures  [ f1]base_n( place_vals,symbs_l, ?seq_l,?v_l)
        &*&  [ f1]base_n( place_vals,symbs_r, ?seq_r,?v_r)
        &*&  seq == append(seq_l,seq_r)
        &*&  val == v_l
                    + pow_nat(length(place_vals),
                              nat_of_int(length(symbs_l)))*v_r;

lemma void base_n_append(list<char> symbs_l,list<char> symbs_r);
    requires [?f1]base_n(?place_vals,symbs_l,?seq_l,?val_l)
        &*&  [?f2]base_n( place_vals,symbs_r,?seq_r,?val_r);
    ensures  [f2]base_n(place_vals,append(symbs_l,symbs_r),
                    append(seq_l,seq_r),
                    val_l
                    + val_r*pow_nat(length(place_vals),
                                    nat_of_int(length(symbs_l))));

lemma void base_n_nonzero(char p0, list<char> ps, list<char> symbs,
                       char witness);
    requires [?f]base_n(cons(p0,ps),symbs,?seq,?val)
        &*&  !!mem(witness,symbs)
        &*&  witness != p0
        ;
    ensures  [ f]base_n(cons(p0,ps),symbs, seq, val)
        &*&  val != 0;

lemma void base_n_trim(char p0, list<char> ps, list<char> symbs,
                       int suff_len);
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

  @*/

uint8_t* bytes_of_hex(size_t len, char* s, size_t* outlen);
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

char* hex_of_bytes(size_t len, uint8_t* b);
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

/* @

predicate b64_string(list<char> s; nat n_padding,
                     list<char> b64_str,list<int> b64_seq,
                     list<int> bytes,int val)
    = switch(s) {
    case nil:
        return  b64_str == nil
            &*& base_n(b64_chars(), b64_str,b64_seq,val)
            &*& bytes == {};
    case cons(c0,cs0):
        return switch(cs0) {
        case nil: return false;
        case cons(c1,cs1):
            return switch(cs1) {
            case nil: return false;
            case cons(c2,cs2):
                return switch(cs2) {
                case nil: return false;
                case cons(c3,cs3):
                    return  switch(c3) {
                    case nil:

                        return (c1 == '=')
                            ?   n_padding == N3
                            &*& c2 == '=' &*& c3 == '='
                            &*& b64_str == {c0}
                            &*& base_n(b64_chars(),reverse(b64_str),
                                       ?rev_seq,val)
                            &*& b64_seq == reverse(rev_seq)

                            : (c2 == '=')
                            ?   n_padding == N2
                            &*& c3 == '='
                            &*& b64_str == {c0,c1}
                            &*& base_n(b64_chars(),reverse(b64_str),
                                       ?rev_seq,val)
                            &*& b64_seq == reverse(rev_seq)

                            : (c3 == '=')
                            ?   n_padding == N1
                            &*& b64_str == {c0,c1,c2}
                            &*& base_n(b64_chars(),reverse(b64_str),
                                       ?rev_seq,val)
                            &*& b64_seq == reverse(rev_seq)

                            :   n_padding == zero
                            &*& b64_str == {c0,c1,c2,c3}
                            &*& base_n(b64_chars(),reverse(b64_str),
                                       ?rev_seq,val)
                            &*& b64_seq == reverse(rev_seq)
                            ;

                    case cons(c4,cs4):
                        return b64_string(cs3, n_padding, ?b64_rest,
                                          ?seq_rest, ?bytes_rest,
                                          ?rest_val)
                        &*& base_n(b64_chars(),reverse({c0,c1,c2,c3}),
                                   ?pref_seq, ?pref_val)
                        &*& b64_str == append({c0,c1,c2,c3},b64_rest)
                        &*& base_n(b64_chars(), reverse(b64_str),
                                   ?rev_seq,val)
                        &*& b64_seq == reverse(rev_seq)
                        &*& bytes
                            == cons(pref_val/256/256,
                               cons((pref_val/256)%256,
                               cons(pref_val%256,bytes_rest)))

                        // should be consequences
                        &*& b64_seq == append(seq_rest,pref_seq)
                        &*& b64_str == append(s,repeat('=',n_padding))
                        ;

                    };
                };
            };
        };
    };

lemma_auto b64_string_inv()
    requires [?f]b64_string(?s,?n_padding,?b64_str,?b64_seq,?bytes,
             ?val);
    ensures  [ f]b64_string( s, n_padding, b64_str, b64_seq, bytes,
              val)
        &*&  length(b64_str) == length(b64_seq)
        &*&  3*length(bytes) == 4*length(s)
        &*&  length(s)%3 == 0
        &*&  int_of_nat(n_padding) < 3
        &*&  s == append(b64_str,repeat('=',n_padding))
        &*&  val == poly_eval(reverse(b64_seq),64)
        &*&  val == poly_eval(reverse(bytes),256)
        &*&  !!forall(b64_str,(flip)(mem,b64_chars()))
        ;

  @*/

//char* b64_of_bytes(size_t len, uint8_t *b)
//    /*@ requires [?f]b[..len] |-> ?bytes
//            &*&  2*len+1 <= ULONG_MAX
//            ; @*/
//    /*@ ensures  [ f]b[..len] |->  bytes
//            &*&  string(result,?b64_str)
//            &*&  length(hex_str) == 2*len
//            &*&  base_n(hex_chars(),reverse(hex_str),_,?val)
//            &*&  malloc_block_chars(result,_)
//            &*&  poly_eval(reverse(bytes),256) == val
//            ; @*/
//    /*@ terminates; @*/
//{
//    // not a fan of this expression but it's correct
//    size_t n_padding = (3-len%3)%3;
//    size_t out_len = ((len+n_padding)/3)*4;
//    size_t i;
//    char* p;
//    char* ret = calloc(out_len+1,sizeof(char));
//
//    if(!ret) { abort(); }
//
//    for(i = 0,p = ret; i < len; p+=4,i+=3) {
//        p[0] = b64_of_byte(b[i]>>2);
//
//        if(i+1 >= len) {
//            p[1] = b64_of_byte((b[i  ]&0x03)<<4);
//            break;
//        } else {
//            p[1] = b64_of_byte((b[i  ]&0x03)<<4 | b[i+1]>>4);
//        }
//
//        if(i+2 >= len) {
//            p[2] = b64_of_byte((b[i+1]&0x0f)<<2);
//            break;
//        } else {
//            p[2] = b64_of_byte((b[i+1]&0x0f)<<2 | b[i+2]>>6);
//        }
//
//        p[3] = b64_of_byte((b[i+2]&0x3f));
//    }
//
//    // Coincidentally, there will be exactly n_padding padding bytes
//    // to output, even though the calculation mod 3 and the number
//    // left in the group of 4 seem unrelated at first glance (check
//    // the cases).
//
//    for(i = 0; i < n_padding; ++i) {
//        p[3-n_padding+i] = '=';
//    }
//
//    return ret;
//}

#endif


