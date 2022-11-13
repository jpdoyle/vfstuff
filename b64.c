#include "b64.h"

#if 1
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() assume(false);
#endif


/*@
lemma void in_range1_hex_chars(char c)
    requires (c >= 'a' && c <= 'f');
    ensures  !!mem(c,hex_chars());
{
    ALREADY_PROVEN()
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
    /*@ ALREADY_PROVEN() @*/
    return (c >= 'a' && c <= 'f') || (c >= '0' && c <= '9');
}

char hex_of_nib(uint8_t c)
    /*@ requires c >= 0 &*& c < 16; @*/
    /*@ ensures  some(result) == nth_of(c,hex_chars())
            &*&  !!mem(result,hex_chars())
            &*&  index_of(result,hex_chars()) == c
            ; @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    /*@ nth_of_index_of(c,hex_chars()); @*/
    if(c < 10)      { return (char)('0'+c);      }
    else if(c < 16) { return (char)('a'+(c-10)); }
    else { /*@ assert false; @*/ abort(); } //~allow_dead_code
}

uint8_t nib_of_hex(char c)
    /*@ requires !!mem(c,hex_chars()); @*/
    /*@ ensures  some(c) == nth_of(result,hex_chars())
            &*&  index_of(c,hex_chars()) == result
            &*&  0 <= result &*& result < length(hex_chars())
            ; @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/
    if(c >= 'a' && c <= 'f') {
        return (uint8_t)(10 + (c-'a'));
    } else if(c >= '0' && c <= '9') {
        return (uint8_t)(c-'0');
    } else { /*@ assert false; @*/ abort(); } //~allow_dead_code
}


/*@

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
    // else if(c < 'h') {}
    // else if(c < 'i') {}
    // else if(c < 'j') {}
    // else if(c < 'k') {}
    // else if(c < 'l') {}
    // else if(c < 'm') {}
    // else if(c < 'n') {}
    // else if(c < 'o') {}
    // else if(c < 'p') {}
    // else if(c < 'q') {}
    // else if(c < 'r') {}
    // else if(c < 's') {}
    // else if(c < 't') {}
    // else if(c < 'u') {}
    // else if(c < 'v') {}
    // else if(c < 'w') {}
    // else if(c < 'x') {}
    // else if(c < 'y') {}
    // else if(c < 'z') {}
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


lemma_auto void base_n_inv()
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
{
    ALREADY_PROVEN()
    if(!(place_vals != nil
        &&  val >= 0
        &&  distinct(place_vals)
        &&  length(seq) == length(symbs)
        &&  !!forall(symbs,(flip)(mem,place_vals))
        &&  !!forall(seq,(bounded)(0,length(place_vals)-1))
        &&  all_eq(symbs,head(place_vals)) == (val == 0)
        &&  poly_eval(seq,length(place_vals)) == val
        &&  map(some,symbs) == map((flip)(nth_of,place_vals),seq)
        &&  seq == map((flip)(index_of,place_vals),symbs)
        )) {
        open base_n(_,_,_,_);
        switch(symbs) {
        case nil:
        case cons(s,ss):
            base_n_inv();
            assert  [ f]base_n( place_vals, ss, _, ?rest_val);
            //cons_head_tail(seq);
            cons_head_tail(place_vals);
            assert val == head(seq) + length(place_vals)*rest_val;
            assert !!mem(s,place_vals);
            assert head(seq) == index_of(s,place_vals);
            mem_index_of(s,place_vals);
            my_mul_mono_r(length(place_vals),0,rest_val);
            my_mul_mono_l(1,length(place_vals),rest_val);
            assert length(place_vals)*rest_val >= 0;
            if(s != head(place_vals)) {
                mem_index_of(s,tail(place_vals));
                assert head(seq) > 0;
                note(val > 0);
                if(val == 0) assert false;
            } else if(all_eq(ss,head(place_vals))) {
            } else {
                assert val > 0;
                if(val == 0) assert false;
            }
        }
        assert false;
    }
}


lemma void base_n_dup()
    requires [?f]base_n(?place_vals,?symbs,?seq,?val);
    ensures  [ f]base_n( place_vals, symbs, seq, val)
        &*&      base_n( place_vals, symbs, seq, val);
{
    ALREADY_PROVEN()
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
                              noi(length(symbs_l)))*v_r;
{
        ALREADY_PROVEN()
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
                                 noi(length(xs)))*v_r;

        assert val == v
                + length(place_vals)*(v_xs
                    + pow_nat(length(place_vals),
                                 noi(length(xs)))*v_r);
        note_eq( length(place_vals)*(v_xs
                    + pow_nat(length(place_vals),
                                 noi(length(xs)))*v_r)
            ,  length(place_vals)*v_xs
                    + length(place_vals)*(pow_nat(length(place_vals),
                                 noi(length(xs)))*v_r));

        assert val == (v + length(place_vals)*v_xs)
                    + length(place_vals)*(pow_nat(length(place_vals),
                                 noi(length(xs)))*v_r);

        mul_assoc(length(place_vals),pow_nat(length(place_vals),
                                 noi(length(xs))),v_r);

        assert val == v_l
                    + (pow_nat(length(place_vals),
                               noi(length(symbs_l)))*v_r);

    }
}


lemma void base_n_append(list<char> symbs_l,list<char> symbs_r)
    requires [?f1]base_n(?place_vals,symbs_l,?seq_l,?val_l)
        &*&  [?f2]base_n( place_vals,symbs_r,?seq_r,?val_r);
    ensures  [f2]base_n(place_vals,append(symbs_l,symbs_r),
                    append(seq_l,seq_r),
                    val_l
                    + val_r*pow_nat(length(place_vals),
                                    noi(length(symbs_l))));
{
        ALREADY_PROVEN()
    switch(symbs_l) {
    case nil:
        open base_n(_,symbs_l,_,_);
    case cons(s,ss):
        open base_n(_,symbs_l,_,_);
        assert [f1]base_n(_,ss,?seq_ss,?val_ss);
        base_n_append(ss,symbs_r);
        assert [f2]base_n(_,append(ss,symbs_r),?seq_rest,?val_res);

        assert noi(length(symbs_l))
            == succ(noi(length(ss)));

        assert [f1]let(index_of(s,place_vals),?v);

        assert val_l == v + length(place_vals)*val_ss;

        assert val_res == val_ss
            + val_r*pow_nat(length(place_vals),
                                    noi(length(ss)));

        close [f2]base_n(place_vals,append(symbs_l,symbs_r),
                    append(seq_l,seq_r),
                    ?val_final);

        assert val_final == v
            + length(place_vals)*(val_ss
                    + val_r*pow_nat(length(place_vals),
                                    noi(length(ss))));

        mul_3var(val_r,length(place_vals),
                pow_nat(length(place_vals), noi(length(ss))));

    }
}

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
    switch(symbs) {
    case nil: assert false;
    case cons(c,cs):
    ALREADY_PROVEN()
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

uint8_t* bytes_of_hex(size_t len, char* s, size_t* outlen)
    /*@ requires [?f]s[..len] |-> ?hex_str &*& *outlen |-> _
            &*&  base_n(hex_chars(),reverse(hex_str),?hexits,?val)
            &*&  len%2 == 0
            ; @*/
    /*@ ensures  [ f]s[..len] |->  hex_str &*& *outlen |-> ?len_out
            &*&  base_n(hex_chars(),reverse(hex_str), hexits, val)
            &*&  result[..len_out] |-> ?out_bytes
            &*&  malloc_block_uchars((unsigned char*)result,len_out)
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

    /*@ assert sizeof(unsigned char) == sizeof(uint8_t); @*/
    ret = calloc(*outlen,sizeof(unsigned char));
    if(!ret) { abort(); }

    /*@ base_n_dup(); @*/

    for(i = 0,p = ret; i < len; i+=2,++p)
        /*@ requires [f]s[i..len] |-> ?loop_hex
                &*&  ((unsigned char*)ret)[i/2..len_out] |-> _
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
            open uchars_((unsigned char*)(ret+(i/2)),_,_);
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
                + pow_nat(16,noi(length(rest_hexits)))
                    *v;

            note_eq(length(rest_hexits),len-2-i);

            assert loop_val
                == rest_val
                + pow_nat(16,noi(len-2-i))
                    *(h*16 + l);

            division_unique(len-2-i,2,len/2-1-i/2,0);
            assert 2*((len-2-i)/2) == len-2-i;

            assert loop_val
                == rest_val
                + pow_nat(16,noi(2*((len-2-i)/2)))
                    *(h*16 + l);
            pow_times2(16,N2,(len-2-i)/2);
            assert loop_val
                == rest_val
                + pow_nat(16*16,noi(((len-2-i)/2)))
                    *v;
        } @*/
    }

    return ret;
}

char b64_of_byte(uint8_t n)
    /*@ requires 0 <= n &*& n < 64; @*/
    /*@ ensures  some(result) == nth_of(n,b64_chars()); @*/
    /*@ terminates; @*/

{
    /*@  ALREADY_PROVEN() @*/
    /*@ b64_cases(n); @*/
    uint8_t thresh0 = (uint8_t)('Z'-'A');
    uint8_t thresh1 = (uint8_t)('z'-'a' + thresh0 + 1);
    uint8_t thresh2 = (uint8_t)('9'-'0' + thresh1 + 1);

    if(n >= 64)             { /*@ assert false; @*/ abort(); }//~allow_dead_code
    else if(n <= thresh0)   { return (char)('A' + n);             }
    else if(n <= thresh1)   { return (char)('a' + (n-thresh0-1)); }
    else if(n <= thresh2)   { return (char)('0' + (n-thresh1-1)); }
    else if(n <= thresh2+1) { return (char)('+');                 }
    else if(n <= thresh2+2) { return (char)('/');                 }
    else                    { /*@ assert false; @*/ abort(); }//~allow_dead_code
}


char* hex_of_bytes(size_t len, uint8_t* b)
    /*@ requires [?f]b[..len] |-> ?bytes
            &*&  2*len+1 <= ULONG_MAX
            ; @*/
    /*@ ensures  [ f]b[..len] |->  bytes
            &*&  string(result,?hex_str)
            &*&  length(hex_str) == 2*len
            &*&  base_n(hex_chars(),reverse(hex_str),_,?val)
            &*&  malloc_block_chars((char*)result,_)
            &*&  poly_eval(reverse(bytes),256) == val
            ; @*/
    /*@ terminates; @*/
{
    /* @ ALREADY_PROVEN() @*/
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
        /*@ open integers_(b+i,_,_,_,_); @*/
        /*@ open  chars_(p,_,_); @*/
        /*@ open  chars_(p+1,_,_); @*/
        /*@ assert [f]b[i]        |-> ?x; @*/
        /*@ assert [f]b[i+1..len] |-> ?xs; @*/
        /*@ {
            integer__limits(b+i);
            shiftleft_def(1,N8);
            assert x < 256;
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
                pow_nat(16,noi(length(rest_hex)))*x;
            pow_times2(16,N2,len-1-old_i);
        } @*/
    }
    ret[2*len] = '\0';

    return ret;
}

