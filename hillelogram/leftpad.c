#include <string.h>
#include <stdlib.h>
/*@ #include <nat.gh> @*/
/*@ #include <listex.gh> @*/

/*@

lemma_auto(length(l))
void length_zero_iff_nil<t>(list<t> l)
    requires true;
    ensures  (length(l) == 0) == (l == nil);
{ switch(l) { case nil: case cons(x,xs): } }

lemma_auto void character_limits_auto()
    requires [?f]character(?pc, ?c);
    ensures  [ f]character( pc,  c)
        &*&  pc > (char *)0
        &*&  pc < (char *)UINTPTR_MAX
        &*&  -128 <= c
        &*&  c <= 127;
{ character_limits(pc); }


lemma_auto void string_limits_auto()
    requires [?f]string(?s, ?cs);
    ensures  [ f]string( s,  cs)
        &*&  true == ((char *)0 < s)
        &*&  s + length(cs) < (char *)UINTPTR_MAX;
{ string_limits(s); }

lemma_auto void chars_limits_auto()
    requires [?f]chars(?array, ?n, ?cs)
        &*&  (char *)0 <= array
        &*&  array <= (char *)UINTPTR_MAX;
    ensures  [ f]chars( array,  n,  cs)
        &*&  (char *)0 <= array
        &*&  array + n <= (char *)UINTPTR_MAX;
{ chars_limits(array); }

lemma void chars_string_join(char* c)
    requires [?f]chars(c,?n,?cs) &*& [f]string(c+n, ?s)
        &*&  !mem('\0',cs);
    ensures  [ f]string(c,append(cs,s));
{
    open chars(_,_,_);
    if(n != 0) {
        chars_string_join(c+1);
    }
}

fixpoint list<char> repchar(nat n, char c) {
    switch(n) {
    case zero:      return {};
    case succ(n0):  return cons(c,repchar(n0,c));
    }
}

lemma_auto(mem(x,repchar(n,c)))
void repchar_mem(char x, nat n, char c)
    requires true;
    ensures  mem(x,repchar(n,c)) == (n != zero && x == c);
{
    switch(n) {
    case zero:
    case succ(n0):
        repchar_mem(x,n0,c);
    }
}

lemma_auto(length(repchar(n,c)))
void length_repchar(nat n, char c)
    requires true;
    ensures  length(repchar(n,c)) == ion(n);
{
    switch(n) {
    case zero:
    case succ(n0):
        length_repchar(n0,c);
    }
}

lemma_auto(take(length(l),append(l,r)))
void take_length_append<t>(list<t> l,list<t> r)
    requires true;
    ensures  take(length(l),append(l,r)) == l;
{
    switch(l) {
    case nil:
    case cons(x,xs): take_length_append(xs,r);
    }
}

lemma_auto void string_inv()
    requires [?f]string(?s,?cs);
    ensures  [ f]string( s, cs)
        &*&  s > 0 &*& !mem('\0',cs);
{
    if(s <= 0 || mem('\0',cs)) {
        open string(s,_);
        assert [_]character(s,?c);
        if(c != 0) string_inv();
    }
}

  @*/

char* leftpad(char pad, size_t len, const char* s)
    /*@ requires [?f]string(s, ?cs)
            &*&  length(cs) < ULONG_MAX
            &*&  len < ULONG_MAX
            &*&  pad != '\0'
            ; @*/
    /*@ ensures  [ f]string(s,  cs)
            &*&  (result == 0 ? emp
                 : string(result, ?newcs)
                 &*& malloc_block(result,length(newcs)+1)
                 &*& (length(cs) >= len
                     ? newcs == cs
                     : length(newcs) == len
                     &*& newcs
                        == append(
                            repchar(noi(len-length(cs)), pad),
                            cs)
                     )
                 )
            ; @*/
    /*@ terminates; @*/
{
    char* ret;
    size_t i;
    size_t pad_len;
    size_t orig_len = strlen(s);

    if(orig_len >= len) {
        len = orig_len;
    }

    pad_len = len-orig_len;
    /*@ assert pad_len >= 0; @*/
    ret = malloc(len+1);

    if(ret) {
        i = 0;
        while(i < pad_len)
            /*@ requires ret[i..pad_len]     |-> _; @*/
            /*@ ensures  ret[old_i..pad_len] |->
                            repchar(noi(pad_len-old_i),pad)
                    &*&  i == pad_len; @*/
            /*@ decreases pad_len-i; @*/
        {
            /*@ assert succ(noi(pad_len-i-1))
                    == noi(pad_len-i); @*/
            ret[i] = pad;
            ++i;
        }

        strcpy(ret+i,s);
        /*@ chars_to_string(ret+i); @*/
        /*@ chars_string_join(ret); @*/
    }

    return ret;
}

