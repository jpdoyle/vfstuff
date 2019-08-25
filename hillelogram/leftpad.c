#include <string.h>
#include <stdlib.h>
/*@ #include <nat.gh> @*/

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

  @*/

/* VeriFast's strlen and strcpy are not currently labeled
 * "terminates", so to prove total correctness I implement them here.
 */

char *my_strcpy(char *d, char *s)
    /*@ requires [?f]string(s, ?cs) &*& chars(d, length(cs) + 1, _);
      @*/
    /*@ ensures [f]string(s, cs)
            &*& string(d, cs)
            &*& result == d;
      @*/
    /*@ terminates; @*/
{
    char* ret = d;
    while(true)
        /*@ requires [ f]string(s, ?loop_cs)
                &*&  chars(d, length(loop_cs) + 1, _);
          @*/
        /*@ ensures [f]string(old_s, loop_cs)
                &*& string(old_d, loop_cs)
                ;
          @*/
        /*@ decreases length(loop_cs); @*/
    {
        *d = *s;
        if(!*s) { break; }
        ++s;
        ++d;
    }
    return ret;
}

size_t my_strlen(char *string)
    /*@ requires [?f]string(string, ?cs)
            &*&  length(cs) <= ULONG_MAX; @*/
    /*@ ensures  [ f]string(string,  cs) &*& result == length(cs); @*/
    /*@ terminates; @*/
{
    size_t ret = 0;
    while(*string)
        /*@ requires [f]string(string,     ?loop_cs)
                &*&  ret + length(loop_cs) == length(cs); @*/
        /*@ ensures  [f]string(old_string,  loop_cs)
                &*&  ret == old_ret + length(loop_cs); @*/
        /*@ decreases length(loop_cs); @*/
    {
        ++ret;
        ++string;
    }
    return ret;
}

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
                            repchar(nat_of_int(len-length(cs)), pad),
                            cs)
                     )
                 )
            ; @*/
    /*@ terminates; @*/
{
    char* ret;
    size_t i;
    size_t pad_len;
    size_t orig_len = my_strlen(s);

    if(orig_len >= len) {
        len = orig_len;
    }

    pad_len = len-orig_len;
    ret = malloc(len+1);

    if(ret) {
        i = 0;
        while(i < pad_len)
            /*@ requires ret[i..pad_len]     |-> _; @*/
            /*@ ensures  ret[old_i..pad_len] |->
                            repchar(nat_of_int(pad_len-old_i),pad)
                    &*&  i == pad_len; @*/
            /*@ decreases pad_len-i; @*/
        {
            /*@ assert succ(nat_of_int(pad_len-i-1))
                    == nat_of_int(pad_len-i); @*/
            ret[i] = pad;
            ++i;
        }

        my_strcpy(ret+i,s);
        /*@ chars_string_join(ret); @*/
    }

    return ret;
}

