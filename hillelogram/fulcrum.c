#include <string.h>
#include <stdlib.h>
#include <stdbool.h>
/*@ #include <nat.gh> @*/
/*@ #include <listex.gh> @*/
/*@ #include <quantifiers.gh> @*/
/*@ #include <arrays.gh> @*/

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

lemma void distinct_step<t>(list<t> l, t x)
    requires !!distinct(l) &*& !mem(x,l);
    ensures  !!distinct(append(l,{x}));
{
    switch(l) {
    case nil:
    case cons(v,vs):
        distinct_step(vs,x);
    }
}

lemma void forall_remove<t>(list<t> l,fixpoint(t,bool) p, t x)
    requires !!forall(l,p);
    ensures  !!forall(remove(x,l),p);
{
    switch(l) {
    case nil:
    case cons(v,vs):
        if(x != v) {
            forall_remove(vs,p,x);
        }
    }
}

lemma_auto(subset(x,x)) void subset_self<t>(list<t> x)
    requires true;
    ensures  !!subset(x,x);
{
    switch(x) {
    case nil:
    case cons(v,vs):
        subset_self(vs);

        if(!subset(vs,x)) {
            t cx = not_forall(vs,(contains)(x));
            assert false;
        }
    }
}

lemma_auto(mem(x,remove(y,l)))
void mem_remove<t>(t x, t y, list<t> l)
    requires !!distinct(l);
    ensures  (mem(x,remove(y,l)) == (mem(x,l) && x != y));
{
    switch(l) {
    case nil:
    case cons(v,vs):
        mem_remove(x,y,vs);
    }
}

lemma_auto(distinct(remove(x,l)))
void distinct_remove<t>(t x, list<t> l)
    requires !!distinct(l);
    ensures  !!distinct(remove(x,l));
{
    switch(l) {
    case nil:
    case cons(v,vs):
        distinct_remove(x,vs);
    }
}

lemma_auto(remove(x,l))
void remove_nonmem<t>(t x, list<t> l)
    requires true;
    ensures  (remove(x,l) == l) == (!mem(x,l));
{
    switch(l) {
    case nil:
    case cons(v,vs):
        remove_nonmem(x,vs);
    }
}

lemma void subset_length<t>(list<t> a,list<t> b)
    requires !!distinct(a) &*& !!subset(a,b);
    ensures  length(a) <= length(b);
{
    switch(b) {
    case nil:
        switch(a) {
        case nil:
        case cons(ax,axs):
        }
    case cons(v,vs):
        forall_remove(a,(contains)(b), v);
        length_remove(v,a);

        if(!subset(remove(v,a),vs)) {
            t cx = not_forall(remove(v,a),(contains)(vs));
            mem_remove_mem(cx,v,a);
            forall_elim(a,(contains)(b), cx);
            if(cx != v) {
                neq_mem_remove(cx,v,a);
                assert false;
            } else {
                assert false;
            }
            assert false;
        }

        subset_length(remove(v,a),vs);
    }
}

  @*/

