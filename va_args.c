#include <stdarg.h>
#include <stdio.h>
#include <string.h>
#include <malloc.h>
/*@ #include "util.gh" @*/

/*@

predicate int_of_vararg(vararg va; int x) =
    switch(va) {
    case vararg_int(y):  return x == y;
    case vararg_uint(y): return x == 0 &*& false;
    case vararg_pointer(p):  return x == 0 &*& false;
    };

predicate varargs_ints(list<vararg> va; list<int> out) =
    switch(va) {
    case nil: return out == {};
    case cons(x,xs):
        return  int_of_vararg(x,?o) &*& varargs_ints(xs,?rest)
            &*& out == cons(o,rest);
    };

lemma void make_varargs_ints(list<int> l)
    requires true;
    ensures  varargs_ints(map(vararg_int,l),l);
{
    switch(l) {
    case nil:
    case cons(x,xs):
        make_varargs_ints(xs);
        close int_of_vararg(vararg_int(x),_);
        close varargs_ints(map(vararg_int,l),l);
    }
}

predicate strings_vararg(list<char*> ps;
        list<vararg> va, list<list<char> > ss) =
    switch(ps) {
    case nil: return va == {} &*& ss == {};
    case cons(x,xs):
        return  string(x,?s) &*& strings_vararg(xs,?va_rest,?ss_rest)
            &*& va == cons(vararg_pointer(x),va_rest)
            &*& ss == cons(s,ss_rest);
    };

lemma_auto void strings_vararg_auto()
    requires [?f]strings_vararg(?ps,?va,?ss);
    ensures  [ f]strings_vararg( ps, va, ss)
        &*&  length(ps) == length(va)
        &*&  length(va) == length(ss)
        &*&  va == map(vararg_pointer,ps);
{
    if(!(length(ps) == length(va)
            &&  length(va) == length(ss)
            &&  va == map(vararg_pointer,ps))) {
        open strings_vararg(_,_,_);
        switch(ps) {
        case nil: assert false;
        case cons(p,rest):
            strings_vararg_auto();
        }
        assert false;
    }
}

fixpoint int sum(list<int> l) {
    switch(l) {
    case nil: return 0;
    case cons(x,xs): return x + sum(xs);
    }
}

fixpoint bool all_nonneg(list<int> l) {
    switch(l) {
    case nil: return true;
    case cons(x,xs): return x >= 0 && all_nonneg(xs);
    }
}

lemma_auto(sum(l))
void sum_nonneg(list<int> l)
    requires !!all_nonneg(l);
    ensures  sum(l) >= 0;
{ switch(l) { case nil: case cons(x,xs): sum_nonneg(xs); } }

lemma_auto(map(length,l))
void map_length_nonneg<t>(list<list<t> > l)
    requires true;
    ensures  !!all_nonneg(map(length,l));
{ switch(l) { case nil: case cons(x,xs): map_length_nonneg(xs); } }

lemma_auto(length(l))
void length_nil(list<int> l)
    requires true;
    ensures  (length(l) == 0) == (l == nil);
{ switch(l) { case nil: case cons(x,xs): } }

fixpoint list<t> flatten<t>(list<list<t> > l) {
    switch(l) {
    case nil: return nil;
    case cons(x,xs):
        return append(x,flatten(xs));
    }
}

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

  @*/

int
add_em_up (int count,...)
    /*@ requires varargs_ints(varargs,?is)
            &*&  length(is) == count
            &*&  !!all_nonneg(is)
            &*&  sum(is) <= INT_MAX
            ;
      @*/
    //@ ensures result == sum(is);
    /*@ terminates; @*/
{
  va_list ap;
  int i, acc;

  va_start (ap, count);         /* Initialize the argument list. */
  /*@ assert count |-> length(is); @*/

  acc = 0;
  for (i = 0; i < count; i++)
    /*@ invariant count |-> length(is)
            &*&   ap |-> ?loop_ap
            &*&   i >= 0 &*& i <= length(is)
            &*&   va_list(loop_ap,&count,1/2,?loop_args)
            &*&   varargs_ints(loop_args,?loop_is)
            &*&   !!all_nonneg(loop_is)
            &*&   acc >= 0
            &*&   acc + sum(loop_is) == sum(is)
            &*&   length(loop_is) + i == length(is);
      @*/
    /*@ decreases length(loop_is); @*/
  {
    /*@ open varargs_ints(_,_); @*/
    /*@ open int_of_vararg(_,_); @*/
    int x = va_arg (ap, int);   /* Get the next argument value. */
    acc += x;
  }
  /*@ open varargs_ints(_,_); @*/

  va_end (ap);                  /* Clean up. */
  return acc;
}

char *mystrcat(int count, ...)
    /*@ requires [?f]strings_vararg(?ps,varargs,?ss)
            &*&  count == length(ps)
            &*&  sum(map(length,ss)) <= UINT_MAX
            ; @*/
    /*@ ensures  [ f]strings_vararg( ps,varargs, ss)
            &*&  result == 0 ? emp
            :    malloced_string(result,flatten(ss)); @*/
    /*@ terminates; @*/
{
    /*@ int n = length(ps); @*/
    va_list ap;
    size_t  len = 0;

    if (count < 1)
        return NULL;

    // First, measure the total length required.
    va_start(ap, count);
    for (int i=0; i < count; i++)
        /*@ requires ap |-> ?loop_ap
                &*&  count |-> n
                &*&  va_list(loop_ap,&count,1/2,?loop_args)
                &*&  [f]strings_vararg(?loop_ps,loop_args,?loop_ss)
                &*&  len + sum(map(length,loop_ss)) == sum(map(length,ss))
                &*&  i >= 0 &*& i <= n &*& n-i == length(loop_ss)
                ; @*/
        /*@ ensures  ap |-> ?final_ap
                &*&  count |-> n
                &*&  va_list(final_ap,&count,1/2,_)
                &*&  [f]strings_vararg( loop_ps,loop_args, loop_ss)
                &*&  len == old_len + sum(map(length,loop_ss))
                ; @*/
        /*@ decreases n-i; @*/
    {
        /*@ open strings_vararg(_,_,_); @*/
        const char *s = va_arg(ap, char *);
        size_t l = strlen(s);
        len += l;
        /*@ recursive_call(); @*/
        /*@ close [f]strings_vararg(loop_ps,_,_); @*/
    }
    va_end(ap);

    // Allocate return buffer.
    char *ret = malloc(len + 1);
    if (ret == NULL)
        return NULL;

    /*@ if(n == 0) {
        assert false;
    } @*/

    // Concatenate all the strings into the return buffer.
    char *dst = ret;
    va_start(ap, count);
    /*@ int remaining_len = len+1; @*/
    for (int i=0; i < count; i++)
        /*@ requires ap |-> ?loop_ap
                &*&  count |-> n
                &*&  va_list(loop_ap,&count,1/2,?loop_args)
                &*&  [f]strings_vararg(?loop_ps,loop_args,?loop_ss)
                &*&  remaining_len == sum(map(length,loop_ss))+1
                &*&  i >= 0 &*& i <= n &*& n-i == length(loop_ss)
                &*&  *dst |-> ?dst_c
                &*&  (dst_c == '\0' || i < n)
                &*&  dst[1..remaining_len] |-> _
                &*&  remaining_len <= len+1 &*& remaining_len >= 0
                &*&  (remaining_len != 0) || (n == i)
                ; @*/
        /*@ ensures  ap |-> ?final_ap
                &*&  count |-> n
                &*&  va_list(final_ap,&count,1/2,_)
                &*&  [f]strings_vararg( loop_ps,loop_args, loop_ss)
                &*&  old_dst[..old_remaining_len-1] |-> flatten(loop_ss)
                &*&  *(old_dst+old_remaining_len-1) |-> '\0'
                &*&  !mem('\0',flatten(loop_ss))
                ; @*/
        /*@ decreases n-i; @*/
    {
        /*@ open strings_vararg(_,_,_); @*/
        const char *src = va_arg(ap, char *);
        /*@ char* orig_dst = dst; @*/

        // This loop is a strcpy.
        char c;
        do
            /*@ requires *dst |-> _
                    &*&  (dst+1)[..?dn] |-> _
                    &*&  [?sf]string(src,?s)
                    &*&  dn+1 > length(s)
                    &*&  remaining_len >= length(s)+1
                    ; @*/
            /*@ ensures  old_dst[..length(s)] |-> s
                    &*&  old_dst+length(s) == dst-1
                    &*&  *(dst - 1) |-> '\0'
                    &*&  dst[..dn-length(s)] |-> _
                    &*&  [sf]string(old_src,s)
                    &*&  remaining_len == old_remaining_len-length(s)-1
                    &*&  !mem('\0',s)
                    ; @*/
            /*@ decreases length(s); @*/
        {
            /*@ character_limits(dst); @*/
            /*@ string_limits(src); @*/
            c = *dst = *src;
            dst++;
            src++;
            /*@ --remaining_len; @*/
        } while(c);
        dst--;
        /*@ ++remaining_len; @*/

        /*@ recursive_call(); @*/
        /*@ close [f]strings_vararg(loop_ps,_,_); @*/
        /*@ chars_join(orig_dst); @*/
    }
    /*@ body_chars_to_string(ret); @*/
    va_end(ap);
    return ret;
}

int
main (void)
    //@ requires true;
    //@ ensures  true;
{
    int x;

    //@ make_varargs_ints({5,5,6});
    x = add_em_up (3, 5, 5, 6);
    //@ assert x == 16;

    /* This call prints 16. */
    printf ("%d\n", x);

    //@ make_varargs_ints({1, 2, 3, 4, 5, 6, 7, 8, 9, 10});
    x = add_em_up (10, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10);

    //@ assert x == 55;

    /* This call prints 55. */
    printf ("%d\n", x);

    return 0;
}

