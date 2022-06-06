#include <stdarg.h>
#include <stdio.h>

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

lemma_auto(length(l))
void length_nil(list<int> l)
    requires true;
    ensures  (length(l) == 0) == (l == nil);
{ switch(l) { case nil: case cons(x,xs): } }

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

