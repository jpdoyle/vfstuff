/*@ #include "core.gh" @*/

/*@

lemma void index_of_positive<t>(t v, list<t> l)
    requires true;
    ensures  index_of(v,l) >= 0;
{
    switch(l) { case nil: case cons(x,xs): index_of_positive(v,xs); }
}

lemma_auto(nth_of(index_of(v,l),l))
void nth_of_index_of<t>(t v, list<t> l)
    requires true;
    ensures  (nth_of(index_of(v,l),l) == some(v))
        == mem(v,l);
{
    switch(l) {
        case nil:
        case cons(x,xs):
            nth_of_index_of(v,xs);
            if(v == x) {
                assert index_of(v,l) == 0;
                assert nth_of(0,l) == some(x);
            } else {
                assert index_of(v,xs)+1 == index_of(v,l);
                index_of_positive(v,xs);
                assert index_of(v,xs) >= 0;
                assert nth_of(index_of(v,l),l)
                    == nth_of(index_of(v,l)-1,xs);
                assert nth_of(index_of(v,l),l)
                    == nth_of(index_of(v,xs),xs);
            }
    }
}

lemma_auto(nth_of(n,l)) void nth_of_bounds<t>(int n, list<t> l)
    requires true;
    ensures  (nth_of(n,l) == none) == (l == nil || n < 0 || n >=
            length(l));
{
    switch(l) {
        case nil:
        case cons(x,xs):
            nth_of_bounds(n-1,xs);
    }
}

lemma void nth_of_is_nth<t>(int n, list<t> l)
    requires true;
    ensures  switch(nth_of(n,l)) {
        case none: return n < 0 || length(l) <= n;
        case some(x):
            return n >= 0 &*& n < length(l) &*& x == nth(n,l);
    };
{
    switch(l) { case nil: case cons(x,xs): nth_of_is_nth(n-1,xs); }
}

//lemma_auto(some(x) == some(y))
lemma
void option_eq<t>(t x, t y)
    requires true;
    ensures  (some(x) == some(y)) == (x == y);
{
    option<t> ox = some(x);
    option<t> oy = some(y);
    TRIVIAL_OPTION(ox)
    TRIVIAL_OPTION(oy)
}

lemma void either_bifunctor<p,q,r, s,t,w>(
        fixpoint(q,r) lf, fixpoint(p,q) lg,
        fixpoint(t,w) rf, fixpoint(s,t) rg,
        either<s,p> e1, either<p,s> e2)
    requires true;
    ensures emp

        &*& either_rmap(id,e1) == e1
        &*& either_rmap(id,e2) == e2
        &*& either_lmap(id,e1) == e1
        &*& either_lmap(id,e2) == e2
        &*& either_bimap(id,id,e1) == e1
        &*& either_bimap(id,id,e2) == e2

        &*& either_rmap(lf,either_rmap(lg,e1))
                == either_rmap((o)(lf,lg),e1)
        &*& either_lmap(lf,either_lmap(lg,e2))
                == either_lmap((o)(lf,lg),e2)

        &*& either_lmap(rf,either_lmap(rg,e1))
                == either_lmap((o)(rf,rg),e1)
        &*& either_rmap(rf,either_rmap(rg,e2))
                == either_rmap((o)(rf,rg),e2)

        &*& either_bimap(rf,lf,either_bimap(rg,lg,e1))
                == either_bimap((o)(rf,rg),(o)(lf,lg),e1)
        &*& either_bimap(lf,rf,either_bimap(lg,rg,e2))
                == either_bimap((o)(lf,lg),(o)(rf,rg),e2)
        ;
{
    TRIVIAL_EITHER(e1)
    TRIVIAL_EITHER(e2)
}

lemma void pair_bifunctor<p,q,r, s,t,w>(
        fixpoint(q,r) lf, fixpoint(p,q) lg,
        fixpoint(t,w) rf, fixpoint(s,t) rg,
        pair<s,p> e1, pair<p,s> e2)
    requires true;
    ensures emp

        &*& pair_rmap(id,e1) == e1
        &*& pair_rmap(id,e2) == e2
        &*& pair_lmap(id,e1) == e1
        &*& pair_lmap(id,e2) == e2
        &*& pair_bimap(id,id,e1) == e1
        &*& pair_bimap(id,id,e2) == e2

        &*& pair_rmap(lf,pair_rmap(lg,e1))
                == pair_rmap((o)(lf,lg),e1)
        &*& pair_lmap(lf,pair_lmap(lg,e2))
                == pair_lmap((o)(lf,lg),e2)

        &*& pair_lmap(rf,pair_lmap(rg,e1))
                == pair_lmap((o)(rf,rg),e1)
        &*& pair_rmap(rf,pair_rmap(rg,e2))
                == pair_rmap((o)(rf,rg),e2)

        &*& pair_bimap(rf,lf,pair_bimap(rg,lg,e1))
                == pair_bimap((o)(rf,rg),(o)(lf,lg),e1)
        &*& pair_bimap(lf,rf,pair_bimap(lg,rg,e2))
                == pair_bimap((o)(lf,lg),(o)(rf,rg),e2)
        ;
{

    TRIVIAL_PAIR(e1)
    TRIVIAL_PAIR(e2)
}

lemma void nth_of_mem<t>(int n, list<t> l, t v)
    requires nth_of(n,l) == some(v);
    ensures  !!mem(v,l);
{ LIST_INDUCTION(l,xs,if(n != 0) nth_of_mem(n-1,xs,v)) }

lemma_auto(ion(nat_minus(n,m)))
void nat_minus_int(nat n, nat m)
    requires true;
    ensures  ion(nat_minus(n,m))
        ==   max_of(0,ion(n)-ion(m));
{
    switch(n) {
    case zero:
    case succ(n0):
        switch(m) {
        case zero:
        case succ(m0):
            nat_minus_int(n0,m0);
        }
    }
}

lemma void max_of_correct(int a, int b, int c)
    requires true;
    ensures  max_of(a,b) >= a &*& max_of(a,b) >= b
        &*&  (c >= a && c >= b) == (c >= max_of(a,b));
{
    if(a >= b) {} else {}
    if(c >= a) {} else {}
    if(c >= b) {} else {}
}

lemma_auto(max_of(a,b))
void max_of_auto1(int a, int b)
    requires true;
    ensures  max_of(a,b) >= a;
{}

lemma_auto(max_of(a,b))
void max_of_auto2(int a, int b)
    requires true;
    ensures  max_of(a,b) == max_of(b,a);
{}

lemma_auto(max_of(a,b))
void max_of_auto3(int a, int b)
    requires a >= b;
    ensures  max_of(a,b) == a;
{}

lemma void min_of_correct(int a, int b, int c)
    requires true;
    ensures  min_of(a,b) <= a &*& min_of(a,b) <= b
        &*&  (c <= a && c <= b) == (c <= min_of(a,b));
{
    if(a <= b) {} else {}
    if(c <= a) {} else {}
    if(c <= b) {} else {}
}

lemma_auto void uintptrs_inv()
    requires [?f]uintptrs(?p, ?count, ?vs);
    ensures [f]uintptrs(p, count, vs) &*& count == length(vs);
{
    open uintptrs(_,_,_);
    if(count != 0) {
        uintptrs_inv();
        switch(vs) { case nil: case cons(vv,vvs): }
    }
}

lemma_auto void uintptrs__inv()
    requires [?f]uintptrs_(?p, ?count, ?vs);
    ensures [f]uintptrs_(p, count, vs) &*& count == length(vs);
{
    open uintptrs_(_,_,_);
    if(count != 0) {
        uintptrs__inv();
        switch(vs) { case nil: case cons(vv,vvs): }
    }
}

  @*/

