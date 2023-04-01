//@ #include "util.gh"
//@ #include "mul.gh"

/*@


lemma void chars_split_as(char *array,
        list<char> pref,list<char> suff)
    requires [?f]chars(array, ?N, append(pref,suff));
    ensures [f]chars(array, length(pref), pref)
        &*& [f]chars(array + length(pref), length(suff), suff);
{
    take_append(length(pref),pref,suff);
    drop_append(length(pref),pref,suff);
}

lemma void uints_split_as(unsigned *array,
        list<unsigned> pref,list<unsigned> suff)
    requires [?f]uints(array, ?N, append(pref,suff));
    ensures [f]uints(array, length(pref), pref)
        &*& [f]uints(array + length(pref), length(suff), suff);
{
    switch(pref) {
    case nil:
        close [f]uints(array, length(pref), pref);
    case cons(x,xs):
        open [f]uints(array, _,_);
        uints_split_as(array+1,xs,suff);
        close [f]uints(array, length(pref), pref);
    }
}

lemma void ints_split_as(int *array,
        list<int> pref,list<int> suff)
    requires [?f]ints(array, ?N, append(pref,suff));
    ensures [f]ints(array, length(pref), pref)
        &*& [f]ints(array + length(pref), length(suff), suff);
{
    switch(pref) {
    case nil:
        close [f]ints(array, length(pref), pref);
    case cons(x,xs):
        open [f]ints(array, _,_);
        ints_split_as(array+1,xs,suff);
        close [f]ints(array, length(pref), pref);
    }
}

lemma void uints_split(unsigned *array, int offset)
    requires [?f]uints(array, ?N, ?as) &*& 0 <= offset &*& offset <= N;
    ensures [f]uints(array, offset, take(offset, as))
        &*& [f]uints(array + offset, N - offset, drop(offset, as))
        &*& as == append(take(offset, as), drop(offset, as));
{
    if(offset == 0) {
        close [f]uints(array, offset, take(offset, as));
    } else {
        open [f]uints(array, _,_);
        uints_split(array+1,offset-1);
        close [f]uints(array, offset,_);
    }
}

lemma void uints_join(unsigned *a)
    requires [?f]uints(a, ?M, ?as) &*& [f]uints(a + M, ?N, ?bs);
    ensures [f]uints(a, M + N, append(as, bs));
{
    open uints(a,M,_);
    if(M != 0) {
        uints_join(a+1);
        close [f]uints(a, M + N, append(as, bs));
    }
}

lemma void uints_limits(unsigned *array)
    requires [?f]uints(array, ?n, ?cs) &*& n > 0;
    ensures [f]uints(array, n, cs) &*& (unsigned *)0 < array &*&
        array + n <= (unsigned *)UINTPTR_MAX;
{
    if(array <= 0 || array + n > (unsigned *)UINTPTR_MAX) {
        open uints(array,n,_);
        if(n > 1) {
            uints_limits(array+1);
        }
        u_integer_limits(array);
        assert false;
    }
}

lemma void ints_limits2(int *array)
    requires [?f]ints(array, ?n, ?cs) &*& n > 0;
    ensures [f]ints(array, n, cs) &*& (int *)0 <= array &*&
        array + n <= (int *)UINTPTR_MAX;
{
    if(array < (int *)0 || array + n > (int *)UINTPTR_MAX) {
        open ints(array,_,_);
        if(n > 1) ints_limits2(array+1);
        integer_limits(array);
        assert false;
    }
}

lemma void integers__limits2(void *array)
    requires [?f]integers_(array, ?sz, ?sgn, ?n, ?cs) &*& n > 0;
    ensures [f]integers_(array, sz, sgn, n, cs) &*& (void *)0 <= array
        &*& array + n <= (void *)UINTPTR_MAX
        &*& array + n*sz <= (void *)UINTPTR_MAX
        &*& !!pointer_within_limits(array);
{
    if(array < (void *)0 || array + n > (void *)UINTPTR_MAX
                         || array + n*sz > (void *)UINTPTR_MAX
                         || !pointer_within_limits(array)) {
        open integers_(array,_,_,_,_);
        integer__limits(array);
        if(n > 1) integers__limits2(array+sz);

        assert false;
    }
}

lemma_auto void malloced_strings_public()
    requires [?f]malloced_strings(?base,?n,?strs);
    ensures  [ f]malloced_strings( base, n, strs)
        &*&  n >= 0
        &*&  base != 0
        &*&  length(strs) == n
        ;
{
    open [ f]malloced_strings( base, n, strs);
    if(n != 0) {
        malloced_strings_public();
    }
}

lemma void u_llong_integer__unique(unsigned long long *p)
    requires [?f]u_llong_integer(p, ?v);
    ensures [f]u_llong_integer(p, v) &*& f <= 1;
{
    if(f > 1) {
        open u_llong_integer(_,_);
        integer__to_chars(p,sizeof(unsigned long long),false);
        chars_split((void*)p,sizeof(int));
        chars_to_ints((char*)(void*)p,1);
        integer_unique((int*)(void*)p);
        assert false;
    }
}

lemma void ullong__unique(unsigned long long *p)
    requires [?f]ullong_(p, ?v);
    ensures [f]ullong_(p, v) &*& f <= 1;
{
    if(f > 1) {
        open ullong_(_,_);
        integer___unique(p);
        assert false;
    }
}

lemma void u_llong_integer_unique(unsigned long long *p)
    requires [?f]u_llong_integer(p, ?v);
    ensures [f]u_llong_integer(p, v) &*& f <= 1;
{
    if(f > 1) {
        open u_llong_integer(_,_);
        integer__to_chars(p,sizeof(unsigned long long),false);
        chars_split((void*)p,sizeof(int));
        chars_to_ints((char*)(void*)p,1);
        integer_unique((int*)(void*)p);
        assert false;
    }
}

lemma void ullongs_split(unsigned long long *array, int offset)
    requires [?f]ullongs(array, ?N, ?as) &*& 0 <= offset &*& offset <= N;
    ensures [f]ullongs(array, offset, take(offset, as))
        &*& [f]ullongs(array + offset, N - offset, drop(offset, as))
        &*& as == append(take(offset, as), drop(offset, as));
{
    if(offset > 0) {
        open ullongs(array,_,_);
        ullongs_split(array+1,offset-1);
        close [f]ullongs(array,offset,_);
    }
}

lemma void ullongs_join(unsigned long long *a)
    requires [?f]ullongs(a, ?M, ?as) &*& [f]ullongs(a + M, ?N, ?bs);
    ensures [f]ullongs(a, M + N, append(as, bs));
{
    open ullongs(a,_,_);
    if(M > 0) {
        ullongs_join(a+1);
        close [f]ullongs(a,M+N,_);
    }
}

lemma void uintptrs_split(uintptr_t *array, int offset)
    requires [?f]uintptrs(array, ?N, ?as) &*& 0 <= offset &*& offset <= N;
    ensures [f]uintptrs(array, offset, take(offset, as))
        &*& [f]uintptrs(array + offset, N - offset, drop(offset, as))
        &*& as == append(take(offset, as), drop(offset, as));
{
    if(offset > 0) {
        open uintptrs(array,_,_);
        uintptrs_split(array+1,offset-1);
        close [f]uintptrs(array,offset,_);
    }
}

lemma void uintptrs_join(uintptr_t *a)
    requires [?f]uintptrs(a, ?M, ?as) &*& [f]uintptrs(a + M, ?N, ?bs);
    ensures [f]uintptrs(a, M + N, append(as, bs));
{
    open uintptrs(a,_,_);
    if(M > 0) {
        uintptrs_join(a+1);
        close [f]uintptrs(a,M+N,_);
    }
}

lemma void uintptrs__join(uintptr_t *a)
    requires [?f]uintptrs_(a, ?M, ?as) &*& [f]uintptrs_(a + M, ?N, ?bs);
    ensures [f]uintptrs_(a, M + N, append(as, bs));
{
    open uintptrs_(a,_,_);
    if(M > 0) {
        uintptrs__join(a+1);
        close [f]uintptrs_(a,M+N,_);
    }
}

lemma_auto void uintptr_buffer_auto()
    requires [?f]uintptr_buffer(?start,?len,?cap,?vals);
    ensures  [ f]uintptr_buffer( start, len, cap, vals)
        &*&  f <= 1 &*& start != 0
        &*&  len >= 0 &*& cap > 0 &*& length(vals) == len
        ;
{
    open uintptr_buffer(_,_,_,_);
    if(f > 1) {
        open uintptrs(start,_,_);
        if(len == 0) { open uintptrs_(start,_,_); }
        open uintptr_(start,_);
        integer___unique(start);
        assert false;
    }
}

lemma void forall_append_exact<t>(list<t> a, list<t> b, fixpoint(t,bool) p)
    requires true;
    ensures  forall(append(a,b),p) == (forall(a,p) && forall(b,p));
{
    switch(a) {
    case nil:
        return;
    case cons(x,xs):
        if(forall(append(a,b),p)) {
            if(!forall(a,p)) {
                t cx = not_forall(a,p);
                forall_elim(append(a,b),p,cx);
                assert false;
            }

            if(!forall(b,p)) {
                t cx = not_forall(b,p);
                forall_elim(append(a,b),p,cx);
                assert false;
            }

        } else {

            t cx = not_forall(append(a,b),p);
            assert mem(cx,a) || mem(cx,b);
            if(mem(cx,a) && forall(a,p)) {
                forall_elim(a,p,cx);
                assert false;
            }

            if(mem(cx,b) && forall(b,p)) {
                forall_elim(b,p,cx);
                assert false;
            }

        }

    }
}

lemma_auto(mem(x,reverse(l))) void reverse_mem<t>(list<t> l, t x)
    requires true;
    ensures  mem(x,l) == mem(x,reverse(l));
{
    switch(l) {
    case nil:
    case cons(v,vs):
        reverse_mem(vs,x);

        assert mem(x,l) == (x == v || mem(x,vs));

        if(mem(x,l)) {
            assert !!mem(x,reverse(l));
        } else if(mem(x,reverse(l))) {
            assert false;
        }

    }
}

lemma void forall_reverse<t>(list<t> l, fixpoint(t,bool) p)
    requires true;
    ensures  forall(l,p) == forall(reverse(l),p);
{
    switch(l) {
    case nil: return;
    case cons(x,xs):

        if(forall(l,p)) {
            assert !!forall(xs,p);
            forall_reverse(xs,p);
            forall_elim(l,p,x);
            forall_append_exact(reverse(xs),{x},p);

            assert !!forall(reverse(l),p);

        } else if(forall(reverse(l),p)) {
            t cx = not_forall(l,p);

            assert !!mem(cx,reverse(l));

            forall_elim(reverse(l),p,cx);

            assert false;

        }

    }
}

lemma_auto(assoc_of(key,l)) void assoc_lookup_of<k,v>(k key,
            list<pair<k,v> > l)
    requires true;
    ensures  assoc_of(key,l) == opmap((pair)(key),lookup_of(key,l));
{
    switch(l) {
    case nil:
    case cons(x,xs):
        assoc_lookup_of(key,xs);
        TRIVIAL_PAIR(x)
    }
}

lemma void disjoint_append<t>(list<t> a, list<t> b)
    requires true;
    ensures  distinct(append(a,b)) == (distinct(a) && distinct(b) && disjoint(a,b));
{
    switch(a) {
        case nil:
        case cons(x,xs):
            disjoint_append(xs,b);
    }
}

lemma void distinct_reverse<t>(list<t> l)
    requires true;
    ensures  distinct(reverse(l)) == distinct(l);
{
    switch(l) {
    case nil:
    case cons(x,xs):
        distinct_reverse(xs);
        disjoint_append({x},xs);
        disjoint_append(reverse(xs),{x});
        assert reverse(l) == append(reverse(xs),{x});
        if(!distinct(l) && distinct(reverse(l))) {
            assert !!distinct(append(reverse(xs),{x}));
            assert !!distinct(reverse(xs));
            assert !!distinct(xs);
            assert !!mem(x,xs);
            forall_elim(reverse(xs),
                (notf)((flip)(mem,{x})),x);
            assert false;
        }
        if(distinct(l) && !distinct(reverse(l))) {
            assert !!distinct(reverse(xs));
            assert !!distinct({x});
            t cx = not_forall(reverse(xs),
                (notf)((flip)(mem,{x})));
            assert false;
        }
    }
}

lemma void disjoint_with_append<t>(list<t> a, list<t> b, list<t> c)
    requires true;
    ensures  disjoint(a,append(b,c)) == (disjoint(a,b) && disjoint(a,c));
{
    switch(a) {
        case nil:
        case cons(x,xs):
            disjoint_with_append(xs,b,c);
    }
}

lemma_auto(disjoint(a,b)) void disjoint_symm<t>(list<t> a, list<t> b)
    requires true;
    ensures  disjoint(a,b) == disjoint(b,a);
{
    if(disjoint(a,b) && !disjoint(b,a)) {
        t cx = not_forall(b,(notf)((flip)(mem,a)));
        forall_elim(a,(notf)((flip)(mem,b)),cx);
        assert false;
    }

    if(!disjoint(a,b) && disjoint(b,a)) {
        t cx = not_forall(a,(notf)((flip)(mem,b)));
        forall_elim(b,(notf)((flip)(mem,a)),cx);
        assert false;
    }
}

lemma_auto(bounded(l,h,x)) void bounded_cases(int l, int h, int x)
    requires bounded(l,h,x) && l <= h;
    ensures  x == l || bounded(l+1,h,x);
{
    if(x != l) {
        assert x > l;
        note(x >= l+1);
        assert !!bounded(l+1,h,x);
    }
}


@*/

