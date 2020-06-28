//@ #include "util.gh"

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

// mul_mono_r/l from verifast's test/longlong.c, renamed because a later
// version of verifast has these in its prelude
lemma void my_mul_mono_l(int a1, int a2, int b)
    requires a1 <= a2 &*& 0 <= b;
    ensures a1 * b <= a2 * b;
{
    for (int i = 0; i < b; i++)
        invariant i <= b &*& a1 * i <= a2 * i;
        decreases b - i;
    {}
}

lemma void my_mul_mono_r(int a, int b1, int b2)
    requires 0 <= a &*& b1 <= b2;
    ensures a * b1 <= a * b2;
{
    for (int i = 0; i < a; i++)
        invariant i <= a &*& i * b1 <= i * b2;
        decreases a - i;
    {}
}

lemma void my_mul_strict_mono_l(int a1, int a2, int b)
    requires a1 < a2 &*& 0 < b;
    ensures a1 * b < a2 * b;
{
    for (int i = 1; i < b; i++)
        invariant i <= b &*& a1 * i < a2 * i;
        decreases b - i;
    {}
}

lemma void my_mul_strict_mono_r(int a, int b1, int b2)
    requires 0 < a &*& b1 < b2;
    ensures a * b1 < a * b2;
{
    for (int i = 1; i < a; i++)
        invariant i <= a &*& i * b1 < i * b2;
        decreases a - i;
    {}
}

lemma void mul_assoc(int x, int y, int z)
    requires true;
    ensures x*(y*z) == (x*y)*z;
{
    if(x == 0) { return; }
    if(x > 0) {
        for(int i =  1; i < x; ++i)
            invariant i >=  1 &*& i <= x &*& i*(y*z) == (i*y)*z;
            decreases x-i;
        { note_eq(((i+1)*y)*z, (i*y+y)*z); }
    } else { assert x < 0;
        for(int i = -1; i > x; --i)
            invariant i <= -1 &*& i >= x &*& i*(y*z) == (i*y)*z;
            decreases i-x;
        { note_eq(((i-1)*y)*z, (i*y-y)*z); }
    }
}

lemma void mul_commutes(int a, int b)
    requires true;
    ensures  a*b == b*a;
{
    if(a >= 0) {
        for(int i = 0; i < a; ++i)
            invariant i*b == b*i
                &*&   0 <= i &*& i <= a;
            decreases a-i;
        { }
    } else {
        for(int i = 0; i > a; --i)
            invariant i*b == b*i
                &*&   0 >= i &*& i >= a;
            decreases i-a;
        { }
    }
}

lemma void mul_3var(int x,int y,int z)
    requires true;
    ensures  x*(y*z) == (x*y)*z
        &*&  x*(y*z) == x*(z*y)
        &*&  x*(y*z) == (x*z)*y
        &*&  x*(y*z) == (y*x)*z
        &*&  x*(y*z) == y*(x*z)
        &*&  x*(y*z) == y*(z*x);
{
    mul_assoc(x,y,z);
    mul_assoc(x,z,y);
    mul_assoc(y,x,z);
    mul_assoc(y,z,x);
    mul_assoc(z,x,y);
    mul_assoc(z,y,x);
    mul_commutes(x,y);
    mul_commutes(x,z);
    mul_commutes(y,z);
}

lemma void mul_abs_commute(int x, int y)
    requires true;
    ensures  abs(x)*abs(y) == abs(x*y);
{
    if(y >= 0) {
        assert abs(y) == y;
        if(x >= 0) {
            assert abs(x) == x;
            my_mul_mono_r(x,0,y);
            assert x*y >= 0; assert abs(x*y) == x*y;
            assert abs(x*y) == abs(x)*abs(y);

        } else {
            my_mul_mono_l(x,-1,y);
            assert x*y <= -y;
            assert x*y <= 0;
            assert abs(x*y) == -(x*y);
            assert abs(x) == -x;
            as_mul(-x,y);
            assert abs(x*y) == (-x)*y;
            assert abs(x*y) == abs(x)*y;
            assert abs(x*y) == abs(x)*abs(y);
        }

    } else {
        assert y < 0;
        assert abs(y) == -y;
        assert y <= -1;

        if(x >= 0) {
            my_mul_mono_r(x,y,-1);
            assert x*y <= -x;
            assert x*y <= 0;
            assert abs(x*y) == -(x*y);
            assert abs(x*y) == x*(-y);
            as_mul(x,-y);
            assert abs(x*y) == x*abs(y);

            assert abs(x*y) == abs(x)*abs(y);

        } else {
            assert x < 0;
            assert abs(x) == -x;
            assert x*y == (-x)*(-y);
            my_mul_mono_l(1,-x,-y);
            assert -y <= (-x)*(-y);
            assert abs(x*y) == x*y;
            as_mul(-x,-y);

            assert abs(x*y) == abs(x)*abs(y);
        }


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

lemma_auto void u_llong_buffer_auto()
    requires [?f]u_llong_buffer(?start,?len,?cap,?vals);
    ensures  [ f]u_llong_buffer( start, len, cap, vals)
        &*&  f <= 1 &*& start != 0
        &*&  len >= 0 &*& cap > 0 &*& length(vals) == len
        ;
{
    open u_llong_buffer(_,_,_,_);
    if(f > 1) {
        open ullongs(start,_,_);
        if(len == 0) { open ullongs(start,_,_); }
        u_llong_integer_unique(start);
    }
}


//lemma void integer_unique(int *p)
//    requires [?f]integer(p, ?v);
//    ensures [f]integer(p, v) &*& f <= 1;
//{
//    if(f > 1) {
//        open integer(p,_);
//        integer__to_chars((void*)p,sizeof(int),true);
//        chars_unique((void*)p);
//        assert false;
//    }
//}

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
            assert mem(x,reverse(vs)) || mem(x,{v});
            assert mem(x,reverse(vs)) || x == v;
            assert mem(x,vs) || x == v;
            assert !!mem(x,l);
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

lemma void zero_mul_unique(int x, int y)
    requires y != 0;
    ensures  (x*y == 0) == (x == 0);
{
    if(x == 0) {
        assert x*y == 0;
    } else if(x*y == 0) {
        assert abs(x*y) == 0;
        assert abs(y) != 0;
        assert abs(x) != 0;
        assert abs(x) > 0;
        assert abs(x) >= 1;
        mul_abs_commute(x,y);
        assert abs(x*y) == abs(x)*abs(y);
        my_mul_mono_l(1,abs(x),abs(y));
        assert abs(y) <= abs(x)*abs(y);
        assert abs(y) <= abs(x*y);
        assert 1 <= abs(x*y);
    }
    
    //if(x < 0) {
    //    assert x <= -1;
    //    mul_mono_l(x,-1,y);
    //    assert x*y <= -y;
    //    
    //} else if(x > 0) {

    //    as_mul(x,x*y);

    //    assert x != 0;
    //    note(x*y == 0);
    //    note(x*0 == 0);
    //    assert x*(x*y) == x*0;
    //    assert x*(x*y) == 0;
    //    assert x*y + x*y == 0;
    //    assert x*(y + y) == 0;

    //    as_mul(x+1,0);
    //    as_mul(x,y);
    //    assert x*y == 0;
    //    assert mul(x+1,0) == 0;
    //    note(mul(x+1,x*y) == 0);
    //    as_mul(x+1,x*y);

    //    assert (x+1)*0 == 0;
    //    assert (x+1)*(x*y) == mul(x+1,x*y);
    //    assert (x+1)*(x*y) == 0;
    //    assert x*(x*y) + x*y == 0;
    //    assert x*(x*y + y) == 0;
    //    assert x*(x*y+1) == x;
    //    assert x*(x*y)+x == 0;

    //}
}

lemma void division_zero_unique(int d, int q, int r)
    requires d != 0 &*& abs(r) < abs(d) &*& 0 == d*q + r;
    ensures  q == (0/d) &*& q == 0 &*& r == (0%d) &*& r == 0;
{
    div_rem(0,d);
    assert abs(0/d*d) == 0;
    assert 0/d*d == 0;
    zero_mul_unique(0/d,d);

    assert 0/d == 0;
    assert 0%d == 0;

    if(r != 0) {
        if(q == 0) {
            assert d*q == 0;
            assert false;
        }

        assert r == -d*q;
        assert abs(r) == abs(d*q);
        mul_abs_commute(d,q);
        assert abs(r) == abs(d)*abs(q);
        my_mul_mono_r(abs(d),1,abs(q));
        assert abs(d)*abs(q) >= abs(d);

        assert false;
    } else {
        zero_mul_unique(q,d);
    }
}

lemma void division_unique(int D, int d, int q, int r)
    requires d != 0 &*& abs(r) < abs(d) &*& abs(d*q) <= abs(D)
        &*&   D == d*q + r;
    ensures  q == (D/d) &*& r == (D%d);
{
    div_rem(D,d);

    assert D == d*q + r;
    assert D == d*(D/d) + (D%d);

    assert 0 == d*q - d*(D/d) + r - (D%d);
    assert 0 == d*(q - (D/d)) + (r - (D%d));
    division_zero_unique(d,(q-(D/d)),(r-(D%d)));
}

lemma void mod_sign(int x, int d)
    requires d > 0;
    ensures  x >= 0 ? x%d >= 0 : x%d <= 0;
{ div_rem(x,d); }

lemma void mod_abs(int x, int d)
    requires d > 0;
    ensures  abs(x%d) == abs(x)%d;
{
    div_rem(x,d);
    if(x < 0) {
        division_unique(-x,d,-(x/d),-(x%d));
    }
}

lemma void mod_plus(int x, int y, int d)
    requires d > 0 &*& x >= 0 &*& y >= 0;
    ensures  (x%d + y)%d == (x+y)%d;
{
    div_rem(x,d);
    div_rem(x+y,d);

    div_rem(x%d+y,d);

    assert x%d + y == (x%d+y)/d*d + (x%d+y)%d;
    assert x + y == (x+y)/d*d + (x+y)%d;

    assert x - x%d == (x+y)/d*d - (x%d+y)/d*d + (x+y)%d - (x%d+y)%d;

    assert x/d*d == (x+y)/d*d - (x%d+y)/d*d + (x+y)%d - (x%d+y)%d;
    assert x/d*d - (x+y)/d*d + (x%d + y)/d*d == (x+y)%d - (x%d+y)%d;
    assert (x/d - (x+y)/d + (x%d + y)/d)*d == (x+y)%d - (x%d+y)%d;
    mod_sign(x+y,d);
    mod_sign(x,d);
    mod_sign(x%d+y,d);

    assert (x+y)%d >= 0 && (x+y)%d < d;
    assert (x+y)%d >= 0 && (x+y)%d <= d-1;
    assert (x%d+y)%d >= 0 && (x%d+y)%d < d;
    assert -((x%d+y)%d) <= 0 && -((x%d+y)%d) > -d;
    assert -((x%d+y)%d) <= 0 && -((x%d+y)%d) >= -d+1;

    assert (x+y)%d - (x%d+y)%d >= -d+1;
    assert (x+y)%d - (x%d+y)%d <= d-1;

    assert abs((x+y)%d - (x%d+y)%d) < abs(d);

    if(x/d - (x+y)/d + (x%d + y)/d != 0) {
        assert abs(x/d - (x+y)/d + (x%d + y)/d) > 0;
        my_mul_mono_l(1, abs(x/d - (x+y)/d + (x%d + y)/d),d);
        assert abs(x/d - (x+y)/d + (x%d + y)/d)*d >= d;
        mul_abs_commute(x/d - (x+y)/d + (x%d + y)/d,d);
        assert abs(x/d - (x+y)/d + (x%d + y)/d*d) >= d;
        assert abs((x+y)%d - (x%d+y)%d) >= d;

        assert false;
    }

    if((x/d - (x+y)/d + (x%d + y)/d)*d != 0) {
        my_mul_mono_l(0,x/d - (x+y)/d + (x%d + y)/d,d);
        my_mul_mono_l(x/d - (x+y)/d + (x%d + y)/d,0,d);

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

lemma void div_monotonic_numerator(int x, int y, int d)
    requires d > 0 &*& x >= 0 &*& y >= x;
    ensures  x/d <= y/d;
{
    div_rem(x,d);
    div_rem(y,d);

    if(y/d < x/d) {
        my_mul_mono_r(d,y/d+1,x/d);
        assert d*(y/d) + d <= d*(x/d);
        assert false;
    }
}

lemma void into_numerator(int x, int y, int d)
    requires d > 0 &*& x >= 0 &*& y >= 0;
    ensures  x + (y/d) == (d*x + y)/d;
{
    division_unique(x*d,d,x,0);
    div_rem(d*x + y,d);

    division_unique(d*x,d,x,0);
    assert (d*x)/d == x;

    my_mul_mono_r(d,0,x);

    assert d*((d*x+y)/d) + (d*x + y)%d == d*x + y;
    assert d*((d*x+y)/d) - d*x + (d*x + y)%d == y;
    assert d*((d*x+y)/d - x) + (d*x + y)%d == y;
    div_monotonic_numerator(y,d*x+y,d);
    div_monotonic_numerator(d*x,d*x+y,d);

    assert ((d*x+y)/d - x) >= 0;
    assert (d*x + y)%d >= 0;
    assert d*((d*x+y)/d - x) <= y;
    my_mul_mono_r(d,0,((d*x+y)/d - x));
    assert d*((d*x+y)/d - x) >= 0;

    //assert (d*x+y)/d >= x;

    division_unique(y,d,(d*x+y)/d - x,(d*x + y)%d);
    (d*x + y)/d - x == y/d;
}

lemma void div_sign(int x, int d)
    requires d > 0;
    ensures  x >= 0 ? x/d >= 0 : x/d <= 0;
{
    div_rem(x,d);
    if(x >= 0 && x/d < 0) {
        mul_mono_l(x/d,-1,d);
        assert false;;
    }

    if(x < 0 && x/d > 0) {
        mul_mono_l(1,x/d,d);
        assert false;
    }
}

lemma void div_monotonic_denominator(int D, int x, int y)
    requires D > 0 &*& x > 0 &*& y >= x;
    ensures  D/y <= D/x;
{
    div_rem(D,x); div_rem(D,y);
    div_sign(D,y);

    if(D/x < D/y) {
        my_mul_mono_r(x,D/x+1,D/y);
        my_mul_mono_l(x,y,D/y);
        assert x*(D/x) + x <= x*(D/y);
        assert x*(D/x) + D%x < x*(D/y);
        assert x*(D/x) + D%x < x*(D/y)+D%y;
        assert x*(D/x) + D%x < y*(D/y)+D%y;

        assert false;
    }
}

lemma void div_shrinks(int x, int d)
    requires d > 0 &*& x >= 0;
    ensures  x/d <= x;
{
    if(x/d > x) {
        div_sign(x,d);
        mod_sign(x,d);
        div_rem(x,d);

        my_mul_mono_l(1,d,x);
        my_mul_strict_mono_r(d,x,x/d);
        assert d*x < d*(x/d);
        assert x < d*(x/d);

        assert false;
    }
}

lemma_auto(pow_nat(x,n))
void pow_nat_pos(int x, nat n)
    requires x >= 1;
    ensures  pow_nat(x,n) >= 1;
{
    switch(n) {
    case zero:
    case succ(n0):
        pow_nat_pos(x,n0);
        my_mul_mono_l(1,x,pow_nat(x,n0));
    }
}

lemma void pow_plus(int x,nat y,int z)
    requires z >= 0;
    ensures  pow_nat(x,nat_of_int(int_of_nat(y)+z))
        ==   pow_nat(x,y)*pow_nat(x,nat_of_int(z));
{
    switch(y) {
    case zero:
    case succ(y0):
        pow_plus(x,y0,z);
        mul_assoc(x,pow_nat(x,y0),pow_nat(x,nat_of_int(z)));
        assert nat_of_int(int_of_nat(y)+z)
            == succ(nat_of_int(int_of_nat(y0)+z));
    }
}

lemma void pow_times1(int x,int y,nat z)
    requires true;
    ensures  pow_nat(x,z)*pow_nat(y,z)
        ==   pow_nat(x*y,z);
{
    switch(z) {
    case zero:
    case succ(z0):
        pow_times1(x,y,z0);
        mul_3var(x,pow_nat(x,z0),y*pow_nat(y,z0));
        mul_3var(pow_nat(x,z0),y,pow_nat(y,z0));
        mul_3var(x,y,pow_nat(x,z0)*pow_nat(y,z0));
        assert pow_nat(x,z)*pow_nat(y,z)
            == (x*pow_nat(x,z0))*(y*pow_nat(y,z0));
        assert pow_nat(x,z)*pow_nat(y,z)
            == x*(pow_nat(x,z0)*(y*pow_nat(y,z0)));
        assert pow_nat(x,z)*pow_nat(y,z)
            == x*(y*(pow_nat(x,z0)*pow_nat(y,z0)));
    }
}

lemma void pow_times2(int x,nat y,int z)
    requires z >= 0;
    ensures  pow_nat(x,nat_of_int(int_of_nat(y)*z))
        ==   pow_nat(pow_nat(x,y),nat_of_int(z));
{
    switch(y) {
    case zero:
    case succ(y0):
        assert nat_of_int(int_of_nat(y))
            == succ(nat_of_int(int_of_nat(y0)));
        note_eq( int_of_nat(y) , 1+int_of_nat(y0));
        note_eq((1+int_of_nat(y0))*z,z + int_of_nat(y0)*z);

        assert pow_nat(x,nat_of_int(int_of_nat(y)*z))
            == pow_nat(x,nat_of_int((1+int_of_nat(y0))*z));
        assert pow_nat(x,nat_of_int(int_of_nat(y)*z))
            == pow_nat(x,nat_of_int(z + int_of_nat(y0)*z));
        my_mul_mono_r(int_of_nat(y0),0,z);
        pow_plus(x,nat_of_int(z),int_of_nat(y0)*z);
        assert pow_nat(x,nat_of_int(int_of_nat(y)*z))
            == pow_nat(x,nat_of_int(z))
              *pow_nat(x,nat_of_int(int_of_nat(y0)*z));
        pow_times2(x,y0,z);
        pow_times1(x,pow_nat(x,y0),nat_of_int(z));
    }
}

lemma void pow_monotonic(int x,nat y,nat z)
    requires x > 1 &*& int_of_nat(y) < int_of_nat(z);
    ensures  pow_nat(x,y) < pow_nat(x,z);
{
    switch(y) {
    case zero:
        switch(z) {
        case zero: assert false;
        case succ(z0):
            pow_nat_pos(x,z0);
            my_mul_mono_r(x,1,pow_nat(x,z0));
        }
    case succ(y0):
        switch(z) {
        case zero: assert false;
        case succ(z0):
            pow_monotonic(x,y0,z0);
            my_mul_strict_mono_r(x,pow_nat(x,y0),pow_nat(x,z0));
        }
    }
}

lemma void pow_soft_monotonic(int x,nat y,nat z)
    requires x >= 1 &*& int_of_nat(y) <= int_of_nat(z);
    ensures  pow_nat(x,y) <= pow_nat(x,z);
{
    if(x > 1 && int_of_nat(y) != int_of_nat(z)) pow_monotonic(x,y,z);
    else if(int_of_nat(y) == int_of_nat(z)) {
        assert nat_of_int(int_of_nat(y)) == y;
        assert nat_of_int(int_of_nat(z)) == z;
        assert pow_nat(x,y) == pow_nat(x,z);
    } else { assert x == 1;
        assert pow_nat(x,y) == 1;
        assert pow_nat(x,z) == 1;
    }
}


@*/

