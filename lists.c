/*@ #include "lists.gh" @*/

/*@

lemma_auto(nth_of(n,l))
void nth_of_bounds_auto<t>(int n,list<t> l)
    requires true;
    ensures  (nth_of(n,l) != none) == (n >= 0 && n < length(l));
{ nth_of_bounds(n,l); }

lemma_auto(remove(pair(k,v),l))
void remove_assoc_of_distinct<s,t>(s k, t v, ASSOC(s,t) l)
    requires distinct(keys(l)) && mem(pair(k,v),l);
    ensures  remove(pair(k,v),l) == remove_assoc(k,l);
{
    switch(l) {
    case nil:
    case cons(lv,vs):
        TRIVIAL_PAIR(lv)
        if(k == fst(lv)) {
            assert !mem(k,keys(vs));
            if(mem(pair(k,v),vs)) {
                mem_keys(k,v,vs);
                assert false;
            }
            assert !mem(pair(k,v),vs);
        } else {
            remove_assoc_of_distinct(k,v,vs);
        }
    }
}

lemma_auto(is_permutation(keys(a),keys(b)))
void keys_permutation<s,t>(ASSOC(s,t) a, ASSOC(s,t) b)
    requires is_permutation(a,b) && distinct(keys(a))
        &&   distinct(keys(b));
    ensures  !!is_permutation(keys(a),keys(b));
{
    switch(a) {
    case nil:
    case cons(x,xs):
        TRIVIAL_PAIR(x)
        assert remove(x,b) == remove_assoc(fst(x),b);
        assert keys(remove_assoc(fst(x),b)) == remove(fst(x), keys(b));
        assert !!distinct(keys(b));
        distinct_remove(fst(x), keys(b));
        assert !!distinct(keys(remove(x,b)));
        keys_permutation(xs,remove(x,b));
        mem_keys(fst(x),snd(x),b);
        assert !!mem(fst(x),keys(b));
    }
}

lemma_auto(drop(n,append(p,s))) void drop_of_append<t>(
        int n, list<t> p, list<t> s)
    requires n == length(p);
    ensures drop(n,append(p,s)) == s;
{
    switch(p) {
    case nil: return;
    case cons(x,xs):
        drop_of_append(n-1, xs, s);
        assert drop(n-1, append(xs,s)) == s;
        assert append(p,s) == append(cons(x,xs),s);
        assert append(p,s) == cons(x,append(xs,s));
        assert drop(n,append(p,s)) == drop(n-1,append(xs,s));
    }
}

lemma_auto(take(n,append(p,s))) void take_of_append<t>(
        int n, list<t> p, list<t> s)
    requires n == length(p);
    ensures take(n,append(p,s)) == p;
{ LIST_INDUCTION(p,ps,take_of_append(n-1,ps,s)) }

lemma_auto(all_eq(drop(n,l),x)) void all_eq_drop<t>(list<t> l, int n,
        t x)
    requires n >= 0 && n <= length(l) && all_eq(l,x);
    ensures  !!all_eq(drop(n,l),x);
{
    switch(l) {
    case nil: return;
    case cons(v,vs):
        if(n > 0) {
            all_eq_drop(vs,n-1,x);
        }
    }
}

lemma_auto(all_eq(append(a,b),x))
void all_eq_append<t>(list<t> a,list<t> b, t x)
    requires true;
    ensures  all_eq(append(a,b),x) == (all_eq(a,x) && all_eq(b,x));
{ LIST_INDUCTION(a,as,all_eq_append(as,b,x)) }

lemma_auto(all_eq(reverse(l),x))
void all_eq_reverse<t>(list<t> l, t x)
    requires true;
    ensures  all_eq(reverse(l),x) == all_eq(l,x);
{
    switch(l) {
    case nil:
    case cons(v,vs):
        all_eq_append(reverse(vs),{v},x);
        all_eq_reverse(vs,x);
    }
}

lemma_auto(take(n,append(p,s))) void take_of_append_exact<t>(
        int n, list<t> p, list<t> s)
    requires n == length(p);
    ensures take(n,append(p,s)) == p;
{ LIST_INDUCTION(p,ps,if(n != 0) take_of_append_exact(n-1,ps,s)) }

lemma_auto(take(n,append(p,s))) void take_of_append_r<t>(
        int n, list<t> p, list<t> s)
    requires n >= length(p);
    ensures take(n,append(p,s)) == append(p,take(n-length(p),s));
{ LIST_INDUCTION(p,ps,take_of_append_r(n-1,ps,s)) }

lemma_auto(drop(n,drop(m,l)))
void drop_n_of_drop_m<t>(int n, int m, list<t> l)
    requires n >= 0 && m >= 0;
    ensures  drop(n,drop(m,l)) == drop(n+m,l);
{
    switch(l) {
        case nil:
        case cons(x,xs):
            if(n != 0) {
                drop_n_of_drop_m(n-1,m,xs);
            }
            if(m != 0) {
                drop_n_of_drop_m(n,m-1,xs);
            }
    }
}

lemma_auto(drop(n,take(m,l)))
void drop_n_of_take_m<t>(int n, int m, list<t> l)
    requires n >= 0 && m >= 0 && m >= n && m <= length(l);
    ensures  drop(n,take(m,l)) == take(m-n,drop(n,l));
{
    switch(l) {
        case nil:
        case cons(x,xs):
            if(n != 0 && m != 0) {
                drop_n_of_take_m(n-1,m-1,xs);
                assert drop(n,take(m,l))
                    == drop(n,cons(x,take(m-1,xs)));
                assert drop(n,take(m,l))
                    == drop(n-1,take(m-1,xs));
                assert drop(n,take(m,l))
                    == take(m-n,drop(n-1,xs));
                assert drop(n,take(m,l))
                    == take(m-n,drop(n,l));
            }
    }
}

lemma_auto(take(n,take(m,l)))
void take_n_of_take_m<t>(int n, int m, list<t> l)
    requires n >= 0 && m >= 0 && m >= n && m <= length(l);
    ensures  take(n,take(m,l)) == take(n,l);
{
    switch(l) {
    case nil:
    case cons(x,xs):
        if(n != 0 && m != 0) {
            take_n_of_take_m(n-1,m-1,xs);
        }
    }
}

lemma_auto(all_eq(take(n,l),v))
void all_eq_take<t>(int n, list<t> l, t v)
    requires n >= 0 && n <= length(l) && all_eq(l,v);
    ensures  !!all_eq(take(n,l),v);
{
    switch(l) {
    case nil:
    case cons(x,xs):
        if(n != 0) {
            all_eq_take(n-1,xs,v);
        }
    }
}

lemma void all_eq_elim<t>(list<t> l, t x, t y)
    requires !!all_eq(l,x) &*& !!mem(y,l);
    ensures  y == x;
{ LIST_INDUCTION(l,xs,if(mem(y,xs)) all_eq_elim(xs,x,y)) }

lemma //_auto(is_permutation(a,b))
void permutation_length<t>(list<t> a, list<t> b)
    requires !!is_permutation(a,b);
    ensures  length(a) == length(b);
{
    switch(a) {
    case nil: return;
    case cons(x,xs):
        assert length(remove(x,b)) + 1 == length(b);
        permutation_length(xs,remove(x,b));
    }
}

lemma_auto(remove(x,append(a,b)))
void remove_append<t>(t x, list<t> a, list<t> b)
    requires !!mem(x,a);
    ensures  remove(x,append(a,b)) == append(remove(x,a),b);
{
    switch(a) {
    case nil:
    case cons(ax,axs):
        if(mem(x,axs)) remove_append(x,axs,b);
    }
}

lemma_auto(is_permutation(a,b))
void permutation_symm<t>(list<t> a, list<t> b)
    requires true;
    ensures  is_permutation(a,b) == is_permutation(b,a);
{
    switch(a) {
    case nil:
        switch(b) { case nil: case cons(bx,bxs): }
    case cons(x,xs):
        switch(b) { case nil: case cons(bx,bxs): }
        permutation_symm(xs,remove(x,b));
        if(is_permutation(a,b)) {
            assert !!is_permutation(xs,remove(x,b));
            is_perm_cons_remove(b,x);
            is_perm_transitive(b, cons(x, remove(x,b)), a);
        } else if(is_permutation(b,a)) {
            assert remove(x,a) == xs;
            is_perm_remove(b,a,x);
            is_perm_mem(b,a,x);
            assert !!is_permutation(remove(x,b),remove(x,a));
            assert !!is_permutation(remove(x,b),xs);
            assert !!is_permutation(xs,remove(x,b));
            assert !!is_permutation(a,b);
            assert false;
        }
    }
}

lemma t filter_diff<t>(fixpoint(t,bool) f1, fixpoint(t,bool) f2, list<t> l)
    requires filter(f1,l) != filter(f2,l);
    ensures  !!mem(result,l) &*& f1(result) != f2(result);
{
    switch(l) {
    case nil: assert false;
    case cons(x,xs):
        if(f1(x) != f2(x)) { return x; }
        return filter_diff(f1,f2,xs);
    }
}

lemma t filter_effect<t>(fixpoint(t,bool) f, list<t> l)
    requires filter(f,l) != l;
    ensures  !!mem(result,l) &*& !f(result);
{ filter_id(l); return filter_diff(f,(constf)(true),l); }

lemma_auto(mem(x,repeat(v,n))) void mem_repeat<t>(t x, t v, nat n)
    requires !!mem(x,repeat(v,n));
    ensures  x == v;
{
    switch(n) {
    case zero:
    case succ(n0):
        switch(repeat(v,n)) {
        case nil: assert false;
        case cons(v0,vs):
            if(x != v0) {
                mem_repeat(x,v,n0);
            }
        }
    }
}

lemma_auto(append(repeat(v,n),repeat(v,m)))
void append_repeat<t>(t v, nat n, nat m)
    requires true;
    ensures  append(repeat(v,n),repeat(v,m))
        ==   repeat(v,nat_of_int(int_of_nat(n)+int_of_nat(m)));
{
    switch(n) {
    case zero:
    case succ(n0):
        append_repeat(v,n0,m);
        assert nat_of_int(int_of_nat(n)+int_of_nat(m))
            == succ(nat_of_int(int_of_nat(n0)+int_of_nat(m)));
    }
}

lemma_auto(forall(repeat(v,n),(bounded)(lo,hi)))
void repeat_bounded(int v, nat n, int lo, int hi)
    requires true;
    ensures  forall(repeat(v,n),(bounded)(lo,hi))
        == (n == zero || bounded(lo,hi,v));
{ NAT_INDUCTION(n,n0,repeat_bounded(v,n0,lo,hi)) }

lemma
void indices_of_inner_correct<t>(t v, list<t> l, int b, int i)
    requires true;
    ensures  mem(i,indices_of_inner(v,l,b))
        ==   (nth_of(i-b,l) == some(v));
{
    switch(l) {
    case nil: return;
    case cons(x,xs):
        indices_of_inner_correct(v,xs,b+1,i);
        nth_of_bounds(i-b,l);
        if(i == b) {
            if(nth_of(i-b,l) != some(v)
               && mem(i,indices_of_inner(v,l,b))) {
                assert false;
            }
            if(x == v) {
                assert nth_of(i-b,l) == some(v);
            } else {
                assert !mem(i,indices_of_inner(v,l,b));
            }
            return;
        }
        /* indices_of_inner(v,xs,b+1,i); */
    }
}

lemma_auto(mem(i,indices_of_inner(v,l,b)))
void indices_of_inner_correct_auto<t>(t v, list<t> l, int b, int i)
    requires !!mem(i,indices_of_inner(v,l,b));
    ensures  (nth_of(i-b,l) == some(v));
{ indices_of_inner_correct(v,l,b,i); }

lemma
void indices_of_inner_bounds<t>(t v, list<t> l, int b, int i)
    requires !!mem(i,indices_of_inner(v,l,b));
    ensures  i >= b &*& i < b+length(l);
{
    switch(l) {
    case nil: assert false;
    case cons(x,xs):
        if(x != v) {
            indices_of_inner_bounds(v,xs,b+1,i);
        }
    }
}

lemma_auto(mem(i,indices_of_inner(v,l,b)))
void indices_of_inner_bounds_auto1<t>(t v, list<t> l, int b, int i)
    requires !!mem(i,indices_of_inner(v,l,b));
    ensures  i >= b;
{ indices_of_inner_bounds(v,l,b,i); }

lemma_auto(mem(i,indices_of_inner(v,l,b)))
void indices_of_inner_bounds_auto2<t>(t v, list<t> l, int b, int i)
    requires !!mem(i,indices_of_inner(v,l,b));
    ensures  i < b+length(l);
{ indices_of_inner_bounds(v,l,b,i); }

lemma void maximum_correct(int x, list<int> l)
    requires !!mem(x,l);
    ensures  !!mem(maximum(l),l) &*& maximum(l) >= x;
{
    switch(l) {
    case nil: assert false;
    case cons(v,vs):
        if(v != x) { maximum_correct(x,vs); }
        switch(vs) {
        case nil:
        case cons(vs_x,vs_xs):
            maximum_correct(vs_x,vs);
        }
    }
}

lemma void maximum_remove(int x,list<int> l)
    requires !!mem(x,l) &*& length(l) > 1;
    ensures  maximum(l) == max_of(x,maximum(remove(x,l)));
{
    switch(l) {
    case nil: assert false;
    case cons(v,vs):
        switch(vs) {
        case nil: assert false;
        case cons(vs_x,vs_xs):
            switch(vs_xs) {
            case nil:
            case cons(x3,rest):
                if(v == x) { return; }
                if(x == vs_x) {
                    assert remove(x,l) == cons(v,vs_xs);
                    assert maximum(l) ==
                        max_of(v,max_of(x,maximum(vs_xs)));
                    assert maximum(l) ==
                        max_of(max_of(v,x),maximum(vs_xs));
                    assert maximum(l) ==
                        max_of(max_of(x,v),maximum(vs_xs));
                    assert maximum(l) ==
                        max_of(x,max_of(v,maximum(vs_xs)));
                    return;
                }
                //TRIVIAL_LIST(vs_xs)
                maximum_remove(x,vs);
            }
        }
    }
}

lemma void maximum_permutation(list<int> a,list<int> b)
    requires !!is_permutation(a,b);
    ensures  maximum(a) == maximum(b);
{
    switch(a) {
    case nil:
    case cons(v,vs):
        permutation_length(a,b);
        maximum_permutation(vs,remove(v,b));
        switch(vs) {
        case nil: TRIVIAL_LIST2(b)
        case cons(vs_x,vs_xs):
            switch(vs_xs) {
            case nil: TRIVIAL_LIST2(b)
            case cons(x3,rest):
                maximum_remove(v,b);
            }
        }
    }
}

lemma
void reverse_ends<t>(t x,list<t> l,t y)
    requires true;
    ensures  reverse(cons(x,append(l,cons(y,nil))))
        ==   cons(y,append(reverse(l),cons(x,nil)));
{
    reverse_append(l,cons(y,nil));
}

@*/

