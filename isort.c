//@ #include <quantifiers.gh>
//@ #include <list.gh>
//@ #include <arrays.gh>

/*@

    lemma_auto(append(l,cons(x,r))) void append_cons<t>(
            list<t> l, t x, list<t> r)
        requires true;
        ensures append(l,cons(x,r)) == append(append(l,{x}),r);
    {
        assert append({x},r) == cons(x,r);
        append_assoc(l,{x},r);
    }

    lemma void head_tail_deconstruct<t>(list<t> l)
        requires l != nil;
        ensures  l == cons(head(l),tail(l));
    {
        switch(l) {
        case nil:
        case cons(x,xs):
        }
    }

    fixpoint bool le(int x, int y) { return x <= y; }
    fixpoint bool ge(int x, int y) { return x >= y; }

    fixpoint bool all_ge(int x, list<int> l) {
        return forall(l,(le)(x));
    }

    fixpoint bool all_le(int x, list<int> l) {
        return forall(l,(ge)(x));
    }

    fixpoint bool sorted(list<int> l) {
        switch(l) {
        case nil: return true;
        case cons(x,xs):
            return all_ge(x,xs) && sorted(xs);
        }
    }

    lemma_auto void sorted_singleton(int x)
        requires true;
        ensures sorted({x}) == true;
    {}

    lemma_auto(length(l)) void zero_length<t>(list<t> l)
        requires true;
        ensures (length(l) == 0) == (l == nil);
    {
        switch(l) {
        case nil:
        case cons(x,xs):
        }
    }

    lemma_auto void sorted_singleton_by_length(list<int> l)
        requires length(l) == 1;
        ensures sorted(l) == true;
    {
        switch(l) {
        case nil:
        case cons(x,xs):
            assert length(l) == 1 + length(xs);
            if(xs != nil) { assert length(xs) != 0; assert false; }
        }
    }

    fixpoint int count_of<t>(t x, list<t> l) {
        switch(l) {
        case nil: return 0;
        case cons(v,vs): return (x == v) ? 1 + count_of(x,vs) : count_of(x,vs);
        }
    }

    lemma void count_of_mem<t>(t x, list<t> l)
        requires true;
        ensures  mem(x,l) ? count_of(x,l) > 0 : count_of(x,l) == 0;
    {
        switch(l) {
        case nil:
        case cons(v,vs):
            count_of_mem(x,vs);
        }
    }

    lemma void count_of_remove<t>(t x, t y, list<t> l)
        requires true;
        ensures  ((x != y || !mem(x,l))
                 ? count_of(y,l) == count_of(y,remove(x,l))
                 : count_of(y,l) == 1+count_of(y,remove(x,l))
                 );
    {
        switch(l) {
        case nil:
        case cons(v,vs):
            if(x != v) {
                count_of_remove(x,y,vs);
            }
        }
    }

    fixpoint bool count_matches<t>(list<t> l, list<t> r, t x) {
        return count_of(x,l) == count_of(x,r);
    }

    fixpoint bool is_permutation<t>(list<t> l, list<t> r) {
        return forall(l,(count_matches)(l,r))
            && forall(r,(count_matches)(l,r));
    }

    lemma_auto void permutation_self<t>(list<t> l)
        requires true;
        ensures  is_permutation(l,l) == true;
    {
        if(!forall(l,(count_matches)(l,l))) {
            t cx = not_forall(l,(count_matches)(l,l));
            assert false;
        }
    }

    lemma_auto(sorted(cons(x,cons(y,suffix))))
    void sorted_cons(int x, int y, list<int> suffix)
        requires x <= y && sorted(cons(y,suffix));
        ensures  sorted(cons(x,cons(y,suffix))) == true;
    {
        if(!sorted(cons(x,cons(y,suffix)))) {
            assert !all_ge(x,cons(y,suffix));
            int cx = not_forall(cons(y,suffix),(le)(x));
            forall_elim(cons(y,suffix),(le)(y),cx);
            assert false;
        }
    }

    fixpoint t flip<r,s,t>(fixpoint(r,s,t) f, s y, r x) {
        return f(x,y);
    }

    lemma void is_permutation_mem(list<int> a, list<int> b)
        requires is_permutation(a,b) == true;
        ensures  forall(a,(flip)(mem,b)) == true;
    {
        if(!forall(a,(flip)(mem,b))) {
            int cx = not_forall(a,(flip)(mem,b));
            forall_elim(a,(count_matches)(a,b),cx);
            count_of_mem(cx,b);
            count_of_mem(cx,a);

            assert false;
        }
    }

    lemma
    void all_ge_permutation(int x, list<int> a, list<int> b)
        requires is_permutation(a,b) == true;
        ensures  all_ge(x,a) == all_ge(x,b);
    {
        if(all_ge(x,a)) {
            if(!all_ge(x,b)) {
                int cx = not_forall(b,(le)(x));
                forall_elim(b,(count_matches)(a,b),cx);

                if(mem(cx,a)) {
                    forall_elim(a,(le)(x),cx);
                    assert false;
                }

                count_of_mem(cx,a);
                count_of_mem(cx,b);
                assert false;
            }
        } else {
            if(all_ge(x,b)) {
                int cx = not_forall(a,(le)(x));
                forall_elim(a,(count_matches)(a,b),cx);
                if(mem(cx,b)) {
                    forall_elim(b,(le)(x),cx);
                    assert false;
                }
                count_of_mem(cx,b);
                count_of_mem(cx,a);
                assert false;
            }
        }
    }

    lemma_auto(is_permutation(cons(x,a),cons(x,b)))
    void permutation_cons<t>(t x, list<t> a, list<t> b)
        requires is_permutation(a,b) == true;
        ensures  is_permutation(cons(x,a),cons(x,b)) == true;
    {
        if(!forall(cons(x,a),
                (count_matches)(cons(x,a),cons(x,b)))) {
            t cx = not_forall(cons(x,a),
                (count_matches)(cons(x,a),cons(x,b)));
            if(cx != x) {
                assert !!mem(cx,a);
                forall_elim(a,(count_matches)(a,b),cx);
                assert !!count_matches(cx,cons(x,a),cons(x,b));
                assert false;
            } else {
                assert count_of(cx,cons(x,a)) == 1 + count_of(cx,a);
                assert count_of(cx,cons(x,b)) == 1 + count_of(cx,b);
                if(mem(x,a)) {
                    forall_elim(a,(count_matches)(a,b),cx);
                } else if(mem(x,b)) {
                    forall_elim(b,(count_matches)(a,b),cx);
                } else {
                    count_of_mem(x,a);
                    count_of_mem(x,b);
                    assert count_of(x,a) == 0;
                    assert count_of(x,b) == 0;
                }
                assert false;
            }
        } else if(!forall(cons(x,b),
                (count_matches)(cons(x,a),cons(x,b)))) {
            t cx = not_forall(cons(x,b),
                (count_matches)(cons(x,a),cons(x,b)));
            if(cx != x) {
                assert !!mem(cx,b);
                forall_elim(b,(count_matches)(a,b),cx);
                assert !!count_matches(cx,cons(x,a),cons(x,b));
                assert false;
            }
        }
    }

    lemma_auto(remove(x,l)) void remove_nonmem<t>(t x, list<t> l)
        requires true;
        ensures  (remove(x,l) == l) == !mem(x,l);
    {
        switch(l) {
        case nil:
        case cons(v,vs):
            if(x != v) {
                remove_nonmem(x,vs);
            }
            if(l == vs) {
                assert length(l) == length(vs);
                assert false;
            }
        }
    }

    lemma_auto(is_permutation(remove(x,a),remove(x,b)))
    void permutation_remove<t>(t x, list<t> a, list<t> b)
        requires (mem(x,a) == mem(x,b));
        ensures  is_permutation(a,b)
            ==   is_permutation(remove(x,a),remove(x,b));
    {
        if(!mem(x,a)) {
            assert remove(x,a) == a;

            assert remove(x,b) == b;
        } else {

            if(is_permutation(a,b) &&
               !is_permutation(remove(x,a),remove(x,b))) {

                if(!forall(remove(x, a),
                           (count_matches)(remove(x, a),
                                           remove(x, b)))) {
                    t cx = not_forall(remove(x, a),
                           (count_matches)(remove(x, a),
                                           remove(x, b)));
                    mem_remove_mem(cx,x,a);
                    forall_elim(a,(count_matches)(a,b),cx);
                    count_of_remove(x,cx,a);
                    count_of_remove(x,cx,b);
                    assert false;
                }
                if(!forall(remove(x, b),
                           (count_matches)(remove(x, a),
                                           remove(x, b)))) {
                    t cx = not_forall(remove(x, b),
                           (count_matches)(remove(x, a),
                                           remove(x, b)));
                    mem_remove_mem(cx,x,b);
                    forall_elim(b,(count_matches)(a,b),cx);
                    count_of_remove(x,cx,a);
                    count_of_remove(x,cx,b);
                    assert false;
                }

                assert false;
            }

            if(!is_permutation(a,b) &&
               is_permutation(remove(x,a),remove(x,b))) {

                if(!forall(a, (count_matches)(a, b))) {
                    t cx = not_forall(a, (count_matches)(a, b));
                    count_of_remove(x,cx,a);
                    count_of_remove(x,cx,b);

                    count_of_mem(cx,remove(x,a));
                    count_of_mem(cx,remove(x,b));
                    count_of_mem(x,a);
                    count_of_mem(x,b);

                    if(cx != x) {
                        neq_mem_remove(cx,x,a);
                        neq_mem_remove(cx,x,b);
                    }

                    if(mem(cx,remove(x,a))) {
                        forall_elim(remove(x,a),
                            (count_matches)(
                                remove(x,a), remove(x,b)),
                            cx);

                        assert false;
                    } else {
                        assert x == cx;
                        assert count_of(cx,a) == 1;
                        assert count_of(cx,b) >= 1;
                        if(mem(cx,remove(x,b))) {
                            forall_elim(remove(x,b),
                                (count_matches)(
                                    remove(x,a), remove(x,b)),
                                cx);
                            assert false;
                        }
                    }

                    //assert count_of(cx,remove(x,a))
                    //    == count_of(cx,remove(x,b));

                    assert false;
                }
                if(!forall(b, (count_matches)(a, b))) {
                    t cx = not_forall(b, (count_matches)(a, b));
                    count_of_remove(x,cx,a);
                    count_of_remove(x,cx,b);

                    count_of_mem(cx,remove(x,a));
                    count_of_mem(cx,remove(x,b));
                    count_of_mem(x,a);
                    count_of_mem(x,b);

                    if(cx != x) {
                        neq_mem_remove(cx,x,a);
                        neq_mem_remove(cx,x,b);
                    }

                    if(mem(cx,remove(x,b))) {
                        forall_elim(remove(x,b),
                            (count_matches)(
                                remove(x,a), remove(x,b)),
                            cx);

                        assert false;
                    } else {
                        assert x == cx;
                        assert count_of(cx,b) == 1;
                        assert count_of(cx,a) >= 1;
                        if(mem(cx,remove(x,a))) {
                            forall_elim(remove(x,a),
                                (count_matches)(
                                    remove(x,a), remove(x,b)),
                                cx);
                            assert false;
                        }
                    }

                    assert false;
                }

                assert false;
            }
        }
    }

    lemma_auto(is_permutation(a,b))
    void permutation_symmetric<t>(list<t> a, list<t> b)
        requires true;
        ensures is_permutation(a,b) == is_permutation(b,a);
    {
        if(is_permutation(a,b)) {
            if(!forall(a,(count_matches)(b,a))) {
                t cx = not_forall(a,(count_matches)(b,a));
                forall_elim(a,(count_matches)(a,b),cx);
                assert false;
            } else if(!forall(b,(count_matches)(b,a))) {
                t cx = not_forall(b,(count_matches)(b,a));
                forall_elim(b,(count_matches)(a,b),cx);
                assert false;
            }
        } else {
            if(!forall(a,(count_matches)(a,b))) {
                t cx = not_forall(a,(count_matches)(a,b));
                if(forall(a,(count_matches)(b,a))) {
                    forall_elim(a,(count_matches)(b,a),cx);
                    assert false;
                }
            } else if(!forall(b,(count_matches)(a,b))) {
                t cx = not_forall(b,(count_matches)(a,b));
                if(forall(b,(count_matches)(b,a))) {
                    forall_elim(b,(count_matches)(b,a),cx);
                    assert false;
                }
            }
        }
    }

    lemma_auto(is_permutation(append(prefix,a),append(prefix,b)))
    void permutation_prepend(list<int> prefix, list<int> a, list<int> b)
        requires is_permutation(a,b) == true;
        ensures  is_permutation(append(prefix,a),append(prefix,b)) == true;
    {
        switch(prefix) {
        case nil:
        case cons(x,xs):
            permutation_prepend(xs,a,b);
            permutation_cons(x,append(xs,a),append(xs,b));
        }
    }

    lemma
    void permutation_transitive<t>(list<t> a, list<t> b, list<t> c)
        requires is_permutation(a,b) && is_permutation(b,c);
        ensures  is_permutation(a,c) == true;
    {
        if(!forall(a,(count_matches)(a,c))) {
            t cx = not_forall(a,(count_matches)(a,c));
            count_of_mem(cx,a);
            count_of_mem(cx,b);
            forall_elim(a,(count_matches)(a,b),cx);
            forall_elim(b,(count_matches)(b,c),cx);
            assert false;
        } else if(!forall(c,(count_matches)(a,c))) {
            t cx = not_forall(c,(count_matches)(a,c));
            count_of_mem(cx,c);
            count_of_mem(cx,b);
            forall_elim(c,(count_matches)(b,c),cx);
            forall_elim(b,(count_matches)(a,b),cx);
            assert false;
        }
    }

    lemma_auto(is_permutation(cons(x,cons(y,a)),cons(y,cons(x,a))))
    void permutation_swap<t>(t x, t y, list<t> a)
        requires true;
        ensures  is_permutation(
            cons(x,cons(y,a)), cons(y,cons(x,a))) == true;
    {
        list<t> l = cons(x,cons(y,a));
        list<t> r = cons(y,cons(x,a));
        if(x != y) {
            if(!forall(l, (count_matches)(l,r))) {
                t cx = not_forall(l, (count_matches)(l,r));
                assert false;
            }
        }
    }

    lemma void permutation_length<t>(list<t> a, list<t> b)
        requires !!is_permutation(a,b);
        ensures  length(a) == length(b);
    {
        switch(a) {
        case nil:
            switch(b) {
            case nil:
            case cons(bx,bxs):
                forall_elim(b,(count_matches)(a,b),bx);
                count_of_mem(bx,b);
                count_of_mem(bx,a);
                assert !!mem(bx,a);
                assert false;
            }
        case cons(ax,axs):
            forall_elim(a,(count_matches)(a,b),ax);
            count_of_mem(ax,a);
            count_of_mem(ax,b);
            permutation_remove(ax,a,b);
            permutation_length(axs,remove(ax,b));
        }
    }

    lemma void sorted_unique(list<int> a, list<int> b)
        requires !!sorted(a) &*& !!sorted(b)
            &*&  !!is_permutation(a,b);
        ensures  a == b;
    {
        switch(a) {
        case nil:
            permutation_length(a,b);
        case cons(ax,axs):
            permutation_length(a,b);
            switch(b) {
            case nil: assert false;
            case cons(bx,bxs):

                if(!mem(ax,b)) {
                    forall_elim(a,(count_matches)(a,b),ax);
                    count_of_mem(ax,b);
                    count_of_mem(ax,a);
                    assert false;
                }

                if(!mem(bx,a)) {
                    forall_elim(b,(count_matches)(a,b),bx);
                    count_of_mem(bx,a);
                    count_of_mem(bx,b);
                    assert false;
                }

                if(ax > bx) {
                    forall_elim(axs,(le)(ax), bx);
                    assert false;
                }
                if(ax < bx) {
                    forall_elim(bxs,(le)(bx), ax);
                    assert false;
                }

                if(!forall(bxs,(count_matches)(axs,bxs))) {
                    int cx = not_forall(bxs,(count_matches)(axs,bxs));
                    forall_elim(b,(count_matches)(a,b),cx);
                    assert false;
                }

                if(!forall(axs,(count_matches)(axs,bxs))) {
                    int cx = not_forall(axs,(count_matches)(axs,bxs));
                    forall_elim(a,(count_matches)(a,b),cx);
                    assert false;
                }

                sorted_unique(axs,bxs);
            }
        }
    }

  @*/

void isort(int* arr, int n)
    /*@ requires arr[..n] |-> ?l; @*/
    /*@ ensures  arr[..n] |-> ?new_l &*& !!sorted(new_l)
            &*&  !!is_permutation(l,new_l); @*/
    /*@ terminates; @*/
{
    int i,j;
    for(i = n; i > 0; --i)
        /*@ invariant arr[..i]  |-> ?prefix
                 &*&  arr[i..n] |-> ?suffix
                 &*&  !!sorted(suffix)
                 &*&  !!is_permutation(append(prefix,suffix),l)
                 &*&  i >= 0 &*& i <= n; @*/
        /*@ decreases i; @*/
    {
        /*@ ints_split(arr,i-1); @*/
        /*@ assert arr[i-1] |-> ?v; @*/
        for(j=i-1; j+1 < n; ++j)
            /*@ requires j >= 0 &*& j+1 <= n
                    &*& arr[j+1..n] |-> ?ins_suffix
                    &*& arr[j]      |-> ?ins_v
                    &*& !!sorted(ins_suffix); @*/
            /*@ ensures arr[old_j..n] |-> ?new_l
                    &*& !!sorted(new_l)
                    &*& !!is_permutation(cons(ins_v,ins_suffix),new_l)
                    ; @*/
            /*@ decreases n-j-1; @*/
        {
            /*@ open ints(arr+j+1,_,_); @*/
            if(arr[j] <= arr[j+1]) { break; }

            int tmp = arr[j+1];
            arr[j+1] = arr[j];
            arr[j] = tmp;

            /*@ recursive_call(); @*/
            /*@ {
                assert arr[old_j]      |-> ?next_v;
                assert arr[old_j+1..n] |-> ?next_suffix;

                list<int> swap_suffix = cons(ins_v, tail(ins_suffix));

                permutation_transitive(
                    cons(next_v,next_suffix),
                    cons(next_v,swap_suffix),
                    cons(ins_v,ins_suffix));
                all_ge_permutation(next_v, swap_suffix, next_suffix);
            } @*/

        }
        /*@ {
            assert arr[..(i-1)]  |-> ?new_prefix;
            assert arr[(i-1)..n] |-> ?new_suffix;
            permutation_transitive(append(new_prefix,new_suffix),
                                   append(new_prefix,cons(v,suffix)),l);
        } @*/
    }
}

