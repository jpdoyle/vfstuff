//@ #include "util.gh"

/*@

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

@*/

