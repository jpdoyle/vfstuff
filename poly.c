/*@ #include "poly.gh" @*/

#if 0
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif

/*@

lemma_auto(poly_is_zero(p)) void poly_all_eq_zero(list<int> p)
    requires true;
    ensures  all_eq(p,0) == poly_is_zero(p);
{ LIST_INDUCTION(p,ps,poly_all_eq_zero(ps)) }

lemma_auto(poly_eval(p,pt))
void poly_eval_zero(list<int> p,int pt)
    requires !!poly_is_zero(p);
    ensures  poly_eval(p,pt) == 0;
{ LIST_INDUCTION(p,ps,poly_eval_zero(ps,pt)) }

lemma int poly_eval_neg(list<int> p,int pt)
    requires pt >= 0 &*& poly_eval(p,pt) < 0;
    ensures  result < 0 &*& !!mem(result,p);
{
    switch(p) {
    case nil: assert false;
    case cons(x,xs):
        assert x + pt*poly_eval(xs,pt) < 0;
        if(x < 0) return x;
        assert pt*poly_eval(xs,pt) < 0;
        my_inv_mul_strict_mono_r(pt, poly_eval(xs,pt), 0);
        return poly_eval_neg(xs,pt);
    }
}

lemma_auto(minimize(p)) void minimal_zero(list<int> p)
    requires true;
    ensures  (minimize(p) == nil) == poly_is_zero(p);
{ TRIVIAL_LIST(p) }


lemma_auto(minimal(minimize(p))) void minimal_minimize(list<int> p)
    requires true;
    ensures  !!minimal(minimize(p));
{
    ALREADY_PROVEN()
    switch(p) {
    case nil: return;
    case cons(x,xs):
        if(poly_is_zero(xs)) { }
        TRIVIAL_LIST(xs)
        minimal_minimize(xs);
    }
}


lemma_auto(minimal(p)) void minimize_minimal(list<int> p)
    requires !!minimal(p);
    ensures  minimize(p) == p;
{
    ALREADY_PROVEN()
    switch(p) {
    case nil: return;
    case cons(x,xs):
        TRIVIAL_LIST(xs)
        minimize_minimal(xs);
    }
}

lemma void minimal_append(list<int> a,list<int> b)
    requires !!minimal(b) &*& b != nil;
    ensures  !!minimal(append(a,b));
{
    switch(a) {
    case nil:
    case cons(x,xs):
        switch(append(xs,b)) {
        case nil:
            assert length(append(xs,b)) == 0;
            assert false;
        case cons(xx,xxs):
            minimal_append(xs,b);
        }
    }
}

lemma void minimize_append_r(list<int> a,list<int> b)
    requires minimize(b) != nil;
    ensures  minimize(append(a,b)) == append(a,minimize(b));
{
    switch(a) {
    case nil:
    case cons(x,xs):
        switch(append(xs,b)) {
        case nil:
            assert length(append(xs,b)) == 0;
            assert false;
        case cons(xx,xxs):
            minimize_append_r(xs,b);
        }
    }
}

lemma void minimize_append_l(list<int> a,list<int> b)
    requires !!minimal(a);
    ensures  minimize(append(a,b)) == append(a,minimize(b));
{
    switch(a) {
    case nil:
    case cons(x,xs):
        switch(xs) {
        case nil:
        case cons(xx,xxs):
            minimize_append_l(xs,b);
        }
    }
}

lemma_auto(mem(x,minimize(p)))
void mem_minimize(int x, list<int> p)
    requires x != 0;
    ensures  mem(x,minimize(p)) == mem(x,p);
{
    switch(p) {
    case nil:
    case cons(v,vs):
        mem_minimize(x,vs);
    }
}

lemma void minimize_is_prefix(list<int> p)
    requires true;
    ensures  take(length(minimize(p)),p)
        ==   minimize(p);
{
    switch(p) {
    case nil:
    case cons(x,xs):
        minimize_is_prefix(xs);
    }
}

lemma_auto(minimize(minimize(p)))
void minimize_idempotent(list<int> p)
    requires true;
    ensures  minimize(minimize(p)) == minimize(p);
{ assert !!minimal(minimize(p)); }


lemma_auto(poly_eval(minimize(p),pt))
void minimize_eval(list<int> p, int pt)
    requires true;
    ensures  poly_eval(minimize(p),pt) == poly_eval(p,pt);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil: return;
    case cons(x,xs):
        TRIVIAL_LIST(xs)
        minimize_eval(xs,pt);
    }
}


lemma_auto(poly_scale(s,p))
void scale_nil(int s,list<int> p)
    requires true;
    ensures  (poly_scale(s,p) == nil) == (p == nil);
{ TRIVIAL_LIST(p) }


lemma_auto(poly_scale(s,nil))
void scale_nil_simple(int s)
    requires true;
    ensures  poly_scale(s,nil) == nil;
{}


lemma_auto(poly_scale(0,p))
void scale_0(list<int> p)
    requires true;
    ensures  !!poly_is_zero(poly_scale(0,p));
{ LIST_INDUCTION(p,xs,scale_0(xs)) }


lemma_auto(poly_scale(1,p))
void scale_1(list<int> p)
    requires true;
    ensures  p == poly_scale(1,p);
{ LIST_INDUCTION(p,xs,scale_1(xs)) }


lemma_auto(poly_scale(s,p))
void scale_nonzero(int s,list<int> p)
    requires s != 0;
    ensures  poly_is_zero(poly_scale(s,p)) == poly_is_zero(p);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        mul_abs_commute(s,x);
        assert abs(s*x) == abs(s)*abs(x);
        if(x != 0 && s*x == 0) {
            my_mul_mono_r(abs(s),1,abs(x));
            assert false;
        }
        scale_nonzero(s,xs);
    }
}


lemma //_auto(length(poly_scale(s,p)))
void len_scale(int s, list<int> p)
    requires true;
    ensures  length(poly_scale(s,p)) == length(p);
{ LIST_INDUCTION(p,xs,len_scale(s,xs)) }


lemma_auto(minimize(poly_scale(s,p)))
void minimize_scale(int s, list<int> p)
    requires s != 0;
    ensures  minimize(poly_scale(s,p))
        ==   poly_scale(s,minimize(p));
{ LIST_INDUCTION(p,xs,minimize_scale(s,xs)) }


lemma_auto(poly_plus(p,q))
void poly_plus_commutes(list<int> p, list<int> q)
    requires true;
    ensures  poly_plus(p,q) == poly_plus(q,p);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
        switch(q) {
        case nil:
        case cons(y,ys):
        }
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys): poly_plus_commutes(xs,ys);
        }
    }
}


lemma
void poly_plus_assoc(list<int> p, list<int> q, list<int> r)
    requires true;
    ensures  poly_plus(p,poly_plus(q,r))
        ==   poly_plus(poly_plus(p,q),r);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
        TRIVIAL_LIST(q) TRIVIAL_LIST(r)
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys):
            switch(r) {
            case nil:
            case cons(z,zs):
                poly_plus_assoc(xs,ys,zs);
            }
        }
    }
}


lemma_auto(poly_plus(p,q))
void poly_plus_nil_only(list<int> p,list<int> q)
    requires true;
    ensures  (poly_plus(p,q) == nil) == (p == nil && q == nil);
{ TRIVIAL_LIST(p) TRIVIAL_LIST(q) }


lemma
void len_plus_bound(list<int> p, list<int> q)
    requires true;
    ensures  length(poly_plus(p,q)) >= length(q)
        &*&  length(poly_plus(p,q)) >= length(p);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys): len_plus_bound(xs,ys);
        }
    }
}


lemma_auto(length(poly_plus(p,q)))
void len_plus_boundi_auto1(list<int> p, list<int> q)
    requires true;
    ensures  length(poly_plus(p,q)) >= length(p);
{ len_plus_bound(p,q); }


lemma_auto(length(poly_plus(p,q)))
void len_plus_boundi_auto2(list<int> p, list<int> q)
    requires true;
    ensures  length(poly_plus(p,q)) >= length(q);
{ len_plus_bound(p,q); }


lemma_auto(length(poly_plus(p,q)))
void len_plus(list<int> p, list<int> q)
    requires length(poly_plus(p,q)) != length(p);
    ensures  length(poly_plus(p,q)) == length(q);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys): len_plus(xs,ys);
        }
    }
}


lemma_auto(minimal(poly_scale(s,p)))
void scale_minimal(int s, list<int> p)
    requires s != 0;
    ensures  minimal(poly_scale(s,p)) == minimal(p);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil: return;
    case cons(x,xs):
        TRIVIAL_LIST(xs)
        mul_abs_commute(s,x);
        assert abs(s*x) == abs(s)*abs(x);
        if(x != 0 && s*x == 0) {
            my_mul_mono_r(abs(s),1,abs(x));
            assert false;
        }
        scale_minimal(s,xs);
    }
}


lemma //_auto(poly_scale(a,poly_scale(b,p)))
void poly_scale_mul(int a, int b, list<int> p)
    requires true;
    ensures  poly_scale(a,poly_scale(b,p)) == poly_scale(a*b,p);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil: return;
    case cons(x,xs):
        mul_assoc(a,b,x);
        assert poly_scale(a,poly_scale(b,p))
            == cons((a*b)*x,poly_scale(a,poly_scale(b,xs)));
        poly_scale_mul(a,b,xs);
    }
}


lemma
void poly_linear(int a, int b, list<int> p)
    requires true;
    ensures  poly_plus(poly_scale(a,p),poly_scale(b,p))
        ==   poly_scale(a+b,p);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        poly_linear(a,b,xs);
        assert poly_scale(a+b,p) == cons((a+b)*x,
               poly_plus(poly_scale(a,xs),poly_scale(b,xs)));
    }
}


lemma
void poly_linear2(int a, list<int> p, list<int> q)
    requires true;
    ensures  poly_plus(poly_scale(a,p),poly_scale(a,q))
        ==   poly_scale(a,poly_plus(p,q));
{
    switch(p) {
    case nil:
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys):
            note_eq( a*x + a*y , a*(x+y));
            poly_linear2(a,xs,ys);
        }
    }
}


lemma_auto(poly_eval(poly_scale(s,p),pt))
void poly_scale_eval(int s, list<int> p, int pt)
    requires true;
    ensures  poly_eval(poly_scale(s,p),pt) == s*poly_eval(p,pt);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        poly_scale_eval(s,xs,pt);
        assert poly_eval(poly_scale(s,p),pt)
            == s*x + pt*poly_eval(poly_scale(s,xs),pt);
        assert poly_eval(poly_scale(s,p),pt)
            == s*x + pt*(s*poly_eval(xs,pt));
        mul_assoc(pt,s,poly_eval(xs,pt));
        mul_assoc(s,pt,poly_eval(xs,pt));
        mul_commutes(s,pt);
        assert poly_eval(poly_scale(s,p),pt)
            == s*x + s*(pt*poly_eval(xs,pt));
        assert poly_eval(poly_scale(s,p),pt)
            == s*(x + pt*poly_eval(xs,pt));
        mul_abstract_def(s,x + pt*poly_eval(xs,pt));
        assert poly_eval(poly_scale(s,p),pt)
            == s*poly_eval(p,pt);
    }
}


lemma void poly_zero_eval(list<int> p, int pt)
    requires poly_eval(p,pt) != 0;
    ensures  !poly_is_zero(p);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        if(poly_is_zero(p)) {
            if(pt == 0) { assert false; }
            zero_mul_unique(pt,poly_eval(xs,pt));
            poly_zero_eval(xs,pt);
            assert false;
        }
    }
}


lemma_auto(poly_eval(poly_plus(p,q),pt))
void poly_plus_eval(list<int> p, list<int> q, int pt)
    requires true;
    ensures  poly_eval(poly_plus(p,q),pt)
        ==   poly_eval(p,pt) + poly_eval(q,pt);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys):
            poly_plus_eval(xs,ys,pt);

            assert poly_eval(poly_plus(p,q),pt)
                == x+y+pt*(poly_eval(poly_plus(xs,ys),pt));
            //mul_abstract_def(pt,poly_eval(poly_plus(xs,ys),pt));
            assert poly_eval(poly_plus(p,q),pt)
                == x+y+pt*(poly_eval(xs,pt) + poly_eval(ys,pt));
            note_eq( pt*(poly_eval(xs,pt) + poly_eval(ys,pt)),
                     pt*poly_eval(xs,pt) + pt*poly_eval(ys,pt));
            assert poly_eval(poly_plus(p,q),pt)
                == x+y+pt*poly_eval(xs,pt) + pt*poly_eval(ys,pt);
        }
    }
}


lemma_auto(poly_eval(poly_mul(a,b),pt))
void poly_mul_eval(list<int> a, list<int> b, int pt)
    requires true;
    ensures  poly_eval(poly_mul(a,b),pt)
        ==   poly_eval(a,pt)*poly_eval(b,pt);
{
    ALREADY_PROVEN()
    switch(a) {
    case nil:
    case cons(x,xs):
        poly_mul_eval(xs,b,pt);
        assert poly_eval(poly_mul(a,b),pt)
            == poly_eval(poly_plus(poly_scale(x,b),
                                   cons(0,poly_mul(xs,b))),
                         pt);
        assert poly_eval(poly_mul(a,b),pt)
            == poly_eval(poly_scale(x,b),pt)
            +  poly_eval(cons(0,poly_mul(xs,b)),pt);
        assert poly_eval(poly_mul(a,b),pt)
            == x*poly_eval(b,pt)
            +  pt*poly_eval(poly_mul(xs,b),pt);
        assert poly_eval(poly_mul(a,b),pt)
            == x*poly_eval(b,pt)
            +  pt*(poly_eval(xs,pt)*poly_eval(b,pt));

        mul_assoc(pt,poly_eval(xs,pt),poly_eval(b,pt));

        assert poly_eval(poly_mul(a,b),pt)
            == (x + pt*poly_eval(xs,pt))*poly_eval(b,pt);

        mul_abstract_def(x + pt*poly_eval(xs,pt),poly_eval(b,pt));

        assert poly_eval(poly_mul(a,b),pt)
            == poly_eval(a,pt)*poly_eval(b,pt);
    }
}


lemma void poly_mul_length(list<int> p, list<int> q)
    requires length(p) >= 1 &*& length(q) >= 1;
    ensures  length(poly_mul(p,q)) == length(p) + length(q) - 1;
{
    ALREADY_PROVEN()
    switch(p) {
    case nil: assert false;
    case cons(x,xs):
        len_scale(x,q);
        if(length(xs) >= 1) {
            poly_mul_length(xs,q);
        }
    }
}


lemma_auto(poly_mul(p,nil))
void poly_mul_nil(list<int> p)
    requires true;
    ensures  poly_mul(p,nil) == nil;
{ LIST_INDUCTION(p,xs,poly_mul_nil(xs)) }


lemma_auto(poly_mul(p,q))
void poly_mul_nil_only(list<int> p, list<int> q)
    requires true;
    ensures  (poly_mul(p,q) == nil) == (p == nil || q == nil);
{ LIST_INDUCTION(p,xs,poly_mul_nil_only(xs,q)) }


lemma_auto(poly_mul(p,cons(s,nil)))
void poly_mul_const(list<int> p,int s)
    requires true;
    ensures  poly_mul(p,cons(s,nil)) == poly_scale(s,p);
{ LIST_INDUCTION(p,xs,poly_mul_const(xs,s)) }


lemma
void poly_plus_zero(list<int> p, list<int> q)
    requires !!poly_is_zero(p) &*& length(p) <= length(q);
    ensures  poly_plus(p,q) == q;
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys):
            poly_plus_zero(xs,ys);
        }
    }
}


lemma_auto(minimize(poly_plus(p,q)))
void poly_plus_zero_min(list<int> p, list<int> q)
    requires !!poly_is_zero(p);
    ensures  minimize(poly_plus(p,q)) == minimize(q);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys):
            poly_plus_zero_min(xs,ys);
        }
    }
}


lemma_auto(minimize(poly_plus(p,q)))
void min_poly_plus(list<int> p, list<int> q)
    requires true;
    ensures  minimize(poly_plus(p,q))
        ==   minimize(poly_plus(minimize(p),minimize(q)));
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys):
            min_poly_plus(xs,ys);
        }
    }
}


lemma_auto(minimize(poly_plus(p,q)))
void poly_plus_min(list<int> p, list<int> q)
    requires degree(p) != degree(q);
    ensures  minimize(poly_plus(p,q))
        ==   poly_plus(minimize(p),minimize(q));
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys):
            if(poly_is_zero(xs)) {
                assert minimize(xs) == nil;
                assert poly_plus(minimize(xs),minimize(ys))
                    == minimize(ys);
            } else if(poly_is_zero(ys)) {
                assert minimize(ys) == nil;
                assert poly_plus(minimize(xs),minimize(ys))
                    == minimize(xs);
            } else {
                poly_plus_min(xs,ys);
            }
        }
    }
}


lemma_auto(degree(p))
void poly_degree_zero(list<int> p)
    requires true;
    ensures  (degree(p) >= 0) == !poly_is_zero(p);
{ LIST_INDUCTION(p,xs,poly_degree_zero(xs)) }


lemma_auto(minimize(p))
void poly_min_nil(list<int> p)
    requires true;
    ensures  (minimize(p) == nil) == poly_is_zero(p);
{ LIST_INDUCTION(p,xs,poly_min_nil(xs)) }


lemma_auto(degree(poly_plus(p,q)))
void poly_plus_degree(list<int> p, list<int> q)
    requires degree(p) > degree(q);
    ensures  degree(poly_plus(p,q)) == degree(p);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys):
            if(degree(p) > 0) {
                poly_plus_degree(xs,ys);
            }
        }
    }
}


lemma
void poly_mul_zero(list<int> p, list<int> q)
    requires poly_is_zero(p) || poly_is_zero(q);
    ensures  !!poly_is_zero(poly_mul(p,q));
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        if(length(xs) < 1) { return; }
        if(length(q) < 1) { return; }
        len_scale(x,q);
        if(x != 0) {
            scale_nonzero(x,q);
        }
        poly_mul_length(xs,q);
        poly_plus_zero(poly_scale(x,q),
            poly_shift(poly_mul(xs,q)));

        poly_mul_zero(xs,q);
    }
}


lemma void poly_mul_commutes_inner(nat f, list<int> p, list<int> q)
    requires ion(f) >= length(p) + length(q);
    ensures  poly_mul(p,q) == poly_mul(q,p);
{
    ALREADY_PROVEN()
    switch(f) {
    case zero: TRIVIAL_LIST(p) TRIVIAL_LIST(q)
    case succ(f0):
        switch(p) {
        case nil:
        case cons(x,xs):
            switch(q) {
            case nil:
            case cons(y,ys):
                poly_mul_commutes_inner(f0,xs,q);
                poly_mul_commutes_inner(f0,xs,ys);
                poly_mul_commutes_inner(f0,p,ys);
                if(xs == nil || ys == nil) {
                    return;
                }
                assert poly_mul(p,q)
                    == poly_plus(poly_scale(x,q),
                            poly_shift(poly_mul(xs,q)));
                assert poly_mul(p,q)
                    == poly_plus(poly_scale(x,q),
                            cons(0,poly_mul(q,xs)));
                assert poly_mul(p,q)
                    == poly_plus(poly_scale(x,q),
                            cons(0,
                                poly_plus(poly_scale(y,xs),
                                    poly_shift(poly_mul(ys,xs)))));
                assert poly_mul(p,q)
                    == poly_plus(cons(x*y,poly_scale(x,ys)),
                            cons(0,
                                poly_plus(poly_scale(y,xs),
                                    poly_shift(poly_mul(ys,xs)))));
                assert poly_mul(p,q)
                    == cons(x*y,
                            poly_plus(poly_scale(x,ys),
                                poly_plus(poly_scale(y,xs),
                                    poly_shift(poly_mul(xs,ys)))));

                poly_plus_assoc(poly_scale(x,ys),poly_scale(y,xs),
                        poly_shift(poly_mul(xs,ys)));

                poly_plus_assoc(poly_scale(y,xs),poly_scale(x,ys),
                        poly_shift(poly_mul(xs,ys)));

                assert poly_mul(p,q)
                    == cons(x*y,
                            poly_plus(poly_scale(y,xs),
                                poly_plus(poly_scale(x,ys),
                                    poly_shift(poly_mul(xs,ys)))));
                assert poly_mul(p,q)
                    == cons(x*y,
                            poly_plus(poly_scale(y,xs),
                                poly_mul(p,ys)));
                assert poly_mul(p,q)
                    == cons(x*y,
                            poly_plus(poly_scale(y,xs),
                                poly_mul(ys,p)));
                assert poly_mul(p,q)
                    == cons(y*x,
                            poly_plus(poly_scale(y,xs),
                                poly_mul(ys,p)));
                assert poly_mul(p,q)
                    == poly_plus(cons(y*x, poly_scale(y,xs)),
                                cons(0,poly_mul(ys,p)));
                assert poly_mul(p,q)
                    == poly_plus(poly_scale(y,p),
                                poly_shift(poly_mul(ys,p)));

                assert poly_mul(q,p)
                    == poly_plus(poly_scale(y,p),
                            poly_shift(poly_mul(ys,p)));

            }
        }
    }
}


lemma void poly_mul_distr(list<int> p, list<int> q,
        list<int> r)
    requires true;
    ensures  poly_mul(poly_plus(p,q),r)
        ==   poly_plus(poly_mul(p,r),poly_mul(q,r));
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys):
            poly_mul_distr(xs,ys,r);

            assert poly_mul(poly_plus(p,q),r)
                == poly_plus(poly_scale(x+y,r),
                        poly_shift(poly_mul(poly_plus(xs,ys),r)));
            poly_linear(x,y,r);
            assert poly_mul(poly_plus(p,q),r)
                == poly_plus(poly_plus(poly_scale(x,r),poly_scale(y,r)),
                        poly_shift(poly_plus(poly_mul(xs,r),poly_mul(ys,r))));

            poly_plus_assoc(poly_scale(x,r),poly_scale(y,r),
                        poly_shift(poly_plus(poly_mul(xs,r),poly_mul(ys,r))));
            assert poly_mul(poly_plus(p,q),r)
                == poly_plus(poly_scale(x,r),poly_plus(poly_scale(y,r),
                        poly_shift(poly_plus(poly_mul(xs,r),poly_mul(ys,r)))));
            assert poly_mul(poly_plus(p,q),r)
                == poly_plus(poly_scale(x,r),poly_plus(poly_scale(y,r),
                        poly_shift(poly_plus(poly_mul(ys,r),poly_mul(xs,r)))));

            poly_plus_assoc(poly_scale(y,r),
                            poly_shift(poly_mul(ys,r)),
                        poly_shift(poly_mul(xs,r)));
            assert poly_mul(poly_plus(p,q),r)
                == poly_plus(poly_scale(x,r),
                    poly_plus(poly_plus(poly_scale(y,r),
                            poly_shift(poly_mul(ys,r))),
                        poly_shift(poly_mul(xs,r))));
            assert poly_mul(poly_plus(p,q),r)
                == poly_plus(poly_scale(x,r),
                    poly_plus(poly_shift(poly_mul(xs,r)),
                        poly_plus(poly_scale(y,r),
                            poly_shift(poly_mul(ys,r)))));

            poly_plus_assoc(poly_scale(x,r),
                                poly_shift(poly_mul(xs,r)),
                                poly_plus(poly_scale(y,r),
                            poly_shift(poly_mul(ys,r))));
            assert poly_mul(poly_plus(p,q),r)
                == poly_plus(poly_plus(poly_scale(x,r),
                                poly_shift(poly_mul(xs,r))),
                        poly_plus(poly_scale(y,r),
                            poly_shift(poly_mul(ys,r))));
            assert poly_mul(poly_plus(p,q),r)
                == poly_plus(poly_mul(p,r), poly_mul(q,r));

        }
    }
}


lemma //_auto(poly_mul(poly_scale(s,p),q))
void poly_mul_scale(int s,list<int> p, list<int> q)
    requires true;
    ensures  poly_mul(poly_scale(s,p),q) == poly_scale(s,poly_mul(p,q));
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        poly_mul_scale(s,xs,q);
        assert poly_scale(s,poly_mul(p,q))
            == poly_scale(s,poly_plus(poly_scale(x,q),
                    poly_shift(poly_mul(xs,q))));
        poly_linear2(s,poly_scale(x,q), poly_shift(poly_mul(xs,q)));
        assert poly_scale(s,poly_mul(p,q))
            == poly_plus(poly_scale(s,poly_scale(x,q)),
                    poly_scale(s,poly_shift(poly_mul(xs,q))));
        assert poly_scale(s,poly_mul(p,q))
            == poly_plus(poly_scale(s,poly_scale(x,q)),
                    poly_shift(poly_scale(s,poly_mul(xs,q))));
        poly_scale_mul(s,x,q);
        assert poly_scale(s,poly_mul(p,q))
            == poly_plus(poly_scale(s*x,q),
                    poly_shift(poly_mul(poly_scale(s,xs),q)));
        assert poly_scale(s,poly_mul(p,q))
            == poly_mul(poly_scale(s,p),q);
    }
}


lemma
void poly_shift_mul(list<int> p, list<int> q)
    requires true;
    ensures  poly_shift(poly_mul(p,q))
        ==   poly_mul(poly_shift(p),q);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys):
            assert poly_mul(p,q)
                == poly_plus(poly_scale(x,q),
                        poly_shift(poly_mul(xs,q)));
            assert poly_mul(poly_shift(p),q)
                == poly_plus(poly_scale(0,q),
                        poly_shift(poly_mul(p,q)));
            poly_mul_length(p,q);
            len_scale(0,q);
            poly_plus_zero(poly_scale(0,q),poly_shift(poly_mul(p,q)));
        }
    }
}


lemma void poly_mul_assoc(list<int> p, list<int> q,
        list<int> r)
    requires true;
    ensures  poly_mul(poly_mul(p,q),r) == poly_mul(p,poly_mul(q,r));
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        poly_mul_assoc(xs,q,r);
        assert poly_mul(p,poly_mul(q,r))
            == poly_plus(poly_scale(x,poly_mul(q,r)),
                    poly_shift(poly_mul(xs,poly_mul(q,r))));
        poly_mul_scale(x,q,r);
        assert poly_mul(p,poly_mul(q,r))
            == poly_plus(poly_mul(poly_scale(x,q),r),
                    poly_shift(poly_mul(poly_mul(xs,q),r)));
        poly_shift_mul(poly_mul(xs,q),r);
        assert poly_mul(p,poly_mul(q,r))
            == poly_plus(poly_mul(poly_scale(x,q),r),
                    poly_mul(poly_shift(poly_mul(xs,q)),r));
        poly_mul_distr(poly_scale(x,q),poly_shift(poly_mul(xs,q)),r);
        assert poly_mul(p,poly_mul(q,r))
            == poly_plus(poly_mul(poly_scale(x,q),r),
                    poly_shift(poly_mul(poly_mul(xs,q),r)));

    }
}


lemma_auto(poly_mul(p,q)) void poly_mul_commutes(list<int> p, list<int> q)
    requires true;
    ensures  poly_mul(p,q) == poly_mul(q,p);
{ poly_mul_commutes_inner(noi(length(p) + length(q)),p,q); }


lemma void poly_mul_zero_unique_inner(nat f,list<int> p, list<int> q)
    requires ion(f) >= length(p) + length(q)
        &*&  !!poly_is_zero(poly_mul(p,q)) &*& !poly_is_zero(p);
    ensures  !!poly_is_zero(q);
{
    ALREADY_PROVEN()
    switch(f) {
    case zero: assert false;
    case succ(f0):
        switch(p) {
        case nil:
        case cons(x,xs):
            switch(q) {
            case nil:
            case cons(y,ys):

                assert poly_mul(p,q)
                    == poly_plus(poly_scale(x,q),
                            poly_shift(poly_mul(xs,q)));

                if(x != 0) {
                    mul_commutes(x,y);
                    zero_mul_unique(y,x);
                    assert poly_mul(p,q)
                        == cons(0,poly_plus(poly_scale(x,ys),
                                poly_mul(q,xs)));
                    assert poly_mul(p,q)
                        == cons(0,poly_plus(poly_scale(x,ys),
                                poly_plus(poly_scale(y,xs),
                                    poly_shift(poly_mul(ys,xs)))));
                    assert poly_mul(p,q)
                        == cons(0,poly_plus(poly_scale(x,ys),
                                poly_plus(poly_scale(y,xs),
                                    poly_shift(poly_mul(xs,ys)))));
                    if(length(xs) >= 1 && length(ys) >= 1) {
                        len_scale(y,xs);
                        poly_mul_length(xs,ys);
                        poly_plus_zero(poly_scale(y,xs),
                                        poly_shift(poly_mul(xs,ys)));
                        assert poly_mul(p,q)
                            == cons(0,poly_plus(poly_scale(x,ys),
                                    poly_shift(poly_mul(xs,ys))));
                        assert poly_mul(p,q)
                            == cons(0,poly_mul(p,ys));
                        poly_mul_zero_unique_inner(f0,p,ys);
                    } else {
                        assert ys == nil || xs == nil;
                        if(ys == nil) {
                            assert q == cons(0,nil);
                        } else {
                            assert poly_mul(p,q) == poly_scale(x,q);
                            scale_nonzero(x,q);
                        }
                    }
                } else {
                    len_scale(x,q);
                    poly_mul_length(xs,q);
                    poly_plus_zero(poly_scale(x,q),
                            poly_shift(poly_mul(xs,q)));
                    poly_mul_zero_unique_inner(f0,xs,q);
                }

            }
        }
    }
}


lemma void poly_mul_zero_unique(list<int> p, list<int> q)
    requires !!poly_is_zero(poly_mul(p,q)) &*& !poly_is_zero(p);
    ensures  !!poly_is_zero(q);
{ poly_mul_zero_unique_inner(noi(length(p) + length(q)),p,q); }


lemma_auto(degree(poly_mul(p,q)))
void degree_poly_mul_bound(list<int> p, list<int> q)
    requires degree(p) >= 0;
    ensures  degree(poly_mul(p,q)) >= degree(q);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        if(degree(xs) >= 0) {
            degree_poly_mul_bound(xs,q);
        } else {
            assert minimize(xs) == nil;
        }
        assert poly_mul(p,q)
            == poly_plus(poly_scale(x,q),
                    poly_shift(poly_mul(xs,q)));

        if(x != 0) {
            len_scale(x,minimize(q));
            assert degree(poly_scale(x,q)) == degree(q);
        }
        assert degree(poly_scale(x,q)) <= degree(q);
        if(degree(xs) >= 0) {
            assert minimize(poly_mul(p,q))
                == poly_plus(minimize(poly_scale(x,q)),
                        poly_shift(minimize(poly_mul(xs,q))));
            assert degree(poly_mul(p,q)) ==
                degree(poly_shift(poly_mul(xs,q)));
        } else if(x == 0) {
            assert false;
        } else {
            assert !!poly_is_zero(xs);
            poly_mul_zero(xs,q);
            assert minimize(poly_mul(xs,q)) == nil;
            assert minimize(poly_mul(p,q))
                == poly_plus(minimize(poly_scale(x,q)),
                        poly_shift(minimize(poly_mul(xs,q))));
            assert minimize(poly_mul(p,q))
                == minimize(poly_scale(x,q));
            assert degree(poly_mul(p,q)) == degree(q);
        }
    }
}


lemma_auto(minimize(poly_mul(p,q)))
void poly_mul_minimal(list<int> p, list<int> q)
    requires true;
    ensures  poly_mul(minimize(p),minimize(q))
        ==   minimize(poly_mul(p,q));
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        poly_mul_minimal(xs,q);
        if(x == 0) {
            poly_shift_mul(xs,q);
            poly_shift_mul(minimize(xs),minimize(q));
            if(!poly_is_zero(xs)) {
                assert poly_mul(p,q)
                    == poly_shift(poly_mul(xs,q));
                assert minimize(p)
                    == poly_shift(minimize(xs));
            }
        }
        if(poly_is_zero(xs)) {
            poly_mul_zero(xs,q);

            //assert minimize(poly_mul(p,q))
            //    == minimize(poly_plus(poly_scale(x,
            assert minimize(poly_mul(p,q))
                == minimize(poly_scale(x,q));

            assert !!poly_is_zero(poly_mul(xs,q));
            assert minimize(xs) == nil;

            //assert poly_is_zero

            if(x != 0) {
                assert minimize(p) == cons(x,nil);
            }
        }

        if(x != 0 && !poly_is_zero(xs)) {
            assert poly_mul(minimize(p),minimize(q))
                == poly_plus(poly_scale(x,minimize(q)),
                        poly_shift(poly_mul(minimize(xs),minimize(q))));
            assert poly_mul(minimize(p),minimize(q))
                == poly_plus(minimize(poly_scale(x,q)),
                        poly_shift(minimize(poly_mul(xs,q))));
            assert poly_mul(minimize(p),minimize(q))
                == poly_plus(minimize(poly_scale(x,q)),
                        minimize(poly_shift(poly_mul(xs,q))));

            assert minimize(poly_scale(x,q)) ==
                poly_scale(x,minimize(q));
            len_scale(x,minimize(q));
            assert degree(poly_scale(x,q)) == degree(q);
            assert degree(poly_mul(xs,q)) >= degree(q);

            assert poly_mul(minimize(p),minimize(q))
                == minimize(poly_plus(poly_scale(x,q),
                        poly_shift(poly_mul(xs,q))));
        }
    }
}


lemma void poly_mul_degree(list<int> p, list<int> q)
    requires degree(p) >= 0 &*& degree(q) >= 0;
    ensures  degree(poly_mul(p,q)) == degree(p) + degree(q);
{ poly_mul_length(minimize(p),minimize(q)); }


lemma_auto(is_monic(p))
void leading_coeff_monic(list<int> p)
    requires true;
    ensures  (leading_coeff(p) == 1) == is_monic(p);
{ LIST_INDUCTION(p,xs,leading_coeff_monic(xs)) }


lemma_auto(leading_coeff(p))
void leading_coeff_zero(list<int> p)
    requires true;
    ensures  (leading_coeff(p) == 0) == poly_is_zero(p);
{ LIST_INDUCTION(p,xs,leading_coeff_zero(xs)) }


lemma_auto(leading_coeff(poly_scale(s,p)))
void leading_coeff_scale(int s, list<int> p)
    requires true;
    ensures  leading_coeff(poly_scale(s,p)) == s*leading_coeff(p);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil:
    case cons(x,xs):
        if(s != 0) scale_nonzero(s,xs);
        leading_coeff_scale(s,xs);
    }
}


lemma void leading_coeff_cancel(list<int> p, list<int> q)
    requires degree(p) == degree(q) &*& degree(p) >= 0
        &*&  leading_coeff(p)+leading_coeff(q) == 0;
    ensures  degree(poly_plus(p,q)) < degree(p);
{
    ALREADY_PROVEN()
    switch(p) {
    case nil: assert false;
    case cons(x,xs):
        switch(q) {
        case nil:
        case cons(y,ys):
            if(degree(xs) >= 0) leading_coeff_cancel(xs,ys);
        }
    }
}


lemma_auto(multishift(n,p))
void multishift_nil(nat n, list<int> p)
    requires true;
    ensures  (multishift(n,p) == nil) == (p == nil);
{ NAT_INDUCTION(n,n0,multishift_nil(n0,p)) }


lemma_auto(poly_is_zero(multishift(n,p)))
void multishift_zero(nat n, list<int> p)
    requires true;
    ensures  poly_is_zero(multishift(n,p)) == poly_is_zero(p);
{ NAT_INDUCTION(n,n0,multishift_zero(n0,p)) }


lemma_auto(degree(multishift(n,p)))
void multishift_deg(nat n, list<int> p)
    requires degree(p) >= 0;
    ensures  degree(multishift(n,p)) == ion(n)+degree(p);
{ NAT_INDUCTION(n,n0,multishift_deg(n0,p)) }


lemma_auto(leading_coeff(multishift(n,p)))
void multishift_coeff(nat n, list<int> p)
    requires true;
    ensures  leading_coeff(multishift(n,p)) == leading_coeff(p);
{ NAT_INDUCTION(n,n0,multishift_coeff(n0,p)) }


lemma void multishift_mul(nat n, list<int> p)
    requires true;
    ensures  multishift(n,p) == poly_mul(multishift(n,cons(1,nil)),p);
{
    ALREADY_PROVEN()
    switch(n) {
    case zero:
    case succ(n0):
        multishift_mul(n0,p);

        len_scale(0,p);
        if(length(p) >= 1) {
            poly_mul_length(multishift(n0,cons(1,nil)),p);
        }
        poly_plus_zero(poly_scale(0,p),
                poly_shift(poly_mul(multishift(n0,cons(1,nil)),p)));
    }
}


lemma pair<list<int>, list<int> > poly_div(list<int> a, list<int> b)
    requires !!is_monic(b);
    ensures  switch(result) {
    case pair(q,r):
        return  degree(r) < degree(b)
            &*& minimize(a) == minimize(poly_plus(poly_mul(q,b),r));
    };
{
    ALREADY_PROVEN()
    list<int> q = nil;
    list<int> r = a;
    list<int> cursor = b;
    nat cursor_mul = zero;

    while(degree(cursor) < degree(r))
        invariant cursor == multishift(cursor_mul,b)
            ;
        decreases max_of(degree(r)-degree(cursor),0);
    {
        cursor     = poly_shift(cursor);
        cursor_mul = succ(cursor_mul);
    }

    while(degree(r) >= degree(b))
        invariant minimize(a) == minimize(poly_plus(poly_mul(q,b),r))
            &*&   cursor == multishift(cursor_mul,b)
            &*&   degree(cursor) >= degree(r)
            ;
        decreases ion(cursor_mul) + degree(r);
    {
        if(degree(cursor) == degree(r)) {
            assert leading_coeff(cursor) == 1;
            list<int> r_diff = poly_scale(-leading_coeff(r),cursor);
            list<int> q_diff = poly_scale(leading_coeff(r),
                multishift(cursor_mul,cons(1,nil)));
            list<int> delta = poly_plus(poly_mul(q_diff,b),r_diff);

            if(!poly_is_zero(delta)) {
                multishift_mul(cursor_mul,b);
                poly_mul_scale(leading_coeff(r),
                        multishift(cursor_mul,cons(1,nil)),b);
                assert delta
                    == poly_plus(
                        poly_scale(leading_coeff(r),
                            multishift(cursor_mul,b)),
                        poly_scale(-leading_coeff(r),
                            multishift(cursor_mul,b)));
                poly_linear(leading_coeff(r),-leading_coeff(r),
                        cursor);
                assert false;
            }

            list<int> new_q = poly_plus(q,q_diff);
            list<int> new_r = poly_plus(r,r_diff);

            if(degree(new_r) >= degree(r)) {
                assert leading_coeff(r) != 0;
                len_scale(-leading_coeff(r),minimize(cursor));

                assert degree(poly_scale(-leading_coeff(r),cursor))
                    == degree(cursor);
                leading_coeff_cancel(r,r_diff);
                assert false;
            }

            if(minimize(poly_plus(poly_mul(new_q,b), new_r)) !=
                    minimize(a)) {
                poly_mul_distr(q,q_diff,b);
                assert poly_plus(poly_mul(new_q,b), new_r)
                    == poly_plus(
                        poly_plus(poly_mul(q,b),poly_mul(q_diff,b)),
                        poly_plus(r,r_diff));

                poly_plus_assoc(poly_mul(q,b),
                        poly_mul(q_diff,b),
                                poly_plus(r,r_diff));
                assert poly_plus(poly_mul(new_q,b), new_r)
                    == poly_plus(poly_mul(q,b),
                            poly_plus(poly_mul(q_diff,b),
                                poly_plus(r,r_diff)));
                assert poly_plus(poly_mul(new_q,b), new_r)
                    == poly_plus(poly_mul(q,b),
                            poly_plus(poly_mul(q_diff,b),
                                poly_plus(r,r_diff)));

                poly_plus_assoc(poly_mul(q_diff,b), r_diff,r);
                assert false;
            }
            q = new_q;
            r = new_r;
        }

        if(cursor_mul != zero) {
            cursor     = tail(cursor);
            TRIVIAL_NAT(cursor_mul)
            cursor_mul = nat_predecessor(cursor_mul);
        }
    }

    return pair(q,r);
}


lemma list<int> poly_root(list<int> a, int pt)
    requires poly_eval(a,pt) == 0;
    ensures  minimize(poly_mul(result,cons(-pt,cons(1,nil))))
        ==   minimize(a);
{
    ALREADY_PROVEN()
    list<int> factor = cons(-pt,cons(1,nil));
    switch(poly_div(a,factor)) {
    case pair(q,r):
        assert minimize(a)
            == minimize(poly_plus(poly_mul(q,factor),r));
        assert degree(r) < degree(factor);
        assert degree(r) < 1;
        if(degree(r) >= 0) {
            assert degree(r) == 0;
            switch(minimize(r)) {
            case nil: assert false;
            case cons(v,vs):
                switch(vs) {
                case nil:
                    assert poly_eval(factor,pt) == 0;
                    assert poly_eval(r,pt)
                        == poly_eval(minimize(r),pt);
                    assert poly_eval(r,pt) == v;
                    assert v != 0;
                    assert poly_eval(poly_mul(q,factor),pt)
                        == poly_eval(q,pt)*poly_eval(factor,pt);
                    assert poly_eval(poly_mul(q,factor),pt) == 0;
                    assert poly_eval(poly_plus(poly_mul(q,factor),r),pt)
                        == poly_eval(poly_mul(q,factor),pt)
                            + poly_eval(r,pt);
                    assert poly_eval(a,pt) == poly_eval(minimize(a),pt);
                    assert poly_eval(a,pt) == v;
                    assert false;
                case cons(vs0,vs1): assert false;
                }
            }
        }
        assert degree(r) == -1;
        assert minimize(a)
            == poly_plus(minimize(poly_mul(q,factor)),minimize(r));
        assert minimize(a)
            == minimize(poly_mul(q,factor));
        return q;
    }
}


lemma void poly_max_roots(list<int> p, list<int> pts)
    requires degree(p) >= 0 &*& !!distinct(pts)
        &*&  !!forall(pts,(is_root)(p));
    ensures  length(pts) <= degree(p);
{
    ALREADY_PROVEN()
    switch(pts) {
    case nil:
    case cons(v,vs):
        list<int> q = poly_root(p,v);
        list<int> factor = {-v,1};
        assert minimize(p) == minimize(poly_mul(q,factor));
        if(degree(q) < 0) { assert false; }
        poly_mul_degree(q,factor);
        assert degree(q) == degree(p)-1;
        if(!forall(vs,(is_root)(q))) {
            int cx = not_forall(vs,(is_root)(q));
            forall_elim(vs,(is_root)(p),cx);
            assert cx != v;
            assert poly_eval(factor,cx) != 0;
            assert poly_eval(p,cx) ==
                poly_eval(minimize(poly_mul(q,factor)),cx);
            assert poly_eval(p,cx) ==
                poly_eval(poly_mul(q,factor),cx);
            assert poly_eval(q,cx)*poly_eval(factor,cx) == 0;
            zero_mul_unique(poly_eval(q,cx),poly_eval(factor,cx));

            assert false;
        }

        poly_max_roots(q,vs);
    }
}


lemma int poly_nonzero_pt(list<int> p)
    requires !poly_is_zero(p);
    ensures  poly_eval(p,result) != 0;
{
    int ret = 0;
    list<int> roots = nil;
    while(poly_eval(p,ret) == 0)
        invariant !!distinct(roots)
            &*&   !!forall(roots,(is_root)(p))
            &*&   !!forall(roots,(flip)(ge_than,ret-1))
            &*&   !mem(ret,roots)
            &*&   length(roots) <= degree(p)
            ;
        decreases degree(p)-length(roots);
    {
        list<int> new_roots = cons(ret,roots);
        poly_max_roots(p,new_roots);
        int new_ret = ret+1;
        if(!forall(new_roots,(flip)(ge_than,new_ret-1))) {
            int cx = not_forall(new_roots,(flip)(ge_than,new_ret-1));
            if(cx != ret) {
                forall_elim(roots,(flip)(ge_than,ret-1),cx);
            }
            assert false;
        }
        if(mem(new_ret,new_roots)) {
            forall_elim(new_roots,(flip)(ge_than,new_ret-1),new_ret);
            assert false;
        }
        ret = new_ret;
        roots = new_roots;
    }
    return ret;
}

lemma void karatsuba_step(
        list<int> x0, list<int> x1, list<int> y0, list<int> y1,
        int B)
    requires B > 0 &*& length(x0) == length(y0)
        &*&  let(poly_eval(x0,B)*poly_eval(y0,B),?z0)
        &*&  let((poly_eval(x0,B) + poly_eval(x1,B))
                *(poly_eval(y0,B) + poly_eval(y1,B)),
                ?z1)
        &*&  let(poly_eval(x1,B)*poly_eval(y1,B),?z2)
        ;
    ensures  poly_eval(append(x0,x1),B)*poly_eval(append(y0,y1),B)
        ==   z0
        +    (z1 - z0 - z2)*pow_nat(B,noi(length(x0)))
        +    z2*pow_nat(B,noi(2*length(x0)));
{
    pow_plus(B,noi(length(x0)),length(x0));

    note_eq( poly_eval(append(x0,x1),B)*poly_eval(append(y0,y1),B)
        ,  (poly_eval(x0,B) + pow_nat(B,noi(length(x0)))*poly_eval(x1,B))
        *  (poly_eval(y0,B) + pow_nat(B,noi(length(y0)))*poly_eval(y1,B)));

    mul_3var(poly_eval(x0,B),pow_nat(B,noi(length(y0))),poly_eval(y1,B));
    mul_3var(poly_eval(y0,B),pow_nat(B,noi(length(x0))),poly_eval(x1,B));

    note_eq( poly_eval(append(x0,x1),B)*poly_eval(append(y0,y1),B)
        ,  poly_eval(x0,B)*poly_eval(y0,B)
        +  (poly_eval(x0,B)*poly_eval(y1,B)
            + poly_eval(x1,B)*poly_eval(y0,B))
           *pow_nat(B,noi(length(x0)))
        +  (poly_eval(x1,B)*pow_nat(B,noi(length(x0))))
           *(poly_eval(y1,B)*pow_nat(B,noi(length(y0)))));

    mul_3var(poly_eval(x1,B)*pow_nat(B,noi(length(x0))),
            poly_eval(y1,B),pow_nat(B,noi(length(y0))));


    mul_3var(poly_eval(x1,B),pow_nat(B,noi(length(x0))),
            poly_eval(y1,B));

    mul_3var(poly_eval(x1,B)*poly_eval(y1,B),
            pow_nat(B,noi(length(x0))),pow_nat(B,noi(length(y0))));

}

@*/

