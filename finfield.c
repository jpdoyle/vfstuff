/*@ #include "finfield.gh" @*/

#if 1
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif

/*@

lemma void Zp_plus(int p, int a, int b)
    requires p > 0;
    ensures  euclid_mod(a+b,p)
        ==   euclid_mod(euclid_mod(a,p)+euclid_mod(b,p),p);
{
ALREADY_PROVEN()
    euclid_mod_correct(a+b,p);
    assert [_] euclid_div_sol(a+b,p,?ab_q,?ab_r);

    euclid_mod_correct(a,p);
    assert [_] euclid_div_sol(a,p,?a_q,?a_r);
    euclid_mod_correct(b,p);
    assert [_] euclid_div_sol(b,p,?b_q,?b_r);

    euclid_mod_correct(a_r+b_r,p);
    assert [_] euclid_div_sol(a_r+b_r,p,?tot_q,?tot_r);

    if(tot_r != ab_r) {
        euclid_div_unique(a+b,p,ab_q,ab_r,tot_q + a_q + b_q, tot_r);
        assert false;
    }

}

lemma void Zp_diff_zero(int p, int a, int b)
    requires p > 0;
    ensures  (euclid_mod(a-b,p) == 0)
        ==   (euclid_mod(a,p) == euclid_mod(b,p));
{
ALREADY_PROVEN()
    euclid_mod_correct(a-b,p);
    assert [_] euclid_div_sol(a-b,p,?ab_q,?ab_r);

    euclid_mod_correct(a,p);
    assert [_] euclid_div_sol(a,p,?a_q,?a_r);
    euclid_mod_correct(b,p);
    assert [_] euclid_div_sol(b,p,?b_q,?b_r);

    if(ab_r == 0 && a_r != b_r) {
        assert a-b == p*ab_q;
        assert (p*a_q + a_r)-(p*b_q + b_r) == p*ab_q;
        assert a_r - b_r == -p*a_q + p*b_q + p*ab_q;
        assert a_r >= 0;
        assert b_r < p;
        assert a_r - b_r > -p;
        assert a_r - b_r < p;

        division_zero_unique(p, a_q - ab_q - b_q, a_r - b_r);
        assert false;
    } else if(ab_r != 0 && a_r == b_r) {
        euclid_div_unique(a-b, p, ab_q, ab_r, a_q-b_q, 0);
        assert false;
    }
}

lemma void Zp_minus(int p, int a, int b)
    requires p > 0;
    ensures  euclid_mod(a-b,p)
        ==   euclid_mod(euclid_mod(a,p)-euclid_mod(b,p),p);
{
ALREADY_PROVEN()
    euclid_mod_correct(a-b,p);
    assert [_] euclid_div_sol(a-b,p,?ab_q,?ab_r);

    euclid_mod_correct(a,p);
    assert [_] euclid_div_sol(a,p,?a_q,?a_r);
    euclid_mod_correct(b,p);
    assert [_] euclid_div_sol(b,p,?b_q,?b_r);

    euclid_mod_correct(a_r-b_r,p);
    assert [_] euclid_div_sol(a_r-b_r,p,?tot_q,?tot_r);

    if(tot_r != ab_r) {
        euclid_div_unique(a-b,p,ab_q,ab_r,tot_q + a_q - b_q, tot_r);
        assert false;
    }
}

lemma void Zp_times(int p, int a, int b)
    requires p > 0;
    ensures  euclid_mod(a*b,p)
        ==   euclid_mod(euclid_mod(a,p)*euclid_mod(b,p),p);
{
ALREADY_PROVEN()
    euclid_mod_correct(a*b,p);
    assert [_] euclid_div_sol(a*b,p,?ab_q,?ab_r);

    euclid_mod_correct(a,p);
    assert [_] euclid_div_sol(a,p,?a_q,?a_r);
    euclid_mod_correct(b,p);
    assert [_] euclid_div_sol(b,p,?b_q,?b_r);

    euclid_mod_correct(a_r*b_r,p);
    assert [_] euclid_div_sol(a_r*b_r,p,?tot_q,?tot_r);

    if(tot_r != ab_r) {
        assert p*tot_q + tot_r == a_r*b_r;
        note_eq( p*tot_q + tot_r , (a-p*a_q)*(b - p*b_q));
        assert p*tot_q + tot_r
            == a*b - (p*a_q)*b - a*(p*b_q) + (p*a_q)*(p*b_q);
        mul_3var(p,a_q,b);
        mul_3var(p,b_q,a);
        mul_3var(p,a_q,p*b_q);
        euclid_div_unique(a*b,p,ab_q,ab_r,
            tot_q + a_q*b + a*b_q - a_q*(p*b_q), tot_r);
        assert false;
    }

}

lemma void Zp_prod_zero(int p, int a, int b)
    requires !!is_prime(p);
    ensures  (euclid_mod(a*b,p) == 0)
        ==   (euclid_mod(a,p) == 0 || euclid_mod(b,p) == 0);
{
ALREADY_PROVEN()
    if((euclid_mod(a*b,p) != 0)
            && (euclid_mod(a,p) == 0 ||
                euclid_mod(b,p) == 0)) {
        Zp_times(p,a,b);
        assert false;
    } else if((euclid_mod(a*b,p) == 0)
            && euclid_mod(a,p) != 0
            && euclid_mod(b,p) != 0) {

        euclid_mod_correct(a*b,p);
        assert [_] euclid_div_sol(a*b,p,?ab_q,?ab_r);

        euclid_mod_correct(a,p);
        assert [_] euclid_div_sol(a,p,?a_q,?a_r);
        euclid_mod_correct(b,p);
        assert [_] euclid_div_sol(b,p,?b_q,?b_r);

        assert a*b == p*ab_q;
        assert a == p*a_q + a_r;
        assert b == p*b_q + b_r;
        note_eq( (p*a_q + a_r)*(p*b_q + b_r) ,  p*ab_q);
        assert (p*a_q)*(p*b_q) + a_r*(p*b_q) + (p*a_q)*b_r + a_r*b_r == p*ab_q;
        mul_3var(p,a_q,p*b_q);
        mul_3var(a_r,p,b_q);
        mul_3var(p,a_q,b_r);

        div_rem(a*b,p);
        division_zero_unique(p, (a*b)/p - ab_q, (a*b)%p);
        mod_abs(a*b,p);
        mul_abs_commute(a,b);
        prime_divides_product(p,abs(a),abs(b));

        mod_abs(a,p);
        mod_abs(b,p);

        assert false;
    }
}

lemma void Zp_x_times_zero(int p, int a, int b)
    requires p > 0 &*& euclid_mod(a,p) == 0;
    ensures  euclid_mod(b*a,p) == 0;
{
    Zp_times(p,b,a);
}

lemma void Zp_pow(int p, int a, nat n)
    requires p > 0;
    ensures  euclid_mod(pow_nat(a,n),p)
        ==   euclid_mod(pow_nat(euclid_mod(a,p),n),p);
{
ALREADY_PROVEN()
    switch(n) {
        case zero:
        case succ(n0):
            Zp_pow(p,a,n0);
            assert euclid_mod(pow_nat(a,n),p)
                == euclid_mod(a*pow_nat(a,n0),p);
            Zp_times(p, a,pow_nat(a,n0));
            assert euclid_mod(pow_nat(a,n),p)
                == euclid_mod(
                    euclid_mod(a,p)*euclid_mod(pow_nat(a,n0),p),
                    p);
            assert euclid_mod(pow_nat(a,n),p)
                == euclid_mod(
                    euclid_mod(a,p)*euclid_mod(pow_nat(euclid_mod(a,p),n0),p),
                    p);
            Zp_times(p, euclid_mod(a,p),pow_nat(euclid_mod(a,p),n0));
            assert euclid_mod(pow_nat(a,n),p)
                == euclid_mod(
                    euclid_mod(a,p)*pow_nat(euclid_mod(a,p),n0),
                    p);
            assert euclid_mod(pow_nat(a,n),p)
                == euclid_mod(pow_nat(euclid_mod(a,p),n), p);
    }
}

lemma int Rp_recip(int p, int x)
    requires p > 1 &*& x != 0 &*& gcd(p,abs(x)) == 1;
    ensures  1 <= result &*& result < p
        &*&  euclid_mod(x*result,p) == 1;
{
ALREADY_PROVEN()
    euclid_mod_correct(x,p);
    assert [_] euclid_div_sol(x,p,?q,?r);
    if(r == 0) {
        div_rem(x,p);

        if(x%p != 0) {
            assert x == p*q;
            assert x == p*(x/p) + x%p;
            assert p*q == p*(x/p) + x%p;
            assert p*(q - x/p) == x%p;
            assert abs(p*(q - x/p)) == abs(x%p);
            mul_abs_commute(p,q-x/p);
            assert abs(p)*abs(q - x/p) == abs(x%p);
            if(q - x/p == 0) { assert false; }
            my_mul_mono_r(abs(p),1,abs(q-x/p));


            assert false;
        }

        assert x%p == 0;
        mod_abs(x,p);

        gcd_is_max_divisor(abs(x),p,p);
        assert false;
    }

    if(gcd(r,p) != 1) {
        int res = gcd(r,p);
        div_rem(r,res);
        div_rem(p,res);
        assert x == p*q + r;
        assert r == res*(r/res);
        assert p == res*(p/res);
        assert x == (res*(p/res))*q + res*(r/res);
        mul_3var(res,p/res,q);
        division_unique(x,res,(p/res)*q + r/res,0);
        mod_abs(x,res);
        gcd_is_max_divisor(abs(x),p,res);
        assert false;
    }

    switch(gcd_min_lincomb_sol(r,p)) {
    case pair(a,b):
        assert a*r + b*p == 1;
        assert euclid_mod(a*r + b*p,p) == euclid_mod(1,p);
        Zp_plus(p,a*r,b*p);
        assert euclid_mod(euclid_mod(a*r,p) + euclid_mod(b*p,p),p)
            == 1;
        if(euclid_mod(b*p,p) != 0) {
            euclid_mod_correct(b*p,p);
            assert [_] euclid_div_sol(b*p,p,?q1,?r1);
            euclid_div_unique(b*p,p,q1,r1,b,0);
            assert false;
        }
        assert euclid_mod(euclid_mod(a*r,p),p)
            == 1;
        assert euclid_mod(a*r,p) == 1;
        Zp_times(p,a,r);
        assert euclid_mod(euclid_mod(a,p)*euclid_mod(r,p),p) == 1;
        assert euclid_mod(euclid_mod(euclid_mod(a,p),p)*euclid_mod(x,p),p) == 1;
        Zp_times(p,euclid_mod(a,p),x);
        assert euclid_mod(euclid_mod(a,p)*x,p) == 1;

        euclid_mod_correct(a,p);
        if(euclid_mod(a,p) == 0) {
            assert false;
        }

        return euclid_mod(a,p);
    }
}

lemma void Zp_recip_unique(int p, int x, int r1, int r2)
    requires p > 0
        &*&  euclid_mod(x*r1,p) == 1
        &*&  euclid_mod(x*r2,p) == 1;
    ensures  euclid_mod(r1,p) == euclid_mod(r2,p);
{
ALREADY_PROVEN()
    assert (euclid_mod(x*r1,p) - euclid_mod(x*r2,p)) == 0;
    assert euclid_mod(euclid_mod(x*r1,p) - euclid_mod(x*r2,p),p) == 0;
    Zp_minus(p,x*r1,x*r2);
    assert euclid_mod(x*r1 - x*r2,p) == 0;
    assert euclid_mod(x*(r1 - r2),p) == 0;
    Zp_times(p,r1,x*(r1-r2));
    assert euclid_mod(r1*(x*(r1 - r2)),p) == 0;

    mul_3var(r1,x,r1-r2);
    assert euclid_mod((r1*x)*(r1 - r2),p) == 0;
    Zp_times(p,r1*x,r1-r2);
    assert euclid_mod(1*euclid_mod(r1 - r2,p),p) == 0;
    assert euclid_mod(r1 - r2,p) == 0;
    Zp_diff_zero(p,r1,r2);
}

lemma void fermat_little_lemma1(int p, int x, int i, int j)
    requires p > 1 &*& x != 0 &*& gcd(abs(x),p) == 1
        &*&  0 <= i &*& i < j &*& j < p &*& gcd(j-i,p) == 1;
    ensures  euclid_mod(i*x,p) != euclid_mod(j*x,p);
{
ALREADY_PROVEN()
    if(euclid_mod(i*x,p) == euclid_mod(j*x,p)) {
        Zp_diff_zero(p,j*x,i*x);
        assert euclid_mod((j-i)*x,p) == 0;
        euclid_mod_correct((j-i)*x,p);
        assert [_] euclid_div_sol((j-i)*x,p,?q,0);
        assert (j-i)*x == p*q;
        assert (j-i)*x == p*q;
        assert abs((j-i)*x) == abs(p*q);
        mul_abs_commute(j-i,x);
        mul_abs_commute(p,q);
        assert (j-i)*abs(x) == p*abs(q);
        division_unique((j-i)*abs(x),p,abs(q),0);
        division_unique(p,p,1,0);
        int f = findSomeFactor(p);
        div_rem(p,f);
        assert (j-i)*abs(x) == (f*(p/f))*abs(q);
        mul_3var(f,p/f,abs(q));
        division_unique((j-i)*abs(x),f,(p/f)*abs(q),0);
        prime_divides_product(f,j-i,abs(x));

        if((j-i)%f == 0) {
            gcd_is_max_divisor(p,j-i,f);
        } else  {
            gcd_is_max_divisor(p,abs(x),f);
        }

        assert false;
    }
}

fixpoint list<pair<int,int> > multiples_mod_p_inner(int p, int x, nat f) {
    switch(f) {
        case zero: return nil;
        case succ(f0):
            return cons(pair(int_of_nat(f),euclid_mod(int_of_nat(f)*x,p)),
                multiples_mod_p_inner(p,x,f0));
    }
}

fixpoint list<pair<int,int> > multiples_mod_p(nat p_minus_1, int x) {
    return multiples_mod_p_inner(int_of_nat(succ(p_minus_1)), x,
            p_minus_1);
}

lemma void remove_from_pair_list<s,t>(s x, t y, list<pair<s,t> > l)
    requires !!mem(y,map(snd,l)) &*& !!mem(y,remove(y,map(snd,l)));
    ensures  !!mem(y,map(snd,remove(pair(x,y),l)));
{
ALREADY_PROVEN()
    switch(l) {
    case nil: assert false;
    case cons(v,vs):
        switch(v) {
        case pair(a,b):
            if(b != y) {
                remove_from_pair_list(x,y,vs);
            }
        }
    }
}

lemma_auto(length(multiples_mod_p(p_minus_1,x)))
void multiples_len(nat p_minus_1, int x)
    requires true;
    ensures  length(multiples_mod_p(p_minus_1,x))
        ==   int_of_nat(p_minus_1);
{
ALREADY_PROVEN()
    int p = int_of_nat(succ(p_minus_1));

    for(nat i = zero; i != p_minus_1; i = succ(i))
        invariant int_of_nat(i) <= int_of_nat(p_minus_1)
            &*&   length(multiples_mod_p_inner(p,x,i))
               == int_of_nat(i);
        decreases int_of_nat(p_minus_1)-int_of_nat(i);
    {
        assert int_of_nat(i) <= int_of_nat(p_minus_1);
        if(int_of_nat(i) >= int_of_nat(p_minus_1)) {
            assert int_of_nat(i) == int_of_nat(p_minus_1);
            nat_of_int_of_nat(i);
            assert false;
        }
        assert int_of_nat(i) < int_of_nat(p_minus_1);
        assert int_of_nat(succ(i)) == 1+int_of_nat(i);
    }

}

lemma void multiples_indices(nat p_minus_1, int x, int i, int v)
    requires !!mem(pair(i,v),multiples_mod_p(p_minus_1,x));
    ensures  1 <= i &*& i <= int_of_nat(p_minus_1);
{
ALREADY_PROVEN()
    int p = int_of_nat(succ(p_minus_1));
    nat f = p_minus_1;
    list<pair<int,int> > l = multiples_mod_p(p_minus_1,x);

    if(1 > i || i > p-1) {
        while(length(l) > 0)
            invariant !!mem(pair(i,v),l)
                &*&   l ==
                    multiples_mod_p_inner(p,x,f)
                &*&   int_of_nat(f) >= 1
                &*&   int_of_nat(f) <= p-1
                ;
            decreases length(l);
        {
            switch(f) {
            case zero: assert false;
            case succ(f0):
                switch(l) {
                case nil: assert false;
                case cons(l_x,l_xs):
                    l = l_xs;
                    f = f0;
                }
            }
        }
        assert false;
    }
}

lemma void multiples_bounded(nat p_minus_1, int x)
    requires let(int_of_nat(succ(p_minus_1)),?p)
        &*&  !!is_prime(p)
        &*&  euclid_mod(x,p) != 0;
    ensures  !!forall(map(snd,multiples_mod_p(p_minus_1,x)),
                (bounded)(1,int_of_nat(p_minus_1)));
{
ALREADY_PROVEN()
    for(nat i = zero; i != p_minus_1; i = succ(i))
        invariant int_of_nat(i) <= int_of_nat(p_minus_1)
            &*&   !!forall(map(snd,multiples_mod_p_inner(p,x,i)),
                (bounded)(1,p-1));
        decreases int_of_nat(p_minus_1)-int_of_nat(i);
    {
        assert int_of_nat(i) <= int_of_nat(p_minus_1);
        if(int_of_nat(i) >= int_of_nat(p_minus_1)) {
            assert int_of_nat(i) == int_of_nat(p_minus_1);
            nat_of_int_of_nat(i);
            assert false;
        }
        assert int_of_nat(i) < int_of_nat(p_minus_1);
        assert int_of_nat(succ(i)) == 1+int_of_nat(i);
        int v = int_of_nat(succ(i))*x;
        assert map(snd,multiples_mod_p_inner(p,x,succ(i)))
            == cons(euclid_mod(v,p),map(snd,multiples_mod_p_inner(p,x,i)));
        euclid_mod_correct(v,p);
        assert [_] euclid_div_sol(v,p,?v_q,?v_r);

        assert v_r >= 0 &*& v_r < p;
        if(v_r == 0) {
            Zp_prod_zero(p,int_of_nat(succ(i)),x);
            assert false;
        }

    }

}

lemma void multiples_include(nat p_minus_1, int p, int x, int i)
    requires 1 <= i &*& i <= int_of_nat(p_minus_1)
        &*&  int_of_nat(succ(p_minus_1)) == p;
    ensures  !!mem(pair(i,euclid_mod(i*x,p)),
                multiples_mod_p(p_minus_1,x))
        &*&  !mem(pair(i,euclid_mod(i*x,p)),
                remove(pair(i,euclid_mod(i*x,p)),
                       multiples_mod_p(p_minus_1,x)));
{
ALREADY_PROVEN()
    for(nat j = zero; j != p_minus_1; j = succ(j))
        invariant int_of_nat(j) <= int_of_nat(p_minus_1)
            &*&   !mem(pair(i,euclid_mod(i*x,p)),
                    remove(pair(i,euclid_mod(i*x,p)),
                        multiples_mod_p_inner(p,x,j)))
            &*&   (int_of_nat(j) >= i)
                == (mem(pair(i,euclid_mod(i*x,p)),
                        multiples_mod_p_inner(p,x,j)))
            ;
        decreases int_of_nat(p_minus_1)-int_of_nat(j);
    {
        if(int_of_nat(j) >= int_of_nat(p_minus_1)) {
            assert int_of_nat(j) == int_of_nat(p_minus_1);
            nat_of_int_of_nat(j);
            assert false;
        }
    }
}

lemma void multiples_correct(nat p_minus_1, int p, int x, int i, int v)
    requires 1 <= i &*& i <= int_of_nat(p_minus_1)
        &*&  int_of_nat(succ(p_minus_1)) == p
        &*&  !!mem(pair(i,v),multiples_mod_p(p_minus_1,x));
    ensures  v == euclid_mod(i*x,p);
{
ALREADY_PROVEN()
    for(nat j = zero; j != p_minus_1; j = succ(j))
        invariant int_of_nat(j) <= int_of_nat(p_minus_1)
            &*&   (int_of_nat(j) < i
                    ? !mem(i, map(fst,multiples_mod_p_inner(p,x,j)))
                    : !mem(i, map(fst,
                        remove(pair(i,euclid_mod(i*x,p)),
                            multiples_mod_p_inner(p,x,j)))))
            ;
        decreases int_of_nat(p_minus_1)-int_of_nat(j);
    {
        if(int_of_nat(j) >= int_of_nat(p_minus_1)) {
            assert int_of_nat(j) == int_of_nat(p_minus_1);
            nat_of_int_of_nat(j);
            assert false;
        }

    }

    if(v != euclid_mod(i*x,p)) {
        assert !!mem(pair(i,v),
            remove(pair(i,euclid_mod(i*x,p)),
                multiples_mod_p(p_minus_1,x)));

        mem_fst_snd(i,v,
            remove(pair(i,euclid_mod(i*x,p)),
                multiples_mod_p(p_minus_1,x)));
        assert false;
    }
}

lemma void multiples_no_repeats(nat p_minus_1, int p, int g,
        int i, int j, int x)
    requires 1 <= i &*& i <= j &*& j <= int_of_nat(p_minus_1)
        &*&  int_of_nat(succ(p_minus_1)) == p
        &*&  euclid_mod(g,p) > 1
        &*&  !!mem(pair(i,x),multiples_mod_p(p_minus_1,g))
        &*&  !!mem(pair(j,x),multiples_mod_p(p_minus_1,g))
        &*&  !!is_prime(p);
    ensures  i == j;
{
ALREADY_PROVEN()
    multiples_correct(p_minus_1,p,g,i,x);
    multiples_correct(p_minus_1,p,g,j,x);
    note_eq( euclid_mod(i*g,p) ,  euclid_mod(j*g,p));
    Zp_diff_zero(p,j*g,i*g);
    assert euclid_mod((j-i)*g,p) == 0;
    Zp_prod_zero(p,j-i,g);
    if(i != j) { assert false; }
}

lemma s find_fst<s,t>(list<pair<s,t> > l, t x)
    requires !!mem(x,map(snd,l));
    ensures  !!mem(pair(result,x),l);
{
ALREADY_PROVEN()
    switch(l) {
    case nil:
        assert false;
    case cons(v,vs):
        switch(v) {
        case pair(a,b):
            if(b == x) {
                return a;
            } else {
                return find_fst(vs,x);
            }
        }
    }
}

lemma int multiples_hits_each_thing(nat p_minus_1, int p, int x, int v)
    requires 1 <= v &*& v <= int_of_nat(p_minus_1)
        &*&  int_of_nat(succ(p_minus_1)) == p
        &*&  euclid_mod(x,p) > 1
        &*&  !!is_prime(p);
    ensures  !!mem(pair(result,v),multiples_mod_p(p_minus_1,x));
{
ALREADY_PROVEN()
    list<pair<int,int> > multiples_full =
        multiples_mod_p(p_minus_1,x);
    list<int> multiples = map(snd,multiples_full);

    if(!mem(v,multiples)) {
        multiples_bounded(p_minus_1,x);
        if(!forall(multiples, (contains)(remove(v,range(1,p))))) {
            int cx = not_forall(multiples,
                    (contains)(remove(v,range(1,p))));
            if(cx == v) { assert false; }
            remove_other(cx,v,range(1,p));
            forall_elim(multiples,(bounded)(1,p-1),cx);
            bounded_range(1,p-1,cx);
            assert false;
        }

        assert length(range(1,p)) == p-1;
        map_length(snd,multiples_full);
        assert length(multiples) == length(multiples_full);
        assert length(multiples_full) == p-1;

        bounded_range(1,p-1,v);
        assert !!mem(v,range(1,p));
        assert length(remove(v,range(1,p))) == p-2;

        int v_doubled = pigeonhole(multiples, remove(v,range(1,p)));
        forall_elim(multiples,(bounded)(1,p-1),v_doubled);
        bounded_range(1,p-1,v_doubled);

        int i = find_fst(multiples_full,v_doubled);
        remove_from_pair_list(i,v_doubled,multiples_full);
        int j = find_fst(remove(pair(i,v_doubled),multiples_full),
                    v_doubled);
        multiples_indices(p_minus_1,x,i,v_doubled);
        multiples_indices(p_minus_1,x,j,v_doubled);
        if(i <= j) {
            multiples_no_repeats(p_minus_1,p,x,i,j,v_doubled);
        } else {
            multiples_no_repeats(p_minus_1,p,x,j,i,v_doubled);
        }
        assert i == j;
        multiples_correct(p_minus_1,p,x,i,v_doubled);
        assert v_doubled == euclid_mod(i*x,p);
        multiples_include(p_minus_1,p,x,i);

        assert false;
    }

    return find_fst(multiples_full, v);
}

fixpoint list<int> one_through_n(nat n) {
    switch(n) {
    case zero:
        return nil;
    case succ(n0):
        return cons(int_of_nat(n),one_through_n(n0));
    }
}

lemma_auto(length(one_through_n(n)))
void length_one_through_n(nat n)
    requires true;
    ensures  length(one_through_n(n)) == int_of_nat(n);
{ NAT_INDUCTION(n,n0,length_one_through_n(n0)) }

lemma_auto(mem(m,one_through_n(n)))
void one_through_n_bounded(nat n,int m)
    requires true;
    ensures  mem(m,one_through_n(n))
        ==   (m >= 1 && m <= int_of_nat(n));
{ NAT_INDUCTION(n,n0,one_through_n_bounded(n0,m)) }

lemma_auto(distinct(one_through_n(n)))
void one_through_n_distinct(nat n)
    requires true;
    ensures  !!distinct(one_through_n(n));
{ NAT_INDUCTION(n,n0,one_through_n_distinct(n0)) }

lemma_auto(product(one_through_n(n)))
void product_one_through_n_is_factorial(nat n)
    requires true;
    ensures  product(one_through_n(n)) == factorial(n);
{ NAT_INDUCTION(n,n0,product_one_through_n_is_factorial(n0)) }

lemma void multiples_distinct(nat p_minus_1, int p, int g)
    requires int_of_nat(succ(p_minus_1)) == p
        &*&  euclid_mod(g,p) > 1
        &*&  !!is_prime(p);
    ensures  !!distinct(map(snd,multiples_mod_p(p_minus_1,g)));
{
ALREADY_PROVEN()
    list<pair<int,int> > multiples = multiples_mod_p(p_minus_1,g);
    if(!distinct(map(snd,multiples))) {
        int cx = not_distinct(map(snd,multiples));
        assert !!mem(cx,map(snd,multiples));

        int i = find_fst(multiples,cx);
        assert !!mem(pair(i,cx),multiples);
        remove_from_pair_list(i,cx,multiples);
        int j = find_fst(remove(pair(i,cx),multiples),cx);

        multiples_indices(p_minus_1,g,i,cx);
        multiples_indices(p_minus_1,g,j,cx);
        if(i <= j) {
            multiples_no_repeats(p_minus_1,p,g,i,j,cx);
        } else {
            multiples_no_repeats(p_minus_1,p,g,j,i,cx);
        }
        assert i == j;
        multiples_correct(p_minus_1,p,g,i,cx);
        assert cx == euclid_mod(i*g,p);
        multiples_include(p_minus_1,p,g,i);

        assert false;
    }
}

lemma void multiples_hits_everything(nat p_minus_1, int p, int g)
    requires int_of_nat(succ(p_minus_1)) == p
        &*&  euclid_mod(g,p) > 1
        &*&  !!is_prime(p);
    ensures  !!is_permutation(map(snd,multiples_mod_p(p_minus_1,g)),
                              one_through_n(p_minus_1));
{
ALREADY_PROVEN()
    nat n = p_minus_1;
    list<pair<int,int> > multiples = multiples_mod_p(p_minus_1,g);
    list<int>            ns = one_through_n(n);

    multiples_distinct(p_minus_1,p,g);

    if(!is_permutation(map(snd,multiples),one_through_n(p_minus_1))) {
        int cx = not_permutation_distinct(map(snd,multiples),
                one_through_n(p_minus_1));

        if(mem(cx,map(snd,multiples))) {
            assert !mem(cx,one_through_n(p_minus_1));
            multiples_bounded(p_minus_1,g);
            forall_elim(map(snd,multiples),(bounded)(1,p-1),cx);
            assert false;
        } else {
            assert !!mem(cx,one_through_n(p_minus_1));
            one_through_n_bounded(p_minus_1,cx);

            int i = multiples_hits_each_thing(p_minus_1,p,g,cx);
            mem_fst_snd(i,cx,multiples);

            assert false;
        }
    }
}


lemma void multiples_product(nat p_minus_1, int p, int g)
    requires int_of_nat(succ(p_minus_1)) == p
        &*&  euclid_mod(g,p) > 1
        &*&  !!is_prime(p);
    ensures  euclid_mod(product(map(snd,
                            multiples_mod_p(p_minus_1, g))), p)
        ==   euclid_mod(factorial(p_minus_1)*pow_nat(g,p_minus_1),p);
{
ALREADY_PROVEN()
    for(nat j = zero; j != p_minus_1; j = succ(j))
        invariant int_of_nat(j) <= p-1
            &*&   euclid_mod(product(map(snd,
                            multiples_mod_p_inner(p, g, j))),
                    p)
               == euclid_mod(factorial(j)*pow_nat(g,j),p)
            ;
        decreases p-int_of_nat(j);
    {
        list<int> old_multiples = map(snd,
                multiples_mod_p_inner(p, g, j));
        list<int> new_multiples = map(snd,
                multiples_mod_p_inner(p, g, succ(j)));
        assert new_multiples
            == cons(euclid_mod(int_of_nat(succ(j))*g,p),
                    old_multiples);
        assert product(new_multiples)
            == euclid_mod(int_of_nat(succ(j))*g,p)
               *product(old_multiples);

        assert euclid_mod(product(new_multiples),p)
            == euclid_mod(euclid_mod(int_of_nat(succ(j))*g,p)
                    *product(old_multiples),p);

        Zp_times(p,
                euclid_mod(int_of_nat(succ(j))*g,p),
                product(old_multiples));
        assert euclid_mod(product(new_multiples),p)
            == euclid_mod(euclid_mod(int_of_nat(succ(j))*g,p)
                    *euclid_mod(factorial(j)*pow_nat(g,j),p),p);

        Zp_times(p,int_of_nat(succ(j))*g, factorial(j)*pow_nat(g,j));

        assert euclid_mod(product(new_multiples),p)
            == euclid_mod((int_of_nat(succ(j))*g)
                        *(factorial(j)*pow_nat(g,j)),p);

        mul_3var(int_of_nat(succ(j)),g,factorial(j)*pow_nat(g,j));

        assert (int_of_nat(succ(j))*g)*(factorial(j)*pow_nat(g,j))
            == int_of_nat(succ(j))*(g*(factorial(j)*pow_nat(g,j)));

        mul_3var(g,factorial(j),pow_nat(g,j));

        assert (int_of_nat(succ(j))*g)*(factorial(j)*pow_nat(g,j))
            == int_of_nat(succ(j))*(factorial(j)*(g*pow_nat(g,j)));

        mul_3var(int_of_nat(succ(j)),factorial(j),g*pow_nat(g,j));

        assert (int_of_nat(succ(j))*g)*(factorial(j)*pow_nat(g,j))
            == (int_of_nat(succ(j))*factorial(j))*(g*pow_nat(g,j));

        assert euclid_mod(product(new_multiples),p)
            == euclid_mod((int_of_nat(succ(j))*factorial(j))
                        *(g*pow_nat(g,j)),p);

        assert euclid_mod(product(new_multiples),p)
            == euclid_mod(factorial(succ(j))*pow_nat(g,succ(j)),p);

    }
}

// "proof as a particular case of Euler's theorem" found on wikipedia,
// attributed to James Ivory and supposedly rediscovered by Dirichlet
lemma void fermat_little(int p, int x)
    requires !!is_prime(p) &*& euclid_mod(x,p) != 0;
    ensures  euclid_mod(pow_nat(x,nat_of_int(p-1)),p) == 1;
{
ALREADY_PROVEN()
    if(euclid_mod(x,p) == 1) {
        Zp_pow(p,x,nat_of_int(p-1));
        assert pow_nat(euclid_mod(x,p),nat_of_int(p-1)) == 1;
    } else {
        euclid_mod_correct(x,p);
        assert euclid_mod(x,p) >= 0;
        if(euclid_mod(x,p) < 1) { assert false; }
        assert euclid_mod(x,p) > 1;

        nat p_minus_1 = nat_of_int(p-1);
        list<int> multiples = map(snd,multiples_mod_p(p_minus_1,x));
        multiples_product(p_minus_1,p,x);

        assert euclid_mod(product(multiples),p)
            == euclid_mod(factorial(p_minus_1)*pow_nat(x,p_minus_1),
                    p);

        multiples_hits_everything(p_minus_1,p,x);
        product_permutation(multiples,one_through_n(p_minus_1));

        assert product(multiples) == factorial(p_minus_1);
        assert euclid_mod(product(multiples),p)
            == euclid_mod(factorial(p_minus_1),p);

        Zp_diff_zero(p,
                factorial(p_minus_1)*pow_nat(x,p_minus_1),
                factorial(p_minus_1));

        assert euclid_mod(
                factorial(p_minus_1)*(pow_nat(x,p_minus_1)-1),p)
            == 0;

        Zp_prod_zero(p, factorial(p_minus_1), pow_nat(x,p_minus_1)-1);

        if(euclid_mod(pow_nat(x,p_minus_1)-1,p) == 0) {
            Zp_diff_zero(p,pow_nat(x,p_minus_1),1);
        } else {
            prime_divides_factorial(p,p_minus_1);
            assert false;
        }
    }
}

lemma void root_of_unity_loops(int n, int g, nat a, nat b)
    requires n > 1 &*& int_of_nat(a) > 0
        &*&  euclid_mod(pow_nat(g,a),n) == 1;
    ensures  euclid_mod(pow_nat(g,b),n)
        ==   euclid_mod(pow_nat(g,
                    nat_of_int(euclid_mod(int_of_nat(b),
                                          int_of_nat(a)))),n);
{
ALREADY_PROVEN()

    if(euclid_mod(pow_nat(g,b),n)
        !=   euclid_mod(pow_nat(g,
                    nat_of_int(euclid_mod(int_of_nat(b),
                                          int_of_nat(a)))),n)) {
        euclid_mod_correct(int_of_nat(b),int_of_nat(a));
        assert [_] euclid_div_sol(int_of_nat(b),int_of_nat(a),?q,?r);
        assert pow_nat(g,b) == pow_nat(g,nat_of_int(q*int_of_nat(a) + r));
        assert euclid_mod(pow_nat(g,b),n)
            == euclid_mod(pow_nat(g,
                        nat_of_int(q*int_of_nat(a) + r)),n);

        assert r >= 0;
        assert r == int_of_nat(nat_of_int(r));
        if(q < 0) {
            my_mul_mono_l(q,-1,int_of_nat(a));
            assert false;
        }
        my_mul_mono_l(0,q,int_of_nat(a));
        assert q*int_of_nat(a) >= 0;
        pow_plus(g,nat_of_int(r),q*int_of_nat(a));

        assert euclid_mod(pow_nat(g,b),n)
            == euclid_mod(pow_nat(g, nat_of_int(q*int_of_nat(a)))
                        *pow_nat(g, nat_of_int(r)),n);

        Zp_times(n,pow_nat(g, nat_of_int(q*int_of_nat(a))),
                pow_nat(g, nat_of_int(r)));

        assert euclid_mod(pow_nat(g,b),n)
            == euclid_mod(euclid_mod(pow_nat(g,
                            nat_of_int(q*int_of_nat(a))),n)
                        *euclid_mod(pow_nat(g, nat_of_int(r)),n),n);

        pow_times2(g,a,q);
        assert pow_nat(g, nat_of_int(q*int_of_nat(a)))
            == pow_nat(pow_nat(g,a), nat_of_int(q));

        Zp_pow(n,pow_nat(g,a), nat_of_int(q));

        assert false;
    }

}

lemma void order_gcd(int n, int g, nat a, nat b)
    requires n > 1 &*& int_of_nat(a) > 0 &*& int_of_nat(b) > 0
        &*&  int_of_nat(a) <= int_of_nat(b)
        &*&  euclid_mod(pow_nat(g,a),n) == 1
        &*&  euclid_mod(pow_nat(g,b),n) == 1;
    ensures  let(gcd(int_of_nat(a),int_of_nat(b)),?d)
        &*&  euclid_mod(pow_nat(g,nat_of_int(d)),n) == 1;
{
ALREADY_PROVEN()
    int av = int_of_nat(a);
    int bv = int_of_nat(b);
    close let(gcd(av,bv),?d);
    switch(gcd_min_lincomb_sol(av,bv)) {
    case pair(x,y):
        assert x*av + y*bv == d;
        assert d > 0;
        assert euclid_mod(pow_nat(g,nat_of_int(d)),n)
            == euclid_mod(pow_nat(g,nat_of_int(x*av + y*bv)),n);

        assert euclid_mod(pow_nat(g,nat_of_int(d)),n)
            == euclid_mod(pow_nat(g,nat_of_int(x*av + y*bv)),n);
        root_of_unity_loops(n, g, a, nat_of_int(d));

        assert euclid_mod(pow_nat(g,nat_of_int(d)),n)
            == euclid_mod(
                pow_nat(g,
                        nat_of_int(euclid_mod(x*av + y*bv,
                                              av))),
                n);

        Zp_plus(av,x*av, y*bv);
        Zp_times(av,x,av);

        assert euclid_mod(x*av,av)
            == euclid_mod(euclid_mod(x,av)*euclid_mod(av,av),
                    av);
        assert euclid_mod(av,av) == 0;
        assert euclid_mod(x*av,av)
            == euclid_mod(euclid_mod(x,av)*0,
                    av);
        assert euclid_mod(x*av,av)
            == euclid_mod(0, av);

        assert euclid_mod(x*av,av) == 0;

        assert euclid_mod(x*av + y*bv, av)
            == euclid_mod(y*bv,av);

        Zp_times(av,y,bv);


        assert euclid_mod(pow_nat(g,nat_of_int(d)),n)
            == euclid_mod(
                pow_nat(g,
                        nat_of_int(euclid_mod(y*bv,av))),
                n);

        assert euclid_mod(pow_nat(g,nat_of_int(d)),n)
            == euclid_mod(
                pow_nat(g,
                        nat_of_int(
                            euclid_mod(euclid_mod(y,av)
                                       *euclid_mod(bv,av),
                                av))),
                n);

        my_mul_mono_l(0, euclid_mod(y,av), euclid_mod(bv,av));
        assert euclid_mod(y,av)*euclid_mod(bv,av) >= 0;

        root_of_unity_loops(n, g, a,
                nat_of_int(euclid_mod(y,av)*euclid_mod(bv,av)));

        int_of_nat_of_int(euclid_mod(y,av)*euclid_mod(bv,av));
        assert euclid_mod(pow_nat(g,nat_of_int(d)),n)
            == euclid_mod(
                pow_nat(g,
                        nat_of_int(euclid_mod(y,av)*euclid_mod(bv,av))),
                n);

        pow_times2(g,nat_of_int(euclid_mod(bv,av)),euclid_mod(y,av));
        assert euclid_mod(pow_nat(g,nat_of_int(d)),n)
            == euclid_mod(
                pow_nat(pow_nat(g,nat_of_int(euclid_mod(bv,av))),
                        nat_of_int(euclid_mod(y,av))),
                n);

        Zp_pow(n,pow_nat(g, nat_of_int(euclid_mod(bv,av))),
               nat_of_int(euclid_mod(y,av)));
        assert euclid_mod(pow_nat(g,nat_of_int(d)),n)
            == euclid_mod(
                pow_nat(euclid_mod(pow_nat(g,
                                    nat_of_int(euclid_mod(bv,av))),n),
                        nat_of_int(euclid_mod(y,av))),
                n);

        root_of_unity_loops(n,g,a,b);

        assert euclid_mod(pow_nat(g,nat_of_int(d)),n)
            == euclid_mod(
                pow_nat(euclid_mod(pow_nat(g, b),n),
                        nat_of_int(euclid_mod(y,av))),
                n);

        assert euclid_mod(pow_nat(g,nat_of_int(d)),n)
            == euclid_mod(
                pow_nat(1, nat_of_int(euclid_mod(y,av))),
                n);

        assert euclid_mod(pow_nat(g,nat_of_int(d)),n)
            == euclid_mod(1, n);
        assert euclid_mod(pow_nat(g,nat_of_int(d)),n)
            == 1;

    }
}

lemma void order_mod_n_bounded(int n, int x, nat o)
    requires n > 1 &*&  order_mod_n(n,x) == some(o);
    ensures  0 < int_of_nat(o) &*& int_of_nat(o) < n;
{
ALREADY_PROVEN()
    nat f = nat_of_int(n-1);
    option<nat> best_so_far = none;
    while(f != zero)
        invariant order_mod_n(n,x)
            ==    order_mod_n_fueled(f, n, x, best_so_far)
            &*&   int_of_nat(f) < n
            &*&   switch(best_so_far) {
            case none: return true;
            case some(b): return int_of_nat(b) > 0 &*& int_of_nat(b) < n;
            };
        decreases int_of_nat(f);
    {
        if(euclid_mod(pow_nat(x,f),n) == 1) {
            best_so_far = some(f);
        }
        switch(f) {
        case zero: assert false;
        case succ(f0): f = f0;
        }
    }
}

lemma void order_mod_n_correct_basic(int n, int x)
    requires n > 1;
    ensures  switch(order_mod_n(n,x)) {
        case none: return true;
        case some(o):
            return  euclid_mod(pow_nat(x,o), n) == 1;
    };
{
ALREADY_PROVEN()
    nat f = nat_of_int(n-1);
    option<nat> best_so_far = none;
    while(f != zero)
        invariant order_mod_n(n,x)
            ==    order_mod_n_fueled(f, n, x, best_so_far)
            &*&   switch(best_so_far) {
            case none: return true;
            case some(b): return euclid_mod(pow_nat(x,b),n) == 1;
            };
        decreases int_of_nat(f);
    {
        if(euclid_mod(pow_nat(x,f),n) == 1) {
            best_so_far = some(f);
        }
        switch(f) {
        case zero: assert false;
        case succ(f0): f = f0;
        }
    }
}

lemma void pow_hits_1_gcd(int n, nat o, int x)
    requires n > 1 &*& x >= 1
        &*&  euclid_mod(pow_nat(x, succ(o)), n) == 1;
    ensures  gcd(x,n) == 1;
{
ALREADY_PROVEN()
    euclid_mod_correct(pow_nat(x,succ(o)),n);

    assert [_] euclid_div_sol(pow_nat(x,succ(o)),n,?q,1);
    assert pow_nat(x,succ(o)) == n*q + 1;
    assert x*pow_nat(x,o) - n*q - 1 == 0;
    int d = gcd(x,n);
    if(d != 1) {

        assert d > 1;
        div_rem(x,d);
        assert x == d*(x/d);
        div_rem(n,d);
        assert n == d*(n/d);
        assert (d*(x/d))*pow_nat(x,o) - (d*(n/d))*q == 1;
        mul_3var(d,x/d,pow_nat(x,o));
        mul_3var(d,n/d,q);
        division_unique(1,d,(x/d)*pow_nat(x,o) - (n/d)*q,0);
        division_unique(1,d,0,1);
        assert false;
    }

}

lemma void coprime_pow_never_hits_0(int n, int x, nat o)
    requires n > 1 &*& x >= 1 &*& gcd(x,n) == 1;
    ensures  euclid_mod(pow_nat(x,o),n) != 0;
{
ALREADY_PROVEN()
    if(euclid_mod(pow_nat(x,o),n) == 0) {
        if(x == 1) { assert false; }

        assert x >= 2;

        euclid_mod_correct(pow_nat(x,o),n);

        assert [_] euclid_div_sol(pow_nat(x,o),n,?q,0);

        switch(o) {
        case zero: assert false;
        case succ(o0):
            assert pow_nat(x,o) == x*pow_nat(x,o0);
            assert pow_nat(x,o) == q*n;
            assert x*pow_nat(x,o0) == q*n;

            int p = findSomeFactor(n);
            assert n%p == 0;
            assert p >= 2;

            if(x%p == 0) {
                gcd_is_max_divisor(x,n,p);
                assert false;
            }

            div_rem(n,p);
            assert n == (n/p)*p;
            assert q*n == q*((n/p)*p);
            mul_3var(q,n/p,p);
            division_unique(q*n,p,(n/p)*q,0);
            assert (q*n)%p == 0;

            prime_divides_product(p,x,pow_nat(x,o0));
            assert pow_nat(x,o0)%p == 0;
            prime_divides_pow(p,x,o0);

            assert false;
        }
    }
}

lemma void equal_pows_mod_n(int n, int x, int e1, int e2)
    requires n > 1 &*& x >= 1 &*& gcd(x,n) == 1
        &*&  e1 >= 0 &*& e2 >= 0
        &*&  euclid_mod(pow_nat(x,nat_of_int(e1)),n)
        ==   euclid_mod(pow_nat(x,nat_of_int(e2)),n);
    ensures  euclid_mod(pow_nat(x,nat_of_int(abs(e1-e2))),n) == 1;
{
ALREADY_PROVEN()
    if(e1 == e2) {
        assert abs(e1-e2) == 0;
        return;
    }

    assert e1 != e2;
    assert euclid_mod(pow_nat(x,nat_of_int(e1)),n)
        == euclid_mod(pow_nat(x,nat_of_int(e2)),n);

    if(e1 > e2) {
        int tmp = e1;
        e1 = e2;
        e2 = tmp;
    }

    note(e1 < e2);
    int_of_nat_of_int(e1);
    int_of_nat_of_int(e2-e1);

    note_eq(pow_nat(x,nat_of_int(e2))
        ,  pow_nat(x,nat_of_int(e1 + (e2-e1))));

    pow_plus(x,nat_of_int(e1),e2-e1);
    assert pow_nat(x,nat_of_int(e2))
        == pow_nat(x,nat_of_int(e1))*pow_nat(x,nat_of_int(e2-e1));

    assert euclid_mod(pow_nat(x,nat_of_int(e1)),n)
        == euclid_mod(pow_nat(x,nat_of_int(e1))
                      *pow_nat(x,nat_of_int(e2-e1)),
                      n);

    assert euclid_mod(pow_nat(x,nat_of_int(e1)),n)
        == euclid_mod(pow_nat(x,nat_of_int(e1))
                      *pow_nat(x,nat_of_int(e2-e1)),
                      n);

    Zp_diff_zero(n,
            pow_nat(x,nat_of_int(e1)),
            pow_nat(x,nat_of_int(e1))*pow_nat(x,nat_of_int(e2-e1)));
    assert euclid_mod(pow_nat(x,nat_of_int(e1))
                      - pow_nat(x,nat_of_int(e1))
                        *pow_nat(x,nat_of_int(e2-e1)),
            n)
        == 0;

    assert euclid_mod(pow_nat(x,nat_of_int(e1))
                      *(1-pow_nat(x,nat_of_int(e2-e1))),
            n)
        == 0;

    int x_p_e1 = pow_nat(x,nat_of_int(e1));

    if(gcd(x_p_e1,n) != 1) {
        int d = gcd(x_p_e1,n);
        int p = findSomeFactor(d);
        assert d%p == 0;

        div_rem(d,p);
        div_rem(n,d);
        div_rem(x_p_e1,d);

        mul_3var(p,n/d,d/p);
        division_unique(n,p,(n/d)*(d/p),0);
        mul_3var(p,x_p_e1/d,d/p);
        division_unique(x_p_e1,p,(x_p_e1/d)*(d/p),0);
        prime_divides_pow(p, x, nat_of_int(e1-1));
        assert x%p == 0;
        gcd_is_max_divisor(x,n,p);

        assert false;
    }

    assert gcd(x_p_e1,n) == 1;
    int x_p_e1_inv = Rp_recip(n,x_p_e1);

    Zp_x_times_zero(n,
            x_p_e1*(1-pow_nat(x,nat_of_int(e2-e1))),
            x_p_e1_inv);
    assert euclid_mod(x_p_e1_inv
                      *(x_p_e1*(1-pow_nat(x,nat_of_int(e2-e1)))),
                      n)
        == 0;

    mul_3var(x_p_e1_inv, x_p_e1, (1-pow_nat(x,nat_of_int(e2-e1))));
    assert euclid_mod((x_p_e1_inv*x_p_e1)
                      *(1-pow_nat(x,nat_of_int(e2-e1))),
                      n)
        == 0;

    Zp_times(n,x_p_e1_inv*x_p_e1, 1-pow_nat(x,nat_of_int(e2-e1)));
    assert euclid_mod(1-pow_nat(x,nat_of_int(e2-e1)),
                      n)
        == 0;

    Zp_diff_zero(n,1,pow_nat(x,nat_of_int(e2-e1)));
    assert euclid_mod(pow_nat(x,nat_of_int(e2-e1)),
                      n)
        == euclid_mod(1,n);

    assert euclid_mod(pow_nat(x,nat_of_int(e2-e1)),
                      n)
        == 1;
}

lemma nat coprime_pow_hits_1(int n, int x)
    requires n > 1 &*& x >= 1 &*& gcd(x,n) == 1;
    ensures  int_of_nat(result) < n &*& int_of_nat(result) > 0
        &*&  euclid_mod(pow_nat(x,result),n) == 1;
{
ALREADY_PROVEN()
    list<int> exps = one_through_n(nat_of_int(n));
    fixpoint(int,int) x_pow_mod_n
        = (o)((flip)(euclid_mod,n),(o)((pow_nat)(x),nat_of_int));
    list<int> pows = map(x_pow_mod_n, exps);

    assert length(exps) == n;
    map_length(x_pow_mod_n,exps);
    assert length(pows) == n;

    if(!forall(pows,(bounded)(1,n-1))) {
        int cx = not_forall(pows,(bounded)(1,n-1));
        int e = map_preimage(cx, x_pow_mod_n, exps);

        assert cx == euclid_mod(pow_nat(x,nat_of_int(e)),n);
        assert cx >= 0 &*& cx < n;
        assert cx < 1;
        assert cx == 0;

        coprime_pow_never_hits_0(n,x,nat_of_int(e));

        assert false;
    }

    if(!forall(pows, (contains)(range(1,n)))) {
        int cx = not_forall(pows, (contains)(range(1,n)));
        forall_elim(pows,(bounded)(1,n-1),cx);
        bounded_range(1,n-1,cx);
        assert false;
    }

    int v  = pigeonhole(pows, range(1,n));
    int e1 = map_remove(v, x_pow_mod_n, exps);

    int e2 = map_preimage(v, x_pow_mod_n, remove(e1,exps));

    assert e1 != e2;
    assert euclid_mod(pow_nat(x,nat_of_int(e1)),n)
        == euclid_mod(pow_nat(x,nat_of_int(e2)),n);

    equal_pows_mod_n(n,x,e1,e2);

    return nat_of_int(abs(e2-e1));
}

lemma void order_mod_n_correct(int n, int x)
    requires n > 1 &*& x >= 1;
    ensures  switch(order_mod_n(n,x)) {
        case none:
            //return gcd(x,n) != 1;
            return euclid_mod(x,n) == 0 || !is_prime(n);
        case some(o):
            return  int_of_nat(o) >= 1
                &*& gcd(x,n) == 1
                &*& euclid_mod(pow_nat(x,o), n) == 1;
    };
{
ALREADY_PROVEN()
    nat f = nat_of_int(n-1);
    option<nat> best_so_far = none;
    while(f != zero)
        invariant order_mod_n(n,x)
            ==    order_mod_n_fueled(f, n, x, best_so_far)
            &*&   int_of_nat(f) < n
            &*&   switch(best_so_far) {
            case none:
                return int_of_nat(f) == n-1 ? true
                    : euclid_mod(x,n) == 0 || !is_prime(n);
            case some(b):
                return  int_of_nat(b) > 0 &*& int_of_nat(b) < n
                    &*& euclid_mod(pow_nat(x,b),n) == 1;
            };
        decreases int_of_nat(f);
    {
        if(euclid_mod(pow_nat(x,f),n) == 1) {
            best_so_far = some(f);
        } else if(int_of_nat(f) == n-1 && is_prime(n) && euclid_mod(x,n) != 0) {
            fermat_little(n,x);
            assert false;
        }
        switch(f) {
        case zero: assert false;
        case succ(f0): f = f0;
        }
    }

    switch(best_so_far) {
    case none:
    case some(o):
        switch(o) {
        case zero:
            assert false;
        case succ(o0):
            pow_hits_1_gcd(n,o0,x);
        }
    }
}

lemma void order_mod_n_minimal(int n, int x, nat o)
    requires n > 1 &*& x >= 1 &*& euclid_mod(pow_nat(x,succ(o)), n) == 1;
    ensures  switch(order_mod_n(n,x)) {
        case none: return false;
        case some(my_o):
            return  int_of_nat(my_o) <= int_of_nat(o)+1;
    };
{
ALREADY_PROVEN()
    pow_hits_1_gcd(n,o,x);
    nat e = coprime_pow_hits_1(n,x);

    nat f = nat_of_int(n-1);
    option<nat> best_so_far = none;
    nat my_o = f;
    while(f != zero)
        invariant order_mod_n(n,x)
            ==    order_mod_n_fueled(f,n,x,best_so_far)
            &*&   (best_so_far == none
                    || (best_so_far == some(my_o)
                        && euclid_mod(pow_nat(x,my_o),n) == 1))
            &*&   (int_of_nat(f) >= int_of_nat(o) + 1
                    || int_of_nat(f) >= int_of_nat(e)
                    || (best_so_far != none
                        && int_of_nat(my_o) <= int_of_nat(o) + 1));
        decreases int_of_nat(f);
    {
        switch(f) {
        case zero: assert false;
        case succ(f0):
            if(euclid_mod(pow_nat(x,f),n) == 1) {
                my_o = f;
                best_so_far = some(f);
            }

            if(int_of_nat(f) >= int_of_nat(o)+1
                || int_of_nat(f) >= int_of_nat(e)) {
                if(int_of_nat(f0) < int_of_nat(o)+1 &&
                        int_of_nat(f0) < int_of_nat(e)) {
                    assert int_of_nat(f) == int_of_nat(o)+1
                        || int_of_nat(f) == int_of_nat(e);
                    if(euclid_mod(pow_nat(x,f),n) != 1) {
                        nat_of_int_of_nat(f);
                        if(int_of_nat(f) == int_of_nat(o)+1) {
                            assert int_of_nat(o)+1
                                == int_of_nat(succ(o));
                            assert false;
                        }
                        if(int_of_nat(f) == int_of_nat(e)) {
                            assert false;
                        }
                    }

                    assert euclid_mod(pow_nat(x,f),n) == 1;
                    assert best_so_far == some(f);
                    assert int_of_nat(f) <= int_of_nat(o)+1;
                }
            }

            f = f0;
        }
    }
}

lemma int orders_mod_n_divides(int n, int x, nat o1, nat o2)
    requires n > 1 &*& x >= 1
        &*&  order_mod_n(n,x) == some(o1)
        &*&  euclid_mod(pow_nat(x,succ(o2)), n) == 1;
    ensures  int_of_nat(o1) <= int_of_nat(succ(o2))
        &*&  result*int_of_nat(o1) == int_of_nat(succ(o2));
{
ALREADY_PROVEN()
    order_mod_n_correct(n,x);
    assert int_of_nat(o1) >= 1;
    assert o1 == succ(nat_of_int(int_of_nat(o1)-1));

    order_mod_n_minimal(n,x,o2);
    order_gcd(n,x,o1,succ(o2));

    int d = gcd(int_of_nat(o1),int_of_nat(succ(o2)));

    order_mod_n_minimal(n,x,nat_of_int(d-1));
    assert d >= int_of_nat(o1);
    assert d == int_of_nat(o1);
    div_rem(int_of_nat(succ(o2)),d);
    return int_of_nat(succ(o2))/d;
}

fixpoint int x_pow_mod_n(int n, int x, int e) {
    return euclid_mod(pow_nat(x,nat_of_int(e)),n);
}

lemma void orbit_mod_n(int n, int x, nat o)
    requires n > 1 &*& x >= 1 &*& order_mod_n(n,x) == some(o);
    ensures  let(one_through_n(o), ?exps)
        &*&  let(map((x_pow_mod_n)(n,x),exps), ?pows)
        &*&  length(pows) == int_of_nat(o)
        &*&  !!forall(pows,(bounded)(1,n-1))
        &*&  !!distinct(pows);
{
ALREADY_PROVEN()
    list<int> exps = one_through_n(o);
    fixpoint(int,int) x_pow_mod_n
        = (x_pow_mod_n)(n,x);
    list<int> pows = map(x_pow_mod_n, exps);

    assert length(exps) == int_of_nat(o);
    map_length(x_pow_mod_n,exps);
    assert length(pows) == int_of_nat(o);
    order_mod_n_correct(n,x);
    assert o == succ(nat_of_int(int_of_nat(o)-1));
    pow_hits_1_gcd(n,nat_of_int(int_of_nat(o)-1),x);

    if(!forall(pows,(bounded)(1,n-1))) {
        int cx = not_forall(pows,(bounded)(1,n-1));
        int e = map_preimage(cx, x_pow_mod_n, exps);

        assert cx == euclid_mod(pow_nat(x,nat_of_int(e)),n);
        assert cx >= 0 &*& cx < n;
        assert cx < 1;
        assert cx == 0;

        coprime_pow_never_hits_0(n,x,nat_of_int(e));

        assert false;
    }

    if(!distinct(pows)) {
        int cx = not_distinct(pows);
        int e1 = map_remove(cx, x_pow_mod_n, exps);
        int e2 = map_preimage(cx, x_pow_mod_n, remove(e1,exps));
        assert e1 != e2;

        assert euclid_mod(pow_nat(x,nat_of_int(e1)),n)
            == euclid_mod(pow_nat(x,nat_of_int(e2)),n);
        assert euclid_mod(pow_nat(x,nat_of_int(e1)),n)
            == euclid_mod(pow_nat(x,nat_of_int(e2)),n);
        equal_pows_mod_n(n,x,e1,e2);
        assert abs(e2-e1) < int_of_nat(o);
        assert abs(e2-e1) >= 1;
        assert euclid_mod(pow_nat(x,nat_of_int(abs(e2-e1))),n)
            == 1;
        int_of_nat_of_int(abs(e2-e1)-1);
        assert nat_of_int(abs(e2-e1))
            == succ(nat_of_int(abs(e2-e1)-1));
        order_mod_n_minimal(n,x,nat_of_int(abs(e2-e1)-1));
        assert false;
    }
}

lemma void pratt_core_lemma(int p, int x)
    requires p > 1 &*& x > 1
        &*&  order_mod_n(p,x) == some(nat_of_int(p-1));
    ensures  !!is_prime(p);
{
ALREADY_PROVEN()
    nat o = nat_of_int(p-1);
    order_mod_n_correct(p,x);
    assert euclid_mod(pow_nat(x,o),p) == 1;

    orbit_mod_n(p,x,nat_of_int(p-1));
    list<int> exps = one_through_n(o);
    fixpoint(int,int) x_pow_mod_p
        = (x_pow_mod_n)(p,x);
    list<int> pows = map(x_pow_mod_p, exps);

    assert !!forall(pows,(bounded)(1,p-1));
    assert !!distinct(pows);
    if(!is_permutation(pows,range(1,p))) {
        int cx = not_permutation_distinct(pows,range(1,p));

        if(mem(cx,range(1,p))) {
            assert !mem(cx,pows);

            if(!forall(pows,(contains)(remove(cx,range(1,p))))) {
                int cx2 = not_forall(pows,
                        (contains)(remove(cx, range(1, p))));
                forall_elim(pows, (bounded)(1,p-1), cx2);
                bounded_range(1,p-1, cx2);
                assert false;
            }
            assert length(remove(cx,range(1,p)))
                == p-2;

            pigeonhole(pows,remove(cx,range(1,p)));
            assert false;
        }

        if(mem(cx,pows)) {
            forall_elim(pows, (bounded)(1,p-1), cx);
            bounded_range(1,p-1, cx);
            assert false;
        }

    }

    //pow_hits_1_gcd(x,

    if(!is_prime(p)) {
        int q = findFactor(p);
        assert q >= 1 &*& q < p;
        bounded_range(1,p-1,q);
        assert !!mem(q,range(1,p));
        is_perm_mem(range(1,p),pows,q);
        int e = map_preimage(q, x_pow_mod_p, exps);
        assert euclid_mod(pow_nat(x,nat_of_int(e)),p) == q;
        assert euclid_mod(pow_nat(q,nat_of_int(p-1)),p)
            == euclid_mod(
                    pow_nat(
                        euclid_mod(pow_nat(x,nat_of_int(e)),p),
                        nat_of_int(p-1)),p);

        Zp_pow(p,pow_nat(x,nat_of_int(e)),nat_of_int(p-1));

        assert euclid_mod(pow_nat(q,nat_of_int(p-1)),p)
            == euclid_mod(
                    pow_nat(pow_nat(x,nat_of_int(e)),
                        nat_of_int(p-1)),p);

        pow_times2(x,nat_of_int(e),p-1);

        assert euclid_mod(pow_nat(q,nat_of_int(p-1)),p)
            == euclid_mod(pow_nat(x,nat_of_int(e*(p-1))), p);

        pow_times2(x,nat_of_int(p-1),e);
        assert euclid_mod(pow_nat(q,nat_of_int(p-1)),p)
            == euclid_mod(pow_nat(pow_nat(x,nat_of_int(p-1)),
                            nat_of_int(e)), p);

        Zp_pow(p,pow_nat(x,nat_of_int(p-1)),nat_of_int(e));
        assert euclid_mod(pow_nat(q,nat_of_int(p-1)),p)
            == euclid_mod(pow_nat(
                        euclid_mod(pow_nat(x,nat_of_int(p-1)),p),
                            nat_of_int(e)), p);

        assert euclid_mod(pow_nat(q,nat_of_int(p-1)),p)
            == euclid_mod(pow_nat(1, nat_of_int(e)), p);

        assert euclid_mod(pow_nat(q,nat_of_int(p-1)),p)
            == euclid_mod(1, p);

        assert euclid_mod(pow_nat(q,nat_of_int(p-1)),p)
            == 1;

        pow_hits_1_gcd(p,nat_of_int(p-2),q);
        division_unique(q,q,1,0);
        gcd_is_max_divisor(p,q,q);

        assert false;
    }

}

lemma void square_roots_of_one_basic(int p, int x)
    requires p > 1 &*& !!mem(euclid_mod(x,p), {p-1,1});
    ensures  (euclid_mod(x*x,p) == 1);
{
    Zp_times(p,x,x);
    if(euclid_mod(x,p) == 1) {
        assert euclid_mod(x*x,p) == euclid_mod(1,p);
        assert euclid_mod(x*x,p) == 1;
    } else {
        assert euclid_mod(x,p) == p-1;
        assert euclid_mod(x*x,p) == euclid_mod((p-1)*(p-1),p);
        assert euclid_mod(x*x,p) == euclid_mod(p*(p - 2)+1,p);
        euclid_div_unique_intro(p*(p-2)+1,p,p-2,1);
    }
}

lemma void pratt_order_check_lemma(int p, list<int> p_minus_1, int x)
    requires p > 1 &*& x > 1 &*& x < p
        &*&  !!forall(p_minus_1,is_prime)
        &*&  product(p_minus_1)+1 == p
        &*&  euclid_mod(pow_nat(x,nat_of_int(p-1)),p) == 1
        &*&  !!forall(p_minus_1,(pratt_pow_thing)(p,x))
        ;
    ensures  order_mod_n(p,x) == some(nat_of_int(p-1));
{
ALREADY_PROVEN()
    order_mod_n_minimal(p, x, nat_of_int(p-2));
    switch(order_mod_n(p,x)) {
    case none: assert false;
    case some(o):
        assert int_of_nat(o) <= p-1;
        order_mod_n_correct(p,x);
        assert euclid_mod(pow_nat(x,o),p) == 1;

        if(o != nat_of_int(p-1)) {
            order_gcd(p,x,o,nat_of_int(p-1));

            int d = gcd(int_of_nat(o),p-1);
            assert euclid_mod(pow_nat(x,nat_of_int(d)),p) == 1;
            assert d >= 1;

            if(d == 1) {
                assert pow_nat(x,nat_of_int(d)) == x;
                euclid_mod_correct(x,p);
                assert [_]euclid_div_sol(x,p,?q,?r);
                euclid_div_unique(x,p,q,r,0,x);
                assert false;
            }

            assert d >= 2;
            assert (p-1)%d == 0;
            assert int_of_nat(o)%d == 0;

            div_rem(p-1,d);
            assert p-1 == d*((p-1)/d);

            if(d == p-1) {
                assert false;
            }

            if((p-1)/d <= 1) {
                if((p-1)/d <= 0) {
                    my_mul_mono_l((p-1)/d,0,d);
                }
                assert false;
            }

            int d_factor = findSomeFactor((p-1)/d);

            div_rem((p-1)/d,d_factor);

            if(((p-1)/d)/d_factor <= 0) {
                my_mul_mono_l(((p-1)/d)/d_factor,0,d_factor);
                assert false;
            }

            mul_3var(d,((p-1)/d)/d_factor,d_factor);

            assert p-1 == d_factor*(d*(((p-1)/d)/d_factor));
            division_unique(p-1,d_factor,d*(((p-1)/d)/d_factor),0);

            prime_factorization_exhaustive(p-1,d_factor,p_minus_1);

            forall_elim(p_minus_1, (pratt_pow_thing)(p,x), d_factor);
            assert euclid_mod(pow_nat(x,nat_of_int((p-1)/d_factor)),p)
                != 1;
            assert euclid_mod(pow_nat(x,nat_of_int(d*(((p-1)/d)/d_factor))),p)
                != 1;

            pow_times2(x,nat_of_int(d),((p-1)/d)/d_factor);
            assert pow_nat(x,nat_of_int(d*(((p-1)/d)/d_factor)))
                == pow_nat(pow_nat(x,nat_of_int(d)),
                        nat_of_int(((p-1)/d)/d_factor));

            assert euclid_mod(pow_nat(x,nat_of_int(d*(((p-1)/d)/d_factor))),p)
                == euclid_mod(pow_nat(pow_nat(x,nat_of_int(d)),
                                nat_of_int(((p-1)/d)/d_factor)),p);

            Zp_pow(p,pow_nat(x,nat_of_int(d)),nat_of_int(((p-1)/d)/d_factor));

            assert false;
        }
    }
}

lemma
void pratt_certificate_raise_fuel(pratt_cert cert, nat f1, nat f2)
    requires [?fr]pratt_certificate(cert,?rest,f1,?p)
        &*&  int_of_nat(f1) <= int_of_nat(f2);
    ensures  [ fr]pratt_certificate(cert, rest,f2, p);
{
    open pratt_certificate(cert,rest,f1,_);
    switch(cert) {
    case pratt_small(x):
    case pratt_cert(g,factors):
        switch(factors) {
        case nil:
        case cons(f,fs):
            switch(f1) {
            case zero: assert false;
            case succ(f1_0):
                switch(f2) {
                case zero: assert false;
                case succ(f2_0):
                    switch(f) {
                    case pair(q,qcert):
                        pratt_certificate_raise_fuel(qcert,f1_0,f2_0);
                        pratt_certificate_raise_fuel(pratt_cert(g,fs),f1_0,f2_0);
                    }
                }
            }
        }
    }
    close [fr]pratt_certificate(cert,rest,f2,_);
}

lemma
void prime_no_divide_sqrt(nat n, int x)
    requires x > 1 &*& int_of_nat(n) < x &*& int_of_nat(n)*int_of_nat(n) >= x;
    ensures  is_prime(x) == all_no_divide(x,primes_below(n));
{
    ALREADY_PROVEN()
    assert int_of_nat(succ(n)) == int_of_nat(n)+1;
    my_mul_strict_mono_l(int_of_nat(n),int_of_nat(n)+1,int_of_nat(n));
    my_mul_strict_mono_r(int_of_nat(n)+1,int_of_nat(n),int_of_nat(n)+1);
    prime_test_sqrt(x,n);
}

lemma
void pratt_certificate_prime_inner(int p, pratt_cert cert, nat fuel)
    requires [?fr]pratt_certificate(cert,1,fuel,p);
    ensures  [ fr]pratt_certificate(cert,1,fuel,p)
        &*&  !!is_prime(p);
{
    switch(fuel) {
    case zero:
        if(!is_prime(p)) {
            open pratt_certificate(_,_,_,_);
            switch(cert) {
            case pratt_small(x):
                if(mem(x,primes_below(nat_of_int(100)))) {
                    assert false;
                } else {
                    assert !!all_no_divide(x,primes_below(nat_of_int(100)));
                    prime_no_divide_sqrt(nat_of_int(100),x);
                }
                assert false;
            case pratt_cert(g,factors):
                assert false;
            }
        }
    case succ(fuel0):
        if(!is_prime(p)) {
            open pratt_certificate(_,_,_,_);
            switch(cert) {
            case pratt_small(x):
                if(mem(x,primes_below(nat_of_int(100)))) {
                    assert false;
                } else {
                    assert !!all_no_divide(x,primes_below(nat_of_int(100)));
                    prime_no_divide_sqrt(nat_of_int(100),x);
                }
                assert false;
            case pratt_cert(g,factors):
                list<int> factorization = map(fst,factors);
                assert product(factorization) == p-1;
                assert !!forall(factorization,(pratt_pow_thing)(p,g));

                if(!forall(factorization,is_prime)) {
                    switch(factors) {
                    case nil: assert false;
                    case cons(f,fs):
                        int rest = 1;
                        assert [fr]pratt_certificate(
                                pratt_cert(g, fs), ?rest_fs, fuel0,
                                p);
                        rest = rest_fs;

                        while(is_prime(fst(f)))
                            invariant !forall(map(fst,cons(f,fs)),is_prime)
                                &*&    [fr]pratt_certificate(snd(f), 1,
                                        fuel0,fst(f))
                                &*&    [fr]pratt_certificate(
                                            pratt_cert(g, fs), rest,
                                            fuel0, p);
                            decreases length(fs);
                        {
                            switch(fs) {
                            case nil: assert false;
                            case cons(f0,fs0):
                                leak [fr]pratt_certificate(snd(f), 1,
                                        fuel0, fst(f));
                                open [fr]pratt_certificate(_,rest,
                                        fuel0, p);
                                assert[fr]pratt_certificate(snd(f0),
                                        _, ?fuel1, fst(f0));
                                pratt_certificate_raise_fuel(
                                        snd(f0), fuel1, fuel0);

                                pratt_certificate_raise_fuel(
                                        pratt_cert(g,fs0), fuel1,
                                        fuel0);
                                assert [fr]pratt_certificate(
                                        pratt_cert(g, fs0), ?rest1, fuel0,
                                        p);
                                rest = rest1;

                                f  = f0;
                                fs = fs0;
                            }
                        }

                        assert !is_prime(fst(f));

                        switch(f) {
                        case pair(q,qcert):
                            pratt_certificate_prime_inner(q, qcert,
                                    fuel0);
                            assert false;
                        }

                    }

                    assert false;

                }

                pratt_order_check_lemma(p,factorization,g);
                pratt_core_lemma(p,g);

                assert false;
            }
        }
    }
}

lemma_auto
void pratt_certificate_prime()
    requires [?f]pratt_certificate(?cert,1,?fl,?p);
    ensures  [ f]pratt_certificate(cert,1,fl,p)
        &*&  !!is_prime(p);
{
    if(!is_prime(p)) {
        pratt_certificate_prime_inner(p, cert,fl);
        assert false;
    }
}

lemma
pratt_cert pratt_certificate_build(int g,
        list<pair<int,pratt_cert> > factors, int q, int p)
    requires pratt_certificate(pratt_cert(g,factors),?rest,?fp,p)
        &*&  pratt_certificate(?qcert,1,?fq,q)
        &*&  rest%q == 0
        &*&  !!pratt_pow_thing(p,g,q);
    ensures  pratt_certificate(result, rest/q, _, p)
        &*& result == pratt_cert(g,cons(pair(q,qcert),factors));
{
    pratt_certificate_prime_inner(q,qcert,fq);
    assert !!is_prime(q);
    if(rest == 1) {
        division_unique(rest,q,0,1);
        assert false;
    }

    if(q >= p) {
        if(rest >= p || rest <= 0) {
            open pratt_certificate(pratt_cert(g,factors),_,_,p);
            assert p - 1
                == product(map(fst,factors))*rest;
            if(product(map(fst,factors)) <= 0) {
                my_mul_mono_l(product(map(fst,factors)),0,rest);
                assert false;
            }
            my_mul_mono_l(1,product(map(fst,factors)),rest);
            assert false;
        }
        assert rest < p;
        division_unique(rest,q,0,rest);
        assert false;
    }

    if(product(map(fst,factors))*rest != p-1 || g <= 1 || g >= p ||
            euclid_mod(pow_nat(g,nat_of_int(p-1)),p) != 1 || rest < 1 ||
            !forall(map(fst,factors),(pratt_pow_thing)(p,g))
            ) {
        open pratt_certificate(pratt_cert(g,factors),rest,fp,p);
        assert false;
    }

    assert pratt_certificate(pratt_cert(g,factors),rest,fp,p)
      &*&  pratt_certificate(qcert,1,fq,q);

    nat f = zero;

    while(int_of_nat(f) < max_of(int_of_nat(fq),int_of_nat(fp)))
        invariant int_of_nat(f) <= max_of(int_of_nat(fq),int_of_nat(fp));
        decreases max_of(int_of_nat(fq),int_of_nat(fp)) - int_of_nat(f);
    { f = succ(f); }

    pratt_certificate_raise_fuel(pratt_cert(g,factors),fp,f);
    pratt_certificate_raise_fuel(qcert,fq,f);

    div_rem(rest,q);
    assert rest == q*(rest/q);
    mul_3var(q,product(map(fst,factors)),rest/q);
    assert product(map(fst,cons(pair(q,qcert),factors)))*(rest/q)
        == (q*product(map(fst,factors)))*(rest/q);
    assert product(map(fst,cons(pair(q,qcert),factors)))*(rest/q)
        == (q*product(map(fst,factors)))*(rest/q);
    if(rest/q < 1) {
        my_mul_mono_r(q,rest/q,0);
        assert false;
    }
    close pratt_certificate(pratt_cert(g,cons(pair(q,qcert),factors)), rest/q, succ(f), p);
    return pratt_cert(g,cons(pair(q,qcert),factors));
}


//lemma_auto void fast_pow_mod_correct()
//    requires [?f]fast_pow_mod(?p,?x,?e_odd,?e_over_2,?e,?res);
//    ensures  [ f]fast_pow_mod( p, x, e_odd, e_over_2, e, res)
//        &*&  p > 1 &*& res == euclid_mod(pow_nat(x,e),p);
//{
//    if(p <= 1) {
//        open [f]fast_pow_mod(_,_,_,_,_,_);
//        assert false;
//    }
//
//    if(res != euclid_mod(pow_nat(x,e),p)) {
//        open [f]fast_pow_mod(_,_,_,_,_,_);
//        switch(e_over_2) {
//        case zero:
//        case succ(e_over_2_0):
//            assert [f]fast_pow_mod(p,x,int_of_nat(e_over_2)%2 == 1,
//                    nat_of_int(int_of_nat(e_over_2)/2), e_over_2, ?x_p_e_2);
//            fast_pow_mod_correct();
//            assert [f]let(euclid_mod(x_p_e_2*x_p_e_2,p), ?x_even);
//            assert nat_of_int(int_of_nat(e_over_2)
//                              +int_of_nat(e_over_2))
//                == nat_double(e_over_2);
//            pow_plus(x,e_over_2,int_of_nat(e_over_2));
//            assert pow_nat(x,e_over_2)*pow_nat(x,e_over_2)
//                == pow_nat(x,nat_double(e_over_2));
//            assert x_even
//                == euclid_mod(euclid_mod(pow_nat(x,e_over_2),p)
//                              *euclid_mod(pow_nat(x,e_over_2),p),
//                              p);
//            Zp_times(p,pow_nat(x,e_over_2),pow_nat(x,e_over_2));
//
//            if(e_odd) {
//                assert res == euclid_mod(x_even*x,p);
//                mul_3var(x_p_e_2,x_p_e_2,x);
//                assert res
//                    == euclid_mod(
//                            euclid_mod(pow_nat(x,e_over_2)*pow_nat(x,e_over_2),p)
//                            *x,p);
//                Zp_times(p,euclid_mod(pow_nat(x,e_over_2)*pow_nat(x,e_over_2),p),x);
//                Zp_times(p,pow_nat(x,e_over_2)*pow_nat(x,e_over_2),x);
//
//                assert false;
//            } else {
//                assert false;
//            }
//        }
//        assert false;
//    }
//}


lemma
void primes_below_step(int n)
    requires n >= 1;
    ensures  int_of_nat(nat_of_int(n)) == n
        &*&  int_of_nat(succ(nat_of_int(n))) == n+1
        &*&  is_prime(n+1)
        ==   all_no_divide(n+1,primes_below(nat_of_int(n)));
{
    ALREADY_PROVEN()
    prime_test(n+1);
    int_of_nat_of_int(n+1);
    assert nat_of_int(n+1) == succ(nat_of_int(n));

    if(forall(primes_below(nat_of_int(n)),(no_divide)(n+1)))  {
        if(!forall(primes_below(nat_of_int(n)),(nonfactor)(n+1))) {
            int cx = not_forall(primes_below(nat_of_int(n)),
                    (nonfactor)(n+1));
            forall_elim(primes_below(nat_of_int(n)),
                    (no_divide)(n+1), cx);
            assert false;
        }
    }

    if(forall(primes_below(nat_of_int(n)),(nonfactor)(n+1))) {
        if(!forall(primes_below(nat_of_int(n)),(no_divide)(n+1)))  {
            int cx = not_forall(primes_below(nat_of_int(n)),
                    (no_divide)(n+1));
            forall_elim(primes_below(nat_of_int(n)),
                    (nonfactor)(n+1), cx);
            assert false;
        }
    }
}

lemma_auto(is_prime(3))
void is_prime_3()
    requires true;
    ensures  !!is_prime(3);
{
    primes_below_step(2);
}

lemma void exp_by_sq(int p, int g, int e, int g_p_e)
    requires p > 1 &*& e >= 0
        &*&  g >= 0 &*& g < p
        &*&  g_p_e == euclid_mod(pow_nat(g,nat_of_int(e)),p);
    ensures  euclid_mod(pow_nat(g,nat_of_int(2*e)),p)
        ==   (g_p_e*g_p_e)%p
        &*&  euclid_mod(pow_nat(g,nat_of_int(2*e+1)),p)
        ==   (g*g_p_e*g_p_e)%p;
{
    ALREADY_PROVEN()
    if(!is_prime(2)) {
        assert false;
    }

    if(!is_prime(3)) {
        assert false;
    }

    int_of_nat_of_int(p);
    int_of_nat_of_int(p-1);
    int g_p_2e = euclid_mod(pow_nat(g,nat_of_int(2*e)),p);
    if(g_p_2e != (g_p_e*g_p_e)%p) {
        Zp_times(p,pow_nat(g,nat_of_int(e)),pow_nat(g,nat_of_int(e)));
        assert euclid_mod(g_p_e*g_p_e,p)
            == euclid_mod(pow_nat(g,nat_of_int(e))
                          *pow_nat(g,nat_of_int(e)),p);
        pow_times2(g,nat_of_int(e),2);
        assert euclid_mod(g_p_e*g_p_e,p)
            == euclid_mod(pow_nat(g,nat_of_int(2*e)),p);
        euclid_mod_correct(g_p_e*g_p_e,p);
        assert [_]euclid_div_sol(g_p_e*g_p_e,p,
                _,g_p_2e);

        my_mul_mono_l(0,g_p_e,g_p_e);
        assert false;
    }

    int g_p_2e_1 = euclid_mod(pow_nat(g,nat_of_int(2*e+1)),p);
    if(g_p_2e_1 != (g*g_p_e*g_p_e)%p) {
        mul_3var(g,g_p_e,g_p_e);
        mul_3var(g,pow_nat(g,nat_of_int(e)),pow_nat(g,nat_of_int(e)));
        Zp_times(p,pow_nat(g,nat_of_int(e)),pow_nat(g,nat_of_int(e)));
        Zp_times(p,g,pow_nat(g,nat_of_int(e))*pow_nat(g,nat_of_int(e)));
        Zp_times(p,g,g_p_e*g_p_e);

        pow_times2(g,nat_of_int(e),2);
        assert succ(nat_of_int(2*e))
            == nat_of_int(2*e + 1);
        euclid_mod_correct(g*g_p_e*g_p_e,p);

        my_mul_mono_l(0,g_p_e,g_p_e);
        my_mul_mono_l(0,g,g_p_e*g_p_e);
        assert false;
    }
}

lemma
void primes_below_sieve_v1(nat n)
    requires true;
    ensures  primes_below(nat_of_int(int_of_nat(n)*int_of_nat(n)))
        ==   append(
                filter((notf)(
                    (flip)(mem,
                        prod(mul,
                            reverse(primes_below(n)),
                            range(2,(int_of_nat(n)*int_of_nat(n)+1)/2+1)))),
                    reverse(range(int_of_nat(n)+1,
                                  int_of_nat(n)*int_of_nat(n)+1))),
                primes_below(n));
{
    ALREADY_PROVEN()
    int n_squared = int_of_nat(n)*int_of_nat(n);

    if(int_of_nat(n) > n_squared) {
        TRIVIAL_NAT(n)
        my_mul_mono_l(1,int_of_nat(n),int_of_nat(n));
        assert false;
    }

    fixpoint(int,bool) sieve_f =
        (notf)((flip)(mem,
                    prod(mul,
                        reverse(primes_below(n)),
                        range(2,(n_squared+1)/2 + 1))));

    for(nat m = n; int_of_nat(m) < int_of_nat(n)*int_of_nat(n);
                   m = succ(m))
        invariant int_of_nat(m) <= int_of_nat(n)*int_of_nat(n)
            &*&   int_of_nat(m) >= int_of_nat(n)
            &*&   primes_below(m)
            ==    append(
                    filter(sieve_f,
                        reverse(range(int_of_nat(n)+1,int_of_nat(m)+1))),
                    primes_below(n))
            ;
        decreases int_of_nat(n)*int_of_nat(n) - int_of_nat(m);
    {
        int p = int_of_nat(succ(m));

        assert filter(sieve_f,
                reverse(range(int_of_nat(n)+1,int_of_nat(succ(m))+1)))
            == filter(sieve_f,
                cons(int_of_nat(m)+1,
                    reverse(range(int_of_nat(n)+1,int_of_nat(m)+1))));

        if(!is_prime(p)) {
            assert primes_below(succ(m)) == primes_below(m);

            int f = findSmallFactor(p);

            div_rem(p,f);
            assert p == f*(p/f);

            if(f > int_of_nat(n)) {
                assert f*f <= p;
                assert p <= int_of_nat(m)+1;
                my_mul_strict_mono_l(int_of_nat(n),f,f);
                my_mul_strict_mono_r(int_of_nat(n),int_of_nat(n),f);
                assert false;
            }

            if(f < 2) {
                assert false;
            }

            if(p/f < 2) {
                my_mul_strict_mono_r(f,p/f,2);
                my_mul_mono_r(f,2,f);
                assert false;
            }

            if(p/f > (n_squared+1)/2) {
                div_rem(n_squared+1,2);
                assert f*(p/f) == p;
                assert p <= n_squared;
                assert p <= 2*((n_squared+1)/2) + (n_squared+1)%2;
                assert p <= 2*((n_squared+1)/2);
                assert p <  2*(p/f);
                my_mul_mono_l(2,f,p/f);

                assert false;
            }

            if(!mem(p/f,
                    range(2,(n_squared+1)/2 + 1))) {
                bounded_range(2,(n_squared+1)/2,p/f);
                assert false;
            }


            if(sieve_f(p)) {
                prod_correct(mul,reverse(primes_below(n)),
                        range(2,(n_squared+1)/2 + 1), f,
                        p/f);
                assert false;
            }

            assert primes_below(succ(m))
                ==    append(
                        filter(sieve_f,
                            reverse(range(int_of_nat(n)+1,
                                          int_of_nat(succ(m))+1))),
                        primes_below(n));
        } else {
            assert primes_below(succ(m)) == cons(p,primes_below(m));

            if(!sieve_f(p)) {
                pair<int,int> factors
                    = prod_exact(mul,reverse(primes_below(n)),
                        range(2,(n_squared+1)/2 + 1), p);
                switch(factors) {
                case pair(a,b):
                    assert a >= 2;
                    bounded_range(2,(n_squared+1)/2,b);
                    assert b >= 2;
                    assert a*b == p;
                    division_unique(p,a,b,0);
                    prime_no_factors(p,a);
                }
                assert false;
            }

            assert primes_below(succ(m))
                ==    append(
                        filter(sieve_f,
                            reverse(range(int_of_nat(n)+1,
                                          int_of_nat(succ(m))+1))),
                        primes_below(n));
        }
    }
}

lemma void multiples_from_map(nat n, int b, int x)
    requires true;
    ensures  multiples_from(n,b*x,x)
        ==   map((mul)(x),range(b+1,b+1+int_of_nat(n)));
{
    switch(n) {
    case zero:
    case succ(n0):
        multiples_from_map(n0,b+1,x);
    }
}

lemma void multiples_map(nat n, int x)
    requires true;
    ensures  multiples(n,x)
        ==   map((mul)(x),range(2,int_of_nat(n)+2));
{ multiples_from_map(n,1,x); }

lemma void multiples_prod(nat n, list<int> l)
    requires true;
    ensures  all_multiples(n,l)
        ==   prod(mul,l,range(2,int_of_nat(n)+2));
{
    switch(l) {
    case nil:
    case cons(x,xs):
        multiples_map(n,x);
        multiples_prod(n,xs);
    }
}

lemma
void primes_below_sieve_v2(nat n)
    requires true;
    ensures  primes_below(nat_of_int(int_of_nat(n)*int_of_nat(n)))
        ==   append(
                reverse(filter((notf)(
                    (flip)(mem,
                        all_multiples(nat_of_int(int_of_nat(n)*int_of_nat(n)),
                            reverse(primes_below(n))))),
                    range(int_of_nat(n)+1,
                                  int_of_nat(n)*int_of_nat(n)+1))),
                primes_below(n));
{
    ALREADY_PROVEN()
    primes_below_sieve_v1(n);
    filter_reverse(range(int_of_nat(n)+1,
                                  int_of_nat(n)*int_of_nat(n)+1),
            (notf)(
                    (flip)(mem,
                        all_multiples(nat_of_int(int_of_nat(n)*int_of_nat(n)),
                            reverse(primes_below(n))))));

    if(primes_below(nat_of_int(int_of_nat(n)*int_of_nat(n)))
        !=   append(
                filter((notf)(
                    (flip)(mem,
                        all_multiples(nat_of_int(int_of_nat(n)*int_of_nat(n)),
                            reverse(primes_below(n))))),
                    reverse(range(int_of_nat(n)+1,
                                  int_of_nat(n)*int_of_nat(n)+1))),
                primes_below(n))) {

        append_cancels(
            filter((notf)(
                (flip)(mem,
                    all_multiples(nat_of_int(int_of_nat(n)*int_of_nat(n)),
                        reverse(primes_below(n))))),
                reverse(range(int_of_nat(n)+1,
                                int_of_nat(n)*int_of_nat(n)+1))),
            filter((notf)(
                (flip)(mem,
                    prod(mul,
                        reverse(primes_below(n)),
                        range(2,(int_of_nat(n)*int_of_nat(n)+1)/2+1)))),
                reverse(range(int_of_nat(n)+1,
                                int_of_nat(n)*int_of_nat(n)+1))),

            primes_below(n));

        int cx = two_filters(
            reverse(range(int_of_nat(n)+1,
                    int_of_nat(n)*int_of_nat(n)+1)),

            (notf)(
                (flip)(mem,
                    all_multiples(nat_of_int(int_of_nat(n)*int_of_nat(n)),
                        reverse(primes_below(n))))),

            (notf)(
                (flip)(mem,
                    prod(mul,
                        reverse(primes_below(n)),
                        range(2,(int_of_nat(n)*int_of_nat(n)+1)/2+1)))));

        bounded_range(int_of_nat(n)+1, int_of_nat(n)*int_of_nat(n), cx);

        multiples_prod(nat_of_int(int_of_nat(n)*int_of_nat(n)),
                reverse(primes_below(n)));

        if(mem(cx,
                all_multiples(nat_of_int(int_of_nat(n)*int_of_nat(n)),
                    reverse(primes_below(n))))) {

            pair<int,int> factors = prod_exact(mul,
                    reverse(primes_below(n)),
                    range(2,int_of_nat(n)*int_of_nat(n)+2),
                    cx);

            switch(factors) {
            case pair(a,b):
                assert cx == a*b;
                assert a >= 2;

                bounded_range(2,int_of_nat(n)*int_of_nat(n)+1,b);

                assert b >= 2;
                assert cx <= int_of_nat(n)*int_of_nat(n);
                if(b > (int_of_nat(n)*int_of_nat(n)+1)/2) {
                    div_rem(int_of_nat(n)*int_of_nat(n)+1,2);
                    my_mul_strict_mono_r(a,
                            (int_of_nat(n)*int_of_nat(n)+1)/2, b);
                    assert a*b > a*((int_of_nat(n)*int_of_nat(n)+1)/2);
                    my_mul_mono_l(2,a,(int_of_nat(n)*int_of_nat(n)+1)/2);

                    assert false;
                }

                if(!mem(b,range(2,(int_of_nat(n)*int_of_nat(n)+1)/2+1))) {
                    if(2 <= (int_of_nat(n)*int_of_nat(n)+1)/2) {
                        bounded_range(2,(int_of_nat(n)*int_of_nat(n)+1)/2,b);
                    }
                    assert false;
                }

                prod_correct(mul,
                        reverse(primes_below(n)),
                        range(2,(int_of_nat(n)*int_of_nat(n)+1)/2+1),
                        a, b);
                assert false;
            }

        } else {
            assert !!mem(cx,
                    prod(mul,
                        reverse(primes_below(n)),
                        range(2,(int_of_nat(n)*int_of_nat(n)+1)/2+1)));

            pair<int,int> factors = prod_exact(mul,
                    reverse(primes_below(n)),
                    range(2,(int_of_nat(n)*int_of_nat(n)+1)/2+1),
                    cx);

            switch(factors) {
            case pair(a,b):
                assert cx == a*b;
                assert a >= 2;

                if(!bounded(2,(int_of_nat(n)*int_of_nat(n)+1)/2,b)) {
                    bounded_range(2,(int_of_nat(n)*int_of_nat(n)+1)/2,b);
                    assert false;
                }

                assert b >= 2;
                assert cx <= int_of_nat(n)*int_of_nat(n);
                assert b <= (int_of_nat(n)*int_of_nat(n)+1)/2;

                if(int_of_nat(n)*int_of_nat(n)+1 <
                        (int_of_nat(n)*int_of_nat(n)+1)/2) {
                    div_rem(int_of_nat(n)*int_of_nat(n)+1,2);
                    assert false;
                }

                assert b <= int_of_nat(n)*int_of_nat(n)+1;

                if(!mem(b,range(2,int_of_nat(n)*int_of_nat(n)+2))) {
                    bounded_range(2,int_of_nat(n)*int_of_nat(n)+1,b);
                    assert false;
                }

                prod_correct(mul,
                        reverse(primes_below(n)),
                        range(2,int_of_nat(n)*int_of_nat(n)+2),
                        a, b);

                assert false;
            }
        }

        assert false;
    }
}

lemma
void primes_below_fast_step(int lo, int hi, int m)
    requires lo >= m &*& lo <= hi &*& m >= 1 &*& hi <= m*m;
    //ensures  primes_below(nat_of_int(n+1))
    //    ==   (all_no_divide(n+1,reverse(primes_below(nat_of_int(m))))
    //         ? cons(n+1,primes_below(nat_of_int(n)))
    //         : primes_below(nat_of_int(n)));
    //ensures  all_no_divide(n+1,reverse(primes_below(nat_of_int(m))))
    ensures  primes_below(nat_of_int(hi))
        ==   append(
                filter((flip)(all_no_divide,primes_below(nat_of_int(m))),
                        reverse(range(lo+1,hi+1))),
                primes_below(nat_of_int(lo)));
{
    ALREADY_PROVEN()
    for(int i = lo; i < hi; ++i)
        invariant i >= lo &*& i <= hi
            &*&   primes_below(nat_of_int(i))
            ==    append(
                    filter((flip)(all_no_divide,primes_below(nat_of_int(m))),
                            reverse(range(lo+1,i+1))),
                    primes_below(nat_of_int(lo)));
        decreases hi-i;
    {
        note_eq(reverse(range(lo+1,i+2)),
                cons(i+1,reverse(range(lo+1,i+1))));
        prime_no_divide_sqrt(nat_of_int(m), i+1);
        assert nat_of_int(i+1) == succ(nat_of_int(i));
    }
}

lemma_auto(primes_below(N16))
void primes_below_16()
    requires true;
    ensures  primes_below(N16) == {13,11,7,5,3,2};
{
    ALREADY_PROVEN()
    primes_below_step(2);
    note_eq(reverse(primes_below(N2)),{2});
    primes_below_fast_step(2,4,2);
    note_eq(reverse(primes_below(N4)),{2,3});
    primes_below_fast_step(4,16,4);
}

lemma_auto(primes_below(N16))
void primes_below_16_correct()
    requires true;
    ensures  !!forall(primes_below(N16),is_prime);
{ primes_below_correct(N16); }



lemma
void primes_below_32()
    requires true;
    ensures  primes_below(nat_of_int(32)) == {31,29,23,19,17,13,11,7,5,3,2};
{
    ALREADY_PROVEN()
    primes_below_fast_step(16,32,16);
}

lemma
void primes_below_48()
    requires true;
    ensures  primes_below(nat_of_int(48))
        == append({47,43,41,37},primes_below(nat_of_int(32)));
{
    ALREADY_PROVEN()
    primes_below_fast_step(32,48,16);
}

// 65 because apparently verifast overworks itself when it encounters
// nat_of_int(64)
lemma
void primes_below_65()
    requires true;
    ensures  primes_below(nat_of_int(65))
        == append({61,59,53},primes_below(nat_of_int(48)));
{
    ALREADY_PROVEN()
    primes_below_fast_step(48,65,16);
}

lemma
void primes_below_80()
    requires true;
    ensures  primes_below(nat_of_int(80))
        == append({79,73,71,67},primes_below(nat_of_int(65)));
{
    ALREADY_PROVEN()
    primes_below_fast_step(65,80,16);
}

lemma
void primes_below_96()
    requires true;
    ensures  primes_below(nat_of_int(96))
        ==   append({89,83},primes_below(nat_of_int(80)));
{
    ALREADY_PROVEN()
    primes_below_fast_step(80,96,16);
}

lemma_auto
void primes_below_100()
    requires true;
    ensures  primes_below(nat_of_int(100)) == {97,89,83,79,73,71,67,61,59,53,47,43,41,37,31,29,23,19,17,13,11,7,5,3,2};
{
    ALREADY_PROVEN()

    primes_below_32();
    primes_below_48();
    primes_below_65();
    primes_below_80();
    primes_below_96();
    primes_below_fast_step(96,100,16);
}

lemma void modpow2_correct(int p, int g, nat bits)
    requires p > 1 &*& g >= 0;
    ensures  modpow2(p,g,bits)
        ==   euclid_mod(pow_nat(g%p,
                            nat_of_int(pow_nat(2,bits))),
                        p);
{
    switch(bits) {
    case zero:
        euclid_mod_nonneg_auto(g, p);

    case succ(bits0):
        modpow2_correct(p,g,bits0);
        div_rem(g,p);
        mod_sign(g,p);
        exp_by_sq(p,g%p,pow_nat(2,bits0),modpow2(p,g,bits0));
    }
}

lemma void modpow_correct_general(int p, int g, int e, nat bits)
    requires p > 1 &*& g >= 0 &*& e >= 0;
    ensures  modpow(p,g,e,bits)
        ==   euclid_mod(pow_nat(g,nat_of_int(e%pow_nat(2,bits))),p);
{
    switch(bits) {
    case zero:
        assert pow_nat(2,bits) == 1;
        division_unique(e,1,e,0);
    case succ(bits0):
        modpow2_correct(p,g,bits0);
        modpow_correct_general(p,g,e,bits0);

        int shift = pow_nat(2,bits0);
        int shifted = e/shift;
        div_rem(e,shift);
        div_sign(e,shift);
        div_rem(shifted,2);
        div_sign(shifted,2);
        assert e == shift*shifted + e%shift;
        note_eq(e ,  shift*(2*(shifted/2) + shifted%2) + e%shift);

        mul_3var(shift,2,shifted/2);
        assert e == (2*shift)*(shifted/2) + shift*(shifted%2) + e%shift;

        mod_sign(shifted,2);
        mod_sign(e,shift);
        assert shifted%2 >= 0;
        assert shifted%2 <= 1;
        my_mul_mono_r(shift,shifted%2,1);
        my_mul_mono_r(shift,0,shifted%2);
        assert shift*2 == 2*shift;
        assert e%shift >= 0;
        assert e%shift < shift;
        assert shift*(shifted%2) + e%shift < 2*shift;
        assert shift*(shifted%2) + e%shift >= 0;

        assert 2*(shifted/2) >= 0;
        assert 2*(shifted/2) <= shifted;
        my_mul_mono_l(0,shift,2*(shifted/2));
        assert shift*(2*(shifted/2)) >= 0;
        assert shift*(2*(shifted/2)) <= e;

        division_unique(e,2*shift,shifted/2,
                shift*(shifted%2)+e%shift);

        assert modpow(p,g,e,bits0)
            == euclid_mod(pow_nat(g, nat_of_int(e%shift)),
                          p);
        assert modpow2(p,g,bits0)
            == euclid_mod(pow_nat(g%p, nat_of_int(shift)),
                          p);

        euclid_mod_nonneg_auto(g,p);
        Zp_pow(p,g,nat_of_int(shift));
        assert modpow2(p,g,bits0)
            == euclid_mod(pow_nat(g, nat_of_int(shift)),
                          p);


        if(shifted%2 == 1) {

            assert modpow(p,g,e,bits)
                == (euclid_mod(pow_nat(g, nat_of_int(shift)),p)
                    *euclid_mod(pow_nat(g, nat_of_int(e%shift)), p))%p;

            my_mul_mono_l(0,
                euclid_mod(pow_nat(g, nat_of_int(shift)),p),
                euclid_mod(pow_nat(g, nat_of_int(e%shift)),p));

            euclid_mod_nonneg_auto(
                euclid_mod(pow_nat(g, nat_of_int(shift)),p)
                    *euclid_mod(pow_nat(g, nat_of_int(e%shift)), p),
                p);

            assert modpow(p,g,e,bits)
                == euclid_mod((euclid_mod(pow_nat(g, nat_of_int(shift)),p)
                    *euclid_mod(pow_nat(g, nat_of_int(e%shift)), p)),p);

            Zp_times(p,pow_nat(g,nat_of_int(shift)),
                    pow_nat(g,nat_of_int(e%shift)));

            assert modpow(p,g,e,bits)
                == euclid_mod((pow_nat(g, nat_of_int(shift))
                    *pow_nat(g, nat_of_int(e%shift))),p);

            pow_plus(g,nat_of_int(shift),e%shift);
            assert modpow(p,g,e,bits)
                == euclid_mod(pow_nat(g, nat_of_int(shift + e%shift)),p);

            assert modpow(p,g,e,bits)
                == euclid_mod(pow_nat(g, nat_of_int(e%(2*shift))),p);

        } else {
            if(shifted%2 >= 1) { assert false; }
            if(shifted%2 < 0) { assert false; }
            assert shifted%2 == 0;

            division_unique(e,2*shift,shifted/2,e%shift);
            assert modpow(p,g,e,bits)
                == modpow(p,g,e,bits0)%p;
            assert modpow(p,g,e,bits)
                == euclid_mod(pow_nat(g, nat_of_int(e%shift)),p)%p;
            euclid_mod_nonneg_auto(
                euclid_mod(pow_nat(g, nat_of_int(e%shift)),p),
                p);
            assert modpow(p,g,e,bits)
                == euclid_mod(pow_nat(g, nat_of_int(e%(2*shift))),p);
        }
    }
}

lemma void modpow_correct(int p, int g, int e, nat bits)
    requires p > 1 &*& g >= 0 &*& pow_nat(2,bits) > e &*& e >= 0;
    ensures  modpow(p,g,e,bits) == euclid_mod(pow_nat(g,nat_of_int(e)),p);
{
    division_unique(e,pow_nat(2,bits),0,e);
    modpow_correct_general(p,g,e,bits);
}

lemma void modpow2_step(int p, int g, nat bits, int acc)
    requires p > 1 &*& acc == modpow2(p,g,bits);
    ensures  modpow2(p,g,succ(bits))
        ==  (acc*acc)%p;
{}

lemma void modpow_step(int p, int g, int e, nat bits0, int acc, int pow2,
        int sofar)
    requires p > 1 &*& g >= 0 &*& acc == modpow2(p,g,bits0) &*& e >= 0
        &*&  pow2 == pow_nat(2,bits0)
        &*&  sofar == modpow(p,g,e,bits0);
    ensures  modpow2(p,g,succ(bits0)) == (acc*acc)%p
        &*&  (e/pow2)%2 != 0
        ?    modpow(p,g,e,succ(bits0)) == (acc*sofar)%p
        :    modpow(p,g,e,succ(bits0)) == sofar
        ;
{
    modpow_correct_general(p,g,e,bits0);
    modpow_correct_general(p,g,e,succ(bits0));
    division_unique(p,p,1,0);

    if((e/pow2)%2 != 0) {
        assert modpow(p,g,e,succ(bits0))
            == (acc*sofar)%p;
    } else {
        assert modpow(p,g,e,succ(bits0))
            == (1*sofar)%p;
        assert sofar == euclid_mod(pow_nat(g,nat_of_int(e%pow2)),p);
        assert sofar == pow_nat(g,nat_of_int(e%pow2))%p;
        mod_twice(pow_nat(g,nat_of_int(e%pow2)),p,p);
    }
}

lemma void modpow_step_by_2_inner(int p, int g, int e, nat bits0, int acc, int pow2,
        int sofar)
    requires p > 1 &*& g >= 0 &*& acc == modpow2(p,g,bits0) &*& e >= 0
        &*&  pow2 == pow_nat(2,bits0)
        &*&  sofar == modpow(p,g,e,bits0)
        &*&  let((acc*acc)%p,?acc1);
    ensures  modpow2(p,g,succ(succ(bits0))) == (acc1*acc1)%p
        &*&  (e/pow2)%2 != 0
        ?    ((e/(2*pow2))%2 != 0
             ? modpow(p,g,e,succ(succ(bits0))) == (acc1*((acc*sofar)%p))%p
             : modpow(p,g,e,succ(succ(bits0))) == (acc*sofar)%p
             )
        :    ((e/(2*pow2))%2 != 0
             ? modpow(p,g,e,succ(succ(bits0))) == (acc1*sofar)%p
             : modpow(p,g,e,succ(succ(bits0))) == sofar
             )
        ;
{
    modpow_step(p,g,e,bits0,acc,pow2,sofar);
    int next_sofar = sofar;
    note_eq(acc1,(acc*acc)%p);

    if((e/pow2)%2 != 0) {
        modpow_step(p,g,e,succ(bits0),(acc*acc)%p,2*pow2,(acc*sofar)%p);
        if((e/(2*pow2))%2 != 0) {
            if(modpow(p,g,e,succ(succ(bits0))) !=
                (acc1*((acc*sofar)%p))%p) { assert false; }
        } else {
            if(modpow(p,g,e,succ(succ(bits0))) !=
                (acc*sofar)%p) { assert false; }
        }
    } else {
        modpow_step(p,g,e,succ(bits0),(acc*acc)%p,2*pow2,sofar);
        if((e/(2*pow2))%2 != 0) {
            if(modpow(p,g,e,succ(succ(bits0))) !=
                (acc1*sofar)%p) { assert false; }
        } else {
            if(modpow(p,g,e,succ(succ(bits0))) !=
                sofar) { assert false; }
        }
    }
}

lemma void modpowp_correct(int p, int g, int e, nat bits)
    requires modpowp(p,g,e,bits,_,?p2,?x)
        &*&  p2 > e;
    ensures  x == euclid_mod(pow_nat(g,nat_of_int(e)),p);
{
    open modpowp(_,_,_,_,_,_,_);
    modpow_correct(p,g,e,bits);
}

lemma void modpow_step_by_2(int p, int g, int e, nat bits0, int acc, int pow2, int sofar)
    requires modpowp(p,g,e,bits0,acc,pow2,sofar);
    ensures  (e/pow2)%2 != 0
        ?    ((e/(2*pow2))%2 != 0
             ? modpowp(p, g, e, succ(succ(bits0)),
                 (((acc*acc)%p)*((acc*acc)%p))%p,
                 4*pow2,
                 (((acc*acc)%p)*((acc*sofar)%p))%p)
             : modpowp(p, g, e, succ(succ(bits0)),
                 (((acc*acc)%p)*((acc*acc)%p))%p,
                 4*pow2,
                 (acc*sofar)%p)
             )
        :    ((e/(2*pow2))%2 != 0
             ? modpowp(p,g,e,succ(succ(bits0)),
                 (((acc*acc)%p)*((acc*acc)%p))%p,
                 4*pow2,
                 (((acc*acc)%p)*sofar)%p)
             : modpowp(p,g,e,succ(succ(bits0)),
                 (((acc*acc)%p)*((acc*acc)%p))%p,
                 4*pow2,
                 sofar)
             )
        ;
{
    open modpowp(p,g,e,bits0,acc,pow2,sofar);
    modpow_step_by_2_inner(p,g,e,bits0,acc,pow2,sofar);
    if((e/pow2)%2 != 0) { sofar = (acc*sofar)%p; }
    pow2 = 2*pow2; bits0 = succ(bits0); acc = (acc*acc)%p;
    if((e/pow2)%2 != 0) { sofar = (acc*sofar)%p; }
    pow2 = 2*pow2; bits0 = succ(bits0); acc = (acc*acc)%p;
    close modpowp(p,g,e,bits0,acc,pow2,sofar);
}



@*/

