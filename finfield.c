/*@ #include "finfield.gh" @*/

/*@

lemma void Zp_plus(int p, int a, int b)
    requires p > 0;
    ensures  euclid_mod(a+b,p)
        ==   euclid_mod(euclid_mod(a,p)+euclid_mod(b,p),p);
{
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

lemma void Zp_pow(int p, int a, nat n)
    requires p > 0;
    ensures  euclid_mod(pow_nat(a,n),p)
        ==   euclid_mod(pow_nat(euclid_mod(a,p),n),p);
{
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
        if(is_prime(p)) {
            prime_divides_product(p,j-i,abs(x));
            if((j-i)%p == 0) {
                gcd_is_max_divisor(p,j-i,p);
            } else  {
                gcd_is_max_divisor(p,abs(x),p);
            }
            assert false;
        } else {
            int f = findFactor(p);
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
    multiples_correct(p_minus_1,p,g,i,x);
    multiples_correct(p_minus_1,p,g,j,x);
    note_eq( euclid_mod(i*g,p) ,  euclid_mod(j*g,p));
    Zp_diff_zero(p,j*g,i*g);
    assert euclid_mod((j-i)*g,p) == 0;
    Zp_prod_zero(p,j-i,g);
    if(i != j) {
        euclid_mod_correct(j-i,p);
        assert [_] euclid_div_sol((j-i),p,?q,0);
        if(q < 0) {
            my_mul_strict_mono_r(p,q,0);
            assert false;
        }
        my_mul_mono_r(p,1,q);
        assert false;
    }
}

lemma s find_fst<s,t>(list<pair<s,t> > l, t x)
    requires !!mem(x,map(snd,l));
    ensures  !!mem(pair(result,x),l);
{
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
            assert factorial(p_minus_1)%p != 0;
            if(euclid_mod(factorial(p_minus_1),p) == 0) {
                euclid_mod_correct(factorial(p_minus_1),p);
                assert [_] euclid_div_sol(factorial(p_minus_1),p,?q,0);
                division_unique(factorial(p_minus_1),p,q,0);
                assert false;
            }
            assert false;
        }
    }
}

lemma void order_mod_n_bounded(int n, int x, nat o)
    requires n > 1 &*&  order_mod_n(n,x) == some(o);
    ensures  0 < int_of_nat(o) &*& int_of_nat(o) < n;
{
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

lemma void order_mod_n_correct(int n, int x)
    requires n > 1 &*& x >= 1;
    ensures  switch(order_mod_n(n,x)) {
        case none:
            //return gcd(x,n) != 1;
            return euclid_mod(x,n) == 0 || !is_prime(n);
        case some(o):
            return  gcd(x,n) == 1
                &*& euclid_mod(pow_nat(x,o), n) == 1;
    };
{
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

//lemma void order_mod_n_minimal(int n, int x, nat o)
//    requires n > 1 &*& euclid_mod(pow_nat(x,o), n) == 1;
//    ensures  switch(order_mod_n(n,x)) {
//        case none: return false;
//        case some(my_o):
//            return  int_of_nat(my_o) >= int_of_nat(o);
//    };
//{
//
//}

//lemma int orders_mod_n_divides(int n, int x, nat o1, nat o2)
//    requires n > 1
//        &*&  order_mod_n(n,x) == some(o1)
//        &*&  euclid_mod(pow_nat(x,o2), n) == 1;
//    ensures  int_of_nat(o1) <= int_of_nat(o2)
//        &*&  result*int_of_nat(o1) == int_of_nat(o2);
//{
//
//}
//
//lemma void pratt_core_lemma(int p, int x)
//    requires p > 1 &*& x > 1
//        &*&  order_mod_n(p,x) == some(nat_of_int(p-1));
//    ensures  !!is_prime(p);
//{
//
//}

@*/

