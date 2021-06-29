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

lemma void multiples_len(nat p_minus_1, int x)
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
            nat_of_int_of_nat(p_minus_1);
            assert false;
        }
        assert int_of_nat(i) < int_of_nat(p_minus_1);
        assert int_of_nat(succ(i)) == 1+int_of_nat(i);
    }

}

lemma void multiples_bounded(nat p_minus_1, int x)
    requires true;
    ensures  !!forall(multiples_mod_p(p_minus_1,x),
                (bounded)(1,int_of_nat(p_minus_1)));
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
            nat_of_int_of_nat(p_minus_1);
            assert false;
        }
        assert int_of_nat(i) < int_of_nat(p_minus_1);
        assert int_of_nat(succ(i)) == 1+int_of_nat(i);
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
            nat_of_int_of_nat(p_minus_1);
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
            nat_of_int_of_nat(p_minus_1);
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

lemma int multiples_hits_each_thing(nat p_minus_1, int p, int x, int v)
    requires 1 <= v &*& v <= int_of_nat(p_minus_1)
        &*&  int_of_nat(succ(p_minus_1)) == p
        &*&  gcd(abs(x),p) == 1
        &*&  !!is_prime(p);
    ensures  !!mem(pair(result,v),multiples_mod_p(p_minus_1,x));
{

}

fixpoint list<int> one_through_n(nat n) {
    switch(n) {
    case zero:
        return nil;
    case succ(n0):
        return cons(int_of_nat(n),one_through_n(n0));
    }
}

lemma void product_one_through_n_is_factorial(nat n)
    requires true;
    ensures  product(one_through_n(n)) == factorial(n);
{
}

lemma void multiples_hits_everything(nat p_minus_1, int p, int x, int v)
    requires 1 <= v &*& v <= int_of_nat(p_minus_1)
        &*&  int_of_nat(succ(p_minus_1)) == p
        &*&  gcd(abs(x),p) == 1
        &*&  !!is_prime(p);
    ensures  !!is_permutation(map(snd,multiples_mod_p(p_minus_1,x)),
                              one_through_n(p_minus_1));
{}


lemma void multiples_product(nat p_minus_1, int p, int x)
    requires int_of_nat(succ(p_minus_1)) == p
        &*&  gcd(abs(x),p) == 1
        &*&  !!is_prime(p);
    ensures  product(map(snd,multiples_mod_p(p_minus_1,x)))
        ==   factorial(p_minus_1)*pow_nat(x,p_minus_1);
{}

// "proof as a particular case of Euler's theorem" found on wikipedia,
// attributed to James Ivory and supposedly rediscovered by Dirichlet
lemma void fermat_little(int p, int x)
    requires !!is_prime(p) &*& euclid_mod(x,p) != 0;
    ensures  euclid_mod(pow_nat(x,nat_of_int(p-1)),p) == 1;
{

}

lemma void order_mod_n_bounded(int n, int x, nat o)
    requires n > 1 &*&  order_mod_n(n,x) == some(o);
    ensures  0 < int_of_nat(o) &*& int_of_nat(o) < n;
{

}

lemma void order_mod_n_correct(int n, int x)
    requires n > 1;
    ensures  switch(order_mod_n(n,x)) {
        case none: return gcd(x,n) != 1;
        case some(o):
            return  gcd(x,n) == 1
                &*& euclid_mod(pow_nat(x,o), n) == 1;
    };
{

}

lemma void order_mod_n_minimal(int n, int x, nat o)
    requires n > 1 &*& euclid_mod(pow_nat(x,o), n) == 1;
    ensures  switch(order_mod_n(n,x)) {
        case none: return false;
        case some(my_o):
            return  int_of_nat(my_o) >= int_of_nat(o);
    };
{

}

lemma int orders_mod_n_divides(int n, int x, nat o1, nat o2)
    requires n > 1
        &*&  euclid_mod(pow_nat(x,o1), n) == 1
        &*&  euclid_mod(pow_nat(x,o2), n) == 1
        &*&  int_of_nat(o1) <= int_of_nat(o2);
    ensures  int_of_nat(o1)*result == int_of_nat(o2);
{

}

lemma void pratt_core_lemma(int p, int x)
    requires p > 1 &*& x > 1
        &*&  order_mod_n(p,x) == some(nat_of_int(p-1));
    ensures  !!is_prime(p);
{

}

@*/

