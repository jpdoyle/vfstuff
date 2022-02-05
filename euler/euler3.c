#include <stdio.h>
#include <stdlib.h>

#include "../numtheo.h"
/*@ #include "../sorting.gh" @*/

/*@

predicate prime_factorization(int x, list<int> l;) =
    x >= 1 &*& !!forall(l,is_prime) &*& x == product(l);

lemma list<int> factorize(int x)
    requires x > 0;
    ensures  prime_factorization(x,result);
{
    int orig_x = x;
    int factor = 1;
    list<int> ret = {};
    while(x > 1)
        invariant prime_factorization(factor,ret)
            &*&   x >= 1 &*& factor >= 1 &*& factor*x == orig_x;
        decreases x;
    {
        int q = x; if(!is_prime(q)) { q = findFactor(x); }
        division_unique(x,x,1,0);
        my_mul_mono_l(1,q,factor);
        div_rem(x,q);
        div_sign(x,q);
        open prime_factorization(factor,ret);
        close prime_factorization(q*factor,cons(q,ret));

        assert orig_x == factor*x;
        assert orig_x == factor*(q*(x/q));
        mul_assoc(factor,q,x/q); mul_commutes(q,factor);
        assert orig_x == (q*factor)*(x/q);

        if(x/q >= x) {
            my_mul_mono_l(2,q,x/q); my_mul_mono_r(q,x,x/q);
            assert false;
        }

        x /= q;
        factor *= q;
        ret = cons(q,ret);

    }
    return ret;
}

  @*/

size_t largest_prime_factor(size_t n)
    /*@ requires n > 1
            &*&  (n+1)*sizeof(size_t) <= ULLONG_MAX
            ; @*/
    /*@ ensures  prime_factorization(n,?l) &*& result == maximum(l);
      @*/
    /*@ terminates; @*/
{
    size_t i;
    size_t sqrt_n;
    size_t* primes;
    size_t n_primes;
    size_t max_factor = 1;
    size_t max_prime = 1;

    sqrt_n = int_sqrt(n);
    /*@ {
        if(sqrt_n+1 > n+1) {
            assert sqrt_n+1 > sqrt_n*sqrt_n+1;
            my_mul_mono_l(1,sqrt_n,sqrt_n);
            assert false;
        }
        my_mul_mono_l(sqrt_n+1,n+1,sizeof(size_t));
    } @*/
    primes = malloc((sqrt_n+1)*sizeof(size_t));
    if(!primes) { abort(); }

    n_primes = prime_sieve(primes,sqrt_n+1);

    /*@ int orig_n = n; @*/
    i = 0;
    /*@ close prime_factorization(max_factor,{}); @*/

    while(i < n_primes && n > 1)
        /*@ invariant i >= 0 &*& i <= n_primes
                &*&   primes[..i] |-> ?pref
                &*&   primes[i..n_primes] |-> ?suff
                &*&   !!sorted(suff)
                &*&   append(pref,suff)
                    == reverse(primes_below(noi(sqrt_n)))
                &*&   max_factor*n == orig_n
                &*&   prime_factorization(max_factor,?ps)
                &*&   max_prime == maximum(cons(1,ps))
                &*&   n == orig_n || (ps != nil && max_prime != 1)
                &*&   !!forall(ps,(flip)(all_ge)(suff))
                &*&   !!subset(ps,append(pref,suff))
                &*&   n >= 1
                //&*&   n == 1 || n >= max_prime
                &*&   max_factor >= 1
                &*&   n == 1 || !!forall(pref,(nonfactor)(n))
                ; @*/
        /*@ decreases length(suff)+n; @*/
    {
        /*@ open ullongs(primes+i,_,_); @*/
        size_t p = primes[i];
        /*@ assert !!mem(p,reverse(primes_below(noi(sqrt_n))));
          @*/
        if(n%p == 0) {
            /*@ {
                div_rem(n,p); div_sign(n,p);
                mul_mono_l(1,max_factor,p);
                assert max_factor*n == orig_n;
                mul_assoc(max_factor,p,n/p);
                assert max_factor*p*(n/p) == orig_n;
                factor_bound(p,n/p);
                factor_bound(max_factor*p,n/p);
                assert n/p >= 1;
                assert max_factor*p <= orig_n;
                open prime_factorization(_,ps);
                close prime_factorization(max_factor*p,cons(p,ps));

                if(p != maximum(cons(1,cons(p,ps)))) {
                    assert maximum(cons(1,ps)) == max_prime;
                    assert max_prime > 1;
                    maximum_correct(p,cons(1,cons(p,ps)));
                    assert max_prime == maximum(cons(1,cons(p,ps)));
                    forall_elim(ps,(flip)(all_ge)(suff),max_prime);
                    assert max_prime <= p;
                    assert false;
                }

                if(n/p == 0) { assert false; }

                assert n != 1;
                if(n/p != 1 && !forall(pref,(nonfactor)(n/p))) {
                    int cx = not_forall(pref,(nonfactor)(n/p));
                    forall_elim(pref,(nonfactor)(n),cx);
                    forall_elim(pref,(nonfactor)(n),cx);
                    primes_below_correct(noi(sqrt_n));
                    disjoint_append(pref,suff);
                    sorted_append(pref,suff);
                    forall_elim(pref,(notf)((flip)(mem,suff)),cx);
                    forall_elim(pref,(flip)(all_ge)(suff),cx);
                    assert cx < p;
                    assert n%cx != 0 &*& cx%n != 0;

                    factor_bound(p,n/p);
                    assert abs(p) == p; assert abs(n/p) == n/p;
                    if(n == p) {
                        division_unique(n,p,1,0); assert false;
                    }

                    assert !!mem(cx,append(pref,suff));
                    forall_elim(primes_below(noi(sqrt_n)),
                        is_prime,cx);

                    if(cx == n/p) { division_unique(n,cx,p,0); assert false; }

                    division_unique(p,n,0,p);
                    assert p%n != 0;
                    if(cx%(n/p) == 0) {
                        div_rem(cx,n/p); div_sign(cx,n/p);
                        factor_bound(n/p,cx/(n/p));
                        assert n/p <= cx; assert n/p < cx;
                        int q = n/p;
                        division_unique(n/p,n/p,1,0);
                        if(!is_prime(q)) { q = findFactor(n/p); }
                        primes_below_complete(q,noi(sqrt_n));
                        assert !!mem(q,append(pref,suff));
                        if(mem(q,suff)) {
                            sorted_append(pref,suff);
                            forall_elim(pref,(flip)(all_ge)(suff),cx);
                            forall_elim(suff,(le)(cx),q);
                            assert false;
                        }
                        assert !!mem(q,pref);
                        div_rem(n/p,q); assert n/p == q*((n/p)/q);
                        mul_assoc(q,p,(n/p)/q); mul_commutes(p,q);
                        mul_assoc(p,q,(n/p)/q);
                        division_unique(n,q,p*((n/p)/q),0);
                        assert n%q == 0;
                        forall_elim(pref,(nonfactor)(n),q);
                        assert false;
                    }

                    assert (n/p)%cx == 0;
                    div_rem(n/p,cx); assert n/p == cx*((n/p)/cx);
                    div_rem(n,p); assert n == p*(n/p);
                    mul_assoc(p,cx,(n/p)/cx); mul_commutes(p,cx);
                    mul_assoc(cx,p,(n/p)/cx);
                    division_unique(n,cx,p*((n/p)/cx),0);

                    assert false;
                }
                factor_bound(p,n/p);
                if(n/p >= n) {
                    my_mul_mono_l(2,p,n); my_mul_mono_r(p,n,n/p);
                    assert false;
                }
            } @*/

            max_factor *= p;
            max_prime = p;
            n /= p;

        } else {
            /*@ {
                close ullongs(primes+i,1,_);
                ullongs_join(primes);
                assert primes[i+1..n_primes] |-> ?new_suff;
                if(!forall(ps,(flip)(all_ge)(new_suff))) {
                    int cx = not_forall(ps,(flip)(all_ge)(new_suff));
                    forall_elim(ps,(flip)(all_ge)(suff),cx);
                    assert false;
                }

                if(n != 1) {
                    if(p%n == 0) {
                        prime_no_factors(p,n);
                        assert false;
                    }

                    assert !!nonfactor(n,p);
                    forall_append(pref,{p},(nonfactor)(n));
                }

            } @*/
            ++i;
        }
    }

    /*@ ullongs_join(primes); @*/
    /*@ ullongs_join(primes); @*/
    free(primes);

    if(n == 1) {
        /*@ {
            assert orig_n != 1;
            assert orig_n == max_factor*n;
            assert max_factor > 1;
            assert prime_factorization(orig_n,?factors);
            maximum_correct(1,cons(1,factors));
            TRIVIAL_LIST(factors)
            assert !!mem(max_prime,factors);
            assert max_prime == maximum(cons(1,factors));
            assert max_prime > 1;
            assert maximum(cons(1,factors)) == maximum(factors);
        } @*/
        return max_prime;
    }
    /*@ {
        assert suff == {};
        assert pref == reverse(primes_below(noi(sqrt_n)));
        if(n <= sqrt_n) {
            int q = n; if(!is_prime(q)) { q = findFactor(q); }
            primes_below_complete(q,noi(sqrt_n));
            forall_elim(pref,(nonfactor)(n),q);
            assert false;
        }
        if(!is_prime(n)) {
            factor_bound(max_factor,n);
            prime_test_sqrt(n,noi(sqrt_n));
            forall_reverse(primes_below(noi(sqrt_n)),(nonfactor)(n));
            assert false;
        }
        assert !!is_prime(n);
        open prime_factorization(max_factor,?factors);
        close prime_factorization(orig_n,cons(n,factors));
        maximum_correct(n,cons(n,factors));
        int final_max = maximum(cons(n,factors));
        if(final_max != n) {
            assert !!mem(final_max,factors);
            primes_below_correct(noi(sqrt_n));
            forall_elim(factors,(contains)(append(pref,suff)),final_max);
            forall_elim(primes_below(noi(sqrt_n)),
                (bounded)(2,sqrt_n),final_max);
            assert false;
        }
    } @*/
    return n;
}

int main() /*@ : main @*/
    /*@ requires true; @*/
    /*@ ensures  true; @*/
{
    size_t target;
    size_t ret;
    unsigned trunc;
#ifndef __FILE__
    target = 600851475143;
#else
    scanf("%llu",&target);
    do {
#endif
    ret = largest_prime_factor(target);
    /*@ assert prime_factorization(target,?l)
            &*&  ret == maximum(l); @*/
    /*@ open prime_factorization(target,l); @*/
#ifndef __FILE__
    trunc = /*@ truncating @*/ (unsigned)ret;
    /*@ u_integer_limits(&trunc); @*/

    if((size_t)trunc != ret) {
        printf("600851475143\n");
    } else {
        printf("%u\n",trunc);
    }
#else
    printf("%llu\n",ret);
    target /= ret;
    } while(target > 1);
#endif
    return 0;
}

