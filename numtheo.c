#include "numtheo.h"
/*@ #include "lists.gh" @*/
/*@ #include <arrays.gh> @*/


/*@

lemma_auto(indices_of_inner(v,l,b))
void indices_of_length<t>(t v, list<t> l, int b)
    requires true;
    ensures  length(indices_of_inner(v,l,b)) <= length(l);
{ LIST_INDUCTION(l, xs, indices_of_length(v,xs,b+1)) }

lemma void ge_than_primes_length_nat(int i, nat n)
    requires true;
    ensures  length(filter((ge_than)(i), primes_below(n)))
        <=   max_of(0,int_of_nat(n)+1-i);
{ NAT_INDUCTION(n,n0, ge_than_primes_length_nat(i,n0)) }

lemma_auto(filter((ge_than)(i),
            primes_below(nat_of_int(n))))
void ge_than_primes_length(int i, int n)
    requires n >= 0;
    ensures  length(filter((ge_than)(i), primes_below(nat_of_int(n))))
        <=   max_of(0,n+1-i);
{ ge_than_primes_length_nat(i,nat_of_int(n)); }


  @*/

size_t euclid_gcd(size_t a,size_t b)
    /*@ requires a > 0 &*& b > 0; @*/
    /*@ ensures  result == gcd(a,b); @*/
    /*@ terminates; @*/
{
    /*@ int orig_a = a; @*/
    /*@ int orig_b = b; @*/

    if(a < b) {
        size_t tmp = b;
        b = a;
        a = tmp;
    }

    while(a%b != 0)
        /*@ invariant a > 0 &*& b > 0 &*& a >= b
                &*&   gcd(a,b) == gcd(orig_a,orig_b); @*/
        /*@ decreases b; @*/
    {
        /*@ {
            div_rem(a,b);
            assert b*(a/b) + a%b == a;
            assert a%b == a - b*(a/b);

            assert a%b == a + b*(-(a/b));
            lincombo_factor(b,a%b,a/b,1,a,gcd(b,a%b));
            lincombo_factor(a,b,1,-(a/b),a%b,gcd(a,b));
            gcd_is_max_divisor(b,a%b,gcd(a,b));
            gcd_is_max_divisor(a,b,gcd(b,a%b));

        } @*/

        size_t new_a = b;
        size_t new_b = a%b;
        a = new_a;
        b = new_b;
    }
    /*@ division_unique(b,b,1,0); @*/
    /*@ gcd_is_max_divisor(a,b,b); @*/
    return b;
}

int prime_sieve(int* buff, int n)
    /*@ requires buff[..n] |-> _ &*& n > 0 &*& n+n <= INT_MAX; @*/
    /*@ ensures  int_buffer(buff, result, n,
                    reverse(primes_below(nat_of_int(n-1))));
      @*/
    /*@ terminates; @*/
{
    /*@ {
        if(buff == 0) {
            open ints(buff,_,_);
            integer_limits(buff);
            assert false;
        }
    } @*/

    int i,j;

    if(n < 2) {
        return 0;
    }

    for(i = 0; i < n; ++i)
        /*@ requires buff[i..n] |-> _ &*& i <= n &*& i >= 0; @*/
        /*@ ensures  buff[old_i..n] |-> repeat(1,nat_of_int(n-old_i));
          @*/
        /*@ decreases n-i; @*/
    {
        buff[i] = 1;
    }
    /*@ assert buff[..n] |-> repeat(1,nat_of_int(n)); @*/

    /*@ {
        open ints(buff,_,_);
        open ints(buff+1,_,_);
    } @*/

    buff[0] = 0;
    buff[1] = 0;
    /* @ assume(false); @*/

    /*@ {
        assert buff[2..n] |-> ?init_nums;
        assert init_nums == repeat(1,nat_of_int(n-2));
        if(!forall(indices_of_inner(1,init_nums,2),
                (prime_up_to)(nat_of_int(1)))) {
            int cx = not_forall(indices_of_inner(1,init_nums,2),
                (prime_up_to)(nat_of_int(1)));
            assert false;
        }
        if(!forall(indices_of_inner(0,init_nums,2),
                (notf)(is_prime))) {
            int cx = not_forall(indices_of_inner(0,init_nums,2),
                (notf)(is_prime));
            //indices_of_inner_correct(0,init_nums,2,cx);
            assert nth_of(cx-2,init_nums) == some(0);
            nth_of_is_nth(cx-2,init_nums);
            mem_repeat(nth(cx-2,init_nums),1,nat_of_int(n-2));
            assert false;
        }
        if(!forall(init_nums,isbit)) {
            int cx = not_forall(init_nums,isbit);
            assert false;
        }
    } @*/

    for(i = 2; i < n; ++i)
        /*@ requires buff[i..n] |-> ?nums
                &*&  !!forall(indices_of_inner(1,nums,i),
                        (prime_up_to)(nat_of_int(i-1)))
                &*&  !!forall(indices_of_inner(0,nums,i),
                        (notf)(is_prime))
                &*&  !!forall(nums,isbit)
                &*&  i >= 2 &*& i <= n
                ;
          @*/
        /*@ ensures  buff[old_i..n] |-> ?primes
                &*&  !!forall(primes,isbit)
                &*&  reverse(indices_of_inner(1,primes,old_i))
                     == filter((ge_than)(old_i),
                            primes_below(nat_of_int(n-1)))
                ;
          @*/
        /*@ decreases n-i; @*/
    {

        /*@ open ints(buff+i,_,_); @*/
        /*@ prime_test(i); @*/
        if(!buff[i]) {
            /*@ {
                assert nth_of(0,nums) == some(0);
                assert !mem(i,indices_of_inner(1,nums,i));
                assert !is_prime(i);
                if(!forall(indices_of_inner(1,tail(nums),i+1),
                        (prime_up_to)(nat_of_int(i)))) {
                    int cx = not_forall(
                        indices_of_inner(1,tail(nums),i+1),
                        (prime_up_to)(nat_of_int(i)));
                    forall_elim(indices_of_inner(1,tail(nums),i+1),
                        (prime_up_to)(nat_of_int(i-1)), cx);
                    prime_up_to_composite(nat_of_int(i-1),cx);

                    assert false;
                }
            } @*/
        } else {
            /* @ open ints(buff+i,_,_); @*/
            /*@ {
                assert buff[i] |-> 1;
                indices_of_inner_correct(1, nums, i, 0);
                assert !!is_prime(i);
                division_unique(i+i,i,2,0);
                if(i+i >= n) {
                    assert buff[i+1..n] |-> ?later;
                    if(!forall(indices_of_inner(1, later,
                                        (i+1)),
                                (prime_up_to)(nat_of_int(i)))) {
                        int cx = not_forall(indices_of_inner(1, later,
                                        (i+1)),
                                (prime_up_to)(nat_of_int(i)));
                        assert cx >= i+1;
                        assert cx < n;
                        forall_elim(indices_of_inner(1,later,i+1),
                                (prime_up_to)(nat_of_int(i-1)),cx);
                        division_unique(cx,i,1,cx-i);
                        if(!is_prime(i)) { assert false; }
                        assert !!prime_up_to(nat_of_int(i-1),cx);
                        assert nat_of_int(i) == succ(nat_of_int(i-1));

                        if(nonfactor(i,cx)) { assert false; }
                        assert i > 0;
                        assert cx > 0;
                        assert cx%i != 0;
                        assert i%cx != 0;
                        assert cx-i >= 1;
                        assert cx-i < n-i;
                        assert false;
                    }
                }
            } @*/

            for(j = i + i; j < n; j += i)
                /*@ requires buff[(j-i+1)..n] |-> ?later
                        &*&  !!forall(indices_of_inner(1,later,j-i+1),
                                (prime_up_to)(nat_of_int(i-1)))
                        &*&  !!forall(indices_of_inner(0,later,j-i+1),
                                (notf)(is_prime))
                        &*&  !!forall(later,isbit)
                        &*&  j-i >= i &*& j%i == 0
                        &*&  j < n ? emp
                        : !!forall(indices_of_inner(1, later,
                                        (j-i+1)),
                                (prime_up_to)(nat_of_int(i)));
                @*/
                /*@ ensures  buff[(old_j-i+1)..n] |-> ?new_later
                        &*&  !!forall(indices_of_inner(1, new_later,
                                        (old_j-i+1)),
                                (prime_up_to)(nat_of_int(i)))
                        &*&  !!forall(indices_of_inner(0,new_later,old_j-i+1),
                                (notf)(is_prime))
                        &*&  !!forall(new_later,isbit)
                        ;
                @*/
                /*@ decreases n-j; @*/
            {

                /*@ {
                    ints_split(buff+j-i+1, i-1);
                    assert buff[(j-i+1)..j] |-> ?pref;
                    assert buff[j..n] |-> ?rest;
                    assert later == append(pref,rest);
                    assert indices_of_inner(1,later,j-i+1)
                        == append(indices_of_inner(1,pref,j-i+1),
                                indices_of_inner(1,rest,j));
                    forall_append_exact(
                        indices_of_inner(1,pref,j-i+1),
                        indices_of_inner(1,rest,j),
                        (prime_up_to)(nat_of_int(i-1)));
                    forall_append_exact(
                        indices_of_inner(0,pref,j-i+1),
                        indices_of_inner(0,rest,j),
                        (notf)(is_prime));
                    forall_append_exact(pref, rest, isbit);

                    div_rem(j,i);
                    division_unique(j+i,i,(j/i+1),0);

                    if(prime_up_to(nat_of_int(i),j)) {
                        prime_up_to_no_factors(nat_of_int(i), j, i);
                        assert false;
                    }

                    if(!forall(indices_of_inner(1,pref,j-i+1),
                            (prime_up_to)(nat_of_int(i)))) {
                        int cx = not_forall(indices_of_inner(1,pref,j-i+1),
                            (prime_up_to)(nat_of_int(i)));
                        if(cx <= 0) { assert false; }
                        assert cx >= j-i+1;
                        assert cx <  j;
                        assert cx-(j-i) >= 1;
                        assert cx-(j-i) <  i;
                        int diff = cx-(j-i);
                        if(diff >= i) { assert false; }
                        if(diff < 0) { assert false; }
                        division_unique(diff,i,0,diff);
                        division_unique(i-j,i,1-j/i,0);
                        forall_elim(indices_of_inner(1,pref,j-i+1),
                            (prime_up_to)(nat_of_int(i-1)), cx);
                        int_of_nat_of_int(i);
                        assert nat_of_int(i) == succ(nat_of_int(i-1));
                        assert cx%i == 0;

                        div_rem(cx,i);

                        division_unique(cx-(j-i),i,cx/i+1-j/i,0);
                        assert false;
                    }

                    if(is_prime(j)) {
                        prime_no_factors(j,i);
                        assert false;
                    }
                    assert !is_prime(j);

                    if(j+i >= n) {
                        assert buff[j+1..n] |-> ?next;
                        if(!forall(indices_of_inner(1, next,
                                            (j+1)),
                                    (prime_up_to)(nat_of_int(i)))) {
                            int cx = not_forall(indices_of_inner(1,
                                            next, (j+1)),
                                    (prime_up_to)(nat_of_int(i)));
                            assert cx >= j+1;
                            assert cx < n;
                            forall_elim(indices_of_inner(1,next,j+1),
                                    (prime_up_to)(nat_of_int(i-1)),cx);
                            division_unique(j,i,j/i,0);
                            division_unique(cx,i,j/i,cx-j);
                            if(!is_prime(i)) { assert false; }
                            assert !!prime_up_to(nat_of_int(i-1),cx);
                            assert nat_of_int(i) == succ(nat_of_int(i-1));

                            if(nonfactor(i,cx)) { assert false; }
                            assert i > 0;
                            assert cx > 0;
                            assert cx%i != 0;
                            assert i%cx != 0;
                            assert cx-j >= 1;
                            assert cx-j < n-j;
                            assert false;
                        }
                        
                    }

                } @*/

                buff[j] = 0;

                /*@ recursive_call(); @*/

                /*@ {
                    assert buff[((old_j+i)-i+1)..n] |-> ?next_later
                        &*&  !!forall(indices_of_inner(1, next_later,
                                        ((old_j+i)-i+1)),
                                (prime_up_to)(nat_of_int(i)));

                    if(!forall(indices_of_inner(1, take(i-1,later),
                                        (old_j-i+1)),
                                (prime_up_to)(nat_of_int(i)))) {
                        int cx = not_forall(
                            indices_of_inner(1, take(i-1,later),
                                (old_j-i+1)),
                            (prime_up_to)(nat_of_int(i)));
                        forall_elim(indices_of_inner(1,later,old_j-i+1),
                                (prime_up_to)(nat_of_int(i-1)), cx);

                        assert false;
                    }
                    indices_of_inner_append(1,{0},next_later,old_j);
                    indices_of_inner_append(1,take(i-1,later),
                        cons(0,next_later),old_j-i+1);
                    indices_of_inner_append(0,{0},next_later,old_j);
                    indices_of_inner_append(0,take(i-1,later),
                        cons(0,next_later),old_j-i+1);

                    assert !!forall(
                        indices_of_inner(1, cons(0,next_later),
                            old_j),
                        (prime_up_to)(nat_of_int(i)));

                    forall_append(
                        indices_of_inner(1, take(i-1,later),
                                        (old_j-i+1)),
                        indices_of_inner(1, cons(0,next_later),
                                        old_j),
                        (prime_up_to)(nat_of_int(i)));

                    forall_append(
                        indices_of_inner(0, take(i-1,later),
                                        (old_j-i+1)),
                        indices_of_inner(0, cons(0,next_later),
                                        old_j),
                        (notf)(is_prime));

                    forall_append(take(i-1,later), cons(0,next_later),
                        isbit);

                    close ints(buff+old_j, n-old_j, _);
                    ints_join(buff+old_j-i+1);
                    assert buff[(old_j-i+1)..n] |-> ?new_later;
                    assert new_later ==
                        append(take(i-1,later),append({0},next_later));
                    assert indices_of_inner(1,new_later,old_j-i+1)
                        == append(
                            indices_of_inner(1,take(i-1,later),old_j-i+1),
                            indices_of_inner(1,append({0},next_later),
                                old_j)
                            );

                    if(!forall(indices_of_inner(0,new_later,old_j-i+1),
                            (notf)(is_prime))) {
                        assert false;
                    }

                } @*/
            }

            /*@ {
                assert buff[(i+1)..n] |-> ?primes;
                if(!forall(indices_of_inner(0,primes,i+1),
                        (notf)(is_prime))) {
                    int cx = not_forall(indices_of_inner(0,primes,i+1),
                        (notf)(is_prime));
                    forall_elim(indices_of_inner(1,primes,i+1),
                            (prime_up_to)(nat_of_int(i)), cx);
                    prime_test(cx);
                    assert false;
                }
            } @*/
        }

        /*@ recursive_call(); @*/

        /*@ {
           assert buff[(old_i+1)..n] |-> ?later_primes;
           assert buff[old_i..n] |-> ?primes;
           assert reverse(indices_of_inner(1,later_primes,old_i+1))
                     == filter((ge_than)(old_i+1),
                            primes_below(nat_of_int(n-1)));

            shift_primes_below_range(old_i+1,nat_of_int(n-1));

        } @*/
    }

    /*@ {
        assert buff[2..n] |-> ?base_primes;
        assert reverse(indices_of_inner(1,base_primes,2))
                     == filter((ge_than)(2),
                            primes_below(nat_of_int(n-1)));

        assert buff[..n] |-> ?primes;
        assert !!forall(primes,isbit);
        if(filter((ge_than)(0),primes_below(nat_of_int(n-1)))
           != filter((ge_than)(2),primes_below(nat_of_int(n-1)))) {
            int cx = filter_diff((ge_than)(0),(ge_than)(2),
                primes_below(nat_of_int(n-1)));
            assert false;
        }

        note_eq(  indices_of_inner(1,primes,0),
             indices_of_inner(1,base_primes,2));
        note_eq(reverse(indices_of_inner(1,primes,0)),
            filter((ge_than)(0),
                        primes_below(nat_of_int(n-1))));
        if(filter((ge_than)(0), primes_below(nat_of_int(n-1)))
           != primes_below(nat_of_int(n-1))) {
            int x = filter_effect((ge_than)(0),
                primes_below(nat_of_int(n-1)));
            assert false;
        }
    } @*/

    /*@  close ints(buff,n,_); @*/

    /*@ assert  buff[..n] |-> ?primes
            &*&  !!forall(primes,isbit)
            &*&  reverse(indices_of_inner(1,primes,0))
                    == primes_below(nat_of_int(n-1))
            ;
        @*/


    /*@ ints_split(buff,2); @*/
    i = 0;
    for(j = 2; j < n; ++j)
        /*@ invariant i+1 < j &*& i >= 0 &*& j <= n
                &*&   buff[..i] |-> ?final_primes
                &*&   buff[i..j] |-> _
                &*&   buff[j..n] |-> ?sieve_primes
                &*&   !!forall(sieve_primes,isbit)
                &*&   reverse(append(final_primes,
                            indices_of_inner(1,sieve_primes,j)))
                    == primes_below(nat_of_int(n-1))
                ;
          @*/
        /*@ decreases n-j; @*/
    {
        /*@ int old_i = i; @*/
        /*@ {
            open ints(buff+j,_,_);
            cons_head_tail(sieve_primes);
        } @*/
        if(buff[j]) {
            buff[i] = j;
            ++i;
            /*@ {
                close ints(buff+old_i,1,{j});
                ints_join(buff);
                assert indices_of_inner(1,sieve_primes,j)
                    == cons(j,indices_of_inner(1,
                        tail(sieve_primes),j+1));
                append_assoc(final_primes,{j},
                    indices_of_inner(1,
                        tail(sieve_primes),j+1));
            } @*/
        } else {
            /*@ {
                assert indices_of_inner(1,sieve_primes,j)
                    == indices_of_inner(1,
                        tail(sieve_primes),j+1);
            } @*/
        }
        /*@ {
            close ints(buff+j,1,_);
            ints_join(buff+i);
        } @*/
    }
    return i;
}

