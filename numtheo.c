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

size_t prime_sieve(int* buff, size_t n)
    /*@ requires buff[..n] |-> _ &*& n > 0 &*& n+n <= UINTPTR_MAX; @*/
    /*@ ensures  int_buffer(buff, result, n,
                    reverse(primes_below(nat_of_int(n))));
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

    size_t i,j;

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
    /*@ assume(false); @*/

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
    } @*/

    for(i = 2; i < n; ++i)
        /*@ requires buff[i..n] |-> ?nums
                &*&  !!forall(indices_of_inner(1,nums,i),
                        (prime_up_to)(nat_of_int(i-1)))
                &*&  !!forall(indices_of_inner(0,nums,i),
                        (notf)(is_prime))
                &*&  i >= 2 &*& i <= n
                ;
          @*/
        /*@ ensures  buff[old_i..n] |-> ?primes
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
                division_unique(i+i,i,2,0);
            } @*/

            for(j = i + i; j < n; j += i)
                /*@ requires buff[(j-i+1)..n] |-> ?later
                        &*&  !!forall(indices_of_inner(1,later,j-i+1),
                                (prime_up_to)(nat_of_int(i-1)))
                        &*&  j-i >= i &*& j%i == 0;
                @*/
                /*@ ensures  buff[(old_j-i+1)..n] |-> ?new_later
                        &*&  !!forall(indices_of_inner(1, new_later,
                                        (old_j-i+1)),
                                (prime_up_to)(nat_of_int(i)))
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
                        forall_elim(indices_of_inner(1,pref,j-i+1),
                            (prime_up_to)(nat_of_int(i-1)), cx);
                        int_of_nat_of_int(i);
                        assert nat_of_int(i) == succ(nat_of_int(i-1));
                        assert cx%i == 0;
                        assert cx >= j-i+1;
                        assert cx <  j;
                        assert cx-(j-i) >= 1;
                        assert cx-(j-i) <  i;

                        div_rem(cx,i);
                        division_unique(i-j,i,1-j/i,0);

                        division_unique(cx-(j-i),i,cx/i+1-j/i,0);
                        division_unique(cx-(j-i),i,0,cx-(j-i));
                        assert false;
                    }

                } @*/

                buff[j] = 0;
            }
        }
    }

    /*@ assume(false); @*/
}

