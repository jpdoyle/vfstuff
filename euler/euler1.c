/*@ #include <listex.gh> @*/
/*@ #include "../util.gh" @*/
/*@ #include "../lists.gh" @*/
/*@ #include "../math.gh" @*/
#include <stdio.h>

/*@

fixpoint bool mult3or5(int x) { return x%3 == 0 || x%5 == 0; }

fixpoint list<int> numsBelow_inner(int base, nat n) {
    switch(n) {
    case zero: return {};
    case succ(n0): return cons(base,numsBelow_inner(base+1,n0));
    }
}

fixpoint list<int> numsBelow(int lim) {
    return lim <= 0 ? {} : numsBelow_inner(0, noi(lim));
}

lemma void numsBelow_length(int base, nat n)
    requires true;
    ensures  length(numsBelow_inner(base,n)) == ion(n);
{
    switch(n) {
    case zero:
    case succ(n0):
        numsBelow_length(base+1,n0);
    }
}

lemma void numsBelow_bounds(int base, nat n, int x)
    requires true;
    ensures  mem(x,numsBelow_inner(base,n))
        ==   (x >= base && x < base + ion(n));
{
    switch(n) {
    case zero:
    case succ(n0):
        numsBelow_bounds(base+1,n0,x);
    }
}

lemma void numsBelow_distinct(int base, nat n)
    requires true;
    ensures  !!distinct(numsBelow_inner(base,n));
{
    switch(n) {
    case zero:
    case succ(n0):
        numsBelow_distinct(base+1,n0);
        numsBelow_bounds(base+1,n0,base);
    }
}

lemma void numsBelow_sum(int base, nat n)
    requires true;
    ensures  sum(numsBelow_inner(base,n))
        ==   ion(n)*base
             + (ion(n)*(ion(n)-1))/2;
{
    switch(n) {
    case zero:
        assert ion(n) == 0;
        assert ion(n)*base == 0;
        assert sum(numsBelow_inner(base,n)) == 0;
        assert (ion(n)*(ion(n)-1)) == 0;
        division_unique(ion(n)*(ion(n)-1),2,0,0);
        assert (ion(n)*(ion(n)-1))/2 == 0;

    case succ(n0):
        numsBelow_sum(base+1,n0);
        assert sum(numsBelow_inner(base,n))
            == base + sum(numsBelow_inner(base+1,n0));
        assert sum(numsBelow_inner(base,n))
            == base + ion(n0)*(base+1)
                + (ion(n0)*(ion(n0)-1))/2;
        assert ion(n) == ion(n0)+1;
        assert sum(numsBelow_inner(base,n))
            == base + ion(n0)*base + ion(n0)
                + (ion(n0)*(ion(n0)-1))/2;

        as_mul(ion(n0)+1,base);

        assert sum(numsBelow_inner(base,n))
            == (ion(n0)+1)*base + ion(n0)
                + (ion(n0)*(ion(n0)-1))/2;


        assert sum(numsBelow_inner(base,n))
            == ion(n)*base + ion(n0)
                + (ion(n0)*(ion(n0)-1))/2;

        div_rem(ion(n0)*(ion(n0)-1),2);

        assert ion(n0) >= 0;
        if((ion(n0)*(ion(n0)-1)) < 0) {
            if(ion(n0) > 0) {
                assert ion(n0)-1 >= 0;
                my_mul_mono_r(ion(n0),0,ion(n0)-1);
            } else {
                assert ion(n0) == 0;
                assert (ion(n0)*(ion(n0)-1)) == 0;
            }

            assert false;
        }

        into_numerator(ion(n0),
                (ion(n0)*(ion(n0)-1)), 2);

        assert sum(numsBelow_inner(base,n))
            == ion(n)*base
                + (2*ion(n0)
                    + ion(n0)*(ion(n0)-1))/2;

        assert sum(numsBelow_inner(base,n))
            == ion(n)*base
                + (2*ion(n0) + ion(n0)*ion(n0)
                    - ion(n0))/2;

        assert sum(numsBelow_inner(base,n))
            == ion(n)*base
                + (ion(n0) + ion(n0)*ion(n0))/2;
        assert sum(numsBelow_inner(base,n))
            == ion(n)*base
                + ((ion(n0) + 1)*ion(n0))/2;
        assert sum(numsBelow_inner(base,n))
            == ion(n)*base
                + (ion(n)*(ion(n)-1))/2;

    }
}

lemma void numsBelow_lowerbound(int base, nat n)
    requires true;
    ensures  !!forall(numsBelow_inner(base,n),(ge_than)(base));
{
    switch(n) {
    case zero:
    case succ(n0):
        numsBelow_lowerbound(base+1,n0);
        if(!forall(numsBelow_inner(base,n),(ge_than)(base))) {
            int cx = not_forall(numsBelow_inner(base,n),
                    (ge_than)(base));
            if(cx != base) {
                forall_elim(numsBelow_inner(base+1,n0),
                        (ge_than)(base+1), cx);
            }
            assert false;
        }
    }
}

  @*/

int multsum(int limit)
    /*@ requires limit >= 0 &*& (limit*(limit-1))/2 <= INT_MAX; @*/
    /*@ ensures  result == sum(filter(mult3or5,numsBelow(limit))); @*/
    /*@ terminates; @*/
{
    int ret = 0;
    int i;

    /*@ {
        numsBelow_sum(0,noi(limit));
        assert sum(numsBelow(limit)) <= INT_MAX;
        numsBelow_lowerbound(0,noi(limit));
        nonneg_filter_sum(numsBelow(limit),mult3or5);
    } @*/

    for(i = 0; i < limit; ++i)
        /*@ invariant i >= 0 &*& i <= limit
                &*&   ret +
                        sum(filter(mult3or5,
                            numsBelow_inner(i,noi(limit-i))))
                      == sum(filter(mult3or5,numsBelow(limit)))
                &*&   !!forall(numsBelow_inner(i,noi(limit-i)),
                        (ge_than)(0))
                ;
          @*/
        /*@ decreases (limit-i); @*/
    {
        /*@ {
            assert noi(limit-i)
                == succ(noi(limit-i-1));
            assert numsBelow_inner(i,noi(limit-i))
                == cons(i,numsBelow_inner(i+1,noi(limit-i-1)));
        } @*/

        if(i%3 == 0 || i%5 == 0) {
            /*@ {
                assert !!mult3or5(i);
                assert filter(mult3or5,
                            numsBelow_inner(i,noi(limit-i)))
                    == cons(i,
                        filter(mult3or5,
                            numsBelow_inner(i+1,
                                noi(limit-i-1))));

                forall_filter(numsBelow_inner(i,noi(limit-i)),
                        (ge_than)(0), mult3or5);

                nonneg_sum(filter(mult3or5,
                            numsBelow_inner(i+1,
                                noi(limit-i-1))));
                assert ret + i >= ret;
                assert ret + i <=
                    sum(filter(mult3or5,numsBelow(limit)));
            } @*/

            ret += i;
        }
    }

    return ret;
}

int main() /*@ : main @*/
    /*@ requires true; @*/
    /*@ ensures  result == sum(filter(mult3or5,numsBelow(1000))); @*/
{
    int ret = multsum(1000);
    printf("%d\n",ret);
    return ret;
}

