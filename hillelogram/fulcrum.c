#include <string.h>
#include <stdlib.h>
#include <stdint.h>
/*@ #include <nat.gh> @*/
/*@ #include <listex.gh> @*/
/*@ #include <quantifiers.gh> @*/
/*@ #include <arrays.gh> @*/
/*@ #include "../util.gh" @*/
/*@ #include "../lists.gh" @*/
/*@ #include "../sorting.gh" @*/

/*@

fixpoint int sum_diff(list<int> a, list<int> b) {
    return abs_of(sum(a) - sum(b));
}

fixpoint pair<list<t>, list<t> > split_at<t>(nat n, list<t> l) {
    switch(n) {
    case zero:
        return pair(nil,l);
    case succ(n0):
        return switch(l) {
        case nil: return pair(nil,nil);
        case cons(x,xs):
            return switch(split_at(n0,xs)) {
            case pair(a,b):
                return pair(cons(x,a),b);
            };
        };
    }
}

fixpoint list<pair<list<t>, list<t> > >
all_splits_inner<t>(nat f,nat rest,list<t> l) {
    switch(f) {
    case zero: return {};
    case succ(f0):
        return cons(split_at(rest,l),all_splits_inner(f0,succ(rest),l));
    }
}

fixpoint list<pair<list<t>, list<t> > > all_splits<t>(list<t> l) {
    return all_splits_inner(succ(noi(length(l))),zero,l);
}

lemma_auto void length_all_splits_inner<t>(nat f, nat n, list<t> l)
    requires true;
    ensures  length(all_splits_inner(f,n,l)) == ion(f);
{ NAT_INDUCTION(f,f0,length_all_splits_inner(f0,succ(n),l)) }

lemma void all_splits_inner_step<t>(nat f0, nat f1, nat n, list<t> l)
    requires true;
    ensures  all_splits_inner(nat_plus(f0,f1),n,l)
        ==   append(all_splits_inner(f0,n,l),
                    all_splits_inner(f1,nat_plus(f0,n),l));
{
    switch(f0) {
    case zero:
    case succ(f00):
        all_splits_inner_step(f00,f1,succ(n),l);
    }
}

lemma void all_splits_step<t>(nat n, list<t> l)
    requires ion(n) <= length(l);
    ensures  all_splits(l)
        ==   append(
                all_splits_inner(n,zero,l),
                all_splits_inner(noi(length(l)+1-ion(n)),n,l));
{
    assert nat_plus(n,zero) == n;
    assert ion(noi(length(l) - ion(n))) == length(l) - ion(n);
    all_splits_inner_step(n,noi(length(l)+1-ion(n)),zero,l);
}

lemma void split_at_nil<t>(nat n, list<t> l, list<t> suff)
    requires split_at(n,l) == pair(nil,suff);
    ensures  l == suff;
{
    switch(n) {
    case zero:
    case succ(n0):
        switch(l) {
        case nil:
        case cons(x,xs):
            switch(split_at(n0,xs)) {
            case pair(a,b):
            }
        }
    }
}

lemma void split_at_is_split<t>(nat n, list<t> l, list<t> pref,
        list<t> suff)
    requires split_at(n,l) == pair(pref,suff);
    ensures  l == append(pref,suff);
{
    switch(n) {
    case zero:
    case succ(n0):
        switch(l) {
        case nil:
        case cons(x,xs):
            switch(split_at(n0,xs)) {
            case pair(a,b):
                split_at_is_split(n0,xs,a,b);
            }
        }
    }
}

lemma void split_at_length<t>(nat n, list<t> l)
    requires split_at(n,l) == pair(?pref,?suff);
    ensures  length(pref) == min_of(ion(n),length(l));
{
    switch(n) {
    case zero:
    case succ(n0):
        switch(l) {
        case nil:
        case cons(x,xs):
            split_at_length(n0,xs);
        }
    }
}

lemma void split_at_step<t>(nat n0, list<t> l, list<t> pref, t x, list<t> suff)
    requires split_at(n0,l) == pair(pref,cons(x,suff));
    ensures  split_at(succ(n0),l) == pair(append(pref,{x}),suff);
{
    switch(n0) {
    case zero:
    case succ(n1):
        switch(l) {
        case nil:
            assert false;
        case cons(v,vs):
            split_at_is_split(n0,l,pref,cons(x,suff));
            switch(split_at(n1,vs)) {
            case pair(a,b):
                split_at_is_split(n1,vs,a,b);
                split_at_step(n1,vs,a,x,suff);
            }
        }
    }
}

lemma void ints_sum_limits(int32_t* arr, int n)
    requires [?f]arr[..n] |-> ?l;
    ensures  [ f]arr[..n] |->  l
        &*&  sum(l) >= -length(l)*(pow_nat(2,N31))
        &*&  sum(l) <=  length(l)*(pow_nat(2,N31)-1);
{
    if(sum(l) < -length(l)*(pow_nat(2,N31))
            || sum(l) > length(l)*(pow_nat(2,N31)-1)) {
        open ints(arr,_,_);
        ints_sum_limits(arr+1,n-1);
        integer_limits(arr);
        assert false;
    }
}

  @*/

int64_t abs64(int64_t x)
    /*@ requires x > -pow_nat(2,N63)+1; @*/
    /*@ ensures  result == abs_of(x); @*/
    /*@ terminates; @*/
{
    return x >= 0 ? x : -x;
}

int fulcrum(int32_t* arr, int n)
    /*@ requires [?f]arr[..n] |-> ?l; @*/
    /*@ ensures  [ f]arr[..n] |->  l
            &*&  result >= 0 &*& result <= length(l)
            &*&  !!all_ge(onpairs(sum_diff,split_at(noi(result),l)),
                    map((onpairs)(sum_diff),
                        all_splits(l)))
        ; @*/
    /*@ terminates; @*/
{
    int i, best_ix = 0;
    int64_t best_split_sum;
    int64_t running_split_sum = 0;

    if(n == 0) {
        return 0;
    }

    /*@ if(n < 0 || n >= pow_nat(2,N31)) {
        assert false;
    } @*/

    for(i = 0; i < n; ++i)
        /*@ requires [f]arr[    i..n] |-> ?loop_l
                &*&  i >= 0 &*& i <= n
                &*&  running_split_sum <=  i*pow_nat(2,N31)
                &*&  running_split_sum >= -i*(pow_nat(2,N31)-1)
                ; @*/
        /*@ ensures  [f]arr[old_i..n] |->  loop_l
                &*&  running_split_sum <=  n*pow_nat(2,N31)
                &*&  running_split_sum >= -n*(pow_nat(2,N31)-1)
                &*&  running_split_sum
                ==   old_running_split_sum - sum(loop_l)
                ; @*/
        /*@ decreases n-i; @*/
    {
        /*@ open ints(arr+i,_,_); @*/

        /*@ {
            assert [f]arr[i] |-> ?x;
            if(x < -pow_nat(2,N31) || x > pow_nat(2,N31)-1) {
                integer_limits(arr+i);
                assert false;
            }

            if(n*pow_nat(2,N31) >= pow_nat(2,N63)-1) {
                assert false;
            }

            if(n*pow_nat(2,N31) <= -pow_nat(2,N63)) {
                assert false;
            }

            mul_mono_l(i+1,n,pow_nat(2,N31));
            mul_mono_l(-n,-i-1,pow_nat(2,N31)-1);

            if(running_split_sum - x > (i+1)*pow_nat(2,N31)) {
                assert false;
            }

            if(running_split_sum - x < -(i+1)*(pow_nat(2,N31)-1)) {
                assert false;
            }

        } @*/

        running_split_sum -= (int64_t)arr[i];
    }

    best_split_sum = abs64(running_split_sum);

    /*@ pair<list<int>, list<int> > first_split
            = split_at(zero,l); @*/

    /*@ {
        assert first_split == pair(nil,l);
        assert sum_diff(nil,l) == abs_of(sum(nil) - sum(l));
        assert sum_diff(nil,l) == abs_of(-sum(l));
        assert sum_diff(nil,l) == best_split_sum;

        assert noi(length(l)) == succ(noi(length(l)-1));
        note_eq( take(1, all_splits(l))
            ,  {first_split});

        split_at_is_split(zero,l,nil,l);

    } @*/

    /*@ list<pair<list<int>, list<int> > > splits_pref = {first_split};
      @*/

    /*@ list<pair<list<int>, list<int> > > splits_suff =
            tail(all_splits(l));
      @*/

    for(i = 0; i < n; ++i)
        /*@ invariant i >= 0 &*& i <= n
                &*&   [f]arr[ ..i] |-> ?pref
                &*&   [f]arr[i..n] |-> ?suff
                &*&   pair(pref,suff)
                ==    split_at(noi(i),l)
                &*&   append(pref,suff) == l
                &*&   running_split_sum
                ==    sum(pref) - sum(suff)
                &*&   best_ix >= 0 &*& best_ix <= i
                &*&   best_split_sum
                ==    onpairs(sum_diff,split_at(noi(best_ix),l))
                &*&   !!all_ge(best_split_sum,
                        map((onpairs)(sum_diff),
                            splits_pref))
                &*&   length(splits_pref) == i+1
                &*&   append(splits_pref,splits_suff)
                        == all_splits(l)

                &*&   splits_pref
                ==    all_splits_inner(noi(i+1),zero,l)
                &*&   splits_suff
                ==    all_splits_inner(noi(length(l)-i),noi(i+1),l)


                &*&   sum(pref) <= length(pref)*(pow_nat(2,N31)-1)
                &*&   sum(pref) >= length(pref)*(-pow_nat(2,N31))

                &*&   sum(suff) <= length(suff)*(pow_nat(2,N31)-1)
                &*&   sum(suff) >= length(suff)*(-pow_nat(2,N31))
                ; @*/
        /*@ decreases n-i; @*/
    {
        int64_t split_sum;
        /*@ open ints(arr+i,_,_); @*/
        /*@ integer_limits(arr+i); @*/
        int64_t x = arr[i];

        /*@ note_eq(
            running_split_sum + 2*x,
            sum(append(pref,{x}))-sum(tail(suff))); @*/

        running_split_sum += 2*x;
        split_sum = abs64(running_split_sum);

        /*@ {
            ints_sum_limits(arr+i+1,n-i-1);

            switch(splits_suff) {
            case nil: assert false;
            case cons(v,vs):

                split_at_step(noi(i),l,pref,x,tail(suff));
                all_splits_step(succ(noi(i)),l);
                assert all_splits(l)
                    == append(all_splits_inner(succ(noi(i)), zero, l),
                            all_splits_inner(noi(length(l)-i), succ(noi(i)),
                                l));
                assert noi(length(l)-i)
                    == succ(noi(length(l)-1-i));
                assert all_splits_inner(noi(length(l)-i), succ(noi(i)), l)
                    == cons(split_at(succ(noi(i)),l),
                        all_splits_inner(noi(length(l)-1-i),noi(i+2), l));

                append_assoc(
                    all_splits_inner(succ(noi(i)), zero, l),
                    {split_at(succ(noi(i)),l)},
                    all_splits_inner(noi(length(l)-1-i),noi(i+2), l));


                map_append((onpairs)(sum_diff),
                    splits_pref,
                    {split_at(noi(i+1),l)});
                forall_append(
                    map((onpairs)(sum_diff),
                        splits_pref),
                    {onpairs(sum_diff,split_at(noi(i+1),l))},
                    (le)(best_split_sum));

                assert v == split_at(noi(i+1),l);

                assert map((onpairs)(sum_diff),
                        append(splits_pref,{v}))
                    == append(
                        map((onpairs)(sum_diff),
                            splits_pref),
                        {onpairs(sum_diff,split_at(noi(i+1),l))});

                note_eq(onpairs(sum_diff,split_at(noi(i+1),l)),
                    split_sum);

                assert map((onpairs)(sum_diff),
                        append(splits_pref,{v}))
                    == append(
                        map((onpairs)(sum_diff),
                            splits_pref),
                        {split_sum});

                if(split_sum < best_split_sum) {
                    if(!all_ge(split_sum,
                            map((onpairs)(sum_diff),
                                append(splits_pref,{v})))) {
                        int cx = not_forall(
                            map((onpairs)(sum_diff),
                                append(splits_pref,{v})),
                            (le)(split_sum));
                        if(cx != split_sum) {
                            forall_elim(
                                map((onpairs)(sum_diff),
                                    splits_pref),
                                (le)(best_split_sum),cx);
                        }
                        assert false;
                    }
                }

                all_splits_inner_step(noi(i+1),N1,zero,l);
                all_splits_inner_step(N1,noi(length(l)-i-1),noi(i+1),l);
                append_assoc(splits_pref,{v},vs);

                splits_pref = append(splits_pref,{v});
                splits_suff = vs;
            }

        } @*/


        if(split_sum < best_split_sum) {
            best_split_sum = split_sum;
            best_ix = i+1;

        }

        /*@ close [f]ints(arr+i,1,_); @*/
        /*@ ints_join(arr); @*/
    }

    return best_ix;


}


