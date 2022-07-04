/*@ #include <permutations.gh> @*/

/*@

fixpoint bool is_at_least(int x, list<int> l) {
    switch(l) {
    case nil: return true;
    case cons(v,vs):
        return x <= v && is_at_least(x,vs);
    }
}

fixpoint bool is_sorted_int(list<int> l) {
    switch(l) {
    case nil: return true;
    case cons(x,xs):
        return xs == nil || (is_at_least(x,xs) && is_sorted_int(xs));
    }
}

lemma_auto void length_nil<t>(list<t> l)
    requires true;
    ensures  (length(l) == 0) == (l == nil);
{ switch(l) { case nil: case cons(v,vs): } }

lemma_auto void sorted_singleton(list<int> l)
    requires length(l) == 1;
    ensures  !!is_sorted_int(l);
{ switch(l) { case nil: case cons(v,vs): } }

lemma void shift_is_at_least(int x, int y, list<int> l)
    requires x <= y &*& !!is_at_least(y,l);
    ensures  !!is_at_least(x,l);
{ switch(l) { case nil: case cons(v,vs): shift_is_at_least(x,y,vs); } }

lemma void indexing_string(char *u, int i)
    requires [?f]string(u,?cs2) &*& i >= 0 &*& i <= length(cs2);
    ensures [f]chars(u,i,take(i,cs2)) &*& [f]string(u+i,drop(i,cs2));
{
    open [f]string(u,cs2);
    assert [f]character(u,?c);
    if(c == 0) {
        assert cs2 == nil;
        assert i == 0;

        close [f]chars(u,0,nil);
        close [f]string(u,nil);
    } else {
        assert [f]string(u+1,?cs1) &*& cs2 == cons(c,cs1);
        if(i == 0) {
            close [f]chars(u,0,nil);
            close [f]string(u,cs2);
        } else {
            assert i > 0;
            assert i-1 >= 0 &*& i-1 <= length(cs1);
            indexing_string(u+1,i-1);

            assert  [f]chars(u+1,i-1,take(i-1,cs1))
                &*& [f]string(u+1+(i-1),drop(i-1,cs1));

            assert u+1+(i-1) == u+i;

            assert drop(i-1,cs1) == drop(i,cons(c,cs1));
            assert drop(i-1,cs1) == drop(i,cs2);

            assert [f]character(u,c) &*& [f]chars(u+1,i-1,take(i-1,cs1));
            close [f]chars(u,i,cons(c,take(i-1,cs1)));
            assert cons(c,take(i-1,cs1)) == take(i,cons(c,cs1));
            assert cons(c,take(i-1,cs1)) == take(i,cs2);
            assert  [f]chars(u,i,take(i,cs2))
                &*& [f]string(u+i,drop(i,cs2));

        }
    }
}

  @*/

bool is_sorted_real(int* arr, int n)
    /*@ requires [?f]arr[..n] |-> ?l; @*/
    /*@ ensures  [ f]arr[..n] |->  l
            &*&  result == is_sorted_int(l); @*/
    /*@ terminates; @*/
{
    int i;
    bool ret = true;
    /*@ int lower_bound = 0; @*/
    for(i = 0; i+1 < n; ++i)
        /*@ requires [f]arr[i..n] |-> ?loop_l
                &*&  i >= 0 &*& (n == 0 || i+1 <= n)
                &*&  switch(loop_l) {
                case nil: return true;
                case cons(v,vs):
                    return i == 0 || lower_bound <= v;
                }
                &*&  (length(loop_l) > 1 || is_sorted_int(loop_l))
                &*&  ret == true
                ; @*/
        /*@ ensures  [f]arr[old_i..n] |-> loop_l
                &*&  ret ==
                    (old_ret
                        && is_sorted_int(loop_l)
                        && (old_i == 0
                            || is_at_least(old_lower_bound,loop_l)))
                ; @*/
        /*@ decreases n-i; @*/
    {
        /*@ open ints(arr+i,_,_); @*/
        /*@ open ints(arr+i+1,_,_); @*/
        if(arr[i] > arr[i+1]) {
            ret = false;
            break;
        }
        /*@ assert [f]arr[i] |-> ?x; @*/
        /*@ assert [f]arr[i+1..n] |-> ?rest_l; @*/
        /*@ int prev_lower_bound = lower_bound; @*/
        /*@ int next_i = i+1; @*/
        /*@ lower_bound = x; @*/

        /*@ recursive_call(); @*/

        /*@ {
            if(ret) {
                assert !!is_sorted_int(rest_l);
                assert (next_i == 0 || is_at_least(x,rest_l));
                if(old_i != 0) {
                    shift_is_at_least(prev_lower_bound,x,rest_l);
                }
            }
        } @*/
    }
    return ret;
}

bool is_sorted_real2(int* arr, int n)
    /*@ requires [?f]arr[..n] |-> ?l; @*/
    /*@ ensures  [ f]arr[..n] |->  l
            &*&  result == is_sorted_int(l); @*/
    /*@ terminates; @*/
{
    /*@ switch(l) { case nil: case cons(v,vs): } @*/
    int i;
    bool ret = true;

    for(i = 0; i+1 < n; ++i)
        /*@ requires [f]arr[i..n] |-> ?loop_l
                &*&  i >= 0 &*& (n == 0 || i+1 <= n)
                &*&  (length(loop_l) > 1 || is_sorted_int(loop_l))
                &*&  ret == true
                ; @*/
        /*@ ensures  [f]arr[old_i..n] |-> loop_l
                &*&  switch(loop_l) {
                case nil:
                    return ret ==
                        (old_ret
                        && is_sorted_int(loop_l));
                case cons(v,vs):
                    return ret == (old_ret && is_sorted_int(loop_l)
                        && is_at_least(v,vs)
                        );
                }
                ; @*/
        /*@ decreases n-i; @*/
    {
        /*@ open ints(arr+i,_,_); @*/
        /*@ open ints(arr+i+1,_,_); @*/
        if(arr[i] > arr[i+1]) {
            ret = false;
            break;
        }
        /*@ assert [f]arr[i] |-> ?x; @*/
        /*@ assert [f]arr[i+1..n] |-> ?rest_l; @*/
        /*@ int next_i = i+1; @*/

        /*@ recursive_call(); @*/

        /*@ {
            if(ret) {
                switch(loop_l) {
                case nil:
                case cons(v,vs):
                    switch(vs) {
                    case nil:
                    case cons(vv,vvs):
                        shift_is_at_least(v,vv,vvs);
                    }
                }
            }
        } @*/
    }
    return ret;
}

bool is_in_array(int x, int* arr, int n)
    /*@ requires [?f]arr[..n] |-> ?l; @*/
    /*@ ensures  [ f]arr[..n] |->  l &*& result == mem(x,l); @*/
    /*@ terminates; @*/
{
    bool ret = false;
    int i;
    for(i = 0; i < n; ++i)
        /*@ requires [f]arr[i..n]     |-> ?loop_l
                &*&  i >= 0 &*& i <= n; @*/
        /*@ ensures  [f]arr[old_i..n] |->  loop_l
                &*&  ret == (old_ret || mem(x,loop_l)); @*/
        /*@ decreases n-i; @*/
    {
        /*@ open ints(arr+i,_,_); @*/
        if(arr[i] == x) {
            ret = true;
            break;
        }

        /*@ recursive_call(); @*/

        /*@ assert true; @*/
    }

    return ret;
}

void insertion_sort(int* arr, int n)
    /*@ requires arr[..n] |-> ?l; @*/
    /*@ ensures  arr[..n] |-> ?new_l &*& !!is_sorted_int(new_l)
            &*&  !!is_permutation(l,new_l); @*/
    /*@ terminates; @*/
{
    /* remove this to start proving! */
    /*@ assume(false); @*/

    int i,j;
    for(i = n; i > 0; --i)
    {
        for(j=i-1; j+1 < n; ++j)
        {
            if(arr[j] <= arr[j+1]) { break; }

            int tmp = arr[j+1];
            arr[j+1] = arr[j];
            arr[j] = tmp;

        }
    }
}

