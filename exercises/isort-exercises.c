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
        return is_at_least(x,xs) && is_sorted_int(xs);
    }
}

  @*/

void isort(int* arr, int n)
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

