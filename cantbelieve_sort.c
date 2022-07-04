#include <stddef.h>
#include <limits.h>
#include "sorting.h"
/*@ #include "termination.gh" @*/

void icantbelieve(int* arr, int n)
    /*@ requires arr[..n] |-> ?l; @*/
    /*@ ensures  arr[..n] |-> ?new_l &*& !!sorted(new_l)
            &*&  !!is_permutation2(l,new_l); @*/
    /*@ terminates; @*/
{
    int i,j;
    for(i = 0; i < n; ++i)
        /*@ invariant i >= 0 &*& i <= n
                &*&   n == 0 ? true
                :     i > 0
                ?     arr[..i-1] |-> ?pref &*& arr[i-1] |-> ?x
                &*&   arr[i..n] |-> ?suff
                &*&   !!sorted(append(pref,{x}))
                &*&   !!is_permutation2(append(pref,cons(x,suff)), l)
                &*&   !!all_le(x,append(pref,suff))
                :     arr[..n] |-> ?new_l
                &*&   !!is_permutation2(new_l, l)
                ; @*/
        /*@ decreases n-i; @*/
    {
        /*@ if(n == 0) assert false; @*/
        /*@ if(i > 0) {
            close ints(arr+i-1,1,_);
            ints_join(arr);
        } @*/
        for(j = 0; j < n; ++j)
            /*@ invariant j >= 0 &*& j <= n

                        &*& j <= i
                        ?   arr[ ..j] |-> ?pref1
                        &*& arr[j..i] |-> ?pref2
                        &*& arr[i] |-> ?x
                        &*& arr[i+1..n] |-> ?suff
                        &*& !!sorted(append(pref1,pref2))
                        &*& !!is_permutation2(
                                append(append(pref1, pref2),
                                       cons(x, suff)),
                                l)
                        &*& !!all_le(x,pref1)

                        :   arr[..i] |-> ?pref
                        &*& arr[i] |-> ?x
                        &*& arr[i+1..j] |-> ?suff1
                        &*& arr[j..n] |-> ?suff2
                        &*& !!sorted(append(pref,{x}))
                        &*& !!is_permutation2(append(pref, cons(x,
                                append(suff1, suff2))),  l)
                        &*& !!all_le(x, append(pref,suff1))

                        ; @*/
            /*@ decreases n-j; @*/
        {
            /*@ {
                if(j != i) {
                    open ints(arr+j,_,_);
                }

            } @*/

            /*@ if(j < i) {
                assert arr[ ..j] |-> ?pref1
                    &*& arr[j..i] |-> ?pref2
                    &*& arr[i] |-> ?x
                    &*& arr[i+1..n] |-> ?suff;
                switch(pref2) {
                case nil: assert false;
                case cons(y,ys):
                    assert arr[j] |-> y;
                    assert !!sorted(append(pref1,pref2));
                    if(x < y) {
                        assert x < y;
                        sorted_append(pref1,pref2);
                        if(!sorted(cons(x,ys))) {
                            int cx = not_forall(ys,(le)(x));
                            forall_elim(ys,(le)(y),cx);
                            assert false;
                        }

                        if(!sorted(append(pref1,cons(x,ys)))) {
                            switch(not_sorted_append(pref1,cons(x,ys))) {
                            case pair(a,b):
                                assert !!all_le(x,pref1);
                                if(b == x) {
                                    forall_elim(pref1,(ge)(x), a);
                                    assert false;
                                } else {
                                    forall_elim(pref1,(flip)(all_ge)(cons(y,ys)),a);
                                    forall_elim(cons(y,ys),(le)(a),b);
                                    assert false;
                                }
                            }
                        }

                        list<int> l_old = append(append(pref1,
                                    cons(y,ys)), cons(x, suff));
                        list<int> l_new = append(append(pref1,
                                    cons(x,ys)), cons(y, suff));
                        if(!is_permutation2(l_new, l))
                        {
                            int cx = not_permutation2(l_new, l);
                            assert count_of(cx,l_new) != count_of(cx,l);
                            if(!mem(cx,l_new) && !mem(cx,l)) {
                                count_of_mem(cx,l_new);
                                count_of_mem(cx,l);
                                assert false;
                            }

                            if(mem(cx,l_new)) {
                                assert !!mem(cx,l_old);
                                forall_elim(l_old,
                                    (count_matches)(l_old,l), cx);
                                assert false;
                            } else {
                                assert !!mem(cx,l);
                                forall_elim(l,
                                    (count_matches)(l_old,l), cx);
                                assert false;
                            }
                        }

                        if(!all_le(y,append(pref1,{x}))) {
                            int cx = not_forall(append(pref1,{x}), (ge)(y));

                            forall_elim(pref1,(ge)(x),cx);
                            assert false;
                        }

                    } else {
                        if(!all_le(x,append(pref1,{y}))) {
                            int cx = not_forall(append(pref1,{y}), (ge)(x));

                            forall_elim(pref1,(ge)(x),cx);
                            assert false;
                        }
                    }
                }

            } else if(j > i) {

                assert arr[ ..i] |-> ?pref
                    &*& arr[i] |-> ?x
                    &*& arr[i+1..j] |-> ?suff1
                    &*& arr[j..n] |-> ?suff2;
                switch(suff2) {
                case nil: assert false;
                case cons(y,ys):
                    assert arr[j] |-> y;
                    assert !!sorted(append(pref,{x}));
                    sorted_append(pref,{x});
                    if(x < y) {

                        if(!sorted(append(pref,{y}))) {
                            maximum_append(pref,{x});
                            maximum_append(pref,{y});
                            assert maximum(append(pref,{x}))
                                == max_of(maximum(pref),x);
                            assert maximum(append(pref,{x}))
                                == x;
                            assert maximum(append(pref,{y}))
                                == max_of(maximum(pref),y);
                            if(maximum(pref) > y) {
                                assert false;
                            }
                            sorted_max_extend(pref,y);
                            assert false;
                        }

                        list<int> l_old = append(pref,
                                    cons(x, append(suff1,cons(y,ys))));
                        list<int> l_new = append(pref,
                                    cons(y, append(suff1,cons(x,ys))));
                        if(!is_permutation2(l_new, l))
                        {
                            int cx = not_permutation2(l_new, l);
                            assert count_of(cx,l_new) != count_of(cx,l);
                            if(!mem(cx,l_new) && !mem(cx,l)) {
                                count_of_mem(cx,l_new);
                                count_of_mem(cx,l);
                                assert false;
                            }

                            if(mem(cx,l_new)) {
                                assert !!mem(cx,l_old);
                                forall_elim(l_old,
                                    (count_matches)(l_old,l), cx);
                                assert false;
                            } else {
                                assert !!mem(cx,l);
                                forall_elim(l,
                                    (count_matches)(l_old,l), cx);
                                assert false;
                            }
                        }

                        if(!all_le(y,append(pref,append(suff1,{x})))) {
                            int cx = not_forall(append(pref, append(suff1,
                                            {x})), (ge)(y));
                            forall_elim(append(pref,suff1), (ge)(x), cx);
                            assert false;
                        }

                    } else {
                        if(!all_le(x,append(pref,append(suff1,{y})))) {
                            int cx = not_forall(append(pref, append(suff1,
                                            {y})), (ge)(x));
                            forall_elim(append(pref,suff1), (ge)(x), cx);
                            assert false;
                        }
                    }

                }
            } @*/

            if(arr[i] < arr[j]) {

                int tmp = arr[i];
                arr[i] = arr[j];
                arr[j] = tmp;
            }

            /*@ {
                if(j < i) {
                    close ints(arr+j,1,_);
                    ints_join(arr);
                } else if(j == i) {
                    assert  arr[ ..j] |-> ?pref1
                        &*& arr[j..i] |-> ?pref2
                        &*& arr[i] |-> ?x
                        &*& arr[i+1..n] |-> ?suff;
                    assert pref2 == nil;
                    assert !!all_le(x,pref1);
                    if(!sorted(append(pref1,{x}))) {
                        switch(not_sorted_append(pref1,{x})) {
                        case pair(a,b):
                            assert b == x;
                            forall_elim(pref1,(ge)(b),a);
                            assert false;
                        }
                    }
                } else {
                    close ints(arr+j,1,_);
                    ints_join(arr+i+1);
                }


            } @*/
        }
    }

    /*@ {
        assert i == n;
        if(n > 0) {
            close ints(arr+i-1,1,_);
            ints_join(arr);
        }
    } @*/

    return;
}

