#include <stddef.h>
#include <limits.h>
#include "sorting.h"
/*@ #include "termination.gh" @*/

#if 1
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif

void merge(int* out, size_t ln, size_t rn, int* l, int* r)
    /*@ requires out[..(ln+rn)] |-> _
            &*&  [?fl]l[..ln] |-> ?ls
            &*&  [?fr]r[..rn] |-> ?rs
            &*&  !!sorted(ls)
            &*&  !!sorted(rs)
            ;
      @*/
    /*@ ensures  out[..(ln+rn)] |-> ?outs
            &*&  [ fl]l[..ln] |->  ls
            &*&  [ fr]r[..rn] |->  rs
            &*&  !!sorted(outs)
            &*&  !!is_permutation(outs,append(ls,rs));
      @*/
    /*@ terminates; @*/
{
    /*@ { ALREADY_PROVEN() } @*/

    /*@ ints_limits(out); @*/
    size_t li = 0, ri = 0;
    while(li < ln || ri < rn)
        /*@ requires out[(li+ri)..(ln+rn)] |-> _
                &*&  [fl]l[li..ln] |-> ?loop_ls
                &*&  [fr]r[ri..rn] |-> ?loop_rs
                &*&  !!sorted(loop_ls)
                &*&  !!sorted(loop_rs)
                &*&  li <= ln
                &*&  ri <= rn
                ;
        @*/
        /*@ ensures  out[(old_li+old_ri)..(ln+rn)] |-> ?loop_outs
                &*&  [fl]l[old_li..ln] |->  loop_ls
                &*&  [fr]r[old_ri..rn] |->  loop_rs
                &*&  !!sorted(loop_outs)
                &*&  !!is_permutation(loop_outs,append(loop_ls,loop_rs));
        @*/
        /*@ decreases ln+rn - (li + ri); @*/
    {
        bool pick_l = true;
        if(li < ln && ri < rn) {
            /*@ open [fl]ints(l+li,_,_); @*/
            /*@ open [fr]ints(r+ri,_,_); @*/
            pick_l = (l[li] < r[ri]);
        } else if(ri < rn) {
            /*@ open [fr]ints(r+ri,_,_); @*/
            pick_l = false;
        } /*@ if(li < ln && ri >= rn) {
            open [fl]ints(l+li,_,_);
        } @*/

        int next_val;
        size_t out_ix = li + ri;
        if(pick_l) {
            next_val = l[li];
            ++li;
        } else {
            next_val = r[ri];
            ++ri;
        }
        out[out_ix] = next_val;

        /*@ assert [fl]l[li..ln] |-> ?next_ls; @*/
        /*@ assert [fr]r[ri..rn] |-> ?next_rs; @*/
        /*@ {
            list<int> next_loop = append(next_ls,next_rs);
            list<int> this_loop = append(loop_ls,loop_rs);
            if(!is_permutation(cons(next_val,next_loop), this_loop)) {
                int cx = not_permutation2(cons(next_val,next_loop),this_loop);
                assert false;
            }
            if(!all_ge(next_val, next_loop)) {
                int cx = not_forall(next_loop,(le)(next_val));

                switch(loop_ls) {
                case nil: assert false;
                case cons(lv,lvs):
                    switch(loop_rs) {
                    case nil: assert false;
                    case cons(rv,rvs):
                        if(mem(cx,lvs)) {
                            forall_elim(lvs,(le)(lv),cx);
                        } else if(mem(cx,rvs)) {
                            forall_elim(rvs,(le)(rv),cx);
                        }
                    }
                }

                assert false;
            }
        } @*/

        /*@ recursive_call(); @*/
        /*@ {
            assert out[(old_li+old_ri+1)..(ln+rn)] |-> ?final_outs;
            assert !!sorted(final_outs);
            assert !!is_permutation(final_outs,append(next_ls,next_rs));
            assert out[(old_li+old_ri)..(ln+rn)]
                |-> cons(next_val,final_outs);
            if(!sorted(cons(next_val,final_outs))) {
                all_ge_permutation(next_val,final_outs,append(next_ls,next_rs));
                assert false;
            }
            permutation2_transitive(append(loop_ls,loop_rs),
                cons(next_val,append(next_ls,next_rs)),
                cons(next_val,final_outs));
        } @*/
    }

}

void mergesort_inner(int* arr, size_t n, int* scratch)
    /*@ requires arr[..n] |-> ?l &*& scratch[..n] |-> _
            &*&  [2]call_perm_level(currentThread,pair(lt, n), {mergesort_inner})
      ; @*/
    /*@ ensures  arr[..n] |-> ?new_l &*& scratch[..n] |-> _
            &*&  !!sorted(new_l)
            &*&  !!is_permutation2(l,new_l); @*/
    /*@ terminates; @*/
{
    /* For recursion */
    /*@ is_wf_lt(); @*/
    if(n <= 1) {
        /*@ leak [?f]call_perm_level(currentThread,_,_); @*/
        /*@ if(!sorted(l)) {
            TRIVIAL_LIST2(l)
            assert false;
        } @*/
        return;
    }

    size_t mid = n/2;

    /*@ {
        div_rem(n,2);
        ints_limits(arr);
        ints_limits(scratch);
        ints_split(arr,mid);
        ints_split(scratch,mid);
    } @*/

    /*@ assert arr[..mid]  |-> ?orig_pref; @*/
    /*@ assert arr[mid..n] |-> ?orig_suff; @*/

    /*@ {
      call_perm_level_weaken(1,lt,n, {mergesort_inner}, 3,mid);
      consume_call_perm_level_for(mergesort_inner);
    } @*/

    mergesort_inner(arr,mid,scratch);

    /*@ {
      call_perm_level_weaken(1,lt,n, {mergesort_inner}, 3,n-mid);
      consume_call_perm_level_for(mergesort_inner);
    } @*/

    mergesort_inner(arr+mid,n-mid,scratch+mid);

    /*@ assert arr[..mid]  |-> ?pref; @*/
    /*@ assert arr[mid..n] |-> ?suff; @*/

    /*@ ints_join(scratch); @*/
    merge(scratch,mid,n-mid,arr,arr+mid);

    /*@ {
        assert scratch[..n] |-> ?final;

        permutation2_append(pref,orig_pref,suff,orig_suff);

        permutation2_transitive(
            append(orig_pref,orig_suff),
            append(pref,suff),
            final);
    } @*/

    /*@ ints_join(arr); @*/
    for(size_t i = 0; i < n; ++i)
        /*@ requires arr[i..n] |-> _ &*& scratch[i..n] |-> ?vals; @*/
        /*@ ensures  arr[old_i..n] |-> vals &*& scratch[old_i..n] |-> _; @*/
        /*@ decreases n-i; @*/
    {
        /*@ open ints(arr+i,_,_); @*/
        /*@ open ints(scratch+i,_,_); @*/
        arr[i] = scratch[i];
    }
}

void mergesort(int* arr, size_t n, int* scratch)
    /*@ requires arr[..n] |-> ?l &*& scratch[..n] |-> _; @*/
    /*@ ensures  arr[..n] |-> ?new_l &*& scratch[..n] |-> _
            &*&  !!sorted(new_l)
            &*&  !!is_permutation2(l,new_l); @*/
    /*@ terminates; @*/
{
    /*@ {
        produce_call_below_perm_();
        call_below_perm__elim(mergesort);
        call_perm_level(2, pair(lt,n), {mergesort_inner});
    } @*/
    mergesort_inner(arr,n,scratch);
}


