#include "sorting.h"

void isort(int* arr, int n)
    /*@ requires arr[..n] |-> ?l; @*/
    /*@ ensures  arr[..n] |-> ?new_l &*& !!sorted(new_l)
            &*&  !!is_permutation2(l,new_l); @*/
    /*@ terminates; @*/
{
    int i,j;
    for(i = n; i > 0; --i)
        /*@ invariant arr[..i]  |-> ?prefix
                 &*&  arr[i..n] |-> ?suffix
                 &*&  !!sorted(suffix)
                 &*&  !!is_permutation2(append(prefix,suffix),l)
                 &*&  i >= 0 &*& i <= n; @*/
        /*@ decreases i; @*/
    {
        /*@ ints_split(arr,i-1); @*/
        /*@ assert arr[i-1] |-> ?v; @*/
        for(j=i-1; j+1 < n; ++j)
            /*@ requires j >= 0 &*& j+1 <= n
                    &*& arr[j+1..n] |-> ?ins_suffix
                    &*& arr[j]      |-> ?ins_v
                    &*& !!sorted(ins_suffix); @*/
            /*@ ensures arr[old_j..n] |-> ?new_l
                    &*& !!sorted(new_l)
                    &*& !!is_permutation2(cons(ins_v,ins_suffix),new_l)
                    ; @*/
            /*@ decreases n-j-1; @*/
        {
            /*@ open ints(arr+j+1,_,_); @*/
            if(arr[j] <= arr[j+1]) { break; }

            int tmp = arr[j+1];
            arr[j+1] = arr[j];
            arr[j] = tmp;

            /*@ recursive_call(); @*/
            /*@ {
                assert arr[old_j]      |-> ?next_v;
                assert arr[old_j+1..n] |-> ?next_suffix;

                list<int> swap_suffix = cons(ins_v, tail(ins_suffix));

                permutation2_transitive(
                    cons(next_v,next_suffix),
                    cons(next_v,swap_suffix),
                    cons(ins_v,ins_suffix));
                all_ge_permutation(next_v, swap_suffix, next_suffix);
            } @*/

        }
        /*@ {
            assert arr[..(i-1)]  |-> ?new_prefix;
            assert arr[(i-1)..n] |-> ?new_suffix;
            permutation2_transitive(append(new_prefix,new_suffix),
                                   append(new_prefix,cons(v,suffix)),l);
        } @*/
    }
}

