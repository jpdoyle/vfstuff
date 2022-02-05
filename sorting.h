#ifndef VFUTIL_SORTING_H
#define VFUTIL_SORTING_H

/*@ #include "sorting.gh" @*/
void isort(int* arr, int n);
    /*@ requires arr[..n] |-> ?l; @*/
    /*@ ensures  arr[..n] |-> ?new_l &*& !!sorted(new_l)
            &*&  !!is_permutation2(l,new_l); @*/
    /*@ terminates; @*/

void heapsort(int* arr, int n);
    /*@ requires arr[..n] |-> ?l; @*/
    /*@ ensures  arr[..n] |-> ?new_l &*& !!sorted(new_l)
            &*&  !!is_permutation2(l,new_l); @*/
    /*@ terminates; @*/

#endif

