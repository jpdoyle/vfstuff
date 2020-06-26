#include <stddef.h>
/*@ #include "termination.gh" @*/
/*@ #include "sorting.gh" @*/

//typedef void slowsort_t(int* arr, size_t i, size_t j);
//    /*@ requires arr[i..j] |-> ?l
//      ; @*/
//    /*@ ensures  arr[i..j] |-> ?new_l &*& !!sorted(new_l)
//            &*&  !!is_permutation2(l,new_l); @*/
//    /*@ terminates; @*/

void slowsort_inner(int* arr, size_t i, size_t j)
  /* @ : slowsort_t @*/
    /*@ requires arr[i..j] |-> ?l
            &*&  [3]call_perm_level(currentThread,pair(lt, j-i), {slowsort_inner})
      ; @*/
    /*@ ensures  arr[i..j] |-> ?new_l &*& !!sorted(new_l)
            &*&  !!is_permutation2(l,new_l); @*/
    /*@ terminates; @*/
{
  /* For recursion */
  /*@ is_wf_lt(); @*/

  if(i >= j || i+1 >= j) {
    /*@ leak [?f]call_perm_level(currentThread,_,_); @*/
    return;
  } else {
    /*@ div_rem(j-i,2); @*/
    size_t m = i+(j-i)/2;

    /*@ {
      assert i < m;
      assert m < j;
      ints_split(arr+i,m-i);
    } @*/

    /*@ assert arr[i..m] |-> ?pref; @*/
    /*@ assert arr[m..j] |-> ?suff; @*/
    /*@ {
      assert maximum(l) == maximum(append(pref,suff));
      maximum_append(pref,suff);
      assert maximum(l) == max_of(maximum(pref),maximum(suff));

      call_perm_level_weaken(1,lt,j-i, {slowsort_inner}, 4,m-i);
      consume_call_perm_level_for(slowsort_inner);
    } @*/

    slowsort_inner(arr,i,m);
    /*@ assert arr[i..m] |-> ?pref_sorted; @*/

    /*@ {
      call_perm_level_weaken(1,lt,j-i, {slowsort_inner}, 4,j-m);
      consume_call_perm_level_for(slowsort_inner);
    } @*/

    slowsort_inner(arr,m,j);
    /*@ assert arr[m..j] |-> ?suff_sorted; @*/

    /*@ {
      maximum_permutation(pref,pref_sorted);
      assert maximum(pref_sorted) == maximum(pref);
      maximum_permutation(suff,suff_sorted);
      assert maximum(suff_sorted) == maximum(suff);

      ints_split(arr+i,m-1-i);
      ints_split(arr+m,(j-1)-m);
      open ints(arr+(m-1),_,_);
      open ints(arr+j-1,_,_);
    } @*/

    if(arr[m-1] > arr[j-1]) {
      int tmp = arr[j-1];
      arr[j-1] = arr[m-1];
      arr[m-1] = tmp;
    }

    /*@ assert arr[i..m-1] |-> ?pref_start; @*/
    /*@ assert arr[m..j-1] |-> ?suff_start; @*/
    /*@ assert arr[m-1]    |-> ?pref_last;  @*/
    /*@ assert arr[j-1]    |-> ?last;       @*/

    /*@ {
      close ints(arr+(m-1),1,_);
      close ints(arr+(j-1),1,_);
      ints_join(arr+i);
      ints_join(arr+m);
      ints_join(arr+i);

      assert maximum(l) == last;
      assert arr[i..j] |-> ?chunked;

      if(!is_permutation2(append(pref_sorted,suff_sorted), chunked))
      {
        int cx = not_permutation2(append(pref_sorted,suff_sorted),
                          chunked);
        assert false;
      }

      append_assoc(append(pref_start,cons(pref_last,nil)),
                suff_start,cons(last,nil));
      assert take(j-1-i,chunked)
        == append(append(pref_start,cons(pref_last,nil)), suff_start);

      ints_split(arr+i,j-1-i);

    } @*/

    /*@ assert arr[i..j-1] |-> ?orig_start; @*/

    /*@ {
      permutation2_append(pref,pref_sorted,suff,suff_sorted);
      permutation2_transitive(append(pref,suff),
        append(pref_sorted,suff_sorted),
        append(orig_start,cons(last,nil)));
      assert !!is_permutation2(append(orig_start,cons(last,nil)),l);

      call_perm_level_weaken(1,lt,j-i, {slowsort_inner}, 4,j-1-i);
      consume_call_perm_level_for(slowsort_inner);
    } @*/
    slowsort_inner(arr,i,j-1);

    /*@ {
      assert arr[i..j-1] |-> ?start;

      permutation2_append(orig_start,start,cons(last,nil),cons(last,nil));
      permutation2_transitive(l,append(orig_start,cons(last,nil)),
        append(start,cons(last,nil)));

      maximum_permutation(l,append(start,cons(last,nil)));
      assert maximum(append(start,cons(last,nil))) == last;

      ints_join(arr+i);
      sorted_max_extend(start,last);
    } @*/
  }
}

void slowsort(int* arr, size_t i, size_t j)
    /*@ requires arr[i..j] |-> ?l; @*/
    /*@ ensures  arr[i..j] |-> ?new_l &*& !!sorted(new_l)
            &*&  !!is_permutation2(l,new_l); @*/
    /*@ terminates; @*/
{
    /*@ {
        produce_call_below_perm_();
        call_below_perm__elim(slowsort);
        call_perm_level(3, pair(lt,j-i), {slowsort_inner});
    } @*/
    slowsort_inner(arr,i,j);
}

