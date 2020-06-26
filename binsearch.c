//@ #include "lists.gh"
//@ #include <arrays.gh>

/*@

fixpoint bool is_above_eq(int x, int y) { return y >= x; }
fixpoint bool is_above(int x, int y) { return y > x; }
fixpoint bool is_below(int x, int y) { return y < x; }

fixpoint bool is_sorted(list<int> l) {
    switch(l) {
    case nil: return true;
    case cons(x,xs):
        return forall(xs,(is_above_eq)(x)) && is_sorted(xs);
    }
}

fixpoint bool all_above_eq(int x, list<int> l) {
    return forall(l,(is_above_eq)(x));
}

lemma_auto(is_sorted(append(a,b)))
//lemma
void is_sorted_append(list<int> a, list<int> b)
    requires true;
    ensures  is_sorted(append(a,b))
        == (is_sorted(a) && is_sorted(b)
            && forall(a,(flip)(all_above_eq,b)));
{
    switch(a) {
    case nil:
    case cons(x,xs):
        is_sorted_append(xs,b);

        if(is_sorted(append(a,b))) {
            assert !!is_sorted(append(xs,b));
            assert !!forall(append(xs,b), (is_above_eq)(x));
            assert !!forall(xs, (flip)(all_above_eq,b));
            assert !!is_sorted(b);
            assert !!is_sorted(xs);

            BEGIN_FORALL(int, v, xs, (is_above_eq)(x))
                forall_elim(append(xs,b), (is_above_eq)(x), v);
            END_FORALL()

            assert !!is_sorted(a);

            BEGIN_FORALL(int, v, a, (flip)(all_above_eq,b))
                if(v != x) {
                    forall_elim(xs, (flip)(all_above_eq,b),v);
                } else {
                    BEGIN_FORALL(int, bv, b,(is_above_eq)(v))
                        forall_elim(append(xs,b), (is_above_eq)(x), bv);
                    END_FORALL()
                }
            END_FORALL()

            assert !!forall(a,(flip)(all_above_eq,b));

        } else if(is_sorted(a) && is_sorted(b)
                && forall(a,(flip)(all_above_eq,b))) {

            assert !!is_sorted(append(xs,b));

            forall_elim(a,(flip)(all_above_eq,b),x);
            BEGIN_FORALL(int, v, append(xs,b), (is_above_eq)(x))
                if(mem(v,xs)) {
                    forall_elim(xs,(is_above_eq)(x),v);
                } else {
                    forall_elim(b,(is_above_eq)(x),v);
                }
            END_FORALL()

            assert false;
        }
    }
}

  @*/

//int binsearch(int x, int* A, int n)
//    /*@ requires [?f]A[..n] |-> ?elems
//            &*&  !!is_sorted(elems);
//      @*/
//    /*@ ensures  [ f]A[..n] |-> elems
//            &*&  result == -1
//                 ? !mem(x,elems)
//                 : result >= 0 &*& result < n
//                 &*& nth_of(result,elems) == some(x)
//            ;
//      @*/
//    //@ terminates;
//
//{
//    int lower = 0;
//    int upper = n;
//    while(lower < upper)
//        /*@ invariant 0 <= lower &*& lower <= upper &*& upper <= n
//                  &*& [f]A[0..lower]     |-> ?gt_seg
//                  &*& [f]A[lower..upper] |-> ?mid_seg
//                  &*& [f]A[upper..n]     |-> ?le_seg
//                  &*& !!is_sorted(append(gt_seg,mid_seg))
//                  &*& !!is_sorted(append(mid_seg,le_seg))
//                  &*& !!is_sorted(append(gt_seg,{x}))
//                  &*& !!is_sorted(append({x},le_seg))
//                  &*& append(append(gt_seg,mid_seg),le_seg) == elems
//                  &*& !!is_sorted(elems)
//                  &*& !mem(x,gt_seg)
//                  &*& mem(x,elems)
//                    == (mem(x,mid_seg)
//                        || safe_head(le_seg) == some(x))
//                  ;
//          @*/
//        //@ decreases upper-lower;
//    {
//        //@ open ints(A+lower,_,_);
//
//        if(A[lower] == x) {
//            /*@ {
//                close [f]ints(A+lower, upper-lower, mid_seg);
//                ints_join(A);
//                ints_join(A);
//                nth_append_r(gt_seg,mid_seg,0);
//                nth_append(append(gt_seg,mid_seg),le_seg,lower);
//
//                assert nth_of(0,mid_seg) == some(x);
//                nth_of_is_nth(lower,append(gt_seg,mid_seg));
//                nth_of_is_nth(lower,
//                    append(append(gt_seg,mid_seg),le_seg));
//                assert nth_of(lower,append(gt_seg,mid_seg)) == some(x);
//                assert nth_of(lower,
//                    append(append(gt_seg,mid_seg),le_seg)) == some(x);
//                assert nth_of(lower,elems) == some(x);
//            } @*/
//
//            return lower;
//        }
//        //@ close [f]ints(A+lower, upper-lower, mid_seg);
//
//        //@ div_rem(upper-lower,2);
//        int mid = lower + (upper-lower)/2;
//
//        //@ int midind = mid-lower;
//        /*@ {
//            //div_sign(upper-lower,2);
//            note_eq((A + lower) + midind, A + mid);
//            note_eq(A + mid + (upper-lower-midind), A + upper);
//            assert lower <= mid;
//            assert mid <= upper;
//
//            ints_split(A+lower,midind);
//            assert mid_seg
//                == append(take(midind,mid_seg),
//                          drop(midind,mid_seg));
//
//            append_assoc(gt_seg,
//                take(midind,mid_seg), drop(midind,mid_seg));
//
//            append_assoc(
//                take(midind,mid_seg), drop(midind,mid_seg),
//                le_seg);
//
//            assert !!is_sorted(
//                append(gt_seg, take(midind,mid_seg)));
//
//            cons_head_tail(drop(midind,mid_seg));
//            append_assoc(append(gt_seg,
//                take(midind,mid_seg)),
//                {head(drop(midind,mid_seg))},
//                tail(drop(midind,mid_seg)));
//
//            append_assoc(gt_seg,mid_seg,le_seg);
//            append_assoc(gt_seg,
//                take(midind,mid_seg),
//                drop(midind,mid_seg));
//            append_assoc(
//                take(midind,mid_seg),
//                drop(midind,mid_seg), le_seg);
//            append_assoc(gt_seg,
//                take(midind,mid_seg),
//                append(drop(midind,mid_seg), le_seg));
//
//            assert !!is_sorted(
//                append(append(gt_seg, take(midind,mid_seg)),
//                       {head(drop(midind,mid_seg))}));
//
//            open ints(A+mid,_,_);
//
//            assert [f]A[mid] |-> head(drop(midind,mid_seg));
//        } @*/
//
//        if(A[mid] < x) {
//            lower = mid+1;
//
//            /*@ {
//                ints_join(A);
//                close [f]ints(A+mid,1,_);
//                ints_join(A);
//                assert [f]A[..lower] |-> ?new_gt;
//                assert [f]A[lower..upper] |-> ?new_mid;
//                assert !!is_sorted(new_gt);
//                assert !!is_sorted(new_mid);
//                assert !!is_sorted(append(new_gt,new_mid));
//
//                assert !!is_sorted({x});
//                assert !!is_sorted(new_gt);
//                assert head(drop(midind,mid_seg)) < x;
//
//                BEGIN_FORALL(int, v, new_gt,
//                        (flip)(all_above_eq, {x}))
//                    if(v != head(drop(midind,mid_seg))) {
//                        forall_elim(
//                            append(gt_seg, take(midind,mid_seg)),
//                            (flip)(all_above_eq,
//                                   {head(drop(midind,mid_seg))}),
//                            v);
//                    }
//                END_FORALL()
//
//                assert !!is_sorted(append(new_gt,{x}));
//
//                if(mem(x,new_gt)) {
//                    forall_elim(
//                        append(gt_seg, take(midind,mid_seg)),
//                        (flip)(all_above_eq,
//                                {head(drop(midind,mid_seg))}),
//                        x);
//                    assert false;
//                }
//            } @*/
//
//        } else {
//            upper = mid;
//
//            /*@ {
//                close [f]ints(A+upper,1,_);
//                if(le_seg != {}) {
//                    ints_join(A+upper);
//                    ints_join(A+upper);
//                }
//
//                assert [f]A[..lower]      |-> ?new_gt;
//                assert [f]A[lower..upper] |-> ?new_mid;
//                assert [f]A[upper..n]     |-> ?new_le;
//                assert !!is_sorted(new_gt);
//                assert !!is_sorted(new_mid);
//                assert !!is_sorted(new_le);
//                assert !!is_sorted(append(new_mid,new_le));
//
//                //append_assoc(
//
//                assert !!is_sorted({x});
//                assert !!is_sorted(new_le);
//                assert head(drop(midind,mid_seg)) >= x;
//
//                BEGIN_FORALL(int, v, new_le,
//                        (is_above_eq)(x))
//                    if(v != head(drop(midind,mid_seg))) {
//                        forall_elim(
//                            append(drop(midind,mid_seg), le_seg),
//                            (is_above_eq)
//                                (head(drop(midind,mid_seg))),
//                            v);
//                    }
//                END_FORALL()
//
//                assert !!is_sorted(append({x},new_le));
//
//                if(mem(x,elems) && !mem(x,new_mid)) {
//                    assert !!mem(x,new_le);
//                    forall_elim(
//                        append(drop(midind,mid_seg), le_seg),
//                        (is_above_eq)
//                            (head(drop(midind,mid_seg))),
//                        x);
//                    if(head(drop(midind,mid_seg)) != x)
//                        assert false;
//                }
//            } @*/
//        }
//    }
//
//    //@ assert lower == upper;
//    //@ open ints(A+upper,_,_);
//    if(lower != n && A[lower] == x) {
//        return lower;
//        /*@ {
//            nth_append_r(gt_seg,le_seg,0);
//            assert mid_seg == {};
//
//            assert nth_of(0,le_seg) == some(x);
//            nth_of_is_nth(lower,
//                append(append(gt_seg,mid_seg),le_seg));
//
//            close [f]ints(A+upper,n-upper,_);
//            ints_join(A);
//            ints_join(A);
//        } @*/
//    }
//    return -1;
//    /*@ {
//        close [f]ints(A+upper,n-upper,_);
//        ints_join(A);
//        ints_join(A);
//    } @*/
//}

/*@

lemma_auto(nth_of(index_of(x,l),l))
void index_of_mem_length_1<t>(t x, list<t> l)
    requires length(l) <= 1;
    ensures  (nth_of(0,l) == some(x))
        == (nth_of(index_of(x,l),l) == some(x));
    //some(x)) == mem(x,l);
{ TRIVIAL_LIST2(l) }

  @*/

//int binsearch_tuerk(int x, int* A, int n)
//    /*@ requires [?f]A[..n] |-> ?elems
//            &*&  !!is_sorted(elems);
//      @*/
//    /*@ ensures  [ f]A[..n] |-> elems
//            &*&  result == -1
//                 ? !mem(x,elems)
//                 : result >= 0 &*& result < n
//                 &*& nth_of(result,elems) == some(x)
//            ;
//      @*/
//    //@ terminates;
//
//{
//    int lower = 0;
//    int upper = n;
//    /*@ if(n <= 1 &&
//            (nth_of(0,elems) == some(x)) != mem(x,elems)) {
//        switch(nth_of(0,elems)) {
//        case none: assert false;
//        case some(e):
//            option_eq(e,x);
//            TRIVIAL_LIST2(elems)
//            assert false;
//        }
//        assert false;
//    } @*/
//
//    while(lower < upper)
//        /*@ requires 0 <= lower &*& lower <= upper &*& upper <= n
//                  &*& let(upper == n ? n : upper+1, ?maxind)
//                  &*& [f]A[lower..maxind] |-> ?mid_seg
//                  &*& !!is_sorted(mid_seg)
//                  &*& mid_seg == drop(lower,take(maxind,elems))
//                  &*& mem(x,elems) == mem(x,mid_seg)
//                  &*& nth_of(0,mid_seg) == nth_of(lower,elems)
//                  &*& (length(mid_seg) != 1 ||
//                       (nth_of(0,mid_seg) == some(x)) == mem(x,elems)
//                      )
//                  ;
//          @*/
//        /*@ ensures [f]A[old_lower..maxind] |-> mid_seg
//                  &*& upper == lower
//                  &*& old_lower <= lower &*& lower <= old_upper
//                  &*& nth_of(lower-old_lower,mid_seg)
//                    == nth_of(lower,elems)
//                  &*& mem(x,elems) == (nth_of(lower,elems) == some(x))
//                  ;
//          @*/
//        //@ decreases upper-lower;
//    {
//        //@ note(maxind <= n);
//        //@ open ints(A+lower,_,_);
//        /*@ int newmaxind = maxind; @*/
//
//        if(A[lower] == x) {
//            upper = lower;
//            /*@ {
//                newmaxind = upper+1;
//                assert upper != n;
//                assert maxind == length(take(maxind,elems));
//                assert lower < maxind;
//                assert lower < length(take(maxind,elems));
//                nth_drop(0,lower,take(maxind,elems));
//
//                nth_of_is_nth(lower,elems);
//
//                note_eq(nth_of(lower,elems),some(x));
//            } @*/
//            break;
//        }
//        //@ close [f]ints(A+lower, maxind-lower, mid_seg);
//
//        //@ div_rem(upper-lower,2);
//        int mid = lower + (upper-lower)/2;
//        //@ int midind = mid-lower;
//        /*@ {
//            ints_split(A+lower,midind);
//            open ints(A+mid,_,_);
//            assert mid_seg ==
//                append(take(midind+1,mid_seg),drop(midind+1,mid_seg));
//            assert take(midind+1,mid_seg) ==
//                append(take(midind,take(midind+1,mid_seg)),
//                       drop(midind,take(midind+1,mid_seg)));
//            assert take(midind+1,mid_seg) ==
//                append(take(midind,mid_seg),
//                       take(1,drop(midind,mid_seg)));
//            assert take(midind+1,mid_seg) ==
//                append(take(midind,mid_seg),
//                    {nth(0,drop(midind,mid_seg))});
//            nth_drop(0,midind,mid_seg);
//            assert take(midind+1,mid_seg) ==
//                append(take(midind,mid_seg),{nth(midind,mid_seg)});
//            append_assoc(take(midind,mid_seg),{nth(midind,mid_seg)},
//                drop(midind+1,mid_seg));
//        } @*/
//
//        if(A[mid] < x) {
//            //@ close [f]ints(A+mid,1,_);
//            //@ if(lower != mid) { ints_join(A+lower); }
//            lower = mid+1;
//            /*@ {
//                assert [f]A[lower..maxind] |-> ?newmid;
//
//                if(lower < length(elems)) {
//                    nth_drop(midind+1,lower-midind-1,take(maxind,elems));
//                    nth_of_is_nth(midind+1,drop(lower-midind-1,take(maxind,elems)));
//                    nth_of_is_nth(lower,take(maxind,elems));
//                    nth_of_is_nth(lower,elems);
//                    assert nth_of(midind+1,mid_seg)
//                        == nth_of(lower,take(maxind,elems));
//                    nth_take(lower,maxind,elems);
//                    assert nth_of(midind+1,mid_seg)
//                        == nth_of(lower,elems);
//                    nth_drop(0,lower,take(maxind,elems));
//                    nth_of_is_nth(0,newmid);
//                    assert nth_of(0,newmid)
//                        == nth_of(lower,elems);
//                }
//
//                if(newmid != drop(lower,take(maxind,elems))) {
//                    assert newmid == tail(drop(midind,mid_seg));
//                    drop_n_of_drop_m(midind,lower,take(maxind,elems));
//                    assert newmid == tail(drop(mid,take(maxind,elems)));
//                    cons_head_tail(drop(mid,take(maxind,elems)));
//                    assert newmid == drop(1,drop(mid,take(maxind,elems)));
//                    drop_n_of_drop_m(1,mid,take(maxind,elems));
//                    assert false;
//                }
//
//                if(mem(x,elems) && !mem(x,newmid)) {
//                    assert newmid == drop(midind+1,mid_seg);
//                    assert mid_seg ==
//                        append(take(midind+1,mid_seg),newmid);
//                    assert take(midind,take(midind+1,mid_seg))
//                        == take(midind,mid_seg);
//                    assert drop(midind,take(midind+1,mid_seg))
//                        == take(1,drop(midind,mid_seg));
//                    assert drop(midind,take(midind+1,mid_seg))
//                        == {nth(0,drop(midind,mid_seg))};
//
//                    assert mid_seg ==
//                        append(append(take(midind,mid_seg),
//                                    {nth(0,drop(midind,mid_seg))}),
//                               newmid);
//
//                    assert nth(0,drop(midind,mid_seg))
//                        == nth(midind,mid_seg);
//                    assert x > nth(midind,mid_seg);
//                    assert !!mem(x,take(midind+1,mid_seg));
//
//                    take_append(midind+1,take(midind+1,mid_seg),newmid);
//
//                    assert take(midind+1,mid_seg)
//                        == append(take(midind,mid_seg),
//                                    {nth(midind,mid_seg)});
//                    assert !!is_sorted(append(take(midind,mid_seg),
//                                    {nth(midind,mid_seg)}));
//                    forall_elim(take(midind,mid_seg),
//                        (flip)(all_above_eq, {nth(midind,mid_seg)}), x);
//                    assert false;
//                }
//            } @*/
//        } else {
//            upper = mid;
//            //@ close [f]ints(A+mid,1,_);
//            //@ if(lower != mid) { ints_join(A+lower); }
//
//            /*@ {
//                newmaxind = upper == n ? n : upper+1;
//                assert [f]A[lower..newmaxind] |-> ?newmid;
//
//                if(newmid != drop(lower,take(newmaxind,elems))) {
//                    assert newmid == append(take(midind,mid_seg),
//                        {nth(midind,mid_seg)});
//                    assert newmid == take(midind+1,mid_seg);
//                    assert newmid
//                        == take(midind+1,drop(lower,
//                            take(maxind,elems)));
//                    assert midind+1+lower >= lower;
//                    drop_n_of_take_m(lower,midind+1+lower,
//                        take(maxind,elems));
//                    assert drop(lower,take(midind+1+lower,
//                            take(maxind,elems)))
//                        == take(midind+1,drop(lower,
//                            take(maxind,elems)));
//                    assert newmid
//                        == drop(lower,take(midind+1+lower,
//                            take(maxind,elems)));
//                    assert newmid
//                        == drop(lower,take(upper+1,
//                            take(maxind,elems)));
//                    assert newmid
//                        == drop(lower,take(newmaxind,
//                            elems));
//                    assert false;
//                }
//
//                if(mem(x,elems) && !mem(x,newmid)) {
//                    assert newmid == take(midind+1,mid_seg);
//                    assert mid_seg ==
//                        append(newmid,drop(midind+1,mid_seg));
//
//                    assert nth(0,drop(midind,mid_seg))
//                        == nth(midind,mid_seg);
//                    assert x < nth(midind,mid_seg);
//                    assert !!mem(x,drop(midind+1,mid_seg));
//
//                    assert !!is_sorted(drop(midind,mid_seg));
//                    assert drop(midind,mid_seg)
//                        == append({nth(midind,mid_seg)},
//                               drop(midind+1,mid_seg));
//                    assert !!is_sorted(
//                        append({nth(midind,mid_seg)},
//                               drop(midind+1,mid_seg)));
//
//                    //take_append(midind+1,take(midind+1,mid_seg),newmid);
//
//                    //assert take(midind+1,mid_seg)
//                    //    == append(take(midind,mid_seg),
//                    //                {nth(midind,mid_seg)});
//                    //assert !!is_sorted(append(take(midind,mid_seg),
//                    //                {nth(midind,mid_seg)}));
//                    forall_elim(drop(midind+1,mid_seg),
//                        (is_above_eq)(nth(midind,mid_seg)), x);
//                    assert false;
//                }
//            } @*/
//        }
//
//        /*@ assert [f]A[lower..newmaxind] |-> ?newmid; @*/
//        /*@ if(newmaxind - lower <= 1 &&
//               !((nth_of(0,newmid) == some(x)) == mem(x,elems))) {
//            switch(nth_of(0,newmid)) {
//            case none: assert false;
//            case some(e):
//                option_eq(e,x);
//                TRIVIAL_LIST2(newmid)
//                assert false;
//            }
//            assert false;
//        } @*/
//
//        //@ recursive_call();
//        //@ if(old_upper-old_lower > 1) { ints_join(A+old_lower); }
//
//        /*@ if(lower < length(elems)) {
//            nth_drop(lower-old_lower,old_lower,take(maxind,elems));
//            nth_of_is_nth(lower-old_lower,drop(old_lower,take(maxind,elems)));
//            nth_of_is_nth(lower,take(maxind,elems));
//            nth_of_is_nth(lower,elems);
//            assert nth_of(lower-old_lower,mid_seg)
//                == nth_of(lower,take(maxind,elems));
//            nth_take(lower,maxind,elems);
//            assert nth_of(lower-old_lower,mid_seg)
//                == nth_of(lower,elems);
//        } @*/
//    }
//
//    //@ assert lower == upper;
//    //@ ints_split(A,upper);
//    //@ open ints(A+lower,_,_);
//    //@ if(lower < n) { nth_of_is_nth(lower,elems); }
//    if(lower != n && A[lower] == x) {
//        return lower;
//        /*@ {
//            close [f]ints(A+lower,n-lower,_);
//            if(lower != 0) { ints_join(A); }
//        } @*/
//    }
//    //@ assert nth_of(0,drop(lower,elems)) != some(x);
//
//    /*@ if(lower < length(elems)) {
//        nth_drop(0,lower,elems);
//        nth_of_is_nth(0,drop(lower,elems));
//        nth_of_is_nth(lower,elems);
//    } @*/
//
//    //@ assert !mem(x,elems);
//    return -1;
//    /*@ {
//        close [f]ints(A+lower,n-lower,_);
//        if(lower != 0) { ints_join(A); }
//    } @*/
//}

//int binsearch_tuerk2(int x, int* A, int n)
//    /*@ requires [?f]A[..n] |-> ?elems
//            &*&  !!is_sorted(elems);
//      @*/
//    /*@ ensures  [ f]A[..n] |-> elems
//            &*&  result == -1
//                 ? !mem(x,elems)
//                 : result >= 0 &*& result < n
//                 &*& nth_of(result,elems) == some(x)
//            ;
//      @*/
//    //@ terminates;
//
//{
//    int lower = 0;
//    int upper = n;
//    //@ TRIVIAL_LIST(elems)
//    /*@ if(n <= 1) {
//        if(((mem(x,elems) !=
//            (nth_of(index_of(x,elems),elems) == some(x)))
//            )) {
//        switch(nth_of(0,elems)) {
//        case none: assert false;
//        case some(e):
//            option_eq(e,x);
//            TRIVIAL_LIST2(elems)
//            assert false;
//        }
//        assert false;
//        }
//
//        if(mem(x,elems) && index_of(x,elems) != 0) {
//            TRIVIAL_LIST2(elems)
//            assert false;
//        }
//    } @*/
//
//
//    while(lower < upper)
//        /*@ requires 0 <= lower &*& lower <= upper &*& upper <= n
//                  &*& let(upper == n ? n : upper+1, ?maxind)
//                  &*& [f]A[lower..maxind] |-> ?mid_seg
//                  &*& !!is_sorted(mid_seg)
//                  &*& mid_seg == drop(lower,take(maxind,elems))
//                  &*& mem(x,elems) == mem(x,mid_seg)
//                  &*& (nth_of(index_of(x,mid_seg),mid_seg) == some(x))
//                    == mem(x,mid_seg)
//                  &*& length(mid_seg) == maxind-lower
//                  &*& lower == upper
//                  ? (nth_of(0,mid_seg) == some(x)) ==
//                        mem(x,mid_seg)
//                  : emp
//                  ;
//          @*/
//        /*@ ensures [f]A[old_lower..maxind] |-> mid_seg
//                  &*& old_lower <= lower &*& lower <= old_upper
//                  &*& (nth_of(lower-old_lower,mid_seg) == some(x))
//                    == mem(x,mid_seg)
//                  ;
//          @*/
//        //@ decreases upper-lower;
//    {
//        //@ open ints(A+lower,_,_);
//
//        if(A[lower] == x) {
//            /*@ {
//                assert maxind == length(take(maxind,elems));
//                assert lower < maxind;
//                assert lower < length(take(maxind,elems));
//                nth_drop(0,lower,take(maxind,elems));
//
//                nth_of_is_nth(lower,elems);
//
//                note_eq(nth_of(lower,elems),some(x));
//            } @*/
//            break;
//        }
//        //@ close [f]ints(A+lower, maxind-lower, mid_seg);
//
//        //@ div_rem(upper-lower,2);
//        int mid = lower + (upper-lower)/2;
//        //@ int midind = mid-lower;
//        /*@ {
//            ints_split(A+lower,midind);
//            open ints(A+mid,_,_);
//            assert mid_seg ==
//                append(take(midind+1,mid_seg),drop(midind+1,mid_seg));
//            assert take(midind+1,mid_seg) ==
//                append(take(midind,take(midind+1,mid_seg)),
//                       drop(midind,take(midind+1,mid_seg)));
//            assert take(midind+1,mid_seg) ==
//                append(take(midind,mid_seg),
//                       take(1,drop(midind,mid_seg)));
//            assert take(midind+1,mid_seg) ==
//                append(take(midind,mid_seg),
//                    {nth(0,drop(midind,mid_seg))});
//            nth_drop(0,midind,mid_seg);
//            assert take(midind+1,mid_seg) ==
//                append(take(midind,mid_seg),{nth(midind,mid_seg)});
//            append_assoc(take(midind,mid_seg),{nth(midind,mid_seg)},
//                drop(midind+1,mid_seg));
//        } @*/
//
//        if(A[mid] < x) {
//            //@ close [f]ints(A+mid,1,_);
//            //@ if(lower != mid) { ints_join(A+lower); }
//            lower = mid+1;
//            /*@ {
//                assert [f]A[lower..maxind] |-> ?newmid;
//
//                if(lower < length(elems)) {
//                    nth_drop(midind+1,lower-midind-1,take(maxind,elems));
//                    nth_of_is_nth(midind+1,drop(lower-midind-1,take(maxind,elems)));
//                    nth_of_is_nth(lower,take(maxind,elems));
//                    nth_of_is_nth(lower,elems);
//                    assert nth_of(midind+1,mid_seg)
//                        == nth_of(lower,take(maxind,elems));
//                    nth_take(lower,maxind,elems);
//                    assert nth_of(midind+1,mid_seg)
//                        == nth_of(lower,elems);
//                    nth_drop(0,lower,take(maxind,elems));
//                    nth_of_is_nth(0,newmid);
//                    assert nth_of(0,newmid)
//                        == nth_of(lower,elems);
//                }
//
//                if(newmid != drop(lower,take(maxind,elems))) {
//                    drop_n_of_drop_m(midind,lower,take(maxind,elems));
//                    cons_head_tail(drop(mid,take(maxind,elems)));
//                    drop_n_of_drop_m(1,mid,take(maxind,elems));
//                    assert false;
//                }
//
//                if(mem(x,mid_seg) && !mem(x,newmid)) {
//                    take_append(midind+1,take(midind+1,mid_seg),newmid);
//
//                    forall_elim(take(midind,mid_seg),
//                        (flip)(all_above_eq, {nth(midind,mid_seg)}), x);
//                    assert false;
//                }
//            } @*/
//        } else {
//            upper = mid;
//            //@ close [f]ints(A+mid,1,_);
//            //@ if(lower != mid) { ints_join(A+lower); }
//
//            /*@ {
//                int newmaxind = upper == n ? n : upper+1;
//                assert [f]A[lower..newmaxind] |-> ?newmid;
//
//                if(newmid != drop(lower,take(newmaxind,elems))) {
//                    drop_n_of_take_m(lower,midind+1+lower,
//                        take(maxind,elems));
//                    assert false;
//                }
//
//                if(mem(x,mid_seg) && !mem(x,newmid)) {
//                    forall_elim(drop(midind+1,mid_seg),
//                        (is_above_eq)(nth(midind,mid_seg)), x);
//                    assert false;
//                }
//            } @*/
//        }
//
//        //@ recursive_call();
//        //@ if(old_upper-old_lower > 1) { ints_join(A+old_lower); }
//
//        /*@ if(lower < length(elems)) {
//            nth_drop(lower-old_lower,old_lower,take(maxind,elems));
//            nth_of_is_nth(lower-old_lower,drop(old_lower,take(maxind,elems)));
//            nth_of_is_nth(lower,take(maxind,elems));
//            nth_of_is_nth(lower,elems);
//            assert nth_of(lower-old_lower,mid_seg)
//                == nth_of(lower,take(maxind,elems));
//            nth_take(lower,maxind,elems);
//            assert nth_of(lower-old_lower,mid_seg)
//                == nth_of(lower,elems);
//        } @*/
//
//    }
//
//    //@ ints_split(A,lower);
//    //@ open ints(A+lower,_,_);
//    //@ if(lower < n) { nth_of_is_nth(lower,elems); }
//    if(lower != n && A[lower] == x) {
//        return lower;
//        /*@ {
//            close [f]ints(A+lower,n-lower,_);
//            if(lower != 0) { ints_join(A); }
//        } @*/
//    }
//    //@ assert nth_of(0,drop(lower,elems)) != some(x);
//
//    /*@ if(lower < length(elems)) {
//        nth_drop(0,lower,elems);
//        nth_of_is_nth(0,drop(lower,elems));
//        nth_of_is_nth(lower,elems);
//    } @*/
//
//    //@ assert !mem(x,elems);
//    return -1;
//    /*@ {
//        close [f]ints(A+lower,n-lower,_);
//        if(lower != 0) { ints_join(A); }
//    } @*/
//}


int binsearch_tuerk(int* A, int n, int x)
    /*@ requires [?f]A[..n] |-> ?elems
             &*& !!is_sorted(elems);
      @*/
    /*@ ensures  [ f]A[..n] |->  elems
            &*&  result == -1 ? !mem(x,elems)
            :    nth_of(result,elems) == some(x);
      @*/
    /*@ terminates; @*/
{
    int lo = 0;
    int hi = n;
    int ret = -1;

    while(lo < hi)
        /*@ requires 0 <= lo &*& hi <= n
                &*&  [ f]A[lo..hi] |-> ?loop_seg
                &*&  !!is_sorted(loop_seg)
                &*&  ret == -1 &*& mem(x,loop_seg) == mem(x,elems);
          @*/
        /*@ ensures  [ f]A[old_lo..old_hi] |->  loop_seg
                &*&  ret == -1 ? !mem(x,loop_seg)
                :    ret >= old_lo &*& ret < old_hi
                &*&  nth_of(ret-old_lo,loop_seg) == some(x);
          @*/
        /*@ decreases (hi-lo); @*/
    {
        /*@ div_rem(hi-lo,2); @*/

        int mid = lo+(hi-lo)/2;

        /*@ ints_split(A+lo,mid-lo); @*/
        /*@ assert [f]A[lo..mid] |-> ?pref; @*/
        /*@ assert [f]A[mid..hi] |-> ?suff; @*/
        /*@ assert loop_seg == append(pref,suff); @*/
        /*@ open ints(A+mid,_,_); @*/

        int v = A[mid];

        if(v == x) {
            ret = mid;
            /*@ {
              close [f]ints(A+mid,hi-mid,_);
              ints_join(A+lo);
              nth_of_append(mid-lo,pref,suff);
            } @*/
            break;
        } else if(v < x) {
            lo = mid+1;
            /*@ if(mem(x,loop_seg) && !mem(x,tail(suff))) {
                forall_elim(pref,(flip)(all_above_eq,suff),x);
                assert false;
            } @*/
        } else { /*@ assert v > x; @*/
            hi = mid;
            /*@ if(mem(x,loop_seg) && !mem(x,pref)) {
                forall_elim(tail(suff),(is_above_eq)(v),x);
                assert false;
            } @*/
        }

        /*@ recursive_call(); @*/
        /*@ {
          close [f]ints(A+mid,old_hi-mid,_);
          ints_join(A+old_lo);
          if(ret != -1) {
            nth_of_append(ret-old_lo,pref,suff);
          }
        } @*/
    }

    return ret;
}

