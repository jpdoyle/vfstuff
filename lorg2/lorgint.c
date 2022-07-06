#include "lorgint.h"
#include "common.h"
/*@ #include "../bitops.gh" @*/

#if 1
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() { assume(false); }
#endif

#if 1
#define SKIP_A_PROOF() {}
#else
#define SKIP_A_PROOF() { assume(false); }
#endif

void lorgint_add_internal(lorgint* dst, lorgint* src)
    /*@ requires     lorgint_view(dst, ?base, ?dst_neg,
                             ?dst_min, ?dst_max, ?dst_start, ?dst_cap,
                             ?dst_limbs, ?dst_v)
            &*&  [?f]lorgint_view(src,  base, ?src_neg, ?src_min, ?src_max,
                             ?src_start, ?src_cap, ?src_limbs, ?src_v)
            &*&  dst_cap >= length(src_limbs)
            &*&  let(max_of(0,dst_max), ?tweaked_max)
            &*&  let(min_of(0,dst_min), ?tweaked_min)
            &*&  let(dst_neg == src_neg ? tweaked_max + src_max
                                        : tweaked_max - src_min,
                     ?combined_max)
            &*&  let(dst_neg == src_neg ? tweaked_min + src_min
                                        : tweaked_min - src_max,
                     ?combined_min)
            &*&  let(max_of(combined_max,tweaked_max),?new_max)
            &*&  let(min_of(combined_min,tweaked_min),?new_min)
            &*&  new_max < (1<<31) &*& new_min > -(1<<31)
            ; @*/
    /*@ ensures      lorgint_view(dst,  base, dst_neg, new_min, new_max,
                              dst_start,  dst_cap, _,
                              src_v+dst_v)
            &*&  [ f]lorgint_view(src,  base,  src_neg,  src_min,  src_max,
                              src_start,  src_cap,  src_limbs,  src_v)
            ; @*/
    /*@ terminates; @*/
{
    /*@ ALREADY_PROVEN() @*/

    int32_t* dst_p;
    int32_t* src_p;
    bool subtract = (src->is_negative != dst->is_negative);

    /*@ if(!forall(dst_limbs, (bounded)(tweaked_min,tweaked_max))) {
        int cx = not_forall(dst_limbs, (bounded)(tweaked_min,tweaked_max));
        forall_elim(dst_limbs,(bounded)(dst_min,dst_max),cx);
        assert false;
    } @*/

    /*@ if(!forall(dst_limbs, (bounded)(new_min,new_max))) {
        int cx = not_forall(dst_limbs, (bounded)(new_min,new_max));
        forall_elim(dst_limbs,(bounded)(tweaked_min,tweaked_max),cx);
        assert false;
    } @*/

    int32_t dst_minval = min32(dst->minval,0);
    int32_t dst_maxval = max32(dst->maxval,0);
    /*@ assert dst_minval == tweaked_min; @*/
    /*@ assert dst_maxval == tweaked_max; @*/

    if(subtract) {
        dst->minval = dst_minval - src->maxval;
        dst->maxval = dst_maxval - src->minval;
    } else {
        dst->minval = dst_minval + src->minval;
        dst->maxval = dst_maxval + src->maxval;
    }
    /*@ assert dst->minval |-> combined_min; @*/
    /*@ assert dst->maxval |-> combined_max; @*/

    dst->minval = min32(dst_minval,dst->minval);
    dst->maxval = max32(dst_maxval,dst->maxval);

    /*@ assert dst->minval |-> new_min; @*/
    /*@ assert dst->maxval |-> new_max; @*/

    /*@ int n = 0; @*/

    for(dst_p = dst->start, src_p = src->start;
                src_p < src->end; ++dst_p, ++src_p)
        /*@ requires dst->end |-> ?dst_end
                &*&  dst->size |-> ?dst_size
                &*&  dst_p + dst_size - n == dst_end
                &*&  dst_size <= dst_cap
                &*&  dst_p[..(dst_size-n)] |-> ?l_dst_limbs
                &*&  dst_end[..dst_cap-dst_size] |-> _
                &*&  !!forall(l_dst_limbs,
                        (bounded)(tweaked_min,tweaked_max))
                &*&  !!forall(l_dst_limbs,
                        (bounded)(new_min,new_max))

                &*&  [f]src->end |-> ?src_end
                &*&  [f]src->size |-> ?src_size
                &*&  src_p + src_size - n == src_end
                &*&  [f]src_p[..(src_size-n)] |-> ?l_src_limbs
                &*&  !!forall(l_src_limbs, (bounded)(src_min,src_max))

                &*&  src_size <= dst_cap
                &*&  n >= 0 &*& n <= src_size
                ; @*/
        /*@ ensures  dst->end |-> ?new_end
                &*&  dst->size |-> ?new_size
                &*&  new_size <= dst_cap
                &*&  dst_end + (new_size-dst_size) == new_end
                &*&  old_dst_p[..(new_size-old_n)] |-> ?new_dst_limbs
                &*&  new_end[..dst_cap-new_size] |-> _
                &*&  !!forall(new_dst_limbs,
                        (bounded)(new_min,new_max))

                &*&  [f]src->end |-> src_end
                &*&  [f]src->size |-> src_size
                &*&  [f]old_src_p[..(src_size-old_n)] |-> l_src_limbs

                &*&  subtract
                ?    poly_eval(new_dst_limbs,base)
                     == poly_eval(l_dst_limbs,base)
                        -poly_eval(l_src_limbs,base)
                :    poly_eval(new_dst_limbs,base)
                     == poly_eval(l_dst_limbs,base)
                        +poly_eval(l_src_limbs,base)
                ; @*/
        /*@ decreases src_size - n; @*/
    {
        if(dst_p == dst->end) {
            /*@ assert dst_size - n == 0; @*/
            /*@ assert dst_size < dst_cap; @*/
            /*@ assert dst_end == dst_p; @*/
            /*@ open ints(dst_p,0,nil); @*/
            /*@ ints_limits(dst_end); @*/
            /*@ open ints(dst_end,_,_); @*/
            *dst_p = 0;
            ++dst->end;
            /*@ ++dst->size; @*/

            /*@ note_eq(l_dst_limbs,nil); @*/
            /*@ note_eq(poly_eval(l_dst_limbs,base),poly_eval({0},base)); @*/
        }
        /*@ assert *dst_p |-> ?dst_x; @*/
        /*@ assert [f]*src_p |-> ?src_x; @*/

        if(subtract) {
            *dst_p -= *src_p;
            /*@ if(bounded(new_min,new_max,dst_x - src_x)) {
            } else {
                assert false;
            } @*/
        } else {
            *dst_p += *src_p;
            /*@ if(bounded(new_min,new_max,dst_x + src_x)) {
            } else {
                assert false;
            } @*/
        }
        /*@ ++n; @*/


        /*@ assert dst->size |-> ?next_size; @*/
        /*@ assert (dst_p+1)[..(next_size-n)] |-> ?next_dst_limbs; @*/
        /*@ assert [f](src_p+1)[..(src_size-n)] |-> ?next_src_limbs; @*/

        /*@ {
            if(!subtract) {
                note_eq( poly_eval(l_src_limbs,base) + poly_eval(l_dst_limbs,base)
                    ,  (dst_x + src_x)
                    +  base*(poly_eval(next_dst_limbs,base)
                            +  poly_eval(next_src_limbs,base)));
            } else {
                note_eq( poly_eval(l_dst_limbs,base) - poly_eval(l_src_limbs,base)
                    ,  (dst_x - src_x)
                    +  base*(poly_eval(next_dst_limbs,base)
                            -  poly_eval(next_src_limbs,base)));
            }
        } @*/
    }
}

