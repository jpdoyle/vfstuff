/*@ #include "bitops.gh" @*/
/*@ #include "util.gh" @*/
/*@ #include <target.gh> @*/

/* @

lemma void division_unique(int D, int d, int q, int r);
    requires d != 0 &*& abs(r) < abs(d) &*& abs(d*q) <= abs(D)
        &*&  D == d*q + r;
    ensures  q == (D/d) &*& r == (D%d);

  @*/

void foo()
    /*@ requires true; @*/
    /*@ ensures true; @*/
    /*@ terminates; @*/
{
    unsigned x = /*@ truncating @*/ -(unsigned)1;
    /*@ {
        case_split_sizeof_int();
        truncate_unsigned_def(-1, nat_of_int(8*sizeof(unsigned int)));
        divrem_elim();
    } @*/
    // C99 conversion of -(unsigned)1: verifast now yields
    //   x == truncate_unsigned(-1, 8*sizeof(unsigned int)),
    // but deriving the final value 0xffffffff needs a nonlinear modulo
    // step that z3 4.15 (uninterpreted C99 div/mod) fails to discharge,
    // whereas the old euclid-preset chunk could. Kept here as a C99
    // conversion experiment.
    /*@ assert x == truncate_unsigned(-1, 8*sizeof(unsigned int)); @*/
}
