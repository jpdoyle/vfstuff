/*@ #include "p74058212732561358302231226437062788676166966415465897661863160754340907.gh" @*/
/*@ #include "p75445702479781427272750846543864801.gh" @*/
/*@ #include "p31757755568855353.gh" @*/

#if 1
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif

/*@

lemma void
p25519_74058212732561358302231226437062788676166966415465897661863160754340907_g2_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(2,
                nat_of_int(74058212732561358302231226437062788676166966415465897661863160754340907-1)),
            74058212732561358302231226437062788676166966415465897661863160754340907)
        == 1;
{
    ALREADY_PROVEN()
    int P = 74058212732561358302231226437062788676166966415465897661863160754340907;
    int g = 2;

    DECLARE_256_NATS(zero,0)

    MODPOW_FULL(P,g,P-1,256)

}

lemma void p25519_74058212732561358302231226437062788676166966415465897661863160754340907_1_factors()
    requires true;
    ensures  product({2, 3, 353, 57467, 132049, 1923133, 31757755568855353,
            75445702479781427272750846543864801}) ==
        74058212732561358302231226437062788676166966415465897661863160754340907-1;
{}

lemma void
p25519_74058212732561358302231226437062788676166966415465897661863160754340907_g2_exact_order()
    requires true;
    ensures  !!forall({2, 3, 353, 57467, 132049, 1923133,
                        31757755568855353,
                        75445702479781427272750846543864801},
            (pratt_pow_thing)(74058212732561358302231226437062788676166966415465897661863160754340907,2));
{
    DECLARE_256_NATS(zero,0)

    int g = 2; int p = 74058212732561358302231226437062788676166966415465897661863160754340907;

    PRATT_FACTOR(p,g,2,256)
    PRATT_FACTOR(p,g,3,256)
    PRATT_FACTOR(p,g,353,256)
    PRATT_FACTOR(p,g,57467,256)
    PRATT_FACTOR(p,g,132049,256)
    PRATT_FACTOR(p,g,1923133,256)
    PRATT_FACTOR(p,g,31757755568855353,192)
    PRATT_FACTOR(p,g,75445702479781427272750846543864801,160)
}

lemma void p25519_1923133_g2_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(2,
                nat_of_int(1923133-1)),
            1923133)
        == 1;
{
    ALREADY_PROVEN()
    int P = 1923133;
    int g = 2;

    MODPOW_FULL(P,g,P-1,32)
}

lemma void p25519_1923133_1_factors()
    requires true;
    ensures  product({2, 2, 3, 43, 3727}) + 1
        ==   1923133;
{}

lemma void p25519_1923133_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3, 43, 3727},(pratt_pow_thing)(1923133,2));
{
    int g = 2; int p = 1923133; int q;

    PRATT_FACTOR(p,g,2,32)
    PRATT_FACTOR(p,g,3,32)
    PRATT_FACTOR(p,g,43,32)
    PRATT_FACTOR(p,g,3727,32)

}

lemma pratt_cert p25519_1923133_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,1923133);
{

    PRATT_BUILD_PRELUDE(1923133,2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(43)
    PRATT_BUILD_SMALL(3727)

    return ret;
}


lemma void p25519_132049_g39_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(39,
                nat_of_int(132049-1)),
            132049)
        == 1;
{
    ALREADY_PROVEN()
    int P = 132049;
    int g = 39;

    int e = P-1;
    int acc = g;
    int pow2 = 1;
    int sofar = 1;
    nat n = zero;

    MODPOW_STEP32(P,g,e,n,acc,pow2,sofar)

    assert sofar == 1;
    assert modpow(P,g,P-1,n) == 1;
    modpow_correct(P,g,P-1,n);
}

lemma void p25519_132049_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 3, 3, 7, 131}) + 1
        ==   132049;
{}

lemma void p25519_132049_g39_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 3, 3, 7, 131},(pratt_pow_thing)(132049,39));
{
    int g = 39; int p = 132049; int q;

    PRATT_FACTOR(p,g,2,32)
    PRATT_FACTOR(p,g,3,32)
    PRATT_FACTOR(p,g,7,32)
    PRATT_FACTOR(p,g,131,32)

}

lemma pratt_cert p25519_132049_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,132049);
{
    PRATT_BUILD_PRELUDE(132049,39)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(131)

    return ret;
}


lemma void p25519_57467_g2_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(2,
                nat_of_int(57467-1)),
            57467)
        == 1;
{
    ALREADY_PROVEN()
    int P = 57467;
    int g = 2;

    int e = P-1;
    int acc = g;
    int pow2 = 1;
    int sofar = 1;
    nat n = zero;

    MODPOW_STEP16(P,g,e,n,acc,pow2,sofar)

    assert sofar == 1;
    assert modpow(P,g,P-1,n) == 1;
    modpow_correct(P,g,P-1,n);
}

lemma void p25519_57467_1_factors()
    requires true;
    ensures  product({2, 59, 487}) + 1
        ==   57467;
{}

lemma void p25519_57467_g2_exact_order()
    requires true;
    ensures  !!forall({2, 59, 487},(pratt_pow_thing)(57467,2));
{
    int g = 2; int p = 57467; int q;

    PRATT_FACTOR(p,g,2,32)
    PRATT_FACTOR(p,g,59,32)
    PRATT_FACTOR(p,g,487,32)

}

lemma pratt_cert p25519_57467_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,57467);
{
    PRATT_BUILD_PRELUDE(57467,2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(59)
    PRATT_BUILD_SMALL(487)

    return ret;
}

lemma pratt_cert p25519_74058212732561358302231226437062788676166966415465897661863160754340907_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,74058212732561358302231226437062788676166966415465897661863160754340907);
{

    PRATT_BUILD_PRELUDE(74058212732561358302231226437062788676166966415465897661863160754340907,2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(353)
    PRATT_BUILD_BIG(57467)
    PRATT_BUILD_BIG(132049)
    PRATT_BUILD_BIG(1923133)
    PRATT_BUILD_BIG(31757755568855353)
    PRATT_BUILD_BIG(75445702479781427272750846543864801)

    return ret;
}


  @*/

