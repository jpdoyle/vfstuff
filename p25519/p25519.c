/*@ #include "p25519.gh" @*/
/*@ #include "p74058212732561358302231226437062788676166966415465897661863160754340907.gh" @*/

#if 1
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif

/*@

lemma void p25519_formula()
    requires true;
    ensures  emp
        //&*&  pow_nat(2,nat_of_int(255)) - 19
        //==   pow_nat(pow_nat(2,N15),N16)*pow_nat(2,N15) - 19
        &*&  pow_nat(2,nat_of_int(255)) - 19 > 0
        &*&  pow_nat(2,nat_of_int(255)) - 19
        ==   (0x8000000000000000000000000000000000000000000000000000000000000000
             - 19)
        ;
{
ALREADY_PROVEN()
    pow_plus(2,nat_of_int(240),15);
    assert pow_nat(2,nat_of_int(255))
        == pow_nat(2,nat_of_int(240))*pow_nat(2,N15);
    pow_times2(2,N15,16);
}

lemma void p25519_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(P25519-1)),P25519) == 1;
{
ALREADY_PROVEN()
    p25519_formula();
    int P = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed;
    int g = 2;

    DECLARE_256_NATS(zero,0)
    MODPOW_FULL(P,g,P-1,256)

}

lemma void p25519_2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(P25519-1)),P25519) == 1;
{
ALREADY_PROVEN()
    p25519_formula();
    int P = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed;
    int g = 2;

    DECLARE_256_NATS(zero,0)
    MODPOW_FULL(P,g,P-1,256)

}

lemma void p25519_57896044618658097711785492504343953926634992332820282019728792003956564819949_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(P25519-1)),P25519) == 1;
{
ALREADY_PROVEN()
    p25519_formula();
    p25519_2_generates();
}

lemma void p25519_1_factors()
    requires true;
    ensures  product({2,2,3,65147,74058212732561358302231226437062788676166966415465897661863160754340907})
             +1
        ==   P25519;
{ p25519_formula(); }

lemma void
p25519_57896044618658097711785492504343953926634992332820282019728792003956564819949_1_factors()
    requires true;
    ensures  product({2,2,3,65147,74058212732561358302231226437062788676166966415465897661863160754340907})
             +1
        ==   57896044618658097711785492504343953926634992332820282019728792003956564819949;
{}

lemma void p25519_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3, 65147, 74058212732561358302231226437062788676166966415465897661863160754340907}, (pratt_pow_thing)(P25519, 2));
{
ALREADY_PROVEN()
    p25519_formula();
    int g = 2;
    int p = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed;
    DECLARE_256_NATS(zero,0)

    PRATT_FACTOR(p,g,2,256)
    PRATT_FACTOR(p,g,3,256)
    PRATT_FACTOR(p,g,65147,256)

    PRATT_FACTOR(p,g,74058212732561358302231226437062788676166966415465897661863160754340907,32)
}

lemma void p25519_57896044618658097711785492504343953926634992332820282019728792003956564819949_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3, 65147, 74058212732561358302231226437062788676166966415465897661863160754340907}, (pratt_pow_thing)(57896044618658097711785492504343953926634992332820282019728792003956564819949, 2));
{
ALREADY_PROVEN()
    p25519_formula();
    p25519_g2_exact_order();
}

lemma void p25519_65147_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(65147-1)),65147) == 1;
{
ALREADY_PROVEN()
    int P = 0xfe7b;
    int g = 2;

    MODPOW_FULL(P,g,P-1,16)
}

lemma void p25519_65147_1_factors()
    requires true;
    ensures  product({2, 32573}) == 65147-1;
{}

lemma void p25519_65147_g2_exact_order()
    requires true;
    ensures  !!forall({2, 32573},(pratt_pow_thing)(65147,2));
{
    ALREADY_PROVEN()

    int g = 2; int p = 65147; int q;

    PRATT_FACTOR(p,g,2,16)

    if(!pratt_pow_thing(p,g,32573)) {
        pratt_pow_thing_auto(p,g,32573);

        assert false;
    }

}

lemma void p25519_32573_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(32573-1)),32573) == 1;
{
    ALREADY_PROVEN()
    int P = 32573;
    int g = 2;

    MODPOW_FULL(P,g,P-1,16)
}

lemma void p25519_32573_1_factors()
    requires true;
    ensures  product({2, 2, 17, 479}) == 32573-1;
{}

lemma void p25519_32573_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 17, 479},(pratt_pow_thing)(32573,2));
{
    ALREADY_PROVEN()
    int g = 2; int p = 32573; int q;

    PRATT_FACTOR(p,g,2,16)
    PRATT_FACTOR(p,g,17,16)
    PRATT_FACTOR(p,g,479,16)

}

lemma pratt_cert p25519_32573_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,32573);
{
    PRATT_BUILD_PRELUDE(32573,2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(17)
    PRATT_BUILD_SMALL(479)

    return ret;
}

lemma pratt_cert p25519_65147_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,65147);
{
    PRATT_BUILD_PRELUDE(65147,2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_BIG(32573)

    return ret;
}

lemma pratt_cert p25519_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,P25519);
{
    p25519_formula();

    PRATT_BUILD_PRELUDE(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed,2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_BIG(65147)
    PRATT_BUILD_BIG(74058212732561358302231226437062788676166966415465897661863160754340907)

    return ret;
}

lemma void p25519_is_prime()
    requires true;
    ensures  !!is_prime(P25519);
{
    ALREADY_PROVEN()
    p25519_pratt();
    leak pratt_certificate(_,_,_,_);
    pratt_certificate_prime();
}

  @*/

