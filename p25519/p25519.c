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

lemma void p25519_2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(P25519-1)),P25519) == 1;
{
ALREADY_PROVEN()
    p25519_formula();
    int P = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed;
    int g = 2;

    DECLARE_256_NATS()
    int e = P-1;
    int acc = g;
    int pow2 = 1;
    int sofar = 1;
    nat n = zero;

    MODPOW_STEP256(P,g,e,n,acc,pow2,sofar)

    assert sofar == 1;
    assert modpow(P,g,P-1,n) == 1;
    modpow_correct(P,g,P-1,n);

}

lemma void p25519_1_factors()
    requires true;
    ensures  product({2,2,3,65147,74058212732561358302231226437062788676166966415465897661863160754340907})
             +1
        ==   P25519;
{ p25519_formula(); }

lemma void p25519_2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3, 65147, 74058212732561358302231226437062788676166966415465897661863160754340907}, (pratt_pow_thing)(P25519, 2));
{
    ALREADY_PROVEN()
    p25519_formula();
    int g = 2;
    int p = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed;
    int q;
    DECLARE_256_NATS()

    q = 2;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP256(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 3;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP256(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 65147;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP256(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 74058212732561358302231226437062788676166966415465897661863160754340907;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP32(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

}

lemma void p25519_65147_2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(65147-1)),65147) == 1;
{
ALREADY_PROVEN()
    int P = 0xfe7b;
    int g = 2;

    int e = P-1;
    int acc = g;
    int pow2 = 1;
    int sofar = 1;
    nat n = zero;

    MODPOW_STEP16(P,g,e,n,acc,pow2,sofar)
    MODPOW_STEP(P,g,e,n,acc,pow2,sofar)

    assert sofar == 1;
    assert modpow(P,g,P-1,n) == 1;
    modpow_correct(P,g,P-1,n);

}

lemma void p25519_65147_1_factors()
    requires true;
    ensures  product({2, 32573}) == 65147-1;
{}

lemma void p25519_65147_2_exact_order()
    requires true;
    ensures  !!forall({2, 32573},(pratt_pow_thing)(65147,2));
{
    ALREADY_PROVEN()

    int g = 2; int p = 65147; int q;
    q = 2;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP16(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 32573;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        assert false;
    }

}

lemma void p25519_32573_2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(32573-1)),32573) == 1;
{
    ALREADY_PROVEN()
    int P = 32573;
    int g = 2;
    int e = P-1;
    int acc = g;
    int pow2 = 1;
    int sofar = 1;
    nat n = zero;

    MODPOW_STEP16(P,g,e,n,acc,pow2,sofar)

    modpow_correct(P,g,P-1,n);
}

lemma void p25519_32573_1_factors()
    requires true;
    ensures  product({2, 2, 17, 479}) == 32573-1;
{}

lemma void p25519_32573_2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 17, 479},(pratt_pow_thing)(32573,2));
{
    ALREADY_PROVEN()
    int g = 2; int p = 32573; int q;
    q = 2;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP16(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 17;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP16(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 479;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP16(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

}

lemma pratt_cert p25519_479_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,479);
{
    ALREADY_PROVEN()
    pratt_cert ret = pratt_small(479);
    close pratt_certificate(ret,1,zero,479);

    return ret;
}

lemma pratt_cert p25519_32573_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,32573);
{
    ALREADY_PROVEN()
    p25519_32573_2_generates();
    p25519_32573_2_exact_order();
    list<pair<int,pratt_cert> > fact = {pair(2,pratt_small(2))};
    close pratt_certificate(pratt_small(2),1,zero,2);
    close pratt_certificate(pratt_cert(2,fact),32573/2,N1,32573);

    close pratt_certificate(pratt_small(2),1,zero,2);
    pratt_certificate_build(2,fact, 2, 32573);
    fact = cons(pair(2,pratt_small(2)),fact);

    close pratt_certificate(pratt_small(17),1,zero,17);
    pratt_certificate_build(2,fact, 17, 32573);
    fact = cons(pair(17,pratt_small(17)),fact);

    pratt_cert cert_479 = p25519_479_pratt();
    pratt_cert ret = pratt_certificate_build(2,fact, 479, 32573);

    return ret;
}

lemma pratt_cert p25519_65147_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,65147);
{
    ALREADY_PROVEN()
    p25519_65147_2_generates();
    p25519_65147_2_exact_order();
    list<pair<int,pratt_cert> > fact = {pair(2,pratt_small(2))};
    close pratt_certificate(pratt_small(2),1,zero,2);
    close pratt_certificate(pratt_cert(2,fact),65147/2,N1,65147);

    pratt_cert cert_32573 = p25519_32573_pratt();
    pratt_cert ret = pratt_certificate_build(2, fact, 32573, 65147);

    return ret;
}

lemma pratt_cert p25519_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,P25519);
{
    ALREADY_PROVEN()
    p25519_2_generates();
    p25519_1_factors();
    p25519_2_exact_order();

    p25519_formula();
    int P = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed;
    int g = 2;

    int f;
    pratt_cert ret;
    pratt_cert cert;
    list<pair<int,pratt_cert> > fact = nil;

    f = 2;
    cert = pratt_small(f);
    fact = cons(pair(f,cert),fact);
    close pratt_certificate(cert,1,zero,f);
    close pratt_certificate(pratt_cert(g,fact),P/f,N1,P);

    f = 2;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 3;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 65147;
    cert = p25519_65147_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 74058212732561358302231226437062788676166966415465897661863160754340907;
    cert = p25519_74058212732561358302231226437062788676166966415465897661863160754340907_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    return ret;
}

lemma void p25519_is_prime()
    requires true;
    ensures  !!is_prime(P25519);
{
    p25519_pratt();
    leak pratt_certificate(_,_,_,_);
    pratt_certificate_prime();
}

  @*/

