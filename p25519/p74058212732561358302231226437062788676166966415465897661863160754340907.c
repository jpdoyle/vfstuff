/*@ #include "p74058212732561358302231226437062788676166966415465897661863160754340907.gh" @*/
/*@ #include "p75445702479781427272750846543864801.gh" @*/
/*@ #include "p31757755568855353.gh" @*/

#if 1
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif

/*@

lemma void p25519_74058212732561358302231226437062788676166966415465897661863160754340907_2_generates()
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

lemma void p25519_74058212732561358302231226437062788676166966415465897661863160754340907_1_factors()
    requires true;
    ensures  product({2, 3, 353, 57467, 132049, 1923133, 31757755568855353,
            75445702479781427272750846543864801}) ==
        74058212732561358302231226437062788676166966415465897661863160754340907-1;
{}

lemma void p25519_74058212732561358302231226437062788676166966415465897661863160754340907_2_exact_order()
    requires true;
    ensures  !!forall({2, 3, 353, 57467, 132049, 1923133,
                        31757755568855353,
                        75445702479781427272750846543864801},
            (pratt_pow_thing)(74058212732561358302231226437062788676166966415465897661863160754340907,2));
{
    ALREADY_PROVEN()
    DECLARE_256_NATS()

    int g = 2; int p = 74058212732561358302231226437062788676166966415465897661863160754340907; int q;
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

    q = 353;
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

    q = 57467;
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

    q = 132049;
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

    q = 1923133;
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

    q = 31757755568855353;
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

    q = 75445702479781427272750846543864801;
    if(!pratt_pow_thing(p,g,q)) {

        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP128(p,g,e,n,acc,pow2,sofar)
        MODPOW_STEP32(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

}

lemma void p25519_1923133_2_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(2,
                nat_of_int(1923133-1)),
            1923133)
        == 1;
{
    int P = 1923133;
    int g = 2;

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

lemma void p25519_1923133_1_factors()
    requires true;
    ensures  product({2, 2, 3, 43, 3727}) + 1
        ==   1923133;
{}

lemma void p25519_1923133_2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3, 43, 3727},(pratt_pow_thing)(1923133,2));
{
    int g = 2; int p = 1923133; int q;

    q = 2;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
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

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 43;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 3727;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

}

lemma pratt_cert p25519_1923133_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,1923133);
{
    p25519_1923133_2_generates();
    p25519_1923133_1_factors();
    p25519_1923133_2_exact_order();

    int P = 1923133;
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

    f = 43;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 3727;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    return ret;
}


lemma void p25519_132049_39_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(39,
                nat_of_int(132049-1)),
            132049)
        == 1;
{
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

lemma void p25519_132049_39_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 3, 3, 7, 131},(pratt_pow_thing)(132049,39));
{
    int g = 39; int p = 132049; int q;

    q = 2;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
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

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 7;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 131;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

}

lemma pratt_cert p25519_132049_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,132049);
{
    p25519_132049_39_generates();
    p25519_132049_1_factors();
    p25519_132049_39_exact_order();

    int P = 132049;
    int g = 39;

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

    f = 2;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

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

    f = 3;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 7;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 131;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    return ret;
}


lemma void p25519_57467_2_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(2,
                nat_of_int(57467-1)),
            57467)
        == 1;
{
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

lemma void p25519_57467_2_exact_order()
    requires true;
    ensures  !!forall({2, 59, 487},(pratt_pow_thing)(57467,2));
{
    int g = 2; int p = 57467; int q;

    q = 2;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 59;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 487;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }
}

lemma pratt_cert p25519_57467_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,57467);
{
    p25519_57467_2_generates();
    p25519_57467_1_factors();
    p25519_57467_2_exact_order();

    int P = 57467;
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

    f = 59;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 487;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    return ret;
}

lemma pratt_cert p25519_74058212732561358302231226437062788676166966415465897661863160754340907_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,74058212732561358302231226437062788676166966415465897661863160754340907);
{
    p25519_74058212732561358302231226437062788676166966415465897661863160754340907_2_generates();
    p25519_74058212732561358302231226437062788676166966415465897661863160754340907_1_factors();
    p25519_74058212732561358302231226437062788676166966415465897661863160754340907_2_exact_order();

    int P = 74058212732561358302231226437062788676166966415465897661863160754340907;
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

    f = 3;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 353;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 57467;
    cert = p25519_57467_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 132049;
    cert = p25519_132049_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 1923133;
    cert = p25519_1923133_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 31757755568855353;
    cert = p25519_31757755568855353_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 75445702479781427272750846543864801;
    cert = p25519_75445702479781427272750846543864801_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    return ret;
}


  @*/

