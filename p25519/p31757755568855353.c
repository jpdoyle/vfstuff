/*@ #include "p31757755568855353.gh" @*/

/*@

lemma void p25519_31757755568855353_10_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(10,
                nat_of_int(31757755568855353-1)),
            31757755568855353)
        == 1;
{
    int P = 31757755568855353;
    int g = 10;

    int e = P-1;
    int acc = g;
    int pow2 = 1;
    int sofar = 1;
    nat n = zero;

    MODPOW_STEP64(P,g,e,n,acc,pow2,sofar)

    assert sofar == 1;
    assert modpow(P,g,P-1,n) == 1;
    modpow_correct(P,g,P-1,n);
}

lemma void p25519_31757755568855353_1_factors()
    requires true;
    ensures  product({2, 2, 2, 3, 31, 107, 223, 4153, 430751}) + 1
        ==   31757755568855353;
{}

lemma void p25519_31757755568855353_10_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 3, 31, 107, 223, 4153, 430751},(pratt_pow_thing)(31757755568855353,10));
{
    int g = 10; int p = 31757755568855353; int q;

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

    q = 31;

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

    q = 107;

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

    q = 223;

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

    q = 4153;

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

    q = 430751;

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

lemma void p25519_430751_17_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(17,
                nat_of_int(430751-1)),
            430751)
        == 1;
{
    int P = 430751;
    int g = 17;

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

lemma void p25519_430751_1_factors()
    requires true;
    ensures  product({2, 5, 5, 5, 1723}) + 1
        ==   430751;
{}

lemma void p25519_430751_17_exact_order()
    requires true;
    ensures  !!forall({2, 5, 5, 5, 1723},(pratt_pow_thing)(430751,17));
{
    int g = 17; int p = 430751; int q;

    q = 2;

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

    q = 5;

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

    q = 1723;

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

lemma pratt_cert p25519_430751_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,430751);
{
    p25519_430751_17_generates();
    p25519_430751_1_factors();
    p25519_430751_17_exact_order();

    int P = 430751;
    int g = 17;

    int f;
    pratt_cert ret;
    pratt_cert cert;
    list<pair<int,pratt_cert> > fact = nil;

    f = 2;
    cert = pratt_small(f);
    fact = cons(pair(f,cert),fact);
    close pratt_certificate(cert,1,zero,f);
    close pratt_certificate(pratt_cert(g,fact),P/f,N1,P);

    f = 5;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 5;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 5;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 1723;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    return ret;
}

lemma pratt_cert p25519_31757755568855353_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,31757755568855353);
{
    p25519_31757755568855353_10_generates();
    p25519_31757755568855353_1_factors();
    p25519_31757755568855353_10_exact_order();

    int P = 31757755568855353;
    int g = 10;

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

    f = 3;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 31;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 107;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 223;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 4153;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 430751;
    cert = p25519_430751_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    return ret;
}


  @*/

