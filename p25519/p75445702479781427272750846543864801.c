/*@ #include "p75445702479781427272750846543864801.gh" @*/
/*@ #include "p75445702479781427272750846543864801_factors.gh" @*/

#if 1
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif

/*@

lemma void p25519_75445702479781427272750846543864801_7_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(7,
                nat_of_int(75445702479781427272750846543864801-1)),
            75445702479781427272750846543864801)
        == 1;
{
ALREADY_PROVEN()
    int P = 75445702479781427272750846543864801;
    int g = 7;

    DECLARE_256_NATS()
    int e = P-1;
    int acc = g;
    int pow2 = 1;
    int sofar = 1;
    nat n = zero;

    MODPOW_STEP128(P,g,e,n,acc,pow2,sofar)

    assert sofar == 1;
    assert modpow(P,g,P-1,n) == 1;
    modpow_correct(P,g,P-1,n);

}

lemma void p25519_75445702479781427272750846543864801_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 2, 3, 3, 5, 5, 75707, 72106336199, 1919519569386763}) + 1
        ==   75445702479781427272750846543864801;
{}


lemma void p25519_75445702479781427272750846543864801_7_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 2, 3, 3, 5, 5, 75707, 72106336199,
        1919519569386763},
        (pratt_pow_thing)(75445702479781427272750846543864801,7));
{
ALREADY_PROVEN()
    DECLARE_256_NATS()

    int g = 7; int p = 75445702479781427272750846543864801; int q;
    q = 2;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP128(p,g,e,n,acc,pow2,sofar)
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

        MODPOW_STEP128(p,g,e,n,acc,pow2,sofar)
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

        MODPOW_STEP128(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 75707;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP128(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 72106336199;
    if(!pratt_pow_thing(p,g,q)) {

        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
        MODPOW_STEP16(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

    q = 1919519569386763;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        int e = (p-1)/q;
        int acc = g;
        int pow2 = 1;
        int sofar = 1;
        nat n = zero;

        MODPOW_STEP64(p,g,e,n,acc,pow2,sofar)
        MODPOW_STEP2(p,g,e,n,acc,pow2,sofar)
        modpow_correct(p,g,e,n);

        assert false;
    }

}

lemma pratt_cert p25519_75445702479781427272750846543864801_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,75445702479781427272750846543864801);
{
    p25519_75445702479781427272750846543864801_7_generates();
    p25519_75445702479781427272750846543864801_1_factors();
    p25519_75445702479781427272750846543864801_7_exact_order();

    int P = 75445702479781427272750846543864801;
    int g = 7;

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

    f = 75707;
    cert = p25519_75707_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 72106336199;
    cert = p25519_72106336199_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 1919519569386763;
    cert = p25519_1919519569386763_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    return ret;
}

@*/

