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
    MODPOW_FULL(P,g,P-1,128)

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
    DECLARE_256_NATS()

    int g = 7; int p = 75445702479781427272750846543864801; int q;

    PRATT_FACTOR(p,g,2,128)
    PRATT_FACTOR(p,g,3,128)
    PRATT_FACTOR(p,g,5,128)
    PRATT_FACTOR(p,g,75707,128)
    PRATT_FACTOR(p,g,72106336199,80)
    PRATT_FACTOR(p,g,1919519569386763,80)
}

lemma pratt_cert p25519_75445702479781427272750846543864801_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,75445702479781427272750846543864801);
{
ALREADY_PROVEN()
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

