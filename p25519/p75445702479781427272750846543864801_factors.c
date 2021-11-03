/*@ #include "p75445702479781427272750846543864801_factors.gh" @*/

#if 1
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif


/*@

lemma void p25519_1919519569386763_2_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(2,
                nat_of_int(1919519569386763-1)),
            1919519569386763)
        == 1;
{
ALREADY_PROVEN()
    int P = 1919519569386763;
    int g = 2;

    MODPOW_FULL(P,g,P-1,64)

}

lemma void p25519_1919519569386763_1_factors()
    requires true;
    ensures  product({2, 3, 7, 19, 47, 47, 127, 8574133}) + 1
        ==   1919519569386763;
{}


lemma void p25519_1919519569386763_2_exact_order()
    requires true;
    ensures  !!forall({2, 3, 7, 19, 47, 47, 127, 8574133},(pratt_pow_thing)(1919519569386763,2));
{
    int g = 2; int p = 1919519569386763; int q;

    PRATT_FACTOR(p,g,2,64)
    PRATT_FACTOR(p,g,3,64)
    PRATT_FACTOR(p,g,7,64)
    PRATT_FACTOR(p,g,19,64)
    PRATT_FACTOR(p,g,47,64)
    PRATT_FACTOR(p,g,127,64)
    PRATT_FACTOR(p,g,8574133,64)

}


lemma void p25519_72106336199_7_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(7,
                nat_of_int(72106336199-1)),
            72106336199)
        == 1;
{
    ALREADY_PROVEN()
    int P = 72106336199;
    int g = 7;

    MODPOW_FULL(P,g,P-1,40)

}

lemma void p25519_72106336199_1_factors()
    requires true;
    ensures  product({2, 13, 2773320623}) + 1
        ==   72106336199;
{}

lemma void p25519_72106336199_7_exact_order()
    requires true;
    ensures  !!forall({2, 13, 2773320623},(pratt_pow_thing)(72106336199,7));
{
    int g = 7; int p = 72106336199; int q;

    PRATT_FACTOR(p,g,2,40)
    PRATT_FACTOR(p,g,13,40)
    PRATT_FACTOR(p,g,2773320623,40)

}

lemma void p25519_2773320623_10_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(10,
                nat_of_int(2773320623-1)),
            2773320623)
        == 1;
{
    ALREADY_PROVEN()
    int P = 2773320623;
    int g = 10;

    MODPOW_FULL(P,g,P-1,32)

}

lemma void p25519_2773320623_1_factors()
    requires true;
    ensures  product({2, 2437, 569003}) + 1
        ==   2773320623;
{}

lemma void p25519_2773320623_10_exact_order()
    requires true;
    ensures  !!forall({2, 2437, 569003},(pratt_pow_thing)(2773320623,10));
{
    int g = 10; int p = 2773320623; int q;

    PRATT_FACTOR(p,g,2,32)
    PRATT_FACTOR(p,g,2437,32)
    PRATT_FACTOR(p,g,569003,32)

}

lemma void p25519_8574133_5_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(5,
                nat_of_int(8574133-1)),
            8574133)
        == 1;
{
    ALREADY_PROVEN()
        int P = 8574133;
        int g = 5;

    MODPOW_FULL(P,g,P-1,32)

}

lemma void p25519_8574133_1_factors()
    requires true;
    ensures  product({2, 2, 3, 7, 103, 991}) + 1
        ==   8574133;
{}

lemma void p25519_8574133_5_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3, 7, 103, 991},(pratt_pow_thing)(8574133,5));
{
    int g = 5; int p = 8574133; int q;

    PRATT_FACTOR(p,g,2,32)
    PRATT_FACTOR(p,g,3,32)
    PRATT_FACTOR(p,g,7,32)
    PRATT_FACTOR(p,g,103,32)
    PRATT_FACTOR(p,g,991,32)

}

lemma void p25519_569003_2_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(2,
                nat_of_int(569003-1)),
            569003)
        == 1;
{
    ALREADY_PROVEN()
        int P = 569003;
        int g = 2;


    MODPOW_FULL(P,g,P-1,32)

}

lemma void p25519_569003_1_factors()
    requires true;
    ensures  product({2, 7, 97, 419}) + 1
        ==   569003;
{}

lemma void p25519_569003_2_exact_order()
    requires true;
    ensures  !!forall({2, 7, 97, 419},(pratt_pow_thing)(569003,2));
{
    int g = 2; int p = 569003; int q;

    PRATT_FACTOR(p,g,2,32)
    PRATT_FACTOR(p,g,7,32)
    PRATT_FACTOR(p,g,97,32)
    PRATT_FACTOR(p,g,419,32)
}

lemma void p25519_75707_2_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(2,
                nat_of_int(75707-1)),
            75707)
        == 1;
{
    ALREADY_PROVEN()
        int P = 75707;
        int g = 2;

    MODPOW_FULL(P,g,P-1,32)

}

lemma void p25519_75707_1_factors()
    requires true;
    ensures  product({2,37853}) + 1
        ==   75707;
{}

lemma void p25519_75707_2_exact_order()
    requires true;
    ensures  !!forall({2, 37853},(pratt_pow_thing)(75707,2));
{
    int g = 2; int p = 75707; int q;

    PRATT_FACTOR(p,g,2,32)

    q = 37853;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        assert false;
    }


}

lemma void p25519_37853_2_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(2,
                nat_of_int(37853-1)),
            37853)
        == 1;
{
    ALREADY_PROVEN()
        int P = 37853;
        int g = 2;

    MODPOW_FULL(P,g,P-1,16)

}

lemma void p25519_37853_1_factors()
    requires true;
    ensures  product({2, 2, 9463}) + 1
        ==   37853;
{}

lemma void p25519_37853_2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 9463},(pratt_pow_thing)(37853,2));
{
    int g = 2; int p = 37853; int q;

    PRATT_FACTOR(p,g,2,16)

    q = 9463;

    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);
        assert false;
    }


}

lemma pratt_cert p25519_37853_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,37853);
{
    ALREADY_PROVEN()
    p25519_37853_2_generates();
    p25519_37853_1_factors();
    p25519_37853_2_exact_order();

    list<pair<int,pratt_cert> > fact = {pair(2,pratt_small(2))};
    close pratt_certificate(pratt_small(2),1,zero,2);
    close pratt_certificate(pratt_cert(2,fact),37853/2,N1,37853);

    close pratt_certificate(pratt_small(2),1,zero,2);
    pratt_certificate_build(2,fact,2,37853);
    fact = cons(pair(2,pratt_small(2)),fact);

    close pratt_certificate(pratt_small(9463),1,zero,9463);
    pratt_cert ret = pratt_certificate_build(2,fact,9463,37853);

    return ret;
}

lemma pratt_cert p25519_75707_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,75707);
{
    ALREADY_PROVEN()
    p25519_75707_2_generates();
    p25519_75707_1_factors();
    p25519_75707_2_exact_order();

    list<pair<int,pratt_cert> > fact = {pair(2,pratt_small(2))};
    close pratt_certificate(pratt_small(2),1,zero,2);
    close pratt_certificate(pratt_cert(2,fact),75707/2,N1,75707);

    pratt_cert cert37853 = p25519_37853_pratt();
    pratt_cert ret = pratt_certificate_build(2,fact,37853,75707);

    return ret;
}

lemma pratt_cert p25519_569003_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,569003);
{
    ALREADY_PROVEN()
    p25519_569003_2_generates();
    p25519_569003_1_factors();
    p25519_569003_2_exact_order();

    list<pair<int,pratt_cert> > fact = {pair(2,pratt_small(2))};
    close pratt_certificate(pratt_small(2),1,zero,2);
    close pratt_certificate(pratt_cert(2,fact),569003/2,N1,569003);

    close pratt_certificate(pratt_small(7),1,zero,7);
    pratt_certificate_build(2,fact,7,569003);
    fact = cons(pair(7,pratt_small(7)),fact);

    close pratt_certificate(pratt_small(97),1,zero,97);
    pratt_certificate_build(2,fact,97,569003);
    fact = cons(pair(97,pratt_small(97)),fact);

    close pratt_certificate(pratt_small(419),1,zero,419);
    pratt_cert ret = pratt_certificate_build(2,fact,419,569003);

    return ret;
}

lemma pratt_cert p25519_8574133_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,8574133);
{
    ALREADY_PROVEN()
    p25519_8574133_5_generates();
    p25519_8574133_1_factors();
    p25519_8574133_5_exact_order();

    int P = 8574133;
    int g = 5;

    int f;

    f = 2;
    list<pair<int,pratt_cert> > fact = {pair(f,pratt_small(f))};
    close pratt_certificate(pratt_small(f),1,zero,f);
    close pratt_certificate(pratt_cert(g,fact),P/f,N1,P);

    f = 2;
    close pratt_certificate(pratt_small(f),1,zero,f);
    pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,pratt_small(f)),fact);

    f = 3;
    close pratt_certificate(pratt_small(f),1,zero,f);
    pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,pratt_small(f)),fact);

    f = 7;
    close pratt_certificate(pratt_small(f),1,zero,f);
    pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,pratt_small(f)),fact);

    f = 103;
    close pratt_certificate(pratt_small(f),1,zero,f);
    pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,pratt_small(f)),fact);

    f = 991;
    close pratt_certificate(pratt_small(f),1,zero,f);
    pratt_cert ret = pratt_certificate_build(g,fact,f,P);

    return ret;
}

lemma pratt_cert p25519_2773320623_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,2773320623);
{
    ALREADY_PROVEN()
    p25519_2773320623_10_generates();
    p25519_2773320623_1_factors();
    p25519_2773320623_10_exact_order();

    int P = 2773320623;
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

    f = 2437;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 569003;
    cert = p25519_569003_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    return ret;
}

lemma pratt_cert p25519_72106336199_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,72106336199);
{
    ALREADY_PROVEN()
    p25519_72106336199_7_generates();
    p25519_72106336199_1_factors();
    p25519_72106336199_7_exact_order();

    int P = 72106336199;
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

    f = 13;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 2773320623;
    cert = p25519_2773320623_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    return ret;
}


lemma pratt_cert p25519_1919519569386763_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,1919519569386763);
{
    ALREADY_PROVEN()
    p25519_1919519569386763_2_generates();
    p25519_1919519569386763_1_factors();
    p25519_1919519569386763_2_exact_order();

    int P = 1919519569386763;
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

    f = 7;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 19;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 47;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 47;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 127;
    cert = pratt_small(f);
    close pratt_certificate(cert,1,zero,f);
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    f = 8574133;
    cert = p25519_8574133_pratt();
    ret = pratt_certificate_build(g,fact,f,P);
    fact = cons(pair(f,cert),fact);

    return ret;
}


  @*/

