/*@ #include "p31757755568855353.gh" @*/

/*@

lemma void p25519_31757755568855353_g10_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(10,
                nat_of_int(31757755568855353-1)),
            31757755568855353)
        == 1;
{
    int P = 31757755568855353;
    int g = 10;

    MODPOW_FULL(P,g,P-1,64)
}

lemma void p25519_31757755568855353_1_factors()
    requires true;
    ensures  product({2, 2, 2, 3, 31, 107, 223, 4153, 430751}) + 1
        ==   31757755568855353;
{}

lemma void p25519_31757755568855353_g10_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 3, 31, 107, 223, 4153, 430751},(pratt_pow_thing)(31757755568855353,10));
{
    int g = 10; int p = 31757755568855353; int q;

    PRATT_FACTOR(p,g,2,64)
    PRATT_FACTOR(p,g,3,64)
    PRATT_FACTOR(p,g,31,64)
    PRATT_FACTOR(p,g,107,64)
    PRATT_FACTOR(p,g,223,64)
    PRATT_FACTOR(p,g,4153,64)
    PRATT_FACTOR(p,g,430751,64)
}

lemma void p25519_430751_g17_generates()
    requires true;
    ensures  euclid_mod(
            pow_nat(17,
                nat_of_int(430751-1)),
            430751)
        == 1;
{
    int P = 430751;
    int g = 17;
    MODPOW_FULL(P,g,P-1,32)
}

lemma void p25519_430751_1_factors()
    requires true;
    ensures  product({2, 5, 5, 5, 1723}) + 1
        ==   430751;
{}

lemma void p25519_430751_g17_exact_order()
    requires true;
    ensures  !!forall({2, 5, 5, 5, 1723},(pratt_pow_thing)(430751,17));
{
    int g = 17; int p = 430751; int q;

    PRATT_FACTOR(p,g,2,32)
    PRATT_FACTOR(p,g,5,32)
    PRATT_FACTOR(p,g,1723,32)

}

lemma pratt_cert p25519_430751_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,430751);
{
    PRATT_BUILD_PRELUDE(430751,17)

    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(1723)

    return ret;
}

lemma pratt_cert p25519_31757755568855353_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,31757755568855353);
{
    PRATT_BUILD_PRELUDE(31757755568855353,10)

    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(31)
    PRATT_BUILD_SMALL(107)
    PRATT_BUILD_SMALL(223)
    PRATT_BUILD_SMALL(4153)
    PRATT_BUILD_BIG(430751)

    return ret;
}


  @*/

