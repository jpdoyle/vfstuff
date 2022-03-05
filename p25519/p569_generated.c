/*@ #include "p25519.gh" @*/
/*@ #include "p569_generated.gh" @*/

/*@

lemma void p25519_0xc2611_g10_generates()
    requires true;
    ensures  euclid_mod(pow_nat(10,nat_of_int(0xc2610)),0xc2611) == 1;
{
    assert (0xc2610/0x100000000) == 0;
    if(euclid_mod(pow_nat(10,nat_of_int(0xc2610)),0xc2611) != 1) {
        MODPOW_FULL(0xc2611,10,0xc2610,32)
        assert false;
    }
}

lemma void p25519_0xc2611_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x3, 0x13, 0x61}) + 1 == 0xc2611;
{}

lemma void p25519_0xc2611_g10_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x3, 0x13, 0x61}, (pratt_pow_thing)(0xc2611,10));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x3, 0x13, 0x61}, (pratt_pow_thing)(0xc2611,10))) {
        int g = 10; int P = 0xc2611;
        PRATT_FACTOR(P,g,0x61,16)
        PRATT_FACTOR(P,g,0x13,16)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0xc2611_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0xc2611);
{
    PRATT_BUILD_PRELUDE(0xc2611,10)
    PRATT_BUILD_SMALL(0x61)
    PRATT_BUILD_SMALL(0x13)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x48e467_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(0x48e466)),0x48e467) == 1;
{
    assert (0x48e466/0x100000000) == 0;
    if(euclid_mod(pow_nat(5,nat_of_int(0x48e466)),0x48e467) != 1) {
        MODPOW_FULL(0x48e467,5,0x48e466,32)
        assert false;
    }
}

lemma void p25519_0x48e467_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0xc2611}) + 1 == 0x48e467;
{}

lemma void p25519_0x48e467_g5_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0xc2611}, (pratt_pow_thing)(0x48e467,5));
{
    if(!forall({0x2, 0x3, 0xc2611}, (pratt_pow_thing)(0x48e467,5))) {
        int g = 5; int P = 0x48e467;
        PRATT_FACTOR(P,g,0xc2611,4)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x48e467_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x48e467);
{
    PRATT_BUILD_PRELUDE(0x48e467,5)
    PRATT_BUILD_BIG(0xc2611)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x643a0db_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x643a0da)),0x643a0db) == 1;
{
    assert (0x643a0da/0x100000000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x643a0da)),0x643a0db) != 1) {
        MODPOW_FULL(0x643a0db,2,0x643a0da,32)
        assert false;
    }
}

lemma void p25519_0x643a0db_1_factors()
    requires true;
    ensures  product({0x2, 0xb, 0x48e467}) + 1 == 0x643a0db;
{}

lemma void p25519_0x643a0db_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0xb, 0x48e467}, (pratt_pow_thing)(0x643a0db,2));
{
    if(!forall({0x2, 0xb, 0x48e467}, (pratt_pow_thing)(0x643a0db,2))) {
        int g = 2; int P = 0x643a0db;
        PRATT_FACTOR(P,g,0x48e467,8)
        PRATT_FACTOR(P,g,0xb,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x643a0db_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x643a0db);
{
    PRATT_BUILD_PRELUDE(0x643a0db,2)
    PRATT_BUILD_BIG(0x48e467)
    PRATT_BUILD_SMALL(0xb)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x316d_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x316c)),0x316d) == 1;
{
    assert (0x316c/0x10000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x316c)),0x316d) != 1) {
        MODPOW_FULL(0x316d,2,0x316c,16)
        assert false;
    }
}

lemma void p25519_0x316d_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0xc5b}) + 1 == 0x316d;
{}

lemma void p25519_0x316d_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0xc5b}, (pratt_pow_thing)(0x316d,2));
{
    if(!forall({0x2, 0x2, 0xc5b}, (pratt_pow_thing)(0x316d,2))) {
        int g = 2; int P = 0x316d;
        PRATT_FACTOR(P,g,0xc5b,4)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x316d_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x316d);
{
    PRATT_BUILD_PRELUDE(0x316d,2)
    PRATT_BUILD_SMALL(0xc5b)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x5efd_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x5efc)),0x5efd) == 1;
{
    assert (0x5efc/0x10000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x5efc)),0x5efd) != 1) {
        MODPOW_FULL(0x5efd,2,0x5efc,16)
        assert false;
    }
}

lemma void p25519_0x5efd_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x17bf}) + 1 == 0x5efd;
{}

lemma void p25519_0x5efd_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x17bf}, (pratt_pow_thing)(0x5efd,2));
{
    if(!forall({0x2, 0x2, 0x17bf}, (pratt_pow_thing)(0x5efd,2))) {
        int g = 2; int P = 0x5efd;
        PRATT_FACTOR(P,g,0x17bf,4)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x5efd_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x5efd);
{
    PRATT_BUILD_PRELUDE(0x5efd,2)
    PRATT_BUILD_SMALL(0x17bf)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x115b1_g11_generates()
    requires true;
    ensures  euclid_mod(pow_nat(11,nat_of_int(0x115b0)),0x115b1) == 1;
{
    assert (0x115b0/0x100000000) == 0;
    if(euclid_mod(pow_nat(11,nat_of_int(0x115b0)),0x115b1) != 1) {
        MODPOW_FULL(0x115b1,11,0x115b0,32)
        assert false;
    }
}

lemma void p25519_0x115b1_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x3, 0x5c9}) + 1 == 0x115b1;
{}

lemma void p25519_0x115b1_g11_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x3, 0x5c9}, (pratt_pow_thing)(0x115b1,11));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x3, 0x5c9}, (pratt_pow_thing)(0x115b1,11))) {
        int g = 11; int P = 0x115b1;
        PRATT_FACTOR(P,g,0x5c9,8)
        PRATT_FACTOR(P,g,0x3,16)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x115b1_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x115b1);
{
    PRATT_BUILD_PRELUDE(0x115b1,11)
    PRATT_BUILD_SMALL(0x5c9)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x456c5_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x456c4)),0x456c5) == 1;
{
    assert (0x456c4/0x100000000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x456c4)),0x456c5) != 1) {
        MODPOW_FULL(0x456c5,2,0x456c4,32)
        assert false;
    }
}

lemma void p25519_0x456c5_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x115b1}) + 1 == 0x456c5;
{}

lemma void p25519_0x456c5_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x115b1}, (pratt_pow_thing)(0x456c5,2));
{
    if(!forall({0x2, 0x2, 0x115b1}, (pratt_pow_thing)(0x456c5,2))) {
        int g = 2; int P = 0x456c5;
        PRATT_FACTOR(P,g,0x115b1,4)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x456c5_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x456c5);
{
    PRATT_BUILD_PRELUDE(0x456c5,2)
    PRATT_BUILD_BIG(0x115b1)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x6cc905a943f3_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x6cc905a943f2)),0x6cc905a943f3) == 1;
{
    assert (0x6cc905a943f2/0x10000000000000000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x6cc905a943f2)),0x6cc905a943f3) != 1) {
        MODPOW_FULL(0x6cc905a943f3,2,0x6cc905a943f2,64)
        assert false;
    }
}

lemma void p25519_0x6cc905a943f3_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0x3, 0x1f, 0x1f, 0x5efd, 0x456c5}) + 1 == 0x6cc905a943f3;
{}

lemma void p25519_0x6cc905a943f3_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0x3, 0x1f, 0x1f, 0x5efd, 0x456c5}, (pratt_pow_thing)(0x6cc905a943f3,2));
{
    if(!forall({0x2, 0x3, 0x3, 0x1f, 0x1f, 0x5efd, 0x456c5}, (pratt_pow_thing)(0x6cc905a943f3,2))) {
        int g = 2; int P = 0x6cc905a943f3;
        PRATT_FACTOR(P,g,0x456c5,32)
        PRATT_FACTOR(P,g,0x5efd,64)
        PRATT_FACTOR(P,g,0x1f,64)
        PRATT_FACTOR(P,g,0x3,64)
        PRATT_FACTOR(P,g,0x2,64)
        assert false;
    }
}

lemma pratt_cert p25519_0x6cc905a943f3_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x6cc905a943f3);
{
    PRATT_BUILD_PRELUDE(0x6cc905a943f3,2)
    PRATT_BUILD_BIG(0x456c5)
    PRATT_BUILD_BIG(0x5efd)
    PRATT_BUILD_SMALL(0x1f)
    PRATT_BUILD_SMALL(0x1f)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x98e88acf5891cd4e1a5_g6_generates()
    requires true;
    ensures  euclid_mod(pow_nat(6,nat_of_int(0x98e88acf5891cd4e1a4)),0x98e88acf5891cd4e1a5) == 1;
{
    assert (0x98e88acf5891cd4e1a4/0x100000000000000000000000000000000) == 0;
    if(euclid_mod(pow_nat(6,nat_of_int(0x98e88acf5891cd4e1a4)),0x98e88acf5891cd4e1a5) != 1) {
        MODPOW_FULL(0x98e88acf5891cd4e1a5,6,0x98e88acf5891cd4e1a4,128)
        assert false;
    }
}

lemma void p25519_0x98e88acf5891cd4e1a5_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x3, 0x5, 0x7, 0x47, 0x316d, 0x6cc905a943f3}) + 1 == 0x98e88acf5891cd4e1a5;
{}

lemma void p25519_0x98e88acf5891cd4e1a5_g6_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x3, 0x5, 0x7, 0x47, 0x316d, 0x6cc905a943f3}, (pratt_pow_thing)(0x98e88acf5891cd4e1a5,6));
{
    if(!forall({0x2, 0x2, 0x3, 0x5, 0x7, 0x47, 0x316d, 0x6cc905a943f3}, (pratt_pow_thing)(0x98e88acf5891cd4e1a5,6))) {
        int g = 6; int P = 0x98e88acf5891cd4e1a5;
        PRATT_FACTOR(P,g,0x6cc905a943f3,32)
        PRATT_FACTOR(P,g,0x316d,64)
        PRATT_FACTOR(P,g,0x47,128)
        PRATT_FACTOR(P,g,0x7,128)
        PRATT_FACTOR(P,g,0x5,128)
        PRATT_FACTOR(P,g,0x3,128)
        PRATT_FACTOR(P,g,0x2,128)
        assert false;
    }
}

lemma pratt_cert p25519_0x98e88acf5891cd4e1a5_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x98e88acf5891cd4e1a5);
{
    PRATT_BUILD_PRELUDE(0x98e88acf5891cd4e1a5,6)
    PRATT_BUILD_BIG(0x6cc905a943f3)
    PRATT_BUILD_BIG(0x316d)
    PRATT_BUILD_SMALL(0x47)
    PRATT_BUILD_SMALL(0x7)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0xdd89_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(0xdd88)),0xdd89) == 1;
{
    assert (0xdd88/0x10000) == 0;
    if(euclid_mod(pow_nat(5,nat_of_int(0xdd88)),0xdd89) != 1) {
        MODPOW_FULL(0xdd89,5,0xdd88,16)
        assert false;
    }
}

lemma void p25519_0xdd89_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x3, 0x11, 0x8b}) + 1 == 0xdd89;
{}

lemma void p25519_0xdd89_g5_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x3, 0x11, 0x8b}, (pratt_pow_thing)(0xdd89,5));
{
    if(!forall({0x2, 0x2, 0x2, 0x3, 0x11, 0x8b}, (pratt_pow_thing)(0xdd89,5))) {
        int g = 5; int P = 0xdd89;
        PRATT_FACTOR(P,g,0x8b,16)
        PRATT_FACTOR(P,g,0x11,16)
        PRATT_FACTOR(P,g,0x3,16)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0xdd89_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0xdd89);
{
    PRATT_BUILD_PRELUDE(0xdd89,5)
    PRATT_BUILD_SMALL(0x8b)
    PRATT_BUILD_SMALL(0x11)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x79b606a54f_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x79b606a54e)),0x79b606a54f) == 1;
{
    assert (0x79b606a54e/0x10000000000000000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x79b606a54e)),0x79b606a54f) != 1) {
        MODPOW_FULL(0x79b606a54f,3,0x79b606a54e,64)
        assert false;
    }
}

lemma void p25519_0x79b606a54f_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0x29, 0x59, 0x1a5, 0xdd89}) + 1 == 0x79b606a54f;
{}

lemma void p25519_0x79b606a54f_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0x29, 0x59, 0x1a5, 0xdd89}, (pratt_pow_thing)(0x79b606a54f,3));
{
    if(!forall({0x2, 0x3, 0x29, 0x59, 0x1a5, 0xdd89}, (pratt_pow_thing)(0x79b606a54f,3))) {
        int g = 3; int P = 0x79b606a54f;
        PRATT_FACTOR(P,g,0xdd89,32)
        PRATT_FACTOR(P,g,0x1a5,32)
        PRATT_FACTOR(P,g,0x59,64)
        PRATT_FACTOR(P,g,0x29,64)
        PRATT_FACTOR(P,g,0x3,64)
        PRATT_FACTOR(P,g,0x2,64)
        assert false;
    }
}

lemma pratt_cert p25519_0x79b606a54f_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x79b606a54f);
{
    PRATT_BUILD_PRELUDE(0x79b606a54f,3)
    PRATT_BUILD_BIG(0xdd89)
    PRATT_BUILD_SMALL(0x1a5)
    PRATT_BUILD_SMALL(0x59)
    PRATT_BUILD_SMALL(0x29)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x89da3_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(0x89da2)),0x89da3) == 1;
{
    assert (0x89da2/0x100000000) == 0;
    if(euclid_mod(pow_nat(5,nat_of_int(0x89da2)),0x89da3) != 1) {
        MODPOW_FULL(0x89da3,5,0x89da2,32)
        assert false;
    }
}

lemma void p25519_0x89da3_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0x3, 0xd, 0x13, 0x7f}) + 1 == 0x89da3;
{}

lemma void p25519_0x89da3_g5_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0x3, 0xd, 0x13, 0x7f}, (pratt_pow_thing)(0x89da3,5));
{
    if(!forall({0x2, 0x3, 0x3, 0xd, 0x13, 0x7f}, (pratt_pow_thing)(0x89da3,5))) {
        int g = 5; int P = 0x89da3;
        PRATT_FACTOR(P,g,0x7f,16)
        PRATT_FACTOR(P,g,0x13,16)
        PRATT_FACTOR(P,g,0xd,16)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x89da3_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x89da3);
{
    PRATT_BUILD_PRELUDE(0x89da3,5)
    PRATT_BUILD_SMALL(0x7f)
    PRATT_BUILD_SMALL(0x13)
    PRATT_BUILD_SMALL(0xd)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x6dc1_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x6dc0)),0x6dc1) == 1;
{
    assert (0x6dc0/0x10000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x6dc0)),0x6dc1) != 1) {
        MODPOW_FULL(0x6dc1,3,0x6dc0,16)
        assert false;
    }
}

lemma void p25519_0x6dc1_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x1b7}) + 1 == 0x6dc1;
{}

lemma void p25519_0x6dc1_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x1b7}, (pratt_pow_thing)(0x6dc1,3));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x1b7}, (pratt_pow_thing)(0x6dc1,3))) {
        int g = 3; int P = 0x6dc1;
        PRATT_FACTOR(P,g,0x1b7,8)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x6dc1_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x6dc1);
{
    PRATT_BUILD_PRELUDE(0x6dc1,3)
    PRATT_BUILD_SMALL(0x1b7)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x267949a57_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,nat_of_int(0x267949a56)),0x267949a57) == 1;
{
    assert (0x267949a56/0x10000000000000000) == 0;
    if(euclid_mod(pow_nat(7,nat_of_int(0x267949a56)),0x267949a57) != 1) {
        MODPOW_FULL(0x267949a57,7,0x267949a56,64)
        assert false;
    }
}

lemma void p25519_0x267949a57_1_factors()
    requires true;
    ensures  product({0x2, 0x11, 0x13, 0x239, 0x6dc1}) + 1 == 0x267949a57;
{}

lemma void p25519_0x267949a57_g7_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x11, 0x13, 0x239, 0x6dc1}, (pratt_pow_thing)(0x267949a57,7));
{
    if(!forall({0x2, 0x11, 0x13, 0x239, 0x6dc1}, (pratt_pow_thing)(0x267949a57,7))) {
        int g = 7; int P = 0x267949a57;
        PRATT_FACTOR(P,g,0x6dc1,32)
        PRATT_FACTOR(P,g,0x239,32)
        PRATT_FACTOR(P,g,0x13,32)
        PRATT_FACTOR(P,g,0x11,32)
        PRATT_FACTOR(P,g,0x2,64)
        assert false;
    }
}

lemma pratt_cert p25519_0x267949a57_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x267949a57);
{
    PRATT_BUILD_PRELUDE(0x267949a57,7)
    PRATT_BUILD_BIG(0x6dc1)
    PRATT_BUILD_SMALL(0x239)
    PRATT_BUILD_SMALL(0x13)
    PRATT_BUILD_SMALL(0x11)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x48a9ca9eec8cee3d7_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(0x48a9ca9eec8cee3d6)),0x48a9ca9eec8cee3d7) == 1;
{
    assert (0x48a9ca9eec8cee3d6/0x100000000000000000000000000000000) == 0;
    if(euclid_mod(pow_nat(5,nat_of_int(0x48a9ca9eec8cee3d6)),0x48a9ca9eec8cee3d7) != 1) {
        MODPOW_FULL(0x48a9ca9eec8cee3d7,5,0x48a9ca9eec8cee3d6,128)
        assert false;
    }
}

lemma void p25519_0x48a9ca9eec8cee3d7_1_factors()
    requires true;
    ensures  product({0x2, 0xb, 0x28d, 0x89da3, 0x267949a57}) + 1 == 0x48a9ca9eec8cee3d7;
{}

lemma void p25519_0x48a9ca9eec8cee3d7_g5_exact_order()
    requires true;
    ensures  !!forall({0x2, 0xb, 0x28d, 0x89da3, 0x267949a57}, (pratt_pow_thing)(0x48a9ca9eec8cee3d7,5));
{
    if(!forall({0x2, 0xb, 0x28d, 0x89da3, 0x267949a57}, (pratt_pow_thing)(0x48a9ca9eec8cee3d7,5))) {
        int g = 5; int P = 0x48a9ca9eec8cee3d7;
        PRATT_FACTOR(P,g,0x267949a57,64)
        PRATT_FACTOR(P,g,0x89da3,64)
        PRATT_FACTOR(P,g,0x28d,64)
        PRATT_FACTOR(P,g,0xb,64)
        PRATT_FACTOR(P,g,0x2,128)
        assert false;
    }
}

lemma pratt_cert p25519_0x48a9ca9eec8cee3d7_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x48a9ca9eec8cee3d7);
{
    PRATT_BUILD_PRELUDE(0x48a9ca9eec8cee3d7,5)
    PRATT_BUILD_BIG(0x267949a57)
    PRATT_BUILD_BIG(0x89da3)
    PRATT_BUILD_SMALL(0x28d)
    PRATT_BUILD_SMALL(0xb)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x1145f5af08b340269c840ddf12c9_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x1145f5af08b340269c840ddf12c8)),0x1145f5af08b340269c840ddf12c9) == 1;
{
    assert (0x1145f5af08b340269c840ddf12c8/0x100000000000000000000000000000000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x1145f5af08b340269c840ddf12c8)),0x1145f5af08b340269c840ddf12c9) != 1) {
        MODPOW_FULL(0x1145f5af08b340269c840ddf12c9,3,0x1145f5af08b340269c840ddf12c8,128)
        assert false;
    }
}

lemma void p25519_0x1145f5af08b340269c840ddf12c9_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x79b606a54f, 0x48a9ca9eec8cee3d7}) + 1 == 0x1145f5af08b340269c840ddf12c9;
{}

lemma void p25519_0x1145f5af08b340269c840ddf12c9_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x79b606a54f, 0x48a9ca9eec8cee3d7}, (pratt_pow_thing)(0x1145f5af08b340269c840ddf12c9,3));
{
    if(!forall({0x2, 0x2, 0x2, 0x79b606a54f, 0x48a9ca9eec8cee3d7}, (pratt_pow_thing)(0x1145f5af08b340269c840ddf12c9,3))) {
        int g = 3; int P = 0x1145f5af08b340269c840ddf12c9;
        PRATT_FACTOR(P,g,0x48a9ca9eec8cee3d7,64)
        PRATT_FACTOR(P,g,0x79b606a54f,128)
        PRATT_FACTOR(P,g,0x2,128)
        assert false;
    }
}

lemma pratt_cert p25519_0x1145f5af08b340269c840ddf12c9_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x1145f5af08b340269c840ddf12c9);
{
    PRATT_BUILD_PRELUDE(0x1145f5af08b340269c840ddf12c9,3)
    PRATT_BUILD_BIG(0x48a9ca9eec8cee3d7)
    PRATT_BUILD_BIG(0x79b606a54f)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x702431065a7bba7aac21520e3bf4ef_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x702431065a7bba7aac21520e3bf4ee)),0x702431065a7bba7aac21520e3bf4ef) == 1;
{
    assert (0x702431065a7bba7aac21520e3bf4ee/0x100000000000000000000000000000000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x702431065a7bba7aac21520e3bf4ee)),0x702431065a7bba7aac21520e3bf4ef) != 1) {
        MODPOW_FULL(0x702431065a7bba7aac21520e3bf4ef,3,0x702431065a7bba7aac21520e3bf4ee,128)
        assert false;
    }
}

lemma void p25519_0x702431065a7bba7aac21520e3bf4ef_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0x115, 0x1145f5af08b340269c840ddf12c9}) + 1 == 0x702431065a7bba7aac21520e3bf4ef;
{}

lemma void p25519_0x702431065a7bba7aac21520e3bf4ef_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0x115, 0x1145f5af08b340269c840ddf12c9}, (pratt_pow_thing)(0x702431065a7bba7aac21520e3bf4ef,3));
{
    if(!forall({0x2, 0x3, 0x115, 0x1145f5af08b340269c840ddf12c9}, (pratt_pow_thing)(0x702431065a7bba7aac21520e3bf4ef,3))) {
        int g = 3; int P = 0x702431065a7bba7aac21520e3bf4ef;
        PRATT_FACTOR(P,g,0x1145f5af08b340269c840ddf12c9,16)
        PRATT_FACTOR(P,g,0x115,128)
        PRATT_FACTOR(P,g,0x3,128)
        PRATT_FACTOR(P,g,0x2,128)
        assert false;
    }
}

lemma pratt_cert p25519_0x702431065a7bba7aac21520e3bf4ef_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x702431065a7bba7aac21520e3bf4ef);
{
    PRATT_BUILD_PRELUDE(0x702431065a7bba7aac21520e3bf4ef,3)
    PRATT_BUILD_BIG(0x1145f5af08b340269c840ddf12c9)
    PRATT_BUILD_SMALL(0x115)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x4c73_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x4c72)),0x4c73) == 1;
{
    assert (0x4c72/0x10000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x4c72)),0x4c73) != 1) {
        MODPOW_FULL(0x4c73,2,0x4c72,16)
        assert false;
    }
}

lemma void p25519_0x4c73_1_factors()
    requires true;
    ensures  product({0x2, 0x5, 0x13, 0x67}) + 1 == 0x4c73;
{}

lemma void p25519_0x4c73_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x5, 0x13, 0x67}, (pratt_pow_thing)(0x4c73,2));
{
    if(!forall({0x2, 0x5, 0x13, 0x67}, (pratt_pow_thing)(0x4c73,2))) {
        int g = 2; int P = 0x4c73;
        PRATT_FACTOR(P,g,0x67,8)
        PRATT_FACTOR(P,g,0x13,16)
        PRATT_FACTOR(P,g,0x5,16)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x4c73_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x4c73);
{
    PRATT_BUILD_PRELUDE(0x4c73,2)
    PRATT_BUILD_SMALL(0x67)
    PRATT_BUILD_SMALL(0x13)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0xfae7_g12_generates()
    requires true;
    ensures  euclid_mod(pow_nat(12,nat_of_int(0xfae6)),0xfae7) == 1;
{
    assert (0xfae6/0x10000) == 0;
    if(euclid_mod(pow_nat(12,nat_of_int(0xfae6)),0xfae7) != 1) {
        MODPOW_FULL(0xfae7,12,0xfae6,16)
        assert false;
    }
}

lemma void p25519_0xfae7_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0x5, 0x85d}) + 1 == 0xfae7;
{}

lemma void p25519_0xfae7_g12_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0x5, 0x85d}, (pratt_pow_thing)(0xfae7,12));
{
    if(!forall({0x2, 0x3, 0x5, 0x85d}, (pratt_pow_thing)(0xfae7,12))) {
        int g = 12; int P = 0xfae7;
        PRATT_FACTOR(P,g,0x85d,8)
        PRATT_FACTOR(P,g,0x5,16)
        PRATT_FACTOR(P,g,0x3,16)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0xfae7_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0xfae7);
{
    PRATT_BUILD_PRELUDE(0xfae7,12)
    PRATT_BUILD_SMALL(0x85d)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0xce15_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0xce14)),0xce15) == 1;
{
    assert (0xce14/0x10000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0xce14)),0xce15) != 1) {
        MODPOW_FULL(0xce15,2,0xce14,16)
        assert false;
    }
}

lemma void p25519_0xce15_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0xb, 0xb, 0x6d}) + 1 == 0xce15;
{}

lemma void p25519_0xce15_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0xb, 0xb, 0x6d}, (pratt_pow_thing)(0xce15,2));
{
    if(!forall({0x2, 0x2, 0xb, 0xb, 0x6d}, (pratt_pow_thing)(0xce15,2))) {
        int g = 2; int P = 0xce15;
        PRATT_FACTOR(P,g,0x6d,16)
        PRATT_FACTOR(P,g,0xb,16)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0xce15_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0xce15);
{
    PRATT_BUILD_PRELUDE(0xce15,2)
    PRATT_BUILD_SMALL(0x6d)
    PRATT_BUILD_SMALL(0xb)
    PRATT_BUILD_SMALL(0xb)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x1019a5_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x1019a4)),0x1019a5) == 1;
{
    assert (0x1019a4/0x100000000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x1019a4)),0x1019a5) != 1) {
        MODPOW_FULL(0x1019a5,2,0x1019a4,32)
        assert false;
    }
}

lemma void p25519_0x1019a5_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x5, 0xce15}) + 1 == 0x1019a5;
{}

lemma void p25519_0x1019a5_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x5, 0xce15}, (pratt_pow_thing)(0x1019a5,2));
{
    if(!forall({0x2, 0x2, 0x5, 0xce15}, (pratt_pow_thing)(0x1019a5,2))) {
        int g = 2; int P = 0x1019a5;
        PRATT_FACTOR(P,g,0xce15,8)
        PRATT_FACTOR(P,g,0x5,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x1019a5_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x1019a5);
{
    PRATT_BUILD_PRELUDE(0x1019a5,2)
    PRATT_BUILD_BIG(0xce15)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x121cd9b_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x121cd9a)),0x121cd9b) == 1;
{
    assert (0x121cd9a/0x100000000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x121cd9a)),0x121cd9b) != 1) {
        MODPOW_FULL(0x121cd9b,2,0x121cd9a,32)
        assert false;
    }
}

lemma void p25519_0x121cd9b_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0x3, 0x1019a5}) + 1 == 0x121cd9b;
{}

lemma void p25519_0x121cd9b_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0x3, 0x1019a5}, (pratt_pow_thing)(0x121cd9b,2));
{
    if(!forall({0x2, 0x3, 0x3, 0x1019a5}, (pratt_pow_thing)(0x121cd9b,2))) {
        int g = 2; int P = 0x121cd9b;
        PRATT_FACTOR(P,g,0x1019a5,8)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x121cd9b_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x121cd9b);
{
    PRATT_BUILD_PRELUDE(0x121cd9b,2)
    PRATT_BUILD_BIG(0x1019a5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0xc905_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0xc904)),0xc905) == 1;
{
    assert (0xc904/0x10000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0xc904)),0xc905) != 1) {
        MODPOW_FULL(0xc905,2,0xc904,16)
        assert false;
    }
}

lemma void p25519_0xc905_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x5, 0x1f, 0x53}) + 1 == 0xc905;
{}

lemma void p25519_0xc905_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x5, 0x1f, 0x53}, (pratt_pow_thing)(0xc905,2));
{
    if(!forall({0x2, 0x2, 0x5, 0x1f, 0x53}, (pratt_pow_thing)(0xc905,2))) {
        int g = 2; int P = 0xc905;
        PRATT_FACTOR(P,g,0x53,16)
        PRATT_FACTOR(P,g,0x1f,16)
        PRATT_FACTOR(P,g,0x5,16)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0xc905_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0xc905);
{
    PRATT_BUILD_PRELUDE(0xc905,2)
    PRATT_BUILD_SMALL(0x53)
    PRATT_BUILD_SMALL(0x1f)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x16839b5d_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x16839b5c)),0x16839b5d) == 1;
{
    assert (0x16839b5c/0x100000000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x16839b5c)),0x16839b5d) != 1) {
        MODPOW_FULL(0x16839b5d,3,0x16839b5c,32)
        assert false;
    }
}

lemma void p25519_0x16839b5d_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x5, 0x16f, 0xc905}) + 1 == 0x16839b5d;
{}

lemma void p25519_0x16839b5d_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x5, 0x16f, 0xc905}, (pratt_pow_thing)(0x16839b5d,3));
{
    if(!forall({0x2, 0x2, 0x5, 0x16f, 0xc905}, (pratt_pow_thing)(0x16839b5d,3))) {
        int g = 3; int P = 0x16839b5d;
        PRATT_FACTOR(P,g,0xc905,16)
        PRATT_FACTOR(P,g,0x16f,32)
        PRATT_FACTOR(P,g,0x5,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x16839b5d_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x16839b5d);
{
    PRATT_BUILD_PRELUDE(0x16839b5d,3)
    PRATT_BUILD_BIG(0xc905)
    PRATT_BUILD_SMALL(0x16f)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x85bf7_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x85bf6)),0x85bf7) == 1;
{
    assert (0x85bf6/0x100000000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x85bf6)),0x85bf7) != 1) {
        MODPOW_FULL(0x85bf7,3,0x85bf6,32)
        assert false;
    }
}

lemma void p25519_0x85bf7_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0x3, 0x3, 0x5, 0x7ed}) + 1 == 0x85bf7;
{}

lemma void p25519_0x85bf7_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0x3, 0x3, 0x5, 0x7ed}, (pratt_pow_thing)(0x85bf7,3));
{
    if(!forall({0x2, 0x3, 0x3, 0x3, 0x5, 0x7ed}, (pratt_pow_thing)(0x85bf7,3))) {
        int g = 3; int P = 0x85bf7;
        PRATT_FACTOR(P,g,0x7ed,16)
        PRATT_FACTOR(P,g,0x5,32)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x85bf7_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x85bf7);
{
    PRATT_BUILD_PRELUDE(0x85bf7,3)
    PRATT_BUILD_SMALL(0x7ed)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x27613d9b_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x27613d9a)),0x27613d9b) == 1;
{
    assert (0x27613d9a/0x100000000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x27613d9a)),0x27613d9b) != 1) {
        MODPOW_FULL(0x27613d9b,2,0x27613d9a,32)
        assert false;
    }
}

lemma void p25519_0x27613d9b_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0x3, 0x43, 0x85bf7}) + 1 == 0x27613d9b;
{}

lemma void p25519_0x27613d9b_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0x3, 0x43, 0x85bf7}, (pratt_pow_thing)(0x27613d9b,2));
{
    if(!forall({0x2, 0x3, 0x3, 0x43, 0x85bf7}, (pratt_pow_thing)(0x27613d9b,2))) {
        int g = 2; int P = 0x27613d9b;
        PRATT_FACTOR(P,g,0x85bf7,16)
        PRATT_FACTOR(P,g,0x43,32)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x27613d9b_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x27613d9b);
{
    PRATT_BUILD_PRELUDE(0x27613d9b,2)
    PRATT_BUILD_BIG(0x85bf7)
    PRATT_BUILD_SMALL(0x43)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x72c13649b1fcfc0b8fa3699c973301235_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x72c13649b1fcfc0b8fa3699c973301234)),0x72c13649b1fcfc0b8fa3699c973301235) == 1;
{
    assert (0x72c13649b1fcfc0b8fa3699c973301234/0x10000000000000000000000000000000000000000000000000000000000000000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x72c13649b1fcfc0b8fa3699c973301234)),0x72c13649b1fcfc0b8fa3699c973301235) != 1) {
        MODPOW_FULL(0x72c13649b1fcfc0b8fa3699c973301235,2,0x72c13649b1fcfc0b8fa3699c973301234,256)
        assert false;
    }
}

lemma void p25519_0x72c13649b1fcfc0b8fa3699c973301235_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x3, 0x5, 0x1aab, 0x4c73, 0xfae7, 0x121cd9b, 0x16839b5d, 0x27613d9b}) + 1 == 0x72c13649b1fcfc0b8fa3699c973301235;
{}

lemma void p25519_0x72c13649b1fcfc0b8fa3699c973301235_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x3, 0x5, 0x1aab, 0x4c73, 0xfae7, 0x121cd9b, 0x16839b5d, 0x27613d9b}, (pratt_pow_thing)(0x72c13649b1fcfc0b8fa3699c973301235,2));
{
    if(!forall({0x2, 0x2, 0x3, 0x5, 0x1aab, 0x4c73, 0xfae7, 0x121cd9b, 0x16839b5d, 0x27613d9b}, (pratt_pow_thing)(0x72c13649b1fcfc0b8fa3699c973301235,2))) {
        int g = 2; int P = 0x72c13649b1fcfc0b8fa3699c973301235;
        PRATT_FACTOR(P,g,0x27613d9b,128)
        PRATT_FACTOR(P,g,0x16839b5d,128)
        PRATT_FACTOR(P,g,0x121cd9b,128)
        PRATT_FACTOR(P,g,0xfae7,128)
        PRATT_FACTOR(P,g,0x4c73,128)
        PRATT_FACTOR(P,g,0x1aab,128)
        PRATT_FACTOR(P,g,0x5,256)
        PRATT_FACTOR(P,g,0x3,256)
        PRATT_FACTOR(P,g,0x2,256)
        assert false;
    }
}

lemma pratt_cert p25519_0x72c13649b1fcfc0b8fa3699c973301235_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x72c13649b1fcfc0b8fa3699c973301235);
{
    PRATT_BUILD_PRELUDE(0x72c13649b1fcfc0b8fa3699c973301235,2)
    PRATT_BUILD_BIG(0x27613d9b)
    PRATT_BUILD_BIG(0x16839b5d)
    PRATT_BUILD_BIG(0x121cd9b)
    PRATT_BUILD_BIG(0xfae7)
    PRATT_BUILD_BIG(0x4c73)
    PRATT_BUILD_SMALL(0x1aab)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x27b3_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x27b2)),0x27b3) == 1;
{
    assert (0x27b2/0x10000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x27b2)),0x27b3) != 1) {
        MODPOW_FULL(0x27b3,2,0x27b2,16)
        assert false;
    }
}

lemma void p25519_0x27b3_1_factors()
    requires true;
    ensures  product({0x2, 0x13d9}) + 1 == 0x27b3;
{}

lemma void p25519_0x27b3_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x13d9}, (pratt_pow_thing)(0x27b3,2));
{
    if(!forall({0x2, 0x13d9}, (pratt_pow_thing)(0x27b3,2))) {
        int g = 2; int P = 0x27b3;
        if(!pratt_pow_thing(P,g,0x13d9)) {
            pratt_pow_thing_auto(P,g,0x13d9);
            assert false;
        }
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x27b3_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x27b3);
{
    PRATT_BUILD_PRELUDE(0x27b3,2)
    PRATT_BUILD_SMALL(0x13d9)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x3a1f_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,nat_of_int(0x3a1e)),0x3a1f) == 1;
{
    assert (0x3a1e/0x10000) == 0;
    if(euclid_mod(pow_nat(7,nat_of_int(0x3a1e)),0x3a1f) != 1) {
        MODPOW_FULL(0x3a1f,7,0x3a1e,16)
        assert false;
    }
}

lemma void p25519_0x3a1f_1_factors()
    requires true;
    ensures  product({0x2, 0x2b, 0xad}) + 1 == 0x3a1f;
{}

lemma void p25519_0x3a1f_g7_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2b, 0xad}, (pratt_pow_thing)(0x3a1f,7));
{
    if(!forall({0x2, 0x2b, 0xad}, (pratt_pow_thing)(0x3a1f,7))) {
        int g = 7; int P = 0x3a1f;
        PRATT_FACTOR(P,g,0xad,8)
        PRATT_FACTOR(P,g,0x2b,16)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x3a1f_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x3a1f);
{
    PRATT_BUILD_PRELUDE(0x3a1f,7)
    PRATT_BUILD_SMALL(0xad)
    PRATT_BUILD_SMALL(0x2b)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x743f_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,nat_of_int(0x743e)),0x743f) == 1;
{
    assert (0x743e/0x10000) == 0;
    if(euclid_mod(pow_nat(7,nat_of_int(0x743e)),0x743f) != 1) {
        MODPOW_FULL(0x743f,7,0x743e,16)
        assert false;
    }
}

lemma void p25519_0x743f_1_factors()
    requires true;
    ensures  product({0x2, 0x3a1f}) + 1 == 0x743f;
{}

lemma void p25519_0x743f_g7_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3a1f}, (pratt_pow_thing)(0x743f,7));
{
    if(!forall({0x2, 0x3a1f}, (pratt_pow_thing)(0x743f,7))) {
        int g = 7; int P = 0x743f;
        if(!pratt_pow_thing(P,g,0x3a1f)) {
            pratt_pow_thing_auto(P,g,0x3a1f);
            assert false;
        }
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x743f_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x743f);
{
    PRATT_BUILD_PRELUDE(0x743f,7)
    PRATT_BUILD_BIG(0x3a1f)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x82c6f_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x82c6e)),0x82c6f) == 1;
{
    assert (0x82c6e/0x100000000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x82c6e)),0x82c6f) != 1) {
        MODPOW_FULL(0x82c6f,3,0x82c6e,32)
        assert false;
    }
}

lemma void p25519_0x82c6f_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0x3, 0x743f}) + 1 == 0x82c6f;
{}

lemma void p25519_0x82c6f_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0x3, 0x743f}, (pratt_pow_thing)(0x82c6f,3));
{
    if(!forall({0x2, 0x3, 0x3, 0x743f}, (pratt_pow_thing)(0x82c6f,3))) {
        int g = 3; int P = 0x82c6f;
        PRATT_FACTOR(P,g,0x743f,8)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x82c6f_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x82c6f);
{
    PRATT_BUILD_PRELUDE(0x82c6f,3)
    PRATT_BUILD_BIG(0x743f)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x146f159_g6_generates()
    requires true;
    ensures  euclid_mod(pow_nat(6,nat_of_int(0x146f158)),0x146f159) == 1;
{
    assert (0x146f158/0x100000000) == 0;
    if(euclid_mod(pow_nat(6,nat_of_int(0x146f158)),0x146f159) != 1) {
        MODPOW_FULL(0x146f159,6,0x146f158,32)
        assert false;
    }
}

lemma void p25519_0x146f159_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x5, 0x82c6f}) + 1 == 0x146f159;
{}

lemma void p25519_0x146f159_g6_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x5, 0x82c6f}, (pratt_pow_thing)(0x146f159,6));
{
    if(!forall({0x2, 0x2, 0x2, 0x5, 0x82c6f}, (pratt_pow_thing)(0x146f159,6))) {
        int g = 6; int P = 0x146f159;
        PRATT_FACTOR(P,g,0x82c6f,8)
        PRATT_FACTOR(P,g,0x5,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x146f159_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x146f159);
{
    PRATT_BUILD_PRELUDE(0x146f159,6)
    PRATT_BUILD_BIG(0x82c6f)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x28de2b3_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x28de2b2)),0x28de2b3) == 1;
{
    assert (0x28de2b2/0x100000000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x28de2b2)),0x28de2b3) != 1) {
        MODPOW_FULL(0x28de2b3,2,0x28de2b2,32)
        assert false;
    }
}

lemma void p25519_0x28de2b3_1_factors()
    requires true;
    ensures  product({0x2, 0x146f159}) + 1 == 0x28de2b3;
{}

lemma void p25519_0x28de2b3_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x146f159}, (pratt_pow_thing)(0x28de2b3,2));
{
    if(!forall({0x2, 0x146f159}, (pratt_pow_thing)(0x28de2b3,2))) {
        int g = 2; int P = 0x28de2b3;
        if(!pratt_pow_thing(P,g,0x146f159)) {
            pratt_pow_thing_auto(P,g,0x146f159);
            assert false;
        }
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x28de2b3_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x28de2b3);
{
    PRATT_BUILD_PRELUDE(0x28de2b3,2)
    PRATT_BUILD_BIG(0x146f159)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x78bdd14c35_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x78bdd14c34)),0x78bdd14c35) == 1;
{
    assert (0x78bdd14c34/0x10000000000000000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x78bdd14c34)),0x78bdd14c35) != 1) {
        MODPOW_FULL(0x78bdd14c35,2,0x78bdd14c34,64)
        assert false;
    }
}

lemma void p25519_0x78bdd14c35_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0xb, 0x11, 0x49, 0x43f, 0x2221}) + 1 == 0x78bdd14c35;
{}

lemma void p25519_0x78bdd14c35_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0xb, 0x11, 0x49, 0x43f, 0x2221}, (pratt_pow_thing)(0x78bdd14c35,2));
{
    if(!forall({0x2, 0x2, 0xb, 0x11, 0x49, 0x43f, 0x2221}, (pratt_pow_thing)(0x78bdd14c35,2))) {
        int g = 2; int P = 0x78bdd14c35;
        PRATT_FACTOR(P,g,0x2221,32)
        PRATT_FACTOR(P,g,0x43f,32)
        PRATT_FACTOR(P,g,0x49,64)
        PRATT_FACTOR(P,g,0x11,64)
        PRATT_FACTOR(P,g,0xb,64)
        PRATT_FACTOR(P,g,0x2,64)
        assert false;
    }
}

lemma pratt_cert p25519_0x78bdd14c35_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x78bdd14c35);
{
    PRATT_BUILD_PRELUDE(0x78bdd14c35,2)
    PRATT_BUILD_SMALL(0x2221)
    PRATT_BUILD_SMALL(0x43f)
    PRATT_BUILD_SMALL(0x49)
    PRATT_BUILD_SMALL(0x11)
    PRATT_BUILD_SMALL(0xb)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x29299_g14_generates()
    requires true;
    ensures  euclid_mod(pow_nat(14,nat_of_int(0x29298)),0x29299) == 1;
{
    assert (0x29298/0x100000000) == 0;
    if(euclid_mod(pow_nat(14,nat_of_int(0x29298)),0x29299) != 1) {
        MODPOW_FULL(0x29299,14,0x29298,32)
        assert false;
    }
}

lemma void p25519_0x29299_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x3, 0x5, 0x5, 0x119}) + 1 == 0x29299;
{}

lemma void p25519_0x29299_g14_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x3, 0x5, 0x5, 0x119}, (pratt_pow_thing)(0x29299,14));
{
    if(!forall({0x2, 0x2, 0x2, 0x3, 0x5, 0x5, 0x119}, (pratt_pow_thing)(0x29299,14))) {
        int g = 14; int P = 0x29299;
        PRATT_FACTOR(P,g,0x119,16)
        PRATT_FACTOR(P,g,0x5,16)
        PRATT_FACTOR(P,g,0x3,16)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x29299_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x29299);
{
    PRATT_BUILD_PRELUDE(0x29299,14)
    PRATT_BUILD_SMALL(0x119)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x24811_g17_generates()
    requires true;
    ensures  euclid_mod(pow_nat(17,nat_of_int(0x24810)),0x24811) == 1;
{
    assert (0x24810/0x100000000) == 0;
    if(euclid_mod(pow_nat(17,nat_of_int(0x24810)),0x24811) != 1) {
        MODPOW_FULL(0x24811,17,0x24810,32)
        assert false;
    }
}

lemma void p25519_0x24811_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x7, 0x59}) + 1 == 0x24811;
{}

lemma void p25519_0x24811_g17_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x7, 0x59}, (pratt_pow_thing)(0x24811,17));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x7, 0x59}, (pratt_pow_thing)(0x24811,17))) {
        int g = 17; int P = 0x24811;
        PRATT_FACTOR(P,g,0x59,16)
        PRATT_FACTOR(P,g,0x7,16)
        PRATT_FACTOR(P,g,0x5,16)
        PRATT_FACTOR(P,g,0x3,16)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x24811_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x24811);
{
    PRATT_BUILD_PRELUDE(0x24811,17)
    PRATT_BUILD_SMALL(0x59)
    PRATT_BUILD_SMALL(0x7)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x323177_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(0x323176)),0x323177) == 1;
{
    assert (0x323176/0x100000000) == 0;
    if(euclid_mod(pow_nat(5,nat_of_int(0x323176)),0x323177) != 1) {
        MODPOW_FULL(0x323177,5,0x323176,32)
        assert false;
    }
}

lemma void p25519_0x323177_1_factors()
    requires true;
    ensures  product({0x2, 0xb, 0x24811}) + 1 == 0x323177;
{}

lemma void p25519_0x323177_g5_exact_order()
    requires true;
    ensures  !!forall({0x2, 0xb, 0x24811}, (pratt_pow_thing)(0x323177,5));
{
    if(!forall({0x2, 0xb, 0x24811}, (pratt_pow_thing)(0x323177,5))) {
        int g = 5; int P = 0x323177;
        PRATT_FACTOR(P,g,0x24811,8)
        PRATT_FACTOR(P,g,0xb,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x323177_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x323177);
{
    PRATT_BUILD_PRELUDE(0x323177,5)
    PRATT_BUILD_BIG(0x24811)
    PRATT_BUILD_SMALL(0xb)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x6462ef_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(0x6462ee)),0x6462ef) == 1;
{
    assert (0x6462ee/0x100000000) == 0;
    if(euclid_mod(pow_nat(5,nat_of_int(0x6462ee)),0x6462ef) != 1) {
        MODPOW_FULL(0x6462ef,5,0x6462ee,32)
        assert false;
    }
}

lemma void p25519_0x6462ef_1_factors()
    requires true;
    ensures  product({0x2, 0x323177}) + 1 == 0x6462ef;
{}

lemma void p25519_0x6462ef_g5_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x323177}, (pratt_pow_thing)(0x6462ef,5));
{
    if(!forall({0x2, 0x323177}, (pratt_pow_thing)(0x6462ef,5))) {
        int g = 5; int P = 0x6462ef;
        if(!pratt_pow_thing(P,g,0x323177)) {
            pratt_pow_thing_auto(P,g,0x323177);
            assert false;
        }
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x6462ef_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x6462ef);
{
    PRATT_BUILD_PRELUDE(0x6462ef,5)
    PRATT_BUILD_BIG(0x323177)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x4eb0325fc583_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(0x4eb0325fc582)),0x4eb0325fc583) == 1;
{
    assert (0x4eb0325fc582/0x10000000000000000) == 0;
    if(euclid_mod(pow_nat(5,nat_of_int(0x4eb0325fc582)),0x4eb0325fc583) != 1) {
        MODPOW_FULL(0x4eb0325fc583,5,0x4eb0325fc582,64)
        assert false;
    }
}

lemma void p25519_0x4eb0325fc583_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0xd, 0x29299, 0x6462ef}) + 1 == 0x4eb0325fc583;
{}

lemma void p25519_0x4eb0325fc583_g5_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0xd, 0x29299, 0x6462ef}, (pratt_pow_thing)(0x4eb0325fc583,5));
{
    if(!forall({0x2, 0x3, 0xd, 0x29299, 0x6462ef}, (pratt_pow_thing)(0x4eb0325fc583,5))) {
        int g = 5; int P = 0x4eb0325fc583;
        PRATT_FACTOR(P,g,0x6462ef,32)
        PRATT_FACTOR(P,g,0x29299,32)
        PRATT_FACTOR(P,g,0xd,64)
        PRATT_FACTOR(P,g,0x3,64)
        PRATT_FACTOR(P,g,0x2,64)
        assert false;
    }
}

lemma pratt_cert p25519_0x4eb0325fc583_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x4eb0325fc583);
{
    PRATT_BUILD_PRELUDE(0x4eb0325fc583,5)
    PRATT_BUILD_BIG(0x6462ef)
    PRATT_BUILD_BIG(0x29299)
    PRATT_BUILD_SMALL(0xd)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x224cc15569db15601217b4a6c662ef599031_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x224cc15569db15601217b4a6c662ef599030)),0x224cc15569db15601217b4a6c662ef599031) == 1;
{
    assert (0x224cc15569db15601217b4a6c662ef599030/0x10000000000000000000000000000000000000000000000000000000000000000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x224cc15569db15601217b4a6c662ef599030)),0x224cc15569db15601217b4a6c662ef599031) != 1) {
        MODPOW_FULL(0x224cc15569db15601217b4a6c662ef599031,3,0x224cc15569db15601217b4a6c662ef599030,256)
        assert false;
    }
}

lemma void p25519_0x224cc15569db15601217b4a6c662ef599031_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x13, 0x1f7, 0x27b3, 0x28de2b3, 0x78bdd14c35, 0x4eb0325fc583}) + 1 == 0x224cc15569db15601217b4a6c662ef599031;
{}

lemma void p25519_0x224cc15569db15601217b4a6c662ef599031_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x13, 0x1f7, 0x27b3, 0x28de2b3, 0x78bdd14c35, 0x4eb0325fc583}, (pratt_pow_thing)(0x224cc15569db15601217b4a6c662ef599031,3));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x13, 0x1f7, 0x27b3, 0x28de2b3, 0x78bdd14c35, 0x4eb0325fc583}, (pratt_pow_thing)(0x224cc15569db15601217b4a6c662ef599031,3))) {
        int g = 3; int P = 0x224cc15569db15601217b4a6c662ef599031;
        PRATT_FACTOR(P,g,0x4eb0325fc583,128)
        PRATT_FACTOR(P,g,0x78bdd14c35,128)
        PRATT_FACTOR(P,g,0x28de2b3,128)
        PRATT_FACTOR(P,g,0x27b3,128)
        PRATT_FACTOR(P,g,0x1f7,256)
        PRATT_FACTOR(P,g,0x13,256)
        PRATT_FACTOR(P,g,0x2,256)
        assert false;
    }
}

lemma pratt_cert p25519_0x224cc15569db15601217b4a6c662ef599031_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x224cc15569db15601217b4a6c662ef599031);
{
    PRATT_BUILD_PRELUDE(0x224cc15569db15601217b4a6c662ef599031,3)
    PRATT_BUILD_BIG(0x4eb0325fc583)
    PRATT_BUILD_BIG(0x78bdd14c35)
    PRATT_BUILD_BIG(0x28de2b3)
    PRATT_BUILD_BIG(0x27b3)
    PRATT_BUILD_SMALL(0x1f7)
    PRATT_BUILD_SMALL(0x13)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,nat_of_int(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc6)),0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7) == 1;
{
    assert (0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc6/0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) == 0;
    if(euclid_mod(pow_nat(7,nat_of_int(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc6)),0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7) != 1) {
        MODPOW_FULL(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7,7,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc6,512)
        assert false;
    }
}

lemma void p25519_0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7_1_factors()
    requires true;
    ensures  product({0x2, 0x17, 0x29, 0x161, 0x643a0db, 0x98e88acf5891cd4e1a5, 0x702431065a7bba7aac21520e3bf4ef, 0x72c13649b1fcfc0b8fa3699c973301235, 0x224cc15569db15601217b4a6c662ef599031}) + 1 == 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7;
{}

lemma void p25519_0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7_g7_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x17, 0x29, 0x161, 0x643a0db, 0x98e88acf5891cd4e1a5, 0x702431065a7bba7aac21520e3bf4ef, 0x72c13649b1fcfc0b8fa3699c973301235, 0x224cc15569db15601217b4a6c662ef599031}, (pratt_pow_thing)(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7,7));
{
    if(!forall({0x2, 0x17, 0x29, 0x161, 0x643a0db, 0x98e88acf5891cd4e1a5, 0x702431065a7bba7aac21520e3bf4ef, 0x72c13649b1fcfc0b8fa3699c973301235, 0x224cc15569db15601217b4a6c662ef599031}, (pratt_pow_thing)(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7,7))) {
        int g = 7; int P = 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7;
        PRATT_FACTOR(P,g,0x224cc15569db15601217b4a6c662ef599031,512)
        PRATT_FACTOR(P,g,0x72c13649b1fcfc0b8fa3699c973301235,512)
        PRATT_FACTOR(P,g,0x702431065a7bba7aac21520e3bf4ef,512)
        PRATT_FACTOR(P,g,0x98e88acf5891cd4e1a5,512)
        PRATT_FACTOR(P,g,0x643a0db,512)
        PRATT_FACTOR(P,g,0x161,512)
        PRATT_FACTOR(P,g,0x29,512)
        PRATT_FACTOR(P,g,0x17,512)
        PRATT_FACTOR(P,g,0x2,512)
        assert false;
    }
}

lemma pratt_cert p25519_0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7);
{
    PRATT_BUILD_PRELUDE(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc7,7)
    PRATT_BUILD_BIG(0x224cc15569db15601217b4a6c662ef599031)
    PRATT_BUILD_BIG(0x72c13649b1fcfc0b8fa3699c973301235)
    PRATT_BUILD_BIG(0x702431065a7bba7aac21520e3bf4ef)
    PRATT_BUILD_BIG(0x98e88acf5891cd4e1a5)
    PRATT_BUILD_BIG(0x643a0db)
    PRATT_BUILD_SMALL(0x161)
    PRATT_BUILD_SMALL(0x29)
    PRATT_BUILD_SMALL(0x17)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}
  @*/

