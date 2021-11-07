/*@ #include "p25519.gh" @*/
/*@ #include "p569_generated.gh" @*/

/*@

lemma void p25519_796177_g10_generates()
    requires true;
    ensures  euclid_mod(pow_nat(10,nat_of_int(796176)),796177) == 1;
{
    if(euclid_mod(pow_nat(10,nat_of_int(796176)),796177) != 1) {
        MODPOW_FULL(796177,10,796176,32)
        assert false;
    }
}

lemma void p25519_796177_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 3, 3, 3, 19, 97}) + 1 == 796177;
{}

lemma void p25519_796177_g10_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 3, 3, 3, 19, 97}, (pratt_pow_thing)(796177,10));
{
    if(!forall({2, 2, 2, 2, 3, 3, 3, 19, 97}, (pratt_pow_thing)(796177,10))) {
        int g = 10; int P = 796177;
        PRATT_FACTOR(P,g,97,16)
        PRATT_FACTOR(P,g,19,16)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_796177_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,796177);
{
    PRATT_BUILD_PRELUDE(796177,10)
    PRATT_BUILD_SMALL(97)
    PRATT_BUILD_SMALL(19)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_4777063_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(4777062)),4777063) == 1;
{
    if(euclid_mod(pow_nat(5,nat_of_int(4777062)),4777063) != 1) {
        MODPOW_FULL(4777063,5,4777062,32)
        assert false;
    }
}

lemma void p25519_4777063_1_factors()
    requires true;
    ensures  product({2, 3, 796177}) + 1 == 4777063;
{}

lemma void p25519_4777063_g5_exact_order()
    requires true;
    ensures  !!forall({2, 3, 796177}, (pratt_pow_thing)(4777063,5));
{
    if(!forall({2, 3, 796177}, (pratt_pow_thing)(4777063,5))) {
        int g = 5; int P = 4777063;
        PRATT_FACTOR(P,g,796177,4)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_4777063_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,4777063);
{
    PRATT_BUILD_PRELUDE(4777063,5)
    PRATT_BUILD_BIG(796177)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_105095387_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(105095386)),105095387) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(105095386)),105095387) != 1) {
        MODPOW_FULL(105095387,2,105095386,32)
        assert false;
    }
}

lemma void p25519_105095387_1_factors()
    requires true;
    ensures  product({2, 11, 4777063}) + 1 == 105095387;
{}

lemma void p25519_105095387_g2_exact_order()
    requires true;
    ensures  !!forall({2, 11, 4777063}, (pratt_pow_thing)(105095387,2));
{
    if(!forall({2, 11, 4777063}, (pratt_pow_thing)(105095387,2))) {
        int g = 2; int P = 105095387;
        PRATT_FACTOR(P,g,4777063,8)
        PRATT_FACTOR(P,g,11,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_105095387_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,105095387);
{
    PRATT_BUILD_PRELUDE(105095387,2)
    PRATT_BUILD_BIG(4777063)
    PRATT_BUILD_SMALL(11)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_12653_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(12652)),12653) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(12652)),12653) != 1) {
        MODPOW_FULL(12653,2,12652,16)
        assert false;
    }
}

lemma void p25519_12653_1_factors()
    requires true;
    ensures  product({2, 2, 3163}) + 1 == 12653;
{}

lemma void p25519_12653_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3163}, (pratt_pow_thing)(12653,2));
{
    if(!forall({2, 2, 3163}, (pratt_pow_thing)(12653,2))) {
        int g = 2; int P = 12653;
        if(!pratt_pow_thing(P,g,3163)) {
            pratt_pow_thing_auto(P,g,3163);
            assert false;
        }
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_12653_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,12653);
{
    PRATT_BUILD_PRELUDE(12653,2)
    PRATT_BUILD_SMALL(3163)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_24317_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(24316)),24317) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(24316)),24317) != 1) {
        MODPOW_FULL(24317,2,24316,16)
        assert false;
    }
}

lemma void p25519_24317_1_factors()
    requires true;
    ensures  product({2, 2, 6079}) + 1 == 24317;
{}

lemma void p25519_24317_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 6079}, (pratt_pow_thing)(24317,2));
{
    if(!forall({2, 2, 6079}, (pratt_pow_thing)(24317,2))) {
        int g = 2; int P = 24317;
        if(!pratt_pow_thing(P,g,6079)) {
            pratt_pow_thing_auto(P,g,6079);
            assert false;
        }
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_24317_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,24317);
{
    PRATT_BUILD_PRELUDE(24317,2)
    PRATT_BUILD_SMALL(6079)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_71089_g11_generates()
    requires true;
    ensures  euclid_mod(pow_nat(11,nat_of_int(71088)),71089) == 1;
{
    if(euclid_mod(pow_nat(11,nat_of_int(71088)),71089) != 1) {
        MODPOW_FULL(71089,11,71088,32)
        assert false;
    }
}

lemma void p25519_71089_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 3, 1481}) + 1 == 71089;
{}

lemma void p25519_71089_g11_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 3, 1481}, (pratt_pow_thing)(71089,11));
{
    if(!forall({2, 2, 2, 2, 3, 1481}, (pratt_pow_thing)(71089,11))) {
        int g = 11; int P = 71089;
        PRATT_FACTOR(P,g,1481,8)
        PRATT_FACTOR(P,g,3,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_71089_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,71089);
{
    PRATT_BUILD_PRELUDE(71089,11)
    PRATT_BUILD_SMALL(1481)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_284357_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(284356)),284357) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(284356)),284357) != 1) {
        MODPOW_FULL(284357,2,284356,32)
        assert false;
    }
}

lemma void p25519_284357_1_factors()
    requires true;
    ensures  product({2, 2, 71089}) + 1 == 284357;
{}

lemma void p25519_284357_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 71089}, (pratt_pow_thing)(284357,2));
{
    if(!forall({2, 2, 71089}, (pratt_pow_thing)(284357,2))) {
        int g = 2; int P = 284357;
        if(!pratt_pow_thing(P,g,71089)) {
            pratt_pow_thing_auto(P,g,71089);
            assert false;
        }
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_284357_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,284357);
{
    PRATT_BUILD_PRELUDE(284357,2)
    PRATT_BUILD_BIG(71089)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_119610639205363_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(119610639205362)),119610639205363) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(119610639205362)),119610639205363) != 1) {
        MODPOW_FULL(119610639205363,2,119610639205362,64)
        assert false;
    }
}

lemma void p25519_119610639205363_1_factors()
    requires true;
    ensures  product({2, 3, 3, 31, 31, 24317, 284357}) + 1 == 119610639205363;
{}

lemma void p25519_119610639205363_g2_exact_order()
    requires true;
    ensures  !!forall({2, 3, 3, 31, 31, 24317, 284357}, (pratt_pow_thing)(119610639205363,2));
{
    if(!forall({2, 3, 3, 31, 31, 24317, 284357}, (pratt_pow_thing)(119610639205363,2))) {
        int g = 2; int P = 119610639205363;
        PRATT_FACTOR(P,g,284357,32)
        PRATT_FACTOR(P,g,24317,64)
        PRATT_FACTOR(P,g,31,64)
        PRATT_FACTOR(P,g,3,64)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_119610639205363_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,119610639205363);
{
    PRATT_BUILD_PRELUDE(119610639205363,2)
    PRATT_BUILD_BIG(284357)
    PRATT_BUILD_BIG(24317)
    PRATT_BUILD_SMALL(31)
    PRATT_BUILD_SMALL(31)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_45130584520747958722981_g6_generates()
    requires true;
    ensures  euclid_mod(pow_nat(6,nat_of_int(45130584520747958722980)),45130584520747958722981) == 1;
{
    if(euclid_mod(pow_nat(6,nat_of_int(45130584520747958722980)),45130584520747958722981) != 1) {
        MODPOW_FULL(45130584520747958722981,6,45130584520747958722980,128)
        assert false;
    }
}

lemma void p25519_45130584520747958722981_1_factors()
    requires true;
    ensures  product({2, 2, 3, 5, 7, 71, 12653, 119610639205363}) + 1 == 45130584520747958722981;
{}

lemma void p25519_45130584520747958722981_g6_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3, 5, 7, 71, 12653, 119610639205363}, (pratt_pow_thing)(45130584520747958722981,6));
{
    if(!forall({2, 2, 3, 5, 7, 71, 12653, 119610639205363}, (pratt_pow_thing)(45130584520747958722981,6))) {
        int g = 6; int P = 45130584520747958722981;
        PRATT_FACTOR(P,g,119610639205363,32)
        PRATT_FACTOR(P,g,12653,64)
        PRATT_FACTOR(P,g,71,128)
        PRATT_FACTOR(P,g,7,128)
        PRATT_FACTOR(P,g,5,128)
        PRATT_FACTOR(P,g,3,128)
        PRATT_FACTOR(P,g,2,128)
        assert false;
    }
}

lemma pratt_cert p25519_45130584520747958722981_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,45130584520747958722981);
{
    PRATT_BUILD_PRELUDE(45130584520747958722981,6)
    PRATT_BUILD_BIG(119610639205363)
    PRATT_BUILD_BIG(12653)
    PRATT_BUILD_SMALL(71)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_56713_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(56712)),56713) == 1;
{
    if(euclid_mod(pow_nat(5,nat_of_int(56712)),56713) != 1) {
        MODPOW_FULL(56713,5,56712,16)
        assert false;
    }
}

lemma void p25519_56713_1_factors()
    requires true;
    ensures  product({2, 2, 2, 3, 17, 139}) + 1 == 56713;
{}

lemma void p25519_56713_g5_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 3, 17, 139}, (pratt_pow_thing)(56713,5));
{
    if(!forall({2, 2, 2, 3, 17, 139}, (pratt_pow_thing)(56713,5))) {
        int g = 5; int P = 56713;
        PRATT_FACTOR(P,g,139,16)
        PRATT_FACTOR(P,g,17,16)
        PRATT_FACTOR(P,g,3,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_56713_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,56713);
{
    PRATT_BUILD_PRELUDE(56713,5)
    PRATT_BUILD_SMALL(139)
    PRATT_BUILD_SMALL(17)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_522744931663_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(522744931662)),522744931663) == 1;
{
    if(euclid_mod(pow_nat(3,nat_of_int(522744931662)),522744931663) != 1) {
        MODPOW_FULL(522744931663,3,522744931662,64)
        assert false;
    }
}

lemma void p25519_522744931663_1_factors()
    requires true;
    ensures  product({2, 3, 41, 89, 421, 56713}) + 1 == 522744931663;
{}

lemma void p25519_522744931663_g3_exact_order()
    requires true;
    ensures  !!forall({2, 3, 41, 89, 421, 56713}, (pratt_pow_thing)(522744931663,3));
{
    if(!forall({2, 3, 41, 89, 421, 56713}, (pratt_pow_thing)(522744931663,3))) {
        int g = 3; int P = 522744931663;
        PRATT_FACTOR(P,g,56713,32)
        PRATT_FACTOR(P,g,421,32)
        PRATT_FACTOR(P,g,89,64)
        PRATT_FACTOR(P,g,41,64)
        PRATT_FACTOR(P,g,3,64)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_522744931663_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,522744931663);
{
    PRATT_BUILD_PRELUDE(522744931663,3)
    PRATT_BUILD_BIG(56713)
    PRATT_BUILD_SMALL(421)
    PRATT_BUILD_SMALL(89)
    PRATT_BUILD_SMALL(41)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_564643_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(564642)),564643) == 1;
{
    if(euclid_mod(pow_nat(5,nat_of_int(564642)),564643) != 1) {
        MODPOW_FULL(564643,5,564642,32)
        assert false;
    }
}

lemma void p25519_564643_1_factors()
    requires true;
    ensures  product({2, 3, 3, 13, 19, 127}) + 1 == 564643;
{}

lemma void p25519_564643_g5_exact_order()
    requires true;
    ensures  !!forall({2, 3, 3, 13, 19, 127}, (pratt_pow_thing)(564643,5));
{
    if(!forall({2, 3, 3, 13, 19, 127}, (pratt_pow_thing)(564643,5))) {
        int g = 5; int P = 564643;
        PRATT_FACTOR(P,g,127,16)
        PRATT_FACTOR(P,g,19,16)
        PRATT_FACTOR(P,g,13,16)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_564643_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,564643);
{
    PRATT_BUILD_PRELUDE(564643,5)
    PRATT_BUILD_SMALL(127)
    PRATT_BUILD_SMALL(19)
    PRATT_BUILD_SMALL(13)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_28097_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(28096)),28097) == 1;
{
    if(euclid_mod(pow_nat(3,nat_of_int(28096)),28097) != 1) {
        MODPOW_FULL(28097,3,28096,16)
        assert false;
    }
}

lemma void p25519_28097_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 2, 2, 439}) + 1 == 28097;
{}

lemma void p25519_28097_g3_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 2, 2, 439}, (pratt_pow_thing)(28097,3));
{
    if(!forall({2, 2, 2, 2, 2, 2, 439}, (pratt_pow_thing)(28097,3))) {
        int g = 3; int P = 28097;
        PRATT_FACTOR(P,g,439,8)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_28097_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,28097);
{
    PRATT_BUILD_PRELUDE(28097,3)
    PRATT_BUILD_SMALL(439)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_10327726679_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,nat_of_int(10327726678)),10327726679) == 1;
{
    if(euclid_mod(pow_nat(7,nat_of_int(10327726678)),10327726679) != 1) {
        MODPOW_FULL(10327726679,7,10327726678,64)
        assert false;
    }
}

lemma void p25519_10327726679_1_factors()
    requires true;
    ensures  product({2, 17, 19, 569, 28097}) + 1 == 10327726679;
{}

lemma void p25519_10327726679_g7_exact_order()
    requires true;
    ensures  !!forall({2, 17, 19, 569, 28097}, (pratt_pow_thing)(10327726679,7));
{
    if(!forall({2, 17, 19, 569, 28097}, (pratt_pow_thing)(10327726679,7))) {
        int g = 7; int P = 10327726679;
        PRATT_FACTOR(P,g,28097,32)
        PRATT_FACTOR(P,g,569,32)
        PRATT_FACTOR(P,g,19,32)
        PRATT_FACTOR(P,g,17,32)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_10327726679_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,10327726679);
{
    PRATT_BUILD_PRELUDE(10327726679,7)
    PRATT_BUILD_BIG(28097)
    PRATT_BUILD_SMALL(569)
    PRATT_BUILD_SMALL(19)
    PRATT_BUILD_SMALL(17)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_83775021211475436503_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(83775021211475436502)),83775021211475436503) == 1;
{
    if(euclid_mod(pow_nat(5,nat_of_int(83775021211475436502)),83775021211475436503) != 1) {
        MODPOW_FULL(83775021211475436503,5,83775021211475436502,128)
        assert false;
    }
}

lemma void p25519_83775021211475436503_1_factors()
    requires true;
    ensures  product({2, 11, 653, 564643, 10327726679}) + 1 == 83775021211475436503;
{}

lemma void p25519_83775021211475436503_g5_exact_order()
    requires true;
    ensures  !!forall({2, 11, 653, 564643, 10327726679}, (pratt_pow_thing)(83775021211475436503,5));
{
    if(!forall({2, 11, 653, 564643, 10327726679}, (pratt_pow_thing)(83775021211475436503,5))) {
        int g = 5; int P = 83775021211475436503;
        PRATT_FACTOR(P,g,10327726679,64)
        PRATT_FACTOR(P,g,564643,64)
        PRATT_FACTOR(P,g,653,64)
        PRATT_FACTOR(P,g,11,64)
        PRATT_FACTOR(P,g,2,128)
        assert false;
    }
}

lemma pratt_cert p25519_83775021211475436503_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,83775021211475436503);
{
    PRATT_BUILD_PRELUDE(83775021211475436503,5)
    PRATT_BUILD_BIG(10327726679)
    PRATT_BUILD_BIG(564643)
    PRATT_BUILD_SMALL(653)
    PRATT_BUILD_SMALL(11)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_350343741906072820209310645555913_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(350343741906072820209310645555912)),350343741906072820209310645555913) == 1;
{
    if(euclid_mod(pow_nat(3,nat_of_int(350343741906072820209310645555912)),350343741906072820209310645555913) != 1) {
        MODPOW_FULL(350343741906072820209310645555913,3,350343741906072820209310645555912,128)
        assert false;
    }
}

lemma void p25519_350343741906072820209310645555913_1_factors()
    requires true;
    ensures  product({2, 2, 2, 522744931663, 83775021211475436503}) + 1 == 350343741906072820209310645555913;
{}

lemma void p25519_350343741906072820209310645555913_g3_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 522744931663, 83775021211475436503}, (pratt_pow_thing)(350343741906072820209310645555913,3));
{
    if(!forall({2, 2, 2, 522744931663, 83775021211475436503}, (pratt_pow_thing)(350343741906072820209310645555913,3))) {
        int g = 3; int P = 350343741906072820209310645555913;
        PRATT_FACTOR(P,g,83775021211475436503,64)
        PRATT_FACTOR(P,g,522744931663,128)
        PRATT_FACTOR(P,g,2,128)
        assert false;
    }
}

lemma pratt_cert p25519_350343741906072820209310645555913_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,350343741906072820209310645555913);
{
    PRATT_BUILD_PRELUDE(350343741906072820209310645555913,3)
    PRATT_BUILD_BIG(83775021211475436503)
    PRATT_BUILD_BIG(522744931663)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_582271299047893027187874292913927407_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(582271299047893027187874292913927406)),582271299047893027187874292913927407) == 1;
{
    if(euclid_mod(pow_nat(3,nat_of_int(582271299047893027187874292913927406)),582271299047893027187874292913927407) != 1) {
        MODPOW_FULL(582271299047893027187874292913927407,3,582271299047893027187874292913927406,128)
        assert false;
    }
}

lemma void p25519_582271299047893027187874292913927407_1_factors()
    requires true;
    ensures  product({2, 3, 277, 350343741906072820209310645555913}) + 1 == 582271299047893027187874292913927407;
{}

lemma void p25519_582271299047893027187874292913927407_g3_exact_order()
    requires true;
    ensures  !!forall({2, 3, 277, 350343741906072820209310645555913}, (pratt_pow_thing)(582271299047893027187874292913927407,3));
{
    if(!forall({2, 3, 277, 350343741906072820209310645555913}, (pratt_pow_thing)(582271299047893027187874292913927407,3))) {
        int g = 3; int P = 582271299047893027187874292913927407;
        PRATT_FACTOR(P,g,350343741906072820209310645555913,16)
        PRATT_FACTOR(P,g,277,128)
        PRATT_FACTOR(P,g,3,128)
        PRATT_FACTOR(P,g,2,128)
        assert false;
    }
}

lemma pratt_cert p25519_582271299047893027187874292913927407_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,582271299047893027187874292913927407);
{
    PRATT_BUILD_PRELUDE(582271299047893027187874292913927407,3)
    PRATT_BUILD_BIG(350343741906072820209310645555913)
    PRATT_BUILD_SMALL(277)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_19571_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(19570)),19571) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(19570)),19571) != 1) {
        MODPOW_FULL(19571,2,19570,16)
        assert false;
    }
}

lemma void p25519_19571_1_factors()
    requires true;
    ensures  product({2, 5, 19, 103}) + 1 == 19571;
{}

lemma void p25519_19571_g2_exact_order()
    requires true;
    ensures  !!forall({2, 5, 19, 103}, (pratt_pow_thing)(19571,2));
{
    if(!forall({2, 5, 19, 103}, (pratt_pow_thing)(19571,2))) {
        int g = 2; int P = 19571;
        PRATT_FACTOR(P,g,103,8)
        PRATT_FACTOR(P,g,19,16)
        PRATT_FACTOR(P,g,5,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_19571_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,19571);
{
    PRATT_BUILD_PRELUDE(19571,2)
    PRATT_BUILD_SMALL(103)
    PRATT_BUILD_SMALL(19)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_64231_g12_generates()
    requires true;
    ensures  euclid_mod(pow_nat(12,nat_of_int(64230)),64231) == 1;
{
    if(euclid_mod(pow_nat(12,nat_of_int(64230)),64231) != 1) {
        MODPOW_FULL(64231,12,64230,16)
        assert false;
    }
}

lemma void p25519_64231_1_factors()
    requires true;
    ensures  product({2, 3, 5, 2141}) + 1 == 64231;
{}

lemma void p25519_64231_g12_exact_order()
    requires true;
    ensures  !!forall({2, 3, 5, 2141}, (pratt_pow_thing)(64231,12));
{
    if(!forall({2, 3, 5, 2141}, (pratt_pow_thing)(64231,12))) {
        int g = 12; int P = 64231;
        PRATT_FACTOR(P,g,2141,8)
        PRATT_FACTOR(P,g,5,16)
        PRATT_FACTOR(P,g,3,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_64231_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,64231);
{
    PRATT_BUILD_PRELUDE(64231,12)
    PRATT_BUILD_SMALL(2141)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_52757_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(52756)),52757) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(52756)),52757) != 1) {
        MODPOW_FULL(52757,2,52756,16)
        assert false;
    }
}

lemma void p25519_52757_1_factors()
    requires true;
    ensures  product({2, 2, 11, 11, 109}) + 1 == 52757;
{}

lemma void p25519_52757_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 11, 11, 109}, (pratt_pow_thing)(52757,2));
{
    if(!forall({2, 2, 11, 11, 109}, (pratt_pow_thing)(52757,2))) {
        int g = 2; int P = 52757;
        PRATT_FACTOR(P,g,109,16)
        PRATT_FACTOR(P,g,11,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_52757_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,52757);
{
    PRATT_BUILD_PRELUDE(52757,2)
    PRATT_BUILD_SMALL(109)
    PRATT_BUILD_SMALL(11)
    PRATT_BUILD_SMALL(11)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_1055141_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(1055140)),1055141) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(1055140)),1055141) != 1) {
        MODPOW_FULL(1055141,2,1055140,32)
        assert false;
    }
}

lemma void p25519_1055141_1_factors()
    requires true;
    ensures  product({2, 2, 5, 52757}) + 1 == 1055141;
{}

lemma void p25519_1055141_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 5, 52757}, (pratt_pow_thing)(1055141,2));
{
    if(!forall({2, 2, 5, 52757}, (pratt_pow_thing)(1055141,2))) {
        int g = 2; int P = 1055141;
        PRATT_FACTOR(P,g,52757,8)
        PRATT_FACTOR(P,g,5,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_1055141_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,1055141);
{
    PRATT_BUILD_PRELUDE(1055141,2)
    PRATT_BUILD_BIG(52757)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_18992539_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(18992538)),18992539) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(18992538)),18992539) != 1) {
        MODPOW_FULL(18992539,2,18992538,32)
        assert false;
    }
}

lemma void p25519_18992539_1_factors()
    requires true;
    ensures  product({2, 3, 3, 1055141}) + 1 == 18992539;
{}

lemma void p25519_18992539_g2_exact_order()
    requires true;
    ensures  !!forall({2, 3, 3, 1055141}, (pratt_pow_thing)(18992539,2));
{
    if(!forall({2, 3, 3, 1055141}, (pratt_pow_thing)(18992539,2))) {
        int g = 2; int P = 18992539;
        PRATT_FACTOR(P,g,1055141,8)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_18992539_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,18992539);
{
    PRATT_BUILD_PRELUDE(18992539,2)
    PRATT_BUILD_BIG(1055141)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_51461_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(51460)),51461) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(51460)),51461) != 1) {
        MODPOW_FULL(51461,2,51460,16)
        assert false;
    }
}

lemma void p25519_51461_1_factors()
    requires true;
    ensures  product({2, 2, 5, 31, 83}) + 1 == 51461;
{}

lemma void p25519_51461_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 5, 31, 83}, (pratt_pow_thing)(51461,2));
{
    if(!forall({2, 2, 5, 31, 83}, (pratt_pow_thing)(51461,2))) {
        int g = 2; int P = 51461;
        PRATT_FACTOR(P,g,83,16)
        PRATT_FACTOR(P,g,31,16)
        PRATT_FACTOR(P,g,5,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_51461_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,51461);
{
    PRATT_BUILD_PRELUDE(51461,2)
    PRATT_BUILD_SMALL(83)
    PRATT_BUILD_SMALL(31)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_377723741_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(377723740)),377723741) == 1;
{
    if(euclid_mod(pow_nat(3,nat_of_int(377723740)),377723741) != 1) {
        MODPOW_FULL(377723741,3,377723740,32)
        assert false;
    }
}

lemma void p25519_377723741_1_factors()
    requires true;
    ensures  product({2, 2, 5, 367, 51461}) + 1 == 377723741;
{}

lemma void p25519_377723741_g3_exact_order()
    requires true;
    ensures  !!forall({2, 2, 5, 367, 51461}, (pratt_pow_thing)(377723741,3));
{
    if(!forall({2, 2, 5, 367, 51461}, (pratt_pow_thing)(377723741,3))) {
        int g = 3; int P = 377723741;
        PRATT_FACTOR(P,g,51461,16)
        PRATT_FACTOR(P,g,367,32)
        PRATT_FACTOR(P,g,5,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_377723741_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,377723741);
{
    PRATT_BUILD_PRELUDE(377723741,3)
    PRATT_BUILD_BIG(51461)
    PRATT_BUILD_SMALL(367)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_547831_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(547830)),547831) == 1;
{
    if(euclid_mod(pow_nat(3,nat_of_int(547830)),547831) != 1) {
        MODPOW_FULL(547831,3,547830,32)
        assert false;
    }
}

lemma void p25519_547831_1_factors()
    requires true;
    ensures  product({2, 3, 3, 3, 5, 2029}) + 1 == 547831;
{}

lemma void p25519_547831_g3_exact_order()
    requires true;
    ensures  !!forall({2, 3, 3, 3, 5, 2029}, (pratt_pow_thing)(547831,3));
{
    if(!forall({2, 3, 3, 3, 5, 2029}, (pratt_pow_thing)(547831,3))) {
        int g = 3; int P = 547831;
        PRATT_FACTOR(P,g,2029,16)
        PRATT_FACTOR(P,g,5,32)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_547831_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,547831);
{
    PRATT_BUILD_PRELUDE(547831,3)
    PRATT_BUILD_SMALL(2029)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_660684187_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(660684186)),660684187) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(660684186)),660684187) != 1) {
        MODPOW_FULL(660684187,2,660684186,32)
        assert false;
    }
}

lemma void p25519_660684187_1_factors()
    requires true;
    ensures  product({2, 3, 3, 67, 547831}) + 1 == 660684187;
{}

lemma void p25519_660684187_g2_exact_order()
    requires true;
    ensures  !!forall({2, 3, 3, 67, 547831}, (pratt_pow_thing)(660684187,2));
{
    if(!forall({2, 3, 3, 67, 547831}, (pratt_pow_thing)(660684187,2))) {
        int g = 2; int P = 660684187;
        PRATT_FACTOR(P,g,547831,16)
        PRATT_FACTOR(P,g,67,32)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_660684187_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,660684187);
{
    PRATT_BUILD_PRELUDE(660684187,2)
    PRATT_BUILD_BIG(547831)
    PRATT_BUILD_SMALL(67)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_2440563294432588452310063876982204011061_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(2440563294432588452310063876982204011060)),2440563294432588452310063876982204011061) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(2440563294432588452310063876982204011060)),2440563294432588452310063876982204011061) != 1) {
        MODPOW_FULL(2440563294432588452310063876982204011061,2,2440563294432588452310063876982204011060,256)
        assert false;
    }
}

lemma void p25519_2440563294432588452310063876982204011061_1_factors()
    requires true;
    ensures  product({2, 2, 3, 5, 6827, 19571, 64231, 18992539, 377723741, 660684187}) + 1 == 2440563294432588452310063876982204011061;
{}

lemma void p25519_2440563294432588452310063876982204011061_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3, 5, 6827, 19571, 64231, 18992539, 377723741, 660684187}, (pratt_pow_thing)(2440563294432588452310063876982204011061,2));
{
    if(!forall({2, 2, 3, 5, 6827, 19571, 64231, 18992539, 377723741, 660684187}, (pratt_pow_thing)(2440563294432588452310063876982204011061,2))) {
        int g = 2; int P = 2440563294432588452310063876982204011061;
        PRATT_FACTOR(P,g,660684187,128)
        PRATT_FACTOR(P,g,377723741,128)
        PRATT_FACTOR(P,g,18992539,128)
        PRATT_FACTOR(P,g,64231,128)
        PRATT_FACTOR(P,g,19571,128)
        PRATT_FACTOR(P,g,6827,128)
        PRATT_FACTOR(P,g,5,256)
        PRATT_FACTOR(P,g,3,256)
        PRATT_FACTOR(P,g,2,256)
        assert false;
    }
}

lemma pratt_cert p25519_2440563294432588452310063876982204011061_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,2440563294432588452310063876982204011061);
{
    PRATT_BUILD_PRELUDE(2440563294432588452310063876982204011061,2)
    PRATT_BUILD_BIG(660684187)
    PRATT_BUILD_BIG(377723741)
    PRATT_BUILD_BIG(18992539)
    PRATT_BUILD_BIG(64231)
    PRATT_BUILD_BIG(19571)
    PRATT_BUILD_SMALL(6827)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_10163_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(10162)),10163) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(10162)),10163) != 1) {
        MODPOW_FULL(10163,2,10162,16)
        assert false;
    }
}

lemma void p25519_10163_1_factors()
    requires true;
    ensures  product({2, 5081}) + 1 == 10163;
{}

lemma void p25519_10163_g2_exact_order()
    requires true;
    ensures  !!forall({2, 5081}, (pratt_pow_thing)(10163,2));
{
    if(!forall({2, 5081}, (pratt_pow_thing)(10163,2))) {
        int g = 2; int P = 10163;
        if(!pratt_pow_thing(P,g,5081)) {
            pratt_pow_thing_auto(P,g,5081);
            assert false;
        }
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_10163_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,10163);
{
    PRATT_BUILD_PRELUDE(10163,2)
    PRATT_BUILD_SMALL(5081)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_14879_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,nat_of_int(14878)),14879) == 1;
{
    if(euclid_mod(pow_nat(7,nat_of_int(14878)),14879) != 1) {
        MODPOW_FULL(14879,7,14878,16)
        assert false;
    }
}

lemma void p25519_14879_1_factors()
    requires true;
    ensures  product({2, 43, 173}) + 1 == 14879;
{}

lemma void p25519_14879_g7_exact_order()
    requires true;
    ensures  !!forall({2, 43, 173}, (pratt_pow_thing)(14879,7));
{
    if(!forall({2, 43, 173}, (pratt_pow_thing)(14879,7))) {
        int g = 7; int P = 14879;
        PRATT_FACTOR(P,g,173,8)
        PRATT_FACTOR(P,g,43,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_14879_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,14879);
{
    PRATT_BUILD_PRELUDE(14879,7)
    PRATT_BUILD_SMALL(173)
    PRATT_BUILD_SMALL(43)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_29759_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,nat_of_int(29758)),29759) == 1;
{
    if(euclid_mod(pow_nat(7,nat_of_int(29758)),29759) != 1) {
        MODPOW_FULL(29759,7,29758,16)
        assert false;
    }
}

lemma void p25519_29759_1_factors()
    requires true;
    ensures  product({2, 14879}) + 1 == 29759;
{}

lemma void p25519_29759_g7_exact_order()
    requires true;
    ensures  !!forall({2, 14879}, (pratt_pow_thing)(29759,7));
{
    if(!forall({2, 14879}, (pratt_pow_thing)(29759,7))) {
        int g = 7; int P = 29759;
        if(!pratt_pow_thing(P,g,14879)) {
            pratt_pow_thing_auto(P,g,14879);
            assert false;
        }
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_29759_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,29759);
{
    PRATT_BUILD_PRELUDE(29759,7)
    PRATT_BUILD_BIG(14879)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_535663_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(535662)),535663) == 1;
{
    if(euclid_mod(pow_nat(3,nat_of_int(535662)),535663) != 1) {
        MODPOW_FULL(535663,3,535662,32)
        assert false;
    }
}

lemma void p25519_535663_1_factors()
    requires true;
    ensures  product({2, 3, 3, 29759}) + 1 == 535663;
{}

lemma void p25519_535663_g3_exact_order()
    requires true;
    ensures  !!forall({2, 3, 3, 29759}, (pratt_pow_thing)(535663,3));
{
    if(!forall({2, 3, 3, 29759}, (pratt_pow_thing)(535663,3))) {
        int g = 3; int P = 535663;
        PRATT_FACTOR(P,g,29759,8)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_535663_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,535663);
{
    PRATT_BUILD_PRELUDE(535663,3)
    PRATT_BUILD_BIG(29759)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_21426521_g6_generates()
    requires true;
    ensures  euclid_mod(pow_nat(6,nat_of_int(21426520)),21426521) == 1;
{
    if(euclid_mod(pow_nat(6,nat_of_int(21426520)),21426521) != 1) {
        MODPOW_FULL(21426521,6,21426520,32)
        assert false;
    }
}

lemma void p25519_21426521_1_factors()
    requires true;
    ensures  product({2, 2, 2, 5, 535663}) + 1 == 21426521;
{}

lemma void p25519_21426521_g6_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 5, 535663}, (pratt_pow_thing)(21426521,6));
{
    if(!forall({2, 2, 2, 5, 535663}, (pratt_pow_thing)(21426521,6))) {
        int g = 6; int P = 21426521;
        PRATT_FACTOR(P,g,535663,8)
        PRATT_FACTOR(P,g,5,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_21426521_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,21426521);
{
    PRATT_BUILD_PRELUDE(21426521,6)
    PRATT_BUILD_BIG(535663)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_42853043_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(42853042)),42853043) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(42853042)),42853043) != 1) {
        MODPOW_FULL(42853043,2,42853042,32)
        assert false;
    }
}

lemma void p25519_42853043_1_factors()
    requires true;
    ensures  product({2, 21426521}) + 1 == 42853043;
{}

lemma void p25519_42853043_g2_exact_order()
    requires true;
    ensures  !!forall({2, 21426521}, (pratt_pow_thing)(42853043,2));
{
    if(!forall({2, 21426521}, (pratt_pow_thing)(42853043,2))) {
        int g = 2; int P = 42853043;
        if(!pratt_pow_thing(P,g,21426521)) {
            pratt_pow_thing_auto(P,g,21426521);
            assert false;
        }
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_42853043_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,42853043);
{
    PRATT_BUILD_PRELUDE(42853043,2)
    PRATT_BUILD_BIG(21426521)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_518580685877_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(518580685876)),518580685877) == 1;
{
    if(euclid_mod(pow_nat(2,nat_of_int(518580685876)),518580685877) != 1) {
        MODPOW_FULL(518580685877,2,518580685876,64)
        assert false;
    }
}

lemma void p25519_518580685877_1_factors()
    requires true;
    ensures  product({2, 2, 11, 17, 73, 1087, 8737}) + 1 == 518580685877;
{}

lemma void p25519_518580685877_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 11, 17, 73, 1087, 8737}, (pratt_pow_thing)(518580685877,2));
{
    if(!forall({2, 2, 11, 17, 73, 1087, 8737}, (pratt_pow_thing)(518580685877,2))) {
        int g = 2; int P = 518580685877;
        PRATT_FACTOR(P,g,8737,32)
        PRATT_FACTOR(P,g,1087,32)
        PRATT_FACTOR(P,g,73,64)
        PRATT_FACTOR(P,g,17,64)
        PRATT_FACTOR(P,g,11,64)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_518580685877_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,518580685877);
{
    PRATT_BUILD_PRELUDE(518580685877,2)
    PRATT_BUILD_SMALL(8737)
    PRATT_BUILD_SMALL(1087)
    PRATT_BUILD_SMALL(73)
    PRATT_BUILD_SMALL(17)
    PRATT_BUILD_SMALL(11)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_168601_g14_generates()
    requires true;
    ensures  euclid_mod(pow_nat(14,nat_of_int(168600)),168601) == 1;
{
    if(euclid_mod(pow_nat(14,nat_of_int(168600)),168601) != 1) {
        MODPOW_FULL(168601,14,168600,32)
        assert false;
    }
}

lemma void p25519_168601_1_factors()
    requires true;
    ensures  product({2, 2, 2, 3, 5, 5, 281}) + 1 == 168601;
{}

lemma void p25519_168601_g14_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 3, 5, 5, 281}, (pratt_pow_thing)(168601,14));
{
    if(!forall({2, 2, 2, 3, 5, 5, 281}, (pratt_pow_thing)(168601,14))) {
        int g = 14; int P = 168601;
        PRATT_FACTOR(P,g,281,16)
        PRATT_FACTOR(P,g,5,16)
        PRATT_FACTOR(P,g,3,16)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_168601_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,168601);
{
    PRATT_BUILD_PRELUDE(168601,14)
    PRATT_BUILD_SMALL(281)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_149521_g17_generates()
    requires true;
    ensures  euclid_mod(pow_nat(17,nat_of_int(149520)),149521) == 1;
{
    if(euclid_mod(pow_nat(17,nat_of_int(149520)),149521) != 1) {
        MODPOW_FULL(149521,17,149520,32)
        assert false;
    }
}

lemma void p25519_149521_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 3, 5, 7, 89}) + 1 == 149521;
{}

lemma void p25519_149521_g17_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 3, 5, 7, 89}, (pratt_pow_thing)(149521,17));
{
    if(!forall({2, 2, 2, 2, 3, 5, 7, 89}, (pratt_pow_thing)(149521,17))) {
        int g = 17; int P = 149521;
        PRATT_FACTOR(P,g,89,16)
        PRATT_FACTOR(P,g,7,16)
        PRATT_FACTOR(P,g,5,16)
        PRATT_FACTOR(P,g,3,16)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_149521_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,149521);
{
    PRATT_BUILD_PRELUDE(149521,17)
    PRATT_BUILD_SMALL(89)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_3289463_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(3289462)),3289463) == 1;
{
    if(euclid_mod(pow_nat(5,nat_of_int(3289462)),3289463) != 1) {
        MODPOW_FULL(3289463,5,3289462,32)
        assert false;
    }
}

lemma void p25519_3289463_1_factors()
    requires true;
    ensures  product({2, 11, 149521}) + 1 == 3289463;
{}

lemma void p25519_3289463_g5_exact_order()
    requires true;
    ensures  !!forall({2, 11, 149521}, (pratt_pow_thing)(3289463,5));
{
    if(!forall({2, 11, 149521}, (pratt_pow_thing)(3289463,5))) {
        int g = 5; int P = 3289463;
        PRATT_FACTOR(P,g,149521,8)
        PRATT_FACTOR(P,g,11,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_3289463_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,3289463);
{
    PRATT_BUILD_PRELUDE(3289463,5)
    PRATT_BUILD_BIG(149521)
    PRATT_BUILD_SMALL(11)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_6578927_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(6578926)),6578927) == 1;
{
    if(euclid_mod(pow_nat(5,nat_of_int(6578926)),6578927) != 1) {
        MODPOW_FULL(6578927,5,6578926,32)
        assert false;
    }
}

lemma void p25519_6578927_1_factors()
    requires true;
    ensures  product({2, 3289463}) + 1 == 6578927;
{}

lemma void p25519_6578927_g5_exact_order()
    requires true;
    ensures  !!forall({2, 3289463}, (pratt_pow_thing)(6578927,5));
{
    if(!forall({2, 3289463}, (pratt_pow_thing)(6578927,5))) {
        int g = 5; int P = 6578927;
        if(!pratt_pow_thing(P,g,3289463)) {
            pratt_pow_thing_auto(P,g,3289463);
            assert false;
        }
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_6578927_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,6578927);
{
    PRATT_BUILD_PRELUDE(6578927,5)
    PRATT_BUILD_BIG(3289463)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_86518666347907_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(86518666347906)),86518666347907) == 1;
{
    if(euclid_mod(pow_nat(5,nat_of_int(86518666347906)),86518666347907) != 1) {
        MODPOW_FULL(86518666347907,5,86518666347906,64)
        assert false;
    }
}

lemma void p25519_86518666347907_1_factors()
    requires true;
    ensures  product({2, 3, 13, 168601, 6578927}) + 1 == 86518666347907;
{}

lemma void p25519_86518666347907_g5_exact_order()
    requires true;
    ensures  !!forall({2, 3, 13, 168601, 6578927}, (pratt_pow_thing)(86518666347907,5));
{
    if(!forall({2, 3, 13, 168601, 6578927}, (pratt_pow_thing)(86518666347907,5))) {
        int g = 5; int P = 86518666347907;
        PRATT_FACTOR(P,g,6578927,32)
        PRATT_FACTOR(P,g,168601,32)
        PRATT_FACTOR(P,g,13,64)
        PRATT_FACTOR(P,g,3,64)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_86518666347907_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,86518666347907);
{
    PRATT_BUILD_PRELUDE(86518666347907,5)
    PRATT_BUILD_BIG(6578927)
    PRATT_BUILD_BIG(168601)
    PRATT_BUILD_SMALL(13)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_2987936166061269764733822017919288608395313_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(2987936166061269764733822017919288608395312)),2987936166061269764733822017919288608395313) == 1;
{
    if(euclid_mod(pow_nat(3,nat_of_int(2987936166061269764733822017919288608395312)),2987936166061269764733822017919288608395313) != 1) {
        MODPOW_FULL(2987936166061269764733822017919288608395313,3,2987936166061269764733822017919288608395312,256)
        assert false;
    }
}

lemma void p25519_2987936166061269764733822017919288608395313_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 19, 503, 10163, 42853043, 518580685877, 86518666347907}) + 1 == 2987936166061269764733822017919288608395313;
{}

lemma void p25519_2987936166061269764733822017919288608395313_g3_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 19, 503, 10163, 42853043, 518580685877, 86518666347907}, (pratt_pow_thing)(2987936166061269764733822017919288608395313,3));
{
    if(!forall({2, 2, 2, 2, 19, 503, 10163, 42853043, 518580685877, 86518666347907}, (pratt_pow_thing)(2987936166061269764733822017919288608395313,3))) {
        int g = 3; int P = 2987936166061269764733822017919288608395313;
        PRATT_FACTOR(P,g,86518666347907,128)
        PRATT_FACTOR(P,g,518580685877,128)
        PRATT_FACTOR(P,g,42853043,128)
        PRATT_FACTOR(P,g,10163,128)
        PRATT_FACTOR(P,g,503,256)
        PRATT_FACTOR(P,g,19,256)
        PRATT_FACTOR(P,g,2,256)
        assert false;
    }
}

lemma pratt_cert p25519_2987936166061269764733822017919288608395313_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,2987936166061269764733822017919288608395313);
{
    PRATT_BUILD_PRELUDE(2987936166061269764733822017919288608395313,3)
    PRATT_BUILD_BIG(86518666347907)
    PRATT_BUILD_BIG(518580685877)
    PRATT_BUILD_BIG(42853043)
    PRATT_BUILD_BIG(10163)
    PRATT_BUILD_SMALL(503)
    PRATT_BUILD_SMALL(19)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,nat_of_int(13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083526)),13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527) == 1;
{
    if(euclid_mod(pow_nat(7,nat_of_int(13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083526)),13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527) != 1) {
        MODPOW_FULL(13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527,7,13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083526,512)
        assert false;
    }
}

lemma void p25519_13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527_1_factors()
    requires true;
    ensures  product({2, 23, 41, 353, 105095387, 45130584520747958722981, 582271299047893027187874292913927407, 2440563294432588452310063876982204011061, 2987936166061269764733822017919288608395313}) + 1 == 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527;
{}

lemma void p25519_13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527_g7_exact_order()
    requires true;
    ensures  !!forall({2, 23, 41, 353, 105095387, 45130584520747958722981, 582271299047893027187874292913927407, 2440563294432588452310063876982204011061, 2987936166061269764733822017919288608395313}, (pratt_pow_thing)(13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527,7));
{
    if(!forall({2, 23, 41, 353, 105095387, 45130584520747958722981, 582271299047893027187874292913927407, 2440563294432588452310063876982204011061, 2987936166061269764733822017919288608395313}, (pratt_pow_thing)(13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527,7))) {
        int g = 7; int P = 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527;
        PRATT_FACTOR(P,g,2987936166061269764733822017919288608395313,512)
        PRATT_FACTOR(P,g,2440563294432588452310063876982204011061,512)
        PRATT_FACTOR(P,g,582271299047893027187874292913927407,512)
        PRATT_FACTOR(P,g,45130584520747958722981,512)
        PRATT_FACTOR(P,g,105095387,512)
        PRATT_FACTOR(P,g,353,512)
        PRATT_FACTOR(P,g,41,512)
        PRATT_FACTOR(P,g,23,512)
        PRATT_FACTOR(P,g,2,512)
        assert false;
    }
}

lemma pratt_cert p25519_13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527);
{
    PRATT_BUILD_PRELUDE(13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006083527,7)
    PRATT_BUILD_BIG(2987936166061269764733822017919288608395313)
    PRATT_BUILD_BIG(2440563294432588452310063876982204011061)
    PRATT_BUILD_BIG(582271299047893027187874292913927407)
    PRATT_BUILD_BIG(45130584520747958722981)
    PRATT_BUILD_BIG(105095387)
    PRATT_BUILD_SMALL(353)
    PRATT_BUILD_SMALL(41)
    PRATT_BUILD_SMALL(23)
    PRATT_BUILD_SMALL(2)
    return ret;
}


  @*/

