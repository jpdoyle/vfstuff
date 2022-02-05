/*@ #include "p25519.gh" @*/
/*@ #include "p448_generated.gh" @*/

/*@

lemma void p25519_18287_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,noi(18286)),18287) == 1;
{
    if(euclid_mod(pow_nat(5,noi(18286)),18287) != 1) {
        MODPOW_FULL(18287,5,18286,16)
        assert false;
    }
}

lemma void p25519_18287_1_factors()
    requires true;
    ensures  product({2, 41, 223}) + 1 == 18287;
{}

lemma void p25519_18287_g5_exact_order()
    requires true;
    ensures  !!forall({2, 41, 223}, (pratt_pow_thing)(18287,5));
{
    if(!forall({2, 41, 223}, (pratt_pow_thing)(18287,5))) {
        int g = 5; int P = 18287;
        PRATT_FACTOR(P,g,223,8)
        PRATT_FACTOR(P,g,41,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_18287_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,18287);
{
    PRATT_BUILD_PRELUDE(18287,5)
    PRATT_BUILD_SMALL(223)
    PRATT_BUILD_SMALL(41)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_196687_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,noi(196686)),196687) == 1;
{
    if(euclid_mod(pow_nat(3,noi(196686)),196687) != 1) {
        MODPOW_FULL(196687,3,196686,32)
        assert false;
    }
}

lemma void p25519_196687_1_factors()
    requires true;
    ensures  product({2, 3, 3, 7, 7, 223}) + 1 == 196687;
{}

lemma void p25519_196687_g3_exact_order()
    requires true;
    ensures  !!forall({2, 3, 3, 7, 7, 223}, (pratt_pow_thing)(196687,3));
{
    if(!forall({2, 3, 3, 7, 7, 223}, (pratt_pow_thing)(196687,3))) {
        int g = 3; int P = 196687;
        PRATT_FACTOR(P,g,223,16)
        PRATT_FACTOR(P,g,7,16)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_196687_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,196687);
{
    PRATT_BUILD_PRELUDE(196687,3)
    PRATT_BUILD_SMALL(223)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_1466449_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,noi(1466448)),1466449) == 1;
{
    if(euclid_mod(pow_nat(7,noi(1466448)),1466449) != 1) {
        MODPOW_FULL(1466449,7,1466448,32)
        assert false;
    }
}

lemma void p25519_1466449_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 3, 137, 223}) + 1 == 1466449;
{}

lemma void p25519_1466449_g7_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 3, 137, 223}, (pratt_pow_thing)(1466449,7));
{
    if(!forall({2, 2, 2, 2, 3, 137, 223}, (pratt_pow_thing)(1466449,7))) {
        int g = 7; int P = 1466449;
        PRATT_FACTOR(P,g,223,16)
        PRATT_FACTOR(P,g,137,16)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_1466449_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,1466449);
{
    PRATT_BUILD_PRELUDE(1466449,7)
    PRATT_BUILD_SMALL(223)
    PRATT_BUILD_SMALL(137)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_2916841_g13_generates()
    requires true;
    ensures  euclid_mod(pow_nat(13,noi(2916840)),2916841) == 1;
{
    if(euclid_mod(pow_nat(13,noi(2916840)),2916841) != 1) {
        MODPOW_FULL(2916841,13,2916840,32)
        assert false;
    }
}

lemma void p25519_2916841_1_factors()
    requires true;
    ensures  product({2, 2, 2, 3, 5, 109, 223}) + 1 == 2916841;
{}

lemma void p25519_2916841_g13_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 3, 5, 109, 223}, (pratt_pow_thing)(2916841,13));
{
    if(!forall({2, 2, 2, 3, 5, 109, 223}, (pratt_pow_thing)(2916841,13))) {
        int g = 13; int P = 2916841;
        PRATT_FACTOR(P,g,223,16)
        PRATT_FACTOR(P,g,109,16)
        PRATT_FACTOR(P,g,5,32)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_2916841_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,2916841);
{
    PRATT_BUILD_PRELUDE(2916841,13)
    PRATT_BUILD_SMALL(223)
    PRATT_BUILD_SMALL(109)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_17449_g14_generates()
    requires true;
    ensures  euclid_mod(pow_nat(14,noi(17448)),17449) == 1;
{
    if(euclid_mod(pow_nat(14,noi(17448)),17449) != 1) {
        MODPOW_FULL(17449,14,17448,16)
        assert false;
    }
}

lemma void p25519_17449_1_factors()
    requires true;
    ensures  product({2, 2, 2, 3, 727}) + 1 == 17449;
{}

lemma void p25519_17449_g14_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 3, 727}, (pratt_pow_thing)(17449,14));
{
    if(!forall({2, 2, 2, 3, 727}, (pratt_pow_thing)(17449,14))) {
        int g = 14; int P = 17449;
        PRATT_FACTOR(P,g,727,8)
        PRATT_FACTOR(P,g,3,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_17449_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,17449);
{
    PRATT_BUILD_PRELUDE(17449,14)
    PRATT_BUILD_SMALL(727)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_6700417_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,noi(6700416)),6700417) == 1;
{
    if(euclid_mod(pow_nat(5,noi(6700416)),6700417) != 1) {
        MODPOW_FULL(6700417,5,6700416,32)
        assert false;
    }
}

lemma void p25519_6700417_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 2, 2, 2, 3, 17449}) + 1 == 6700417;
{}

lemma void p25519_6700417_g5_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 2, 2, 2, 3, 17449}, (pratt_pow_thing)(6700417,5));
{
    if(!forall({2, 2, 2, 2, 2, 2, 2, 3, 17449}, (pratt_pow_thing)(6700417,5))) {
        int g = 5; int P = 6700417;
        PRATT_FACTOR(P,g,17449,16)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_6700417_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,6700417);
{
    PRATT_BUILD_PRELUDE(6700417,5)
    PRATT_BUILD_BIG(17449)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_411743_g10_generates()
    requires true;
    ensures  euclid_mod(pow_nat(10,noi(411742)),411743) == 1;
{
    if(euclid_mod(pow_nat(10,noi(411742)),411743) != 1) {
        MODPOW_FULL(411743,10,411742,32)
        assert false;
    }
}

lemma void p25519_411743_1_factors()
    requires true;
    ensures  product({2, 29, 31, 229}) + 1 == 411743;
{}

lemma void p25519_411743_g10_exact_order()
    requires true;
    ensures  !!forall({2, 29, 31, 229}, (pratt_pow_thing)(411743,10));
{
    if(!forall({2, 29, 31, 229}, (pratt_pow_thing)(411743,10))) {
        int g = 10; int P = 411743;
        PRATT_FACTOR(P,g,229,16)
        PRATT_FACTOR(P,g,31,16)
        PRATT_FACTOR(P,g,29,16)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_411743_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,411743);
{
    PRATT_BUILD_PRELUDE(411743,10)
    PRATT_BUILD_SMALL(229)
    PRATT_BUILD_SMALL(31)
    PRATT_BUILD_SMALL(29)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_1609403_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(1609402)),1609403) == 1;
{
    if(euclid_mod(pow_nat(2,noi(1609402)),1609403) != 1) {
        MODPOW_FULL(1609403,2,1609402,32)
        assert false;
    }
}

lemma void p25519_1609403_1_factors()
    requires true;
    ensures  product({2, 23, 59, 593}) + 1 == 1609403;
{}

lemma void p25519_1609403_g2_exact_order()
    requires true;
    ensures  !!forall({2, 23, 59, 593}, (pratt_pow_thing)(1609403,2));
{
    if(!forall({2, 23, 59, 593}, (pratt_pow_thing)(1609403,2))) {
        int g = 2; int P = 1609403;
        PRATT_FACTOR(P,g,593,16)
        PRATT_FACTOR(P,g,59,16)
        PRATT_FACTOR(P,g,23,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_1609403_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,1609403);
{
    PRATT_BUILD_PRELUDE(1609403,2)
    PRATT_BUILD_SMALL(593)
    PRATT_BUILD_SMALL(59)
    PRATT_BUILD_SMALL(23)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_3402277943_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,noi(3402277942)),3402277943) == 1;
{
    if(euclid_mod(pow_nat(5,noi(3402277942)),3402277943) != 1) {
        MODPOW_FULL(3402277943,5,3402277942,32)
        assert false;
    }
}

lemma void p25519_3402277943_1_factors()
    requires true;
    ensures  product({2, 7, 151, 1609403}) + 1 == 3402277943;
{}

lemma void p25519_3402277943_g5_exact_order()
    requires true;
    ensures  !!forall({2, 7, 151, 1609403}, (pratt_pow_thing)(3402277943,5));
{
    if(!forall({2, 7, 151, 1609403}, (pratt_pow_thing)(3402277943,5))) {
        int g = 5; int P = 3402277943;
        PRATT_FACTOR(P,g,1609403,16)
        PRATT_FACTOR(P,g,151,32)
        PRATT_FACTOR(P,g,7,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_3402277943_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,3402277943);
{
    PRATT_BUILD_PRELUDE(3402277943,5)
    PRATT_BUILD_BIG(1609403)
    PRATT_BUILD_SMALL(151)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_1469495262398780123809_g17_generates()
    requires true;
    ensures  euclid_mod(pow_nat(17,noi(1469495262398780123808)),1469495262398780123809) == 1;
{
    if(euclid_mod(pow_nat(17,noi(1469495262398780123808)),1469495262398780123809) != 1) {
        MODPOW_FULL(1469495262398780123809,17,1469495262398780123808,128)
        assert false;
    }
}

lemma void p25519_1469495262398780123809_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 2, 3, 7, 7, 223, 411743, 3402277943}) + 1 == 1469495262398780123809;
{}

lemma void p25519_1469495262398780123809_g17_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 2, 3, 7, 7, 223, 411743, 3402277943}, (pratt_pow_thing)(1469495262398780123809,17));
{
    if(!forall({2, 2, 2, 2, 2, 3, 7, 7, 223, 411743, 3402277943}, (pratt_pow_thing)(1469495262398780123809,17))) {
        int g = 17; int P = 1469495262398780123809;
        PRATT_FACTOR(P,g,3402277943,64)
        PRATT_FACTOR(P,g,411743,64)
        PRATT_FACTOR(P,g,223,64)
        PRATT_FACTOR(P,g,7,128)
        PRATT_FACTOR(P,g,3,128)
        PRATT_FACTOR(P,g,2,128)
        assert false;
    }
}

lemma pratt_cert p25519_1469495262398780123809_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,1469495262398780123809);
{
    PRATT_BUILD_PRELUDE(1469495262398780123809,17)
    PRATT_BUILD_BIG(3402277943)
    PRATT_BUILD_BIG(411743)
    PRATT_BUILD_SMALL(223)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_47497_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,noi(47496)),47497) == 1;
{
    if(euclid_mod(pow_nat(5,noi(47496)),47497) != 1) {
        MODPOW_FULL(47497,5,47496,16)
        assert false;
    }
}

lemma void p25519_47497_1_factors()
    requires true;
    ensures  product({2, 2, 2, 3, 1979}) + 1 == 47497;
{}

lemma void p25519_47497_g5_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 3, 1979}, (pratt_pow_thing)(47497,5));
{
    if(!forall({2, 2, 2, 3, 1979}, (pratt_pow_thing)(47497,5))) {
        int g = 5; int P = 47497;
        PRATT_FACTOR(P,g,1979,8)
        PRATT_FACTOR(P,g,3,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_47497_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,47497);
{
    PRATT_BUILD_PRELUDE(47497,5)
    PRATT_BUILD_SMALL(1979)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_189989_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(189988)),189989) == 1;
{
    if(euclid_mod(pow_nat(2,noi(189988)),189989) != 1) {
        MODPOW_FULL(189989,2,189988,32)
        assert false;
    }
}

lemma void p25519_189989_1_factors()
    requires true;
    ensures  product({2, 2, 47497}) + 1 == 189989;
{}

lemma void p25519_189989_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 47497}, (pratt_pow_thing)(189989,2));
{
    if(!forall({2, 2, 47497}, (pratt_pow_thing)(189989,2))) {
        int g = 2; int P = 189989;
        if(!pratt_pow_thing(P,g,47497)) {
            pratt_pow_thing_auto(P,g,47497);
            assert false;
        }
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_189989_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,189989);
{
    PRATT_BUILD_PRELUDE(189989,2)
    PRATT_BUILD_BIG(47497)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_379979_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(379978)),379979) == 1;
{
    if(euclid_mod(pow_nat(2,noi(379978)),379979) != 1) {
        MODPOW_FULL(379979,2,379978,32)
        assert false;
    }
}

lemma void p25519_379979_1_factors()
    requires true;
    ensures  product({2, 189989}) + 1 == 379979;
{}

lemma void p25519_379979_g2_exact_order()
    requires true;
    ensures  !!forall({2, 189989}, (pratt_pow_thing)(379979,2));
{
    if(!forall({2, 189989}, (pratt_pow_thing)(379979,2))) {
        int g = 2; int P = 379979;
        if(!pratt_pow_thing(P,g,189989)) {
            pratt_pow_thing_auto(P,g,189989);
            assert false;
        }
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_379979_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,379979);
{
    PRATT_BUILD_PRELUDE(379979,2)
    PRATT_BUILD_BIG(189989)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_97859369123353_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,noi(97859369123352)),97859369123353) == 1;
{
    if(euclid_mod(pow_nat(5,noi(97859369123352)),97859369123353) != 1) {
        MODPOW_FULL(97859369123353,5,97859369123352,64)
        assert false;
    }
}

lemma void p25519_97859369123353_1_factors()
    requires true;
    ensures  product({2, 2, 2, 3, 3, 67, 197, 271, 379979}) + 1 == 97859369123353;
{}

lemma void p25519_97859369123353_g5_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 3, 3, 67, 197, 271, 379979}, (pratt_pow_thing)(97859369123353,5));
{
    if(!forall({2, 2, 2, 3, 3, 67, 197, 271, 379979}, (pratt_pow_thing)(97859369123353,5))) {
        int g = 5; int P = 97859369123353;
        PRATT_FACTOR(P,g,379979,32)
        PRATT_FACTOR(P,g,271,64)
        PRATT_FACTOR(P,g,197,64)
        PRATT_FACTOR(P,g,67,64)
        PRATT_FACTOR(P,g,3,64)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_97859369123353_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,97859369123353);
{
    PRATT_BUILD_PRELUDE(97859369123353,5)
    PRATT_BUILD_BIG(379979)
    PRATT_BUILD_SMALL(271)
    PRATT_BUILD_SMALL(197)
    PRATT_BUILD_SMALL(67)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_167773885276849215533569_g17_generates()
    requires true;
    ensures  euclid_mod(pow_nat(17,noi(167773885276849215533568)),167773885276849215533569) == 1;
{
    if(euclid_mod(pow_nat(17,noi(167773885276849215533568)),167773885276849215533569) != 1) {
        MODPOW_FULL(167773885276849215533569,17,167773885276849215533568,128)
        assert false;
    }
}

lemma void p25519_167773885276849215533569_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 7, 7, 2531, 97859369123353}) + 1 == 167773885276849215533569;
{}

lemma void p25519_167773885276849215533569_g17_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 7, 7, 2531, 97859369123353}, (pratt_pow_thing)(167773885276849215533569,17));
{
    if(!forall({2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 7, 7, 2531, 97859369123353}, (pratt_pow_thing)(167773885276849215533569,17))) {
        int g = 17; int P = 167773885276849215533569;
        PRATT_FACTOR(P,g,97859369123353,32)
        PRATT_FACTOR(P,g,2531,128)
        PRATT_FACTOR(P,g,7,128)
        PRATT_FACTOR(P,g,3,128)
        PRATT_FACTOR(P,g,2,128)
        assert false;
    }
}

lemma pratt_cert p25519_167773885276849215533569_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,167773885276849215533569);
{
    PRATT_BUILD_PRELUDE(167773885276849215533569,17)
    PRATT_BUILD_BIG(97859369123353)
    PRATT_BUILD_SMALL(2531)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_217003_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,noi(217002)),217003) == 1;
{
    if(euclid_mod(pow_nat(3,noi(217002)),217003) != 1) {
        MODPOW_FULL(217003,3,217002,32)
        assert false;
    }
}

lemma void p25519_217003_1_factors()
    requires true;
    ensures  product({2, 3, 59, 613}) + 1 == 217003;
{}

lemma void p25519_217003_g3_exact_order()
    requires true;
    ensures  !!forall({2, 3, 59, 613}, (pratt_pow_thing)(217003,3));
{
    if(!forall({2, 3, 59, 613}, (pratt_pow_thing)(217003,3))) {
        int g = 3; int P = 217003;
        PRATT_FACTOR(P,g,613,16)
        PRATT_FACTOR(P,g,59,16)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_217003_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,217003);
{
    PRATT_BUILD_PRELUDE(217003,3)
    PRATT_BUILD_SMALL(613)
    PRATT_BUILD_SMALL(59)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_1764234391_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,noi(1764234390)),1764234391) == 1;
{
    if(euclid_mod(pow_nat(3,noi(1764234390)),1764234391) != 1) {
        MODPOW_FULL(1764234391,3,1764234390,32)
        assert false;
    }
}

lemma void p25519_1764234391_1_factors()
    requires true;
    ensures  product({2, 3, 5, 271, 217003}) + 1 == 1764234391;
{}

lemma void p25519_1764234391_g3_exact_order()
    requires true;
    ensures  !!forall({2, 3, 5, 271, 217003}, (pratt_pow_thing)(1764234391,3));
{
    if(!forall({2, 3, 5, 271, 217003}, (pratt_pow_thing)(1764234391,3))) {
        int g = 3; int P = 1764234391;
        PRATT_FACTOR(P,g,217003,16)
        PRATT_FACTOR(P,g,271,32)
        PRATT_FACTOR(P,g,5,32)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_1764234391_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,1764234391);
{
    PRATT_BUILD_PRELUDE(1764234391,3)
    PRATT_BUILD_BIG(217003)
    PRATT_BUILD_SMALL(271)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_34741861125639557_g13_generates()
    requires true;
    ensures  euclid_mod(pow_nat(13,noi(34741861125639556)),34741861125639557) == 1;
{
    if(euclid_mod(pow_nat(13,noi(34741861125639556)),34741861125639557) != 1) {
        MODPOW_FULL(34741861125639557,13,34741861125639556,64)
        assert false;
    }
}

lemma void p25519_34741861125639557_1_factors()
    requires true;
    ensures  product({2, 2, 7, 7, 7, 31, 463, 1764234391}) + 1 == 34741861125639557;
{}

lemma void p25519_34741861125639557_g13_exact_order()
    requires true;
    ensures  !!forall({2, 2, 7, 7, 7, 31, 463, 1764234391}, (pratt_pow_thing)(34741861125639557,13));
{
    if(!forall({2, 2, 7, 7, 7, 31, 463, 1764234391}, (pratt_pow_thing)(34741861125639557,13))) {
        int g = 13; int P = 34741861125639557;
        PRATT_FACTOR(P,g,1764234391,32)
        PRATT_FACTOR(P,g,463,64)
        PRATT_FACTOR(P,g,31,64)
        PRATT_FACTOR(P,g,7,64)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_34741861125639557_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,34741861125639557);
{
    PRATT_BUILD_PRELUDE(34741861125639557,13)
    PRATT_BUILD_BIG(1764234391)
    PRATT_BUILD_SMALL(463)
    PRATT_BUILD_SMALL(31)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_36131535570665139281_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,noi(36131535570665139280)),36131535570665139281) == 1;
{
    if(euclid_mod(pow_nat(3,noi(36131535570665139280)),36131535570665139281) != 1) {
        MODPOW_FULL(36131535570665139281,3,36131535570665139280,128)
        assert false;
    }
}

lemma void p25519_36131535570665139281_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 5, 13, 34741861125639557}) + 1 == 36131535570665139281;
{}

lemma void p25519_36131535570665139281_g3_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 5, 13, 34741861125639557}, (pratt_pow_thing)(36131535570665139281,3));
{
    if(!forall({2, 2, 2, 2, 5, 13, 34741861125639557}, (pratt_pow_thing)(36131535570665139281,3))) {
        int g = 3; int P = 36131535570665139281;
        PRATT_FACTOR(P,g,34741861125639557,16)
        PRATT_FACTOR(P,g,13,64)
        PRATT_FACTOR(P,g,5,64)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_36131535570665139281_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,36131535570665139281);
{
    PRATT_BUILD_PRELUDE(36131535570665139281,3)
    PRATT_BUILD_BIG(34741861125639557)
    PRATT_BUILD_SMALL(13)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_596242599987116128415063_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,noi(596242599987116128415062)),596242599987116128415063) == 1;
{
    if(euclid_mod(pow_nat(5,noi(596242599987116128415062)),596242599987116128415063) != 1) {
        MODPOW_FULL(596242599987116128415063,5,596242599987116128415062,128)
        assert false;
    }
}

lemma void p25519_596242599987116128415063_1_factors()
    requires true;
    ensures  product({2, 37, 223, 36131535570665139281}) + 1 == 596242599987116128415063;
{}

lemma void p25519_596242599987116128415063_g5_exact_order()
    requires true;
    ensures  !!forall({2, 37, 223, 36131535570665139281}, (pratt_pow_thing)(596242599987116128415063,5));
{
    if(!forall({2, 37, 223, 36131535570665139281}, (pratt_pow_thing)(596242599987116128415063,5))) {
        int g = 5; int P = 596242599987116128415063;
        PRATT_FACTOR(P,g,36131535570665139281,16)
        PRATT_FACTOR(P,g,223,128)
        PRATT_FACTOR(P,g,37,128)
        PRATT_FACTOR(P,g,2,128)
        assert false;
    }
}

lemma pratt_cert p25519_596242599987116128415063_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,596242599987116128415063);
{
    PRATT_BUILD_PRELUDE(596242599987116128415063,5)
    PRATT_BUILD_BIG(36131535570665139281)
    PRATT_BUILD_SMALL(223)
    PRATT_BUILD_SMALL(37)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_36753053_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(36753052)),36753053) == 1;
{
    if(euclid_mod(pow_nat(2,noi(36753052)),36753053) != 1) {
        MODPOW_FULL(36753053,2,36753052,32)
        assert false;
    }
}

lemma void p25519_36753053_1_factors()
    requires true;
    ensures  product({2, 2, 7, 443, 2963}) + 1 == 36753053;
{}

lemma void p25519_36753053_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 7, 443, 2963}, (pratt_pow_thing)(36753053,2));
{
    if(!forall({2, 2, 7, 443, 2963}, (pratt_pow_thing)(36753053,2))) {
        int g = 2; int P = 36753053;
        PRATT_FACTOR(P,g,2963,16)
        PRATT_FACTOR(P,g,443,32)
        PRATT_FACTOR(P,g,7,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_36753053_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,36753053);
{
    PRATT_BUILD_PRELUDE(36753053,2)
    PRATT_BUILD_SMALL(2963)
    PRATT_BUILD_SMALL(443)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_116989_g10_generates()
    requires true;
    ensures  euclid_mod(pow_nat(10,noi(116988)),116989) == 1;
{
    if(euclid_mod(pow_nat(10,noi(116988)),116989) != 1) {
        MODPOW_FULL(116989,10,116988,32)
        assert false;
    }
}

lemma void p25519_116989_1_factors()
    requires true;
    ensures  product({2, 2, 3, 9749}) + 1 == 116989;
{}

lemma void p25519_116989_g10_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3, 9749}, (pratt_pow_thing)(116989,10));
{
    if(!forall({2, 2, 3, 9749}, (pratt_pow_thing)(116989,10))) {
        int g = 10; int P = 116989;
        PRATT_FACTOR(P,g,9749,4)
        PRATT_FACTOR(P,g,3,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_116989_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,116989);
{
    PRATT_BUILD_PRELUDE(116989,10)
    PRATT_BUILD_SMALL(9749)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_1255525949_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(1255525948)),1255525949) == 1;
{
    if(euclid_mod(pow_nat(2,noi(1255525948)),1255525949) != 1) {
        MODPOW_FULL(1255525949,2,1255525948,32)
        assert false;
    }
}

lemma void p25519_1255525949_1_factors()
    requires true;
    ensures  product({2, 2, 2683, 116989}) + 1 == 1255525949;
{}

lemma void p25519_1255525949_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2683, 116989}, (pratt_pow_thing)(1255525949,2));
{
    if(!forall({2, 2, 2683, 116989}, (pratt_pow_thing)(1255525949,2))) {
        int g = 2; int P = 1255525949;
        PRATT_FACTOR(P,g,116989,16)
        PRATT_FACTOR(P,g,2683,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_1255525949_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,1255525949);
{
    PRATT_BUILD_PRELUDE(1255525949,2)
    PRATT_BUILD_BIG(116989)
    PRATT_BUILD_SMALL(2683)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_1335912079_g6_generates()
    requires true;
    ensures  euclid_mod(pow_nat(6,noi(1335912078)),1335912079) == 1;
{
    if(euclid_mod(pow_nat(6,noi(1335912078)),1335912079) != 1) {
        MODPOW_FULL(1335912079,6,1335912078,32)
        assert false;
    }
}

lemma void p25519_1335912079_1_factors()
    requires true;
    ensures  product({2, 3, 19, 31, 61, 6197}) + 1 == 1335912079;
{}

lemma void p25519_1335912079_g6_exact_order()
    requires true;
    ensures  !!forall({2, 3, 19, 31, 61, 6197}, (pratt_pow_thing)(1335912079,6));
{
    if(!forall({2, 3, 19, 31, 61, 6197}, (pratt_pow_thing)(1335912079,6))) {
        int g = 6; int P = 1335912079;
        PRATT_FACTOR(P,g,6197,32)
        PRATT_FACTOR(P,g,61,32)
        PRATT_FACTOR(P,g,31,32)
        PRATT_FACTOR(P,g,19,32)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_1335912079_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,1335912079);
{
    PRATT_BUILD_PRELUDE(1335912079,6)
    PRATT_BUILD_SMALL(6197)
    PRATT_BUILD_SMALL(61)
    PRATT_BUILD_SMALL(31)
    PRATT_BUILD_SMALL(19)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_32061889897_g10_generates()
    requires true;
    ensures  euclid_mod(pow_nat(10,noi(32061889896)),32061889897) == 1;
{
    if(euclid_mod(pow_nat(10,noi(32061889896)),32061889897) != 1) {
        MODPOW_FULL(32061889897,10,32061889896,64)
        assert false;
    }
}

lemma void p25519_32061889897_1_factors()
    requires true;
    ensures  product({2, 2, 2, 3, 1335912079}) + 1 == 32061889897;
{}

lemma void p25519_32061889897_g10_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 3, 1335912079}, (pratt_pow_thing)(32061889897,10));
{
    if(!forall({2, 2, 2, 3, 1335912079}, (pratt_pow_thing)(32061889897,10))) {
        int g = 10; int P = 32061889897;
        PRATT_FACTOR(P,g,1335912079,8)
        PRATT_FACTOR(P,g,3,64)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_32061889897_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,32061889897);
{
    PRATT_BUILD_PRELUDE(32061889897,10)
    PRATT_BUILD_BIG(1335912079)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_25136521679249_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,noi(25136521679248)),25136521679249) == 1;
{
    if(euclid_mod(pow_nat(3,noi(25136521679248)),25136521679249) != 1) {
        MODPOW_FULL(25136521679249,3,25136521679248,64)
        assert false;
    }
}

lemma void p25519_25136521679249_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 7, 7, 32061889897}) + 1 == 25136521679249;
{}

lemma void p25519_25136521679249_g3_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 7, 7, 32061889897}, (pratt_pow_thing)(25136521679249,3));
{
    if(!forall({2, 2, 2, 2, 7, 7, 32061889897}, (pratt_pow_thing)(25136521679249,3))) {
        int g = 3; int P = 25136521679249;
        PRATT_FACTOR(P,g,32061889897,16)
        PRATT_FACTOR(P,g,7,64)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_25136521679249_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,25136521679249);
{
    PRATT_BUILD_PRELUDE(25136521679249,3)
    PRATT_BUILD_BIG(32061889897)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_37414057161322375957408148834323969_g23_generates()
    requires true;
    ensures  euclid_mod(pow_nat(23,noi(37414057161322375957408148834323968)),37414057161322375957408148834323969) == 1;
{
    if(euclid_mod(pow_nat(23,noi(37414057161322375957408148834323968)),37414057161322375957408148834323969) != 1) {
        MODPOW_FULL(37414057161322375957408148834323969,23,37414057161322375957408148834323968,128)
        assert false;
    }
}

lemma void p25519_37414057161322375957408148834323969_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 36753053, 1255525949, 25136521679249}) + 1 == 37414057161322375957408148834323969;
{}

lemma void p25519_37414057161322375957408148834323969_g23_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 36753053, 1255525949, 25136521679249}, (pratt_pow_thing)(37414057161322375957408148834323969,23));
{
    if(!forall({2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 7, 36753053, 1255525949, 25136521679249}, (pratt_pow_thing)(37414057161322375957408148834323969,23))) {
        int g = 23; int P = 37414057161322375957408148834323969;
        PRATT_FACTOR(P,g,25136521679249,128)
        PRATT_FACTOR(P,g,1255525949,128)
        PRATT_FACTOR(P,g,36753053,128)
        PRATT_FACTOR(P,g,7,128)
        PRATT_FACTOR(P,g,3,128)
        PRATT_FACTOR(P,g,2,128)
        assert false;
    }
}

lemma pratt_cert p25519_37414057161322375957408148834323969_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,37414057161322375957408148834323969);
{
    PRATT_BUILD_PRELUDE(37414057161322375957408148834323969,23)
    PRATT_BUILD_BIG(25136521679249)
    PRATT_BUILD_BIG(1255525949)
    PRATT_BUILD_BIG(36753053)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,noi(726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365438)),726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439) == 1;
{
    if(euclid_mod(pow_nat(7,noi(726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365438)),726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439) != 1) {
        MODPOW_FULL(726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439,7,726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365438,512)
        assert false;
    }
}

lemma void p25519_726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439_1_factors()
    requires true;
    ensures  product({2, 641, 18287, 196687, 1466449, 2916841, 6700417, 1469495262398780123809, 167773885276849215533569, 596242599987116128415063, 37414057161322375957408148834323969}) + 1 == 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439;
{}

lemma void p25519_726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439_g7_exact_order()
    requires true;
    ensures  !!forall({2, 641, 18287, 196687, 1466449, 2916841, 6700417, 1469495262398780123809, 167773885276849215533569, 596242599987116128415063, 37414057161322375957408148834323969}, (pratt_pow_thing)(726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439,7));
{
    if(!forall({2, 641, 18287, 196687, 1466449, 2916841, 6700417, 1469495262398780123809, 167773885276849215533569, 596242599987116128415063, 37414057161322375957408148834323969}, (pratt_pow_thing)(726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439,7))) {
        int g = 7; int P = 726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439;
        PRATT_FACTOR(P,g,37414057161322375957408148834323969,512)
        PRATT_FACTOR(P,g,596242599987116128415063,512)
        PRATT_FACTOR(P,g,167773885276849215533569,512)
        PRATT_FACTOR(P,g,1469495262398780123809,512)
        PRATT_FACTOR(P,g,6700417,512)
        PRATT_FACTOR(P,g,2916841,512)
        PRATT_FACTOR(P,g,1466449,512)
        PRATT_FACTOR(P,g,196687,512)
        PRATT_FACTOR(P,g,18287,512)
        PRATT_FACTOR(P,g,641,512)
        PRATT_FACTOR(P,g,2,512)
        assert false;
    }
}

lemma pratt_cert p25519_726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439);
{
    PRATT_BUILD_PRELUDE(726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439,7)
    PRATT_BUILD_BIG(37414057161322375957408148834323969)
    PRATT_BUILD_BIG(596242599987116128415063)
    PRATT_BUILD_BIG(167773885276849215533569)
    PRATT_BUILD_BIG(1469495262398780123809)
    PRATT_BUILD_BIG(6700417)
    PRATT_BUILD_BIG(2916841)
    PRATT_BUILD_BIG(1466449)
    PRATT_BUILD_BIG(196687)
    PRATT_BUILD_BIG(18287)
    PRATT_BUILD_SMALL(641)
    PRATT_BUILD_SMALL(2)
    return ret;
}

  @*/

