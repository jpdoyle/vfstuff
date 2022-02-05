/*@ #include "p25519.gh" @*/

/*@
lemma void p25519_0x5a01_g11_generates()
    requires true;
    ensures  euclid_mod(pow_nat(11,nat_of_int(0x5a00)),0x5a01) == 1;
{
    assert (0x5a00/0x10000) == 0;
    if(euclid_mod(pow_nat(11,nat_of_int(0x5a00)),0x5a01) != 1) {
        MODPOW_FULL(0x5a01,11,0x5a00,16)
        assert false;
    }
}

lemma void p25519_0x5a01_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x5}) + 1 == 0x5a01;
{}

lemma void p25519_0x5a01_g11_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x5}, (pratt_pow_thing)(0x5a01,11));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x5}, (pratt_pow_thing)(0x5a01,11))) {
        int g = 11; int P = 0x5a01;
        PRATT_FACTOR(P,g,0x5,16)
        PRATT_FACTOR(P,g,0x3,16)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x5a01_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x5a01);
{
    PRATT_BUILD_PRELUDE(0x5a01,11)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0xf0f1_g29_generates()
    requires true;
    ensures  euclid_mod(pow_nat(29,nat_of_int(0xf0f0)),0xf0f1) == 1;
{
    assert (0xf0f0/0x10000) == 0;
    if(euclid_mod(pow_nat(29,nat_of_int(0xf0f0)),0xf0f1) != 1) {
        MODPOW_FULL(0xf0f1,29,0xf0f0,16)
        assert false;
    }
}

lemma void p25519_0xf0f1_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x101}) + 1 == 0xf0f1;
{}

lemma void p25519_0xf0f1_g29_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x101}, (pratt_pow_thing)(0xf0f1,29));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x101}, (pratt_pow_thing)(0xf0f1,29))) {
        int g = 29; int P = 0xf0f1;
        PRATT_FACTOR(P,g,0x101,8)
        PRATT_FACTOR(P,g,0x5,16)
        PRATT_FACTOR(P,g,0x3,16)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0xf0f1_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0xf0f1);
{
    PRATT_BUILD_PRELUDE(0xf0f1,29)
    PRATT_BUILD_SMALL(0x101)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x10001_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x10000)),0x10001) == 1;
{
    assert (0x10000/0x100000000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x10000)),0x10001) != 1) {
        MODPOW_FULL(0x10001,3,0x10000,32)
        assert false;
    }
}

lemma void p25519_0x10001_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2}) + 1 == 0x10001;
{}

lemma void p25519_0x10001_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2}, (pratt_pow_thing)(0x10001,3));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2}, (pratt_pow_thing)(0x10001,3))) {
        int g = 3; int P = 0x10001;
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x10001_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x10001);
{
    PRATT_BUILD_PRELUDE(0x10001,3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x65401_g13_generates()
    requires true;
    ensures  euclid_mod(pow_nat(13,nat_of_int(0x65400)),0x65401) == 1;
{
    assert (0x65400/0x100000000) == 0;
    if(euclid_mod(pow_nat(13,nat_of_int(0x65400)),0x65401) != 1) {
        MODPOW_FULL(0x65401,13,0x65400,32)
        assert false;
    }
}

lemma void p25519_0x65401_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x3, 0x3, 0x5}) + 1 == 0x65401;
{}

lemma void p25519_0x65401_g13_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x3, 0x3, 0x5}, (pratt_pow_thing)(0x65401,13));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x3, 0x3, 0x5}, (pratt_pow_thing)(0x65401,13))) {
        int g = 13; int P = 0x65401;
        PRATT_FACTOR(P,g,0x5,32)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x65401_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x65401);
{
    PRATT_BUILD_PRELUDE(0x65401,13)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x1c4bf_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x1c4be)),0x1c4bf) == 1;
{
    assert (0x1c4be/0x100000000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x1c4be)),0x1c4bf) != 1) {
        MODPOW_FULL(0x1c4bf,3,0x1c4be,32)
        assert false;
    }
}

lemma void p25519_0x1c4bf_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0x3, 0x2f, 0x89}) + 1 == 0x1c4bf;
{}

lemma void p25519_0x1c4bf_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0x3, 0x2f, 0x89}, (pratt_pow_thing)(0x1c4bf,3));
{
    if(!forall({0x2, 0x3, 0x3, 0x2f, 0x89}, (pratt_pow_thing)(0x1c4bf,3))) {
        int g = 3; int P = 0x1c4bf;
        PRATT_FACTOR(P,g,0x89,16)
        PRATT_FACTOR(P,g,0x2f,16)
        PRATT_FACTOR(P,g,0x3,16)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x1c4bf_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x1c4bf);
{
    PRATT_BUILD_PRELUDE(0x1c4bf,3)
    PRATT_BUILD_SMALL(0x89)
    PRATT_BUILD_SMALL(0x2f)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x1538f41_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(0x1538f40)),0x1538f41) == 1;
{
    assert (0x1538f40/0x100000000) == 0;
    if(euclid_mod(pow_nat(5,nat_of_int(0x1538f40)),0x1538f41) != 1) {
        MODPOW_FULL(0x1538f41,5,0x1538f40,32)
        assert false;
    }
}

lemma void p25519_0x1538f41_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x1c4bf}) + 1 == 0x1538f41;
{}

lemma void p25519_0x1538f41_g5_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x1c4bf}, (pratt_pow_thing)(0x1538f41,5));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x1c4bf}, (pratt_pow_thing)(0x1538f41,5))) {
        int g = 5; int P = 0x1538f41;
        PRATT_FACTOR(P,g,0x1c4bf,8)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x1538f41_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x1538f41);
{
    PRATT_BUILD_PRELUDE(0x1538f41,5)
    PRATT_BUILD_BIG(0x1c4bf)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x64661_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x64660)),0x64661) == 1;
{
    assert (0x64660/0x100000000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x64660)),0x64661) != 1) {
        MODPOW_FULL(0x64661,3,0x64660,32)
        assert false;
    }
}

lemma void p25519_0x64661_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x47, 0xb5}) + 1 == 0x64661;
{}

lemma void p25519_0x64661_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x47, 0xb5}, (pratt_pow_thing)(0x64661,3));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x47, 0xb5}, (pratt_pow_thing)(0x64661,3))) {
        int g = 3; int P = 0x64661;
        PRATT_FACTOR(P,g,0xb5,16)
        PRATT_FACTOR(P,g,0x47,16)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x64661_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x64661);
{
    PRATT_BUILD_PRELUDE(0x64661,3)
    PRATT_BUILD_SMALL(0xb5)
    PRATT_BUILD_SMALL(0x47)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x1787ebc1_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,nat_of_int(0x1787ebc0)),0x1787ebc1) == 1;
{
    assert (0x1787ebc0/0x100000000) == 0;
    if(euclid_mod(pow_nat(7,nat_of_int(0x1787ebc0)),0x1787ebc1) != 1) {
        MODPOW_FULL(0x1787ebc1,7,0x1787ebc0,32)
        assert false;
    }
}

lemma void p25519_0x1787ebc1_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x64661}) + 1 == 0x1787ebc1;
{}

lemma void p25519_0x1787ebc1_g7_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x64661}, (pratt_pow_thing)(0x1787ebc1,7));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x64661}, (pratt_pow_thing)(0x1787ebc1,7))) {
        int g = 7; int P = 0x1787ebc1;
        PRATT_FACTOR(P,g,0x64661,16)
        PRATT_FACTOR(P,g,0x5,32)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x1787ebc1_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x1787ebc1);
{
    PRATT_BUILD_PRELUDE(0x1787ebc1,7)
    PRATT_BUILD_BIG(0x64661)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0xff00ff01_g23_generates()
    requires true;
    ensures  euclid_mod(pow_nat(23,nat_of_int(0xff00ff00)),0xff00ff01) == 1;
{
    assert (0xff00ff00/0x100000000) == 0;
    if(euclid_mod(pow_nat(23,nat_of_int(0xff00ff00)),0xff00ff01) != 1) {
        MODPOW_FULL(0xff00ff01,23,0xff00ff00,32)
        assert false;
    }
}

lemma void p25519_0xff00ff01_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x11, 0x10001}) + 1 == 0xff00ff01;
{}

lemma void p25519_0xff00ff01_g23_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x11, 0x10001}, (pratt_pow_thing)(0xff00ff01,23));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x11, 0x10001}, (pratt_pow_thing)(0xff00ff01,23))) {
        int g = 23; int P = 0xff00ff01;
        PRATT_FACTOR(P,g,0x10001,16)
        PRATT_FACTOR(P,g,0x11,32)
        PRATT_FACTOR(P,g,0x5,32)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0xff00ff01_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0xff00ff01);
{
    PRATT_BUILD_PRELUDE(0xff00ff01,23)
    PRATT_BUILD_BIG(0x10001)
    PRATT_BUILD_SMALL(0x11)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x10feef011_g11_generates()
    requires true;
    ensures  euclid_mod(pow_nat(11,nat_of_int(0x10feef010)),0x10feef011) == 1;
{
    assert (0x10feef010/0x10000000000000000) == 0;
    if(euclid_mod(pow_nat(11,nat_of_int(0x10feef010)),0x10feef011) != 1) {
        MODPOW_FULL(0x10feef011,11,0x10feef010,64)
        assert false;
    }
}

lemma void p25519_0x10feef011_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x11, 0x13, 0xe5, 0x101}) + 1 == 0x10feef011;
{}

lemma void p25519_0x10feef011_g11_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x11, 0x13, 0xe5, 0x101}, (pratt_pow_thing)(0x10feef011,11));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x11, 0x13, 0xe5, 0x101}, (pratt_pow_thing)(0x10feef011,11))) {
        int g = 11; int P = 0x10feef011;
        PRATT_FACTOR(P,g,0x101,32)
        PRATT_FACTOR(P,g,0xe5,32)
        PRATT_FACTOR(P,g,0x13,32)
        PRATT_FACTOR(P,g,0x11,32)
        PRATT_FACTOR(P,g,0x5,32)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x10feef011_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x10feef011);
{
    PRATT_BUILD_PRELUDE(0x10feef011,11)
    PRATT_BUILD_SMALL(0x101)
    PRATT_BUILD_SMALL(0xe5)
    PRATT_BUILD_SMALL(0x13)
    PRATT_BUILD_SMALL(0x11)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x52d803_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x52d802)),0x52d803) == 1;
{
    assert (0x52d802/0x100000000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x52d802)),0x52d803) != 1) {
        MODPOW_FULL(0x52d803,2,0x52d802,32)
        assert false;
    }
}

lemma void p25519_0x52d803_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0x3, 0x5, 0x5, 0x5, 0x13, 0x7f}) + 1 == 0x52d803;
{}

lemma void p25519_0x52d803_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0x3, 0x5, 0x5, 0x5, 0x13, 0x7f}, (pratt_pow_thing)(0x52d803,2));
{
    if(!forall({0x2, 0x3, 0x3, 0x5, 0x5, 0x5, 0x13, 0x7f}, (pratt_pow_thing)(0x52d803,2))) {
        int g = 2; int P = 0x52d803;
        PRATT_FACTOR(P,g,0x7f,16)
        PRATT_FACTOR(P,g,0x13,32)
        PRATT_FACTOR(P,g,0x5,32)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x52d803_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x52d803);
{
    PRATT_BUILD_PRELUDE(0x52d803,2)
    PRATT_BUILD_SMALL(0x7f)
    PRATT_BUILD_SMALL(0x13)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0xaebfa6541_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,nat_of_int(0xaebfa6540)),0xaebfa6541) == 1;
{
    assert (0xaebfa6540/0x10000000000000000) == 0;
    if(euclid_mod(pow_nat(7,nat_of_int(0xaebfa6540)),0xaebfa6541) != 1) {
        MODPOW_FULL(0xaebfa6541,7,0xaebfa6540,64)
        assert false;
    }
}

lemma void p25519_0xaebfa6541_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x3, 0x5, 0x52d803}) + 1 == 0xaebfa6541;
{}

lemma void p25519_0xaebfa6541_g7_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x3, 0x5, 0x52d803}, (pratt_pow_thing)(0xaebfa6541,7));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x3, 0x5, 0x52d803}, (pratt_pow_thing)(0xaebfa6541,7))) {
        int g = 7; int P = 0xaebfa6541;
        PRATT_FACTOR(P,g,0x52d803,16)
        PRATT_FACTOR(P,g,0x5,64)
        PRATT_FACTOR(P,g,0x3,64)
        PRATT_FACTOR(P,g,0x2,64)
        assert false;
    }
}

lemma pratt_cert p25519_0xaebfa6541_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0xaebfa6541);
{
    PRATT_BUILD_PRELUDE(0xaebfa6541,7)
    PRATT_BUILD_BIG(0x52d803)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x4285_g10_generates()
    requires true;
    ensures  euclid_mod(pow_nat(10,nat_of_int(0x4284)),0x4285) == 1;
{
    assert (0x4284/0x10000) == 0;
    if(euclid_mod(pow_nat(10,nat_of_int(0x4284)),0x4285) != 1) {
        MODPOW_FULL(0x4285,10,0x4284,16)
        assert false;
    }
}

lemma void p25519_0x4285_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x3, 0x3, 0xb, 0x2b}) + 1 == 0x4285;
{}

lemma void p25519_0x4285_g10_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x3, 0x3, 0xb, 0x2b}, (pratt_pow_thing)(0x4285,10));
{
    if(!forall({0x2, 0x2, 0x3, 0x3, 0xb, 0x2b}, (pratt_pow_thing)(0x4285,10))) {
        int g = 10; int P = 0x4285;
        PRATT_FACTOR(P,g,0x2b,16)
        PRATT_FACTOR(P,g,0xb,16)
        PRATT_FACTOR(P,g,0x3,16)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x4285_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x4285);
{
    PRATT_BUILD_PRELUDE(0x4285,10)
    PRATT_BUILD_SMALL(0x2b)
    PRATT_BUILD_SMALL(0xb)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x5d05ff_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(0x5d05fe)),0x5d05ff) == 1;
{
    assert (0x5d05fe/0x100000000) == 0;
    if(euclid_mod(pow_nat(5,nat_of_int(0x5d05fe)),0x5d05ff) != 1) {
        MODPOW_FULL(0x5d05ff,5,0x5d05fe,32)
        assert false;
    }
}

lemma void p25519_0x5d05ff_1_factors()
    requires true;
    ensures  product({0x2, 0xb3, 0x4285}) + 1 == 0x5d05ff;
{}

lemma void p25519_0x5d05ff_g5_exact_order()
    requires true;
    ensures  !!forall({0x2, 0xb3, 0x4285}, (pratt_pow_thing)(0x5d05ff,5));
{
    if(!forall({0x2, 0xb3, 0x4285}, (pratt_pow_thing)(0x5d05ff,5))) {
        int g = 5; int P = 0x5d05ff;
        PRATT_FACTOR(P,g,0x4285,16)
        PRATT_FACTOR(P,g,0xb3,16)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x5d05ff_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x5d05ff);
{
    PRATT_BUILD_PRELUDE(0x5d05ff,5)
    PRATT_BUILD_BIG(0x4285)
    PRATT_BUILD_SMALL(0xb3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x28741f88ac01_g13_generates()
    requires true;
    ensures  euclid_mod(pow_nat(13,nat_of_int(0x28741f88ac00)),0x28741f88ac01) == 1;
{
    assert (0x28741f88ac00/0x10000000000000000) == 0;
    if(euclid_mod(pow_nat(13,nat_of_int(0x28741f88ac00)),0x28741f88ac01) != 1) {
        MODPOW_FULL(0x28741f88ac01,13,0x28741f88ac00,64)
        assert false;
    }
}

lemma void p25519_0x28741f88ac01_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x5, 0x5, 0x13, 0x5d05ff}) + 1 == 0x28741f88ac01;
{}

lemma void p25519_0x28741f88ac01_g13_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x5, 0x5, 0x13, 0x5d05ff}, (pratt_pow_thing)(0x28741f88ac01,13));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x5, 0x5, 0x13, 0x5d05ff}, (pratt_pow_thing)(0x28741f88ac01,13))) {
        int g = 13; int P = 0x28741f88ac01;
        PRATT_FACTOR(P,g,0x5d05ff,32)
        PRATT_FACTOR(P,g,0x13,64)
        PRATT_FACTOR(P,g,0x5,64)
        PRATT_FACTOR(P,g,0x3,64)
        PRATT_FACTOR(P,g,0x2,64)
        assert false;
    }
}

lemma pratt_cert p25519_0x28741f88ac01_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x28741f88ac01);
{
    PRATT_BUILD_PRELUDE(0x28741f88ac01,13)
    PRATT_BUILD_BIG(0x5d05ff)
    PRATT_BUILD_SMALL(0x13)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x11489_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x11488)),0x11489) == 1;
{
    assert (0x11488/0x100000000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x11488)),0x11489) != 1) {
        MODPOW_FULL(0x11489,3,0x11488,32)
        assert false;
    }
}

lemma void p25519_0x11489_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2291}) + 1 == 0x11489;
{}

lemma void p25519_0x11489_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2291}, (pratt_pow_thing)(0x11489,3));
{
    if(!forall({0x2, 0x2, 0x2, 0x2291}, (pratt_pow_thing)(0x11489,3))) {
        int g = 3; int P = 0x11489;
        PRATT_FACTOR(P,g,0x2291,4)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x11489_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x11489);
{
    PRATT_BUILD_PRELUDE(0x11489,3)
    PRATT_BUILD_SMALL(0x2291)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x22913_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0x22912)),0x22913) == 1;
{
    assert (0x22912/0x100000000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0x22912)),0x22913) != 1) {
        MODPOW_FULL(0x22913,2,0x22912,32)
        assert false;
    }
}

lemma void p25519_0x22913_1_factors()
    requires true;
    ensures  product({0x2, 0x11489}) + 1 == 0x22913;
{}

lemma void p25519_0x22913_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x11489}, (pratt_pow_thing)(0x22913,2));
{
    if(!forall({0x2, 0x11489}, (pratt_pow_thing)(0x22913,2))) {
        int g = 2; int P = 0x22913;
        if(!pratt_pow_thing(P,g,0x11489)) {
            pratt_pow_thing_auto(P,g,0x11489);
            assert false;
        }
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x22913_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x22913);
{
    PRATT_BUILD_PRELUDE(0x22913,2)
    PRATT_BUILD_BIG(0x11489)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x1b13caa19_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,nat_of_int(0x1b13caa18)),0x1b13caa19) == 1;
{
    assert (0x1b13caa18/0x10000000000000000) == 0;
    if(euclid_mod(pow_nat(7,nat_of_int(0x1b13caa18)),0x1b13caa19) != 1) {
        MODPOW_FULL(0x1b13caa19,7,0x1b13caa18,64)
        assert false;
    }
}

lemma void p25519_0x1b13caa19_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x3, 0x3, 0x17, 0x1f, 0x22913}) + 1 == 0x1b13caa19;
{}

lemma void p25519_0x1b13caa19_g7_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x3, 0x3, 0x17, 0x1f, 0x22913}, (pratt_pow_thing)(0x1b13caa19,7));
{
    if(!forall({0x2, 0x2, 0x2, 0x3, 0x3, 0x17, 0x1f, 0x22913}, (pratt_pow_thing)(0x1b13caa19,7))) {
        int g = 7; int P = 0x1b13caa19;
        PRATT_FACTOR(P,g,0x22913,16)
        PRATT_FACTOR(P,g,0x1f,32)
        PRATT_FACTOR(P,g,0x17,32)
        PRATT_FACTOR(P,g,0x3,32)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x1b13caa19_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x1b13caa19);
{
    PRATT_BUILD_PRELUDE(0x1b13caa19,7)
    PRATT_BUILD_BIG(0x22913)
    PRATT_BUILD_SMALL(0x1f)
    PRATT_BUILD_SMALL(0x17)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x283f_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x283e)),0x283f) == 1;
{
    assert (0x283e/0x10000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x283e)),0x283f) != 1) {
        MODPOW_FULL(0x283f,3,0x283e,16)
        assert false;
    }
}

lemma void p25519_0x283f_1_factors()
    requires true;
    ensures  product({0x2, 0x3, 0x11, 0x65}) + 1 == 0x283f;
{}

lemma void p25519_0x283f_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x3, 0x11, 0x65}, (pratt_pow_thing)(0x283f,3));
{
    if(!forall({0x2, 0x3, 0x11, 0x65}, (pratt_pow_thing)(0x283f,3))) {
        int g = 3; int P = 0x283f;
        PRATT_FACTOR(P,g,0x65,8)
        PRATT_FACTOR(P,g,0x11,16)
        PRATT_FACTOR(P,g,0x3,16)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0x283f_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x283f);
{
    PRATT_BUILD_PRELUDE(0x283f,3)
    PRATT_BUILD_SMALL(0x65)
    PRATT_BUILD_SMALL(0x11)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0xa0fd_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(0xa0fc)),0xa0fd) == 1;
{
    assert (0xa0fc/0x10000) == 0;
    if(euclid_mod(pow_nat(2,nat_of_int(0xa0fc)),0xa0fd) != 1) {
        MODPOW_FULL(0xa0fd,2,0xa0fc,16)
        assert false;
    }
}

lemma void p25519_0xa0fd_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x283f}) + 1 == 0xa0fd;
{}

lemma void p25519_0xa0fd_g2_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x283f}, (pratt_pow_thing)(0xa0fd,2));
{
    if(!forall({0x2, 0x2, 0x283f}, (pratt_pow_thing)(0xa0fd,2))) {
        int g = 2; int P = 0xa0fd;
        PRATT_FACTOR(P,g,0x283f,4)
        PRATT_FACTOR(P,g,0x2,16)
        assert false;
    }
}

lemma pratt_cert p25519_0xa0fd_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0xa0fd);
{
    PRATT_BUILD_PRELUDE(0xa0fd,2)
    PRATT_BUILD_BIG(0x283f)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x47675_g3_generates()
    requires true;
    ensures  euclid_mod(pow_nat(3,nat_of_int(0x47674)),0x47675) == 1;
{
    assert (0x47674/0x100000000) == 0;
    if(euclid_mod(pow_nat(3,nat_of_int(0x47674)),0x47675) != 1) {
        MODPOW_FULL(0x47675,3,0x47674,32)
        assert false;
    }
}

lemma void p25519_0x47675_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0xb, 0x11, 0x11, 0x17}) + 1 == 0x47675;
{}

lemma void p25519_0x47675_g3_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0xb, 0x11, 0x11, 0x17}, (pratt_pow_thing)(0x47675,3));
{
    if(!forall({0x2, 0x2, 0xb, 0x11, 0x11, 0x17}, (pratt_pow_thing)(0x47675,3))) {
        int g = 3; int P = 0x47675;
        PRATT_FACTOR(P,g,0x17,16)
        PRATT_FACTOR(P,g,0x11,16)
        PRATT_FACTOR(P,g,0xb,16)
        PRATT_FACTOR(P,g,0x2,32)
        assert false;
    }
}

lemma pratt_cert p25519_0x47675_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x47675);
{
    PRATT_BUILD_PRELUDE(0x47675,3)
    PRATT_BUILD_SMALL(0x17)
    PRATT_BUILD_SMALL(0x11)
    PRATT_BUILD_SMALL(0x11)
    PRATT_BUILD_SMALL(0xb)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x1853c5f1a49_g10_generates()
    requires true;
    ensures  euclid_mod(pow_nat(10,nat_of_int(0x1853c5f1a48)),0x1853c5f1a49) == 1;
{
    assert (0x1853c5f1a48/0x10000000000000000) == 0;
    if(euclid_mod(pow_nat(10,nat_of_int(0x1853c5f1a48)),0x1853c5f1a49) != 1) {
        MODPOW_FULL(0x1853c5f1a49,10,0x1853c5f1a48,64)
        assert false;
    }
}

lemma void p25519_0x1853c5f1a49_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x3, 0x3, 0x3, 0x3, 0x2275, 0x47675}) + 1 == 0x1853c5f1a49;
{}

lemma void p25519_0x1853c5f1a49_g10_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x3, 0x3, 0x3, 0x3, 0x2275, 0x47675}, (pratt_pow_thing)(0x1853c5f1a49,10));
{
    if(!forall({0x2, 0x2, 0x2, 0x3, 0x3, 0x3, 0x3, 0x2275, 0x47675}, (pratt_pow_thing)(0x1853c5f1a49,10))) {
        int g = 10; int P = 0x1853c5f1a49;
        PRATT_FACTOR(P,g,0x47675,32)
        PRATT_FACTOR(P,g,0x2275,32)
        PRATT_FACTOR(P,g,0x3,64)
        PRATT_FACTOR(P,g,0x2,64)
        assert false;
    }
}

lemma pratt_cert p25519_0x1853c5f1a49_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x1853c5f1a49);
{
    PRATT_BUILD_PRELUDE(0x1853c5f1a49,10)
    PRATT_BUILD_BIG(0x47675)
    PRATT_BUILD_SMALL(0x2275)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x2de53384f3fce6f01_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,nat_of_int(0x2de53384f3fce6f00)),0x2de53384f3fce6f01) == 1;
{
    assert (0x2de53384f3fce6f00/0x100000000000000000000000000000000) == 0;
    if(euclid_mod(pow_nat(5,nat_of_int(0x2de53384f3fce6f00)),0x2de53384f3fce6f01) != 1) {
        MODPOW_FULL(0x2de53384f3fce6f01,5,0x2de53384f3fce6f00,128)
        assert false;
    }
}

lemma void p25519_0x2de53384f3fce6f01_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0xa0fd, 0x1853c5f1a49}) + 1 == 0x2de53384f3fce6f01;
{}

lemma void p25519_0x2de53384f3fce6f01_g5_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0xa0fd, 0x1853c5f1a49}, (pratt_pow_thing)(0x2de53384f3fce6f01,5));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0xa0fd, 0x1853c5f1a49}, (pratt_pow_thing)(0x2de53384f3fce6f01,5))) {
        int g = 5; int P = 0x2de53384f3fce6f01;
        PRATT_FACTOR(P,g,0x1853c5f1a49,32)
        PRATT_FACTOR(P,g,0xa0fd,64)
        PRATT_FACTOR(P,g,0x3,64)
        PRATT_FACTOR(P,g,0x2,128)
        assert false;
    }
}

lemma pratt_cert p25519_0x2de53384f3fce6f01_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x2de53384f3fce6f01);
{
    PRATT_BUILD_PRELUDE(0x2de53384f3fce6f01,5)
    PRATT_BUILD_BIG(0x1853c5f1a49)
    PRATT_BUILD_BIG(0xa0fd)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0x2d82843d1bc3c7c78ed941da4a601_g26_generates()
    requires true;
    ensures  euclid_mod(pow_nat(26,nat_of_int(0x2d82843d1bc3c7c78ed941da4a600)),0x2d82843d1bc3c7c78ed941da4a601) == 1;
{
    assert (0x2d82843d1bc3c7c78ed941da4a600/0x100000000000000000000000000000000) == 0;
    if(euclid_mod(pow_nat(26,nat_of_int(0x2d82843d1bc3c7c78ed941da4a600)),0x2d82843d1bc3c7c78ed941da4a601) != 1) {
        MODPOW_FULL(0x2d82843d1bc3c7c78ed941da4a601,26,0x2d82843d1bc3c7c78ed941da4a600,128)
        assert false;
    }
}

lemma void p25519_0x2d82843d1bc3c7c78ed941da4a601_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x5, 0x1b13caa19, 0x2de53384f3fce6f01}) + 1 == 0x2d82843d1bc3c7c78ed941da4a601;
{}

lemma void p25519_0x2d82843d1bc3c7c78ed941da4a601_g26_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x5, 0x1b13caa19, 0x2de53384f3fce6f01}, (pratt_pow_thing)(0x2d82843d1bc3c7c78ed941da4a601,26));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x5, 0x5, 0x1b13caa19, 0x2de53384f3fce6f01}, (pratt_pow_thing)(0x2d82843d1bc3c7c78ed941da4a601,26))) {
        int g = 26; int P = 0x2d82843d1bc3c7c78ed941da4a601;
        PRATT_FACTOR(P,g,0x2de53384f3fce6f01,64)
        PRATT_FACTOR(P,g,0x1b13caa19,128)
        PRATT_FACTOR(P,g,0x5,128)
        PRATT_FACTOR(P,g,0x3,128)
        PRATT_FACTOR(P,g,0x2,128)
        assert false;
    }
}

lemma pratt_cert p25519_0x2d82843d1bc3c7c78ed941da4a601_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0x2d82843d1bc3c7c78ed941da4a601);
{
    PRATT_BUILD_PRELUDE(0x2d82843d1bc3c7c78ed941da4a601,26)
    PRATT_BUILD_BIG(0x2de53384f3fce6f01)
    PRATT_BUILD_BIG(0x1b13caa19)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

lemma void p25519_0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001_g23_generates()
    requires true;
    ensures  euclid_mod(pow_nat(23,nat_of_int(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000)),0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001) == 1;
{
    assert (0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000/0x100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000) == 0;
    if(euclid_mod(pow_nat(23,nat_of_int(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000)),0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001) != 1) {
        MODPOW_FULL(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001,23,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000,512)
        assert false;
    }
}

lemma void p25519_0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001_1_factors()
    requires true;
    ensures  product({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x5, 0x5, 0x7, 0xb, 0xd, 0x11, 0x1f, 0x29, 0x3d, 0x61, 0x97, 0xc1, 0xf1, 0x101, 0x14b, 0x2a1, 0x529, 0x5a01, 0xf0f1, 0x10001, 0x65401, 0x1538f41, 0x1787ebc1, 0xff00ff01, 0x10feef011, 0xaebfa6541, 0x28741f88ac01, 0x2d82843d1bc3c7c78ed941da4a601}) + 1 == 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001;
{}

lemma void p25519_0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001_g23_exact_order()
    requires true;
    ensures  !!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x5, 0x5, 0x7, 0xb, 0xd, 0x11, 0x1f, 0x29, 0x3d, 0x61, 0x97, 0xc1, 0xf1, 0x101, 0x14b, 0x2a1, 0x529, 0x5a01, 0xf0f1, 0x10001, 0x65401, 0x1538f41, 0x1787ebc1, 0xff00ff01, 0x10feef011, 0xaebfa6541, 0x28741f88ac01, 0x2d82843d1bc3c7c78ed941da4a601}, (pratt_pow_thing)(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001,23));
{
    if(!forall({0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x2, 0x3, 0x3, 0x5, 0x5, 0x7, 0xb, 0xd, 0x11, 0x1f, 0x29, 0x3d, 0x61, 0x97, 0xc1, 0xf1, 0x101, 0x14b, 0x2a1, 0x529, 0x5a01, 0xf0f1, 0x10001, 0x65401, 0x1538f41, 0x1787ebc1, 0xff00ff01, 0x10feef011, 0xaebfa6541, 0x28741f88ac01, 0x2d82843d1bc3c7c78ed941da4a601}, (pratt_pow_thing)(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001,23))) {
        int g = 23; int P = 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001;
        PRATT_FACTOR(P,g,0x2d82843d1bc3c7c78ed941da4a601,512)
        PRATT_FACTOR(P,g,0x28741f88ac01,512)
        PRATT_FACTOR(P,g,0xaebfa6541,512)
        PRATT_FACTOR(P,g,0x10feef011,512)
        PRATT_FACTOR(P,g,0xff00ff01,512)
        PRATT_FACTOR(P,g,0x1787ebc1,512)
        PRATT_FACTOR(P,g,0x1538f41,512)
        PRATT_FACTOR(P,g,0x65401,512)
        PRATT_FACTOR(P,g,0x10001,512)
        PRATT_FACTOR(P,g,0xf0f1,512)
        PRATT_FACTOR(P,g,0x5a01,512)
        PRATT_FACTOR(P,g,0x529,512)
        PRATT_FACTOR(P,g,0x2a1,512)
        PRATT_FACTOR(P,g,0x14b,512)
        PRATT_FACTOR(P,g,0x101,512)
        PRATT_FACTOR(P,g,0xf1,512)
        PRATT_FACTOR(P,g,0xc1,512)
        PRATT_FACTOR(P,g,0x97,512)
        PRATT_FACTOR(P,g,0x61,512)
        PRATT_FACTOR(P,g,0x3d,512)
        PRATT_FACTOR(P,g,0x29,512)
        PRATT_FACTOR(P,g,0x1f,512)
        PRATT_FACTOR(P,g,0x11,512)
        PRATT_FACTOR(P,g,0xd,512)
        PRATT_FACTOR(P,g,0xb,512)
        PRATT_FACTOR(P,g,0x7,512)
        PRATT_FACTOR(P,g,0x5,512)
        PRATT_FACTOR(P,g,0x3,512)
        PRATT_FACTOR(P,g,0x2,512)
        assert false;
    }
}

lemma pratt_cert p25519_0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001);
{
    PRATT_BUILD_PRELUDE(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000001,23)
    PRATT_BUILD_BIG(0x2d82843d1bc3c7c78ed941da4a601)
    PRATT_BUILD_BIG(0x28741f88ac01)
    PRATT_BUILD_BIG(0xaebfa6541)
    PRATT_BUILD_BIG(0x10feef011)
    PRATT_BUILD_BIG(0xff00ff01)
    PRATT_BUILD_BIG(0x1787ebc1)
    PRATT_BUILD_BIG(0x1538f41)
    PRATT_BUILD_BIG(0x65401)
    PRATT_BUILD_BIG(0x10001)
    PRATT_BUILD_BIG(0xf0f1)
    PRATT_BUILD_BIG(0x5a01)
    PRATT_BUILD_SMALL(0x529)
    PRATT_BUILD_SMALL(0x2a1)
    PRATT_BUILD_SMALL(0x14b)
    PRATT_BUILD_SMALL(0x101)
    PRATT_BUILD_SMALL(0xf1)
    PRATT_BUILD_SMALL(0xc1)
    PRATT_BUILD_SMALL(0x97)
    PRATT_BUILD_SMALL(0x61)
    PRATT_BUILD_SMALL(0x3d)
    PRATT_BUILD_SMALL(0x29)
    PRATT_BUILD_SMALL(0x1f)
    PRATT_BUILD_SMALL(0x11)
    PRATT_BUILD_SMALL(0xd)
    PRATT_BUILD_SMALL(0xb)
    PRATT_BUILD_SMALL(0x7)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x5)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x3)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    PRATT_BUILD_SMALL(0x2)
    return ret;
}

  @*/

