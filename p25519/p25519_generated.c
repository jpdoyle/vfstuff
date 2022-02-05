/*@ #include "p25519.gh" @*/
/*@ #include "p25519_generated.gh" @*/

/*@

lemma void p25519_32573_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(32572)),32573) == 1;
{
    if(euclid_mod(pow_nat(2,noi(32572)),32573) != 1) {
        MODPOW_FULL(32573,2,32572,16)
        assert false;
    }
}

lemma void p25519_32573_1_factors()
    requires true;
    ensures  product({2, 2, 17, 479}) + 1 == 32573;
{}

lemma void p25519_32573_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 17, 479}, (pratt_pow_thing)(32573,2));
{
    if(!forall({2, 2, 17, 479}, (pratt_pow_thing)(32573,2))) {
        int g = 2; int P = 32573;
        PRATT_FACTOR(P,g,479,8)
        PRATT_FACTOR(P,g,17,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_32573_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,32573);
{
    PRATT_BUILD_PRELUDE(32573,2)
    PRATT_BUILD_SMALL(479)
    PRATT_BUILD_SMALL(17)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_65147_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(65146)),65147) == 1;
{
    if(euclid_mod(pow_nat(2,noi(65146)),65147) != 1) {
        MODPOW_FULL(65147,2,65146,16)
        assert false;
    }
}

lemma void p25519_65147_1_factors()
    requires true;
    ensures  product({2, 32573}) + 1 == 65147;
{}

lemma void p25519_65147_g2_exact_order()
    requires true;
    ensures  !!forall({2, 32573}, (pratt_pow_thing)(65147,2));
{
    if(!forall({2, 32573}, (pratt_pow_thing)(65147,2))) {
        int g = 2; int P = 65147;
        if(!pratt_pow_thing(P,g,32573)) {
            pratt_pow_thing_auto(P,g,32573);
            assert false;
        }
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_65147_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,65147);
{
    PRATT_BUILD_PRELUDE(65147,2)
    PRATT_BUILD_BIG(32573)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_57467_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(57466)),57467) == 1;
{
    if(euclid_mod(pow_nat(2,noi(57466)),57467) != 1) {
        MODPOW_FULL(57467,2,57466,16)
        assert false;
    }
}

lemma void p25519_57467_1_factors()
    requires true;
    ensures  product({2, 59, 487}) + 1 == 57467;
{}

lemma void p25519_57467_g2_exact_order()
    requires true;
    ensures  !!forall({2, 59, 487}, (pratt_pow_thing)(57467,2));
{
    if(!forall({2, 59, 487}, (pratt_pow_thing)(57467,2))) {
        int g = 2; int P = 57467;
        PRATT_FACTOR(P,g,487,8)
        PRATT_FACTOR(P,g,59,16)
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_57467_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,57467);
{
    PRATT_BUILD_PRELUDE(57467,2)
    PRATT_BUILD_SMALL(487)
    PRATT_BUILD_SMALL(59)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_132049_g26_generates()
    requires true;
    ensures  euclid_mod(pow_nat(26,noi(132048)),132049) == 1;
{
    if(euclid_mod(pow_nat(26,noi(132048)),132049) != 1) {
        MODPOW_FULL(132049,26,132048,32)
        assert false;
    }
}

lemma void p25519_132049_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 3, 3, 7, 131}) + 1 == 132049;
{}

lemma void p25519_132049_g26_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 3, 3, 7, 131}, (pratt_pow_thing)(132049,26));
{
    if(!forall({2, 2, 2, 2, 3, 3, 7, 131}, (pratt_pow_thing)(132049,26))) {
        int g = 26; int P = 132049;
        PRATT_FACTOR(P,g,131,16)
        PRATT_FACTOR(P,g,7,16)
        PRATT_FACTOR(P,g,3,16)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_132049_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,132049);
{
    PRATT_BUILD_PRELUDE(132049,26)
    PRATT_BUILD_SMALL(131)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_1923133_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(1923132)),1923133) == 1;
{
    if(euclid_mod(pow_nat(2,noi(1923132)),1923133) != 1) {
        MODPOW_FULL(1923133,2,1923132,32)
        assert false;
    }
}

lemma void p25519_1923133_1_factors()
    requires true;
    ensures  product({2, 2, 3, 43, 3727}) + 1 == 1923133;
{}

lemma void p25519_1923133_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3, 43, 3727}, (pratt_pow_thing)(1923133,2));
{
    if(!forall({2, 2, 3, 43, 3727}, (pratt_pow_thing)(1923133,2))) {
        int g = 2; int P = 1923133;
        PRATT_FACTOR(P,g,3727,16)
        PRATT_FACTOR(P,g,43,16)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_1923133_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,1923133);
{
    PRATT_BUILD_PRELUDE(1923133,2)
    PRATT_BUILD_SMALL(3727)
    PRATT_BUILD_SMALL(43)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_430751_g17_generates()
    requires true;
    ensures  euclid_mod(pow_nat(17,noi(430750)),430751) == 1;
{
    if(euclid_mod(pow_nat(17,noi(430750)),430751) != 1) {
        MODPOW_FULL(430751,17,430750,32)
        assert false;
    }
}

lemma void p25519_430751_1_factors()
    requires true;
    ensures  product({2, 5, 5, 5, 1723}) + 1 == 430751;
{}

lemma void p25519_430751_g17_exact_order()
    requires true;
    ensures  !!forall({2, 5, 5, 5, 1723}, (pratt_pow_thing)(430751,17));
{
    if(!forall({2, 5, 5, 5, 1723}, (pratt_pow_thing)(430751,17))) {
        int g = 17; int P = 430751;
        PRATT_FACTOR(P,g,1723,8)
        PRATT_FACTOR(P,g,5,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_430751_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,430751);
{
    PRATT_BUILD_PRELUDE(430751,17)
    PRATT_BUILD_SMALL(1723)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_31757755568855353_g10_generates()
    requires true;
    ensures  euclid_mod(pow_nat(10,noi(31757755568855352)),31757755568855353) == 1;
{
    if(euclid_mod(pow_nat(10,noi(31757755568855352)),31757755568855353) != 1) {
        MODPOW_FULL(31757755568855353,10,31757755568855352,64)
        assert false;
    }
}

lemma void p25519_31757755568855353_1_factors()
    requires true;
    ensures  product({2, 2, 2, 3, 31, 107, 223, 4153, 430751}) + 1 == 31757755568855353;
{}

lemma void p25519_31757755568855353_g10_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 3, 31, 107, 223, 4153, 430751}, (pratt_pow_thing)(31757755568855353,10));
{
    if(!forall({2, 2, 2, 3, 31, 107, 223, 4153, 430751}, (pratt_pow_thing)(31757755568855353,10))) {
        int g = 10; int P = 31757755568855353;
        PRATT_FACTOR(P,g,430751,64)
        PRATT_FACTOR(P,g,4153,64)
        PRATT_FACTOR(P,g,223,64)
        PRATT_FACTOR(P,g,107,64)
        PRATT_FACTOR(P,g,31,64)
        PRATT_FACTOR(P,g,3,64)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_31757755568855353_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,31757755568855353);
{
    PRATT_BUILD_PRELUDE(31757755568855353,10)
    PRATT_BUILD_BIG(430751)
    PRATT_BUILD_SMALL(4153)
    PRATT_BUILD_SMALL(223)
    PRATT_BUILD_SMALL(107)
    PRATT_BUILD_SMALL(31)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_37853_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(37852)),37853) == 1;
{
    if(euclid_mod(pow_nat(2,noi(37852)),37853) != 1) {
        MODPOW_FULL(37853,2,37852,16)
        assert false;
    }
}

lemma void p25519_37853_1_factors()
    requires true;
    ensures  product({2, 2, 9463}) + 1 == 37853;
{}

lemma void p25519_37853_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 9463}, (pratt_pow_thing)(37853,2));
{
    if(!forall({2, 2, 9463}, (pratt_pow_thing)(37853,2))) {
        int g = 2; int P = 37853;
        if(!pratt_pow_thing(P,g,9463)) {
            pratt_pow_thing_auto(P,g,9463);
            assert false;
        }
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_37853_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,37853);
{
    PRATT_BUILD_PRELUDE(37853,2)
    PRATT_BUILD_SMALL(9463)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_75707_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(75706)),75707) == 1;
{
    if(euclid_mod(pow_nat(2,noi(75706)),75707) != 1) {
        MODPOW_FULL(75707,2,75706,32)
        assert false;
    }
}

lemma void p25519_75707_1_factors()
    requires true;
    ensures  product({2, 37853}) + 1 == 75707;
{}

lemma void p25519_75707_g2_exact_order()
    requires true;
    ensures  !!forall({2, 37853}, (pratt_pow_thing)(75707,2));
{
    if(!forall({2, 37853}, (pratt_pow_thing)(75707,2))) {
        int g = 2; int P = 75707;
        if(!pratt_pow_thing(P,g,37853)) {
            pratt_pow_thing_auto(P,g,37853);
            assert false;
        }
        PRATT_FACTOR(P,g,2,16)
        assert false;
    }
}

lemma pratt_cert p25519_75707_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,75707);
{
    PRATT_BUILD_PRELUDE(75707,2)
    PRATT_BUILD_BIG(37853)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_569003_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(569002)),569003) == 1;
{
    if(euclid_mod(pow_nat(2,noi(569002)),569003) != 1) {
        MODPOW_FULL(569003,2,569002,32)
        assert false;
    }
}

lemma void p25519_569003_1_factors()
    requires true;
    ensures  product({2, 7, 97, 419}) + 1 == 569003;
{}

lemma void p25519_569003_g2_exact_order()
    requires true;
    ensures  !!forall({2, 7, 97, 419}, (pratt_pow_thing)(569003,2));
{
    if(!forall({2, 7, 97, 419}, (pratt_pow_thing)(569003,2))) {
        int g = 2; int P = 569003;
        PRATT_FACTOR(P,g,419,16)
        PRATT_FACTOR(P,g,97,16)
        PRATT_FACTOR(P,g,7,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_569003_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,569003);
{
    PRATT_BUILD_PRELUDE(569003,2)
    PRATT_BUILD_SMALL(419)
    PRATT_BUILD_SMALL(97)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_2773320623_g5_generates()
    requires true;
    ensures  euclid_mod(pow_nat(5,noi(2773320622)),2773320623) == 1;
{
    if(euclid_mod(pow_nat(5,noi(2773320622)),2773320623) != 1) {
        MODPOW_FULL(2773320623,5,2773320622,32)
        assert false;
    }
}

lemma void p25519_2773320623_1_factors()
    requires true;
    ensures  product({2, 2437, 569003}) + 1 == 2773320623;
{}

lemma void p25519_2773320623_g5_exact_order()
    requires true;
    ensures  !!forall({2, 2437, 569003}, (pratt_pow_thing)(2773320623,5));
{
    if(!forall({2, 2437, 569003}, (pratt_pow_thing)(2773320623,5))) {
        int g = 5; int P = 2773320623;
        PRATT_FACTOR(P,g,569003,16)
        PRATT_FACTOR(P,g,2437,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_2773320623_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,2773320623);
{
    PRATT_BUILD_PRELUDE(2773320623,5)
    PRATT_BUILD_BIG(569003)
    PRATT_BUILD_SMALL(2437)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_72106336199_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,noi(72106336198)),72106336199) == 1;
{
    if(euclid_mod(pow_nat(7,noi(72106336198)),72106336199) != 1) {
        MODPOW_FULL(72106336199,7,72106336198,64)
        assert false;
    }
}

lemma void p25519_72106336199_1_factors()
    requires true;
    ensures  product({2, 13, 2773320623}) + 1 == 72106336199;
{}

lemma void p25519_72106336199_g7_exact_order()
    requires true;
    ensures  !!forall({2, 13, 2773320623}, (pratt_pow_thing)(72106336199,7));
{
    if(!forall({2, 13, 2773320623}, (pratt_pow_thing)(72106336199,7))) {
        int g = 7; int P = 72106336199;
        PRATT_FACTOR(P,g,2773320623,8)
        PRATT_FACTOR(P,g,13,64)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_72106336199_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,72106336199);
{
    PRATT_BUILD_PRELUDE(72106336199,7)
    PRATT_BUILD_BIG(2773320623)
    PRATT_BUILD_SMALL(13)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_8574133_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(8574132)),8574133) == 1;
{
    if(euclid_mod(pow_nat(2,noi(8574132)),8574133) != 1) {
        MODPOW_FULL(8574133,2,8574132,32)
        assert false;
    }
}

lemma void p25519_8574133_1_factors()
    requires true;
    ensures  product({2, 2, 3, 7, 103, 991}) + 1 == 8574133;
{}

lemma void p25519_8574133_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3, 7, 103, 991}, (pratt_pow_thing)(8574133,2));
{
    if(!forall({2, 2, 3, 7, 103, 991}, (pratt_pow_thing)(8574133,2))) {
        int g = 2; int P = 8574133;
        PRATT_FACTOR(P,g,991,16)
        PRATT_FACTOR(P,g,103,32)
        PRATT_FACTOR(P,g,7,32)
        PRATT_FACTOR(P,g,3,32)
        PRATT_FACTOR(P,g,2,32)
        assert false;
    }
}

lemma pratt_cert p25519_8574133_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,8574133);
{
    PRATT_BUILD_PRELUDE(8574133,2)
    PRATT_BUILD_SMALL(991)
    PRATT_BUILD_SMALL(103)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_1919519569386763_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(1919519569386762)),1919519569386763) == 1;
{
    if(euclid_mod(pow_nat(2,noi(1919519569386762)),1919519569386763) != 1) {
        MODPOW_FULL(1919519569386763,2,1919519569386762,64)
        assert false;
    }
}

lemma void p25519_1919519569386763_1_factors()
    requires true;
    ensures  product({2, 3, 7, 19, 47, 47, 127, 8574133}) + 1 == 1919519569386763;
{}

lemma void p25519_1919519569386763_g2_exact_order()
    requires true;
    ensures  !!forall({2, 3, 7, 19, 47, 47, 127, 8574133}, (pratt_pow_thing)(1919519569386763,2));
{
    if(!forall({2, 3, 7, 19, 47, 47, 127, 8574133}, (pratt_pow_thing)(1919519569386763,2))) {
        int g = 2; int P = 1919519569386763;
        PRATT_FACTOR(P,g,8574133,32)
        PRATT_FACTOR(P,g,127,64)
        PRATT_FACTOR(P,g,47,64)
        PRATT_FACTOR(P,g,19,64)
        PRATT_FACTOR(P,g,7,64)
        PRATT_FACTOR(P,g,3,64)
        PRATT_FACTOR(P,g,2,64)
        assert false;
    }
}

lemma pratt_cert p25519_1919519569386763_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,1919519569386763);
{
    PRATT_BUILD_PRELUDE(1919519569386763,2)
    PRATT_BUILD_BIG(8574133)
    PRATT_BUILD_SMALL(127)
    PRATT_BUILD_SMALL(47)
    PRATT_BUILD_SMALL(47)
    PRATT_BUILD_SMALL(19)
    PRATT_BUILD_SMALL(7)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_75445702479781427272750846543864801_g7_generates()
    requires true;
    ensures  euclid_mod(pow_nat(7,noi(75445702479781427272750846543864800)),75445702479781427272750846543864801) == 1;
{
    if(euclid_mod(pow_nat(7,noi(75445702479781427272750846543864800)),75445702479781427272750846543864801) != 1) {
        MODPOW_FULL(75445702479781427272750846543864801,7,75445702479781427272750846543864800,128)
        assert false;
    }
}

lemma void p25519_75445702479781427272750846543864801_1_factors()
    requires true;
    ensures  product({2, 2, 2, 2, 2, 3, 3, 5, 5, 75707, 72106336199, 1919519569386763}) + 1 == 75445702479781427272750846543864801;
{}

lemma void p25519_75445702479781427272750846543864801_g7_exact_order()
    requires true;
    ensures  !!forall({2, 2, 2, 2, 2, 3, 3, 5, 5, 75707, 72106336199, 1919519569386763}, (pratt_pow_thing)(75445702479781427272750846543864801,7));
{
    if(!forall({2, 2, 2, 2, 2, 3, 3, 5, 5, 75707, 72106336199, 1919519569386763}, (pratt_pow_thing)(75445702479781427272750846543864801,7))) {
        int g = 7; int P = 75445702479781427272750846543864801;
        PRATT_FACTOR(P,g,1919519569386763,128)
        PRATT_FACTOR(P,g,72106336199,128)
        PRATT_FACTOR(P,g,75707,128)
        PRATT_FACTOR(P,g,5,128)
        PRATT_FACTOR(P,g,3,128)
        PRATT_FACTOR(P,g,2,128)
        assert false;
    }
}

lemma pratt_cert p25519_75445702479781427272750846543864801_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,75445702479781427272750846543864801);
{
    PRATT_BUILD_PRELUDE(75445702479781427272750846543864801,7)
    PRATT_BUILD_BIG(1919519569386763)
    PRATT_BUILD_BIG(72106336199)
    PRATT_BUILD_BIG(75707)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(5)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_74058212732561358302231226437062788676166966415465897661863160754340907_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(74058212732561358302231226437062788676166966415465897661863160754340906)),74058212732561358302231226437062788676166966415465897661863160754340907) == 1;
{
    if(euclid_mod(pow_nat(2,noi(74058212732561358302231226437062788676166966415465897661863160754340906)),74058212732561358302231226437062788676166966415465897661863160754340907) != 1) {
        MODPOW_FULL(74058212732561358302231226437062788676166966415465897661863160754340907,2,74058212732561358302231226437062788676166966415465897661863160754340906,256)
        assert false;
    }
}

lemma void p25519_74058212732561358302231226437062788676166966415465897661863160754340907_1_factors()
    requires true;
    ensures  product({2, 3, 353, 57467, 132049, 1923133, 31757755568855353, 75445702479781427272750846543864801}) + 1 == 74058212732561358302231226437062788676166966415465897661863160754340907;
{}

lemma void p25519_74058212732561358302231226437062788676166966415465897661863160754340907_g2_exact_order()
    requires true;
    ensures  !!forall({2, 3, 353, 57467, 132049, 1923133, 31757755568855353, 75445702479781427272750846543864801}, (pratt_pow_thing)(74058212732561358302231226437062788676166966415465897661863160754340907,2));
{
    if(!forall({2, 3, 353, 57467, 132049, 1923133, 31757755568855353, 75445702479781427272750846543864801}, (pratt_pow_thing)(74058212732561358302231226437062788676166966415465897661863160754340907,2))) {
        int g = 2; int P = 74058212732561358302231226437062788676166966415465897661863160754340907;
        PRATT_FACTOR(P,g,75445702479781427272750846543864801,128)
        PRATT_FACTOR(P,g,31757755568855353,256)
        PRATT_FACTOR(P,g,1923133,256)
        PRATT_FACTOR(P,g,132049,256)
        PRATT_FACTOR(P,g,57467,256)
        PRATT_FACTOR(P,g,353,256)
        PRATT_FACTOR(P,g,3,256)
        PRATT_FACTOR(P,g,2,256)
        assert false;
    }
}

lemma pratt_cert p25519_74058212732561358302231226437062788676166966415465897661863160754340907_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,74058212732561358302231226437062788676166966415465897661863160754340907);
{
    PRATT_BUILD_PRELUDE(74058212732561358302231226437062788676166966415465897661863160754340907,2)
    PRATT_BUILD_BIG(75445702479781427272750846543864801)
    PRATT_BUILD_BIG(31757755568855353)
    PRATT_BUILD_BIG(1923133)
    PRATT_BUILD_BIG(132049)
    PRATT_BUILD_BIG(57467)
    PRATT_BUILD_SMALL(353)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    return ret;
}

lemma void p25519_57896044618658097711785492504343953926634992332820282019728792003956564819949_g2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,noi(57896044618658097711785492504343953926634992332820282019728792003956564819948)),57896044618658097711785492504343953926634992332820282019728792003956564819949) == 1;
{
    if(euclid_mod(pow_nat(2,noi(57896044618658097711785492504343953926634992332820282019728792003956564819948)),57896044618658097711785492504343953926634992332820282019728792003956564819949) != 1) {
        MODPOW_FULL(57896044618658097711785492504343953926634992332820282019728792003956564819949,2,57896044618658097711785492504343953926634992332820282019728792003956564819948,256)
        assert false;
    }
}

lemma void p25519_57896044618658097711785492504343953926634992332820282019728792003956564819949_1_factors()
    requires true;
    ensures  product({2, 2, 3, 65147, 74058212732561358302231226437062788676166966415465897661863160754340907}) + 1 == 57896044618658097711785492504343953926634992332820282019728792003956564819949;
{}

lemma void p25519_57896044618658097711785492504343953926634992332820282019728792003956564819949_g2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 3, 65147, 74058212732561358302231226437062788676166966415465897661863160754340907}, (pratt_pow_thing)(57896044618658097711785492504343953926634992332820282019728792003956564819949,2));
{
    if(!forall({2, 2, 3, 65147, 74058212732561358302231226437062788676166966415465897661863160754340907}, (pratt_pow_thing)(57896044618658097711785492504343953926634992332820282019728792003956564819949,2))) {
        int g = 2; int P = 57896044618658097711785492504343953926634992332820282019728792003956564819949;
        PRATT_FACTOR(P,g,74058212732561358302231226437062788676166966415465897661863160754340907,32)
        PRATT_FACTOR(P,g,65147,256)
        PRATT_FACTOR(P,g,3,256)
        PRATT_FACTOR(P,g,2,256)
        assert false;
    }
}

lemma pratt_cert p25519_57896044618658097711785492504343953926634992332820282019728792003956564819949_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,57896044618658097711785492504343953926634992332820282019728792003956564819949);
{
    PRATT_BUILD_PRELUDE(57896044618658097711785492504343953926634992332820282019728792003956564819949,2)
    PRATT_BUILD_BIG(74058212732561358302231226437062788676166966415465897661863160754340907)
    PRATT_BUILD_BIG(65147)
    PRATT_BUILD_SMALL(3)
    PRATT_BUILD_SMALL(2)
    PRATT_BUILD_SMALL(2)
    return ret;
}

  @*/

