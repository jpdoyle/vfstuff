/*@ #include "p25519.gh" @*/
/*@ #include "p25519_generated.gh" @*/
/*@ #include "p448_generated.gh" @*/

/*@

lemma void p25519_formula()
    requires true;
    ensures  emp
        //&*&  pow_nat(2,nat_of_int(255)) - 19
        //==   pow_nat(pow_nat(2,N15),N16)*pow_nat(2,N15) - 19
        &*&  pow_nat(2,nat_of_int(255)) - 19 > 0
        &*&  pow_nat(2,nat_of_int(255)) - 19
        ==   (0x8000000000000000000000000000000000000000000000000000000000000000
             - 19)
        ;
{
    pow_plus(2,nat_of_int(240),15);
    assert pow_nat(2,nat_of_int(255))
        == pow_nat(2,nat_of_int(240))*pow_nat(2,N15);
    pow_times2(2,N15,16);
}

lemma pratt_cert p25519_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,P25519);
{
    p25519_formula();
    return p25519_57896044618658097711785492504343953926634992332820282019728792003956564819949_pratt();
}

lemma void p25519_is_prime()
    requires true;
    ensures  !!is_prime(P25519);
{
    p25519_pratt();
    leak pratt_certificate(_,_,_,_);
    pratt_certificate_prime();
}

lemma void p448_formula()
    requires true;
    ensures  P448
        ==   pow_nat(pow_nat(pow_nat(2,N8),N8),N7)
        -    pow_nat(pow_nat(pow_nat(2,N8),N4),N7)
        -    1;
{
    pow_times2(2,N8,8);
    assert pow_nat(2,nat_of_int(64))
        == pow_nat(pow_nat(2,N8),N8);
    pow_times2(2,nat_of_int(64),7);
    assert pow_nat(2,nat_of_int(64*7))
        == pow_nat(pow_nat(pow_nat(2,N8),N8),N7);
    pow_times2(2,N8,4);
    pow_times2(2,nat_of_int(32),7);
}

lemma pratt_cert p448_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,P448);
{
    p448_formula();
    return p25519_726838724295606890549323807888004534353641360687318060281490199180612328166730772686396383698676545930088884461843637361053498018365439_pratt();
}

lemma void p448_is_prime()
    requires true;
    ensures  !!is_prime(P448);
{
    p448_pratt();
    leak pratt_certificate(_,_,_,_);
    pratt_certificate_prime();
}


  @*/

