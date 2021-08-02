/*@ #include "p25519.gh" @*/

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

lemma void p25519_2_generates1()
    requires true;
    ensures fast_pow_mod(P25519, 2, true,
            nat_of_int(pow_nat(2,nat_of_int(4))-1),
            nat_of_int(pow_nat(2,nat_of_int(5))-1),
            2147483648);
{
    p25519_formula();

    close fast_pow_mod(P25519, 2, true,
        nat_of_int(0),
        nat_of_int(pow_nat(2,nat_of_int(1))-1),
        ?r1);
    note_eq(r1, 2);

    division_unique(
        pow_nat(2,nat_of_int(1))-1,
        2,
        pow_nat(2,nat_of_int(0))-1,
        1);

    close fast_pow_mod(P25519, 2, true,
        nat_of_int(pow_nat(2,nat_of_int(1))-1),
        nat_of_int(pow_nat(2,nat_of_int(2))-1),
        ?r2);
    note_eq(r2, 2*r1*r1);

    division_unique(
        pow_nat(2,nat_of_int(2))-1,
        2,
        pow_nat(2,nat_of_int(1))-1,
        1);

    close fast_pow_mod(P25519, 2, true,
        nat_of_int(pow_nat(2,nat_of_int(2))-1),
        nat_of_int(pow_nat(2,nat_of_int(3))-1),
        ?r3);
    note_eq(r3, 2*r2*r2);
    note_eq(r3, 128);

    division_unique(
        pow_nat(2,nat_of_int(3))-1,
        2,
        pow_nat(2,nat_of_int(2))-1,
        1);

    close fast_pow_mod(P25519, 2, true,
        nat_of_int(pow_nat(2,nat_of_int(3))-1),
        nat_of_int(pow_nat(2,nat_of_int(4))-1),
        ?r4);
    euclid_mod_small(2*r3*r3,P25519);
    note_eq(r4, 2*r3*r3);

    division_unique(
        pow_nat(2,nat_of_int(4))-1,
        2,
        pow_nat(2,nat_of_int(3))-1,
        1);

    close fast_pow_mod(P25519, 2, true,
        nat_of_int(pow_nat(2,nat_of_int(4))-1),
        nat_of_int(pow_nat(2,nat_of_int(5))-1),
        ?r5);
    euclid_mod_small(2*r4*r4,P25519);
    note_eq(r5, 2*r4*r4);

}

lemma void p25519_2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(P25519-1)),P25519)
        ==   1;
{
    p25519_2_generates1();
    p25519_formula();
    int r5 = 2147483648;

    division_unique(
        pow_nat(2,nat_of_int(5))-1,
        2,
        pow_nat(2,nat_of_int(4))-1,
        1);

    close fast_pow_mod(P25519, 2, true,
        nat_of_int(pow_nat(2,nat_of_int(5))-1),
        nat_of_int(pow_nat(2,nat_of_int(6))-1),
        ?r6);
    note_eq(r6, 2*r5*r5);

    division_unique(
        pow_nat(2,nat_of_int(6))-1,
        2,
        pow_nat(2,nat_of_int(5))-1,
        1);

}

  @*/

