/*@ #include "p75445702479781427272750846543864801_factors.gh" @*/

#if 0
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
    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x6d1cafa129d0b));

    if(euclid_mod(pow_nat(2,nat_of_int(0xda39)),0x6d1cafa129d0b) != 0x578c2671fcfaf) {
        exp_by_sq(0x6d1cafa129d0b,2,0x0,0x1);
        exp_by_sq(0x6d1cafa129d0b,2,0x1,0x2);
        exp_by_sq(0x6d1cafa129d0b,2,0x3,0x8);
        exp_by_sq(0x6d1cafa129d0b,2,0x6,0x40);
        exp_by_sq(0x6d1cafa129d0b,2,0xd,0x2000);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b,0x8000000);
        exp_by_sq(0x6d1cafa129d0b,2,0x36,0x29fdd35587a9d);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d,0x295b2fbcd42f4);
        exp_by_sq(0x6d1cafa129d0b,2,0xda,0x61166addedc17);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b4,0x6b0a0954e7b6e);
        exp_by_sq(0x6d1cafa129d0b,2,0x368,0x45420b5fadccd);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1,0x3b98a4bf53795);
        exp_by_sq(0x6d1cafa129d0b,2,0xda3,0x37e0f607e7f94);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b47,0x4894d4d314935);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e,0x6555b55fdf9e6);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1c,0x8d138ebee13d);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0xda395f42)),0x6d1cafa129d0b) != 0x548ac4b2aa061) {
        exp_by_sq(0x6d1cafa129d0b,2,0xda39,0x578c2671fcfaf);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472,0x4c09b770744d1);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e5,0x468400872000b);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1ca,0x5b3ea75e30cf3);
        exp_by_sq(0x6d1cafa129d0b,2,0xda395,0x5a17505e6a087);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472b,0x4630268a12c4f);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57,0x464d73f2f6364);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1caf,0x25bb03d69c925);
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f,0x1223cbf886e1e);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be,0x2127135d49b56);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d,0x4918ac85163c8);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1cafa,0x4938d0da891e2);
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f4,0x37d8eb9780af3);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be8,0x5997b1847406a);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d0,0x5d349af453cb);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1cafa1,0x1b30a8554d7c5);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0xda395f4253a1)),0x6d1cafa129d0b) != 0x242c583969aab) {
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f42,0x548ac4b2aa061);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be84,0x4a2d12b335b6c);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d09,0x57f5fff71d20c);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1cafa12,0x47ad71b73d6a2);
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f425,0x4b0e49a3b7d9f);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be84a,0x6664fbe0bf9d5);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d094,0x206b2c857eb86);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1cafa129,0x52dd302e14596);
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f4253,0x336910aac2051);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be84a7,0x37c19492ff0fd);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d094e,0x33f45d6c97d75);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1cafa129d,0x5dfefa9462cb3);
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f4253a,0x3147a3c99c3c);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be84a74,0x395bbb7e480be);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d094e8,0x16fca513d7e13);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1cafa129d0,0x553615ee67494);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0x6d1cafa129d0a)),0x6d1cafa129d0b) != 0x1) {
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f4253a1,0x242c583969aab);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be84a742,0x2f143f8d4b441);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d094e85,0x6d1cafa129d0a);
        assert false;
    }


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
    ALREADY_PROVEN()
    int g = 2; int p = 1919519569386763; int q;
    q = 2;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x6d1cafa129d0b));

    if(euclid_mod(pow_nat(2,nat_of_int(0xda39)),0x6d1cafa129d0b) != 0x578c2671fcfaf) {
        exp_by_sq(0x6d1cafa129d0b,2,0x0,0x1);
        exp_by_sq(0x6d1cafa129d0b,2,0x1,0x2);
        exp_by_sq(0x6d1cafa129d0b,2,0x3,0x8);
        exp_by_sq(0x6d1cafa129d0b,2,0x6,0x40);
        exp_by_sq(0x6d1cafa129d0b,2,0xd,0x2000);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b,0x8000000);
        exp_by_sq(0x6d1cafa129d0b,2,0x36,0x29fdd35587a9d);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d,0x295b2fbcd42f4);
        exp_by_sq(0x6d1cafa129d0b,2,0xda,0x61166addedc17);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b4,0x6b0a0954e7b6e);
        exp_by_sq(0x6d1cafa129d0b,2,0x368,0x45420b5fadccd);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1,0x3b98a4bf53795);
        exp_by_sq(0x6d1cafa129d0b,2,0xda3,0x37e0f607e7f94);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b47,0x4894d4d314935);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e,0x6555b55fdf9e6);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1c,0x8d138ebee13d);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0xda395f42)),0x6d1cafa129d0b) != 0x548ac4b2aa061) {
        exp_by_sq(0x6d1cafa129d0b,2,0xda39,0x578c2671fcfaf);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472,0x4c09b770744d1);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e5,0x468400872000b);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1ca,0x5b3ea75e30cf3);
        exp_by_sq(0x6d1cafa129d0b,2,0xda395,0x5a17505e6a087);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472b,0x4630268a12c4f);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57,0x464d73f2f6364);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1caf,0x25bb03d69c925);
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f,0x1223cbf886e1e);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be,0x2127135d49b56);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d,0x4918ac85163c8);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1cafa,0x4938d0da891e2);
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f4,0x37d8eb9780af3);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be8,0x5997b1847406a);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d0,0x5d349af453cb);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1cafa1,0x1b30a8554d7c5);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0xda395f4253a1)),0x6d1cafa129d0b) != 0x242c583969aab) {
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f42,0x548ac4b2aa061);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be84,0x4a2d12b335b6c);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d09,0x57f5fff71d20c);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1cafa12,0x47ad71b73d6a2);
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f425,0x4b0e49a3b7d9f);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be84a,0x6664fbe0bf9d5);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d094,0x206b2c857eb86);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1cafa129,0x52dd302e14596);
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f4253,0x336910aac2051);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be84a7,0x37c19492ff0fd);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d094e,0x33f45d6c97d75);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1cafa129d,0x5dfefa9462cb3);
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f4253a,0x3147a3c99c3c);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be84a74,0x395bbb7e480be);
        exp_by_sq(0x6d1cafa129d0b,2,0x368e57d094e8,0x16fca513d7e13);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d1cafa129d0,0x553615ee67494);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0x368e57d094e85)),0x6d1cafa129d0b) != 0x6d1cafa129d0a) {
        exp_by_sq(0x6d1cafa129d0b,2,0xda395f4253a1,0x242c583969aab);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b472be84a742,0x2f143f8d4b441);
        assert false;
    }


        assert false;
    }

    q = 3;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x6d1cafa129d0b));

    if(euclid_mod(pow_nat(2,nat_of_int(0x917b)),0x6d1cafa129d0b) != 0x43b90d4942a06) {
        exp_by_sq(0x6d1cafa129d0b,2,0x0,0x1);
        exp_by_sq(0x6d1cafa129d0b,2,0x1,0x2);
        exp_by_sq(0x6d1cafa129d0b,2,0x2,0x4);
        exp_by_sq(0x6d1cafa129d0b,2,0x4,0x10);
        exp_by_sq(0x6d1cafa129d0b,2,0x9,0x200);
        exp_by_sq(0x6d1cafa129d0b,2,0x12,0x40000);
        exp_by_sq(0x6d1cafa129d0b,2,0x24,0x1000000000);
        exp_by_sq(0x6d1cafa129d0b,2,0x48,0x33adac13a3019);
        exp_by_sq(0x6d1cafa129d0b,2,0x91,0x51e0708cc2203);
        exp_by_sq(0x6d1cafa129d0b,2,0x122,0x5359eb013dc98);
        exp_by_sq(0x6d1cafa129d0b,2,0x245,0x1028eb68f2db4);
        exp_by_sq(0x6d1cafa129d0b,2,0x48b,0x188e93cec86ef);
        exp_by_sq(0x6d1cafa129d0b,2,0x917,0x50272828b112c);
        exp_by_sq(0x6d1cafa129d0b,2,0x122f,0x5d6bf9c5c8255);
        exp_by_sq(0x6d1cafa129d0b,2,0x245e,0x57289231447b9);
        exp_by_sq(0x6d1cafa129d0b,2,0x48bd,0x5f3794eb763ce);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0x917b94d6)),0x6d1cafa129d0b) != 0x448d361f09e8a) {
        exp_by_sq(0x6d1cafa129d0b,2,0x917b,0x43b90d4942a06);
        exp_by_sq(0x6d1cafa129d0b,2,0x122f7,0x36e029e623047);
        exp_by_sq(0x6d1cafa129d0b,2,0x245ee,0x1032d8741e04f);
        exp_by_sq(0x6d1cafa129d0b,2,0x48bdc,0x114c415c1a4f8);
        exp_by_sq(0x6d1cafa129d0b,2,0x917b9,0x11018aa3c5f7a);
        exp_by_sq(0x6d1cafa129d0b,2,0x122f72,0x533398c4b37bf);
        exp_by_sq(0x6d1cafa129d0b,2,0x245ee5,0x6a25eb496db28);
        exp_by_sq(0x6d1cafa129d0b,2,0x48bdca,0x361e55366874f);
        exp_by_sq(0x6d1cafa129d0b,2,0x917b94,0x961e38cc6509);
        exp_by_sq(0x6d1cafa129d0b,2,0x122f729,0x5e80f556b6e1);
        exp_by_sq(0x6d1cafa129d0b,2,0x245ee53,0x64a1085775064);
        exp_by_sq(0x6d1cafa129d0b,2,0x48bdca6,0x60359e5a6b9f4);
        exp_by_sq(0x6d1cafa129d0b,2,0x917b94d,0x248d6d2861ec2);
        exp_by_sq(0x6d1cafa129d0b,2,0x122f729a,0x4f7e57f585abb);
        exp_by_sq(0x6d1cafa129d0b,2,0x245ee535,0xe48602bc4980);
        exp_by_sq(0x6d1cafa129d0b,2,0x48bdca6b,0x13f33e4f0f48c);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0x917b94d6e26b)),0x6d1cafa129d0b) != 0x36f38bba57849) {
        exp_by_sq(0x6d1cafa129d0b,2,0x917b94d6,0x448d361f09e8a);
        exp_by_sq(0x6d1cafa129d0b,2,0x122f729ad,0x17b7601b7ce91);
        exp_by_sq(0x6d1cafa129d0b,2,0x245ee535b,0x2d7398cc83c64);
        exp_by_sq(0x6d1cafa129d0b,2,0x48bdca6b7,0x1c838e93278d4);
        exp_by_sq(0x6d1cafa129d0b,2,0x917b94d6e,0x23b2f52982671);
        exp_by_sq(0x6d1cafa129d0b,2,0x122f729adc,0x439b9e8919b28);
        exp_by_sq(0x6d1cafa129d0b,2,0x245ee535b8,0x188e4062a09f6);
        exp_by_sq(0x6d1cafa129d0b,2,0x48bdca6b71,0x33efc6e23f0d3);
        exp_by_sq(0x6d1cafa129d0b,2,0x917b94d6e2,0x2cdf720c6f011);
        exp_by_sq(0x6d1cafa129d0b,2,0x122f729adc4,0x61ee9c5a1892b);
        exp_by_sq(0x6d1cafa129d0b,2,0x245ee535b89,0x5056a874ab101);
        exp_by_sq(0x6d1cafa129d0b,2,0x48bdca6b713,0x6b17fadece1b3);
        exp_by_sq(0x6d1cafa129d0b,2,0x917b94d6e26,0x2e2e6305d634a);
        exp_by_sq(0x6d1cafa129d0b,2,0x122f729adc4d,0x4d951224f5a4);
        exp_by_sq(0x6d1cafa129d0b,2,0x245ee535b89a,0x6b070cc1d9af);
        exp_by_sq(0x6d1cafa129d0b,2,0x48bdca6b7135,0x525116210789e);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0x245ee535b89ae)),0x6d1cafa129d0b) != 0x6587710223b6c) {
        exp_by_sq(0x6d1cafa129d0b,2,0x917b94d6e26b,0x36f38bba57849);
        exp_by_sq(0x6d1cafa129d0b,2,0x122f729adc4d7,0x6587710223b6d);
        assert false;
    }


        assert false;
    }

    q = 7;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x6d1cafa129d0b));

    if(euclid_mod(pow_nat(2,nat_of_int(0xf966)),0x6d1cafa129d0b) != 0x5ad2abf7d965b) {
        exp_by_sq(0x6d1cafa129d0b,2,0x0,0x1);
        exp_by_sq(0x6d1cafa129d0b,2,0x1,0x2);
        exp_by_sq(0x6d1cafa129d0b,2,0x3,0x8);
        exp_by_sq(0x6d1cafa129d0b,2,0x7,0x80);
        exp_by_sq(0x6d1cafa129d0b,2,0xf,0x8000);
        exp_by_sq(0x6d1cafa129d0b,2,0x1f,0x80000000);
        exp_by_sq(0x6d1cafa129d0b,2,0x3e,0x38d819d5a7eca);
        exp_by_sq(0x6d1cafa129d0b,2,0x7c,0x614252c81935f);
        exp_by_sq(0x6d1cafa129d0b,2,0xf9,0x50fa065c28b4);
        exp_by_sq(0x6d1cafa129d0b,2,0x1f2,0x328fbc0f81066);
        exp_by_sq(0x6d1cafa129d0b,2,0x3e5,0x56d2efcdf52c5);
        exp_by_sq(0x6d1cafa129d0b,2,0x7cb,0x1c1daff148297);
        exp_by_sq(0x6d1cafa129d0b,2,0xf96,0x2379f65834469);
        exp_by_sq(0x6d1cafa129d0b,2,0x1f2c,0x669dd9b4741c3);
        exp_by_sq(0x6d1cafa129d0b,2,0x3e59,0x5fe572bfe89b2);
        exp_by_sq(0x6d1cafa129d0b,2,0x7cb3,0x1e175a57a8c44);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0xf96623b9)),0x6d1cafa129d0b) != 0x3bb2db9bc4a8e) {
        exp_by_sq(0x6d1cafa129d0b,2,0xf966,0x5ad2abf7d965b);
        exp_by_sq(0x6d1cafa129d0b,2,0x1f2cc,0x1fd3c5dc0311b);
        exp_by_sq(0x6d1cafa129d0b,2,0x3e598,0x658de3d0e90b5);
        exp_by_sq(0x6d1cafa129d0b,2,0x7cb31,0x33fd516ee1b24);
        exp_by_sq(0x6d1cafa129d0b,2,0xf9662,0x329109a1f052b);
        exp_by_sq(0x6d1cafa129d0b,2,0x1f2cc4,0x6a215a150a5ec);
        exp_by_sq(0x6d1cafa129d0b,2,0x3e5988,0x2436525804763);
        exp_by_sq(0x6d1cafa129d0b,2,0x7cb311,0x57cd479d92a11);
        exp_by_sq(0x6d1cafa129d0b,2,0xf96623,0x151dd380e56b6);
        exp_by_sq(0x6d1cafa129d0b,2,0x1f2cc47,0x4b72b2b625f3c);
        exp_by_sq(0x6d1cafa129d0b,2,0x3e5988e,0x41592a1fac14);
        exp_by_sq(0x6d1cafa129d0b,2,0x7cb311d,0x14d05b8e48275);
        exp_by_sq(0x6d1cafa129d0b,2,0xf96623b,0x4a8e7830a1edf);
        exp_by_sq(0x6d1cafa129d0b,2,0x1f2cc477,0xf36b6e8501d3);
        exp_by_sq(0x6d1cafa129d0b,2,0x3e5988ee,0x5249f6666a6f0);
        exp_by_sq(0x6d1cafa129d0b,2,0x7cb311dc,0x699de46ee946e);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0xf96623b98426)),0x6d1cafa129d0b) != 0x3feed21da4894) {
        exp_by_sq(0x6d1cafa129d0b,2,0xf96623b9,0x3bb2db9bc4a8e);
        exp_by_sq(0x6d1cafa129d0b,2,0x1f2cc4773,0x57057c978f9cf);
        exp_by_sq(0x6d1cafa129d0b,2,0x3e5988ee6,0x6826d42238ab2);
        exp_by_sq(0x6d1cafa129d0b,2,0x7cb311dcc,0x977c28d3022a);
        exp_by_sq(0x6d1cafa129d0b,2,0xf96623b98,0x61a4c6bbcbe23);
        exp_by_sq(0x6d1cafa129d0b,2,0x1f2cc47730,0x67807af010aa6);
        exp_by_sq(0x6d1cafa129d0b,2,0x3e5988ee61,0xd10368a05bda);
        exp_by_sq(0x6d1cafa129d0b,2,0x7cb311dcc2,0x604a314cb1663);
        exp_by_sq(0x6d1cafa129d0b,2,0xf96623b984,0xd731fdfe351f);
        exp_by_sq(0x6d1cafa129d0b,2,0x1f2cc477308,0x143fde21345c1);
        exp_by_sq(0x6d1cafa129d0b,2,0x3e5988ee610,0x30f38d1a6beb4);
        exp_by_sq(0x6d1cafa129d0b,2,0x7cb311dcc21,0x5e8877342fcfd);
        exp_by_sq(0x6d1cafa129d0b,2,0xf96623b9842,0x1507df96925f5);
        exp_by_sq(0x6d1cafa129d0b,2,0x1f2cc4773084,0x6a68fcc25e89a);
        exp_by_sq(0x6d1cafa129d0b,2,0x3e5988ee6109,0x63c16573ce6b6);
        exp_by_sq(0x6d1cafa129d0b,2,0x7cb311dcc213,0x503f42090cc9a);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0xf96623b98426)),0x6d1cafa129d0b) != 0x3feed21da4894) {
        assert false;
    }


        assert false;
    }

    q = 19;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x6d1cafa129d0b));

    if(euclid_mod(pow_nat(2,nat_of_int(0xb7c4)),0x6d1cafa129d0b) != 0x393a4f0fe208c) {
        exp_by_sq(0x6d1cafa129d0b,2,0x0,0x1);
        exp_by_sq(0x6d1cafa129d0b,2,0x1,0x2);
        exp_by_sq(0x6d1cafa129d0b,2,0x2,0x4);
        exp_by_sq(0x6d1cafa129d0b,2,0x5,0x20);
        exp_by_sq(0x6d1cafa129d0b,2,0xb,0x800);
        exp_by_sq(0x6d1cafa129d0b,2,0x16,0x400000);
        exp_by_sq(0x6d1cafa129d0b,2,0x2d,0x200000000000);
        exp_by_sq(0x6d1cafa129d0b,2,0x5b,0x63972e206c62c);
        exp_by_sq(0x6d1cafa129d0b,2,0xb7,0x29dcfca31d8fa);
        exp_by_sq(0x6d1cafa129d0b,2,0x16f,0x62053b0a0729c);
        exp_by_sq(0x6d1cafa129d0b,2,0x2df,0x1ee596da204b7);
        exp_by_sq(0x6d1cafa129d0b,2,0x5be,0x1ce4cfa771347);
        exp_by_sq(0x6d1cafa129d0b,2,0xb7c,0x294cba4b23394);
        exp_by_sq(0x6d1cafa129d0b,2,0x16f8,0x693e981a8a105);
        exp_by_sq(0x6d1cafa129d0b,2,0x2df1,0x4afdd215530b8);
        exp_by_sq(0x6d1cafa129d0b,2,0x5be2,0x387258271e5e2);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0xb7c4861c)),0x6d1cafa129d0b) != 0xdf3c573092b7) {
        exp_by_sq(0x6d1cafa129d0b,2,0xb7c4,0x393a4f0fe208c);
        exp_by_sq(0x6d1cafa129d0b,2,0x16f89,0x12872bd8a27a0);
        exp_by_sq(0x6d1cafa129d0b,2,0x2df12,0x54c2299cc2477);
        exp_by_sq(0x6d1cafa129d0b,2,0x5be24,0x46c73e90a4aad);
        exp_by_sq(0x6d1cafa129d0b,2,0xb7c48,0x387a6cc328ec8);
        exp_by_sq(0x6d1cafa129d0b,2,0x16f890,0x5b7862d530345);
        exp_by_sq(0x6d1cafa129d0b,2,0x2df121,0x3b99b56989fad);
        exp_by_sq(0x6d1cafa129d0b,2,0x5be243,0x2ed90fbf69476);
        exp_by_sq(0x6d1cafa129d0b,2,0xb7c486,0x45bf9f99b71b6);
        exp_by_sq(0x6d1cafa129d0b,2,0x16f890c,0x3e4c12996200e);
        exp_by_sq(0x6d1cafa129d0b,2,0x2df1218,0x4c75c450073d);
        exp_by_sq(0x6d1cafa129d0b,2,0x5be2430,0x4ceb2513265e0);
        exp_by_sq(0x6d1cafa129d0b,2,0xb7c4861,0x644ed3a3b411f);
        exp_by_sq(0x6d1cafa129d0b,2,0x16f890c3,0x326e80fd35394);
        exp_by_sq(0x6d1cafa129d0b,2,0x2df12187,0x4f765812dc3ee);
        exp_by_sq(0x6d1cafa129d0b,2,0x5be2430e,0x27c830e3ab11c);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0x5be2430e740e)),0x6d1cafa129d0b) != 0x223c41686965d) {
        exp_by_sq(0x6d1cafa129d0b,2,0xb7c4861c,0xdf3c573092b7);
        exp_by_sq(0x6d1cafa129d0b,2,0x16f890c39,0x6c6af3b1a9f82);
        exp_by_sq(0x6d1cafa129d0b,2,0x2df121873,0x3461edb22eb87);
        exp_by_sq(0x6d1cafa129d0b,2,0x5be2430e7,0x226291f012169);
        exp_by_sq(0x6d1cafa129d0b,2,0xb7c4861ce,0x76838b55cc00);
        exp_by_sq(0x6d1cafa129d0b,2,0x16f890c39d,0x4b9b226d4bff0);
        exp_by_sq(0x6d1cafa129d0b,2,0x2df121873a,0x3cf9b989fea15);
        exp_by_sq(0x6d1cafa129d0b,2,0x5be2430e74,0x22a71a67181d4);
        exp_by_sq(0x6d1cafa129d0b,2,0xb7c4861ce8,0x6b13a850fe70a);
        exp_by_sq(0x6d1cafa129d0b,2,0x16f890c39d0,0x329f408a483ea);
        exp_by_sq(0x6d1cafa129d0b,2,0x2df121873a0,0xdf36c8f2b6a2);
        exp_by_sq(0x6d1cafa129d0b,2,0x5be2430e740,0x44edd2f4f1bb5);
        exp_by_sq(0x6d1cafa129d0b,2,0xb7c4861ce81,0x45e7f7bdfa79a);
        exp_by_sq(0x6d1cafa129d0b,2,0x16f890c39d03,0x6cdec1707dd8d);
        exp_by_sq(0x6d1cafa129d0b,2,0x2df121873a07,0x6334c0dbe3037);
        assert false;
    }


        assert false;
    }

    q = 47;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x6d1cafa129d0b));

    if(euclid_mod(pow_nat(2,nat_of_int(0x9493)),0x6d1cafa129d0b) != 0x83e2c8d3db86) {
        exp_by_sq(0x6d1cafa129d0b,2,0x0,0x1);
        exp_by_sq(0x6d1cafa129d0b,2,0x1,0x2);
        exp_by_sq(0x6d1cafa129d0b,2,0x2,0x4);
        exp_by_sq(0x6d1cafa129d0b,2,0x4,0x10);
        exp_by_sq(0x6d1cafa129d0b,2,0x9,0x200);
        exp_by_sq(0x6d1cafa129d0b,2,0x12,0x40000);
        exp_by_sq(0x6d1cafa129d0b,2,0x25,0x2000000000);
        exp_by_sq(0x6d1cafa129d0b,2,0x4a,0x619a00ad62359);
        exp_by_sq(0x6d1cafa129d0b,2,0x94,0x57669f161d6);
        exp_by_sq(0x6d1cafa129d0b,2,0x129,0x5516f48e0cad5);
        exp_by_sq(0x6d1cafa129d0b,2,0x252,0x1c80efb8462e1);
        exp_by_sq(0x6d1cafa129d0b,2,0x4a4,0x6b9f8b2a14be8);
        exp_by_sq(0x6d1cafa129d0b,2,0x949,0x55ee5fee0b0d9);
        exp_by_sq(0x6d1cafa129d0b,2,0x1292,0x203a61e39e8b9);
        exp_by_sq(0x6d1cafa129d0b,2,0x2524,0x35b60090d79c1);
        exp_by_sq(0x6d1cafa129d0b,2,0x4a49,0x4376230fa3faa);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0x9493ff7e)),0x6d1cafa129d0b) != 0x32ca1e0f55904) {
        exp_by_sq(0x6d1cafa129d0b,2,0x9493,0x83e2c8d3db86);
        exp_by_sq(0x6d1cafa129d0b,2,0x12927,0x7022de25367a);
        exp_by_sq(0x6d1cafa129d0b,2,0x2524f,0x5571fb39aef6c);
        exp_by_sq(0x6d1cafa129d0b,2,0x4a49f,0x16d3ac4ead37a);
        exp_by_sq(0x6d1cafa129d0b,2,0x9493f,0x1933b84bd6cb0);
        exp_by_sq(0x6d1cafa129d0b,2,0x12927f,0x467c7a0822deb);
        exp_by_sq(0x6d1cafa129d0b,2,0x2524ff,0x10b27cfc255c5);
        exp_by_sq(0x6d1cafa129d0b,2,0x4a49ff,0x385eaa44e664c);
        exp_by_sq(0x6d1cafa129d0b,2,0x9493ff,0x1234c532d98f6);
        exp_by_sq(0x6d1cafa129d0b,2,0x12927fe,0x13909b8825c30);
        exp_by_sq(0x6d1cafa129d0b,2,0x2524ffd,0x27f14d10b42fe);
        exp_by_sq(0x6d1cafa129d0b,2,0x4a49ffb,0x362162d45395d);
        exp_by_sq(0x6d1cafa129d0b,2,0x9493ff7,0x602cef6b71c9c);
        exp_by_sq(0x6d1cafa129d0b,2,0x12927fef,0x279dae8d288f8);
        exp_by_sq(0x6d1cafa129d0b,2,0x2524ffdf,0x1aedaef88bc7e);
        exp_by_sq(0x6d1cafa129d0b,2,0x4a49ffbf,0x23da1d82e5a5a);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0x2524ffdfb716)),0x6d1cafa129d0b) != 0x235a4cf8e39bf) {
        exp_by_sq(0x6d1cafa129d0b,2,0x9493ff7e,0x32ca1e0f55904);
        exp_by_sq(0x6d1cafa129d0b,2,0x12927fefd,0x2ec9eec349754);
        exp_by_sq(0x6d1cafa129d0b,2,0x2524ffdfb,0x3a07884ecc2cd);
        exp_by_sq(0x6d1cafa129d0b,2,0x4a49ffbf6,0x6941187a1aa28);
        exp_by_sq(0x6d1cafa129d0b,2,0x9493ff7ed,0x5e679bf755db2);
        exp_by_sq(0x6d1cafa129d0b,2,0x12927fefdb,0x479d33ce4892f);
        exp_by_sq(0x6d1cafa129d0b,2,0x2524ffdfb7,0xd53612d7f067);
        exp_by_sq(0x6d1cafa129d0b,2,0x4a49ffbf6e,0x4163c3dd39051);
        exp_by_sq(0x6d1cafa129d0b,2,0x9493ff7edc,0x61321be16acd);
        exp_by_sq(0x6d1cafa129d0b,2,0x12927fefdb8,0x53d4991198a57);
        exp_by_sq(0x6d1cafa129d0b,2,0x2524ffdfb71,0x6ca9bd9a93f28);
        exp_by_sq(0x6d1cafa129d0b,2,0x4a49ffbf6e2,0x1b06b13eb49b5);
        exp_by_sq(0x6d1cafa129d0b,2,0x9493ff7edc5,0x47451dc847a27);
        exp_by_sq(0x6d1cafa129d0b,2,0x12927fefdb8b,0x551bba3a170d1);
        assert false;
    }


        assert false;
    }

    q = 127;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x6d1cafa129d0b));

    if(euclid_mod(pow_nat(2,nat_of_int(0xdbf1)),0x6d1cafa129d0b) != 0x67ae1e5b38fae) {
        exp_by_sq(0x6d1cafa129d0b,2,0x0,0x1);
        exp_by_sq(0x6d1cafa129d0b,2,0x1,0x2);
        exp_by_sq(0x6d1cafa129d0b,2,0x3,0x8);
        exp_by_sq(0x6d1cafa129d0b,2,0x6,0x40);
        exp_by_sq(0x6d1cafa129d0b,2,0xd,0x2000);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b,0x8000000);
        exp_by_sq(0x6d1cafa129d0b,2,0x36,0x29fdd35587a9d);
        exp_by_sq(0x6d1cafa129d0b,2,0x6d,0x295b2fbcd42f4);
        exp_by_sq(0x6d1cafa129d0b,2,0xdb,0x5510261ab1b23);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b7,0x5c877d3f19023);
        exp_by_sq(0x6d1cafa129d0b,2,0x36f,0x1af21dd8ab605);
        exp_by_sq(0x6d1cafa129d0b,2,0x6df,0x5a8507b4c1b84);
        exp_by_sq(0x6d1cafa129d0b,2,0xdbf,0x4b180bcec765f);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b7e,0x118c2f68357fd);
        exp_by_sq(0x6d1cafa129d0b,2,0x36fc,0x50e1fbe5692bc);
        exp_by_sq(0x6d1cafa129d0b,2,0x6df8,0x15cd3a87c646);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0xdbf141c5)),0x6d1cafa129d0b) != 0x20534fa8fd523) {
        exp_by_sq(0x6d1cafa129d0b,2,0xdbf1,0x67ae1e5b38fae);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b7e2,0x162383d01442e);
        exp_by_sq(0x6d1cafa129d0b,2,0x36fc5,0x177c607aff2e0);
        exp_by_sq(0x6d1cafa129d0b,2,0x6df8a,0x4fe9e97d95740);
        exp_by_sq(0x6d1cafa129d0b,2,0xdbf14,0x20b1710b225fe);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b7e28,0x3b230b07283d0);
        exp_by_sq(0x6d1cafa129d0b,2,0x36fc50,0x62ef0d703638a);
        exp_by_sq(0x6d1cafa129d0b,2,0x6df8a0,0x314767575867f);
        exp_by_sq(0x6d1cafa129d0b,2,0xdbf141,0x4f9080dd9d27d);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b7e283,0x4a785ab37a75);
        exp_by_sq(0x6d1cafa129d0b,2,0x36fc507,0x3d6aa47c25ab6);
        exp_by_sq(0x6d1cafa129d0b,2,0x6df8a0e,0x37f19dfcd00b5);
        exp_by_sq(0x6d1cafa129d0b,2,0xdbf141c,0x415981a1234ad);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b7e2838,0x13cb87645d882);
        exp_by_sq(0x6d1cafa129d0b,2,0x36fc5071,0x6aae77eb2abde);
        exp_by_sq(0x6d1cafa129d0b,2,0x6df8a0e2,0x257a4a6514457);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0xdbf141c5df6)),0x6d1cafa129d0b) != 0x20c92d89f364e) {
        exp_by_sq(0x6d1cafa129d0b,2,0xdbf141c5,0x20534fa8fd523);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b7e2838b,0x21fc8e813bad6);
        exp_by_sq(0x6d1cafa129d0b,2,0x36fc50717,0x278626bc78e17);
        exp_by_sq(0x6d1cafa129d0b,2,0x6df8a0e2e,0x593346d482ef9);
        exp_by_sq(0x6d1cafa129d0b,2,0xdbf141c5d,0x4b163bc24ea95);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b7e2838bb,0x3655d6bd349a);
        exp_by_sq(0x6d1cafa129d0b,2,0x36fc507177,0x46175c0f44f9b);
        exp_by_sq(0x6d1cafa129d0b,2,0x6df8a0e2ef,0x119024765a96e);
        exp_by_sq(0x6d1cafa129d0b,2,0xdbf141c5df,0x6027da76fb833);
        exp_by_sq(0x6d1cafa129d0b,2,0x1b7e2838bbe,0x4ad3eec75f58f);
        exp_by_sq(0x6d1cafa129d0b,2,0x36fc507177d,0x3ccf22a0ca59);
        exp_by_sq(0x6d1cafa129d0b,2,0x6df8a0e2efb,0x616e4e2d8dc92);
        assert false;
    }


        assert false;
    }

    q = 8574133;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x6d1cafa129d0b));

    if(euclid_mod(pow_nat(2,nat_of_int(0xd580)),0x6d1cafa129d0b) != 0x4eb4d9d00b27c) {
        exp_by_sq(0x6d1cafa129d0b,2,0x0,0x1);
        exp_by_sq(0x6d1cafa129d0b,2,0x1,0x2);
        exp_by_sq(0x6d1cafa129d0b,2,0x3,0x8);
        exp_by_sq(0x6d1cafa129d0b,2,0x6,0x40);
        exp_by_sq(0x6d1cafa129d0b,2,0xd,0x2000);
        exp_by_sq(0x6d1cafa129d0b,2,0x1a,0x4000000);
        exp_by_sq(0x6d1cafa129d0b,2,0x35,0x4b8d417b58bd4);
        exp_by_sq(0x6d1cafa129d0b,2,0x6a,0x3bb9bdc82f6e4);
        exp_by_sq(0x6d1cafa129d0b,2,0xd5,0x5f18e786eab62);
        exp_by_sq(0x6d1cafa129d0b,2,0x1ab,0x34a24d67198b2);
        exp_by_sq(0x6d1cafa129d0b,2,0x356,0x404d9a606b02c);
        exp_by_sq(0x6d1cafa129d0b,2,0x6ac,0x6a2603b88121b);
        exp_by_sq(0x6d1cafa129d0b,2,0xd58,0x19004c5c350df);
        exp_by_sq(0x6d1cafa129d0b,2,0x1ab0,0x42d8f2a2ec64a);
        exp_by_sq(0x6d1cafa129d0b,2,0x3560,0x508eccc5fc7a7);
        exp_by_sq(0x6d1cafa129d0b,2,0x6ac0,0xd194095d85ca);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0xd580922)),0x6d1cafa129d0b) != 0x3c3ffdef7c0b1) {
        exp_by_sq(0x6d1cafa129d0b,2,0xd580,0x4eb4d9d00b27c);
        exp_by_sq(0x6d1cafa129d0b,2,0x1ab01,0x28416ba0b6a57);
        exp_by_sq(0x6d1cafa129d0b,2,0x35602,0x2eb989126ce8e);
        exp_by_sq(0x6d1cafa129d0b,2,0x6ac04,0x5772cd6bce94b);
        exp_by_sq(0x6d1cafa129d0b,2,0xd5809,0x5d322c8ac0852);
        exp_by_sq(0x6d1cafa129d0b,2,0x1ab012,0x4e0d9428f0339);
        exp_by_sq(0x6d1cafa129d0b,2,0x356024,0xfeb816ba61af);
        exp_by_sq(0x6d1cafa129d0b,2,0x6ac049,0x4c0d7a2b0b64b);
        exp_by_sq(0x6d1cafa129d0b,2,0xd58092,0x259cb28ce652d);
        exp_by_sq(0x6d1cafa129d0b,2,0x1ab0124,0x38f03576a55f7);
        exp_by_sq(0x6d1cafa129d0b,2,0x3560248,0x675002e71f67f);
        exp_by_sq(0x6d1cafa129d0b,2,0x6ac0491,0x14b705744ee84);
        assert false;
    }


        assert false;
    }


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
    note_eq(1,euclid_mod(pow_nat(7,nat_of_int(0)),0x10c9df5fc7));

    if(euclid_mod(pow_nat(7,nat_of_int(0x864e)),0x10c9df5fc7) != 0xea0ff2cc4) {
        exp_by_sq(0x10c9df5fc7,7,0x0,0x1);
        exp_by_sq(0x10c9df5fc7,7,0x1,0x7);
        exp_by_sq(0x10c9df5fc7,7,0x2,0x31);
        exp_by_sq(0x10c9df5fc7,7,0x4,0x961);
        exp_by_sq(0x10c9df5fc7,7,0x8,0x57f6c1);
        exp_by_sq(0x10c9df5fc7,7,0x10,0xee7a563ed);
        exp_by_sq(0x10c9df5fc7,7,0x21,0x25da47ac6);
        exp_by_sq(0x10c9df5fc7,7,0x43,0xd50535984);
        exp_by_sq(0x10c9df5fc7,7,0x86,0xed0f0a1b4);
        exp_by_sq(0x10c9df5fc7,7,0x10c,0x10a0b330c0);
        exp_by_sq(0x10c9df5fc7,7,0x219,0xf6773204c);
        exp_by_sq(0x10c9df5fc7,7,0x432,0x87c31f0d3);
        exp_by_sq(0x10c9df5fc7,7,0x864,0x6dc1a88c9);
        exp_by_sq(0x10c9df5fc7,7,0x10c9,0x27858256a);
        exp_by_sq(0x10c9df5fc7,7,0x2193,0xdaa81eca3);
        exp_by_sq(0x10c9df5fc7,7,0x4327,0x963d270c8);
        assert false;
    }

    if(euclid_mod(pow_nat(7,nat_of_int(0x864efafe)),0x10c9df5fc7) != 0x1ff0be179) {
        exp_by_sq(0x10c9df5fc7,7,0x864e,0xea0ff2cc4);
        exp_by_sq(0x10c9df5fc7,7,0x10c9d,0xc6ce71a05);
        exp_by_sq(0x10c9df5fc7,7,0x2193b,0x1c5025426);
        exp_by_sq(0x10c9df5fc7,7,0x43277,0x412c3a20d);
        exp_by_sq(0x10c9df5fc7,7,0x864ef,0x2d90e6cc3);
        exp_by_sq(0x10c9df5fc7,7,0x10c9df,0xa7e221ac2);
        exp_by_sq(0x10c9df5fc7,7,0x2193be,0x274491e22);
        exp_by_sq(0x10c9df5fc7,7,0x43277d,0x10b4d08f8);
        exp_by_sq(0x10c9df5fc7,7,0x864efa,0xf47b17528);
        exp_by_sq(0x10c9df5fc7,7,0x10c9df5,0xaf0e48f31);
        exp_by_sq(0x10c9df5fc7,7,0x2193beb,0xdb32ac9ca);
        exp_by_sq(0x10c9df5fc7,7,0x43277d7,0x1079849a80);
        exp_by_sq(0x10c9df5fc7,7,0x864efaf,0x995aa8459);
        exp_by_sq(0x10c9df5fc7,7,0x10c9df5f,0xf68bc3f9f);
        exp_by_sq(0x10c9df5fc7,7,0x2193bebf,0x7a09125be);
        exp_by_sq(0x10c9df5fc7,7,0x43277d7f,0x84dd51e8b);
        assert false;
    }

    if(euclid_mod(pow_nat(7,nat_of_int(0x10c9df5fc6)),0x10c9df5fc7) != 0x1) {
        exp_by_sq(0x10c9df5fc7,7,0x864efafe,0x1ff0be179);
        exp_by_sq(0x10c9df5fc7,7,0x10c9df5fc,0x574eec936);
        exp_by_sq(0x10c9df5fc7,7,0x2193bebf8,0x49ad973c2);
        exp_by_sq(0x10c9df5fc7,7,0x43277d7f1,0xf1ecea7e);
        exp_by_sq(0x10c9df5fc7,7,0x864efafe3,0x10c9df5fc6);
        assert false;
    }


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
    ALREADY_PROVEN()
    int g = 7; int p = 72106336199; int q;
    q = 2;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(7,nat_of_int(0)),0x10c9df5fc7));

    if(euclid_mod(pow_nat(7,nat_of_int(0x864e)),0x10c9df5fc7) != 0xea0ff2cc4) {
        exp_by_sq(0x10c9df5fc7,7,0x0,0x1);
        exp_by_sq(0x10c9df5fc7,7,0x1,0x7);
        exp_by_sq(0x10c9df5fc7,7,0x2,0x31);
        exp_by_sq(0x10c9df5fc7,7,0x4,0x961);
        exp_by_sq(0x10c9df5fc7,7,0x8,0x57f6c1);
        exp_by_sq(0x10c9df5fc7,7,0x10,0xee7a563ed);
        exp_by_sq(0x10c9df5fc7,7,0x21,0x25da47ac6);
        exp_by_sq(0x10c9df5fc7,7,0x43,0xd50535984);
        exp_by_sq(0x10c9df5fc7,7,0x86,0xed0f0a1b4);
        exp_by_sq(0x10c9df5fc7,7,0x10c,0x10a0b330c0);
        exp_by_sq(0x10c9df5fc7,7,0x219,0xf6773204c);
        exp_by_sq(0x10c9df5fc7,7,0x432,0x87c31f0d3);
        exp_by_sq(0x10c9df5fc7,7,0x864,0x6dc1a88c9);
        exp_by_sq(0x10c9df5fc7,7,0x10c9,0x27858256a);
        exp_by_sq(0x10c9df5fc7,7,0x2193,0xdaa81eca3);
        exp_by_sq(0x10c9df5fc7,7,0x4327,0x963d270c8);
        assert false;
    }

    if(euclid_mod(pow_nat(7,nat_of_int(0x864efafe)),0x10c9df5fc7) != 0x1ff0be179) {
        exp_by_sq(0x10c9df5fc7,7,0x864e,0xea0ff2cc4);
        exp_by_sq(0x10c9df5fc7,7,0x10c9d,0xc6ce71a05);
        exp_by_sq(0x10c9df5fc7,7,0x2193b,0x1c5025426);
        exp_by_sq(0x10c9df5fc7,7,0x43277,0x412c3a20d);
        exp_by_sq(0x10c9df5fc7,7,0x864ef,0x2d90e6cc3);
        exp_by_sq(0x10c9df5fc7,7,0x10c9df,0xa7e221ac2);
        exp_by_sq(0x10c9df5fc7,7,0x2193be,0x274491e22);
        exp_by_sq(0x10c9df5fc7,7,0x43277d,0x10b4d08f8);
        exp_by_sq(0x10c9df5fc7,7,0x864efa,0xf47b17528);
        exp_by_sq(0x10c9df5fc7,7,0x10c9df5,0xaf0e48f31);
        exp_by_sq(0x10c9df5fc7,7,0x2193beb,0xdb32ac9ca);
        exp_by_sq(0x10c9df5fc7,7,0x43277d7,0x1079849a80);
        exp_by_sq(0x10c9df5fc7,7,0x864efaf,0x995aa8459);
        exp_by_sq(0x10c9df5fc7,7,0x10c9df5f,0xf68bc3f9f);
        exp_by_sq(0x10c9df5fc7,7,0x2193bebf,0x7a09125be);
        exp_by_sq(0x10c9df5fc7,7,0x43277d7f,0x84dd51e8b);
        assert false;
    }

    if(euclid_mod(pow_nat(7,nat_of_int(0x864efafe3)),0x10c9df5fc7) != 0x10c9df5fc6) {
        exp_by_sq(0x10c9df5fc7,7,0x864efafe,0x1ff0be179);
        exp_by_sq(0x10c9df5fc7,7,0x10c9df5fc,0x574eec936);
        exp_by_sq(0x10c9df5fc7,7,0x2193bebf8,0x49ad973c2);
        exp_by_sq(0x10c9df5fc7,7,0x43277d7f1,0xf1ecea7e);
        assert false;
    }


        assert false;
    }

    q = 13;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(7,nat_of_int(0)),0x10c9df5fc7));

    if(euclid_mod(pow_nat(7,nat_of_int(0xa54d)),0x10c9df5fc7) != 0xb052ff5a2) {
        exp_by_sq(0x10c9df5fc7,7,0x0,0x1);
        exp_by_sq(0x10c9df5fc7,7,0x1,0x7);
        exp_by_sq(0x10c9df5fc7,7,0x2,0x31);
        exp_by_sq(0x10c9df5fc7,7,0x5,0x41a7);
        exp_by_sq(0x10c9df5fc7,7,0xa,0x10d63af1);
        exp_by_sq(0x10c9df5fc7,7,0x14,0xa27c3ec48);
        exp_by_sq(0x10c9df5fc7,7,0x29,0x658f27fa3);
        exp_by_sq(0x10c9df5fc7,7,0x52,0xfbc71b4d2);
        exp_by_sq(0x10c9df5fc7,7,0xa5,0x15465d2ab);
        exp_by_sq(0x10c9df5fc7,7,0x14a,0x2c72effcf);
        exp_by_sq(0x10c9df5fc7,7,0x295,0x85a9b4e1c);
        exp_by_sq(0x10c9df5fc7,7,0x52a,0x3edeb46f9);
        exp_by_sq(0x10c9df5fc7,7,0xa54,0x87140110d);
        exp_by_sq(0x10c9df5fc7,7,0x14a9,0xc5f831fa1);
        exp_by_sq(0x10c9df5fc7,7,0x2953,0x1a54e1b3e);
        exp_by_sq(0x10c9df5fc7,7,0x52a6,0x41174e886);
        assert false;
    }

    if(euclid_mod(pow_nat(7,nat_of_int(0xa54d83af)),0x10c9df5fc7) != 0x9a404bb56) {
        exp_by_sq(0x10c9df5fc7,7,0xa54d,0xb052ff5a2);
        exp_by_sq(0x10c9df5fc7,7,0x14a9b,0xe7bbb35fb);
        exp_by_sq(0x10c9df5fc7,7,0x29536,0xc6d5144ca);
        exp_by_sq(0x10c9df5fc7,7,0x52a6c,0x5419b2112);
        exp_by_sq(0x10c9df5fc7,7,0xa54d8,0x9fab0e4a);
        exp_by_sq(0x10c9df5fc7,7,0x14a9b0,0x77ba9b1e);
        exp_by_sq(0x10c9df5fc7,7,0x295360,0x4a0e86216);
        exp_by_sq(0x10c9df5fc7,7,0x52a6c1,0x23de57aad);
        exp_by_sq(0x10c9df5fc7,7,0xa54d83,0x65d32c2f8);
        exp_by_sq(0x10c9df5fc7,7,0x14a9b07,0xa68b5b97b);
        exp_by_sq(0x10c9df5fc7,7,0x295360e,0xec467f701);
        exp_by_sq(0x10c9df5fc7,7,0x52a6c1d,0x85d1d2358);
        exp_by_sq(0x10c9df5fc7,7,0xa54d83a,0x6359918bf);
        exp_by_sq(0x10c9df5fc7,7,0x14a9b075,0x575aea6d9);
        exp_by_sq(0x10c9df5fc7,7,0x295360eb,0x5fb46eb9d);
        exp_by_sq(0x10c9df5fc7,7,0x52a6c1d7,0xca79b15e0);
        assert false;
    }

    if(euclid_mod(pow_nat(7,nat_of_int(0x14a9b075e)),0x10c9df5fc7) != 0xdaad68deb) {
        exp_by_sq(0x10c9df5fc7,7,0xa54d83af,0x9a404bb56);
        assert false;
    }


        assert false;
    }

    q = 2773320623;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(7,nat_of_int(0)),0x10c9df5fc7));

    if(euclid_mod(pow_nat(7,nat_of_int(0x1a)),0x10c9df5fc7) != 0x69a39f21d) {
        exp_by_sq(0x10c9df5fc7,7,0x0,0x1);
        exp_by_sq(0x10c9df5fc7,7,0x1,0x7);
        exp_by_sq(0x10c9df5fc7,7,0x3,0x157);
        exp_by_sq(0x10c9df5fc7,7,0x6,0x1cb91);
        exp_by_sq(0x10c9df5fc7,7,0xd,0x5c5299920);
        assert false;
    }


        assert false;
    }


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

    note_eq(1,euclid_mod(pow_nat(10,nat_of_int(0)),0xa54d83af));

    if(euclid_mod(pow_nat(10,nat_of_int(0xa54d)),0xa54d83af) != 0x5be31f7e) {
        exp_by_sq(0xa54d83af,10,0x0,0x1);
        exp_by_sq(0xa54d83af,10,0x1,0xa);
        exp_by_sq(0xa54d83af,10,0x2,0x64);
        exp_by_sq(0xa54d83af,10,0x5,0x186a0);
        exp_by_sq(0xa54d83af,10,0xa,0x642358f3);
        exp_by_sq(0xa54d83af,10,0x14,0x7db33e3a);
        exp_by_sq(0xa54d83af,10,0x29,0x2fcf8212);
        exp_by_sq(0xa54d83af,10,0x52,0x763f181f);
        exp_by_sq(0xa54d83af,10,0xa5,0x8807f85c);
        exp_by_sq(0xa54d83af,10,0x14a,0x475f59ec);
        exp_by_sq(0xa54d83af,10,0x295,0xa4a5bbd);
        exp_by_sq(0xa54d83af,10,0x52a,0x27380187);
        exp_by_sq(0xa54d83af,10,0xa54,0x9e4d2329);
        exp_by_sq(0xa54d83af,10,0x14a9,0x50242a5a);
        exp_by_sq(0xa54d83af,10,0x2953,0x4092fc54);
        exp_by_sq(0xa54d83af,10,0x52a6,0x53f2a6ea);
        assert false;
    }

    if(euclid_mod(pow_nat(10,nat_of_int(0xa54d83ae)),0xa54d83af) != 0x1) {
        exp_by_sq(0xa54d83af,10,0xa54d,0x5be31f7e);
        exp_by_sq(0xa54d83af,10,0x14a9b,0x81d6ece5);
        exp_by_sq(0xa54d83af,10,0x29536,0x102c82e6);
        exp_by_sq(0xa54d83af,10,0x52a6c,0x10b09e98);
        exp_by_sq(0xa54d83af,10,0xa54d8,0x7e05e442);
        exp_by_sq(0xa54d83af,10,0x14a9b0,0x8fff89d4);
        exp_by_sq(0xa54d83af,10,0x295360,0x93269b67);
        exp_by_sq(0xa54d83af,10,0x52a6c1,0x5930d3c8);
        exp_by_sq(0xa54d83af,10,0xa54d83,0x11b7562d);
        exp_by_sq(0xa54d83af,10,0x14a9b07,0x3396a62c);
        exp_by_sq(0xa54d83af,10,0x295360e,0x76bf307d);
        exp_by_sq(0xa54d83af,10,0x52a6c1d,0x931fd36b);
        exp_by_sq(0xa54d83af,10,0xa54d83a,0x90b65c03);
        exp_by_sq(0xa54d83af,10,0x14a9b075,0x706c75a2);
        exp_by_sq(0xa54d83af,10,0x295360eb,0x24c40ad6);
        exp_by_sq(0xa54d83af,10,0x52a6c1d7,0xa54d83ae);
        assert false;
    }

    if(euclid_mod(pow_nat(10,nat_of_int(0xa54d83ae)),0xa54d83af) != 0x1) {
        assert false;
    }

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
    ALREADY_PROVEN()

    int g = 10; int p = 2773320623; int q;
    q = 2;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(10,nat_of_int(0)),0xa54d83af));

    if(euclid_mod(pow_nat(10,nat_of_int(0xa54d)),0xa54d83af) != 0x5be31f7e) {
        exp_by_sq(0xa54d83af,10,0x0,0x1);
        exp_by_sq(0xa54d83af,10,0x1,0xa);
        exp_by_sq(0xa54d83af,10,0x2,0x64);
        exp_by_sq(0xa54d83af,10,0x5,0x186a0);
        exp_by_sq(0xa54d83af,10,0xa,0x642358f3);
        exp_by_sq(0xa54d83af,10,0x14,0x7db33e3a);
        exp_by_sq(0xa54d83af,10,0x29,0x2fcf8212);
        exp_by_sq(0xa54d83af,10,0x52,0x763f181f);
        exp_by_sq(0xa54d83af,10,0xa5,0x8807f85c);
        exp_by_sq(0xa54d83af,10,0x14a,0x475f59ec);
        exp_by_sq(0xa54d83af,10,0x295,0xa4a5bbd);
        exp_by_sq(0xa54d83af,10,0x52a,0x27380187);
        exp_by_sq(0xa54d83af,10,0xa54,0x9e4d2329);
        exp_by_sq(0xa54d83af,10,0x14a9,0x50242a5a);
        exp_by_sq(0xa54d83af,10,0x2953,0x4092fc54);
        exp_by_sq(0xa54d83af,10,0x52a6,0x53f2a6ea);
        assert false;
    }

    if(euclid_mod(pow_nat(10,nat_of_int(0x52a6c1d7)),0xa54d83af) != 0xa54d83ae) {
        exp_by_sq(0xa54d83af,10,0xa54d,0x5be31f7e);
        exp_by_sq(0xa54d83af,10,0x14a9b,0x81d6ece5);
        exp_by_sq(0xa54d83af,10,0x29536,0x102c82e6);
        exp_by_sq(0xa54d83af,10,0x52a6c,0x10b09e98);
        exp_by_sq(0xa54d83af,10,0xa54d8,0x7e05e442);
        exp_by_sq(0xa54d83af,10,0x14a9b0,0x8fff89d4);
        exp_by_sq(0xa54d83af,10,0x295360,0x93269b67);
        exp_by_sq(0xa54d83af,10,0x52a6c1,0x5930d3c8);
        exp_by_sq(0xa54d83af,10,0xa54d83,0x11b7562d);
        exp_by_sq(0xa54d83af,10,0x14a9b07,0x3396a62c);
        exp_by_sq(0xa54d83af,10,0x295360e,0x76bf307d);
        exp_by_sq(0xa54d83af,10,0x52a6c1d,0x931fd36b);
        exp_by_sq(0xa54d83af,10,0xa54d83a,0x90b65c03);
        exp_by_sq(0xa54d83af,10,0x14a9b075,0x706c75a2);
        exp_by_sq(0xa54d83af,10,0x295360eb,0x24c40ad6);
        assert false;
    }


        assert false;
    }

    q = 2437;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(10,nat_of_int(0)),0xa54d83af));

    if(euclid_mod(pow_nat(10,nat_of_int(0x8aea)),0xa54d83af) != 0x3e61c74b) {
        exp_by_sq(0xa54d83af,10,0x0,0x1);
        exp_by_sq(0xa54d83af,10,0x1,0xa);
        exp_by_sq(0xa54d83af,10,0x2,0x64);
        exp_by_sq(0xa54d83af,10,0x4,0x2710);
        exp_by_sq(0xa54d83af,10,0x8,0x5f5e100);
        exp_by_sq(0xa54d83af,10,0x11,0x5d069f51);
        exp_by_sq(0xa54d83af,10,0x22,0x8b2e9cad);
        exp_by_sq(0xa54d83af,10,0x45,0x4fd2e6bb);
        exp_by_sq(0xa54d83af,10,0x8a,0x4d371c36);
        exp_by_sq(0xa54d83af,10,0x115,0x52ba989f);
        exp_by_sq(0xa54d83af,10,0x22b,0x8c3c0509);
        exp_by_sq(0xa54d83af,10,0x457,0x9b2c0c43);
        exp_by_sq(0xa54d83af,10,0x8ae,0x9034f141);
        exp_by_sq(0xa54d83af,10,0x115d,0x605d8870);
        exp_by_sq(0xa54d83af,10,0x22ba,0x6603ad27);
        exp_by_sq(0xa54d83af,10,0x4575,0x925dc777);
        assert false;
    }

    if(euclid_mod(pow_nat(10,nat_of_int(0x115d56)),0xa54d83af) != 0x1d1c0bc7) {
        exp_by_sq(0xa54d83af,10,0x8aea,0x3e61c74b);
        exp_by_sq(0xa54d83af,10,0x115d5,0x51e9b252);
        exp_by_sq(0xa54d83af,10,0x22baa,0x956a4a35);
        exp_by_sq(0xa54d83af,10,0x45755,0x76222bd9);
        exp_by_sq(0xa54d83af,10,0x8aeab,0x5c2d31e);
        assert false;
    }


        assert false;
    }

    q = 569003;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(10,nat_of_int(0)),0xa54d83af));

    if(euclid_mod(pow_nat(10,nat_of_int(0x130a)),0xa54d83af) != 0x7a1767d0) {
        exp_by_sq(0xa54d83af,10,0x0,0x1);
        exp_by_sq(0xa54d83af,10,0x1,0xa);
        exp_by_sq(0xa54d83af,10,0x2,0x64);
        exp_by_sq(0xa54d83af,10,0x4,0x2710);
        exp_by_sq(0xa54d83af,10,0x9,0x3b9aca00);
        exp_by_sq(0xa54d83af,10,0x13,0x2da16d5c);
        exp_by_sq(0xa54d83af,10,0x26,0x889681a3);
        exp_by_sq(0xa54d83af,10,0x4c,0x524e0c32);
        exp_by_sq(0xa54d83af,10,0x98,0x3ae2f6f5);
        exp_by_sq(0xa54d83af,10,0x130,0x379fe93d);
        exp_by_sq(0xa54d83af,10,0x261,0x46072060);
        exp_by_sq(0xa54d83af,10,0x4c2,0x43e8b703);
        exp_by_sq(0xa54d83af,10,0x985,0x1a3db1af);
        assert false;
    }


        assert false;
    }
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
    note_eq(1,euclid_mod(pow_nat(5,nat_of_int(0)),0x82d4b5));

    if(euclid_mod(pow_nat(5,nat_of_int(0x82d4)),0x82d4b5) != 0x6c516a) {
        exp_by_sq(0x82d4b5,5,0x0,0x1);
        exp_by_sq(0x82d4b5,5,0x1,0x5);
        exp_by_sq(0x82d4b5,5,0x2,0x19);
        exp_by_sq(0x82d4b5,5,0x4,0x271);
        exp_by_sq(0x82d4b5,5,0x8,0x5f5e1);
        exp_by_sq(0x82d4b5,5,0x10,0x27f96d);
        exp_by_sq(0x82d4b5,5,0x20,0x4a00c8);
        exp_by_sq(0x82d4b5,5,0x41,0x93163);
        exp_by_sq(0x82d4b5,5,0x82,0x5ff23d);
        exp_by_sq(0x82d4b5,5,0x105,0x6143f0);
        exp_by_sq(0x82d4b5,5,0x20b,0x6a429f);
        exp_by_sq(0x82d4b5,5,0x416,0x5949be);
        exp_by_sq(0x82d4b5,5,0x82d,0x405ba1);
        exp_by_sq(0x82d4b5,5,0x105a,0x7ca402);
        exp_by_sq(0x82d4b5,5,0x20b5,0x7d5de4);
        exp_by_sq(0x82d4b5,5,0x416a,0x6f6cfa);
        assert false;
    }

    if(euclid_mod(pow_nat(5,nat_of_int(0x82d4b4)),0x82d4b5) != 0x1) {
        exp_by_sq(0x82d4b5,5,0x82d4,0x6c516a);
        exp_by_sq(0x82d4b5,5,0x105a9,0x55a572);
        exp_by_sq(0x82d4b5,5,0x20b52,0xab66f);
        exp_by_sq(0x82d4b5,5,0x416a5,0x771b5c);
        exp_by_sq(0x82d4b5,5,0x82d4b,0x4a574d);
        exp_by_sq(0x82d4b5,5,0x105a96,0xdedbf);
        exp_by_sq(0x82d4b5,5,0x20b52d,0x23a56e);
        exp_by_sq(0x82d4b5,5,0x416a5a,0x82d4b4);
        assert false;
    }


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
    ALREADY_PROVEN()
    int g = 5; int p = 8574133; int q;
    q = 2;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(5,nat_of_int(0)),0x82d4b5));

    if(euclid_mod(pow_nat(5,nat_of_int(0x82d4)),0x82d4b5) != 0x6c516a) {
        exp_by_sq(0x82d4b5,5,0x0,0x1);
        exp_by_sq(0x82d4b5,5,0x1,0x5);
        exp_by_sq(0x82d4b5,5,0x2,0x19);
        exp_by_sq(0x82d4b5,5,0x4,0x271);
        exp_by_sq(0x82d4b5,5,0x8,0x5f5e1);
        exp_by_sq(0x82d4b5,5,0x10,0x27f96d);
        exp_by_sq(0x82d4b5,5,0x20,0x4a00c8);
        exp_by_sq(0x82d4b5,5,0x41,0x93163);
        exp_by_sq(0x82d4b5,5,0x82,0x5ff23d);
        exp_by_sq(0x82d4b5,5,0x105,0x6143f0);
        exp_by_sq(0x82d4b5,5,0x20b,0x6a429f);
        exp_by_sq(0x82d4b5,5,0x416,0x5949be);
        exp_by_sq(0x82d4b5,5,0x82d,0x405ba1);
        exp_by_sq(0x82d4b5,5,0x105a,0x7ca402);
        exp_by_sq(0x82d4b5,5,0x20b5,0x7d5de4);
        exp_by_sq(0x82d4b5,5,0x416a,0x6f6cfa);
        assert false;
    }

    if(euclid_mod(pow_nat(5,nat_of_int(0x416a5a)),0x82d4b5) != 0x82d4b4) {
        exp_by_sq(0x82d4b5,5,0x82d4,0x6c516a);
        exp_by_sq(0x82d4b5,5,0x105a9,0x55a572);
        exp_by_sq(0x82d4b5,5,0x20b52,0xab66f);
        exp_by_sq(0x82d4b5,5,0x416a5,0x771b5c);
        exp_by_sq(0x82d4b5,5,0x82d4b,0x4a574d);
        exp_by_sq(0x82d4b5,5,0x105a96,0xdedbf);
        exp_by_sq(0x82d4b5,5,0x20b52d,0x23a56e);
        assert false;
    }


        assert false;
    }

    q = 3;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(5,nat_of_int(0)),0x82d4b5));

    if(euclid_mod(pow_nat(5,nat_of_int(0xae70)),0x82d4b5) != 0x2066ef) {
        exp_by_sq(0x82d4b5,5,0x0,0x1);
        exp_by_sq(0x82d4b5,5,0x1,0x5);
        exp_by_sq(0x82d4b5,5,0x2,0x19);
        exp_by_sq(0x82d4b5,5,0x5,0xc35);
        exp_by_sq(0x82d4b5,5,0xa,0x122e44);
        exp_by_sq(0x82d4b5,5,0x15,0x6b150f);
        exp_by_sq(0x82d4b5,5,0x2b,0x5c5839);
        exp_by_sq(0x82d4b5,5,0x57,0x20cf8a);
        exp_by_sq(0x82d4b5,5,0xae,0x82c34e);
        exp_by_sq(0x82d4b5,5,0x15c,0x292e07);
        exp_by_sq(0x82d4b5,5,0x2b9,0x579dc6);
        exp_by_sq(0x82d4b5,5,0x573,0x7e9c33);
        exp_by_sq(0x82d4b5,5,0xae7,0x4927c2);
        exp_by_sq(0x82d4b5,5,0x15ce,0x57dbc8);
        exp_by_sq(0x82d4b5,5,0x2b9c,0x60ea50);
        exp_by_sq(0x82d4b5,5,0x5738,0x2c8af);
        assert false;
    }

    if(euclid_mod(pow_nat(5,nat_of_int(0x2b9c3c)),0x82d4b5) != 0x6c0491) {
        exp_by_sq(0x82d4b5,5,0xae70,0x2066ef);
        exp_by_sq(0x82d4b5,5,0x15ce1,0x7630a7);
        exp_by_sq(0x82d4b5,5,0x2b9c3,0x1bfcbb);
        exp_by_sq(0x82d4b5,5,0x57387,0x20323c);
        exp_by_sq(0x82d4b5,5,0xae70f,0x5c8bb4);
        exp_by_sq(0x82d4b5,5,0x15ce1e,0x6c0492);
        assert false;
    }


        assert false;
    }

    q = 7;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(5,nat_of_int(0)),0x82d4b5));

    if(euclid_mod(pow_nat(5,nat_of_int(0x9585)),0x82d4b5) != 0x31f0b9) {
        exp_by_sq(0x82d4b5,5,0x0,0x1);
        exp_by_sq(0x82d4b5,5,0x1,0x5);
        exp_by_sq(0x82d4b5,5,0x2,0x19);
        exp_by_sq(0x82d4b5,5,0x4,0x271);
        exp_by_sq(0x82d4b5,5,0x9,0x1dcd65);
        exp_by_sq(0x82d4b5,5,0x12,0x538ab2);
        exp_by_sq(0x82d4b5,5,0x25,0x515c15);
        exp_by_sq(0x82d4b5,5,0x4a,0x4d5836);
        exp_by_sq(0x82d4b5,5,0x95,0x66864d);
        exp_by_sq(0x82d4b5,5,0x12b,0x46aa1c);
        exp_by_sq(0x82d4b5,5,0x256,0x320858);
        exp_by_sq(0x82d4b5,5,0x4ac,0x6eb250);
        exp_by_sq(0x82d4b5,5,0x958,0x559fb8);
        exp_by_sq(0x82d4b5,5,0x12b0,0x7bf16b);
        exp_by_sq(0x82d4b5,5,0x2561,0x5c4aac);
        exp_by_sq(0x82d4b5,5,0x4ac2,0x4d66f2);
        assert false;
    }

    if(euclid_mod(pow_nat(5,nat_of_int(0x12b0ac)),0x82d4b5) != 0x393cb8) {
        exp_by_sq(0x82d4b5,5,0x9585,0x31f0b9);
        exp_by_sq(0x82d4b5,5,0x12b0a,0xd2c3d);
        exp_by_sq(0x82d4b5,5,0x25615,0x42b8a7);
        exp_by_sq(0x82d4b5,5,0x4ac2b,0x61f01a);
        exp_by_sq(0x82d4b5,5,0x95856,0x31e36a);
        assert false;
    }


        assert false;
    }

    q = 103;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(5,nat_of_int(0)),0x82d4b5));

    if(euclid_mod(pow_nat(5,nat_of_int(0xa296)),0x82d4b5) != 0x46ac9a) {
        exp_by_sq(0x82d4b5,5,0x0,0x1);
        exp_by_sq(0x82d4b5,5,0x1,0x5);
        exp_by_sq(0x82d4b5,5,0x2,0x19);
        exp_by_sq(0x82d4b5,5,0x5,0xc35);
        exp_by_sq(0x82d4b5,5,0xa,0x122e44);
        exp_by_sq(0x82d4b5,5,0x14,0x7e14c7);
        exp_by_sq(0x82d4b5,5,0x28,0x5ffbd0);
        exp_by_sq(0x82d4b5,5,0x51,0x785541);
        exp_by_sq(0x82d4b5,5,0xa2,0x10059c);
        exp_by_sq(0x82d4b5,5,0x145,0x6e4378);
        exp_by_sq(0x82d4b5,5,0x28a,0x3dbabc);
        exp_by_sq(0x82d4b5,5,0x514,0x50309c);
        exp_by_sq(0x82d4b5,5,0xa29,0x37ec07);
        exp_by_sq(0x82d4b5,5,0x1452,0x5c3522);
        exp_by_sq(0x82d4b5,5,0x28a5,0x376ebf);
        exp_by_sq(0x82d4b5,5,0x514b,0x5d9463);
        assert false;
    }

    if(euclid_mod(pow_nat(5,nat_of_int(0x1452c)),0x82d4b5) != 0x51a6c7) {
        exp_by_sq(0x82d4b5,5,0xa296,0x46ac9a);
        assert false;
    }


        assert false;
    }

    q = 991;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(5,nat_of_int(0)),0x82d4b5));

    if(euclid_mod(pow_nat(5,nat_of_int(0x21cc)),0x82d4b5) != 0x103b60) {
        exp_by_sq(0x82d4b5,5,0x0,0x1);
        exp_by_sq(0x82d4b5,5,0x1,0x5);
        exp_by_sq(0x82d4b5,5,0x2,0x19);
        exp_by_sq(0x82d4b5,5,0x4,0x271);
        exp_by_sq(0x82d4b5,5,0x8,0x5f5e1);
        exp_by_sq(0x82d4b5,5,0x10,0x27f96d);
        exp_by_sq(0x82d4b5,5,0x21,0x6c5a7e);
        exp_by_sq(0x82d4b5,5,0x43,0x62fdf6);
        exp_by_sq(0x82d4b5,5,0x87,0x6272d2);
        exp_by_sq(0x82d4b5,5,0x10e,0x1bb972);
        exp_by_sq(0x82d4b5,5,0x21c,0x2c6f3b);
        exp_by_sq(0x82d4b5,5,0x439,0x413574);
        exp_by_sq(0x82d4b5,5,0x873,0x5b7994);
        exp_by_sq(0x82d4b5,5,0x10e6,0x45cfcc);
        assert false;
    }


        assert false;
    }


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
    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x8aeab));

    if(euclid_mod(pow_nat(2,nat_of_int(0x8aea)),0x8aeab) != 0x6f820) {
        exp_by_sq(0x8aeab,2,0x0,0x1);
        exp_by_sq(0x8aeab,2,0x1,0x2);
        exp_by_sq(0x8aeab,2,0x2,0x4);
        exp_by_sq(0x8aeab,2,0x4,0x10);
        exp_by_sq(0x8aeab,2,0x8,0x100);
        exp_by_sq(0x8aeab,2,0x11,0x20000);
        exp_by_sq(0x8aeab,2,0x22,0x818b0);
        exp_by_sq(0x8aeab,2,0x45,0x54d73);
        exp_by_sq(0x8aeab,2,0x8a,0x72d51);
        exp_by_sq(0x8aeab,2,0x115,0x502be);
        exp_by_sq(0x8aeab,2,0x22b,0x419d6);
        exp_by_sq(0x8aeab,2,0x457,0x61489);
        exp_by_sq(0x8aeab,2,0x8ae,0x6c8a3);
        exp_by_sq(0x8aeab,2,0x115d,0x592fb);
        exp_by_sq(0x8aeab,2,0x22ba,0x584b8);
        exp_by_sq(0x8aeab,2,0x4575,0x1848e);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0x8aeaa)),0x8aeab) != 0x1) {
        exp_by_sq(0x8aeab,2,0x8aea,0x6f820);
        exp_by_sq(0x8aeab,2,0x115d5,0x57143);
        exp_by_sq(0x8aeab,2,0x22baa,0x7ac6b);
        exp_by_sq(0x8aeab,2,0x45755,0x8aeaa);
        assert false;
    }


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
    ALREADY_PROVEN()
    int g = 2; int p = 569003; int q;
    q = 2;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x8aeab));

    if(euclid_mod(pow_nat(2,nat_of_int(0x8aea)),0x8aeab) != 0x6f820) {
        exp_by_sq(0x8aeab,2,0x0,0x1);
        exp_by_sq(0x8aeab,2,0x1,0x2);
        exp_by_sq(0x8aeab,2,0x2,0x4);
        exp_by_sq(0x8aeab,2,0x4,0x10);
        exp_by_sq(0x8aeab,2,0x8,0x100);
        exp_by_sq(0x8aeab,2,0x11,0x20000);
        exp_by_sq(0x8aeab,2,0x22,0x818b0);
        exp_by_sq(0x8aeab,2,0x45,0x54d73);
        exp_by_sq(0x8aeab,2,0x8a,0x72d51);
        exp_by_sq(0x8aeab,2,0x115,0x502be);
        exp_by_sq(0x8aeab,2,0x22b,0x419d6);
        exp_by_sq(0x8aeab,2,0x457,0x61489);
        exp_by_sq(0x8aeab,2,0x8ae,0x6c8a3);
        exp_by_sq(0x8aeab,2,0x115d,0x592fb);
        exp_by_sq(0x8aeab,2,0x22ba,0x584b8);
        exp_by_sq(0x8aeab,2,0x4575,0x1848e);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0x45755)),0x8aeab) != 0x8aeaa) {
        exp_by_sq(0x8aeab,2,0x8aea,0x6f820);
        exp_by_sq(0x8aeab,2,0x115d5,0x57143);
        exp_by_sq(0x8aeab,2,0x22baa,0x7ac6b);
        assert false;
    }


        assert false;
    }

    q = 7;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x8aeab));

    if(euclid_mod(pow_nat(2,nat_of_int(0x9ec3)),0x8aeab) != 0x36231) {
        exp_by_sq(0x8aeab,2,0x0,0x1);
        exp_by_sq(0x8aeab,2,0x1,0x2);
        exp_by_sq(0x8aeab,2,0x2,0x4);
        exp_by_sq(0x8aeab,2,0x4,0x10);
        exp_by_sq(0x8aeab,2,0x9,0x200);
        exp_by_sq(0x8aeab,2,0x13,0x80000);
        exp_by_sq(0x8aeab,2,0x27,0x74ca1);
        exp_by_sq(0x8aeab,2,0x4f,0x35c85);
        exp_by_sq(0x8aeab,2,0x9e,0x6d20c);
        exp_by_sq(0x8aeab,2,0x13d,0x81c0a);
        exp_by_sq(0x8aeab,2,0x27b,0x556ba);
        exp_by_sq(0x8aeab,2,0x4f6,0x62057);
        exp_by_sq(0x8aeab,2,0x9ec,0x3e0b0);
        exp_by_sq(0x8aeab,2,0x13d8,0x527e2);
        exp_by_sq(0x8aeab,2,0x27b0,0x528ec);
        exp_by_sq(0x8aeab,2,0x4f61,0x2591d);
        assert false;
    }

    if(euclid_mod(pow_nat(2,nat_of_int(0x13d86)),0x8aeab) != 0x6e0dc) {
        exp_by_sq(0x8aeab,2,0x9ec3,0x36231);
        assert false;
    }


        assert false;
    }

    q = 97;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x8aeab));

    if(euclid_mod(pow_nat(2,nat_of_int(0x16ea)),0x8aeab) != 0x6b524) {
        exp_by_sq(0x8aeab,2,0x0,0x1);
        exp_by_sq(0x8aeab,2,0x1,0x2);
        exp_by_sq(0x8aeab,2,0x2,0x4);
        exp_by_sq(0x8aeab,2,0x5,0x20);
        exp_by_sq(0x8aeab,2,0xb,0x800);
        exp_by_sq(0x8aeab,2,0x16,0x33953);
        exp_by_sq(0x8aeab,2,0x2d,0x6fed9);
        exp_by_sq(0x8aeab,2,0x5b,0x6df45);
        exp_by_sq(0x8aeab,2,0xb7,0x66a35);
        exp_by_sq(0x8aeab,2,0x16e,0x10287);
        exp_by_sq(0x8aeab,2,0x2dd,0x2256);
        exp_by_sq(0x8aeab,2,0x5ba,0x6d8b7);
        exp_by_sq(0x8aeab,2,0xb75,0x837);
        assert false;
    }


        assert false;
    }

    q = 419;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x8aeab));

    if(euclid_mod(pow_nat(2,nat_of_int(0x54e)),0x8aeab) != 0x39a80) {
        exp_by_sq(0x8aeab,2,0x0,0x1);
        exp_by_sq(0x8aeab,2,0x1,0x2);
        exp_by_sq(0x8aeab,2,0x2,0x4);
        exp_by_sq(0x8aeab,2,0x5,0x20);
        exp_by_sq(0x8aeab,2,0xa,0x400);
        exp_by_sq(0x8aeab,2,0x15,0x5f3ff);
        exp_by_sq(0x8aeab,2,0x2a,0x64d06);
        exp_by_sq(0x8aeab,2,0x54,0x3609c);
        exp_by_sq(0x8aeab,2,0xa9,0x73de8);
        exp_by_sq(0x8aeab,2,0x153,0x6259e);
        exp_by_sq(0x8aeab,2,0x2a7,0x3c1a2);
        assert false;
    }


        assert false;
    }


}


  @*/

