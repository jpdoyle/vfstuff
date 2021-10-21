/*@ #include "p25519.gh" @*/

#if 1
#define ALREADY_PROVEN()
#else
#define ALREADY_PROVEN() assume(false);
#endif

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

//lemma void p25519_2_generates1()
//    requires true;
//    ensures fast_pow_mod(P25519, 2, true,
//            nat_of_int(pow_nat(2,nat_of_int(4))-1),
//            nat_of_int(pow_nat(2,nat_of_int(5))-1),
//            2147483648);
//{
//
//}

lemma void p25519_2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(P25519-1)),P25519) == 1;
{
ALREADY_PROVEN()
    p25519_formula();
    int P = 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed;
    int g = 2;
    note_eq(1,euclid_mod(pow_nat(g,nat_of_int(0)),P));

    if(euclid_mod(pow_nat(g,nat_of_int(0xffff)),P) != 0x7f7e97cd178ef6c053d43ee4017c1d92ddc1ae18350ff99ab05d59d28f491555) {
        exp_by_sq(P,g,0x0,0x1);
        exp_by_sq(P,g,0x1,0x2);
        exp_by_sq(P,g,0x3,0x8);
        exp_by_sq(P,g,0x7,0x80);
        exp_by_sq(P,g,0xf,0x8000);
        exp_by_sq(P,g,0x1f,0x80000000);
        exp_by_sq(P,g,0x3f,0x8000000000000000);
        exp_by_sq(P,g,0x7f,0x80000000000000000000000000000000);
        exp_by_sq(P,g,0xff,0x13);
        exp_by_sq(P,g,0x1ff,0x2d2);
        exp_by_sq(P,g,0x3ff,0xfe888);
        exp_by_sq(P,g,0x7ff,0x1fa264d9080);
        exp_by_sq(P,g,0xfff,0x7d176e0b4b0cc7d208000);
        exp_by_sq(P,g,0x1fff,0x7a3fc737f93f58db10bf314a30b1e9824080000000);
        exp_by_sq(P,g,0x3fff,0xb8cd5e7255890d0e0d907986602bddc9c67ba97196e7941267ca3056254b232);
        exp_by_sq(P,g,0x7fff,0x1f0dfe590cd9d85bc54f6df96a681c2f5d07c94c7b4a77dc54a7229c1723133a);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffff)),P) != 0x3b5822765de225e133be342f95c09f0e7914206ef4a0d297740ccf3336a0bcb5) {
        exp_by_sq(P,g,0xffff,0x7f7e97cd178ef6c053d43ee4017c1d92ddc1ae18350ff99ab05d59d28f491555);
        exp_by_sq(P,g,0x1ffff,0xde3d0ec62b72d4aeb36cbf321895273c2f8448d08a0b497109c12f489b2c1f5);
        exp_by_sq(P,g,0x3ffff,0x5c5b021c025321741192954188216b1154e01f00d9f83522770dd2554e78c18d);
        exp_by_sq(P,g,0x7ffff,0x1b776bbea07930d25162ad35f34a44e31ad5e75309fb8e7a6274fca9b38b5064);
        exp_by_sq(P,g,0xfffff,0x467038a8aad2effd9b3ed28402ab6f4ff081bc0947e8f8e3b63278c2ee40ccd5);
        exp_by_sq(P,g,0x1fffff,0x423ff9abcd6e0ac2cf971a6f0233cadea24c49c564bb59aeea815d78b0bdff17);
        exp_by_sq(P,g,0x3fffff,0x524a02b8dc468def7eb7e95ad469eee1ccab3d521c3c4986984e845dbcf311ac);
        exp_by_sq(P,g,0x7fffff,0x5c221fac61c0d6ffe66104d19e84e07208db61a97320b6960d900864519e3877);
        exp_by_sq(P,g,0xffffff,0x1fbe3b0fb70b360cdf1e8c696eca5d7fd5baccb35fb8479131e4ab98c2ef2538);
        exp_by_sq(P,g,0x1ffffff,0x7b87c61a21bd1607de6d79162713dc578522256259be972e711046f84f99ef74);
        exp_by_sq(P,g,0x3ffffff,0x12b24d6c18eb768b7724f3f7d3dd5b18e34a5a3e71ba3dc0756d930bacfe0acd);
        exp_by_sq(P,g,0x7ffffff,0x36accf8464cc55eb112dfe4ce8a197c0a0e7dd3a65cc0db42d86974422d51bcf);
        exp_by_sq(P,g,0xfffffff,0x331d6459ffbff29a0bcfaf627910978d4b25d0aa6998888324d6c00a3117477);
        exp_by_sq(P,g,0x1fffffff,0x1d6a3e0e33e7d36e6f1956bbcfc0fb038ff048f6e430c94db515f9aeae98564);
        exp_by_sq(P,g,0x3fffffff,0x4599cc19f91ab66ae385744bcbd7468eab1d8bca124390c56de62e1096cb7846);
        exp_by_sq(P,g,0x7fffffff,0x539ee148b32774f7f3aaeca65f110118df5ca04f77e1232fded8d83cce9a9b08);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffff)),P) != 0x7e7fa578f05b7f51a80b82d5df335dba51eb6a9f6dc4258a8bbcc9caaaf8369a) {
        exp_by_sq(P,g,0xffffffff,0x3b5822765de225e133be342f95c09f0e7914206ef4a0d297740ccf3336a0bcb5);
        exp_by_sq(P,g,0x1ffffffff,0x4544a25fe11230f1ac5e2c3229e3cb05acd1b509957074665eb3ae801b4d6511);
        exp_by_sq(P,g,0x3ffffffff,0x31e303467df86d50e8e12275cc3f33332f4f99ad3ef3b38faa2245031dd105d);
        exp_by_sq(P,g,0x7ffffffff,0x450172c0ac3a455a330d82fc1fc4e86d23d66bf206db8ee551b8855f0760813f);
        exp_by_sq(P,g,0xfffffffff,0x51ca4e3284e1c9964e809cc55b3211c0fc431bc20ee5e321d22353c59b07b6d);
        exp_by_sq(P,g,0x1fffffffff,0x63eb51ea169cde66974dad19de73cf0d5fc158c29c4f1bfc548adc741b397dec);
        exp_by_sq(P,g,0x3fffffffff,0x9f32ad3cb4e7bbed9f68a88befe5e1772862f90a89d7f93ddcbd4f81f8a26cf);
        exp_by_sq(P,g,0x7fffffffff,0x28d053961137c98ea810238b76355510820e9c5668a70f4c33c02649f16a065);
        exp_by_sq(P,g,0xffffffffff,0x5a537fe0cb35b3bea7db382afebbaae6c42fc4dfc94025db7f483a979476d6af);
        exp_by_sq(P,g,0x1ffffffffff,0x1c2261269bde5d8a23e88bdcfa0efa5f91c60951386a6441dfa38e5f6c500bc3);
        exp_by_sq(P,g,0x3ffffffffff,0x53e16d58acb9b712cd3fd2a6217e2f4505df411ee8ca807fbc2eee7a24f7f72c);
        exp_by_sq(P,g,0x7ffffffffff,0x65fd3f4e16ec12888efb70cc8b28a29273846a5da1823ce24525c3af1a0e5928);
        exp_by_sq(P,g,0xfffffffffff,0x54b45c911bd0aa55f16b194fdd80e3065ac19b2c1488bbbd4f837ab614121ca6);
        exp_by_sq(P,g,0x1fffffffffff,0x45e788cb47435e1b6fc2051646cbe0eb6024b4dc2885f89bed089a226205a5b8);
        exp_by_sq(P,g,0x3fffffffffff,0x6788c579f377d5eb202f037034d58d67c9c46b96360332d744b9d9fc19984635);
        exp_by_sq(P,g,0x7fffffffffff,0x60302490d899f5f2e9e02601a667c42b7d6d8b1c905afb24b5b1f35ed9c4d703);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffffffff)),P) != 0x29bd1bc5fb701b6202102431303b2b4a8a3a2af6213119638e0b454b035a3342) {
        exp_by_sq(P,g,0xffffffffffff,0x7e7fa578f05b7f51a80b82d5df335dba51eb6a9f6dc4258a8bbcc9caaaf8369a);
        exp_by_sq(P,g,0x1ffffffffffff,0x37bb5bbcc46568414878c06702bb06e01dfef02225d056072546c7c8f2231075);
        exp_by_sq(P,g,0x3ffffffffffff,0x410e5be1ceec75389eac57fe3b8cf3e2ec40bb5a87dd61b95b58669638e4b647);
        exp_by_sq(P,g,0x7ffffffffffff,0x639782956b2d03c3b50ee26f49583a17c209caff6f283b5f308dbc8fa243804d);
        exp_by_sq(P,g,0xfffffffffffff,0x4a2f51afd3bf227ecc6f11c09d42adce4fc162482eb021d85953f1bda6a07d65);
        exp_by_sq(P,g,0x1fffffffffffff,0x62b27de316c873c65664c140ea184f417a463bb2f2bd349003527247adeca31e);
        exp_by_sq(P,g,0x3fffffffffffff,0x1f187ccbd81c70a97ea3db6abe43172065bb4c67dadaec056830a01d0df9edbe);
        exp_by_sq(P,g,0x7fffffffffffff,0x5db09e4076e9cef49658f729d857859216d074616635cbcf8f178d0b5c23b74e);
        exp_by_sq(P,g,0xffffffffffffff,0x304d384d2f9dbc378a27d19919a4a9514b56d6ae3ca9c0a001b34d10cc9285ad);
        exp_by_sq(P,g,0x1ffffffffffffff,0x714520e2ad0d3064e4648a0fa8e7213495c02233aa2f5ffb84c4edbcdc966f4f);
        exp_by_sq(P,g,0x3ffffffffffffff,0x7d6149f0d55f4be6d972b2673e6f1dedf743b811a5f0fbecf4e123fa2cde07c);
        exp_by_sq(P,g,0x7ffffffffffffff,0x1863621ef9cc507e2bc8b5340dcdc52c6b49032850bd067731b407940c6c62c6);
        exp_by_sq(P,g,0xfffffffffffffff,0x322c8f19542013330297c68b0c40609919693fac1dacfb57831868a326baad10);
        exp_by_sq(P,g,0x1fffffffffffffff,0x3e9755f029ad926c8f281686ec26cd545a5851ed269a8d0eb2dc3fff1d3fe3db);
        exp_by_sq(P,g,0x3fffffffffffffff,0x5a259bd002319b926716cfc81dbb8232bc7b48bce62b4db7bba2069862b3fc20);
        exp_by_sq(P,g,0x7fffffffffffffff,0x419f3b1a98f90c89d23f8327b91b94acb7c20ec1b1840b06daf7e961f6ff7df9);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffffffffffff)),P) != 0x2de3c13da94fb24d31a7291fa97c7ea60976e7ba7af24d40fd7f16638635ec9e) {
        exp_by_sq(P,g,0xffffffffffffffff,0x29bd1bc5fb701b6202102431303b2b4a8a3a2af6213119638e0b454b035a3342);
        exp_by_sq(P,g,0x1ffffffffffffffff,0x70ab5ea2da24b64d4d7191eefbe84cbe45d0ab9628454f2495915384beb77a15);
        exp_by_sq(P,g,0x3ffffffffffffffff,0x66522a754d891bbeca560372d45e6a7f7491d8062a8e9ac7dc3d2017c2c3a6a1);
        exp_by_sq(P,g,0x7ffffffffffffffff,0x5e009653e507c594898678ae5d0037407ed5bf4610b44a725d19675bef3d6c13);
        exp_by_sq(P,g,0xfffffffffffffffff,0x17d33b601b5f68bc78e9cc60b751ad46bfa468fec5052828bd389f612a835c7c);
        exp_by_sq(P,g,0x1fffffffffffffffff,0x7e5441f05138612df3b7215ae4b97eda016c91f96e896a3f2385973c9790383a);
        exp_by_sq(P,g,0x3fffffffffffffffff,0x4757007b8c414bff9b42fc0985e1bec31ecc471943fbef18e4564fe3c109e2a3);
        exp_by_sq(P,g,0x7fffffffffffffffff,0x45224608a5add3adaba078f9a3888da0ba8914ba5c15a934580ebdfc060bf140);
        exp_by_sq(P,g,0xffffffffffffffffff,0x4bbd6f63fb19d327092a0c86654245a62e7b60e51f22f60e3679616e8e08bd40);
        exp_by_sq(P,g,0x1ffffffffffffffffff,0x484c304b2cfe32810b6bef75002edd6a4bd07a326483a15477d83b979306ab07);
        exp_by_sq(P,g,0x3ffffffffffffffffff,0xe7c4616bd8c84041b2efc968940b19c8396fab61ab16d4a02263f8cddb6c9f9);
        exp_by_sq(P,g,0x7ffffffffffffffffff,0x50238158174c551fb0a070b5ae8c248e3ec878e2f75cfb20010e28c37ad2ab1);
        exp_by_sq(P,g,0xfffffffffffffffffff,0x3049055d5aa594440ae71a1dda29615021ea5b26ed510d0a89bbf3f6d04167aa);
        exp_by_sq(P,g,0x1fffffffffffffffffff,0x1344f1f380acdc6c84ccbdc91c4f1e3c3cf60dcb5c7bcea68c6559c0624fcda);
        exp_by_sq(P,g,0x3fffffffffffffffffff,0x605bf1a17ffedc5a22f3aa4b542bafcee95998eff8cde3bd064f7f8ea935eeae);
        exp_by_sq(P,g,0x7fffffffffffffffffff,0x6da40bad5859c0b0f7e0d217a1555a70a40310e610ea052dca695e6e826223bc);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffffffffffffffff)),P) != 0x6f97c8c769da1c291f633cd37e817b567804f88a60217141e7e048779597a578) {
        exp_by_sq(P,g,0xffffffffffffffffffff,0x2de3c13da94fb24d31a7291fa97c7ea60976e7ba7af24d40fd7f16638635ec9e);
        exp_by_sq(P,g,0x1ffffffffffffffffffff,0x60c27697f559f88c2f8b1f2db010c5cab89e19c30795269440b599e1a9e3b23c);
        exp_by_sq(P,g,0x3ffffffffffffffffffff,0x4c28358c0a63c47ade38ef0754d5cfb4782112a6824907b555649228765ce6d8);
        exp_by_sq(P,g,0x7ffffffffffffffffffff,0x26886446a5c1070536bb80608b9df6dfd9bf5ae9748aba37d735fcc1e1fa7c72);
        exp_by_sq(P,g,0xfffffffffffffffffffff,0x6c4bf7949a61d793ad122cc1d0b9d1d92b2ceb7e29b99e08235ceb5b56b6fcd8);
        exp_by_sq(P,g,0x1fffffffffffffffffffff,0x4b8d6f110d9bd3e9742dd96bb3945266df4b29ebf92e31d23561913dce9675d3);
        exp_by_sq(P,g,0x3fffffffffffffffffffff,0x1db2afb7ff29a9b84efa4bbb79825c3cba12e2b483b4928f57b9635bbc344e3);
        exp_by_sq(P,g,0x7fffffffffffffffffffff,0x445eaa228303d740c1f0c8111aa1a43da17464872ee11c85c8b7263f67cbfcf8);
        exp_by_sq(P,g,0xffffffffffffffffffffff,0x1690bb51b13f6e0dee0cb31d8e2540ae46099b2f5aa8fe24a34dc8e0880df274);
        exp_by_sq(P,g,0x1ffffffffffffffffffffff,0x1648827ae6cf5096bf3df57e0e218860fc1e3850c1496ae29fa29c0390f88836);
        exp_by_sq(P,g,0x3ffffffffffffffffffffff,0x36e4fef770e0ebb0eefbd1400e5cee2392e09986734f273cc909f7cb82868b3a);
        exp_by_sq(P,g,0x7ffffffffffffffffffffff,0x111baef8ecf7e940001fd734aaa12dc469820baec835b9fcc155b15c368e2e6e);
        exp_by_sq(P,g,0xfffffffffffffffffffffff,0x3ec1fb89a68687237b23de07148750d8c2357676a16b57ea5255224a758f266f);
        exp_by_sq(P,g,0x1fffffffffffffffffffffff,0x67cad1c7d7c7fd36134bcfa0e615c08130a84be05941d90990d2dbd8d36c49c8);
        exp_by_sq(P,g,0x3fffffffffffffffffffffff,0x7b0e932db621b2ff0c9a1d36caa4af6b92b918fc66e22718060a37abd413c932);
        exp_by_sq(P,g,0x7fffffffffffffffffffffff,0x2abb4c95321b78db0dfd5768e49f7c21359a05f26807c5df6abbf8b7e0cc846b);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffffffffffffffffffff)),P) != 0x305ff504f38c9dead5fea2a87f8855ed24f61c46d6ad44ed8ddb294e279c748f) {
        exp_by_sq(P,g,0xffffffffffffffffffffffff,0x6f97c8c769da1c291f633cd37e817b567804f88a60217141e7e048779597a578);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffff,0x449c2f5239333dd904083b3ac10d9cbf3f1b688ce7060fe69a45633a5193b021);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffff,0x4d250478710852639c536ca84cf21977842f0f49fb02bca5bf01e92c7055d673);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffff,0x4b1497e95da51643fc9724f875c64ed1c77a2a0eb373cdab35e98c303b129df4);
        exp_by_sq(P,g,0xfffffffffffffffffffffffff,0x78577c78225b8c3a6338b0baf2e4e7badd6e66fd365d7950ce0a6f9be14ac8fe);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffff,0x3738a60ebe123e5f8825254430aebeec235e0a6ab1f8118555ca73da288f542f);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffff,0x62c079c9d9fc47013ce6740e285d14a86da6c77d2d9f1eacb6e1ea925b54d6a3);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffff,0x6116698f2fbdc0d9ffdd8b2145aa1560d54bc52fffc32bf29d4bc7f48dba18ba);
        exp_by_sq(P,g,0xffffffffffffffffffffffffff,0x7f5cfe517161e30f81ee6ebdd0169eadd8c9b3642805b9e904e8ba87ac2edcb9);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffff,0x1b63eae1c1031c9387ed8d5b1b95dd0c0969e7108572b2e6ab5733340b5ca75f);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffff,0x7ccf23c9ca519de2504f9d475d91f147e40d206d164cb9d5439cf8710ca09ca8);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffff,0x3bf660e9e465d9b4d35e5f5951b0ddf7f8990885004f6095e6b7737be653ed6d);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffff,0x1338488add0af95c404fa0402113ae43243ec47ceb4d8adbd17772198d644a6e);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffff,0xfd7b2f998a56543be37c177e850888f82727268000fe49954a112390864f7b9);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffff,0x6e15686488df199392a01b4a8ac94875e665d622ede0874e2eb42673a99827e4);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffff,0x4654c072c17c2aadd95251b2543f6eee8ae3c8b5c8758ecddc0a4e682a7108f4);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffffffffffffffffffffffff)),P) != 0x3b9cc3524e6bdb8580d278d115d042eaa7c19b2145a23a1197eb5466c460af7b) {
        exp_by_sq(P,g,0xffffffffffffffffffffffffffff,0x305ff504f38c9dead5fea2a87f8855ed24f61c46d6ad44ed8ddb294e279c748f);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffff,0x7f5154b89a9793334592de6b912acc24bc8fb0ba4e65952093cba23e1d1a1762);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffff,0x418626877ad3f0c2f37fbce1aa31c2f60d8cfed27a577daf6a1dcb317bc8b9b);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffff,0x6a1de49a2f911c03abd5b7a5bb1452533e8dccd17acb0e45aa98e50d69b857c);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffff,0x7d72c109d65f59d607e1d4264817fd5647892449fc15e397d10acbbcb8077118);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffff,0x752379dde0daefd9fbf695281c26f66b233090acbd076280e9605188d008cd8d);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffff,0x33d382ea3fef1cb8f59e816f31103782239b9e4d156a454347006d6819abe990);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffff,0x61c35c85fe9fbc3c72f8e6fc6b69b01d3b7c504b3df986e8a4658b4f999a353f);
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffff,0x7bab852e8224e61b30fffd9fcaa90920859d66e68c0f4d18b9683662e7255a3e);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffff,0x8f07602cd009e6ccabc1a25642a7dcd28374c01dd2e197131136915896c8a46);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffff,0x4255d86fbc10253a88961173400b45a2997840c2d8f2e42e0b563cb1f16a75a1);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffff,0x2e6f1f4a2e8f5b34aa3b7228f09e1766a4808c9410519959b8de91355e1e0aec);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffff,0x2718c571cbd695d3b44154454ffe04ef815e26c01aa3938c68814ba2ef3fc5c7);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffff,0x4a7092a9de3e8c50291cf15f0358e81d7698548c905decbf21a7b3dc53715ea3);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffff,0x19112028e6a666ecea034c65f668804ddc0bb26843c958e843d5829c00283cc2);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffff,0x6fa832d70dc171f98a99ab0c0ae5c98fb58d4dffe0e132b63c6974141937d3a0);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffffffffffffffffffffffffffff)),P) != 0x1fd571ebc05fcae1e68fa278f24c5ac839dbf35344df44f90e67d83989dc71f3) {
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffff,0x3b9cc3524e6bdb8580d278d115d042eaa7c19b2145a23a1197eb5466c460af7b);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffff,0x9420d4302987a6d9df5a9828552135e8b06145acef936fa0ee45505f81b09b0);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffff,0xfb674c11d5165ad50ad3f818e3b6e03122f6c55b38d0c24b17437393f5294e7);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffff,0x41364f9981abaf7ed0cf4072d21de43ed919ce6b91f7ba87de1062a5bf9326cc);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffff,0x6e8b443ee73f81760bba50fb8987a46b178cc0f59a520968b5c355493f08eb1f);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffff,0x44d61060e5a745fb450e39d473ed51a80622a81e57d908d7bc01aaca6e475c1b);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffff,0x677eb04e9118fd8f89fc608b94681b76569eb188e10d8e4dd67ae287f3397b36);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffff,0x58aba42e4ff91d81c01a58d4f77cd6fd004d7b444491f39399b41b1334e871ec);
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffff,0x49e18973ed40d9c4baee4cbd0880ad1187fdbbf6c75548ef31f32fdf893027b4);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffff,0x2704c3e10709d430d475e31db14a20806722f9d1ce4ef6d074467e95893ea801);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffff,0x1cfd8f5e73a8137e72a282b6e51bd32d13941502179c6021e60b98daef64acab);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffff,0x3d83e64e5f66f0a7120cd19cc6bcc5e6d8ecfdbe6146b367f4404e8775565829);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffff,0x2cb0dcdf1750c74a72c61d2c4aee2c31267a745b38bb3b7abb76b16eae1c3f2b);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffff,0x140e2289d512d6d81eeb317076f7d13fa3d8b4514a126bfe8fb07a824c91f6f8);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffff,0x453d5a4bde793099af854346b73877d52e3ba01ea494223118545560bef47c29);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffff,0x3012e63b6c18b7c3693e92e9c3106233077b5e5441117fd5e86880466bee868);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffffffffffffffffffffffffffffffff)),P) != 0x5bec4671395f5c6d85b58812ee657cfe392ef79f082e5478a5233d2c326f28f1) {
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffff,0x1fd571ebc05fcae1e68fa278f24c5ac839dbf35344df44f90e67d83989dc71f3);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffff,0x7f34c30f9811bde34280bc47bd61af35613f0c620ceec536039a9aaed9a1e2e9);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffff,0x59a50c8ac92d6c1b1d74ad1042757f7876ede60b4dcc07eeef43bb4de284a6c5);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffff,0x65a33817ede08fc19cc044ef64107c7e45d457f2b921dcbe75f3805ba787fe84);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffff,0x3d34c25bef575f5ec89a1c31afa52819670eddeb68d70039cf57fb0b07ee8470);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffff,0x4f0dc24d1280e22b5677e07e2e1692d65b38f34c0a3a455ed74391ad158804e9);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffff,0x544b387e8b0bf858b63ba7d75d975896c092030aab333193987ff852c9ff0844);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffff,0x1ebbd07684972aad18e11c8277bfd2a949e5d93766074f6e5cef38d06a75d9f4);
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffff,0xc0f1634d8374d86a38d952f4b190e9be7f363e76149c1cdf118fa7beb5f2a21);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffff,0x7a6631b5f9818a68739c79c8612a2b317d6af2ada13adcf65d975a2d6d2ad627);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffff,0x301e9858b806dbef9859d3de521d70626ec2e9544f97179d507520c914a4b48d);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffffff,0xf2f6a58dd46d615b52e1a27f23fc57c53d0882b735d7314e8207e4cbdf363fd);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffffff,0x2f9f4ca0ebdef08e4b2c1b47eb8c3e5d39e8531eeed698cff3777b231ec49036);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffffff,0x33895213d1fbf607c00497f8917082690d5273fa4efeae50f1e22e13fe56b49c);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffffff,0x148d28ac5b29f124e1a419997ef15f5063cd09d6f9264b42a11fe0e953b5339b);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffff,0x3a57b027d1608f19b2d6e16b321802f37b9f3f91f6de950ff8599b550ce841c9);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffffffffffffffffffffffffffffffffffff)),P) != 0xdb23a9a95203b8ebb3e79ff8fcb4a85c01f68e00f5f51dfc2b7ceb7f8a4ebca) {
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffff,0x5bec4671395f5c6d85b58812ee657cfe392ef79f082e5478a5233d2c326f28f1);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffff,0x3ac4cdd312d5cbea8b140f7a382ccb7ac30a7d6bcc8bbc4f968160021d6be731);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffff,0x7ae707646eb04fc63bbfc4d75c67d8f1e3651e412773190df288fcc6455a98cd);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffffffff,0xfc82279aabcd068314b4875883a19654e0cb4f8bdadafa7b711fd9cd445cf8b);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffffffff,0x2f3b44dea79ce22969e28248b9627f8f91e77d11704a21f5bd9aa16c283d5c6d);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffffffff,0x3dc2fcec5787389c670713cb5c306627978b8b27aa31a5483214499f37b1b75b);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffffffff,0x4ea93f9ba68c0bba678eec3e96fe46fb7df781cbba81086aa0c538eb58ce32d4);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffffff,0x7fef81a7d01be5db858ac1e0c8d5efc4ecd03a62af63472a8cd83a1f81be6ed0);
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffffff,0x5fdd5e93f03a3b9bcbfbbe91d05a9502ca36792712cac57d45781211c8d70173);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffffff,0x22acf76b3be7a6899e078d568e1e78bf270d0142ac99d03a7b61b976edcced4b);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffffff,0x365a1725c5975c06d6054245bba5080caf9e741df1be36a2c9c484bb07e33eb);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffffffffff,0x167eb50db4312cbccb615f9f22c396946da5645d8d40065bc39431fb4bb2646c);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffffffffff,0x75b5965ba4a6f883e9c4b335ccbde1ca343ee2109612c2df1fb50465aaf123e8);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffffffffff,0x1f038713c67d2518bcc84692fe012decb92b42b7926d186e422a34dc39eede93);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffffffffff,0xd68ede480676ed7b444ee1dd54f5f6d8d1b6c95e7a34a2f0a017a8e62257f94);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffffffff,0x24593c1ede8c9cebc7bde5f51882f592f3f9fe654fad85578b2ffb0ed50975a8);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffffffffffffffffffffffffffffffffffffffff)),P) != 0x46e144311c54583630c130ba66d4651d16e9e0db7a918eb9e7b7144877c64198) {
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffffffff,0xdb23a9a95203b8ebb3e79ff8fcb4a85c01f68e00f5f51dfc2b7ceb7f8a4ebca);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffffffff,0x1837a6306707fe8664adcd9044f21bfac2d28b059f26210909f9dd1deaae3ab);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffffffff,0x783184d066b2a94b29656756217afda85a9750736bc5ea19ed7533b4ec8c7c79);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffffffffffff,0x5b7fdc14c006017b416da389d0201482bbd63a94731ec0572f8c9789ff56b4e7);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffffffffffff,0x7649359da7edf0f22fe305eb2964cf8a5365ec1e312cbca59d451d7c106f36c9);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffffffffffff,0x41d10fb133fdc1f2125655bb0b3445b2530fc558333458971572934bcbca0338);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffffffffffff,0xe6edbaa58d2a38905a875d9f3083976bc15d323675d522adb4485c4ff31e51e);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffffffffff,0x1c6b1de7d692a61dd9ea3bb2c7f5afdf0e7f0f2d4121cd69909090ff7691732a);
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffffffffff,0x351cabb514e79da8af43f2299f9d85776fe1751c9d128c0bb89dcc83c3673bc2);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffffffffff,0x51d223e61ac4eb6998d9771dc72c137e771bbfa62066c3693d01bc4af72df030);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffffffffff,0x5a98250d9544880a23d26a5dd2d5b8d77c3d8b656a12d3833856412238b0ee16);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffffffffffffff,0x4357ed4a9250b4706959c7a5f7861c03d9c0892545c2be1841a72cca33181026);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffffffffffffff,0x6acf703ef6f0238480649afbef9dbd593f396d92092d7c0e713f71033fec6d75);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffffffffffffff,0x359372836d876d8cf11dcad4311505f91463ff7e3760328a11dfdbd491a9f52c);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffffffffffffff,0x627a8fafe107c3e453ae6e8a686363cc2d7435f384e5013afe89027f0b24e376);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffffffffffff,0x76fdb306a2b03a98b631b569ff0a668731dab5fd49c13f1de50b3b021a2e2fb6);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffffffffffffffffffffffffffffffffffffffffffff)),P) != 0x3c553aaf846c54946229033406f32bb64864b3c04ad33daee227581bdaedcc7b) {
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffffffffffff,0x46e144311c54583630c130ba66d4651d16e9e0db7a918eb9e7b7144877c64198);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffffffffffff,0x710082c4fbeeaec768b038f494b75ab8441daad98ce5d0be69893a78b35c2bd1);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffffffffffff,0x6bca1a076b9e31319e5dbcf4e6686405641464d2c500127141feeaefa048f6f4);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffffffffffffffff,0x501800f54892d55acce34cad3ea1ecd34ad0d93a146792b88493f0f7877d17a2);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffffffffffffffff,0x559e220cfeed955813fda85426acc15a6682fc8a8e4174dc749b7a4fef8d14ab);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffffffffffffffff,0x648c665b35748c2785c9fbb33cd925375ee04d74845fa2923ce309776edc5500);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffffffffffffffff,0x5f65072209ef98970ccfaeb6803ac24a4e619c630680c598217b9f523e30b216);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffffffffffffff,0x6efc714204f46ad9d469f6d7584edc09d0a44a3fde49f7ecfd2c4e134bd30af8);
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffffffffffffff,0x4708fd1d49a240e8047cca68e2b902d9528690d5b30a54ae98ef0810e3d8078d);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffffffffffffff,0x1871c6e332a5196c95e2e5ece5202f0e3e487500e26ea89098ad6bb20815283f);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffffffffffffff,0xc2e403618925f6716b62058bf65f56ba5c250b4bfa9c33e606117002a009c64);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffffffffffffffffff,0x56a07718b3fd3192ac8020bbd4b54f4df397d79ef160a42155ada0e4fa5a712f);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffffffffffffffffff,0x453244418555930b8eded0a348cc6bd25ea64c7c684ad86e5edf0418647e1483);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffffffffffffffffff,0x236909bfd1f9b1b36201fbf7f2d5b32973dfa0f7f371f063d9abe52c1af57f25);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffffffffffffffffff,0xf2ec932d1797488b4f7d6595a03d1990d50adbab1caecd189996f1f577ec927);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffffffffffffffff,0x5cd15c90e265bbca9f47a190c451de7df4766e3cdbe0477c38edfef94db0585);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),P) != 0x36662b1935aeba2ed9ca4092a29ca8eaf63264a1de78bdf68209818eb72a1e18) {
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffffffffffffffff,0x3c553aaf846c54946229033406f32bb64864b3c04ad33daee227581bdaedcc7b);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffff,0x36c8d57fe59cf5b50131893beff5f19a251093de6f438d8e769dbe66d5998e86);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffff,0x6170fc5212282bff7bf89961957c7509ef0d26a1182e19b822f296a59008cf3c);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffffffffffffffffffff,0x7e31dcdea8843195c937622831b294ef2d7d252087fe190a58f2fcd28b830cf4);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffffffffffffffffffff,0x6caa96919a793352c65f64132a665a1887230380614199d0e087a9a94895b20);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffff,0x25e75686e9d058b44466fa9da9f7243791a29d901f525e7fa5764f717d9f2bea);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffff,0x6ffd4c7762b25e8052a138d8dd4c56a4a16b4c292c90e36b78f6e2cd4192683);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffffffffffffffffff,0x794c22ee8022654e58f5706e8a04cbfbe9de24a9846a8d69886836cd82670d3e);
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x546248644e74a05bf53648b6a2871cf2cdf3779360705d25ebeae1b79b7b2204);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x5a0070bbdbaec550c34d7320f42ef3be93e9e22958c18d4119cf570add2717b7);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x1987ba8628bb48bac640e8a86a9475a6b6c758838824607a5270f18bfa0a9fae);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x14368d620af9e06ea7258aad2cf532c97a181f3b9e5b997fc24a56ce9d0762ec);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xacbadb290a65f3a4834bee1aa9dd374b386c4dd6fa58e3e6acb980db153aeed);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x34b0237582fc32db8566225e50136ee4c161cbcfd89284ffe369393c3e6d952c);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x7d62b22f10521440e0413f6d168fa3039a2f3b8485961f5ae92b89fac7eca84e);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x2f20cd0b61a8f9d5f54493ef1a9bf3572691f44537768dc0394d1a9da50a5181);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)),P) != 0x7894996b30af4bcee3942feaeb7862c7a6d0ddafc3c3bb34cf47498e7e6e415c) {
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x36662b1935aeba2ed9ca4092a29ca8eaf63264a1de78bdf68209818eb72a1e18);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x747d8bb9c7f2923092d6c754ca769a7efecf88b29093813f9d5db39b09c9d62d);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x1b4256e64cccd5a646be516473d8a528fd8b0c0b8469e1a430e1f4a6fc1bb51f);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x5f3d73b11382bbf3bc19500498e41d4837b4f764c49f57ea2468b4039cf497);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x69a5f23f1a0449b1a391ccd60f956da930707f3378f6c03c2d3310d05ddf6fe0);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x2b1e68bccd8700dadc428a2a003bd709cdc40f60fe24ce63240205b8e4603beb);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x253392fca6d90387fcbc0a72674718f9a9033b76341157cd8ed443031c998804);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x484538b08925867f8331377131cb76ee94aa4bb0b07d610d78b6a5fc9d6ddfec);
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x535e83ebf0302eb958eb5bd781d648af9bd42d9771f1bf938d686dc874d77ea3);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x48cbdcee84fc53ac5e5ec953add55b257eb1f2e0b0859fd7da3242f4b58f4a7);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x2cc48846f44f9811078ed4f56630857241656016241e99536106b6a1afab0e2a);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x5e1ee569c6f05795cf0ef3a6086b1acf02d658e5238520e50defd5175652bc86);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0xc044534349a3c04887bdb6773ab62d7138332f7ddf2fc238833d5014dbeae58);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x4ae8ab606b45876d92567cbc10aac8f0ff97fa18606940a1d04c884af5795b39);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x710725894d325997603a56ef0998c9cd485ab6e2953f90ad0dceb0ef04813d3d);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x5f8d3e6839da7774898646dab878c348b669e49b6959a13450d0ba09f5f12cf3);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec)),P) != 0x1) {
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x7894996b30af4bcee3942feaeb7862c7a6d0ddafc3c3bb34cf47498e7e6e415c);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x5305614711bd445a0662d9534326de5c2d2e1a19210bd48a1981f8077e7f86e8);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x868f06590bdfc693d9e5133cacf0b5e3c5aa6e68ceeef57b33c556d993d05f1);
        exp_by_sq(P,g,0x7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x8779312ab35c954c3471c636fa99f2f0dae1343d935685a3a9c51f67b550086);
        exp_by_sq(P,g,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x27c4d02412c8b43b26650b2f6cf9526fbda8662a9aa6ddae1d1e93d9ead31626);
        exp_by_sq(P,g,0x1fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x4318c76c03527f54180d82e2b2c4d3840720d138a124a57cf83da4a363527785);
        exp_by_sq(P,g,0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x224c266e5e62e6688dce3bd1dc0985bd7d6d6ce48bead9727b81ed3b8adc8938);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x487c219ffb57031e21906f937a56ad0727008f9add2e939d7868beb22bf4d65b);
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x38c96be353a2528c9d770a44bbf1f49aa37ddc973af2cf88d745ed3e1e28b81d);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x394910df33187c3135f8ed9c8e2f9ca4b5e34655773473ddfc2d95fe064d642d);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff,0x7f8c93ad10b56258d55fdaeefe606340a2aeb27fcc09f34af495e0b5be4f023c);
        exp_by_sq(P,g,0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe,0x32c3972e911d2f7bb05f4b8c6db60e0038687a672696cc25eecf94076fb5c22b);
        exp_by_sq(P,g,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd,0x55c1924027e0ef8595a6804c9efdebd397a18c035697f23c62770d93a507504f);
        exp_by_sq(P,g,0x1ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb,0x2b8324804fc1df0b2b4d00993dfbd7a72f431806ad2fe478c4ee1b274a0ea0b0);
        exp_by_sq(P,g,0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff6,0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec);
        assert false;
    }

}

lemma void p25519_1_factors()
    requires true;
    ensures  product({2,2,3,65147,74058212732561358302231226437062788676166966415465897661863160754340907})
             +1
        ==   P25519;
{ p25519_formula(); }

lemma void p25519_65147_2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(65147-1)),65147) == 1;
{
    ALREADY_PROVEN()
    int P = 0xfe7b;
    int g = 2;
    note_eq(1,euclid_mod(pow_nat(g,nat_of_int(0)),P));

    if(euclid_mod(pow_nat(g,nat_of_int(0xfe7a)),P) != 0x1) {
        exp_by_sq(P,g,0x0,0x1);
        exp_by_sq(P,g,0x1,0x2);
        exp_by_sq(P,g,0x3,0x8);
        exp_by_sq(P,g,0x7,0x80);
        exp_by_sq(P,g,0xf,0x8000);
        exp_by_sq(P,g,0x1f,0xa84f);
        exp_by_sq(P,g,0x3f,0xdb67);
        exp_by_sq(P,g,0x7f,0xa3f7);
        exp_by_sq(P,g,0xfe,0xa);
        exp_by_sq(P,g,0x1fc,0x64);
        exp_by_sq(P,g,0x3f9,0x4e20);
        exp_by_sq(P,g,0x7f3,0xea53);
        exp_by_sq(P,g,0xfe7,0x65f5);
        exp_by_sq(P,g,0x1fcf,0x9c6c);
        exp_by_sq(P,g,0x3f9e,0xe5c9);
        exp_by_sq(P,g,0x7f3d,0xfe7a);
        assert false;
    }

    if(euclid_mod(pow_nat(g,nat_of_int(0xfe7a)),P) != 0x1) {
        assert false;
    }
}

lemma void p25519_65147_1_factors()
    requires true;
    ensures  product({2, 32573}) == 65147-1;
{}

lemma void p25519_65147_2_exact_order()
    requires true;
    ensures  !!forall({2, 32573},(pratt_pow_thing)(65147,2));
{
    ALREADY_PROVEN()

    int g = 2; int p = 65147; int q;
    q = 2;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0xfe7b));

        if(euclid_mod(pow_nat(2,nat_of_int(0x7f3d)),0xfe7b) != 0xfe7a) {
            exp_by_sq(0xfe7b,2,0x0,0x1);
            exp_by_sq(0xfe7b,2,0x1,0x2);
            exp_by_sq(0xfe7b,2,0x3,0x8);
            exp_by_sq(0xfe7b,2,0x7,0x80);
            exp_by_sq(0xfe7b,2,0xf,0x8000);
            exp_by_sq(0xfe7b,2,0x1f,0xa84f);
            exp_by_sq(0xfe7b,2,0x3f,0xdb67);
            exp_by_sq(0xfe7b,2,0x7f,0xa3f7);
            exp_by_sq(0xfe7b,2,0xfe,0xa);
            exp_by_sq(0xfe7b,2,0x1fc,0x64);
            exp_by_sq(0xfe7b,2,0x3f9,0x4e20);
            exp_by_sq(0xfe7b,2,0x7f3,0xea53);
            exp_by_sq(0xfe7b,2,0xfe7,0x65f5);
            exp_by_sq(0xfe7b,2,0x1fcf,0x9c6c);
            exp_by_sq(0xfe7b,2,0x3f9e,0xe5c9);
            assert false;
        }


        assert false;
    }

    q = 32573;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

        note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0xfe7b));

        if(euclid_mod(pow_nat(2,nat_of_int(0x2)),0xfe7b) != 0x4) {
            exp_by_sq(0xfe7b,2,0x0,0x1);
            exp_by_sq(0xfe7b,2,0x1,0x2);
            assert false;
        }


        assert false;
    }

}

lemma void p25519_32573_2_generates()
    requires true;
    ensures  euclid_mod(pow_nat(2,nat_of_int(32573-1)),32573) == 1;
{
    ALREADY_PROVEN()
    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x7f3d));

    if(euclid_mod(pow_nat(2,nat_of_int(0x7f3c)),0x7f3d) != 0x1) {
        exp_by_sq(0x7f3d,2,0x0,0x1);
        exp_by_sq(0x7f3d,2,0x1,0x2);
        exp_by_sq(0x7f3d,2,0x3,0x8);
        exp_by_sq(0x7f3d,2,0x7,0x80);
        exp_by_sq(0x7f3d,2,0xf,0xc3);
        exp_by_sq(0x7f3d,2,0x1f,0x2a98);
        exp_by_sq(0x7f3d,2,0x3f,0x2d0c);
        exp_by_sq(0x7f3d,2,0x7f,0x3c8f);
        exp_by_sq(0x7f3d,2,0xfe,0x4bd7);
        exp_by_sq(0x7f3d,2,0x1fc,0x1d2d);
        exp_by_sq(0x7f3d,2,0x3f9,0x24b5);
        exp_by_sq(0x7f3d,2,0x7f3,0x7139);
        exp_by_sq(0x7f3d,2,0xfe7,0x39e2);
        exp_by_sq(0x7f3d,2,0x1fcf,0x73c3);
        exp_by_sq(0x7f3d,2,0x3f9e,0x7f3c);
        assert false;
    }

}

lemma void p25519_32573_1_factors()
    requires true;
    ensures  product({2, 2, 17, 479}) == 32573-1;
{}

lemma void p25519_32573_2_exact_order()
    requires true;
    ensures  !!forall({2, 2, 17, 479},(pratt_pow_thing)(32573,2));
{
    ALREADY_PROVEN()
    int g = 2; int p = 32573; int q;
    q = 2;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x7f3d));

    if(euclid_mod(pow_nat(2,nat_of_int(0x3f9e)),0x7f3d) != 0x7f3c) {
        exp_by_sq(0x7f3d,2,0x0,0x1);
        exp_by_sq(0x7f3d,2,0x1,0x2);
        exp_by_sq(0x7f3d,2,0x3,0x8);
        exp_by_sq(0x7f3d,2,0x7,0x80);
        exp_by_sq(0x7f3d,2,0xf,0xc3);
        exp_by_sq(0x7f3d,2,0x1f,0x2a98);
        exp_by_sq(0x7f3d,2,0x3f,0x2d0c);
        exp_by_sq(0x7f3d,2,0x7f,0x3c8f);
        exp_by_sq(0x7f3d,2,0xfe,0x4bd7);
        exp_by_sq(0x7f3d,2,0x1fc,0x1d2d);
        exp_by_sq(0x7f3d,2,0x3f9,0x24b5);
        exp_by_sq(0x7f3d,2,0x7f3,0x7139);
        exp_by_sq(0x7f3d,2,0xfe7,0x39e2);
        exp_by_sq(0x7f3d,2,0x1fcf,0x73c3);
        assert false;
    }


        assert false;
    }

    q = 17;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x7f3d));

    if(euclid_mod(pow_nat(2,nat_of_int(0x77c)),0x7f3d) != 0x4d17) {
        exp_by_sq(0x7f3d,2,0x0,0x1);
        exp_by_sq(0x7f3d,2,0x1,0x2);
        exp_by_sq(0x7f3d,2,0x3,0x8);
        exp_by_sq(0x7f3d,2,0x7,0x80);
        exp_by_sq(0x7f3d,2,0xe,0x4000);
        exp_by_sq(0x7f3d,2,0x1d,0xaa6);
        exp_by_sq(0x7f3d,2,0x3b,0x22a0);
        exp_by_sq(0x7f3d,2,0x77,0x2288);
        exp_by_sq(0x7f3d,2,0xef,0x173a);
        exp_by_sq(0x7f3d,2,0x1df,0x6736);
        exp_by_sq(0x7f3d,2,0x3be,0x448c);
        assert false;
    }


        assert false;
    }

    q = 479;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(2,nat_of_int(0)),0x7f3d));

    if(euclid_mod(pow_nat(2,nat_of_int(0x44)),0x7f3d) != 0x29e1) {
        exp_by_sq(0x7f3d,2,0x0,0x1);
        exp_by_sq(0x7f3d,2,0x1,0x2);
        exp_by_sq(0x7f3d,2,0x2,0x4);
        exp_by_sq(0x7f3d,2,0x4,0x10);
        exp_by_sq(0x7f3d,2,0x8,0x100);
        exp_by_sq(0x7f3d,2,0x11,0x30c);
        exp_by_sq(0x7f3d,2,0x22,0x5646);
        assert false;
    }


        assert false;
    }

}

lemma void p25519_479_1_factors()
    requires true;
    ensures  product({2,239}) == 479-1;
{}

lemma void p25519_479_13_generates()
    requires true;
    ensures  euclid_mod(pow_nat(13,nat_of_int(479-1)),479) == 1;
{
    ALREADY_PROVEN()
    note_eq(1,euclid_mod(pow_nat(13,nat_of_int(0)),0x1df));

    if(euclid_mod(pow_nat(13,nat_of_int(0x1de)),0x1df) != 0x1) {
        exp_by_sq(0x1df,13,0x0,0x1);
        exp_by_sq(0x1df,13,0x1,0xd);
        exp_by_sq(0x1df,13,0x3,0x119);
        exp_by_sq(0x1df,13,0x7,0x1db);
        exp_by_sq(0x1df,13,0xe,0x10);
        exp_by_sq(0x1df,13,0x1d,0x1c6);
        exp_by_sq(0x1df,13,0x3b,0x1cd);
        exp_by_sq(0x1df,13,0x77,0x17c);
        exp_by_sq(0x1df,13,0xef,0x1de);
        assert false;
    }
}


lemma void p25519_479_13_exact_order()
    requires true;
    ensures  !!forall({2, 239},(pratt_pow_thing)(479,13));
{
    ALREADY_PROVEN()
    ALREADY_PROVEN()
    int g = 13; int p = 479; int q;
    q = 2;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(13,nat_of_int(0)),0x1df));

    if(euclid_mod(pow_nat(13,nat_of_int(0xef)),0x1df) != 0x1de) {
        exp_by_sq(0x1df,13,0x0,0x1);
        exp_by_sq(0x1df,13,0x1,0xd);
        exp_by_sq(0x1df,13,0x3,0x119);
        exp_by_sq(0x1df,13,0x7,0x1db);
        exp_by_sq(0x1df,13,0xe,0x10);
        exp_by_sq(0x1df,13,0x1d,0x1c6);
        exp_by_sq(0x1df,13,0x3b,0x1cd);
        exp_by_sq(0x1df,13,0x77,0x17c);
        assert false;
    }


        assert false;
    }

    q = 239;
    if(!pratt_pow_thing(p,g,q)) {
        pratt_pow_thing_auto(p,g,q);

    note_eq(1,euclid_mod(pow_nat(13,nat_of_int(0)),0x1df));

    if(euclid_mod(pow_nat(13,nat_of_int(0x2)),0x1df) != 0xa9) {
        exp_by_sq(0x1df,13,0x0,0x1);
        exp_by_sq(0x1df,13,0x1,0xd);
        assert false;
    }


        assert false;
    }

}

lemma pratt_cert p25519_479_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,479);
{
    close pratt_certificate(pratt_small(2),1,zero,2);

    p25519_479_13_generates();
    p25519_479_13_exact_order();
    close pratt_certificate(pratt_cert(13,{pair(2,pratt_small(2))}),239,N1,479);

    close pratt_certificate(pratt_small(239),1,N1,239);
    pratt_cert ret = pratt_certificate_build(13,{pair(2,pratt_small(2))}, 239, 479);
    return ret;
}

lemma pratt_cert p25519_32573_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,32573);
{
    p25519_32573_2_generates();
    p25519_32573_2_exact_order();
    list<pair<int,pratt_cert> > fact = {pair(2,pratt_small(2))};
    close pratt_certificate(pratt_small(2),1,zero,2);
    close pratt_certificate(pratt_cert(2,fact),32573/2,N1,32573);

    close pratt_certificate(pratt_small(2),1,zero,2);
    pratt_certificate_build(2,fact, 2, 32573);
    fact = cons(pair(2,pratt_small(2)),fact);

    close pratt_certificate(pratt_small(17),1,zero,17);
    pratt_certificate_build(2,fact, 17, 32573);
    fact = cons(pair(17,pratt_small(17)),fact);

    pratt_cert cert_479 = p25519_479_pratt();
    pratt_cert ret = pratt_certificate_build(2,fact, 479, 32573);

    return ret;
}

lemma pratt_cert p25519_65147_pratt()
    requires true;
    ensures  pratt_certificate(result,1,_,65147);
{
    p25519_65147_2_generates();
    p25519_65147_2_exact_order();
    list<pair<int,pratt_cert> > fact = {pair(2,pratt_small(2))};
    close pratt_certificate(pratt_small(2),1,zero,2);
    close pratt_certificate(pratt_cert(2,fact),65147/2,N1,65147);

    pratt_cert cert_32573 = p25519_32573_pratt();
    pratt_cert ret = pratt_certificate_build(2, fact, 32573, 65147);

    return ret;
}

  @*/

