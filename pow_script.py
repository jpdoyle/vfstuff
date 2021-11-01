{2, 3, 353, 57467, 132049, 1923133, 31757755568855353, 75445702479781427272750846543864801}

def prove_g(g,P,e):
    s = 0
    while e>>(s+1) > 0:
        s += 1
    print("    note_eq(1,euclid_mod(pow_nat({},nat_of_int(0)),{}));".format(g,hex(P)))
    print("")
    x = g
    pows = [(s+1,1),(s,g)]
    while s > 0:
        odd = (((e>>(s-1))&1) == 1)
        x1 = x*x
        if odd:
            x1 *= g
        r = x1%P
        q = x1//P
        x = r
        s -= 1
        pows.append((s,x))
    chunk_size = 16
    i = 0
    while chunk_size*i < len(pows):
        chunk = pows[i*chunk_size:(i+1)*chunk_size+1]
        final_s,final_x = chunk[-1]
        chunk = chunk[:-1]
        print("    if(euclid_mod(pow_nat({},nat_of_int({})),{}) != {}) {{".format(g,hex(e>>final_s),hex(P),hex(final_x)))
        for s,x in chunk:
            print("        exp_by_sq({},{},{},{});".format(hex(P),g,hex(e>>s),hex(x)))
        print("        assert false;")
        print("    }")
        print("")
        i += 1


        # print("    exp_by_sq(P,g,{},{});".format(hex(e>>s),hex(g)))

def prove_g(g,P,e):
 s = 0
 while e>>(s+1) > 0:
  s += 1
 print("    int r_prev;")
 print("    int r = {};".format(g))
 print("    fast_pow_base({}, {}, true, 1, r);".format(P,g))
 print("")
 x = g
 while s > 0:
  odd = (((e>>(s-1))&1) == 1)
  x1 = x*x
  if odd:
   x1 *= g
  r = x1%P
  q = x1//P
  print("")
  print("    r_prev = r;")
  print("    r = {};".format(r))
  print("    euclid_div_exact({}*r_prev*r_prev,{},{},r);".format((g if odd else 1),P,q))
  print("    fast_pow_step({}, {}, {}, nat_of_int({}), {}, r);".format(P, g, ("true" if odd else "false"), hex(e>>s), hex(e>>(s-1))))
  x = r
  s -= 1

def prove_factors(p,g,factors):
 print("    int g = {}; int p = {}; int q;".format(g,p))
 for q in factors:
  print("    q = {};".format(q))
  print("    if(!pratt_pow_thing(p,g,q)) {")
  print("        pratt_pow_thing_auto(p,g,q);")
  print("")
  prove_g(g,p,(p-1)//q)
  print("")
  print("        assert false;")
  print("    }")
  print("")




"""


>>> prove_factors(2773320623,10,sorted(list(set([2, 2437, 569003]))))
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

>>> prove_g(10,2773320623,2773320623-1)
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

>>> prove_factors(569003,2,sorted(list(set([2, 7, 97, 419]))))
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

>>> prove_g(2,569003,569003-1)
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

>>>

"""

