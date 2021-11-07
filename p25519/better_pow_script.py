# attach("p25519/better_pow_script.py")

def my_ceil_log2(x):
    acc = 2
    ret = 1
    while acc < x:
        acc *= acc
        ret *= 2
    # if ret == 256:
    #     for i in [160,192]:
    #         if 2**i >= x:
    #             return i
    # if ret == 128 and 2**40 >= x:
    #     return i
    return ret

def prove_generates(P,g):
    print("lemma void p25519_{}_g{}_generates()".format(P,g))
    print("    requires true;")
    print("    ensures  euclid_mod(pow_nat({},nat_of_int({})),{}) == 1;"
            .format(g,P-1,P))
    print("{")
    lg = my_ceil_log2(P-1)
    # if lg > 100:
    #     print("    DECLARE_{}_NATS(zero,0)".format(lg))

    print("    if(euclid_mod(pow_nat({},nat_of_int({})),{}) != 1) {{"
            .format(g,P-1,P))
    print("        MODPOW_FULL({},{},{},{})"
            .format(P,g,P-1,lg))
    print("        assert false;")
    print("    }")
    print("}")
    print("")

def prove_factors(P,g,qs):
    assert product(qs) == P-1;
    for q in sorted(set(qs)):
        assert is_prime(q)

    print("lemma void p25519_{}_1_factors()".format(P))
    print("    requires true;")
    print("    ensures  product({{{}}}) + 1 == {};"
        .format(", ".join(map(str,qs)), P))
    print("{}")
    print("")

def prove_exact_order(P,g,qs):
    assert product(qs) == P-1;

    print("lemma void p25519_{}_g{}_exact_order()".format(P,g))
    print("    requires true;")
    print("    ensures  !!forall({{{}}}, (pratt_pow_thing)({},{}));"
            .format(", ".join(map(str,qs)),P,g))
    print("{")
    print("    if(!forall({{{}}}, (pratt_pow_thing)({},{}))) {{"
            .format(", ".join(map(str,qs)),P,g))
    lgs = (my_ceil_log2((P-1)/q) for q in qs)
    lg = max(lgs)
    # if lg > 100:
    #     print("    DECLARE_256_NATS(zero,0)")
    print("        int g = {}; int P = {};".format(g,P))
    for q in sorted(set(qs))[::-1]:
        this_lg = my_ceil_log2((P-1)/q)

        if this_lg > 2:
            print("        PRATT_FACTOR(P,g,{},{})"
                    .format(q,this_lg))
        else:
            print("        if(!pratt_pow_thing(P,g,{})) {{".format(q))
            print("            pratt_pow_thing_auto(P,g,{});".format(q))
            print("            assert false;")
            print("        }")

    print("        assert false;")
    print("    }")

    print("}")
    print("")

def prove_pratt(P,g,qs):
    print("lemma pratt_cert p25519_{}_pratt()".format(P))
    print("    requires true;")
    print("    ensures  pratt_certificate(result,1,_,{});".format(P))
    print("{")
    print("    PRATT_BUILD_PRELUDE({},{})".format(P,g))
    for q in sorted(qs)[::-1]:
        if q <= 100*100:
            print("    PRATT_BUILD_SMALL({})".format(q))
        else:
            print("    PRATT_BUILD_BIG({})".format(q))
    print("    return ret;")
    print("}")
    print("")

def pratt_cert(P,known_primes,qs=None):
    if P in known_primes:
        return
    if P <= 100*100:
        return

    assert is_prime(P)

    if qs is None:
        qs = ecm.factor(P-1)
    if qs is None:
        qs = qsieve(P-1)
    assert product(qs) == P-1

    g = 1
    good_g = False
    while not good_g:
        g += 1
        if power_mod(g,P-1,P) != 1:
            continue

        bad_g = False
        for q in sorted(set(qs)):
            e = int((P-1)/q)
            assert e*q == P-1
            if power_mod(g,e,P) == 1:
                bad_g = True
                break
        if bad_g:
            continue

        good_g = True

    for q in sorted(set(qs)):
        pratt_cert(q,known_primes)
        known_primes.add(q)

    prove_generates(P,g)
    prove_factors(P,g,qs)
    prove_exact_order(P,g,qs)
    prove_pratt(P,g,qs)

