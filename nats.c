/*@ #include "nats.gh" @*/

/*@

lemma_auto(nat_minus(zero,n))
void nat_zero_minus(nat n)
    requires true;
    ensures  nat_minus(zero,n) == zero;
{ TRIVIAL_NAT(n) }

lemma_auto(nat_minus(n,zero))
void nat_minus_zero(nat n)
    requires true;
    ensures  nat_minus(n,zero) == n;
{ TRIVIAL_NAT(n) }


lemma void nat_plus_deconstruct(nat n, nat m)
    requires true;
    ensures  nat_plus(succ(n),m) == succ(nat_plus(n,m))
        &*&  nat_plus(n,succ(m)) == succ(nat_plus(n,m))
        ;
{ NAT_INDUCTION(n,n0,nat_plus_deconstruct(n0,succ(m))) }

lemma_auto(nat_plus(succ(n),m)) void nat_plus_deconstruct_auto_l(nat n, nat m)
    requires true;
    ensures  nat_plus(succ(n),m) == succ(nat_plus(n,m))
        &&  nat_plus(n,succ(m)) == succ(nat_plus(n,m))
        ;
{ nat_plus_deconstruct(n,m); }

lemma_auto(nat_plus(n,succ(m))) void nat_plus_deconstruct_auto_r(nat n, nat m)
    requires true;
    ensures  nat_plus(succ(n),m) == succ(nat_plus(n,m))
        &&  nat_plus(n,succ(m)) == succ(nat_plus(n,m))
        ;
{ nat_plus_deconstruct(n,m); }

lemma void nat_plus_assoc(nat l, nat n, nat m)
    requires true;
    ensures  nat_plus(l,nat_plus(n,m)) == nat_plus(nat_plus(l,n),m);
{ NAT_INDUCTION(l,l0,nat_plus_assoc(l0,n,m)) }

lemma_auto(nat_plus(n,zero)) void nat_plus_zero(nat n)
    requires true;
    ensures  nat_plus(n,zero) == n;
{ NAT_INDUCTION(n,n0,nat_plus_zero(n0)) }

lemma_auto(nat_plus(n,m)) void nat_plus_comm(nat n, nat m)
    requires true;
    ensures  nat_plus(n,m) == nat_plus(m,n);
{ NAT_INDUCTION(n,n0,nat_plus_comm(n0,m)) }

lemma_auto(nat_plus(n,m))
void nat_plus_int_of_nat(nat n, nat m)
    requires true;
    ensures  nat_plus(n,m) == noi(ion(n)+ion(m));
{ NAT_INDUCTION(n,n0,nat_plus_int_of_nat(n0,m)) }


lemma_auto(noi(length(cons(x,xs)))) void nat_of_int_of_length<t>(t x, list<t> xs)
    requires true;
    ensures noi(length(cons(x,xs))) == succ(noi(length(xs)));
{ }

lemma_auto(noi(length(append(a,b)))) void nat_of_int_of_length_append<t>(list<t> a, list<t> b)
    requires true;
    ensures noi(length(append(a,b))) ==
        nat_plus(noi(length(a)),noi(length(b)));
{
    switch(a) {
    case nil:
    case cons(x,xs):
        nat_of_int_of_length_append(xs,b);
    }
}

lemma_auto(noi(x)) void nat_of_int_auto(int x)
    requires x > 0;
    ensures  (noi(x) != zero);
{
    assert noi(x) == succ(noi(x-1));
}

lemma void pow10_distrib(int x, int y, nat n)
    requires true;
    ensures  timespow10(x+y,n) == timespow10(x,n) + timespow10(y,n);
{
    switch(n) {
    case zero: return;
    case succ(n0):
        assert timespow10(x+y,n) == 10*timespow10(x+y,n0);

        pow10_distrib(x,y,n0);

        assert timespow10(x+y,n) == 10*(timespow10(x,n0) + timespow10(y,n0));
        assert timespow10(x+y,n) == 10*timespow10(x,n0) + 10*timespow10(y,n0);
        assert timespow10(x+y,n) == timespow10(x,n) + timespow10(y,n);
    }
}

lemma void pow10_mult(int x, nat n)
    requires true;
    ensures  timespow10(10*x,n) == timespow10(x,succ(n));
{
    switch(n) {
    case zero: return;
    case succ(n0):
        pow10_mult(x,n0);
        assert timespow10(x,succ(n)) == 10*timespow10(x,n);
        assert timespow10(x,succ(n)) == 10*timespow10(10*x,n0);
        assert timespow10(x,succ(n)) == timespow10(10*x,n);
    }
}

@*/

