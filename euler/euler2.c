/*@ #include <listex.gh> @*/
/*@ #include "../util.gh" @*/
/*@ #include "../lists.gh" @*/
/*@ #include "../math.gh" @*/
#include <stdio.h>

/*@

fixpoint bool is_even(int x) { return x%2 == 0; }

fixpoint list<int> fibFrom(int f0, int f1, nat n) {
    switch(n) {
    case zero: return {};
    case succ(n0):
        return cons(f0,fibFrom(f1,f0+f1,n0));
    }
}

lemma_auto(length(fibFrom(x,y,n)))
void fibFrom_length(int x, int y, nat n)
    requires true;
    ensures  length(fibFrom(x,y,n)) == ion(n);
{ NAT_INDUCTION(n,n0,fibFrom_length(y,x+y,n0)) }

lemma void even_fib_likelihood_core(int f0, int f1, nat n)
    requires f0 >= 0 &*& f1 >= 0 &*& ((f0%2 != 0) || (f1%2 != 0))
        &*&  let((f0%2 == 0) ? 0 :
                 (f1%2 == 0) ? 1 : 2, ?firstEvenInd)
        ;
    ensures  (ion(n)-firstEvenInd+2)/3
        ==   length(filter(is_even,fibFrom(f0,f1,n)))
        ;
{
    switch(n) {
    case zero:

        assert abs(ion(n) - firstEvenInd + 2) < abs(3);
        division_unique((ion(n)-firstEvenInd+2),3,0,
            2-firstEvenInd);

    case succ(n0):
        if(ion(n) <= firstEvenInd) {
            division_unique((ion(n)-firstEvenInd+2),3,0,
                ion(n)+2-firstEvenInd);
            switch(n0) {
            case zero:
            case succ(n1):
                assert n == succ(succ(n1));
                switch(n1) {
                case zero:
                case succ(n2):
                    switch(n2) {
                    case zero:
                    case succ(n3):
                        assert false;
                    }

                }
            }
            return;

        }

        close let((f1%2 == 0) ? 0 :
                 ((f0+f1)%2 == 0) ? 1 : 2, ?newEvenInd);
        div_rem(f0,2);
        div_rem(f1,2);
        div_rem(f0+f1,2);

        assert ion(n) == 1+ion(n0);

        if(f0%2 == 0) {
            assert f1%2 != 0;
            assert f0+f1 == 2*((f0+f1)/2)+(f0+f1)%2;
            assert f0 + f1 == 2*(f0/2)+2*(f1/2)+f1%2;
            assert f0 + f1 == 2*((f0/2)+(f1/2))+f1%2;
            division_unique(f0+f1,2,f0/2+f1/2,f1%2);
            assert (f0+f1)%2 != 0;

            assert newEvenInd == 2;

        } else if(f1%2 == 0) {
            assert f0%2 != 0;
            division_unique(f0+f1,2,f0/2+f1/2,f0%2);
            assert (f0+f1)%2 != 0;
        } else {
            if(f0%2 < 1) { assert false; }
            if(f1%2 < 1) { assert false; }

            assert f0%2+f1%2 == 2;
            division_unique(f0+f1,2,f0/2+f1/2+1,0);

            assert (f0+f1)%2 == 0;
        }
        even_fib_likelihood_core(f1,f0+f1,n0);

        assert (ion(n0)-newEvenInd+2)/3
            == length(filter(is_even,fibFrom(f1,f0+f1,n0)));

        if(f0%2 == 0) {
            assert (ion(n0)-newEvenInd+2)/3
                == length(filter(is_even,fibFrom(f1,f0+f1,n0)));
            assert length(filter(is_even,fibFrom(f0,f1,n)))
                == 1 + length(filter(is_even,fibFrom(f1,f0+f1,n0)));
            assert length(filter(is_even,fibFrom(f0,f1,n)))
                == 1 + (ion(n0)-newEvenInd+2)/3;
            assert length(filter(is_even,fibFrom(f0,f1,n)))
                == 1 + (ion(n0))/3;
            into_numerator(1,ion(n0)-newEvenInd+2,3);
            assert length(filter(is_even,fibFrom(f0,f1,n)))
                == (3 + ion(n0))/3;
            assert length(filter(is_even,fibFrom(f0,f1,n)))
                == (ion(n)+2)/3;

        }

    }
}

//lemma void even_fib_likelihood(int f0, int f1, nat n)
//    //requires (f0%2 != 0) || (f1%2 != 0);
//    requires f0 >= 0 &*& f1 >= 0 &*& ((f0%2 != 0) || (f1%2 != 0));
//    ensures  3*length(filter(is_even,fibFrom(f0,f1,n)))
//        >=   length(fibFrom(f0,f1,n))
//        ;
//{
//    even_fib_likelihood_core(f0,f1,n);
//    fibFrom_length(f0,f1,n);
//    div_rem(ion(n),3);
//    div_rem(ion(n),3);
//}


  @*/

