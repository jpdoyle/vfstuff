#include <stdlib.h>
/*@ #include <nat.gh> @*/
/*@ #include "termination.gh" @*/


/***********************************************************
 * Hello! 
 **********************************************************/

/*@ // First, an abstract representation of lambda terms

inductive lambda<t>
    = lamb_symbol(t)                // constant symbols
    | lamb_var(nat)                 // DeBruijn-indexed variables
    | lamb_fn(lambda<t>)            // \x -> E
    | lamb_app(lambda<t>,lambda<t>) // E1 E2
    ;

fixpoint int lambda_depth<t>(lambda<t> term) {
    switch(term) {
    case lamb_symbol(x): return 0;
    case lamb_var   (i): return 0;
    case lamb_fn    (E): return 1+lambda_depth(E);
    case lamb_app   (E1,E2):
        return 1+max_of(lambda_depth(E1),lambda_depth(E2));
    }
}

lemma_auto(lambda_depth(term))
void lambda_depth_nonneg<t>(lambda<t> term)
    requires true;
    ensures  lambda_depth(term) >= 0;
{
    switch(term) {
    case lamb_symbol(x):
    case lamb_var   (i):
    case lamb_fn    (E): lambda_depth_nonneg(E);
    case lamb_app   (E1,E2):
        lambda_depth_nonneg(E1);
        lambda_depth_nonneg(E2);
    }
}

fixpoint bool valid_lambda<t>(lambda<t> term, nat depth) {
    switch(term) {
    case lamb_symbol(x): return true;
    case lamb_var   (i): return ion(i) < ion(depth);
    case lamb_fn    (E): return valid_lambda(E,succ(depth));
    case lamb_app   (E1,E2):
        return valid_lambda(E1,depth)
            && valid_lambda(E2,depth);
    }
}

fixpoint bool valid_combinator<t>(lambda<t> term) {
    return valid_lambda(term,zero);
}

fixpoint bool lambda_is_reduced<t>(lambda<t> term) {
    switch(term) {
    case lamb_symbol(x): return true;
    case lamb_var   (i): return true;
    case lamb_fn    (E): return lambda_is_reduced(E);
    case lamb_app   (E1,E2):
        return false;
    }
}

fixpoint lambda<t> lambda_subst<t>(
        lambda<t> E, nat ind, lambda<t> v) {
    switch(E) {
    case lamb_symbol(x):   return E;
    case lamb_var   (i):   return (i == ind ? v : E);
    case lamb_fn    (fnE):
        return lamb_fn(lambda_subst(fnE, succ(ind), v));
    case lamb_app   (E1,E2):
        return lamb_app(lambda_subst(E1,ind,v),
                        lambda_subst(E2,ind,v));
    }
}

fixpoint option<lambda<t> > lambda_step<t>(lambda<t> term) {
    switch(term) {
    case lamb_symbol(x): return none;
    case lamb_var   (i): return none;
    case lamb_fn    (E):
        return switch(lambda_step(E)) {
        case none:       return none;
        case some(newE): return some(lamb_fn(newE));
        };
    case lamb_app   (E1,E2):
        return some(lambda_subst(E1,zero,E2));
    }
}

lemma void lambda_step_reduced<t>(lambda<t> term, nat n)
    requires !!valid_lambda(term,n);
    ensures  (lambda_step(term) == none)
        ==   lambda_is_reduced(term);
{
    switch(term) {
    case lamb_symbol(x):
    case lamb_var   (i):
    case lamb_fn    (E):
        lambda_step_reduced(E,succ(n));
        switch(lambda_step(E)) {
        case none:
        case some(newE):
        }
    case lamb_app   (E1,E2):
    }
}

lemma_auto(lambda_depth(lambda_subst(E,ind,v)))
void lambda_subst_depth<t>(lambda<t> E, nat ind, lambda<t> v)
    requires true;
    ensures  lambda_depth(lambda_subst(E,ind,v))
        <=   lambda_depth(E) + lambda_depth(v);
{
    switch(E) {
    case lamb_symbol(x):
    case lamb_var   (i):
    case lamb_fn    (fnE):
        lambda_subst_depth(fnE,succ(ind),v);
    case lamb_app   (E1,E2):
        lambda_subst_depth(E1,ind,v);
        lambda_subst_depth(E2,ind,v);
    }
}

  @*/

/* Next, the C representation of these things. Because of some
 * current limitations of VeriFast (ie. `union` support), we can't
 * implement this sum type using a tagged union directly. Also,
 * because of limitations of C, we'll need extra invariants to
 * guarantee that the `tag` field is valid.
 */

typedef enum LambdaTag {
    LambSymbol,
    LambVar,
    LambFn,
    LambApp
} LambdaTag;

struct LambdaTerm;

typedef struct LambdaSymbol {
    intptr_t val;
} LambdaSymbol;

typedef struct LambdaVar {
    uintptr_t var_ix;
} LambdaVar;

typedef struct LambdaFn {
    struct LambdaTerm* body;
} LambdaFn;

typedef struct LambdaApp {
    struct LambdaTerm* fn;
    struct LambdaTerm* param;
} LambdaApp;

union UntaggedLambdaTerm {
    LambdaSymbol symb;
    LambdaVar    var;
    LambdaFn     fn;
    LambdaApp    app;
};

typedef struct LambdaTerm {
    LambdaTag tag;
    union UntaggedLambdaTerm term;
} LambdaTerm;

/*@

// This is necessary because types mean basically nothing in C :(
fixpoint bool valid_LambdaTag(LambdaTag t) {
    return t == LambSymbol || t == LambVar
        || t == LambFn     || t == LambApp;
}

// The parameters after the ; are "output parameters" -- specifically,
// proof information which can be extracted purely from the "input
// parameters" and the current heap state. In this case, if there is a
// valid lambda term at the location `term` refers to, we can extract
// the abstract `lambda<int>` value it represents.
predicate valid_LambdaTerm(LambdaTerm* term, nat depth;
                           lambda<int> abstractVal)
    =   malloc_block_LambdaTerm(term)
    &*& term != 0
    &*& term->tag  |-> ?tag &*& !!valid_LambdaTag(tag)
    &*& (  (tag == LambSymbol)
            ? (     term->term.symb.val |-> ?val
                &*& struct_LambdaSymbol_padding(&term->term.symb)
                &*& chars((void*)&term->term + sizeof(LambdaSymbol),
                        sizeof(union UntaggedLambdaTerm)\
                            - sizeof(LambdaSymbol),_)
                &*& abstractVal == lamb_symbol(val)
              )
         : (tag == LambVar)
            ? (     term->term.var.var_ix |-> ?var_ix
                &*& struct_LambdaVar_padding(&term->term.var)
                &*& chars((void*)&term->term + sizeof(LambdaVar),
                        sizeof(union UntaggedLambdaTerm)
                            - sizeof(LambdaVar),_)
                &*& var_ix < ion(depth)
                &*& abstractVal == lamb_var(noi(var_ix))
              )
         : (tag == LambFn)
            ? (     term->term.fn.body |-> ?body
                &*& struct_LambdaFn_padding(&term->term.fn)
                &*& chars((void*)&term->term
                            + sizeof(LambdaFn),
                        sizeof(union UntaggedLambdaTerm)
                            - sizeof(LambdaFn),
                        _)
                &*& valid_LambdaTerm(body, succ(depth), ?innerVal)
                &*& abstractVal == lamb_fn(innerVal)
              )
         : (tag == LambApp) &*&
              (     term->term.app.fn |-> ?fn
                &*& term->term.app.param |-> ?param
                &*& struct_LambdaApp_padding(&term->term.app)
                &*& chars((void*)&term->term + sizeof(LambdaApp),
                        sizeof(union UntaggedLambdaTerm)
                            - sizeof(LambdaApp),
                        _)
                &*& valid_LambdaTerm(fn, depth, ?E1)
                &*& valid_LambdaTerm(param, depth, ?E2)
                &*& abstractVal == lamb_app(E1,E2)
              )
        )
    &*& ion(depth) + lambda_depth(abstractVal) <= UINTPTR_MAX
    ;

// As both a sanity check and a convenience, we can prove that any
// structure in memory matching the `valid_LambdaTerm` predicate will
// have a valid corresponding lambda term. By declaring a version as
// `lemma_auto`, this lemma will be automatically applied whenever a
// `valid_LambdaTerm` predicate is generated. The `lemma_auto` version
// is implemented separately due to some reasonable-but-annoying
// restrictions in VeriFast's implementation.
lemma
void valid_LambdaTerm_auto_inner(LambdaTerm* term)
    requires [?f]valid_LambdaTerm( term, ?depth, ?val);
    ensures  [ f]valid_LambdaTerm( term,  depth,  val)
        &*&  term != 0
        &*&  !!valid_lambda(val,depth)
        &*&  ion(depth) + lambda_depth(val) <= UINTPTR_MAX
        ;
{
    if(ion(depth) + lambda_depth(val) > UINTPTR_MAX) {
        open valid_LambdaTerm(_,_,_);
        assert false;
    }
    if(!valid_lambda(val,depth) || term == 0) {
        open valid_LambdaTerm(_,_,_);
        assert [f]term->tag  |-> ?tag;
        if(tag == LambFn) {
            assert [f]term->term.fn.body |-> ?body;
            valid_LambdaTerm_auto_inner(body);
        } else if(tag == LambApp) {
            assert [f]term->term.app.fn |-> ?fn;
            assert [f]term->term.app.param |-> ?param;
            valid_LambdaTerm_auto_inner(fn);
            valid_LambdaTerm_auto_inner(param);
        }
        assert false;
    }
}

lemma_auto
void valid_LambdaTerm_auto()
    requires [?f]valid_LambdaTerm(?term, ?depth, ?val);
    ensures  [ f]valid_LambdaTerm( term,  depth,  val)
        &*&  term != 0
        &*&  !!valid_lambda(val,depth)
        &*&  ion(depth) + lambda_depth(val) <= UINTPTR_MAX
        ;
{ valid_LambdaTerm_auto_inner(term); }

lemma void raiseLambdaTermDepth(LambdaTerm* t, nat depth)
    requires [?f]valid_LambdaTerm(t,?oldDepth,?val)
        &*&  ion(depth) >= ion(oldDepth)
        &*&  ion(depth) + lambda_depth(val) <= UINTPTR_MAX
        ;
    ensures  [ f]valid_LambdaTerm(t,depth,val);
{
    open valid_LambdaTerm(t,_,_);

    assert [f]t->tag |-> ?tag;
    if(tag == LambFn) {
        assert [f]t->term.fn.body |-> ?body;
        raiseLambdaTermDepth(body,succ(depth));
    } else if(tag == LambApp) {
        assert [f]t->term.app.fn |-> ?fn;
        assert [f]t->term.app.param |-> ?param;
        raiseLambdaTermDepth(fn,depth);
        raiseLambdaTermDepth(param,depth);
    }

    close  [ f]valid_LambdaTerm(t,depth,val);
}

lemma void valid_LambdaTerm_unique(LambdaTerm* t1, LambdaTerm* t2)
    requires [?f1]valid_LambdaTerm(t1,?d1,?v1)
        &*&  [?f2]valid_LambdaTerm(t2,?d2,?v2)
        ;
    ensures  [ f1]valid_LambdaTerm(t1, d1, v1)
        &*&  [ f2]valid_LambdaTerm(t2, d2, v2)
        &*&  (f1 + f2 <= 1 ? emp : t1 != t2)
        ;
{
    if(f1 + f2 > 1 && t1 == t2) {
        assert &t1->tag == &t2->tag;
        open LambdaTerm_tag(t1,_);
        open LambdaTerm_tag(t2,_);
        integer_unique(&t1->tag);
        assert false;
    }
}

  @*/

/* Now that we have the preliminaries, I have some slightly bad news.
 *
 * Verifast is quite good at handling termination-checking of
 * recursive lemmas and `fixpoint`s -- `fixpoint`s must be
 * structurally recursive in a fairly naive way, and lemmas have
 * several ways of being shown to terminate, including my favorite --
 * by performing the recursive call with some element of an `open`ed
 * precondition.
 *
 * Termination is an utter necessity for fixpoints and lemmas, because
 * it guarantees that fixpoints can be replaced with their bodies, and
 * lemmas can be treated as inductive proofs. In contrast, this is not
 * a property available in Haskell -- even ignoring `undefined`,
 * Haskell allows many and sundry kinds of infinite (coinductive)
 * data, meaning that in many cases your program isn't *quite* the
 * proof you thought it was.
 *
 * Termination is also a nice property to have in the code itself -- 
 */

LambdaTerm* newLambdaTerm()
    /*@ requires true; @*/
    /*@ ensures  valid_LambdaTerm(result,zero,lamb_symbol(0)); @*/
    /*@ terminates; @*/
{
    LambdaTerm* ret = malloc(sizeof(LambdaTerm));
    if(!ret) { abort(); }
    ret->tag  = LambSymbol;
    /*@ close_struct(&ret->term.symb); @*/
    ret->term.symb.val = 0;
    return ret;
}

typedef LambdaTerm* cloneLambdaTerm_inner_t(const LambdaTerm* term);
    /*@ requires [?f]valid_LambdaTerm(term,?depth,?val)
            &*&  [2]call_perm_level(currentThread,pair(lt, lambda_depth(val)),
                    {cloneLambdaTerm_inner})
            ;
      @*/
    /*@ ensures  [ f]valid_LambdaTerm(term, depth, val)
            &*&  valid_LambdaTerm(result,depth,val)
            ;
      @*/
    /*@ terminates; @*/

LambdaTerm* cloneLambdaTerm_inner(const LambdaTerm* term)
        /*@ : cloneLambdaTerm_inner_t @*/
    /*@ requires [?f]valid_LambdaTerm(term,?depth,?val)
            &*&  [2]call_perm_level(currentThread,pair(lt, lambda_depth(val)),
                    {cloneLambdaTerm_inner})
            ;
      @*/
    /*@ ensures  [ f]valid_LambdaTerm(term, depth, val)
            &*&  valid_LambdaTerm(result,depth,val)
            ;
      @*/
    /*@ terminates; @*/
{
    cloneLambdaTerm_inner_t* rec = cloneLambdaTerm_inner;
    /*@ {
        is_wf_lt();
        open valid_LambdaTerm(term,_,_);
    } @*/

    LambdaTerm* ret = newLambdaTerm();

    ret->tag = term->tag;
    /*@ open_struct(&ret->term.symb); @*/
    /*@ chars_join((void*)&ret->term.symb); @*/

    switch(term->tag) {
    case LambSymbol:
        /*@ close_struct(&ret->term.symb); @*/
        ret->term.symb.val = term->term.symb.val;
        /*@ leak [2]call_perm_level(currentThread,_,_); @*/
        break;

    case LambVar:
        /*@ close_struct(&ret->term.var); @*/
        ret->term.var.var_ix = term->term.var.var_ix;
        /*@ leak [2]call_perm_level(currentThread,_,_); @*/
        break;

    case LambFn:
        /*@ close_struct(&ret->term.fn); @*/
        /*@ {
            assert [f]term->term.fn.body |-> ?body;
            assert [f]valid_LambdaTerm(body,_,?innerVal);
            assert lambda_depth(val) == 1 + lambda_depth(innerVal);
            assert !!lt(lambda_depth(innerVal),lambda_depth(val));
            call_perm_level_weaken(2,lt,lambda_depth(val),
                {cloneLambdaTerm_inner}, 3,lambda_depth(innerVal));
            consume_call_perm_level_for(cloneLambdaTerm_inner);
        } @*/
        {
            LambdaTerm* E = rec(term->term.fn.body);
            ret->term.fn.body = E;
        }
        break;

    case LambApp:
        /*@ close_struct(&ret->term.app); @*/
        /*@ {
            assert [f]term->term.app.fn |-> ?fn;
            assert [f]term->term.app.param |-> ?param;
            assert [f]valid_LambdaTerm(fn,_,?innerE1);
            assert [f]valid_LambdaTerm(param,_,?innerE2);
            call_perm_level_weaken(1,lt,lambda_depth(val),
                {cloneLambdaTerm_inner}, 3,lambda_depth(innerE1));
            consume_call_perm_level_for(cloneLambdaTerm_inner);
            call_perm_level_weaken(1,lt,lambda_depth(val),
                {cloneLambdaTerm_inner}, 3,lambda_depth(innerE2));
            consume_call_perm_level_for(cloneLambdaTerm_inner);
        } @*/
        {
            LambdaTerm* E1 = rec(term->term.app.fn);
            LambdaTerm* E2 = rec(term->term.app.param);
            ret->term.app.fn = E1;
            ret->term.app.param = E2;
        }
        break;
    default:
        /*@ assert false; @*/
        abort();
    }
    return ret;
}

LambdaTerm* cloneLambdaTerm(const LambdaTerm* term)
    /*@ requires [?f]valid_LambdaTerm(term,?depth,?val)
            ;
      @*/
    /*@ ensures  [ f]valid_LambdaTerm(term, depth, val)
            &*&  valid_LambdaTerm(result,depth,val)
            ;
      @*/
    /*@ terminates; @*/
{
    /*@ {
        produce_call_below_perm_();
        call_below_perm__elim(cloneLambdaTerm);
        call_perm_level(2, pair(lt,lambda_depth(val)),
            {cloneLambdaTerm_inner});
    } @*/
    return cloneLambdaTerm_inner(term);
}

typedef LambdaTerm* lambdaSubst_inner_t(const LambdaTerm* term,
        uintptr_t ind, const LambdaTerm* v);
    /*@ requires [?tf]valid_LambdaTerm(term,?depth,?t_val)
            &*&  ind >= 0
            &*&  ion(depth) > ind
            &*&  [?vf]valid_LambdaTerm(v,zero,?v_val)
            &*&  [2]call_perm_level(currentThread,pair(lt, lambda_depth(t_val)),
                    {lambdaSubst_inner})
            &*&  ion(depth) +
                    lambda_depth(lambda_subst(t_val,noi(ind),
                                 v_val)) <= UINTPTR_MAX
            ;
      @*/
    /*@ ensures  [ tf]valid_LambdaTerm(term, depth, t_val)
            &*&  [ vf]valid_LambdaTerm(v,zero, v_val)
            &*&  valid_LambdaTerm(result, depth,
                    lambda_subst(t_val,noi(ind),v_val))
            ;
      @*/
    /*@ terminates; @*/

LambdaTerm* lambdaSubst_inner(const LambdaTerm* term, uintptr_t ind,
        const LambdaTerm* v) /*@ : lambdaSubst_inner_t @*/
    /*@ requires [?tf]valid_LambdaTerm(term,?depth,?t_val)
            &*&  ind >= 0
            &*&  ion(depth) > ind
            &*&  [?vf]valid_LambdaTerm(v,zero,?v_val)
            &*&  [2]call_perm_level(currentThread,pair(lt, lambda_depth(t_val)),
                    {lambdaSubst_inner})
            &*&  ion(depth) +
                    lambda_depth(lambda_subst(t_val,noi(ind),
                                 v_val)) <= UINTPTR_MAX
            ;
      @*/
    /*@ ensures  [ tf]valid_LambdaTerm(term, depth, t_val)
            &*&  [ vf]valid_LambdaTerm(v,zero, v_val)
            &*&  valid_LambdaTerm(result, depth,
                    lambda_subst(t_val,noi(ind),v_val))
            ;
      @*/
    /*@ terminates; @*/
{
    lambdaSubst_inner_t* rec = lambdaSubst_inner;
    /*@ {
        is_wf_lt();
        open valid_LambdaTerm(term,_,_);
    } @*/

    LambdaTerm* ret = newLambdaTerm();

    ret->tag = term->tag;
    /*@ open_struct(&ret->term.symb); @*/
    /*@ chars_join((void*)&ret->term.symb); @*/

    switch(term->tag) {
    case LambSymbol:
        /*@ close_struct(&ret->term.symb); @*/
        ret->term.symb.val = term->term.symb.val;
        /*@ leak [2]call_perm_level(_,_,_); @*/
        break;

    case LambVar:
        if(term->term.var.var_ix == ind) {
            /*@ {
                assert t_val == lamb_var(noi(ind));
                assert lambda_subst(t_val,noi(ind),v_val)
                    == v_val;
            } @*/
            free(ret);
            ret = cloneLambdaTerm(v);
            /*@ raiseLambdaTermDepth(ret,depth); @*/
        } else {
            /*@ close_struct(&ret->term.var); @*/
            ret->term.var.var_ix = term->term.var.var_ix;
        }
        /*@ leak [2]call_perm_level(_,_,_); @*/
        break;

    case LambFn:
        /*@ close_struct(&ret->term.fn); @*/
        /*@ {
            assert [tf]term->term.fn.body |-> ?body;
            assert [tf]valid_LambdaTerm(body,_,?innerVal);
            call_perm_level_weaken(2,lt,lambda_depth(t_val),
                {lambdaSubst_inner}, 3,lambda_depth(innerVal));
            consume_call_perm_level_for(lambdaSubst_inner);
        } @*/
        {
            LambdaTerm* E = rec(term->term.fn.body,ind+1,v);
            ret->term.fn.body = E;
        }
        break;

    case LambApp:
        /*@ close_struct(&ret->term.app); @*/
        /*@ {
            assert [tf]term->term.app.fn |-> ?fn;
            assert [tf]term->term.app.param |-> ?param;
            assert [tf]valid_LambdaTerm(fn,_,?innerE1);
            assert [tf]valid_LambdaTerm(param,_,?innerE2);
            call_perm_level_weaken(1,lt,lambda_depth(t_val),
                {lambdaSubst_inner}, 3,lambda_depth(innerE1));
            consume_call_perm_level_for(lambdaSubst_inner);
            call_perm_level_weaken(1,lt,lambda_depth(t_val),
                {lambdaSubst_inner}, 3,lambda_depth(innerE2));
            consume_call_perm_level_for(lambdaSubst_inner);
        } @*/
        {
            LambdaTerm* E1 = rec(term->term.app.fn,ind,v);
            LambdaTerm* E2 = rec(term->term.app.param,ind,v);
            ret->term.app.fn = E1;
            ret->term.app.param = E2;
        }
        break;
    default:
        /*@ assert false; @*/
        abort();
    }
    return ret;
}


