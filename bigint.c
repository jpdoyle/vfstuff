#include <string.h>
#include <stdio.h>
#include <limits.h>
#include "bi_big_int.h"
/*@ #include "util.gh" @*/
/*@ #include "poly.gh" @*/

char* read_line(void)
    /*@ requires true; @*/
    /*@ ensures  malloced_string(result,?cs)
            &*&  !mem('\n',cs); @*/
{
    size_t len = 0,cap = 8;
    char* ret = malloc(cap*sizeof(char));
    if(!ret) abort();

    while(true)
        /*@ requires len >= 0 &*& len < cap
                &*&  malloc_block_chars(ret,cap)
                &*&  ret[..len] |-> ?pref
                &*&  ret[len..cap] |-> _
                &*&  !mem('\n',pref)
                &*&  !mem('\0',pref)
                ; @*/
        /*@ ensures  len >= 0 &*& len < cap
                &*&  malloc_block_chars(ret,cap)
                &*&  ret[..old_len] |-> pref
                &*&  ret[old_len..len] |-> ?suff
                &*&  ret[len..cap] |-> _
                &*&  !mem('\n',append(pref,suff))
                &*&  !mem('\0',append(pref,suff))
                ; @*/
    {
        int i = getchar();
        if(i <= 0) break;
        if(i > CHAR_MAX) abort();

        char c = (char)i;

        if(c == '\n') break;

        ret[len] = c;
        /*@ close chars(ret+len,1,_); @*/
        /*@ chars_join(ret); @*/
        ++len;
        if(len == cap) {
            if(cap > UINT_MAX/2) abort();
            cap *= 2;
            ret = realloc(ret,cap);
            if(!ret) abort();
        }
    }
    ret[len] = '\0';
    /*@ body_chars_to_string(ret); @*/
    return ret;
}

bool is_hex_string(const char* s)
    /*@ requires [?f]string(s,?cs); @*/
    /*@ ensures  [ f]string(s, cs)
            &*&  result
            ?    base_n(hex_chars(),reverse(cs),_,_)
            :    exists<char>(?c)
            &*&  !mem(c,hex_chars())
            &*&  !!mem(c,cs); @*/
    /*@ terminates; @*/
{
    bool ret = true;
    for(;*s;++s)
        /*@ requires [f]string(s,?loop_cs) &*& !!ret; @*/
        /*@ ensures  [f]string(old_s,loop_cs)
                &*&  ret 
                ?    base_n(hex_chars(),reverse(loop_cs),_,_)
                :    exists<char>(?c)
                &*&  !mem(c,hex_chars())
                &*&  !!mem(c,loop_cs); @*/
        /*@ decreases length(loop_cs); @*/
    {
        /*@ string_limits(s); @*/
        /*@ assert [f]*s |-> ?c; @*/
        if(!is_hex(*s)) {
            ret = false;
            /*@ {
                close exists(c);
            } @*/
            break;
        }
        /*@ assert [f]string(s+1,?rest_cs); @*/

        /*@ recursive_call(); @*/

        /*@ if(ret) {
            close base_n(hex_chars(),{c},_,_);
            base_n_append(reverse(rest_cs),{c});
        } @*/
    }
    return ret;
}

char* read_hex_string()
    /*@ requires true; @*/
    /*@ ensures  result == 0 ? emp
            :    malloced_string(result,?cs)
            &*&  safe_head(cs) == some('-')
                ? base_n(hex_chars(),reverse(tail(cs)),_,_)
                : base_n(hex_chars(),reverse(cs),_,_)
            ; @*/
{
    char* ret = read_line();
    /*@ assert string(ret,?cs); @*/
    /*@ TRIVIAL_LIST(cs) @*/
    if(is_hex_string(ret)) {
        /*@ if(safe_head(cs) == some('-')) {
          forall_elim(reverse(cs),(flip)(mem,hex_chars()),'-');
          assert false;
        } @*/
        return ret;
    }
    if(*ret == '-' && is_hex_string(ret+1)) return ret;
    free(ret);
    return NULL;
}

int test1(void)
    /*@ requires true; @*/
    /*@ ensures  result == 0; @*/
{
    const char* s = "ff";
    /*@ close base_n(hex_chars(),"f",_,15); @*/
    /*@ close base_n(hex_chars(),"ff",_,255); @*/
    big_int* p = big_int_from_hex(s);
    /*@ assert bi_big_int(p,_,_,255); @*/
    char* s2 = big_int_to_hex(p);
    printf("%s\n",s);
    printf("%s\n",s2);
    free_big_int_inner(p);
    free(s2);
    /*@ leak base_n(_,_,_,_); @*/

    return 0;
}

int test2(void)
    /*@ requires true; @*/
    /*@ ensures  result == 0; @*/
{
    const char* s = "-ff";
    /*@ close base_n(hex_chars(),"f",_,15); @*/
    /*@ close base_n(hex_chars(),"ff",_,255); @*/
    big_int* p = big_int_from_hex(s);
    /*@ assert bi_big_int(p,_,_,-255); @*/
    char* s2 = big_int_to_hex(p);
    printf("%s\n",s);
    printf("%s\n",s2);
    free_big_int_inner(p);
    free(s2);
    /*@ leak base_n(_,_,_,_); @*/

    return 0;
}

#ifndef __FILE__
int test_main(void)
#else
int main(void)
#endif
    /*@ requires true; @*/
    /*@ ensures  result == 0; @*/
{
    int n;
    /*@ int orig_n; @*/
    big_int* x = NULL;
    big_int* y = NULL;
    /*@ int xv; @*/
    /*@ int yv; @*/

    if(sizeof(big_int_block) > (size_t)INT_MAX) abort();

    printf("%d\n",(int)sizeof(big_int_block));

    while(true)
        /*@ requires true; @*/
        /*@ ensures  bi_big_int(x,CARRY_BITS,false,xv); @*/
    {
        printf("x? ");
        char* s = read_hex_string();
        if(s) {
            x = big_int_from_hex(s);
            free(s);
            /*@ assert bi_big_int(x,_,_,?x_v); @*/
            /*@ xv = x_v; @*/
            break;
        }
        printf("Please enter a hex string\n");
    }

    do
        /*@ requires n |-> _; @*/
        /*@ ensures  n |-> ?n_v &*& n_v >= 0; @*/
    {
        int n_read;
        printf("n? ");
        n_read = scanf("%d\n",&n);
        if(n_read < 1) n = -1;
    } while(n < 0);

    /*@ orig_n = n; @*/

    while(true)
        /*@ requires true; @*/
        /*@ ensures  bi_big_int(y,CARRY_BITS,false,yv); @*/
    {
        printf("y? "); 
        char* s = read_hex_string();
        if(s) {
            y = big_int_from_hex(s);
            free(s);
            /*@ assert bi_big_int(y,_,_,?y_v); @*/
            /*@ yv = y_v; @*/
            break;
        }
        printf("Please enter a hex string\n"); 
    }

    for(;n > 0; --n)
        /*@ requires     bi_big_int(x,CARRY_BITS,false,?loop_xv)
                &*&  [?f]bi_big_int(y,CARRY_BITS,false,yv)
                &*&  n |-> ?n_v
                &*& n_v >= 0
                ; @*/
        /*@ ensures      bi_big_int(x,CARRY_BITS,false,loop_xv+n_v*yv)
                &*&  [ f]bi_big_int(y,CARRY_BITS,false,yv)
                &*&  n |-> 0
                ; @*/
        /*@ decreases n_v; @*/
    {
        big_int_pluseq(x,y);
        big_int_reduce(x);
    }
    
    {
        char* x_hex = big_int_to_hex(x);;
         /*@ assert string(x_hex,?cs)
                &*& let(xv+orig_n*yv,?res)
                &*& res >= 0
                ?   base_n(hex_chars(),reverse(cs),_,res)
                :   cs == cons('-',tail(cs))
                &*& base_n(hex_chars(),reverse(tail(cs)),_,-res); @*/
        printf("x+n*y=\n%s\n",x_hex);
        free(x_hex);
    }

    /*@ open bi_big_int(x,?car,?und,_); @*/
    printf("%p\n",(void*)x->first);
    /*@ close bi_big_int(x,car,und,_); @*/

    free_big_int_inner(x);
    free_big_int_inner(y);
    /*@ leak base_n(_,_,_,_); @*/

    return 0;
}

