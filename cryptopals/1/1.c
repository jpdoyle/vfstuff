#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "../../b64.h"

int main(void)
    //@ requires true;
    //@ ensures true;
{
    size_t ix = 0;
    size_t n_chars = 10;
    char c;
    char* inbuf = calloc(n_chars+1,sizeof(char));

    if(!inbuf) { abort(); }

    while(1)
        /*@ invariant malloc_block_chars(inbuf,n_chars+1)
                &*&  inbuf[0..ix] |-> ?cs
                &*&  inbuf[ix..n_chars+1] |-> _
                &*&  0 <= ix &*& ix <= n_chars &*& n_chars >= 10
                &*&  n_chars < UINTPTR_MAX
                &*&  length(cs) == ix
                &*&  !!forall(cs,(flip)(mem,hex_chars()))
                &*&  !mem('\0', cs)
                &*&  base_n(hex_chars(),reverse(cs),_,_)
                ; @*/
        /*@ decreases n_chars - ix; @*/
    {
        c = /*@ truncating @*/ (char)getchar();
        if(!is_hex(c)) break;
        //@ assert !!mem(c, hex_chars());

        inbuf[ix] = c;
        //@ close chars(inbuf + ix, 1, cons(c, nil));
        //@ chars_join(inbuf);
        ++ix;
        if(ix == n_chars) {
            if(n_chars > UINT_MAX/2) abort();
            inbuf[ix] = c;
            //@ close chars(inbuf + ix, 1, cons(c, nil));
            //@ chars_join(inbuf);
            n_chars *= 2;
            inbuf = realloc(inbuf,n_chars+1);
            if(!inbuf) { abort(); }
        }
    }

    inbuf[ix] = '\0';
    //@ assert chars(inbuf, ix, ?cs);

    if(ix % 2 == 0)
    {
        size_t n_bytes;
        unsigned char* bytes = bytes_of_hex(ix,inbuf,&n_bytes);
        if(n_bytes > UINT_MAX) abort();
        //@ body_chars_to_string(inbuf);
        printf("%s\n",inbuf);
        printf("%u\n",(unsigned)n_bytes);
        //@ string_to_chars_(inbuf);
        //@ chars__join(inbuf);
        //@ leak base_n(hex_chars(),reverse(cs),_,_);
        free(inbuf);
        //@ uchars_to_uchars_(bytes);
        free(bytes);
        return 0;
    }

    printf("Odd number of hex digits\n");
    //@ chars_to_chars_(inbuf);
    //@ open character(inbuf + ix, 0);
    //@ close chars_(inbuf + ix, 1, cons(some(0), nil));
    //@ chars__join(inbuf);
    //@ chars__join(inbuf);
    //@ leak base_n(hex_chars(),reverse(cs),_,_);
    free(inbuf);
    return -1;
}

