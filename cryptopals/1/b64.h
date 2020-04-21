#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
/*@ #include "../../lists.gh" @*/

#ifndef CRYPTOPALS_B64_H
#define CRYPTOPALS_B64_H

/*@

fixpoint list<char> hex_chars() {
    return {'0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
            'a', 'b', 'c', 'd', 'e', 'f'};
}

lemma void in_range1_hex_chars(char c)
    requires (c >= 'a' && c <= 'f');
    ensures  !!mem(c,hex_chars());
{
         if(c < 'b') {}
    else if(c < 'c') {}
    else if(c < 'd') {}
    else if(c < 'e') {}
    else if(c < 'f') {}
}

lemma void in_range2_hex_chars(char c)
    requires (c >= '0' && c <= '9');
    ensures  !!mem(c,hex_chars());
{
         if(c < '1') {}
    else if(c < '2') {}
    else if(c < '3') {}
    else if(c < '4') {}
    else if(c < '5') {}
    else if(c < '6') {}
    else if(c < '7') {}
    else if(c < '8') {}
    else if(c < '9') {}
}

lemma_auto(mem(c,hex_chars()))
void hex_chars_range(char c)
    requires true;
    ensures  mem(c,hex_chars())
        ==   ((c >= 'a' && c <= 'f') || (c >= '0' && c <= '9'));
{
    if(c >= 'a' && c <= 'f') {
        in_range1_hex_chars(c);
    } else if(c >= '0' && c <= '9') {
        in_range2_hex_chars(c);
    }
}

//lemma void hex_chars_range2_add(int c)
//    requires 10 <= c &*& c < 16;
//    ensures  nth_of(c,hex_chars()) == some('a'+c);
//{}

  @*/

bool is_hex(char c)
    /*@ requires true; @*/
    /*@ ensures  result == mem(c,hex_chars()); @*/
    /*@ terminates; @*/
{
    return (c >= 'a' && c <= 'f') || (c >= '0' && c <= '9');
}

char hex_of_nib(uint8_t c)
    /*@ requires c >= 0 &*& c < 16; @*/
    /*@ ensures  some(result) == nth_of(c,hex_chars()); @*/
    /*@ terminates; @*/
{
    if(c < 10)      { return (char)('0'+c);      }
    else if(c < 16) { return (char)('a'+(c-10)); }
    else { /*@ assert false; @*/ abort(); }
}

uint8_t nib_of_hex(char c)
    /*@ requires !!mem(c,hex_chars()); @*/
    /*@ ensures  some(c) == nth_of(result,hex_chars()); @*/
    /*@ terminates; @*/
{
    if(c >= 'a' && c <= 'f') {
        return (uint8_t)(10 + (c-'a'));
    } else if(c >= '0' && c <= '9') {
        return (uint8_t)(c-'0');
    } else { abort(); }
}

char b64_of_byte(uint8_t n) {
    uint8_t thresh0 = 'Z'-'A';
    uint8_t thresh1 = 'z'-'a' + thresh0 + 1;
    uint8_t thresh2 = '9'-'0' + thresh1 + 1;

    if(n >= 64)             { abort();                    }
    else if(n <= thresh0)   { return 'A' + n;             }
    else if(n <= thresh1)   { return 'a' + (n-thresh0-1); }
    else if(n <= thresh2)   { return '0' + (n-thresh1-1); }
    else if(n == thresh2+1) { return '+';                 }
    else if(n == thresh2+2) { return '/';                 }
    else                    { /* impossible*/ abort();    }
}

uint8_t* bytes_of_hex(size_t len, char* s, size_t* outlen) {
    uint8_t* ret;
    uint8_t* p;
    size_t i;
    *outlen = len/2;
    ret = calloc(*outlen,sizeof(uint8_t));
    if(!ret) { abort(); }

    for(i = 0,p = ret; i < len; i+=2,++p) {
        uint8_t h = nib_of_hex(s[i  ]);
        *p = h<<4 | nib_of_hex(s[i+1]);
    }

    return ret;
}

char* hex_of_bytes(size_t len, uint8_t* b) {
    uint8_t* ret;
    uint8_t* p;
    size_t i;
    ret = calloc(2*len,sizeof(char));
    if(!ret) { abort(); }

    for(i = 0,p = ret; i < len; ++i,p+=2) {
        p[0] = hex_of_nib(b[i]>>4);
        p[1] = hex_of_nib(b[i]&0xf);
    }

    return ret;
}

char* b64_of_bytes(size_t len, uint8_t *b) {
    // not a fan of this expression but it's correct
    size_t n_padding = (3-len%3)%3;
    size_t out_len = ((len+n_padding)/3)*4;
    size_t i;
    char* p;
    char* ret = calloc(out_len+1,sizeof(char));

    if(!ret) { abort(); }

    for(i = 0,p = ret; i < len; p+=4,i+=3) {
        p[0] = b64_of_byte(b[i]>>2);

        if(i+1 >= len) {
            p[1] = b64_of_byte((b[i  ]&0x03)<<4);
            break;
        } else {
            p[1] = b64_of_byte((b[i  ]&0x03)<<4 | b[i+1]>>4);
        }

        if(i+2 >= len) {
            p[2] = b64_of_byte((b[i+1]&0x0f)<<2);
            break;
        } else {
            p[2] = b64_of_byte((b[i+1]&0x0f)<<2 | b[i+2]>>6);
        }

        p[3] = b64_of_byte((b[i+2]&0x3f));
    }

    // Coincidentally, there will be exactly n_padding padding bytes
    // to output, even though the calculation mod 3 and the number
    // left in the group of 4 seem unrelated at first glance (check
    // the cases).

    for(i = 0; i < n_padding; ++i) {
        p[3-n_padding+i] = '=';
    }

    return ret;
}

#endif

