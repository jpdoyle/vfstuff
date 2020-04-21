#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "b64.h"

int main(void) {
    size_t i;
    size_t ixs[2] = { 0 };
    size_t n_chars[2] = { 10, 10 };
    char c;
    char* inbufs[2] = {
        calloc(n_chars[0]+1,sizeof(char)),
        calloc(n_chars[1]+1,sizeof(char))
    }

    if(!inbufs[0]) { abort(); }
    if(!inbufs[1]) { abort(); }

    for(i=0; i < 2; ++i) {
        while(is_hex((c = getchar()))) {
            if(ixs[i] == n_chars[i]) {
                n_chars[i] *= 2;
                inbufs[i] = realloc(inbufs[i],n_chars[i]+1);
                if(!inbufs[i]) { abort(); }
            }

            inbufs[i][ixs[i]] = c;
            ++ixs[i];
        }
        inbufs[i][ixs[i]] = '\0';
    }

    {
        size_t n_bytes1;
        size_t n_bytes2;
        uint8_t* bytes1 = bytes_of_hex(ixs[0],inbufs[0],&n_bytes[0]);
        uint8_t* bytes2 = bytes_of_hex(ixs[0],inbufs[1],&n_bytes[1]);
        free(inbuf);
        free(bytes);
        free(b64);
    }

    return 0;
}


