#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "../../b64.h"

int main(void) {
    size_t ix = 0;
    size_t n_chars = 10;
    char c;
    char* inbuf = calloc(n_chars+1,sizeof(char));

    if(!inbuf) { abort(); }

    while(is_hex((c = getchar()))) {
        if(ix == n_chars) {
            n_chars *= 2;
            inbuf = realloc(inbuf,n_chars+1);
            if(!inbuf) { abort(); }
        }

        inbuf[ix] = c;
        ++ix;
    }

    inbuf[ix] = '\0';

    {
        printf("%s\n",inbuf);
        size_t n_bytes;
        uint8_t* bytes = bytes_of_hex(ix,inbuf,&n_bytes);
        printf("%u\n",(unsigned)n_bytes);
        char* b64 = b64_of_bytes(n_bytes,bytes);
        printf("%s\n",b64);
        free(inbuf);
        free(bytes);
        free(b64);
    }

    return 0;
}

