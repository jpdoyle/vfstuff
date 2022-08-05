#include "lorgint.h"
#include "common.h"
/*@ #include "../bitops.gh" @*/

#if 1
#define ALREADY_PROVEN() {}
#else
#define ALREADY_PROVEN() { assume(false); }
#endif

#if 1
#define SKIP_A_PROOF() {}
#else
#define SKIP_A_PROOF() { assume(false); }
#endif

