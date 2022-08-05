VF=time verifast -target Linux64 -shared -emit_vfmanifest

.PHONY: all clean core_lib demos bins lorg_lib

DEMOS = binsearch.vfmanifest isort.vfmanifest mergesort.vfmanifest slowsort.vfmanifest b64.vfmanifest bcd.vfmanifest
BINS = bin/fibber bin/calc bin/calc-dbg

all: core_lib demos bins lorg_lib lorg2_lib p25519_lib
bins: ${BINS}

clean:
	rm *.vfmanifest || true
	rm lorg/*.vfmanifest || true
	rm lorg2/*.vfmanifest || true
	rm p25519/*.vfmanifest || true
	rm bin/* || true

%.vfmanifest: %.c
	${VF} -c $<
%.vfmanifest: %.c %.gh
	${VF} -c $<
%.vfmanifest: %.c %.h
	${VF} -c $<
%.vfmanifest: %.c %.gh %.h
	${VF} -c $<

CORE_LIB  = axioms/prelude.vfmanifest nats.vfmanifest core.vfmanifest
CORE_LIB += mul.vfmanifest div.vfmanifest util.vfmanifest
CORE_LIB += lists.vfmanifest poly.vfmanifest
CORE_LIB += axioms/bitops_axioms.vfmanifest bitops.vfmanifest
CORE_LIB += axioms/call_perms.vfmanifest termination.vfmanifest
CORE_LIB += numtheo.vfmanifest finfield.vfmanifest

core_lib: ${CORE_LIB}
	${VF} ${CORE_LIB}

demos: ${DEMOS} ${CORE_LIB}
	${VF} ${CORE_LIB} ${DEMOS}

P25519_LIB = p25519/p25519_generated.vfmanifest p25519/p448_generated.vfmanifest p25519/p569_generated.vfmanifest p25519/p25519.vfmanifest p25519/p512m32p1.vfmanifest

p25519_lib: ${P25519_LIB} ${CORE_LIB}
	${VF} ${CORE_LIB} ${P25519_LIB}

LORG_LIB = b64.vfmanifest lorg/bi_big_int.vfmanifest lorg/bi_big_int_plus.vfmanifest lorg/bi_big_int_hex.vfmanifest lorg/bi_big_int_hex2.vfmanifest lorg/bi_big_int_mul.vfmanifest

lorg_lib: ${LORG_LIB} ${CORE_LIB}
	${VF} ${CORE_LIB} ${LORG_LIB}

LORG2_LIB = lorg2/lorgint.vfmanifest lorg2/lorgint-reduce.vfmanifest lorg2/lorgint-add-int.vfmanifest

lorg2_lib: ${LORG2_LIB} ${CORE_LIB}
	${VF} ${CORE_LIB} ${LORG2_LIB}

bin/fibber: bigint/fibber.vfmanifest ${CORE_LIB} ${LORG_LIB}
	${VF} ${CORE_LIB} ${LORG_LIB} bigint/fibber.vfmanifest
	mkdir -p bin
	${CC} -Wall -Werror -Wextra -pedantic -O3 -march=native -flto -o bin/fibber b64.c lorg/bi_big_int.c lorg/bi_big_int_plus.c lorg/bi_big_int_hex.c lorg/bi_big_int_hex2.c lorg/bi_big_int_mul.c bigint/fibber.c

bin/calc: bigint.vfmanifest ${CORE_LIB} ${LORG_LIB}
	${VF} ${CORE_LIB} ${LORG_LIB} bigint.vfmanifest
	mkdir -p bin
	${CC} -Wall -Werror -Wextra -pedantic -O3 -march=native -flto -o bin/calc b64.c lorg/bi_big_int.c lorg/bi_big_int_plus.c lorg/bi_big_int_hex.c lorg/bi_big_int_hex2.c bigint.c

bin/calc-dbg: bigint.vfmanifest ${CORE_LIB} ${LORG_LIB}
	${VF} ${CORE_LIB} ${LORG_LIB} bigint.vfmanifest
	mkdir -p bin
	${CC} -Wall -Werror -Wextra -pedantic -O1 -g -o bin/calc-dbg b64.c lorg/bi_big_int.c lorg/bi_big_int_plus.c lorg/bi_big_int_hex.c lorg/bi_big_int_hex2.c bigint.c

