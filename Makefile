VF=verifast -target Linux64 -shared -emit_vfmanifest

.PHONY: all clean

all: nats.vfmanifest util.vfmanifest lists.vfmanifest bitops.vfmanifest termination.vfmanifest isort.vfmanifest slowsort.vfmanifest poly.vfmanifest numtheo.vfmanifest bigint.vfmanifest bin/calc

clean:
	rm *.vfmanifest

nats.vfmanifest: nats.c nats.gh axioms/prelude.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.c

util.vfmanifest: util.c util.gh nats.vfmanifest axioms/prelude.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.c

lists.vfmanifest: lists.c lists.gh util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.c

bitops.vfmanifest: bitops.c bitops.gh util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest axioms/bitops_axioms.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest axioms/bitops_axioms.vfmanifest bitops.c

termination.vfmanifest: termination.c termination.gh util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest axioms/call_perms.vfmanifest call_perms.gh
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest axioms/call_perms.vfmanifest termination.c

numtheo.vfmanifest: numtheo.c numtheo.h numtheo.gh util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest lists.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest numtheo.c

isort.vfmanifest: isort.c sorting.h sorting.gh util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest lists.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest isort.c

poly.vfmanifest: poly.c poly.gh util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest lists.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest poly.c

b64.vfmanifest: b64.c b64.h util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest lists.vfmanifest poly.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest 
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest poly.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest b64.c

slowsort.vfmanifest: slowsort.c sorting.h sorting.gh util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest lists.vfmanifest termination.vfmanifest axioms/call_perms.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/call_perms.vfmanifest termination.vfmanifest slowsort.c

bi_big_int.vfmanifest: bi_big_int.c bigint.h b64.h util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest bi_big_int.c

bi_big_int_plus.vfmanifest: bi_big_int_plus.c bigint.h b64.h bi_big_int.vfmanifest util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest bi_big_int.vfmanifest bi_big_int_plus.c

bi_big_int_hex.vfmanifest: bi_big_int_hex.c bigint.h bi_big_int.vfmanifest util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest b64.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest bi_big_int.vfmanifest bi_big_int_hex.c

bigint.vfmanifest: bigint.c bigint.h util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest lists.vfmanifest b64.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest bi_big_int.vfmanifest bi_big_int_hex.vfmanifest bi_big_int_plus.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest bi_big_int.vfmanifest bi_big_int_hex.vfmanifest bi_big_int_plus.vfmanifest bigint.c

bin/calc: bigint.vfmanifest bi_big_int.vfmanifest bi_big_int_plus.vfmanifest bi_big_int_hex.vfmanifest
	mkdir -p bin
	${CC} -Wall -Werror -Wextra -pedantic -O3 -march=native -flto -o bin/calc b64.c bi_big_int.c bi_big_int_plus.c bi_big_int_hex.c bigint.c

