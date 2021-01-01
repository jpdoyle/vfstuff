VF=time verifast -target Linux64 -shared -emit_vfmanifest

.PHONY: all clean

all: nats.vfmanifest.done util.vfmanifest.done lists.vfmanifest.done bitops.vfmanifest.done termination.vfmanifest.done isort.vfmanifest.done slowsort.vfmanifest.done poly.vfmanifest.done numtheo.vfmanifest.done bigint.vfmanifest.done lorg/bi_big_int_mul.vfmanifest.done bin/calc bin/calc-dbg bin/fibber

clean:
	rm *.vfmanifest
	rm *.vfmanifest.done
	rm bigint/*.vfmanifest

nats.vfmanifest.done: nats.c nats.gh axioms/prelude.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.c
	touch nats.vfmanifest.done

util.vfmanifest.done: util.c util.gh nats.vfmanifest.done axioms/prelude.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.c
	touch util.vfmanifest.done

lists.vfmanifest.done: lists.c lists.gh util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.c
	touch lists.vfmanifest.done

bitops.vfmanifest.done: bitops.c bitops.gh util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest axioms/bitops_axioms.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest axioms/bitops_axioms.vfmanifest bitops.c
	touch bitops.vfmanifest.done

termination.vfmanifest.done: termination.c termination.gh util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest axioms/call_perms.vfmanifest call_perms.gh
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest axioms/call_perms.vfmanifest termination.c
	touch termination.vfmanifest.done

numtheo.vfmanifest.done: numtheo.c numtheo.h numtheo.gh util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest lists.vfmanifest.done
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest numtheo.c
	touch numtheo.vfmanifest.done

isort.vfmanifest.done: isort.c sorting.h sorting.gh util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest lists.vfmanifest.done
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest isort.c
	touch isort.vfmanifest.done

poly.vfmanifest.done: poly.c poly.gh util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest lists.vfmanifest.done
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest poly.c
	touch poly.vfmanifest.done

b64.vfmanifest.done: b64.c b64.h util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest lists.vfmanifest.done poly.vfmanifest.done axioms/bitops_axioms.vfmanifest bitops.vfmanifest.done 
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest poly.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest b64.c
	touch b64.vfmanifest.done

slowsort.vfmanifest.done: slowsort.c sorting.h sorting.gh util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest lists.vfmanifest.done termination.vfmanifest.done axioms/call_perms.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/call_perms.vfmanifest termination.vfmanifest slowsort.c
	touch slowsort.vfmanifest.done

lorg/bi_big_int.vfmanifest.done: lorg/bi_big_int.c bigint.h lorg/bi_big_int.h b64.h util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest lists.vfmanifest.done axioms/bitops_axioms.vfmanifest bitops.vfmanifest.done poly.vfmanifest.done b64.vfmanifest.done
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest lorg/bi_big_int.c
	touch lorg/bi_big_int.vfmanifest.done

lorg/bi_big_int_plus.vfmanifest.done: lorg/bi_big_int_plus.c lorg/bi_big_int.h bigint.h b64.h lorg/bi_big_int.vfmanifest.done util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest lists.vfmanifest.done axioms/bitops_axioms.vfmanifest bitops.vfmanifest.done poly.vfmanifest.done b64.vfmanifest.done
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest lorg/bi_big_int.vfmanifest lorg/bi_big_int_plus.c
	touch lorg/bi_big_int_plus.vfmanifest.done

lorg/bi_big_int_hex.vfmanifest.done: lorg/bi_big_int_hex.c bigint.h lorg/bi_big_int.h lorg/bi_big_int.vfmanifest.done util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest b64.vfmanifest.done lists.vfmanifest.done axioms/bitops_axioms.vfmanifest bitops.vfmanifest.done poly.vfmanifest.done
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest lorg/bi_big_int.vfmanifest lorg/bi_big_int_hex.c
	touch lorg/bi_big_int_hex.vfmanifest.done

lorg/bi_big_int_hex2.vfmanifest.done: lorg/bi_big_int_hex2.c bigint.h lorg/bi_big_int.h lorg/bi_big_int.vfmanifest.done util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest b64.vfmanifest.done lists.vfmanifest.done axioms/bitops_axioms.vfmanifest bitops.vfmanifest.done poly.vfmanifest.done
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest lorg/bi_big_int.vfmanifest lorg/bi_big_int_hex2.c
	touch lorg/bi_big_int_hex2.vfmanifest.done

bigint.vfmanifest.done: bigint.c bigint.h lorg/bi_big_int.h util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest lists.vfmanifest.done b64.vfmanifest.done axioms/bitops_axioms.vfmanifest bitops.vfmanifest.done poly.vfmanifest.done lorg/bi_big_int.vfmanifest.done lorg/bi_big_int_hex.vfmanifest.done lorg/bi_big_int_hex2.vfmanifest.done lorg/bi_big_int_plus.vfmanifest.done
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest lorg/bi_big_int.vfmanifest lorg/bi_big_int_hex.vfmanifest lorg/bi_big_int_hex2.vfmanifest lorg/bi_big_int_plus.vfmanifest bigint.c
	touch bigint.vfmanifest.done

bigint/fibber.vfmanifest.done: bigint/fibber.c bigint.h util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest lists.vfmanifest.done b64.vfmanifest.done axioms/bitops_axioms.vfmanifest bitops.vfmanifest.done poly.vfmanifest.done lorg/bi_big_int.vfmanifest.done lorg/bi_big_int_hex.vfmanifest.done lorg/bi_big_int_hex2.vfmanifest.done lorg/bi_big_int_plus.vfmanifest.done lorg/bi_big_int_mul.vfmanifest.done
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest lorg/bi_big_int.vfmanifest lorg/bi_big_int_hex.vfmanifest lorg/bi_big_int_hex2.vfmanifest lorg/bi_big_int_plus.vfmanifest lorg/bi_big_int_mul.vfmanifest bigint/fibber.c
	touch bigint/fibber.vfmanifest.done

lorg/bi_big_int_mul.vfmanifest.done: lorg/bi_big_int_mul.c bigint.h lorg/bi_big_int.h util.vfmanifest.done nats.vfmanifest.done axioms/prelude.vfmanifest lists.vfmanifest.done b64.vfmanifest.done axioms/bitops_axioms.vfmanifest bitops.vfmanifest.done poly.vfmanifest.done lorg/bi_big_int.vfmanifest.done lorg/bi_big_int_plus.vfmanifest.done
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest b64.vfmanifest lorg/bi_big_int.vfmanifest lorg/bi_big_int_plus.vfmanifest lorg/bi_big_int_mul.c
	touch lorg/bi_big_int_mul.vfmanifest.done

bin/fibber: bigint/fibber.vfmanifest.done lorg/bi_big_int.vfmanifest.done lorg/bi_big_int_plus.vfmanifest.done lorg/bi_big_int_hex.vfmanifest.done lorg/bi_big_int_hex2.vfmanifest.done
	mkdir -p bin
	${CC} -Wall -Werror -Wextra -pedantic -O3 -march=native -flto -o bin/fibber b64.c lorg/bi_big_int.c lorg/bi_big_int_plus.c lorg/bi_big_int_hex.c lorg/bi_big_int_hex2.c lorg/bi_big_int_mul.c bigint/fibber.c

bin/calc: bigint.vfmanifest.done lorg/bi_big_int.vfmanifest.done lorg/bi_big_int_plus.vfmanifest.done lorg/bi_big_int_hex.vfmanifest.done lorg/bi_big_int_hex2.vfmanifest.done
	mkdir -p bin
	${CC} -Wall -Werror -Wextra -pedantic -O3 -march=native -flto -o bin/calc b64.c lorg/bi_big_int.c lorg/bi_big_int_plus.c lorg/bi_big_int_hex.c lorg/bi_big_int_hex2.c bigint.c

bin/calc-dbg: bigint.vfmanifest.done lorg/bi_big_int.vfmanifest.done lorg/bi_big_int_plus.vfmanifest.done lorg/bi_big_int_hex.vfmanifest.done lorg/bi_big_int_hex2.vfmanifest.done
	mkdir -p bin
	${CC} -Wall -Werror -Wextra -pedantic -O1 -g -o bin/calc-dbg b64.c lorg/bi_big_int.c lorg/bi_big_int_plus.c lorg/bi_big_int_hex.c lorg/bi_big_int_hex2.c bigint.c

