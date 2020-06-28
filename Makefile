VF=verifast -target Linux64 -shared -emit_vfmanifest

.PHONY: all clean

clean:
	rm *.vfmanifest

all: nats.vfmanifest util.vfmanifest lists.vfmanifest bitops.vfmanifest termination.vfmanifest isort.vfmanifest slowsort.vfmanifest poly.vfmanifest numtheo.vfmanifest bigint.vfmanifest 

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

slowsort.vfmanifest: slowsort.c sorting.h sorting.gh util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest lists.vfmanifest termination.vfmanifest axioms/call_perms.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/call_perms.vfmanifest termination.vfmanifest slowsort.c

bigint.vfmanifest: bigint.c bigint.h util.vfmanifest nats.vfmanifest axioms/prelude.vfmanifest lists.vfmanifest b64.h axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest
	${VF} axioms/prelude.vfmanifest nats.vfmanifest util.vfmanifest lists.vfmanifest axioms/bitops_axioms.vfmanifest bitops.vfmanifest poly.vfmanifest bigint.c


