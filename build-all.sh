#!/usr/bin/env bash
# TODO: make this a makefile? how tf do vfmanifests work
exec verifast -target Linux64 -shared prelude.vfmanifest bitops_axioms.vfmanifest call_perms.vfmanifest nats.c util.c lists.c bitops.c termination.c isort.c slowsort.c poly.c numtheo.

