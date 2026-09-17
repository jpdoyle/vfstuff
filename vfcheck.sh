#!/bin/bash
# Verify one file under a systemd-run --user scope with memory limits so big
# VeriFast/z3 runs don't take down the machine.
# usage: vfcheck.sh <file.c|file.gh> [extra verifast args...]
# Defaults to -shared -c (compile-only, library mode) like the Makefile's VF.
F="$1"; shift
hasmode=0
for a in "$@"; do case "$a" in -c|-shared) hasmode=1;; esac; done
[ "$hasmode" = 0 ] && set -- "$@" -shared -c
timeout 900 systemd-run --user --scope -q -p MemoryHigh=2G -p MemoryMax=3G \
  /home/joe/verifast/result/bin/verifast -target Linux64 "$@" "$F" 2>&1 \
  | grep -v "no version information\|redux: INFO"
