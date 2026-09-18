#!/bin/bash
# usage: vfpar.sh <outfile> <file.c> [flags...]
# Runs one verification in the background, memory-scoped, result to outfile.
OUT="$1"; shift
F="$1"; shift
(
  timeout 2400 systemd-run --user --scope -q -p MemoryHigh=1500M -p MemoryMax=2500M \
    /home/joe/verifast/result/bin/verifast -target Linux64 "$@" "$F" 2>&1
  echo "EXIT:$?" >> "$OUT"
) > "$OUT" 2>&1 &
echo "started $F -> $OUT"
