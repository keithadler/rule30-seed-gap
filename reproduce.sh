#!/bin/bash
# Reproduces the headline numbers.  Needs a C compiler and python3.  Takes a few minutes.
set -e
cd "$(dirname "$0")"
cc -O3 -march=native -DMAXN=400 -o gapscan src/gapscan.c
echo "== period 2: longest gap beyond the seed edge, over ALL right halves of width r, both alternating traces =="
for r in 12 16 20 24 26; do
  for tr in 2 3; do
    n=$((1<<r)); out=$(./gapscan G $r $tr 0 $n | sort -n | tail -1 | cut -d' ' -f1)
    echo "r=$r trace=$([ $tr = 2 ] && echo 0101 || echo 1010): longest gap $out"
  done
done
echo "== independent pure-python reference on small widths (compare with the lines above) =="
for r in 8 10 12; do python3 src/reference.py $r 01; python3 src/reference.py $r 10; done
