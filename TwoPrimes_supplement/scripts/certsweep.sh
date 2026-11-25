#!/bin/bash
# usage: certsweep.sh <nonres executable> <output file>
exe=$1; out=$2; : > "$out"
ispow() { local D=$1 b=$2 x=$2; while [ $x -lt $D ]; do x=$((x*b)); done; [ $x -eq $D ]; }
Ds="$(seq 20 1 200) $(seq 207 7 1000) $(seq 1050 50 3000)"
for l in 3 7; do for D in $Ds; do
  if ispow $D 2 || ispow $D $l; then continue; fi
  timeout 300 "$exe" cert $D $l 3.4 6.0 1.0 | tr -d '\r' >> "$out"
done; done
echo done >> "$out"
