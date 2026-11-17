#!/bin/bash
# re-run of the (0.961, 0.935) certificate with the repaired coefficients a = 0.18094, b = 0.36751
cd "$(dirname "$0")"
A=0.18094; B=0.36751
for job in "B 1" "B 2" "C 1" "C 2" "C 3"; do
  set -- $job
  { time ./tailmem5 $1 10 20 28 109 109 22 0.961 0.935 $A $B 1 1.23 $2 ; } > r961A_$1_$2.txt 2>&1
done
for X in B C; do
  { time ./tailmem4 $X 10 20 28 260 53 109 0.961 0.935 $A $B 1 1.23 ; } > r961B_$X.txt 2>&1
done
echo done > ALLDONE
