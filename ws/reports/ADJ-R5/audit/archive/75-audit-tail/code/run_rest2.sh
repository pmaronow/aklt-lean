#!/bin/bash
# mode B row C, started once the small python cross-check (pid given) has finished
cd "$(dirname "$0")"
while kill -0 $1 2>/dev/null; do sleep 10; done
A=0.18094; B=0.36751
{ time ./tailmem4 C 10 20 28 260 53 109 0.961 0.935 $A $B 1 1.23 ; } > r961B_C.txt 2>&1
echo done > DONE2
