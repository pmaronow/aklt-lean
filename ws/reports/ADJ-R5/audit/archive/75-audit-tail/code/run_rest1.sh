#!/bin/bash
# continue the re-run: wait for the running C_2 job (pid given), then C_3 and mode B row B
cd "$(dirname "$0")"
while kill -0 $1 2>/dev/null; do sleep 10; done
A=0.18094; B=0.36751
{ time ./tailmem5 C 10 20 28 109 109 22 0.961 0.935 $A $B 1 1.23 3 ; } > r961A_C_3.txt 2>&1
{ time ./tailmem4 B 10 20 28 260 53 109 0.961 0.935 $A $B 1 1.23 ; } > r961B_B.txt 2>&1
echo done > DONE1
