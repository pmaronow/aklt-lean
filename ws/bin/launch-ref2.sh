#!/bin/bash
A=$HOME/aklt
while IFS="|" read -r KEY PART; do
  sed -e "s/__KEY__/$KEY/g" -e "s#__PART__#$PART#" $A/briefs/REF2-COMMON.md > $A/briefs/$KEY.md; mkdir -p $A/reports/$KEY
  until $A/bin/aklt-budget-check 1 >/dev/null 2>&1; do sleep 60; done
  tmux new-session -d -s $KEY "cd $A/reports/$KEY; python3 $A/bin/sol-retry.py max 1 -- run -C $A/reports/$KEY --write --search -e max --name $KEY -f $A/briefs/$KEY.md > $A/logs/$KEY.out 2>&1; touch $A/flags/$KEY.done"; sleep 2
done <<LIST
REF2_1|Sections 1 and 3 (the model and main theorem; polynomial model, edge lemma, uniqueness on every torus, frames, quantum-to-classical comparison, finite energy, local gauge)
REF2_2|Section 4 and Appendix A (windows, stopped coupling, the periodic block criterion, assembly of the main theorem; finite probability and operator tools)
REF2_3|Section 5 and Appendix B (shell geometry, cut factorization, removal, thickened cut, the window theorem from the response property; planar topology)
REF2_4|Sections 2 and 6 (finite moment functional, pin model, positivity, quadrature; walk expansion, tracing, pair expansion, exposure, local covering, one-point bound)
REF2_5|Section 7 (closure invariant, terminal cover, logarithmic-mean bounds, type-dependent kernel, positive-vector witness, renewal, the response property)
REF2_6|Section 8 and Appendix C (statements of the computational inputs; memory automata, the one-step growth test, stationary domination, Bellman soundness, prefix bounds, assembly)
REF2_7|Appendix D (operator-only verification of the local inequalities: reductions, Pauli operators, inversion, sectors, ladder lemma, Gram/residual positivity, certificate proposition)
LIST
