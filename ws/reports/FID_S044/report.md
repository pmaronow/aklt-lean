STATUS: PASS
BLOCKING: 0

DECL: groupLeader PASS

This is auxiliary indexing for the groups in Definition `d:reduction` (`paper/app-local-operator.tex:146`, especially the remaining-vector list at line 154 and the group definition at line 157). The paper specifies the twenty external slots geometrically (`paper/sec6-walks.tex:488`, lines 492–494), without prescribing their numerical order. Against `lean/AKLT/Defs/Pattern.lean:18`, the eight values are exactly the first original slot at each site:

| Site | Leader | Second corner slot |
| --- | ---: | ---: |
| `(1,1)` | 0 | 1 |
| `(-1,1)` | 2 | 3 |
| `(-1,-1)` | 4 | 5 |
| `(1,-1)` | 6 | 7 |
| `(2,0)` | 8 | — |
| `(0,2)` | 11 | — |
| `(-2,0)` | 14 | — |
| `(0,-2)` | 17 | — |

`Plane` is `ℤ × ℤ`, so the negative coordinates have their intended integer meaning. `Fin 20` numerals are reduced modulo 20 (Mathlib `Data/Fin/Basic.lean:539`); every listed numeral is already in range. The eight leaders are distinct, and no corner second slot equals any leader. The final default correctly handles the south tip. Although other plane sites also map to 17, every operational use takes its site from `reductionGroups`, a subset of precisely these eight sites. A replacement uses the leader as a fresh vector label, without imposing equality to the old slot vector, as permitted by `paper/app-local-operator.tex:166`.

DECL: groupSecond PASS

This auxiliary definition selects the other original slot of a retained corner, as required by `paper/app-local-operator.tex:152` and the two-factor formula at line 162. Its values at the four corners are exactly 1, 3, 5, and 7 in the table above. The addition is ordinary natural-number addition on `groupLeader x |>.val`, followed by `min 19`; it is not modular addition in `Fin 20`. In fact every possible leader is at most 17, so the minimum never clips the result. The explicit `Fin` constructor supplies only a bound proof and preserves the computed value. Consumers use the second token only when the group is a pair, which implies that the site is a corner. Values at tips and other sites therefore cannot introduce an extra vector or tensor factor. There is no natural-number subtraction or predecessor convention involved.

DECL: groupIsPair PASS

On the group domain this is exactly the classification in `paper/app-local-operator.tex:147`–157: a bonded tip is always a single; an unreduced bonded corner is a pair; a reduced one-bond corner is a single; a reduced two-bond corner is a pair. Expanding `SingleReplacement` (`lean/AKLT/Defs/Operator.lean:21`) gives these cases directly. Boundary geometry permits at most one internal tip bond and two internal corner bonds. `patternDegree` counts incident present bonds once: `internalBonds` uses positive orientations, and `PatternData.bonds` filters those bonds by nonremoved endpoints and the appropriate kept rules. It does not count external slots or merely kept half-bonds.

Mathlib `Data/Bool/Basic.lean:71` gives `decide P = true ↔ P`; coercing the result to a condition tests truth, without changing its polarity. Classical decidability adds no hypothesis. A degree-zero corner does return `true` in isolation, but it is excluded from `reductionGroups` before any pair factor, token, or basis is constructed. Thus this totalization does not retain a deleted corner. Removed sites likewise have degree zero because present bonds exclude status `X`.

DECL: reductionVectors PASS

This realizes exactly the remaining list of vectors in `paper/app-local-operator.tex:154` and its single/pair grouping at line 157. `reductionGroups` first excludes every zero-bond tip or corner, matching deletion at line 147. Each remaining group contributes one leader token or the two distinct corner-slot tokens according to the classification above. Consequently neither the other two original tip slots nor the second slot of a replaced corner survives as an independent variable. Both original slots of a retained corner survive even if its actual external bonds are missing, as required by `paper/sec6-walks.tex:510`.

Mathlib `Data/Finset/Filter.lean:127` makes filtering conjunction with the predicate; `Data/Finset/Union.lean:194` and `:202` make `biUnion` the ordinary union over members of the source finset. Although this union removes duplicates, the verified index table makes different groups disjoint and each pair genuinely two-element, so no intended variable is identified or lost. Finiteness is explicit: this is a finset in `Fin 20`, with no finiteness assumption on the ambient plane. `reducedIntegrand` uses precisely these tokens in its factors, and the group-inversion and exchange-basis definitions use the same indexing. The definitions allow arbitrary replacement vectors, with ball or sphere restrictions supplied only by the relevant statements; this agrees with `paper/app-local-operator.tex:166`–168.

DECL: replacementRadius PASS

Lemma `l:leaf` specifies tip radius `3/5`, U-corner radius `1/2`, and D-corner radius `1/3` (`paper/app-local-operator.tex:91`–96); Definition `d:reduction` adopts exactly these values (`paper/app-local-operator.tex:148`–153). The Lean branches return those exact rational numbers. The declared codomain `ℚ` makes each division rational field division, not natural-number or integer division (Mathlib `Algebra/Field/Rat.lean:27`; `Data/Rat/Defs.lean:246`). Denominators 5, 2, and 3 are fixed and nonzero. The rational-to-real coercion in the leaf statement preserves these quotients (Mathlib `Data/Rat/Cast/Defs.lean:195`).

The tip branch takes priority, correctly making every covering tip radius `3/5`. For a singleton corner in a covered pattern, a present bond ensures nonremoved status, so the non-U branch means D. `LeafStatement` explicitly assumes coveredness and nonremoved boundary status (`lean/AKLT/Blueprint/Top/Operator.lean:38`); `reducedIntegrand` uses the radius only for singleton groups. Retained pairs instead have two factors of radius 1 and do not use this function. Its values at removed sites, retained corners, or nonboundary sites do not affect these constructions. No additional representation argument is needed: corner replacement is selected separately, while its radius depends only on its status. The positive sign in the replacement factor agrees with `paper/app-local-operator.tex:160`.

Non-blocking remarks:

- The total definitions intentionally extend beyond the paper's covered-pattern domain. Their off-domain defaults do not alter the five declarations' intended uses; no added domain hypotheses are needed on these auxiliary functions.
- Read all of `Operator.lean` and its local transitive imports: `Pattern`, `Trails`, `Domain`, `PinModel`, `Moment`, `Geometry`, and `Frame`. Also inspected the operator interfaces and downstream token, polynomial, and tensor constructions. Paths beginning `paper/` or `lean/` above are relative to `/home/ubuntu/aklt/review/FID_S/`; Mathlib paths are relative to `/home/ubuntu/aklt/repo/.lake/packages/mathlib/Mathlib/`.
- A Python source-table check verified all twenty external slots, all eight leaders, and all four corner second slots. An exhaustive check of the 2,592 boundary-degree/representation combinations (`3^4 · 2^4 · 2`, including configurations not realizable by covered patterns) found the prescribed group sizes and no token collisions. These checks supplement source inspection; no Lean compilation was run. Inputs were not modified.
