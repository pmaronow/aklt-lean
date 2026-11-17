STATUS: COMPLETE

| Leaf (namespace `AKLT.Blueprint.H3`) | Verdict | Difficulty | Finding |
| --- | --- | --- | --- |
| `ReflectionPairLabelsStatement` | TRUE | medium | Reflection preserves coefficients, pair types and B-row shifts, including on non-trails. |
| `FirstDirectionPartitionStatement` | TRUE | easy | Positive-length closed trails have exactly one first direction among north, west and south. |
| `LengthShiftSupportStatement` | TRUE | easy | The defined finite support contains every response-pair shift at that length. |
| `LengthRewardPartitionStatement` | TRUE | medium | Unique type/shift classification and reward linearity give the finite identity. |
| `KernelSeriesRegroupingStatement` | TRUE | medium | The stated support and partition premises suffice for regrouping in `ℝ≥0∞`. |
| `CutoffSeriesLiftStatement` | TRUE | easy | The hypotheses bound every nonnegative range partial sum, hence their supremum. |

All six statements are true and self-sufficient as written. No corrected statement or additional premise is needed; `fix` is the empty string in each JSON record. None is vacuous. This is a truth review and contains proof routes, not formal proofs.

Reviewed repository revision: `7a3393531c12080d76aefbdab300ac0c2df834b7`. The exact declarations are in [NodesReflection.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesReflection.lean:30) and [NodesKernel.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesKernel.lean:12). The repository was read only; all generated files are under this report directory.

**Definition audit.** The following are the relevant transitive definitions, including the finite-type instances and scalar constants. Imported network, certificate and automaton data that do not occur in these expansions are not assumptions of these leaves.

| Source | Definitions read and their role |
| --- | --- |
| [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8) | `Plane = ℤ × ℤ`; `latticeDist` is the sum of the two integer differences' natural absolute values. `Compass`, its four-element `Fintype`, `Compass.step`, `Compass.reverse`, and `neighbours` supply the four actual lattice neighbours. |
| [Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:110) | `PairType` has exactly B and C, with its explicit two-element `Fintype`. |
| [Trails.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:9) | `localThreshold` is `961/1000` for straight and `187/200` for turn; `passageFactor` is its inverse. Straight/turn `alphaBound` values are `145217/10^6`, `150000/10^6`; `betaBound` values are `352782/10^6`, `357549/10^6`; `betaPrimeBound` values are `340008/10^6`, `344661/10^6`. All are positive rationals. |
| [Trails.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:24) | `DirectionWord n = Fin n → Compass`. `wordVertex` sums steps whose indices are below its natural argument; `wordBond` is the unordered two-vertex finset. `IsTrail` requires injective bonds and forbids initial reversal. `wordIncoming` uses the virtual incoming direction at index zero and the preceding letter otherwise; `wordStraight` compares directions. `departureCount` counts earlier departures over `range (min i n)`; `wordRevisit` tests positivity of that count. `trailBaseWeight` multiplies `1/5` on revisits and `1/3` otherwise. |
| [Kernel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:8) | `kernelStart = (-1,0)`, `kernelCentre = (0,0)`, B target `(1,0)`, C target `(0,1)`, and `kernelIncoming = west`. `ClosedTrail` includes `IsTrail`, the final target equality, centre avoidance through the endpoint and target avoidance strictly before the endpoint. |
| [Kernel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:21) | `deadAt` means centre or at least two earlier departures. `responseNeighbours` erases the arrival site; `liveOtherNeighbours` also erases the outgoing site and filters out dead sites. `responsePairs` is `powersetCard 2` of the live-other sites with the outgoing site inserted. `pairCoefficient` selects alpha, beta or beta-prime using outgoing membership, live-other cardinality and straightness. |
| [Kernel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:47) | `responsePairType` tests whether every two sites share a coordinate. `pairShift X` is the finite supremum of the minimum distances to the start and X target. `responseKappa` sums coefficients whose type and exact shift match. `kernelWitness` is exactly `(1, 5404319552844595/4503599627370496)`; `witnessKappa` is the pairwise witness-weighted reward. |
| [Kernel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:73) | `firstVisitList` filters `List.finRange`; `shortOrderLE` uses the rational score, explicit zero-reward branches and index tie breaking. `kernelOrdering` sorts through length 12 and otherwise places straight first visits before turning first visits, preserving path order within each group. `exposureSum` recursively multiplies the current passage factor into the current reward plus the remaining exposure. |
| [Kernel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:101) | `closedContribution` is base weight times witness exposure. `kernelLengthCoefficient` uses the same ordering and base weight with `responseKappa`, restricted by `ClosedTrail`. `shiftKernel` sums nonnegative real embeddings over all natural lengths; `shiftedKernel` then sums over shifts with the real integer power `θ ^ (-(s : ℤ))`. `kernelPartialRow` sums contributions over `Icc 1 R`. |
| [Stationary.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Stationary.lean:128) | `FirstDirection` explicitly requires a `Fin n` index of value zero with the specified letter; it is false at length zero. `firstDirectionPartialRow` adds that condition to the same closed-trail contribution and cutoff. |
| [Basic.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/Basic.lean:68) | `kernelLengthRow` is the one-length contribution. `lengthShifts` unions the shift images over **all** words and all departure indices. `reflectSite` negates the second coordinate; `reflectWord` applies `reflectDirection` letterwise. |
| [Automaton.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Automaton.lean:107) | `reflectDirection` interchanges north/south and fixes east/west. No quotient or memory-window hypothesis enters its use here. |

The `by classical` blocks internal to definitions supply decidability for their filters and conditionals; they do not add a hypothesis to any leaf. Writers may need to enable classical decidability locally when unfolding these expressions. The diagnostic confirms that no instance argument or other section parameter was silently dropped. `Finset` handles the finite site and pair collections despite the infinite ambient plane; `Fintype` is used for compass directions, pair types, finite indices and direction words.

**`AKLT.Blueprint.H3.ReflectionPairLabelsStatement` — TRUE, medium.** Paper: [l:kernel-reflection](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1024).

The statement quantifies over every word, without `ClosedTrail`. This stronger domain is valid: reflection fixes the start, centre and virtual incoming west direction, transports all prefix departure counts and hence the live-other-neighbour set, and preserves its cardinality. Outgoing membership and straightness select the same coefficient-table branch. Coordinate equalities preserve the pair type. Both B endpoints are fixed by the lattice isometry, so the maximum of the minimum endpoint distances is preserved. None of these arguments requires trail admissibility. The shift claim is correctly restricted to B.

Proof route, line 1: Derive reflection equivariance of vertices, incoming directions, prefix counts and live-other neighbours; transport outgoing membership and cardinality and unfold `pairCoefficient`.  
Proof route, line 2: Preserve the coordinate-equality test for `responsePairType`, then transport `Finset.sup` using the endpoint-fixing lattice isometry.

Lean traps: `Finset.image` preserves cardinality only after establishing injectivity, available from reflection's involution. A word can reverse immediately or repeat bonds; do not use true-trail facts about the outgoing site. `wordIncoming` guards its `ℕ` subtraction at zero, and reflection preserves the same index. `pairShift` uses a supremum in `ℕ`, not a sum or an integer maximum. Its empty-set default is zero, while actual members of `responsePairs` have cardinality two. Local geometric helpers must be derived from the definitions; the other reflection leaves are not hypotheses of this leaf.

**`AKLT.Blueprint.H3.FirstDirectionPartitionStatement` — TRUE, easy.** Paper: [l:stationary-assembly](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1175).

Every length in the cutoff is positive, so its first index exists uniquely. `IsTrail` already forbids initial east, because west's reverse is east; centre avoidance independently excludes that step. The three remaining direction predicates are disjoint and exhaustive on contributing words, for both pair types. At `R = 0` all cutoff sums are empty.

Proof route, line 1: For each `n ∈ Icc 1 R`, construct the zero-valued `Fin n` index, split its compass value and exclude east using `ClosedTrail`.  
Proof route, line 2: Split the closed-trail indicator into its three first-direction indicators and distribute the finite word and length sums.

Lean traps: `DirectionWord 0` has one element, the empty function; it is not an empty type. `FirstDirection` is false there because `Fin 0` is empty. Construct the first index only after obtaining `1 ≤ n`. `Plane` need not be a `Fintype`; the sum is over finite direction words. No B-row symmetry is used to establish the C-row partition.

**`AKLT.Blueprint.H3.LengthShiftSupportStatement` — TRUE, easy.** Paper: [h:H3 and its equivalence explanation](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:594).

For any word, index and response pair, its shift belongs to the two `biUnion`s and the image defining `lengthShifts`. An outside shift therefore makes every selector in `responseKappa` false. The recursive exposure of a zero reward is zero, so the coefficient vanishes. The support deliberately includes non-trails and revisits; it needs no bound such as `n/2+1`. At zero length the support is empty and the coefficient is zero.

Proof route, line 1: Establish direct support membership for every response-pair shift and use it to make `responseKappa X Y s w i` zero outside the support.  
Proof route, line 2: Propagate zero rewards through `exposureSum`, then simplify the finite sum defining `kernelLengthCoefficient`.

Lean traps: The leaf quantifies `n s`, whereas the coefficient's arguments are `s n`. Membership in `lengthShifts` uses `Finset.mem_biUnion` twice and `Finset.mem_image`; it is not an abstract finite-support assertion. At `n = 0` the inner index finset is empty even though the outer word type is inhabited. Image deduplication removes duplicate shift labels, not response-pair coefficients.

**`AKLT.Blueprint.H3.LengthRewardPartitionStatement` — TRUE, medium.** Paper: [d:kernel](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:517) and [h:H3](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:594).

Each response pair contributes to one type and one shift. Its shift belongs to the displayed finite support by definition. Regrouping therefore recovers `witnessKappa` exactly. Exposure is linear in its reward on any fixed list, and both sides use the identical `kernelOrdering w`. The ordering's original dependence on the witness reward creates no circularity: it is never recomputed for an individual type or shift. All sums at this stage are finite. At `n = 0` both sides vanish.

Proof route, line 1: Partition each `witnessKappa w i` by the unique pair type and shift, establishing support membership directly from `lengthShifts`.  
Proof route, line 2: Apply reward linearity on the fixed ordering, multiply by the base weight and commute the finite word, type and shift sums.

Lean traps: Keep `kernelOrdering w` fixed while proving linearity; sorting separately with `responseKappa` would describe another expression. Preserve the exact dyadic `kernelWitness C`, rather than replacing it by `6/5`. The finite partition sums live in `ℚ`, so no real casts or summability premises belong here. Prove support membership locally; this leaf does not assume `LengthShiftSupportStatement`.

**`AKLT.Blueprint.H3.KernelSeriesRegroupingStatement` — TRUE, medium.** Paper: [h:H3 equivalence](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:610).

The two explicit premises are exactly the finite-support property and the lengthwise weighted partition. Nonnegativity of coefficients and witnesses follows from their fixed definitions; [Positivity.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/Positivity.lean:15) already proves it and is imported by this module. At `θ = 1`, the integer-power shift factor is one, including at shift zero. The remaining nonnegative sums may be exchanged in `ℝ≥0∞`, even if their value is infinity. The fixed witness factors distribute through those sums. Nonnegative finite sums and products survive the rational-to-real and `ofReal` conversions. Length zero occurs on both sides consistently.

Proof route, line 1: Expand both kernel series at `θ = 1`, move the finite witness factors through the tsums and commute the type, shift and length sums in `ℝ≥0∞`.  
Proof route, line 2: Remove outside-support shifts at each length, convert the nonnegative finite products and sums through `ofReal`, and apply the supplied length-row identity.

Lean traps: Use `ENNReal.tsum_comm` and `ENNReal.tsum_mul_right`, whose statements require no real-valued summability hypothesis. Do not convert an infinite series using `ENNReal.toReal`, which would lose infinity. `ENNReal.ofReal` is not additive on arbitrary signed reals: use coefficient/witness nonnegativity and `ENNReal.ofReal_sum_of_nonneg`, `ENNReal.ofReal_mul`. Make `ℚ → ℝ` casts explicit before using these lemmas. The finite `PairType` sum can be converted to a tsum when commuting indices. No H2 estimate, certificate, H3 bound or finiteness premise is missing.

**`AKLT.Blueprint.H3.CutoffSeriesLiftStatement` — TRUE, easy.** Paper: [h:H3 equivalence](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:610).

The nonnegativity and zero-at-zero hypotheses allow every `range N` sum to be bounded by the `Icc 1 N` cutoff. The cutoff hypothesis at `R = 0` also gives `0 ≤ B`. Converting these finite bounds to `ℝ≥0∞` and taking the supremum gives the claimed bound on the series. The premises are consistent with nonzero data, for example `f 1 = 1`, every other value zero, and `B = 1`.

Proof route, line 1: Bound every rational `range N` sum by the `Icc 1 N` cutoff using `f 0 = 0` and nonnegativity; cast and identify its finite ENNReal sum.  
Proof route, line 2: Apply `ENNReal.tsum_eq_iSup_nat` and bound the supremum by `ENNReal.ofReal B`.

Lean traps: `Icc 1 R` includes its upper endpoint, while `range N` excludes `N` and includes zero. The existing `f 0 = 0` premise handles the latter; nonnegativity permits the extra endpoint. Using `R = N` avoids natural-subtraction boundary cases. Negative `B` is excluded by the cutoff premise, rather than requiring another hypothesis. The infinite sum is in `ℝ≥0∞`; treating it as an arbitrary rational or real tsum would be a different assertion.

**Verification and limits.** A single Lean diagnostic module, [Diagnostics.lean](/home/ubuntu/aklt/reports/TS_H3M_04/scratch/Diagnostics.lean), imported the two leaf modules without producing proofs or rebuilding the repository. It exited successfully. Each declaration has type `Prop` with no external parameters; the finite word and pair-type instances synthesize. The printed series and cutoff statements retain all their explicit hypotheses. The diagnostic also checked the imported positivity results and the unconditional ENNReal commutation, multiplication and partial-supremum lemmas. See [diagnostics.txt](/home/ubuntu/aklt/reports/TS_H3M_04/scratch/diagnostics.txt).

The exact rational model in [finite_checks.py](/home/ubuntu/aklt/reports/TS_H3M_04/scratch/finite_checks.py) exhausted all **5,461 direction words of lengths 0–6**, including non-trails: **30,948 departure indices** and **110,280 response-pair instances**. Reflection labels and B shifts, fixed-list reward decomposition, finite support membership and first-direction row partition all passed. It also checked 150 reproducible random words of lengths 13, 14 and 16, exercising the long-order branch. The support was empty at length zero, and both zero-length rows were zero. Nonzero closed-trail witnesses included B word N,E,E,S and C word N,E. Exact aggregate results are in [finite_checks.json](/home/ubuntu/aklt/reports/TS_H3M_04/scratch/finite_checks.json).

These computations are finite sanity checks. The infinite-series verdicts rest on the reviewed definitions, supplied hypotheses and unconditional ENNReal library results, not on extrapolation from finite samples. No sub-agents were launched, and no formal proofs were written.
