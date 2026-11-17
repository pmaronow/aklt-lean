STATUS: COMPLETE

| Leaf (all in `AKLT.Blueprint.H3`) | Paper label | Verdict | Difficulty | Reason |
| --- | --- | --- | --- | --- |
| [RawSuccessorStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesAutomaton.lean:12) | `l:automaton-quotient` | **TRUE** | medium | Retained bonds translate injectively; the new bond is explicitly unused. |
| [ProjectionRealizationStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesAutomaton.lean:19) | `l:automaton-quotient` | **TRUE** | easy | The fibre hypotheses supply every field required by Correct. |
| [PhaseFoldExpansionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesPhase.lean:12) | `l:phase-expansion` | **TRUE** | medium | Every terminal history has exactly one A-to-C or B-to-D change. |
| [SingleChangeFactorStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesPhase.lean:21) | `l:phase-expansion` | **TRUE** | medium | The surviving change has exactly the base and long-order factors. |
| [ExposureListExpansionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesPhase.lean:30) | `l:phase-expansion` | **TRUE** | medium | The recursion gives inclusive prefix products; Nodup preserves multiplicity. |
| [LongOrderingMultiplierStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesPhase.lean:37) | `l:phase-expansion` | **TRUE** | medium | The two stable, disjoint filters have exactly the specified prefixes. |
| [PrefixCoefficientCausalityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesPhase.lean:53) | `l:phase-expansion` | **TRUE** | medium | All input data at i<L use only vertices through i+1<=L. |
| [PhaseSplitAlgebraStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesPhase.lean:62) | `l:phase-expansion` | **TRUE** | medium | The given matrix equality and suffix linearity suffice for the split. |

All eight leaves are true and self-sufficient as written. No missing premises, counterexamples, unintended vacuity, or required corrections were found. No proofs were written.

The automaton argument matches the paper’s [raw-window definition and successor closure](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:21) and [quotient lemma](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:315). The phase argument matches the [transition table](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:422) and [phase-expansion lemma and proof](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:457). In particular, the paper explicitly retains prefix history in a true suffix. The phase leaves state finite algebra and prefix causality that remain valid on arbitrary words; they do not need the surrounding paper’s closed-trail restriction.

**Definition audit.** The statements were read in their exact modules and checked against these transitive, relevant definition chains; library list and finite-sum conventions were also inspected.

| Source | Definitions checked |
| --- | --- |
| [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:7) and [Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:109) | `Plane`, `Compass`, `Compass.step`, `Compass.reverse`, `neighbours`, `PairType`, and their finite instances. |
| [Trails.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:8) | `localThreshold`, `passageFactor`, `alphaBound`, `betaBound`, `betaPrimeBound`, `DirectionWord`, `wordVertex`, `wordBond`, `wordIncoming`, `wordStraight`, `departureCount`, `wordRevisit`, `trailBaseWeight`; `IsTrail` was checked to distinguish its stronger contract from `RawWindow`. |
| [Automaton.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Automaton.lean:8) | `RawWindow`, `windowArrival`, `windowSuccessor`, `WindowAdmissible`, `StepKind`, `windowKind`, every `MemoryQuotient` field, `MemoryQuotient.Correct`, `CompatibleProjection`. |
| [Kernel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:8) | `kernelStart`, `kernelCentre`, `kernelIncoming`, `deadAt`, `responseNeighbours`, `liveOtherNeighbours`, `responsePairs`, `pairCoefficient`, `responsePairType`, `kernelWitness`, `witnessKappa`, `firstVisitList`, `exposureSum`; `kernelOrdering` was checked to distinguish it from `longOrdering`. |
| [Stationary.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Stationary.lean:9) and [prefixPhases](/home/ubuntu/aklt/repo/AKLT/Defs/Stationary.lean:120) | `Phase` and its finite instance, `phaseTerminal`, `phaseInitial`, `phaseDiagonal`, `phaseTransition`, `prefixPhases`. |
| [Computational.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Computational.lean:49) | `takeWord`, `truePhaseCoefficient`, `longOrdering`, `truePhaseSuffix`. |
| [H3/Basic.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/Basic.lean:11) | `trueKind`, `phaseUpdate`, `phaseRun`, `singleChange`, `longMultiplier`, `orderedMultiplier`, `longRewardTerm`. |

**Per-leaf assessment and two-line proof routes.** These are routes for the future writers, not formal proofs.

**RawSuccessorStatement: TRUE (medium).** RawWindow is injectivity of the unoriented-bond map. For positive memory, each retained successor bond is the translate by minus the first step of old bond i+1; its last bond is the same translate of the newly appended bond. Old injectivity separates retained bonds, and WindowAdmissible explicitly separates the appended bond from every old bond. The case m=1 has just one successor bond; the hypotheses have nonempty examples.

Proof route: Establish successor-vertex identities and transport equality of two-element Finsets through the inverse translation.  
Split a pair of successor indices into retained/last cases; apply old bond injectivity or the unused-bond clause of admissibility.

Lean cautions: bonds are Finsets, so transport them by an injective translation; guard the last-index subtraction with 1<=m.

**ProjectionRealizationStatement: TRUE (easy).** CompatibleProjection supplies a raw representative in every fibre, agreement of admissibility and kind, agreement of projected admitted successors, and arrival agreement whenever an admitted nonrevisit edge exists. Set Q.project to pi on all words and define its other fields using chosen representatives. These are exactly the clauses of MemoryQuotient.Correct, including its conditional arrival clause; no separate closure, minimization, or arrival condition on revisit-only classes is needed.

Proof route: Use classical choice on fibre surjectivity; define representative, allowed, kind, successor and arrival from the chosen raw word, and set project=pi.  
Apply the fibre clauses between each raw word and its representative; an admitted nonrevisit direction supplies the existential needed for arrival agreement.

Lean cautions: use classical choice and decidability to define the representative and Boolean allowed field; define project on every direction word, including nonraw ones. The q=0 parameter has no pi because DirectionWord m is inhabited, but the theorem has nonvacuous instances (m=1, q=4).

**PhaseFoldExpansionStatement: TRUE (medium).** The transition matrices have only diagonal entries and the two off-diagonal entries A-to-C on turns and B-to-D on straights. Initial mass lies in A and B, terminal mass is selected only in C and D, and no transition returns from C or D. Every contributing product consequently has exactly one of those two changes, at a unique index, and singleChange is precisely its product. This remains algebraically valid for zero or negative rational rewards. At n=0 both sides are zero.

Proof route: Induct through finRange in path order, keeping the A and B diagonal products and the C and D single-change sums as four coordinate invariants.  
Use the sparse transition table for the next coordinate update, then select C+D with phaseTerminal and identify the products with singleChange.

Lean cautions: phaseRun is a left fold of row-vector updates in increasing finRange order; preserve that order and do not assume reward positivity.

**SingleChangeFactorStatement: TRUE (medium).** At a revisit index j both change entries are zero, matching longRewardTerm=0. At a straight first departure only B-to-D survives, with passage factors at exactly the straight first indices i<=j. At a turning first departure only A-to-C survives, with passage factors at every straight first index and each turning first index i<=j. In both cases all departures contribute the base factor 1/5 on revisits or 1/3 otherwise, exactly trailBaseWeight. This argument uses only the revisit and straight flags, not trail validity or any extra property of witnessKappa.

Proof route: Split on the revisit and straight flags at j and use the transition table to eliminate the impossible phase change.  
Factor the surviving finite product into its base factors, the reward at j, and the passage-factor mask in longMultiplier; commute rational products without dividing by the reward.

Lean cautions: revisit takes precedence over straight, products include j, and all divisions are in Q; do not cancel or divide by witnessKappa, which may be zero.

**ExposureListExpansionStatement: TRUE (medium).** The recursion x_i*(reward_i+tail) gives each occurrence its reward times the inclusive prefix product of passage factors. Nodup makes occurrences correspond exactly to l.toFinset and makes idxOf select that occurrence. Membership in l.toFinset prevents the absent-index default from contributing. The empty list gives zero on each side; rewards may be arbitrary rationals, and no first-visit or trail hypothesis is required.

Proof route: Induct on the nodup list; the empty case is zero and the cons case separates the head from the tail in toFinset.  
Use idxOf(head)=0 and idxOf(tail member in head::tail)=1+idxOf(tail member), so each tail prefix product gains exactly the head factor; distribute the finite sum.

Lean cautions: toFinset discards multiplicity, so retain Nodup; idxOf and take(idxOf+1) must be used only for actual members, with the +1 giving an inclusive product.

**LongOrderingMultiplierStatement: TRUE (medium).** firstVisitList is the increasing finRange list filtered by nonrevisit. Its straight and nonstraight filters are disjoint, so their concatenation is nodup and contains exactly the nonrevisit indices. For a straight member j its inclusive prefix contains precisely straight first indices i<=j. For a turning member j it contains all straight first indices plus turning first indices i<=j. Those are exactly the two masks in longMultiplier, including j itself. No trail or lower length assumption is needed.

Proof route: Use nodup and increasing order of finRange, preservation by filtering, and disjointness of the straight/nonstraight filters to prove the first two conjuncts.  
For each member j, identify the elements of take(idxOf(j)+1) in the appropriate block and convert its nodup product into the conditional product over Fin n.

Lean cautions: preserve the stable order of the two list filters; prove prefix membership before changing list products to Finset products. The definition is longOrdering, not the short-length branch of kernelOrdering.

**PrefixCoefficientCausalityStatement: TRUE (medium).** For i<L<=n, takeWord retains the outgoing direction at i, the incoming direction at i-1 when i>0, all vertices through i+1, and all earlier departure vertices. The min in departureCount is i for both lengths. Thus revisit/straight flags and deadAt agree, as do responseNeighbours, liveOtherNeighbours, responsePairs, pairCoefficient and witnessKappa. In particular i=L-1 needs the vertex at L, which wordVertex of a length-L prefix does retain. Arbitrary nontrail words also satisfy the equality; L=0 merely has no departure index.

Proof route: Establish prefix-letter equality and wordVertex equality through L, then use i<L to identify incoming directions, departure counts, revisit flags and straight flags.  
Transport the equalities through deadAt, the neighbour/pair Finsets and pairCoefficient to witnessKappa, then unfold truePhaseCoefficient.

Lean cautions: takeWord has an east-padding branch excluded by L<=n; prove vertex agreement through L, not just below L, and normalize min and guarded Nat subtraction before comparing the two Fin index types.

**PhaseSplitAlgebraStatement: TRUE (medium).** prefixPhases is a forward row-vector fold, and truePhaseSuffix is the remaining full-word fold from a phase basis vector followed by phaseTerminal. Splitting finRange at L splits the fold; the displayed premise identifies the first L full-word matrices with the prefix matrices. Linearity of the suffix fold gives the phase-indexed contraction in the conclusion. The suffix correctly keeps the original word's revisit and dead-neighbour history. The premise is sufficient without any other blueprint theorem or trail assumption; both L=0 and L=n are valid.

Proof route: Split the finRange fold into take L and drop L, identify the initial fold with prefixPhases(takeWord w L) using the assumed coefficient equalities and index embedding.  
Expand that prefix row in the four phase basis vectors and use linearity of the suffix fold and terminal functional to obtain the displayed sum.

Lean cautions: use the cast from Fin L to Fin n, the first L entries of finRange, and basis vectors delta(psi=phi) in the row-vector orientation. Do not recompute the suffix coefficients on a fresh word.

**Shared Lean and boundary checks.** All eight declarations are closed `Prop`s; inspection showed no accidentally omitted hypothesis or instance parameter. The implicit word length remains present in the underlying definitions. `Phase` and `Compass` have the intended explicit finite instances, while `Fin n` supplies the index type; no cardinality identity between a `Finset` and an ambient type is being assumed. Classical choice/decidability is available where needed and does not add a mathematical premise.

The weights and rewards in these leaves are rational throughout. The factors `1/3`, `1/5`, and the exact dyadic `kernelWitness .C` are not natural-number divisions or real approximations. The only inverses used in the passage factors have the fixed nonzero thresholds `961/1000` and `187/200`. None of the arguments divides by a reward. Empty lists, empty products, `n=0`, `m=1`, `L=0`, and `L=n` are consistent. A quantified index in `Fin 0` is absent in the expected boundary cases; this does not make any whole leaf unintentionally vacuous.

**Validation.** [inspect.lean](/home/ubuntu/aklt/reports/TS_H3M_01/inspect.lean) imported the two existing compiled leaf modules with Lean `v4.35.0-rc2`, printed the exact eight statements, and checked the underlying function signatures. It completed with exit code 0; its output is in [lean-inspection.txt](/home/ubuntu/aklt/reports/TS_H3M_01/lean-inspection.txt). This was one Lean process, with no proof declarations or repository build.

[check_small_cases.py](/home/ubuntu/aklt/reports/TS_H3M_01/check_small_cases.py) independently modeled the definitions using exact `fractions.Fraction` arithmetic. All checks passed; [small-case-results.json](/home/ubuntu/aklt/reports/TS_H3M_01/small-case-results.json) records the bounds and counts:

- Raw windows at memory lengths 1–7: 4,020 raw windows and 11,516 admitted successors.
- All abstract kind sequences of lengths 0–6 with three reward assignments, including zero, negative, and fractional rewards: 3,279 fold identities, 18,045 single-change factorizations, and 12,030 long-order member identities.
- All straight-flag patterns on 0–5 indices and every ordered nodup sublist, with signed/zero rewards: 11,625 exposure identities.
- Every compass word of lengths 0–5, including immediate reversals and repeated bonds: 1,365 words, 18,356 prefix departure-matrix checks, and 7,737 prefix/suffix splits, including both endpoint splits.

These bounded checks are supplementary evidence, not formal verification of the universally quantified statements. Projection realization was assessed by its direct representative construction. The repository was read only; all output and scratch files are under the requested working directory.

All eight machine-readable records, including the reasons, fixes (`None.`), two-line routes, difficulty, and Lean cautions, are in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_H3M_01/verdicts.jsonl).
