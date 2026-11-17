STATUS: COMPLETE

| Leaf (namespace `AKLT.Blueprint.H3`) | Verdict | Difficulty | Finding |
| --- | --- | --- | --- |
| [ClosedTrailStepGeometryStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesDomination.lean:104) | TRUE | easy | The first-hit and centre-avoidance clauses include exactly the required indices. |
| [SuffixWordComparisonStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesDomination.lean:115) | TRUE | medium | The explicit entrywise and successor premises suffice for the matrix-product comparison. |
| [StationaryWordExpansionStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesDomination.lean:133) | TRUE | medium | Expanding the iterate retains every absolute direction word and phase history. |
| [StationaryFreeEdgeStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesCertificate.lean:13) | TRUE | medium | Centre deletion and the known-site rules can only reduce the corresponding free coefficient. |
| [LongTrailPrefixStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesPrefix.lean:13) | TRUE | easy | Strictly greater length puts the entire twelve-step prefix before the target hit. |
| [LongRowRegroupingStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesPrefix.lean:49) | TRUE | hard | The supplied factorization and equivalences justify finite regrouping; the zero suffix vanishes. |
| [ReflectionGeometryStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesReflection.lean:12) | TRUE | medium | Horizontal reflection fixes all B sites and the virtual incoming direction. |
| [ReflectionLivePairsStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/NodesReflection.lean:23) | TRUE | medium | Reflection transports dead predicates and the two-element finite subsets bijectively. |

All eight statements are true as written and self-sufficient. No missing premise, correction, or counterexample was found. Full names and the requested six fields are recorded in [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_H3M_03/verdicts.jsonl). These are mathematical truth verdicts; no proofs of the leaves were written.

The exact statements were read in the four linked modules and checked against Lean's elaborated declarations. The paper arguments were read at `l:stationary-domination`, `l:stationary-local-global`, `l:prefix-domination`, and `l:kernel-reflection` in [app-input-contracts.tex](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:555).

The project definitions were traced through the following files:

- [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8) and [Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:110): `Plane = ℤ × ℤ`, `Compass`, its finite enumeration, displacements and reversal, `neighbours`, and `PairType`.
- [Trails.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:9): the rational threshold/coefficient tables, `passageFactor`, `DirectionWord`, `wordVertex`, `wordBond`, `IsTrail`, `wordIncoming`, `wordStraight`, `departureCount`, `wordRevisit`, `trailWeight`, and `trailBaseWeight`.
- [Kernel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Kernel.lean:9): the four fixed kernel parameters, `ClosedTrail`, `deadAt`, `responseNeighbours`, `liveOtherNeighbours`, `responsePairs`, `pairCoefficient`, `responsePairType`, `kernelWitness`, `witnessKappa`, `firstVisitList`, `shortOrderLE`, `kernelOrdering`, `exposureSum`, and `closedContribution`.
- [Automaton.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Automaton.lean:9): `RawWindow`, `windowArrival`, `windowSuccessor`, `WindowAdmissible`, `StepKind`, `windowKind`, `lastWindowWord`, all `MemoryQuotient` fields, `MemoryQuotient.Correct`, and `reflectDirection`.
- [Stationary.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Stationary.lean:10): the finite `Phase` type, initial/terminal/diagonal/transition tables, `relaxedReward`, `freeCoefficient`, `stationaryCoefficient`, `stationaryApply`, `prefixPhases`, `FirstDirection`, `SurvivingPrefix`, and `firstDirectionPartialRow`.
- [Computational.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Computational.lean:46) and [H3/Basic.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/Basic.lean:12): `appendWords`, `takeWord`, `truePhaseCoefficient`, `truePhaseSuffix`, `trueContinuationSum`, `stationaryReward`, `suffixWindow`, `stationaryWordValue`, `reflectSite`, and `reflectWord`. Nonnegativity follows directly from the positive tables and finite sums/products; existing helper statements in [Positivity.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/H3/Positivity.lean:11) were also inspected.

**ClosedTrailStepGeometryStatement.** `ClosedTrail` requires centre avoidance at every `j ≤ n` and target avoidance at every `j < n`. For `i : Fin n`, both `i.val` and `i.val + 1` satisfy the first bound, and `i.val` satisfies the second. The endpoint may be the target, as required. The vertex increment is the difference of two consecutive prefix sums and does not require bond injectivity.

Route: Isolate the summand with index `i` in the definition of `wordVertex`.  
Apply the two avoidance clauses at `i.val` and `i.val + 1`, using `i.isLt`.

Lean traps: `wordVertex` clamps indices beyond the word, so its increment formula needs `i.val < n`; the `Fin n` binder supplies that condition. For `n = 0` there is no departure index; this expected boundary case does not make the whole leaf vacuous.

**SuffixWordComparisonStatement.** Write the completed word as `w = appendWords P v`. At suffix time `L + k`, the actual direction is `v k`, the actual next vertex is the current vertex plus its displacement, and the second explicit premise gives the quotient successor. The first explicit premise bounds every phase-matrix entry. True and stationary coefficients and terminal rewards are nonnegative, so successive multiplication preserves the bound. `ClosedTrail` puts the final vertex at `kernelTarget X`, where `stationaryReward` is exactly `phaseTerminal`. At time `L`, the remembered word and endpoint are those of `P`.

Route: Express the forward suffix fold as the backward finite sum over phase histories and align its classes, directions, and positions.  
Induct backward using nonnegative entrywise domination, ending with the matching target rewards.

Lean traps: The forward fold and the backward recursion use opposite presentations of the same matrix product; preserve the chronological order. The empty suffix is allowed: both sides equal the same phase terminal reward because `P` is then already closed. `takeWord`'s default east letters never enter the relevant indices. A separate `SurvivingPrefix` hypothesis is unnecessary here because the needed local comparison is supplied explicitly.

**StationaryWordExpansionStatement.** This is a finite algebraic identity for arbitrary quotient data. Expanding one application selects one absolute direction and one next phase; repeating gives exactly the recursion in `stationaryWordValue`. Different direction words remain distinct summands even when their quotient successors coincide. Quotient correctness and coefficient positivity are unnecessary for the equality.

Route: Induct on `r`, using the unique empty word for the base case.  
Split a word of length `r + 1` into its head and tail, expand the operator, and interchange the finite sums.

Lean traps: `DirectionWord 0` has one element, since it is the function type `Fin 0 → Compass`. Its sum is not an empty sum. Reindex the full finite function type, preserving parallel labelled edges, and handle the casts between `Fin (r + 1)` and head/tail indices.

**StationaryFreeEdgeStatement.** Terminal, disallowed, and otherwise killed stationary edges have coefficient zero. A surviving known-site edge is diagonal with coefficient `1/5`; every free diagonal is at least `1/5`, and all free off-diagonal entries are nonnegative. At an ordinary site, translate its neighbour sets to the origin. Translation preserves the pair type and hence its witness. Deleting the centre removes nonnegative pair contributions. If only one non-outgoing live neighbour remains, an existing outgoing pair receives `betaPrimeBound` instead of `betaBound`, which decreases its coefficient for both straight and turn rows. All other retained coefficients agree.

Route: Split the stationary definition into killed, known-site, and ordinary cases, comparing diagonal entries with the explicit phase table.  
Translate ordinary response pairs to the origin and compare their live sets with `betaPrimeBound ≤ betaBound` and nonnegative added terms.

Lean traps: `Q.Correct` does not fix `Q.arrival a` on revisit-only behavior; revisit transitions are independent of that field and reward. If following the paper's two-other-neighbour proof, recover a raw representative for an arbitrary class `a` before using correctness to infer nonreversal. The direct live-set comparison also works for arbitrary incoming/outgoing labels, allowing a proof with weaker quotient assumptions. The witness is the exact dyadic rational `5404319552844595 / 4503599627370496`, not `6/5`.

**LongTrailPrefixStatement.** Restricting a word of length greater than twelve to its first twelve directions preserves its vertices through time twelve, its initial nonreversal, and injectivity of the unoriented bonds. It also preserves the first direction. Every prefix vertex has index `j ≤ 12 < n`, so it precedes the original first target hit. Centre avoidance holds at those indices as well.

Route: Identify all prefix vertices and bonds with the corresponding full-word vertices and bonds, and restrict `IsTrail` and `FirstDirection`.  
Use `j ≤ 12 < n` for target avoidance and the closed-trail centre clause for centre avoidance.

Lean traps: `SurvivingPrefix` excludes the target at the prefix endpoint. The strict hypothesis `12 < n` supplies this fact; replacing it by `12 ≤ n` would fail for a first hit at time twelve. No extra condition on `d₀` is needed; an eastward first step is already excluded by centre avoidance.

**LongRowRegroupingStatement.** The three explicit premises supply the word equivalences, survival of all relevant long prefixes, and phase factorization of every contributing long word. Split the length interval into `1..12` and `13..R`. The substitution `n = 12 + r` identifies the latter interval with `1..(R - 12)`. The supplied equivalence reindexes each word by its actual prefix and suffix. A closed extension of a surviving prefix automatically has the required first direction. Nonsurviving prefixes contribute zero by the second premise. Each surviving prefix's extra `r = 0` term in `trueContinuationSum` is zero because its endpoint is not the target. All sums are finite and each original prefix keeps its own summand.

Route: Split and reindex the length/word sums, then apply the supplied phase factorization on the contributing terms.  
Remove nonsurviving terms, commute the finite sums, and insert the vanishing zero-length suffix to match `trueContinuationSum`.

Lean traps: `Finset.Icc 1 R` includes `R`; `Finset.range (R - 12 + 1)` includes suffix length `R - 12`. The strict bound on `R` prevents truncated natural subtraction. The equivalence's stated inverse fixes the complete concatenation, so no further suffix-coordinate premise is missing. Do not merge different prefixes that share a class or endpoint. The factorization hypothesis is an explicit hypothesis of this leaf, so no unmentioned phase-expansion result is required.

**ReflectionGeometryStatement.** Reflection `(x,y) ↦ (x,-y)` is additive and involutive. It carries each compass displacement to its reflected displacement, fixes `kernelStart = (-1,0)`, `kernelCentre = (0,0)`, `kernelTarget .B = (1,0)`, and the virtual incoming west direction. Thus it commutes with every clamped vertex sum and maps each bond bijectively. The same indices satisfy the same chronological avoidance conditions. Equality of departure sites is preserved, so every prefix departure count, revisit Boolean, and straightness Boolean is preserved; north and south are interchanged.

Route: Commute reflection with the finite vertex sums and transport bonds and departure-count filters using injectivity.  
Apply the fixed B parameters and the involution to transport `ClosedTrail`, first directions, straightness, and revisits in both directions.

Lean traps: The vertex assertion quantifies over every natural `j`, including `j > n`; both sides then use the full clamped sum. `wordIncoming` must be handled separately at index zero and at a positive index. Row C's target is not fixed, and the statement correctly restricts the closed-trail equivalence to row B.

**ReflectionLivePairsStatement.** The same geometric identities can be derived directly from the definitions without assuming another leaf. Reflection transports the incoming site, outgoing vertex, and neighbour set. It fixes the centre and preserves every prior departure count, so it preserves `deadAt` in both directions. Consequently it maps `liveOtherNeighbours` exactly to its reflected version. Injectivity transports two-element subsets of the outgoing vertex plus those neighbours, giving the stated nested image equality. No distinct-bond or first-hit assumption is used.

Route: Transport vertices, incoming sites, neighbour erases, and the dead predicate under reflection to identify the live-other sets.  
Commute the injective image with insertion and `powersetCard 2` to obtain equality of response-pair sets.

Lean traps: A `Finset.image` can collapse elements, so use the involution to prove injectivity on sites and on finite subsets before transporting cardinality. `responsePairs` inserts the outgoing vertex even when it is dead or equals the erased incoming site; transport that exact definition. Immediate reversals, repeated bonds, and dead outgoing vertices therefore cause no missing-premise problem. Finite-set predicate manipulations can use `classical` locally.

Lean inspection succeeded with Lean `v4.35.0-rc2`, importing the four individual leaf modules from their existing build artifacts. [CheckStatements.lean](/home/ubuntu/aklt/reports/TS_H3M_03/CheckStatements.lean) contains only imports, `#check`, `#print`, `#synth`, and `#eval` commands. [lean-inspection.log](/home/ubuntu/aklt/reports/TS_H3M_03/lean-inspection.log) confirms all eight are closed constants of type `Prop`; no instance argument or intended premise was silently omitted. It also confirms the finite word types at lengths zero and two have cardinalities one and sixteen. All leaf weight comparisons occur in `ℚ`; no real/rational coercion issue arises. The only inverse in the phase weights uses one of the two strictly positive local thresholds.

The reproducible finite checks in [small_checks.py](/home/ubuntu/aklt/reports/TS_H3M_03/small_checks.py) passed; their results are in [small-checks.json](/home/ubuntu/aklt/reports/TS_H3M_03/small-checks.json):

- Exhausted all 21,845 words of lengths zero through seven, checking reflection of clamped vertices, B closed-trail predicates, north/south first directions, straightness, revisits, and live-pair images at 145,636 departures. This includes arbitrary non-trails. Closed-step geometry was also checked on all 28 B/C closed words in this range.
- Checked 614,400 stationary/free coefficient inequalities with exact rational arithmetic over fifty positions, both targets, all four initial directions, allowed/disallowed labels, all incoming/outgoing directions, all kinds, and all phase pairs. Local labels were allowed to violate quotient correctness, exercising the stronger local comparison too.
- Checked 576 iterate/word-expansion equalities for lengths zero through three and arbitrary quotient transitions whose reachable class labels lie in `Fin 3741`.
- Checked closed detours of lengths twelve, fourteen, sixteen, eighteen, and twenty, plus a sixteen-step trail with a genuine revisit; verified the twelve-step stopping boundary, phase splitting and entrywise matrix domination, and length-interval endpoints for cutoffs thirteen through thirty-four.

The finite checks support the boundary analysis; the universal verdicts rest on the definition-level arguments and routes above. Every generated file is in this working directory. The repository was not modified, no sub-agents were launched, and only one Lean process was used.
