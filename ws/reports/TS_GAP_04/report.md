STATUS: COMPLETE

| Leaf | Verdict | Difficulty | Reason |
| --- | --- | --- | --- |
| `AKLT.Blueprint.Gap.ProductPoincareTransportStatement` | TRUE | medium | The site and configuration equivalences preserve every singleton fibre and both quadratic forms. |
| `AKLT.Blueprint.Gap.ProductCouplingTransportStatement` | TRUE | medium | Pulling back the joint mass preserves its two marginals and its Hamming cost. |
| `AKLT.Blueprint.Gap.ThresholdSpacingStatement` | TRUE | easy | The threshold is at least 16^4; two monotone square roots give spacing at least 16. |
| `AKLT.Blueprint.Gap.ContainingBlockCountStatement` | TRUE | medium | The offset-to-centre bijection gives exactly (2M+1)^2 labels. |
| `AKLT.Blueprint.Gap.ExteriorBlockCountStatement` | TRUE | medium | The halo offset injection remains valid at minimal periods; the difference is 8M+8. |
| `AKLT.Blueprint.Gap.BlockVolumeBoundStatement` | TRUE | easy | (2M+1)^2 is at most L.val*N.val, the number of sites. |
| `AKLT.Blueprint.Gap.PeriodicNeighbourCouplingStatement` | TRUE | hard | A common label has cost 0, at most 1+K, or 1; the stated counts give the bound. |
| `AKLT.Blueprint.Gap.TorusColourStatement` | TRUE | medium | The explicit cycle colouring handles both parity cases and every wrap edge. |

All eight statements are true and self-sufficient for the conclusions they assert. No fixes or missing premises were found. This is a truth audit and proof-route assessment; no Lean leaf proofs were written.

**Sources and definition closure.** The repository snapshot is branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The exact leaf declarations and all project definitions in the following chains were read. Ordinary Mathlib finite sums, finsets, equivalences, integer intervals, real/complex arithmetic, and finite nonzero `ZMod` types have their standard meanings.

- [Gap/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:15): `Config`, `restrict`, `AgreeOn`, `fibre`, `blockLaw`, `blockAverage`, `couplingCost`, `ProductChange`, and `Carries`; also [the periodic definitions](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:214): `reduction`, `torusSquare`, `torusHalo`, `volumeCount`, `haloCount`, `cycleColour`, `torusColour`, `TorusRangeOne`, `BlockInfluence`, and `PeriodicCounts`. The last is explicitly a conjunction of the two label-count equations and the volume bound, rather than an unproved named theorem.
- [Defs/Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:9): `Weight`, `normalize`, `PositiveProbability`, `Probability`, `complexMean`, `variance`, `AgreeOutside`, `conditionalExpectation`, `blockDirichlet`, `dirichlet`, `PoincareLower`, `hamming`, and `Coupling`. `PoincareLower` quantifies over complex functions and uses rate one per site.
- [Defs/FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:42): `conditionOn` is normalization of the event-restricted weight. [Defs/FrameModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:50): `marginal` is a finite pushforward sum; [its colouring predicate](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:14) uses the actual frozen torus bonds.
- [Defs/Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:74): `Plane = ℤ × ℤ`, `square` uses inclusive integer-coordinate intervals, `shellSpacing u = sqrt(sqrt(u))`, and `geometryThreshold l = (max 16 (6*(l+1)))^4`.
- [Challenge/Main.lean](/home/ubuntu/aklt/repo/AKLT/Challenge/Main.lean:17): `Size`, `size_neZero`, `Site`, `Direction`, `Bond`, and `nextSite`; in particular each period is at least three and `Site L N = ZMod L.val × ZMod N.val`.

The manuscript comparisons used the local TeX sources for `l:boxlift`, `l:stopped`, `t:periodic`, and `l:colour`, together with the transport applications in [the proof of t:mainW](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:438). No other blueprint leaf was assumed as an extra premise.

**Declaration and boundary checks.** [Inspect.lean](/home/ubuntu/aklt/reports/TS_GAP_04/scratch/Inspect.lean) imported the supplied compiled modules and printed all eight statements plus their principal structures, successfully exiting with code 0 on Lean `4.35.0-rc2`; see [inspect.log](/home/ubuntu/aklt/reports/TS_GAP_04/scratch/inspect.log). This checks the actual elaborated binders, not provability. The alphabet `Fintype` binders survive in the transport leaves; the finite/nonempty alphabet binders survive in the periodic coupling leaf. No needed instance premise was silently dropped. Classical decidability is used explicitly in the source definitions and can be restored with `classical` when working with their finite filters; it is not an extra mathematical hypothesis.

Python checks independently enumerated all labels and sites for 125 parameter triples: `M=1,…,5` and each period independently in `2*M+3,…,2*M+7`. Both exact counts and the volume bound passed at 16,125 sites, including 45 triples with at least one minimal period. Cycle-colour checks passed for periods 3 through 500 (125,247 edges), and torus-colour checks passed for all period pairs 3 through 30 (426,888 directed bonds). These finite checks support the boundary analysis; the general reasons and routes below determine the verdicts. Counts and ranges are saved in [small_cases.json](/home/ubuntu/aklt/reports/TS_GAP_04/scratch/small_cases.json).

**Nonvacuity.** The statements have ordinary nondegenerate instances. Identity product changes on a finite binary product witness the transport setting. For `l=1`, the threshold `u=65536` has spacing exactly 16. For `M=1, L=N=5`, the counts are `T=9`, `H=16`, `A=25`; the uniform binary product law satisfies range one and influence with `K=0`, and inputs differing at one site exist. The period-three colouring has cycle colours `0,1,2`. Some individual empty-product or singleton-alphabet instances are trivial, as intended; none makes the whole leaf vacuous.

**1. ProductPoincareTransportStatement — TRUE (medium).**

[Exact statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:264); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:801).

ProductChange supplies both a site equivalence and a configuration equivalence preserving equality at each corresponding coordinate. Hence every singleton exterior fibre, its numerator and denominator, the complex mean, variance, and the unnormalised sum of one-site Dirichlet forms are preserved. Neither positivity nor nonempty alphabets are needed for these algebraic identities; zero denominators agree on both sides.

Lean traps: Use `coordinate_eq`, not merely the configuration equivalence, to identify `AgreeOutside {x}` with the corresponding singleton fibre. The premise `Carries e p q` reads `q (e.configurations σ) = p σ`. There are no positivity, normalization, alphabet-nonemptiness, or positive-gap premises here, and none is needed: transport the finite sums and quotient denominators exactly, including zero denominators. For arbitrary unnormalized weights, do not assume variance on a one-point space vanishes.

Proof route (two lines):  
For a test function f on Config S use f composed with e.configurations.symm on Config T; reindex the finite sums and identify singleton fibres using coordinate_eq.  
Transport variance and the sum of one-site forms exactly, then apply the supplied PoincareLower q g.

Fix: none.

**2. ProductCouplingTransportStatement — TRUE (medium).**

[Exact statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:272); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:801).

Pulling c.mass back along e.configurations in both coordinates gives nonnegative mass with marginals p and p′ by Carries and finite reindexing. coordinate_eq and the site equivalence preserve the number of unequal coordinates, so the cost is exactly equal. Coupling does not itself require total mass one, and the argument works for its stated arbitrary weights.

Lean traps: `Coupling` has nonnegative mass and its two marginal identities; it does not include total mass one. Preserve exactly these fields rather than assuming the weights are probabilities. A permutation of configurations alone need not preserve Hamming cost; the site equivalence and `coordinate_eq` are essential. Empty alphabets cause no missing instance or division issue.

Proof route (two lines):  
Set the pulled-back mass to c.mass (e.configurations sigma) (e.configurations tau) and reindex each marginal.  
Use coordinate_eq to biject the unequal-coordinate finsets, then reindex both cost sums.

Fix: none.

**3. ThresholdSpacingStatement — TRUE (easy).**

[Exact statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesMain.lean:13); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:56).

geometryThreshold l is the natural number (max 16 (6*(l+1)))^4 and shellSpacing u is the real number sqrt(sqrt(u)). Thus the premise implies u >= 16^4 = 65536, and monotonicity of the two real square roots yields shellSpacing u >= 16. The statement also holds at l=0 and at the threshold.

Lean traps: `l` and `u` are naturals, whereas `shellSpacing u` is real. Cast the fourth-power bound before using real square-root monotonicity. The spacing is `Real.sqrt (Real.sqrt u)`, with no floor and no integer or rational division. `l=0` is allowed and causes no failure; the lower bound comes from `max 16 ...`.

Proof route (two lines):  
Use max >= 16 and monotonicity of fourth powers to get 65536 <= u, then cast the inequality to the reals.  
Apply Real.sqrt monotonicity twice and evaluate sqrt(sqrt(65536)) = 16.

Fix: none.

**4. ContainingBlockCountStatement — TRUE (medium).**

[Exact statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:14); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:314).

For fixed x, the labels containing x are exactly x - reduction(z) for z in the integer offset square of radius M. Distinct offsets have coordinate differences of absolute value at most 2*M < L.val,N.val, so reduction is injective. The square contains (2*M+1)^2 offsets, and the statement counts centre labels rather than distinct block sets.

Lean traps: `square` is a product of inclusive integer intervals, and `torusSquare` uses `Finset.image`, which removes duplicate reductions. Establish injectivity before using image cardinality. The filter is over all centre labels in `Site L N`, not over distinct finsets of sites. The integer casts in negative offsets are intentional; there is no truncated natural subtraction in those intervals.

Proof route (two lines):  
Construct a bijection between the centre-label filter and the offset square via z maps to x - reduction(z), using the defining image membership.  
Prove modular injectivity from 2*M < L.val,N.val and count the two integer intervals.

Fix: none.

**5. ExteriorBlockCountStatement — TRUE (medium).**

[Exact statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:21); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:314).

torusHalo is precisely the translated radius-(M+1) square and contains torusSquare. Reduction is still injective on its offsets because coordinate differences are at most 2*M+2 < L.val,N.val, even at a period equal to 2*M+3. Subtracting inner label count (2*M+1)^2 from outer label count (2*M+3)^2 gives 8*M+8, including the four corners.

Lean traps: The halo is the full sup-distance one-neighbourhood, including corners. Its square has radius `M+1`; at `L.val=2*M+3` it fills that coordinate cycle and is still injectively parametrized. Do not apply the containing-count leaf at `M+1`: that leaf would require the stronger period bound `2*M+5`. Prove the elementary injection directly from `2*M+2 < L.val,N.val`. For `Finset.card_sdiff`, first establish the inner-label subset relation; otherwise natural subtraction can hide an error.

Proof route (two lines):  
Count halo-containing labels by the radius-(M+1) offset bijection; prove square inclusion so the inner label filter is a subset.  
Identify the exterior-label filter with the finset difference and subtract the two cardinalities to obtain 8*M+8.

Fix: none.

**6. BlockVolumeBoundStatement — TRUE (easy).**

[Exact statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:27); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:314).

Size gives nonzero positive moduli, so Fintype.card (Site L N) = L.val*N.val. Each period is at least 2*M+3 and therefore at least 2*M+1, implying (2*M+1)^2 <= L.val*N.val in the naturals. No probability law or invariance hypothesis is needed.

Lean traps: `Fintype.card (Site L N)` counts the entire product type, not a chosen block finset. `Size` includes `3 ≤ L.val,N.val`, and `size_neZero` supplies the nonzero-modulus instances, so the finite `ZMod` cardinality formulas apply. All arithmetic in this leaf is in the naturals.

Proof route (two lines):  
Use the product cardinality formula and ZMod cardinalities to identify Fintype.card (Site L N) with L.val*N.val.  
Multiply the two natural inequalities 2*M+1 <= L.val and 2*M+1 <= N.val.

Fix: none.

**7. PeriodicNeighbourCouplingStatement — TRUE (hard).**

[Exact statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:34); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:314).

hamming sigma tau = 1 identifies a unique differing site x. For a common label, a containing block has identical full conditional laws and cost 0; an exterior-halo block uses BlockInfluence, with cost at most 1+K after restoring its fixed exterior; every other block uses TorusRangeOne and has cost 1. The positive law normalizes every fibre, and Size makes the number A of labels positive. PeriodicCounts gives T containing and H exterior-halo labels, so the uniform mixture has cost at most 1-(T-H*K)/A. A strict contraction premise H*K<T is unnecessary for this coupling estimate.

Lean traps: `BlockInfluence` couples laws on block coordinates; `blockAverage` averages full-state fibres. Restore the appropriate input exterior in each component to obtain the required full-state coupling. At an exterior-halo label, the old disagreement contributes an additional 1 to the block cost K. In the remaining noncontaining labels, only the block samples are identical; the full outputs retain the exterior disagreement. Count centre labels, including corner halos, and justify disjoint-class cardinalities before using natural subtraction (or perform the final algebra over the reals). The quotient is real, with positive denominator A=L.val*N.val≥9. The displayed bound needs neither an additional period bound nor `haloCount M*K < volumeCount M`: `PeriodicCounts` is already an explicit premise, and strict contraction is a later spectral requirement. `K≥0` and `volumeCount M≤A` also make the right side nonnegative.

Proof route (two lines):  
For each label lift either an identical block sample or the supplied block-law coupling to full configurations by restoring the corresponding input exterior.  
Average these couplings over the same uniform label, identify the full marginals as blockAverage, and sum the costs 0, 1+K, and 1 with PeriodicCounts.

Fix: none.

**8. TorusColourStatement — TRUE (medium).**

[Exact statement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesPeriodic.lean:52); [paper argument](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:434).

Size guarantees both cycle lengths are at least three. On even cycles cycleColour alternates 0,1 including the wrap edge; on odd cycles the last residue is coloured 2 and is adjacent to colours 1 and 0. Every frozen torus bond changes exactly one summand in torusColour, so adding the other summand modulo 3 preserves inequality. This includes all parity choices and period three.

Lean traps: `x.1.val` and `x.2.val` are the canonical natural representatives of nonzero `ZMod` moduli, not arbitrary integer lifts. Split successor and wrap cases; omitting wraparound would miss the odd-cycle issue. `m-1` is natural subtraction but is safe because `Size` forces `m≥3`. Check addition modulo 3, not equality of unreduced natural sums. `ProperTorusColouring` concerns the frozen horizontal and vertical bonds, not diagonal halo adjacency.

Proof route (two lines):  
Check successor residues and the wrap edge of each even or odd cycle, using ZMod.val in the range 0 <= i < m.  
Split the bond direction; adding the unchanged cycle colour modulo 3 preserves the unequal endpoint colours.

Fix: none.
