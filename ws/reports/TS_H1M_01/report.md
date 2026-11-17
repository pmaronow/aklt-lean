STATUS: COMPLETE

| Leaf (namespace `AKLT.Blueprint.H1`) | Verdict | Difficulty | Finding |
| --- | --- | --- | --- |
| `H1FiniteDataStatementV2` | TRUE | hard | Complete finite Gram data exist; coverage and identification with the reconstructed Lean matrices must be proved. |
| `CoveredSlotEnumerationStatement` | TRUE | easy | Exactly three unit slots at a U tip, or two at a nonremoved U/D corner. |
| `CornerMeanBoundsStatement` | TRUE | medium | Positive normalizers and squared mean bounds follow from the moment formulas. |
| `NormalizedMeanFactorStatement` | TRUE | easy | Finite linearity and positive scaling suffice, including zero mean and an empty field list. |
| `PassageSiteMomentsStatement` | TRUE | medium | Degree-zero through degree-three moments give the identities for arbitrary vectors. |
| `PassageFubiniStatement` | TRUE | medium | Coveredness supplies exactly the passage bonds; removed neighbours have spin zero. |
| `PassageNetworkPositiveStatement` | TRUE | medium | The erased network with all surviving slots satisfies `FiniteSpinNetwork.Valid`. |
| `PassageNextLowerBoundStatement` | TRUE | easy | `passageJ ≥ 4/5` pointwise and the remaining weights are nonnegative. |

All eight statements are mathematically true and self-sufficient as written. No missing premise, counterexample, unintended vacuity, or statement correction was found. These are truth verdicts, not claims that the leaves have been proved in Lean. No proofs were written and no repository files were modified.

**1. `H1FiniteDataStatementV2`.** Exact statement: [NodesCertificate.lean:17](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesCertificate.lean:17). Paper: [t:H1](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:148), [p:certificate](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:830).

The quantifier order is correct: a covered raw pattern first chooses one representation, one inversion and one positive coefficient denominator, followed by witnesses for every exchange sector. None of these choices depends on an external slot assignment. `ClearsDenominator` includes `0 < D₀`; `SectorWitnesses` includes an actual basis equivalence, an integer lower-triangular factor, and positive `g,d,S` through `GramResidualRows`. Both thresholds are positive and less than one.

The complete saved dataset at [/home/ubuntu/aklt/data/h1](/home/ubuntu/aklt/data/h1/README.md) contains witnesses for 7,962 effective patterns and 12,173 central blocks. A fresh exact check passed all 144,554 residual rows: 8,439 blocks use a zero factor and 3,734 use nonzero triangular factors; the smallest residual margin is 195. The paper itself uses direct dominance, two supplied factors and Bareiss for the other blocks. The complete saved Gram dataset supplies the all-Gram format requested by this leaf, so the paper's fallback does not create a truth obstruction.

I independently enumerated the normalized `Covered` choices and checked their passage bonds and degree bounds. The result is 106,101 consistent configurations, 184,914 outgoing-marked configurations, and precisely the 7,962 archived effective reflection classes, with no missing or extra key. Masks at X sites and covering tips are irrelevant to bonds. Isolated peripheral sites are absent from `reducedIntegrand`; an isolated retained arrival spin contributes the constant moment one. These facts account for the raw data omitted by an effective record.

The definitions and constructor agree on rational moments, tip/corner radii, groupwise inversion, unnormalized pair vectors, and the scale `15 D₀ q`. Site and token permutations account for the constructor's ring order versus the original `Fin 20` labels. A constructor tip token is labelled by its axial neighbour; the corresponding Lean group is labelled by the tip endpoint. Central blocks select weight zero for an even number of singles and positive weight one-half for an odd number, exactly as `centralWeight` does. In archive parity labels, an antisymmetric D pair has bit one; in Lean it is selected by `ε x = false`. Signs on singles and U pairs are immaterial, so the universal `ExchangeSigns` quantifier repeats existing blocks rather than requiring new ones.

Proof route, hard:

1. Normalize unused masks, prove exhaustive effective coverage and reflection transport, choose each archived representation/inversion, and prove its positive denominator clears the reconstructed coefficients.
2. Identify its explicit central bases and matrices with `indexedSectorMatrix`, then transport the saved triangular factors and check every `GramResidualRows` obligation.

There is no missing mathematical hypothesis. `Top.CertificateStatement` is a soundness implication and cannot alone supply this existence theorem. A writer still owes coverage, exact matrix reconstruction, basis identification and kernel checking of the finite arithmetic. The fresh residual check validates saved integer matrices; it does not establish their Lean identification. That identification was audited through the definitions and constructor, without producing a proof.

**2. `CoveredSlotEnumerationStatement`.** Exact statement: [NodesLeaf.lean:12](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesLeaf.lean:12). Paper: [l:leaf](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:89).

The table `externalSlot` has corner index pairs `(0,1), (2,3), (4,5), (6,7)` and tip triples `(8,9,10), (11,12,13), (14,15,16), (17,18,19)`. All extracted vectors retain their `UnitVector` property. Coveredness forces tips to U and nonremoved corners to U or D. The rational radius tests agree with `replacementRadius`. The reversed argument order in `coveredSiteField` and `localProduct` is harmless because `dot` is symmetric.

Proof route, easy:

1. Enumerate the eight peripheral coordinates and select the corresponding two or three entries of `m`.
2. Expand the finite product and simplify the status, radius and dot-product equalities.

**3. `CornerMeanBoundsStatement`.** Exact statement: [NodesLeaf.lean:24](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesLeaf.lean:24). Paper: [corner calculation](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:136).

Put `t = dot a b`. Unit vectors give `-1 ≤ t ≤ 1`. The U normalizer and unnormalized mean are `A = 1+t/3`, `V = (a+b)/3`; the D values are `A = 1+t/5`, `V = (a+b)/5`. Thus the normalizers are at least `2/3` and `4/5`. The exact differences are `A² - 4 normSq V = (1-t)²/9` and `A² - 9 normSq V = (1-t)(7-t)/25`. They give the required bounds for `localMean = V/A`. Antipodal inputs give zero mean with a positive denominator; coincident inputs attain the stated radii.

Proof route, medium:

1. Expand the normalizer and coordinate mean using `MonomialMoments` through degree three.
2. Use the unit-vector dot bound and the two factorizations, then divide by the positive `A²`.

**4. `NormalizedMeanFactorStatement`.** Exact statement: [NodesLeaf.lean:33](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesLeaf.lean:33). Paper: [l:leaf proof](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:122).

Take `A` to be the supplied positive normalizer and `u = ρ⁻¹ • localMean s a`. Finite linearity gives `A + dot V v`, where `V` is the unnormalized mean; its coordinates equal `A * localMean s a`. Positive `ρ` makes the norm scaling valid. Neither the fields nor the mean need to be nonzero, and the identity actually holds for every `v`. With `k=0`, the U/D normalizer is one and the mean is zero. Status X has normalizer zero and cannot meet the positive-normalizer hypothesis.

Proof route, easy:

1. Interchange finite coordinate and spin sums to express the integral as `A + dot V v`.
2. Scale the normalized mean by `ρ⁻¹` and cancel the two positive denominators.

**5. `PassageSiteMomentsStatement`.** Exact statement: [NodesPassage.lean:11](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPassage.lean:11). Paper: [passage moment calculation](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:57).

The monomial premise provides mass one, zero first and third moments, and second moments `δᵢⱼ/3` for U and `δᵢⱼ/5` for D. All needed monomials have degree at most three. Arbitrary real neighbour vectors, including zero, are permitted. No invariance of the finite atom law on arbitrary functions is required.

Proof route, medium:

1. Expand the three U factors and two D factors into coordinate monomials.
2. Apply the supplied moments and collect the surviving pairwise scalar products.

**6. `PassageFubiniStatement`.** Exact statement: [NodesPassage.lean:20](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPassage.lean:20). Paper: [passage factorization](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:42).

The passage belongs to `π.active`, has status U, and has no external slot. Its present bonds are precisely the nonremoved members of E,N,W. A nonremoved D neighbour keeps its passage bond, a U neighbour keeps all bonds, and the arrival bond is absent. `PassageNeighbours` explicitly makes the outgoing neighbour, `f`, and `g` those three distinct positions. For next, the passage law becomes D and only the outgoing bond is deleted. The remaining factors and laws are exactly those in `withoutPassageFunctional`. Removed `f` or `g` are assigned zero by `supportSpins`; their extra displayed factor is therefore one.

Proof route, medium:

1. Reindex spin assignments as a passage spin and an assignment on `π.active.erase (0,0)`, factoring out unaffected weights, bonds and slots.
2. Identify the passage factors from coveredness and apply the supplied U and D identities.

**7. `PassageNetworkPositiveStatement`.** Exact statement: [NodesPassage.lean:32](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPassage.lean:32). Paper: [l:Iw positivity](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:67), [l:finitefacts](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:126).

Order the finite erased active set and keep its non-passage bonds. Give every surviving corner its two original unit pins and every tip its three; the twenty original slots are accounted for by these lists or by the factor one at a removed corner. The degree-plus-pin counts are at most `1+3` at tips, `2+2` at corners, and `3+0` at axial neighbours. All active statuses are U/D and all edges have distinct endpoints. An order-preserving enumeration or reorientation supplies the required `e.1 < e.2`. The resulting partition equals the target sum. The generic positivity premise is consistent: the paper's twelve-letter greedy argument proves it, including the empty network.

Proof route, medium:

1. Enumerate erased sites, surviving edges and per-site slot indices to construct a valid `FiniteSpinNetwork`.
2. Reindex its partition sum and apply the supplied universal positivity assertion.

**8. `PassageNextLowerBoundStatement`.** Exact statement: [NodesPassage.lean:39](/home/ubuntu/aklt/repo/AKLT/Blueprint/H1/NodesPassage.lean:39). Paper: [l:Iw lower bound](/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:69).

Every support spin is zero or a unit icosahedron vector under the premise. Consequently every scalar product of two such spins is at least minus one, for arbitrary `f,g`, including equal or omitted sites. Thus `passageJ ≥ 4/5`. Spin weights are nonnegative, as are all bond and unit-slot factors. Multiplying by this common nonnegative weight and summing proves the claimed comparison. Neither `PassageNeighbours` nor strict positivity of the partition is needed here; the existing coveredness premise is also stronger than necessary.

Proof route, easy:

1. Bound every support spin by one and obtain the pointwise bound on `passageJ` by coordinate Cauchy–Schwarz.
2. Establish nonnegativity of every remaining weight/factor and sum the weighted inequalities.

**Definitions and Lean traps checked.** The dependency audit followed `PatternData`, `Covered`, `statusAt`, `keptAt`, `bonds`, `active`, `spins`, both pattern functionals, template geometry and the twenty-slot table; `supportSpins`, `withoutPassageFunctional`, and `coveredSiteField`; `Vec3`, `dot`, `normSq`, `UnitVector`, both finite spin laws and all icosahedron constants; `localProduct`, `localMean`, `MonomialMoments` and rational moments; and `FiniteSpinNetwork.Valid`, its weight and partition. For the certificate it also followed both representations, degrees and leaf neighbours, spin sites and groups, vector tokens and radii, `reducedIntegrand`, `contractSpins`, both reduced polynomials, inversion, rational Pauli entries, exchange/group/central bases and weights, basis vectors, denominator clearing, integer/threshold/indexed sector matrices, and the full integer Gram residual predicate.

- All eight declarations elaborate as closed `Prop`s. There are no silently dropped hypothesis instances or extra free parameters. `CentralBasis` has a noncomputable finite enumeration; the existential explicit `Fin t ≃ CentralBasis` makes the certificate's ordering part of its data.
- `Vec3 = Fin 3 → ℝ` has a default function-space norm that should not be confused with the Euclidean quantity `normSq = dot v v`. Use coordinate Cauchy–Schwarz or an explicit Euclidean-space identification.
- `coveredSiteField` multiplies over all `Fin 20` indices, using one at unrelated sites. `localProduct` multiplies over `Fin 2` or `Fin 3`; proving their equality requires reindexing or finite expansion, not identifying their index types.
- `replacementRadius` and the first leaf's radius equalities are in ℚ. The mean bounds and `ρ` are in ℝ. Cast the rational conditional and divisions explicitly. The certificate numerators and denominators are naturals, but matrix subtraction and Gram arithmetic are in ℤ; no truncated natural subtraction or natural division occurs.
- Positivity of `A` and `ρ` is explicitly supplied before division. The integer matrix definition uses a rational floor: prove denominator clearing and exact integrality before replacing that floor by an integer entry. Saved matrix arrays cannot bypass that obligation.
- Finite sums over subtype/function spaces may need `classical`, as do basis enumeration and some function equalities. The sums are finite `Fintype` sums, not integrals over an asserted invariant atom measure.
- `SpinLetter` contains the zero atom. It has zero U weight and positive D weight. Its norm is zero and it causes no failure in the lower bound. Omitted sites also receive zero, without introducing a site law or an extra variable.
- The hypotheses are nonvacuous. For example, use outgoing north, passage U keeping E/N/W, arrival X, all other sites U with every non-tip U except the passage keeping all four directions. This is covered and supplies unit slots. The exact moment diagnostic also confirms that the supplied moment and unit-vector premises are consistent.

**Validation artifacts.** [verdicts.jsonl](verdicts.jsonl) contains one object per fully qualified leaf with reason, fix, two-line route and difficulty. [audit_geometry.py](audit_geometry.py) and [geometry-check.json](geometry-check.json) record the independent coverage, passage-bond and factor-count diagnostic. [audit_moments.py](audit_moments.py) and [moments-check.json](moments-check.json) check all 35 monomials of degree at most four for U and D, exactly in `ℚ(φ)` with `φ²=φ+1`, and the twelve unit vectors. [witness-verification.json](witness-verification.json) and [its log](witness-verification.log) record a fresh run of the saved-data exact integer verifier. [Inspect.lean](Inspect.lean) only imports and prints declarations; [lean-inspection.log](lean-inspection.log) records its successful single-module run with Lean 4.35.0-rc2. One Lean process was used, with the repository packages linked into this directory. No full build, theorem proof, sub-agent or repository mutation was performed.
