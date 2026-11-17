# Mathematical correspondence

This note identifies the exact mathematical surface. Source line references are
relative to `/home/ubuntu/aklt/manuscript-v2` as read on 2026-11-17; the source
hashes are recorded with the architecture report. The selected theorem is
`AKLTPalomar.aklt_gap : Main`.

The selected release theorem is now `AKLTPalomar.aklt_gap : Main`.
It has no premises. `Solution.main_iff` identifies its Main with the original
`AKLT.Challenge.MainStatementV2`, and `CertData.Close.main` supplies its proof.
Generated H1 and H3 certificate sources are part of this proof closure and must
be rebuilt against the ported kernels. This phase verifies the hand-written
sources and the retained two-input regression; it does not claim that the
pending unconditional package build has completed.

The sections on H1 and H3 below describe internal mathematical inputs and the
historical two-input regression, not assumptions of the root Challenge theorem.
Challenge itself inlines only the physical model and Main. The physical model,
Hamiltonian, and VBS product are `d:model` in `sec1-result.tex`; polynomial
normalization is `d:poly` in `sec3-quantum-frames.tex`. `ClosedTrail` describes a
first-hit path, as its defining doc comment states; its identifier is preserved.

## H1: the pointwise covered-pattern inequality

The defining statement is `sec6-walks.tex:531–541`, label `h:H1`. Its fixed
thresholds are also the conclusion `sec8-inputs.tex:158–168`, label `t:H1`;
`sec8-inputs.tex:280–283`, label `t:inputs`, supplies their certificate route.
The pattern class is `sec6-walks.tex:488–519`, label `d:pattern`, and its finite
site laws are `sec2-moments.tex:8–29`, label `d:moment`.

| Paper clause | Lean clause and correspondence |
| --- | --- |
| The plane is the integer square lattice with ambient taxicab distance. | `Plane := ℤ × ℤ` and `latticeDist` are exactly that distance. `templateSites` filters the radius-two square by distance ≤ 2, giving the same thirteen sites. |
| Passage at 0, arrival south, outgoing east/north/west. | `PatternData.outgoing : Compass` and `Covered` exclude `.south`. The central status is U and its kept set is precisely east, north, west. |
| Arrival is removed, or D with two non-passage bonds. | The arrival disjunction in `Covered` requires X, or D with a two-element kept set excluding 0. A kept set is a set of compass directions, hence contains only the four incident half-bonds. |
| Other neighbors may be U, X, or D; D keeps the passage bond and one other; outgoing is present. | The neighbor disjunction requires exactly those statuses and D conditions; `statusAt outgoing.step ≠ .X` and the central kept set make the out-bond present. |
| Corners are U, X, or D with two of four bonds; noncentral, nontip U sites keep all four. | The corner cardinality clause and the U-neighborhood clause impose precisely these restrictions. |
| Nonremoved nontip ends agree on keeping an internal bond. | The last clause of `Covered` imposes the mutual-keep equivalence on adjacent nonremoved nontips. |
| Tips are U covering sites; no global tip kept-set constraint is used. | Tips have status U. `PatternData.bonds` ignores the kept set at a tip, testing the other endpoint instead. Arbitrary tip kept sets are redundant data and do not change either polynomial. |
| Twenty independent unit slots: two per corner, three per tip; all survive at a nonremoved site even when a corresponding actual external half-bond is absent. | `externalSlot : Fin 20 → Plane × Compass` lists these twenty slots. `m : Fin 20 → UnitVector` chooses each separately. `patternFunctional` includes each slot exactly once unless its site is X; it never filters slots by `kept`. Pins sharing an outside endpoint remain independent. |
| U is the uniform twelve-vertex icosahedron law; D is 3/5 U + 2/5 at zero. | `icoVector` uses the same golden ratio, radius, three coordinate groups, and two signs. `SpinLetter = Option IcoLetter` adds the zero atom. `spinWeight` assigns 1/12 at each U vertex, 1/20 at each D vertex, and 2/5 at D's zero atom. U's extra zero label has weight zero. |
| Current polynomial uses all present template bonds and status laws; next changes only the central law to D and removes its out-bond. | `patternFunctional π false/true` performs exactly these two operations. `patternCurrent` and `patternNext` insert the constant observable 1. Internal bonds are counted once in the positive orientations. Removed sites contribute no variable or slot. |
| For every covered pattern and all twenty unit pins, current ≥ the type threshold times next. | `LocalPatternBound` universally quantifies over `π`, its `Covered` proof, and `m`. The conditional is straight precisely when `outgoing = .north`; the constants are the exact real rationals 961/1000 and 187/200. The inequality is cross-multiplied, so it assumes no denominator or minimizer. |
| Both thresholds belong to (0,1]. | The first four conjuncts of `LocalPatternBound` say `0 < cs ∧ cs ≤ 1 ∧ 0 < ct ∧ ct ≤ 1`. At the specified rationals these are elementary truths, so they add no mathematical assumption beyond the paper's fixed H1. |

Thus `H1` is the paper's H1 at its fixed thresholds. Redundant tip and removed-site kept data and
zero-weight atoms change the indexing presentation, not the quantified
polynomials. No optimality, minimizing pins, operator certificate, enumeration
coverage, or finite-data provenance condition is added to this premise.

## H3: every finite cutoff of the specified positive-vector kernel

The premise is `sec7-recursion.tex:598–612`, label `h:H3`, specifically the
finite-cutoff inequality at lines 602–607. Its kernel is defined at lines
520–556 (`d:kernel`); its vector, contraction ceiling and orderings are at lines
575–591 (`d:kernel-order`). `sec8-inputs.tex:289–295`, label `t:inputs`, supplies
the finite stationary/prefix route. The coefficient table is
`sec7-recursion.tex:263–303`, label `l:log-mean-bounds`.

| Paper clause | Lean clause and correspondence |
| --- | --- |
| X is B or C; center 0, start (−1,0), target (1,0) for B or (0,1) for C; incoming is start minus center. | `PairType`, `kernelCenter`, `kernelStart`, `kernelTarget` and `kernelIncoming = .west` give exactly these data. |
| Length-n plane trails avoid the center, repeat no unoriented bond, and stop at their first target hit. | `DirectionWord n` gives every compass word. `IsTrail` makes `wordBond` injective and forbids the initial reversal. `ClosedTrail` requires the final vertex to be the target, excludes it at every earlier index, and avoids the center at all indices 0,…,n. There is no torus or finite spatial boundary. |
| A revisit means an earlier departure from the same lattice site. | `departureCount` counts precisely the indices before the current index. `wordRevisit` tests whether this count is positive. Neither an arrival alone nor finite-memory equality is substituted. |
| Dead neighbors are the center or sites with at least two earlier departures. | `deadAt` is exactly this predicate. `responseNeighbors` removes the actual arrival neighbor; `liveOtherNeighbors` also removes the outgoing neighbor and all dead ones. On a first-hit trail the outgoing neighbor is live, as proved by the lattice argument at paper lines 563–573; it is included unconditionally in `responsePairs`. |
| With two live other neighbors: a to their mutual pair and b to each outgoing pair; with one: b′ to its outgoing pair; with none: no reward. | `responsePairs` takes all two-element subsets of outgoing plus live others. `pairCoefficient` tests membership of outgoing and whether exactly one other neighbor is live. This gives exactly the three cases. |
| Exact straight/turn coefficients a, b, b′. | `alphaBound = (145217,150000)/10^6`, `betaBound = (352782,357549)/10^6`, and `betaPrimeBound = (340008,344661)/10^6`, in straight/turn order. `passageFactor` is the reciprocal of the corresponding H1 threshold. |
| Pair type B is collinear; C is diagonal. | For a two-element response pair of neighbors of the same site, `responsePairType` tests whether the two sites share a coordinate. This is exactly the collinear/diagonal distinction. |
| κ_h(i) is the sum of pair coefficients weighted by h of their type. | `witnessKappa` is that finite sum. At θ = 1, all shift factors are 1, so aggregation over shifts disappears; no shift cutoff is assumed or lost. The separate shifted-series definitions are therefore unnecessary in the Challenge. |
| h = (1,5404319552844595/4503599627370496), ρ₀ = 993015/10^6. | `kernelWitness` and `kernelRho` use these exact rational numbers. In particular h_C is the prescribed dyadic, not 6/5 or a decimal approximation. |
| For n ≤ 12, first-departure indices are ordered by (x−1)/(x κ_h), zero reward at +∞, ties by path index. | `firstVisitList` filters increasing `Fin n` indices by not-revisit. `shortOrderLE` implements exactly the finite-key comparison, both zero cases and tie-breaking. `kernelOrdering` uses `mergeSort` with it at n ≤ 12. |
| For n > 12, straight first departures, then turning first departures, each in path order. | The long branch concatenates the two filters of the same increasing first-visit list. The ordering does not depend on θ. |
| Each reward receives every x up to and including its position. | `exposureSum` recurses as `x_i * (reward i + rest)`. Expanding the recursion gives exactly the displayed prefix products, including the current x. |
| Base factor is 3^(−n)(3/5)^rev. | `trailBaseWeight` multiplies 1/3 at first departures and 1/5 at revisits, which is the same rational factor. `closedContribution` multiplies it by the ordered exposure sum. |
| For both row types and every integer cutoff R₀ ≥ 0, the length-1-through-R₀ sum is at most ρ₀ h_X. | `PositiveVectorBound` is `∀ X, ∀ R : ℕ, kernelPartialRow X R ≤ kernelRho * kernelWitness X`. `kernelPartialRow` sums `Finset.Icc 1 R` and all direction words, assigning zero to nontrails. Naturals parameterize exactly the paper's nonnegative integer cutoffs, including the empty cutoff 0. |

This is the displayed finite-cutoff formulation of H3 itself, not just a finite
prefix bound, Bellman supersolution, quotient identity, or an assertion at one
cutoff. The equivalence with `M₁h ≤ ρ₀h` uses nonnegativity and increasing
cutoffs as explained at paper lines 614–620. No additional finite archive
conjunct appears in the package theorem.

## Main: the all-parity physical headline

The headline is `sec1-result.tex:39–45`, label `t:main`. The physical model and
edge-counting conventions are `sec1-result.tex:16–37`, label `d:model`.
Polynomial normalization is `sec3-quantum-frames.tex:14–23`, label `d:poly`, with
the tensor identification at lines 74–76.

| Paper clause | Lean clause and correspondence |
| --- | --- |
| Integer periods L,N ≥ 3. | `Size := {n : ℕ // 3 ≤ n}` parameterizes exactly these periods. Positive integers ≥ 3 and naturals ≥ 3 give the same domain. No evenness assumption occurs in `MainStatementV2`. |
| The torus is ℤ/Lℤ × ℤ/Nℤ with each simple unoriented nearest-neighbor edge counted once. | `Site` is the product of the two `ZMod`s. `Bond = Site × Fin 2` chooses the positive horizontal and vertical orientations. For periods ≥ 3 this is a bijective indexing of the paper's unordered edges, including period 3; the separate torus-kernel proof supplies the no-loop and distinctness facts. |
| Each site is the spin-2 space V₄ with the specified inner product. | `Hilbert` is the Euclidean tensor-coordinate space indexed by configurations in `Fin 5`. Its basis is `sqrt (choose 4 k) z₁^(4−k)z₂^k`, so its standard Hermitian inner product is exactly the paper's polynomial normalization. `spinZ`, `spinPlus`, `spinMinus` are its usual spin-2 matrices. |
| P_e is the orthogonal projection onto total spin 4; H is their sum with coefficient one. | `bondCasimir` is the square of total bond spin, `spin4Space` its eigenspace at 4(4+1)=20, and `P` its orthogonal projection. `H` sums it over `Bond` once each. `AKLT/Challenge/Sanity.lean` proves `p_positive`, `h_positive`, `h_selfAdjoint` and `h_eigenvaluesReal`; these are facts about this concrete model, not premises of `Main`. |
| B is the unnormalized product of oriented singlets. | `singlet` is precisely z_x,1 z_y,2 − z_x,2 z_y,1. `vbsPolynomial` multiplies these over all bonds. `B` divides its monomial coefficients by the product of square roots of binomial coefficients to express the same polynomial in the orthonormal basis; it introduces no global normalization. |
| For every L,N ≥ 3, B ≠ 0 and ker H = ℂB. | The first conjunct of `MainStatementV2` says both for every `L N : Size`, with `Submodule.span ℂ {B L N}` expressing ℂB. These clauses have no eventual-size restriction. |
| There are c > 0 and one L₀ ≥ 3 such that all sufficiently large L,N have every nonzero eigenvalue at least c. | The second conjunct chooses `c`, then `L₀`, before quantifying over L and N. Its hypotheses are only the two size bounds, `μ ≠ 0`, and `(H L N).HasEigenvalue (μ : ℂ)`; its conclusion is `c ≤ μ`. Since H is self-adjoint and nonnegative, quantifying real nonzero eigenvalues is the paper's spectral-gap formulation. No parity condition or size-dependent gap constant is introduced. |

The concrete model agrees clause by clause with the paper. The current advertised
statement is the same unconditional theorem, with no extra antecedents. Its proof
source closes the finite certificate contracts through `CertData.Close.main`.
The pending regenerated certificate build is an explicit verification boundary.

## Interface identity and verification boundary

Challenge and Solution are separate environments and intentionally declare the
same fully qualified mathematical names. Challenge contains the independent,
Mathlib-only physical definitions and Main. Solution imports the complete tree,
proves `main_iff` by `Iff.rfl`, and applies `CertData.Close.main`. It never imports
Challenge or its placeholder. Comparator must compare every recursively
reachable statement definition; `comparator.json` has no definition exemption.
The unconditional comparison will run after regenerated certificates make that
Solution available.

Challenge resets Lean's auxiliary-proof cache at the original source boundaries
and uses `backward.proofsInPublic` to preserve helper names. These affect naming
and visibility, not theorem statements, proof rules, or kernel checks.

The retained two-input regression has its own independent Challenge template
and `Regression.Solution`. Its `h1_iff`, `h3_iff`, and `main_iff` remain `Iff.rfl`.
That template retains the original `moment` and `trailWeight` definitions because
they own shared numeral-proof helpers used by `spinWeight` and `trailBaseWeight`.
The modern Compass matcher agrees between its two environments. These analytic
definitions are unnecessary in the new physical-only root Challenge. The
conditional export's protected Lean/NanoDa/con-ron receipts apply to that
regression, not to the pending unconditional export. The ordinary reduction
remains available as `AKLT.Final.main_of_inputs`.

## Module-system port note

The standalone hand-written port preserves every mathematical assertion and definition/proof body up to the consistent
American English identifier substitution. It preserves numeric/string data. It makes public/exposed interfaces explicit and retains the
explicit exposure of `AKLT.Challenge.size_neZero`. Literal elaborators are meta,
and the H3 sorting proof module imports the standard sorting implementation with
`import all` so its unchanged proofs can unfold the required bodies. The source
fidelity receipt checks all 1,104 imported hand-written files. See
PORT-CHANGES.md, REGEN-INTERFACE.md, and the scoped verification records.

## Identifier spelling update

The independent Challenge, regression template, and proof development use the
same current American English names. The alias identifications still use
Iff.rfl. Declaration, binder, field, module, and import spellings change together;
no mathematical premise, numeric input, or semantic definition changes. Paper
citation labels and external dependency names are preserved. Verification after
the fresh rebuild is recorded separately under verification/rename/.
