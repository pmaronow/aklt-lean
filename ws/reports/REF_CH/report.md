VERDICT: FAITHFUL WITH REMARKS

**Fatal:** None found.

**Major:** None found. The conclusion and both fixed premises have the paper's mathematical meaning. The differences in coordinates, indexing and redundant raw data do not strengthen or weaken them.

**Minor M1 — stale paper references in comments.** Lean lines 429, 443–468 and 501–527 refer to `(e:H)`, `(e:Vinner)`, `(e:B)` and `§s:poly`, and put the polynomial normalization in §2. Those labels do not exist in this manuscript version. The model, Hamiltonian and VBS product are in [sec1-result.tex:18](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:18), `d:model`, lines 18–39; polynomial normalization is in [sec3-quantum-frames.tex:14](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex:14), `d:poly`, lines 14–35 and 74–76. This affects navigation, not the definitions. **Fix:** update these comments to the current files/labels and §3. The comments at Lean lines 504, 507, 514, 519 and 525 particularly need this correction.

**Minor M2 — `ClosedTrail` is a misleading name for a first-hit path.** [Lean lines 221–225](/home/ubuntu/aklt/repo/palomar/Challenge.lean:221) describe a path from `(-1,0)` to `(1,0)` or `(0,1)`, not a path returning to its start. This agrees with `d:kernel`, [sec7-recursion.tex:520](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:520), lines 520–525. Its accompanying comment correctly describes the stopping rule. **Fix:** optionally rename it `FirstHitTrail`, or explain that “closed” refers to reaching the pair target. No predicate change is needed.

**Scope and reading convention.** This review concerns the mathematics of [Challenge.lean](/home/ubuntu/aklt/repo/palomar/Challenge.lean), not the placeholder proof at lines 569–570 or the correctness of external certificates. Source line numbers are for the files read on 2026-11-17. I compared definitions directly with the manuscript; the package's `FIDELITY.md` is not used as evidence of mathematical equivalence.

The paper's `t:main` is unconditional. The requested statement is its conditional reduction, `H1 → H3 → Main`, and that is exactly the implication at Lean line 569. The paper uses three computational inputs: H1, H2 and H3_h. H2 at these fixed thresholds is independently supplied by `sec8-inputs.tex:288–325` (`t:inputs`), with `C_V = 10` and `q = 1119948287353/1120437614225`; its finite test and all-length consequence are in `app-input-contracts.tex:200–314` (`p:H2-test`, `l:H2-CV`). Consequently H2 can be discharged in deriving the requested two-premise implication. Its absence as an explicit antecedent is not a missing mathematical hypothesis here. Challenge itself contains neither that derivation nor a proof of the unconditional headline, as expected under the placeholder convention.

**The conclusion is equivalent to `t:main`.**

`Size := {n : ℕ // 3 ≤ n}` (line 424) parameterizes precisely the paper's integers at least three. `Site` is exactly `ℤ/Lℤ × ℤ/Nℤ`. Positive horizontal and vertical bonds give one orientation of each simple unoriented nearest-neighbour edge. For periods at least three, no bond is a loop, the two directions at a site are different, and opposite descriptions cannot duplicate an unordered bond: such a duplication in one coordinate would require the period to divide two. At period three, the three positive edges around that coordinate form the three distinct edges of its triangle. Thus there are exactly `2LN` bonds, each counted once, also when one or both periods equal three. This matches `d:model` (`sec1-result.tex:18–39`) and the small-period discussion in `sec3-quantum-frames.tex:137–205`.

The Hilbert space is the tensor product in orthonormal coordinates. The identification with the paper's polynomial space sends a coordinate vector `ψ` to

\[
 \sum_\sigma \psi_\sigma\prod_x
 \sqrt{\binom4{\sigma_x}}\,
 z_{x,1}^{4-\sigma_x}z_{x,2}^{\sigma_x}.
\]

This is unitary because `d:poly` gives the unscaled monomial squared norm `binom(4,k)⁻¹`. `EuclideanSpace ℂ (Configuration L N)` therefore has exactly the requisite complex inner product, conjugate linear in its first argument. The single-site matrices implement spin two in these coordinates: `spinZ` has diagonal `2,1,0,-1,-2`, `spinPlus e_k = √(k(5-k)) e_(k-1)`, and `spinMinus` is its adjoint. Their Casimir is `6I`. The total bond Casimir has eigenvalues `j(j+1)`, `j = 0,…,4`, with multiplicities `1,3,5,7,9`; its eigenvalue-20 eigenspace is precisely total spin four. Any conventional choice of signs for the infinitesimal generators of the polynomial action leaves this Casimir and its subspaces unchanged. `P` is the orthogonal projection onto that space, including the spectator tensor factors. Thus `H` is the paper's Hamiltonian with coefficient one per bond, without a normalization by sites, bonds, or degree.

`singlet` and `vbsPolynomial` are exactly the oriented determinants and their product. The positive-coordinate orientation is one of the orientations allowed by `d:model`; changing it changes only the overall sign of the VBS vector. `B` divides monomial coefficients by the product of square roots of binomial coefficients. This is the coordinate change displayed above, not a normalization of the VBS polynomial. In particular the represented polynomial is exactly the paper's unnormalized product.

At lines 547–548, nonvanishing and `ker H = span ℂ {B}` are asserted for **every** pair of periods at least three. Neither assertion is limited by the eventual gap threshold. At lines 549–551, one positive real `c` and one natural `L₀ ≥ 3` are chosen before `L,N`; both periods must be at least that same threshold, including equality. All aspect ratios and all parities are permitted. The order `∃ c, ∃ L₀, ∀ L,N, ∀ μ` is the paper's order. The paper requires no particular numerical value of `c` or `L₀`, so the existential formulation loses no constant.

Restricting `μ` to real numbers loses no eigenvalues: `H` is a finite sum of orthogonal projections, hence self-adjoint and positive semidefinite. Mathlib's `HasEigenvalue` means that the eigenspace contains a nonzero vector, not merely that zero solves an eigenvector equation. Every nonzero eigenvalue of this `H` is therefore positive and real. The condition `μ ≠ 0` followed by `c ≤ μ` is equivalent to the paper's smallest-positive-eigenvalue bound. It does not ignore possible nonreal spectrum, since this operator has none.

There is also no empty-spectrum loophole. The configuration with every site in `e_0` lies in the spin-four space on every bond. It is an eigenvector of `H` with eigenvalue `2LN > 0`. For any proposed `L₀`, periods satisfying the size conditions exist. The uniform-gap quantifiers consequently range over nonempty sets of tori with nonzero eigenvalues.

**H1 is equivalent to the paper's fixed H1, neither stronger nor weaker.**

The template is exactly the thirteen-site taxicab diamond, with passage at zero, arrival south, four corners and four tips. I checked all twenty entries of `externalSlot`: they are precisely the external half-bonds of that diamond, without omission or repetition, with two at each corner and three at each tip. Each pin is independently an element of the full real unit sphere; slots with a common outside endpoint are not identified. `Vec3` is a function type, but the sphere and all scalar products use the explicitly defined Euclidean `dot` and `normSq`, not a function-space norm.

`Covered` imposes all the non-tip rules of `d:pattern` (`sec6-walks.tex:488–519`): the passage U site keeps E,N,W; the arrival is X or D keeping two non-passage directions; E,N,W neighbours have the specified U/X/D options, with every nonremoved D neighbour retaining the passage bond; the outgoing neighbour is nonremoved; corners have the stated options; every other non-tip U site keeps all four directions; adjacent nonremoved non-tip endpoints agree on their keep decision. A kept set contains only compass directions, so cardinality two really means two of the four incident bonds.

All tips are U. Their bond is controlled exclusively by the non-tip endpoint in `PatternData.bonds`, exactly as the covering-tip exception requires. Lean leaves tip kept sets, and the kept sets at X sites, arbitrary. These are redundant raw fields: they affect neither the consistency test on nonremoved non-tips nor either partition polynomial. Erasing them maps every covered Lean datum to the paper's pattern data; every paper pattern has a Lean representative, for example with full tip kept sets and empty X kept sets. All representatives give identical current/next values. Universal quantification over these duplicates does not strengthen the premise. The raw type is not meant to be the list of 7962 reduced reflection-class records used by the certificates.

The icosahedral coordinates, both independent signs and radius `√(φ+2)` are exactly those in `d:moment` (`sec2-moments.tex:8–29`). They give twelve distinct unit atoms. `SpinLetter` adds one zero label to a common alphabet. Its weight is zero at a U site, so summing over that extra label leaves the U functional unchanged. At D sites the twelve unit atoms each have weight `1/20 = (3/5)/12`, and zero has weight `2/5`. Both laws have total mass one. X sites are omitted from the product type, not assigned a zero-total-mass site law.

`patternFunctional` includes each present internal unoriented bond once and every external slot at every nonremoved corner/tip, even if the corresponding external direction is not kept. It creates no slots at a removed site or newly exposed leg. Its `next` switch changes precisely the passage law to D and replaces the out-bond factor by one; all other laws, bonds and slot factors persist. Hence `patternCurrent` and `patternNext` are exactly the **unreduced** polynomials in `d:pattern`. A tip's effective field radius `3/5` is obtained by integrating its three unit slots, as in `sec2-moments.tex:197–294` (`l:35`); the original pin domain correctly remains twenty unit vectors. No extra restriction to finitely many pin directions or a preselected inversion is present.

`LocalPatternBound` quantifies over every covered raw pattern and then every twenty-pin assignment, with straight exactly when the outgoing direction is north. Its four scalar side conditions express `cs,ct ∈ (0,1]`. At `H1`'s fixed real rationals `961/1000` and `187/200` they are true, so add no premise beyond `h:H1` (`sec6-walks.tex:531–541`) or `t:H1` (`sec8-inputs.tex:167–177`). It asserts a pointwise cross-multiplied inequality, with no minimizer, optimality, normalized ratio, or numerical certificate substituted for it.

The quantification is nonvacuous. For instance, take passage, E and N to be U; arrival, W and all corners X; tips U; choose an E out-bond and full kept sets at the two non-tip U neighbours. This is covered. Giving the E tip three identical pins `a` and the N tip three pins `-a`, for any unit `a`, gives effective tip means `±3a/5` and neighbour means `±a/5`. Passage integration yields

\[
 Z_{\rm cur}/Z_{\rm next}
 =1+\tfrac13(a/5)\cdot(-a/5)=74/75.
\]

The other tip normalizers are common positive factors. Thus equality of the two partition functions or positivity alone does not make H1 automatic. Both sums are strictly positive: a corner has at most two internal factors plus two slots, a tip one plus three, a neighbour at most four, and the passage three before/two after. The positivity argument of `l:finitefacts` (`sec2-moments.tex:126–157`) applies. There is no zero partition function making the inequality vacuous.

**H3 is equivalent to the paper's H3_h, neither stronger nor weaker.**

`PairType` has exactly B (collinear) and C (diagonal). The centre, start, targets and incoming direction are exactly `d:kernel`'s: `c=0`, `u=(-1,0)`, `v_B=(1,0)`, `v_C=(0,1)`, incoming west `=u-c`. A direction word encodes each nearest-neighbour path once. `IsTrail` requires injectivity of the two-endpoint **unoriented** bond sets, allows vertex revisits, and forbids the initial reversal. The virtual incoming bond is not put into its used-bond set. Later immediate reversal is excluded by bond injectivity. `ClosedTrail` additionally avoids the centre at every index from zero through the endpoint and excludes the target at every index before the endpoint. These are exactly the paper's first-hit trails; no self-avoiding-path condition, spatial torus, finite box, or memory approximation replaces them.

The departure count runs over preceding departure indices only. Thus “first visit” here means first departure, and a terminal arrival produces no additional reward. A neighbour is dead precisely if it is the centre or has at least two prior departures. The incoming neighbour is `current - incoming.step`, including the virtual arrival at the start. Removing that neighbour, then the outgoing neighbour, and filtering dead sites leaves exactly the paper's live `f,g`. On a valid first-hit trail the outgoing neighbour cannot be dead, by the argument in `sec7-recursion.tex:563–573`; including it unconditionally in `responsePairs` is therefore sound. Invalid words are removed by the `ClosedTrail` filter before their contributions enter a row.

If both other neighbours are live, the three two-element subsets give `a_τ` on `{f,g}` and `b_τ` on the two outgoing pairs. If one is live, exactly its outgoing pair remains and receives `b′_τ`; if neither is live, the pair set is empty. `responsePairType`'s coordinate-sharing test is exactly collinear versus diagonal for two distinct neighbours of one lattice site. Its vacuous result on empty sets is never used for a response pair.

Every adopted constant agrees with `l:log-mean-bounds` (`sec7-recursion.tex:283–296`) and `d:kernel-order` (lines 575–591):

| Constant | Straight | Turning |
| --- | --- | --- |
| `c_τ` | `961/1000` | `187/200` |
| `x_τ` | `1000/961` | `200/187` |
| `a_τ` | `145217/10^6` | `150000/10^6` |
| `b_τ` | `352782/10^6` | `357549/10^6` |
| `b′_τ` | `340008/10^6` | `344661/10^6` |

Also `h_B=1`, `h_C=5404319552844595/4503599627370496`, `ρ₀=993015/10^6`, and the ordering cutoff is 12. In particular `h_C = 6/5 - 1/22517998136852480`, so Lean uses the paper's exact dyadic, not the nearby rational `6/5`.

`witnessKappa` is precisely `κ_h(i)`, summing coefficients times the witness of the response-pair type. For length at most twelve, `shortOrderLE` compares the exact rational keys `(x_i-1)/(x_i κ_h(i))`, puts zero rewards at infinity, and breaks all ties by path index. Its two zero branches implement both finite-versus-infinite comparisons and infinite-versus-infinite ties correctly. For longer words, the two filters preserve path order within straight and then turning first departures. The order does not depend on any shift parameter.

Unfolding `exposureSum` for an ordered list `i₁,…,i_m` gives

\[
 \sum_{k=1}^m \kappa_h(i_k)\prod_{\ell\le k}x_{i_\ell}.
\]

The reward's own `x` is included. Multiplying `1/3` at first departures and `1/5` at revisits gives exactly `3^{-n}(3/5)^rev`, not a second copy of the passage factors. Hence `closedContribution` is the summand displayed in `h:H3`. `trailWeight` is the separate full open-trail majorant; it is not mistakenly multiplied into this expression a second time.

`kernelPartialRow X R` sums lengths `1,…,R` and all valid words of each length. `PositiveVectorBound` then quantifies over **both** types and **every** natural cutoff R, with the prescribed fixed witness and ceiling. This is the paper's displayed finite-cutoff definition (`sec7-recursion.tex:598–620`) verbatim in rational coordinates. It is not limited to lengths twelve, certificate radius seventy, or any other tested prefix. The shift-resolved coefficients `M_{XY,s}` need not be separately represented here: at `θ=1`, weighting and summing over all `(Y,s)` is exactly summing each pair's coefficient times `h_Y`, as `witnessKappa` does. No shift is omitted or bounded. Nonnegativity and finiteness at each length identify the supremum of these cutoffs with the full nonnegative series, without relying on a real infinite-sum convention that could assign zero to a divergent series.

The trail classes are nonempty. Row C already contains `(-1,0),(-1,1),(0,1)` at length two, and row B contains the path over the top of the centre at length four. For the C path, put `x=200/187` and `k=(a_t+b_t)h_C+b_t`. Its exact contribution is `kx(1+x)/9`; it is the only length-two C path, and gives

\[
 \texttt{kernelPartialRow C 2}
 =\frac{187188224699416837344237}{787431876847594373120000}
 \approx0.2377198971>0.
\]

Thus the row quantifiers do not disappear through empty types or impossible trails. The all-cutoff upper bound remains a substantive assertion. No extra inconsistency or triviality is introduced relative to the paper's input; verifying all cutoffs via its certificates is outside this statement comparison.

**Arithmetic and degenerate-case audit.**

- **Small/empty tori:** `Size` excludes 0, 1 and 2. Thus `ZMod 0`'s infinite interpretation never occurs, no site or bond type is empty, and the four incident edges remain distinct at period three. The `size_neZero` instance proves only this existing size fact.
- **Other quantified types:** `UnitVector` contains `(1,0,0)`, `Compass` has four elements and `PairType` two. Covered patterns and both first-hit trail classes have the explicit examples above. None of these universal quantifiers is over an empty type or an impossible admissibility condition.
- **Natural subtraction:** `wordIncoming` uses `i.val-1` only in the branch `i.val ≠ 0`. In `spinPlus`, `5-j.val` has `j.val ≤ 4`. In `monomialDegree`, `4-σ_x.val` has `σ_x.val ≤ 4`. None truncates an intended negative value. In contrast, `spinZ` casts the index to ℂ before subtracting, so its negative magnetic labels are retained. Plane coordinate subtraction is in ℤ; `latticeDist` applies `natAbs` afterwards.
- **Division and coercions:** all thresholds, weights and ordering expressions have explicit ℝ or ℚ result types. Their divisions are field divisions, not ℕ division. The ℚ-to-ℝ embedding preserves these finite sums, products and inequalities. The norm radius is positive. The five binomial values used by `B` are `1,4,6,4,1`, so every square root and their finite product are nonzero. Both local thresholds and all nonzero ordering denominators are positive. At `κ_h=0`, the score's field division by zero is avoided by the explicit infinity comparison. The ℝ-to-ℂ eigenvalue coercion is injective.
- **Empty products/sums:** a zero-length direction word has one empty assignment and base weight one. It is not a closed first-hit trail, because the start differs from both targets, and kernel lengths begin at one anyway. `Finset.Icc 1 0` is empty, so cutoff zero gives the intended `0 ≤ ρ₀h_X`. An empty response-pair set has reward zero; an empty exposure list has sum zero. The latter yields zero contribution, not a spurious mass. Empty-site product assignments follow the paper's one-empty-configuration convention.
- **Total helper definitions:** `wordVertex` is constant after index n, and `departureCount` clamps its prefix to n. Relevant path indices never exceed n. `square` also permits radius zero, a harmless extension of `d:shells`' positive-radius convention; the template uses radius two. `responsePairType`, `pairCoefficient` and the raw pattern functionals accept more arguments than their documented mathematical domains, but the premises use them only on the covered patterns and valid two-element trail response pairs described above.

**Checks performed.** The unmodified Challenge elaborated with Lean `4.35.0-rc2` and the existing Mathlib dependency cache; exit code 0, with only the expected `sorry` warning at line 569. No build artifacts were emitted. Independent exact arithmetic checked the 25-dimensional bond Casimir eigenvalue multiplicities `1,3,5,7,9`, law masses, binomial denominators, dyadic difference and the C length-two contribution. Direct enumeration checked the template's 13 sites, 16 internal bonds and all 20 slots, and sample tori `(3,3),(3,4),(4,3),(4,4)` had `2LN` distinct non-loop bonds. The general edge-counting argument is given above; samples alone are not the basis for that conclusion. These are semantic sanity checks, not verifications of H1/H3 certificates or of the ignored proof. Only this report was written.

**Complete declaration map.** The table covers all 107 explicitly authored declarations, including the five instances and the theorem. `PatternData`'s three fields and inductive constructors are included in their parent rows; generated constructors, recursors and elaborator proof helpers add no separate mathematical statement. Namespace abbreviations: **D** = `AKLT.Defs`, **C** = `AKLT.Challenge`, **P** = `AKLTPalomar`.

Paper keys: **S1** = [sec1-result.tex](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex), **S2** = [sec2-moments.tex](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex), **S3** = [sec3-quantum-frames.tex](/home/ubuntu/aklt/manuscript-v2/sec3-quantum-frames.tex), **S4** = [sec4-periodic-gap.tex](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex), **S6** = [sec6-walks.tex](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex), **S7** = [sec7-recursion.tex](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex), **S8** = [sec8-inputs.tex](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex), **AC** = [app-input-contracts.tex](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex). References below are source lines, with labels where available.

| Lean declaration | Lean lines | Paper location | Mathematical correspondence |
| --- | --- | --- | --- |
| `D.Plane` | 21 | S1:129–140; S2 `d:moment`, 20–21 | Ambient integer plane, not a quotient. |
| `D.latticeDist` | 24 | S1:129–138 | Ambient taxicab distance. Integer differences precede absolute values. |
| `D.Compass` | 27–29 | AC `d:memory-automaton`, 22–35 | The four absolute directions E,N,W,S. |
| `Fintype D.Compass` instance | 31–32 | AC:23–24 | Enumerates exactly those four directions. |
| `D.Compass.step` | 35–39 | AC:23–24 | The four specified unit displacements. |
| `D.Compass.reverse` | 42–46 | S6 `d:weights`, 658–660 | Negation of an incoming unit direction. |
| `D.Adjacent` | 49 | S1:134; S2 `d:pinmodel`, 108–110 | Nearest-neighbour relation `d=1`. |
| `Decidable (D.Adjacent x y)` instance | 51 | Same adjacency convention | Computational decision of that equality; no additional assumption. |
| `D.neighbours` | 54 | S1:134; S6 `d:pattern`, 489–509 | Four physical neighbours. |
| `D.positiveNeighbours` | 57 | S2 `d:pinmodel`, 108–110 | Chosen orientation to count unordered internal bonds once. |
| `D.internalBonds` | 60–61 | S2 `d:pinmodel`, 98–110 | Exactly the internal nearest-neighbour unordered bonds, positively indexed. |
| `D.square` | 64–66 | S4 `d:shells`, 10–12 | Translated integer square; harmless extension to radius zero. |
| `D.Vec3` | 77 | S2 `d:moment`, 9–12 | Three real coordinates. |
| `D.dot` | 80 | S2 `d:moment`; `d:pinmodel`, 108–110 | Euclidean scalar product. |
| `D.normSq` | 83 | S2 `d:moment`, 9 | Squared Euclidean norm. |
| `D.UnitVector` | 86 | S2 `d:moment`, 9; S6:510 | Full unit sphere, not a finite alphabet. |
| `D.goldenRatio` | 89 | S2 `d:moment`, 10 | Exact `(1+√5)/2`. |
| `D.icoRadius` | 92 | S2 `d:moment`, 10 | Exact `√(φ+2)`, positive. |
| `D.IcoLetter` | 95 | S2 `d:moment`, 12–16 | Three coordinate groups and two independent binary signs. |
| `D.signValue` | 98 | S2:12–16 | Values +1 and −1, each once. |
| `D.icoVector` | 101–106 | S2 `d:moment`, 10–18 | The same twelve normalized icosahedron vectors. |
| `D.Status` | 109–111 | S6 `d:domain`, 8–17 | U, D and removed X. |
| `Fintype D.Status` instance | 113 | S6:10–11 | Exactly the three statuses. |
| `D.SpinLetter` | 117 | S2:16–19; S6:25–26 | Common alphabet `D ∪ {0}`; zero has U weight zero. |
| `D.spinVector` | 120–122 | S2 `d:moment`, 12–18 | Zero or the corresponding geometric atom. |
| `D.spinWeight` | 126–128 | S2:16–19; S6:23–26 | U mass 1/12; D masses 1/20 and 2/5; X omitted by active-site indexing. |
| `D.PairType` | 139–141 | S7 `d:pairenv`, 36–41 | B collinear and C diagonal. |
| `Fintype D.PairType` instance | 143 | S7:37–40 | Both pair types, no empty type. |
| `D.localThreshold` | 154 | S6 `h:H1`, 538–539; S8 `t:H1`, 167–177 | Straight 961/1000 and turning 187/200. |
| `D.passageFactor` | 157 | S6 `d:weights`, 655–656 | Reciprocal threshold `x_τ`. |
| `D.alphaBound` | 160 | S7 `l:log-mean-bounds`, 283–296 | Exact `a_s=145217/10^6`, `a_t=150000/10^6`. |
| `D.betaBound` | 163 | S7:283–296 | Exact `b_s=352782/10^6`, `b_t=357549/10^6`. |
| `D.betaPrimeBound` | 166 | S7:283–296 | Exact `b′_s=340008/10^6`, `b′_t=344661/10^6`. |
| `D.DirectionWord` | 169 | S6 `d:weights`, 657–660 | Finite sequence of absolute nearest-neighbour steps. |
| `D.wordVertex` | 172–173 | S6:657–669; AC:27–28 | Start plus preceding steps; clamped extension after the last vertex. |
| `D.wordBond` | 176–177 | S6:657–660 | Unordered two-endpoint bond at one departure. |
| `D.IsTrail` | 180–181 | S6 `d:weights`, 657–672 | Distinct unoriented bonds and forbidden initial reversal. |
| `D.wordIncoming` | 184–185 | S6:668–669 | Designated first incoming direction, then actual previous step. |
| `D.wordStraight` | 188–189 | S6:661–669 | Outgoing direction equals incoming direction. |
| `D.departureCount` | 192–193 | S6:661–662; S7:525,529 | Number of departures strictly before the current index. |
| `D.wordRevisit` | 196–197 | S6:661–664; S7:525 | Positive prior departure count, not just arrival history. |
| `D.trailWeight` | 200–201 | S6 `d:weights`, 661–665 | Full `W(w)`: 1/5 at revisits, `x_τ/3` otherwise. |
| `D.trailBaseWeight` | 204–205 | S6:91–95; S7 `d:kernel`, 547–555 | Mass-free `3^{-n}(3/5)^rev`; no passage factors yet. |
| `D.kernelStart` | 216 | S7 `d:kernel`, 521 | `u=(-1,0)`. |
| `D.kernelCentre` | 217 | S7:521 | `c=(0,0)`. |
| `D.kernelTarget` | 218 | S7:521–522 | B target `(1,0)`, C target `(0,1)`. |
| `D.kernelIncoming` | 219 | S7:524 | West, equal to `u-c`. |
| `D.ClosedTrail` | 222–225 | S7 `d:kernel`, 523–525 | Centre-avoiding first-hit trail to target; name remark M2. |
| `D.deadAt` | 228–229 | S7:529 | Centre or at least two previous departures. |
| `D.responseNeighbours` | 232–234 | S7:527–528 | Three non-arrival neighbours, with actual incoming direction. |
| `D.liveOtherNeighbours` | 237–240 | S7:528–534 | Live non-outgoing `f,g`, excluding centre/twice-departed sites. |
| `D.responsePairs` | 243–244 | S7:531–534 | All two-element pairs of live others and outgoing neighbour. |
| `D.pairCoefficient` | 247–251 | S7:531–535 | `a`, `b` or one-live-neighbour `b′` in exactly the specified cases. |
| `D.responsePairType` | 254–256 | S7 `d:pairenv`, 38–40; `d:kernel`, 536 | Collinear/diagonal classification on valid response pairs. |
| `D.kernelWitness` | 259–261 | S7 `d:kernel-order`, 575–579 | Prescribed exact dyadic vector `(1,h_C)`. |
| `D.kernelRho` | 264 | S7:579; S8 `t:inputs`, 299 | Exact contraction ceiling `993015/10^6`. |
| `D.witnessKappa` | 267–268 | S7:540,581 | Sum over all live pairs of coefficient times `h_Y`, aggregating all shifts. |
| `D.firstVisitList` | 271–272 | S7:525–526,581–588 | First-departure indices in increasing path order. |
| `D.shortOrderLE` | 276–285 | S7 `d:kernel-order`, 583–586,593–596 | Exact score comparison, zero at infinity, path-index ties. |
| `D.kernelOrdering` | 288–291 | S7:579–590 | Short ordering for `n≤12`; straight then turning path order otherwise. |
| `D.exposureSum` | 294–296 | S6 `l:exposure`, 437–446; S7:548–549 | Reward times product of all passage factors up to and including its position. |
| `D.closedContribution` | 299–300 | S7 `h:H3`, 604–606 | Base weight times the ordered `h`-weighted exposure sum. |
| `D.kernelPartialRow` | 303–306 | S7:602–607 | Exact finite row sum over lengths 1 through R. |
| `D.PositiveVectorBound` | 309–310 | S7 `h:H3`, 598–620 | Both rows, every nonnegative integer cutoff, fixed `ρ₀h_X`. |
| `D.templateSites` | 321 | S6 `d:pattern`, 488–492 | Thirteen-site taxicab diamond. |
| `D.templateTips` | 324 | S6:492,506–509 | Four axial covering tips. |
| `D.templateCorners` | 327 | S6:492–494 | Four diagonal corners. |
| `D.externalSlot` | 330–336 | S6:493–494,510–512 | All twenty external half-bonds, independently indexed. |
| `D.PatternData` and fields `outgoing`, `status`, `kept` | 339–342 | S6:495–509 | Raw finite choice of out-neighbour and site data; constraints imposed separately. |
| `D.PatternData.statusAt` | 345–346 | S6:489–509 | Template status; harmless X extension outside template. |
| `D.PatternData.keptAt` | 349–350 | S6:496–509 | Compass kept sets converted to physical neighbours; empty outside template. |
| `D.PatternData.Covered` | 353–369 | S6 `d:pattern`, 495–509 | All covered-pattern rules; tip/X kept fields are redundant. |
| `D.PatternData.bonds` | 372–376 | S6:505–509; `d:domain`, 11–13 | Mutual keep at non-tips, covering-tip exception, each internal bond once. |
| `D.PatternData.active` | 379–380 | S6:513–514; `d:domain`, 23–26 | Exactly the nonremoved template sites. |
| `D.PatternData.spins` | 383–384 | S6:513–514; S2 `d:moment` | Coordinates of an active-site spin assignment, harmless zero extension. |
| `D.patternFunctional` | 388–399 | S6:510–516; `d:domain`, 18–26 | Finite product functional with all slots; next changes only passage law/out-bond. |
| `D.patternCurrent` | 402–403 | S6:513–514 | `Z_cur`, constant observable one. |
| `D.patternNext` | 406–407 | S6:515–516 | `Z_next`, constant observable one. |
| `D.LocalPatternBound` | 410–413 | S6 `h:H1`, 531–541 | Threshold range and every covered pattern/every unit-slot assignment. |
| `C.Size` | 424 | S1 `d:model`, 18–19; `t:main`, 41–46 | Exactly integer periods at least three. |
| `C.size_neZero` instance | 427 | S1:18–19 | Nonzero modulus follows from the existing period bound. |
| `C.Site` | 430 | S1 `d:model`, 19–20 | Product of the two cyclic groups. |
| `C.Direction` | 433 | S1:24,34–38 | Two positive coordinate orientations. |
| `C.Bond` | 437 | S1:20,24,30,34–38 | Bijective indexing of simple unordered edges for periods at least three. |
| `C.nextSite` | 440–441 | S1:34–38 | Positive horizontal/vertical endpoint modulo the periods. |
| `C.V` | 447 | S1:21–23; S3 `d:poly`, 14–35 | Spin-two space in its binomially normalized orthonormal basis. |
| `C.spinZ` | 451–452 | S3:37–65; S1:22–23 | Spin-two magnetic matrix; generator conventions preserve the bond Casimir. |
| `C.spinPlus` | 456–458 | S3:51–60; `d:poly`, 16–18 | `z₁∂₂` in normalized coordinates, coefficient `√(k(5-k))`. |
| `C.spinMinus` | 461 | S3:51–60; `d:poly`, 16–18 | Adjoint lowering matrix. |
| `C.Configuration` | 464 | S1:21; S3:74–76 | Labels for the tensor-product orthonormal basis. |
| `C.Hilbert` | 468 | S1:21; S3 `d:poly`, 14–35,74–76 | Complex tensor Hilbert space, represented as Euclidean coordinates. |
| `C.atSite` | 472–475 | S1:21–23; S3 `l:edge`, 128–134 | Single-site matrix tensored with spectator identities. |
| `C.onBond` | 478–480 | S1:22–23; S3 `l:edge`, 112–124 | Total-spin component on the two endpoints. |
| `C.bondCasimir` | 485–489 | S1:22–23; S3:112–124 | Total-spin squared operator on the bond. |
| `C.spin4Space` | 493–494 | S1:22–23; S3:112–124 | Its eigenvalue-20 space, the spin-four summand. |
| `C.P` | 498–499 | S1 `d:model`, 22–23 | Orthogonal projection onto that summand. |
| `C.H` | 502 | S1 `d:model`, 28–31 | Sum of one unscaled projection per edge. |
| `C.SpinorPolynomial` | 505 | S1:26–27; S3:74–76 | Polynomial ring in two variables at every physical site. |
| `C.singlet` | 509–512 | S1 `d:model`, 24–27 | Oriented determinant `q_xy`, using zero-based variable indices. |
| `C.vbsPolynomial` | 516–517 | S1:27; S3 `p:toruskernel`, 202–205 | Product of all oriented determinants, multidegree four at each site. |
| `C.monomialDegree` | 520–523 | S3 `d:poly`, 15–18,74–76 | Exponents `(4-σ_x,σ_x)` of a tensor monomial. |
| `C.B` | 528–531 | S1:27; S3 `d:poly`, 16–18 | The same unnormalized VBS polynomial in orthonormal coordinates. |
| `C.MainStatementV2` | 546–551 | S1 `t:main`, 41–47 | All-size nonzero VBS/unique kernel and one eventual uniform positive spectral bound. |
| `P.H1` | 559 | S6 `h:H1`, 531–541; S8 `t:H1`, 167–177 | Equivalent to H1 at the paper's two fixed thresholds. |
| `P.H3` | 563 | S7 `h:H3`, 598–620; S8 `t:inputs`, 297–325 | Equivalent to the fixed H3_h, with every cutoff. |
| `P.Main` | 566 | S1 `t:main`, 41–47 | Alias for the equivalent physical main conclusion. |
| `P.aklt_gap_of_inputs` | 569–570 | S1 proof of `t:main`, 49–71; S7 `t:rec`, 1012–1056; S8 `t:inputs`, 288–325 | Requested conditional reduction; fixed H2 is independently available. Placeholder proof intentionally excluded from this review. |

The file's module/import/visibility commands, `noncomputable section`, notation scopes and auxiliary-proof-cache resets at lines 1–17, 73, 135, 150, 212, 317, 420 and 538 have no paper-level mathematical counterpart. They do not replace any of the definitions or add a mathematical hypothesis. In particular, only Mathlib is imported; no certificate premise is silently imported as an axiom.
