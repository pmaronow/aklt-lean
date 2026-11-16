VERDICT: SOUND WITH FIXES

Lane R3: `sec5-cut.tex` and `app-lattice-topology.tex`. Line numbers below refer to the frozen bundle's LaTeX sources. I read all manuscript source files for context and checked this lane line by line. I found no Critical or Major defect in the implication **(P) ⇒ window estimate**, or in the boundary-connectivity lemma. The fixes below concern well-posedness, an imprecise geometric case distinction, and an unnecessarily strong decay requirement in a remark. The verdict is conditional on (P); it does not independently certify the computer-assisted inputs used elsewhere to prove (P).

## 1. Findings

1. **Minor — establish positivity before using logarithms and pointwise probability ratios.**

   **Location:** `sec5-cut.tex:7–11,52–61,67–79`, especially `e:Zpin`, `e:cutcost`, `l:cut` and `e:cutratio`.

   **Exact claims:** “the corresponding probability measures,” `Ψ_D(τ) = Z_D^τ/Z_D^0`, `e(η,s) = log Ψ_{G\X}(ηs) − log Ψ_G(ηs)`, and the ratio `μ^η_{D,F}(n_B=s)/ν(s)` for **all** window configurations.

   **Issue:** The required strictly positive denominators and arguments of the logarithms are not proved at their introduction. Continuous bond and leg factors can vanish, so their nonnegativity alone does not establish these assertions. The pointwise ratio also requires `ν(s)>0`, beyond the fact that ν is a probability measure. These assertions are true in the setting actually used; this is a missing well-posedness justification, not a zero-denominator counterexample.

   **Repair:** For any finite collection of unit pins, choose a unit vector q that is not the negative of any pin. Put every remaining spin equal to q. Every internal bond factor is then 2 and every surviving leg factor is positive. Continuity gives a product of open spherical neighborhoods on which the integrand is positive, of positive product measure. Thus `Z_D^τ>0`; also `Z_D^0>0`. For `D=∅`, both partition functions are 1. For the checkerboard frame, positive site weights and `1+s_x·s_y ≥ 1−γ_+>0` on every bond imply `W_B(s)>0`; applying the continuous positivity argument to `Z_{G_1}^s` gives `ν(s)>0`. Insert these facts before the logarithms and the ratio. Arbitrary unit pins are allowed in the continuous argument; they need not be frame letters.

2. **Minor — the removal lemma needs a nonempty list, or a separate empty-list clause.**

   **Location:** `sec5-cut.tex:101–105,109,127–129`, `l:removal` / `e:removal`.

   **Exact claim:** For distinct sites `x_1,…,x_p` satisfying the stated conditions, the right side includes `F(b(x_1)−3)`.

   **Issue:** No condition `p≥1` is stated. For an empty list, the quantified conditions are vacuous but `x_1` and that right side are undefined. This does not obstruct the theorem's application: there U′ is finite and nonempty, hence its outer boundary X is nonempty.

   **Repair:** State `p≥1`. Separately record that removing `X=∅` changes `log Ψ` by zero. In the application at `sec5-cut.tex:221`, explicitly obtain nonemptiness of X from the nonemptiness of U′ established in `l:Xconn` and finiteness of U′.

3. **Minor — make the side-depth argument in the cut count precise.**

   **Location:** `sec5-cut.tex:179`, proof of `l:cutgeom(3)` / `e:cutsum`.

   **Exact claim:** A side that did not meet `C_M` has “distance at most 0,” and after changing the radius by j “their distance is at most j.”

   **Issue:** This needs an orientation relative to the particular edge E. A side outside the square beyond the *opposite* edge has large positive distance from the half-plane beyond E. A side's ordinary distance to a half-plane also changes by **at most** j, rather than always exactly j. The intended exclusion of overlapping sides is valid, but the stated dichotomy suppresses the opposite-edge case.

   **Repair:** Use signed inward depths `δ_E` of the supporting coordinate lines. For example, for the left edge take `δ_E=x_1+M+1`, and for the right edge take `δ_E=M+1−x_1`. Changing `k` to `k±j` changes this signed depth by at most j. If the original side meets `C_M`, `l:shellgeom` gives `δ_E≥s/3`, so the new depth is at least `s/3−j>l_0/2+j` once `s>3l_0`. If the original side misses `C_M` beyond E, `δ_E≤0`, so its new depth is at most j, below `l_0/2+j−2`. If it misses beyond the opposite edge, its depth is at least `2M+2`, and remains above this interval after the shift. Here radii `k±j` are at least 1 and much smaller than M; since `dist_∞(y,C_M)=1`, their varying-coordinate intervals intersect the corresponding coordinate interval of `C_M`. Thus these cases exhaust the possibilities for a shifted side that meets `C_M`. This supplies the missing qualification without changing 48 cells, 192 sites, or any displayed bound.

4. **Minor — the crude-count decay requirement in the final remark is stronger than necessary.**

   **Location:** `sec5-cut.tex:228–229`, Remark 5.9, `r:Pweak`.

   **Exact claim:** “with the crude count `|X| ≤ 4(2M+1)^2` used above one needs `F(d)=o(d^{-8})` instead.”

   **Issue:** The proof requires a uniformly bounded cut cost, as the paper correctly emphasizes at line 134. With `s=M^{1/4}`, the crude long-part contribution has the form `O(M^2) sup_{r≥c M^{1/4}−C} F(r)`. The bound `F(d)=O(d^{-8})` already makes this uniformly bounded. Little-o makes it tend to zero, which is unnecessary. For example `F(d)=(d+1)^{-8}` is not `o(d^{-8})` and suffices for this argument.

   **Repair:** Replace “one needs … `o(d^{-8})`” by “`O(d^{-8})` suffices for a uniform bound; `o(d^{-8})` makes the long-part contribution vanish.” The main exponential theorem is unaffected.

## 2. Statement table

“Correct” for (P) means a well-posed hypothesis, assumed in this lane. All other verdicts assess the stated mathematical result; the indicated fixes do not change the main conclusions or constants.

| Number / label | Location | One-line content | Verdict | Dependencies |
|---|---|---|---|---|
| Lemma 5.1, `l:35` | `sec5-cut.tex:23–33` | A spin subject to at most three unit-vector factors has conditional mean of norm at most 3/5. | correct | `e:moments`; Gram identity in line 30; normalization and convex mixtures. |
| Lemma 5.2, `l:exact` | `sec5-cut.tex:37–46` | Products with at most four incident factors per site have identical frame sums and sphere integrals. | correct | `d:frame`; separate degree ≤4; finite sums and Fubini. |
| Lemma 5.3, `l:cut` | `sec5-cut.tex:58–86` | A cut with logarithmic cost bounded by ε gives a common reference law with density ratios `e^{±2ε}` and pairwise TV ≤ `tanh(2ε)`. | correct after fix | Finding 1; `e:muDW`; `l:exact`; factorization; elementary likelihood-ratio/TV inequality. |
| Hypothesis 5.4 (P), `h:P` | `sec5-cut.tex:90–99` | Responses of distance-two pairs with a removed common neighbor decay with distance to the fixed original boundary layer S(G). | correct | Positive normalized continuous measures; graph-distance convention. Discharged elsewhere by `t:rec`, not assumed proved by this report. |
| Lemma 5.5, `l:removal` | `sec5-cut.tex:101–132` | A connected removal order bounds the logarithmic cut cost by a first-site constant and a sum of pair responses. | correct after fix | Findings 1–2; (P); `l:35`; joint conditional independence; free positivity; `e:Ij`; logarithm bound. |
| Lemma 5.6, `l:cutgeom` | `sec5-cut.tex:150–184` | The tapered shell neighborhood provides a separating cut, depth ≥3, and the weighted cut bound. | correct after fix | Finding 3; `d:W`; `e:shells`; `l:shellgeom`; cell/site distance comparison; Lipschitz distance functions; square-side intersection count. |
| Lemma 5.7, `l:Xconn` | `sec5-cut.tex:186–210` | The chosen site cut X is nearest-neighbor connected. | correct | `l:boundaryconn`; shell exclusion `i∉I_0`; `e:Ucut` / `e:Ualt`; radial paths; complement paths; exclusion of diagonal-only blocks; cell/site path lifting. |
| Theorem 5.8, `t:cutMOS` | `sec5-cut.tex:216–226` | (P) implies the window estimate for both offsets with `l_0=20` and a uniform positive coupling probability. | correct after fix | `l:cut`, `l:removal`, `l:cutgeom`, `l:Xconn`; `d:W`; polynomial times exponential tends to zero. Findings 1–3 are the inherited local clarifications. |
| Remark 5.9, `r:Pweak` | `sec5-cut.tex:228–229` | Weaker decay assumptions can replace exponential decay, with a better count for long cut sides. | correct after fix | Finding 4; removal argument; 192-site taper-level bound; `O(s^2)` long-part count explained below. |
| Lemma B.1, `l:boundaryconn` | `app-lattice-topology.tex:8–30` | Finite nonempty A, *-connected A and complement, and no diagonal-only block imply nearest-neighbor connectivity of its outer *-boundary. | correct | The appendix's explicit cycle-space and parity proof; no external connectivity theorem is required. |

For completeness, the numbered equations in Section 5 are also covered:

| Equation / label | Location | Content and check |
|---|---|---|
| (5.1), `e:Zpin` | `sec5-cut.tex:8–10` | Pinned/free partition functions with original legs only; correct, with positivity as in Finding 1. |
| (5.2), `e:moments` | `sec5-cut.tex:14–16` | Uniform spherical even moments as sums of pairings; correct, including the empty product at k=0. |
| (5.3), `e:cutcost` | `sec5-cut.tex:53–55` | Definition of the logarithmic pinned/free removal response; well-defined after Finding 1. |
| (5.4), `e:cutratio` | `sec5-cut.tex:60–62` | Common-reference probability ratio between `e^{-2ε}` and `e^{2ε}`; correct. |
| (5.5), `e:windowlaw` | `sec5-cut.tex:68–70` | Frame window probability is `W_B(s) Z_G^{ηs}/Z_{D,F}^η`; correct. |
| (5.6), `e:P` | `sec5-cut.tex:94–96` | The inequality in the hypothesis; graph distances are to S(G), not to the holes. |
| (5.7), `e:removal` | `sec5-cut.tex:103–105` | Removal bound with 0.0707, 2.73, and 1.22; correct for p≥1. |
| (5.8), `e:Ij` | `sec5-cut.tex:110–112` | Integrated star polynomial for k≤4; correct coefficients 1/3 and 1/15. |
| (5.9), `e:telescope` | `sec5-cut.tex:114–116` | Telescoping of logarithmic partition-function ratios; signs correct. |
| (5.10), `e:Ucut` | `sec5-cut.tex:141–143` | Definition of the tapered cell region; consistent with the subsequent alternative description. |
| (5.11), `e:Xcut` | `sec5-cut.tex:145–147` | Outer site *-boundary and the two remaining regions; correct. |
| (5.12), `e:cutsum` | `sec5-cut.tex:156–158` | Weighted depth sum; correct with the geometric qualification in Finding 3. The weaker exponent `s/6−7` is harmless. |
| (5.13), `e:Ualt` | `sec5-cut.tex:192–194` | Equivalent definition of U on all cells; correct because `h≥l_0/2+t>0` forces membership in `C_M`. |

### Checks of the substantive steps

**Frame versus continuous model.** In `e:windowlaw`, the window spins remain fixed frame letters. Summation over G alone is replaced by a continuous integral, with one factor per original lattice direction and hence at most four incident factors at every summed site. Removing sites only decreases this number. No correlation expectation is transferred by the design identity. In particular an observable could raise the degree above four, and Lemma 5.2 gives no such transfer. Both offsets have the same degree and positivity properties.

**Cut factorization and TV constant.** The two regions have no mutual bonds, and retain respectively only window pins and exterior pins. Thus the factorization at lines 71–77 holds, with no new leg factor into X. If `q(s)=W_B(s)Z_{G_1}^s`, then `ν=q/Σq` and the window law is exactly

`p_η(s)=ν(s)e^{-e(η,s)}/Σ_t ν(t)e^{-e(η,t)}`.

The normalizing sum is in `[e^{-ε},e^ε]`. Two such laws satisfy `p≤R p′` and `p′≤R p` for `R=e^{4ε}`. On `{p>p′}`, writing `x=p′(A)` and `y=p(A)` gives both `y−x≤(R−1)x` and `y−x≤(R−1)(1−x)/R`. Their maximum possible minimum is `(R−1)/(R+1)=tanh(2ε)`. The signs in the complement inequality are correct. The argument also covers ε=0 and an empty window (one configuration).

**Removal constants.** After removing x_j, all surviving neighbors of x_j are mutually nonadjacent, carry no original leg, and have at most three remaining bonds. Conditional on the spins outside this *whole neighbor set*, their joint law is a product. Let the means be m_i. Then

`Σ_{i<i′} m_i·m_{i′} ≥ −(1/2)Σ_i |m_i|²`, with `|m_i|≤3/5`.

For k≤3 the pinned expectation of I_j is at least 0.82. For k=4 it is at least `1−4(9/25)/6−3(9/25)^2/15 = 2294/3125 = 0.73408 > 0.734`. Each of the three quartic products uses four distinct neighbors, so its conditional expectation is a product of two scalar products of means and has absolute value at most `(9/25)^2`. Thus the bracket has absolute expectation at most 0.3888. Free positivity makes its free expectation nonnegative and makes the entire free expectation of I_j at least 1. The bracket-response bound 0.7776 is conservative but valid. Exact comparisons give

`1/0.82 ≤ 1.22`, `2/0.734 ≤ 2.73`, and `0.7776/(15·0.734) ≤ 0.0707`.

Every pair used in (P) is at graph distance two, has the just-removed x_j as a common neighbor, and lies in `G\Y_j`, with `Y_j⊂G\S(G)`. The Lipschitz estimate gives distance at least `b(x_j)−3` to S(G). The cases k=0 and k=1 have I_j=1 and zero response. The quartic residual is paid only at the first removal, since every later site has a previously removed neighbor. No decay assertion about a four-point response is needed.

**Geometry and connectivity.** The two cell-distance lower bounds in lines 169–175 give site graph depths at least `s/6−3` on the long part and `2max(t,l_0/4)−5` on the taper. In particular the latter is at least 5 for `l_0≥20`, and the former exceeds 3 for sufficiently large s. At a fixed taper level t=j there are at most two square radii, at most three permissible integer depths h′ (in fact the half-open interval has only two), and at most eight isolated square-boundary intersections for each pair. The bound 192 is safe. If `l_0/4` is not integral, the geometric-series estimate still holds: the number of integers `j≤l_0/4` is at most `l_0/4+1`, and the remaining geometric tail is bounded by `1/(1−ϑ²)` after factoring out `ϑ^{l_0/2−5}`.

In `l:Xconn`, radial paths stay in U and reach its clipped radius-k skeleton; the skeleton is nonempty and connected because the clipping square has side at least that of the radius-k square and the clipped rectangle contains a corner of the latter. The three complement-path cases cover every cell outside U and terminate outside `C_M`. The block argument correctly excludes all three possibilities for the smaller-radius set (row/column, a missing diagonal site, or an included diagonal site); its last case contradicts the established corner clearance when `s≥3l_0`. Lifting to sites preserves *-connectivity, gives the stronger nearest-neighbor connectivity of the complement, and excludes site blocks with just two diagonal sites. These are all the hypotheses of B.1; replacing *-connectivity of the complement by nearest-neighbor connectivity in this application is permissible.

**Uniformity in the theorem.** A concrete admissible choice, after making the last geometric term at most 1, is

`ε_max = 0.0707 + 2.73 A + 1.22 A θ^{-3}[192 θ^5(6 + 1/(1−θ²)) + 1]`.

For fixed `0<θ<1`, `(2M+1)^2 θ^{M^{1/4}/6−7}→0`. All shape thresholds depend only on `l_0=20`; the remaining threshold depends only on A and θ, uniformly in y, i, pins and offset. One can define `p_0=2/(e^{4ε_max}+1)>0`, which is exactly `1−tanh(2ε_max)` and avoids any numerical cancellation. A small coupling probability is sufficient; ε_max need not be small.

**The weaker-decay remark.** For the first part of Remark 5.9, the asserted sharper count follows directly from `s/12<t≤s/12+1` on the long part: integer t has only one possible value, and its cells lie on the two square spheres of radii `k±t`. Their total size is `O(k+t)=O(s²)` since `k≤s²`. The taper has at most 192 sites at each t. If `C=sup_{d≥1}d²F(d)<∞` and F(0) is finite, the taper is controlled by a summable `O((t+1)^{-2})` envelope, and the long part by `O(s²)·O(s^{-2})`. This works even if F is not monotone. Thus the stated summability plus quadratic bound is sufficient (indeed the quadratic bound already gives summability for a nonnegative sequence). With the crude count, the correction in Finding 4 applies.

**Appendix B.** In Step 1, cancelling diagonals with triangles leaves a finite even nearest-neighbor edge set. Each vertical cut is crossed an even number of times, so the coefficients n(i,j) have finite support, including in the negative-j direction. The horizontal coefficients of the square-boundary sum match by construction; the vertical coefficients match by evenness on the vertical half-line. Every square boundary is the mod-two sum of two triangle boundaries. In Step 2, a triangle intersects the cut in zero or two edges; the proposed partition of cut edges therefore makes its `B_1` parity zero. The closed walk formed using the two connectivity assumptions has parity one, giving the contradiction. In Step 3, two distinct non-neighbor outer endpoints of linked edges are the diagonal sites of a block with a common inner endpoint. Assumption (iii) forces the fourth block site outside A, yielding a two-step path in the outer boundary. The example at line 18 correctly shows why (iii) cannot simply be omitted.

## 3. Formalization notes

1. **Retain the ambient graph and original leg set in the type of a domain.** `Z_D^τ` and `Ψ_D(τ)` are not functions of D and its ordinary geometric boundary alone. They depend on the original G and its legs. Removing Y never creates pinned legs into Y. Likewise, the factorized `Z_{G_1}^s` and `Z_{G_2}^η` in the cut proof use the explicitly retained pin subsets, not all legs of these new regions. A definition such as a finite site set plus an explicit finite set of pinned oriented legs avoids accidental re-pinning. The paper states the intended convention, but the abbreviated notation should not be copied literally as a function of D only.

2. **Use separate types for cells and sites.** The cell map is `C_c^(o)=(2c_1+o,2c_2)+{0,1}²`. Specify the inverse with integer floor division, including negative coordinates and offset 1. Prove cells partition the site lattice, each has four sites, graph neighbors lie in the same or neighboring cells, and sites in cells at cell ℓ∞ distance q≥1 have site ℓ∞ distance at least `2q−1`. The graph distance d in (P) and b is the full-lattice ℓ¹ distance, not distance in G or in a punctured domain. All geometric `dist` quantities in lines 167–175 are cell ℓ∞ distances.

3. **Make integer domains explicit.** Take `M,i∈ℕ`, `l_0∈2ℕ`, `l_0≥20`, with i≥2, and use real `s=M^{1/4}` and integer `k=⌊is⌋`. The identity `h(c)=max(0,M+1−|c|_∞)` and the cardinality `(2M+1)²` use integral M. The range `2≤i≤s` means an integer i with the indicated real inequality. A common sufficiently large threshold must include the `M_g(l_0)` hypothesis of `l:shellgeom`, `s>3l_0`, `s/12≥1`, `k−s/12−1>(i−1)s`, and `k≤M+1−l_0/2`. Floors cost the one or two units already allowed in the text. No parity restriction on M or i is needed. The role of even l_0 includes integrality of `l_0/2` in the block contradiction.

4. **Distances to sets and empty cases.** Define distances as minima for nonempty target sets, or use an extended metric with explicit finiteness lemmas. For finite nonempty G, its boundary layer S(G) is nonempty. When (P) has a pair to quantify over, G is nonempty. Distances to `Z²\G` are attained, integer-valued and 1-Lipschitz; `b≥3` is equivalent to exclusion from S(G). Empty G, empty removed set, empty B, and empty G_1 or G_2 can be handled with empty product/integral conventions. The latter two have partition function 1. Prove finite nonempty U′ has a nonempty outer boundary before choosing x_1.

5. **Continuous probability construction.** Use normalized surface measure on `S²`, finite product measure and a continuous bounded nonnegative density. Establish finite strictly positive normalizers as in Finding 1. Local conditional kernels have positive normalizers for every fixed configuration of other spins, so no assertion about a zero-probability conditioning event is needed. Identify these explicit kernels with conditional distributions almost everywhere. Conditional independence of an entire set with no internal bonds must be a joint product statement; pairwise conditional independence alone is insufficient in general. The four-neighbor argument uses the joint statement.

6. **Moment and algebra nodes.** Prove the spherical moment identity (or just its degree-two and degree-four cases for the main reduction), odd-moment vanishing, nonnegative index-contraction sums for all products of scalar products, and the Gram-polynomial identity in Lemma 5.1. Treat the added antipodal factors in the fewer-than-three-factor case as a mixture with weights proportional to their positive normalizers; the normalized mixture weights are generally not the original 1/2 coefficients. This distinction does not change the bound.

7. **Integration and quadrature nodes.** Products of finitely many continuous factors are integrable; Fubini and finite-sum interchange apply. The frame equality follows by separate polynomial degree and induction over sites. If self-factors `1+n_x·n_x` are admitted by the very general wording of `l:exact`, first replace them by the constant 2 on the sphere; alternatively explicitly require distinct endpoints for spin-spin factors, as in every application. Count incidence at both endpoints of a bond, irrespective of how its displayed factor is oriented.

8. **Removal algebra.** Introduce `Y_0=∅` explicitly, normalize the integration-out identity, prove the logarithmic telescoping identity, and use `|log a−log b|≤|a−b|/min(a,b)` for positive a,b. Encode all finite decimal constants as rationals; no floating-point argument is needed here. The quartic bracket involves four distinct neighbors, and this must be retained when using conditional independence.

9. **Graph and planar-combinatorial nodes.** A finite nonempty connected graph admits an ordering with each non-root vertex having an earlier neighbor, e.g. by distance from a root. Square exterior connectivity, radial-path termination, connectivity of the clipped skeleton, at most eight intersections of square boundaries without coincident sides, the signed-depth exclusion, and the four possible low-radius subsets of a block each need explicit lemmas. The distinction between nearest-neighbor and *-adjacency must remain explicit in both lattices.

10. **Finite-support mod-two chains in Appendix B.** Represent edge sets as finitely supported F₂-valued functions or finite sets with symmetric difference. Sums described over infinite half-planes or half-lines reduce to finitely many nonzero incidences; establish this before parity counting. The triangle boundaries generate all finite even chains of the king graph by the proof in Step 1; this is a separate theorem rather than a consequence of ordinary nearest-neighbor planar duality. The closed walk in Step 2 need not be simple: use its edge multiplicities modulo two. In Step 3, outer endpoints can coincide; a zero-length connecting path is permitted.

11. **Uniform and asymptotic statements.** Formalize “for s large” as an existential threshold independent of y, i and o, with the fixed l_0 parameter. Convert the weighted bound's real exponents to real powers of a positive θ; b itself is integral. The final limit can be proved by setting `a=−log θ>0` and comparing `M²` with `exp(a M^{1/4}/6)`. All constants are chosen after fixing A and θ. Use an exact positive expression for p_0, not a machine evaluation of tanh.

### Independent finite evidence

The accompanying `verify_r3.py` writes no data outside this directory. Its output is in `verification.json`.

- **Exact algebra:** symbolic coefficient comparison of the polynomial identity in `l:35`, and rational verification of the four-factor lower bound and all three rounded removal coefficients.
- **Exact finite topology checks:** all 65,535 nonempty subsets of `{0,1,2,3}²` were examined. Of these, 9,349 satisfy the three hypotheses of B.1, and every one has a nearest-neighbor connected outer *-boundary. Complement *-connectivity was checked in a box with a one-site exterior frame; since A is inside the smaller box and that frame is connected, this is equivalent to connectivity of the infinite complement in these cases.
- **Finite cut checks:** 64 choices with `s∈{72,84}`, `M=s⁴`, `l_0∈{20,22}`, `i∈{2,5}`, four boundary placements and both offsets. These placements are away from the excluded corner shells. The checks verified exact site-boundary connectivity, graph depths, and the bound of 48 cells at each taper level. The largest sampled boundary had 6,708 sites. Weighted sums at `ϑ=0.5,0.95,0.999` were checked in **floating-point arithmetic: numerical evidence only**.

These finite checks supplement the proofs and are not substitutes for the universal statements. I did not reproduce the manuscript's separate assertion at `sec5-cut.tex:212` that 430 configurations were checked; that sentence supplies no program or data locator, and the proof expressly does not depend on it.

## 4. External inputs

No external source was retrieved: the review obeyed the restriction to the bundle and this directory. The following distinguishes imported facts from results proved inside the lane.

| Input | Exact form used here | Locator given by the manuscript | Hypothesis check / status |
|---|---|---|---|
| Gaussian pairing formula and radial decomposition | For `g∼N(0,I_3)`, odd coordinate moments vanish and `E∏_{j=1}^{2k}g^{a_j}=Σ_pairings ∏δ_{a_i a_j}`; direction `g/|g|` is uniform on S² and independent of radius, and `E|g|^{2k}=3·5···(2k+1)`. This yields `e:moments`. | `sec5-cut.tex:13–17`; no bibliographic citation or theorem locator. | Correct for centered identity-covariance Gaussian and normalized surface measure. The event g=0 has probability zero. Only moments through degree four are needed for Lemmas 5.1 and 5.5. |
| Spherical-design property of the two frames | Positive weights reproduce the normalized sphere integral of every polynomial of degree ≤4, including the constant polynomial, for both the icosahedron and dual-dodecahedron letters. | `d:frame`, `sec2-frames-Q.tex:51–67`; cites Delsarte–Goethals–Seidel, *Spherical codes and designs*, Geom. Dedicata 6 (1977), 363–388 (`DGS77`), without a theorem/page locator for this fact. | Lemma 5.2 uses precisely the degree-four property and stays within it. The assertion that these specific polyhedra are 5-designs is an upstream input; its external citation was not independently checked from the unavailable source. R3 never uses equality of frame and continuous expectations. |
| Fubini / finite-sum interchange | Repeated integration and frame summation may be exchanged for a finite product of bounded continuous factors on a finite product of spheres. | `sec5-cut.tex:45`; “Fubini's theorem,” no external locator. | All measures are finite, all functions integrable. No limiting interchange or infinite-volume Gibbs measure is involved. |
| Gibbs factorization / conditional independence | Conditional on spins outside an independent set, the spins in that set have a product of their single-site conditional laws. With no bonds between two regions and disjoint pin dependences, their unnormalized partition functions factor. | `sec5-cut.tex:21,71–77,117`; no external citation. | Holds for these finite nearest-neighbor densities with positive normalizers. Applied after removing the common center, so the retained neighbors form an independent set. |
| Elementary logarithm and TV bounds | For a,b>0, `|log a−log b|≤|a−b|/min(a,b)`. If probability laws satisfy `p≤R p′` and `p′≤R p`, R≥1, then `TV(p,p′)≤(R−1)/(R+1)`. | `sec5-cut.tex:123–129` and `81–85`; no external citation. | Correct with the positivity justified in Finding 1. The TV bound is proved in the text, including its optimizing value of x. |
| Connected-graph ordering | A finite nonempty connected nearest-neighbor set has an enumeration with each vertex after the first adjacent to an earlier vertex. | `sec5-cut.tex:221`; no citation. | A rooted spanning tree or distance ordering proves it. X is finite, nonempty, and connected; see Finding 2 for the omitted nonemptiness sentence. |
| Polynomial/exponential comparison | For fixed a>0, `(2M+1)² exp(−a M^{1/4}/6)→0` as integer M→∞. | `sec5-cut.tex:225`; no citation. | Correct; θ∈(0,1) supplies a=−log θ>0. Constants and threshold may depend on A,θ, but not on shell or boundary data. |
| Timár boundary-connectivity argument | The only attributed ingredient is the parity argument: in a connected graph whose finite even edge sets are generated by triangles, a cut separating two connected vertex sets has its edges connected through triangles. The appendix proves generation and the parity implication, then uses condition (iii) to obtain nearest-neighbor paths of outer endpoints. | `app-lattice-topology.tex:32`; cites Á. Timár, *Boundary-connectivity via graph theory*, Proc. Amer. Math. Soc. 141 (2013), 475–480 (`Tim13`). No theorem, lemma or page locator beyond the article range. | **No external theorem is imported.** The required hypotheses are exactly finite nonempty A, *-connected A, *-connected complement, and no block containing exactly two diagonal sites of A. All are verified for U′ in `l:Xconn`. The self-contained proof is valid; the historical attribution was not independently checked against Timár's article. |

The geometric input `l:shellgeom` is internal, at `sec4-mixing-to-gap.tex:70–76`: for sufficiently large integral M, boundary-neighbor y, and `2≤i≤⌊s⌋+1` outside I_0, every radius-k_i square side meeting `C_M` is at least s/3 from each parallel outer half-plane. Section 5 uses the narrower range `i≤s`, so its use is within those hypotheses after including `M≥M_g(l_0)` in the common threshold. Definition `d:W` and the cell-model identification are also internal. The MOS and MO theorems are downstream of this lane and are not invoked in the proof of Theorem 5.8; no extension of an external mixing theorem is needed for the R3 implication itself.
