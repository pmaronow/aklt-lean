VERDICT: SOUND WITH FIXES

The intended 7,962-pattern argument is sound, subject to making the kept-bond convention in Finding 1 explicit. The definition as written admits a broader reading on which (H1) fails; an exact witness is given below. The analytic arguments in Appendix D, including the FKG step, the inversion argument, and the reduction to one spin sector, check out. There are also corrections needed to the computational description and to the claim of global optimality of the displayed constants.

Locations below are relative to `/Users/paronow/aklt-lean/bundle/`. I read all the LaTeX source for context and audited the requested H1 programs and their imported local module `ring.py`. I used no web sources or subagents. Details of the independent computations and their limitations appear after the statement table.

## 1. Findings

1. **Major — the definition must say which bonds a status-U site keeps.**

   **Location:** `manuscript/sec6-walks.tex:104–108`, Definition `d:pattern` (6.6), read with `sec6-walks.tex:10–16`, Definition `d:domain`; consequently `app-local.tex:18–26`, Lemma `l:Iw`, and `sec8-computer-assisted.tex:52–56`, Theorem `t:H1`.

   **Claim:** The stated rules define the family represented by the 7,962 records, and in that family “the site y has status U and keeps all its bonds other than {y,s}.”

   **Problem:** Definition 6.1 permits a general status-U site to have a chosen kept set. It requires U sites to keep every bond only in the separately defined class `D_cons(G)`. Definition 6.6 refers to Definition 6.1 and explicitly specifies the kept sets for D sites, but does not explicitly impose the corresponding all-bonds rule on U sites, or specify the other three bonds of y. The enumeration and Lemma D.1 use these additional restrictions. “As in Definition 6.1” needs to distinguish a general domain from the restrictions defining `D_cons`.

   This distinction can change (H1), not merely the number of encodings. Under the broader reading, take a turn with out-neighbour e, remove s, and give every other site status U. Let y retain its bonds to e,N,W. Let N retain only its bonds to y and its tip. Drop the two N-to-upper-corner bonds at both ends. Retain all other bonds, with bonds into removed s absent. This satisfies (C). Every corner then hangs on e or W, while N has only its tip after y is integrated out.

   Fix a unit vector d. Assign all slots in the e branch the vector −d, and all slots in the W and N branches the vector d; unused slots can be arbitrary. The exact means after pruning are

   `μ_e = −r d`, `μ_W = r d`, `μ_N = (1/5)d`, where `r = ρ_U(3/5,1/2,1/2) = 169/385`.

   Consequently, at this slot configuration,

   `Z_cur/Z_next = (1 − r²/3)/(1 + r/25) = 1040285/1131207 ≈ 0.919624 < 187/200`.

   This is an exact rational counterexample to the broader interpretation. The supplied list excludes it, because its U sites must keep all their bonds.

   **Repair:** Add to Definition 6.6: every U site other than y keeps all four lattice bonds; y keeps exactly its three bonds other than the arrival bond. Keep the stated exception that a tip bond is present precisely when its non-tip neighbour retains it. Explain that outside corner legs are filled with slots even when the original kept set omitted them. With these conventions the enumerated family and the localization argument agree. This is a local definition repair; the supplied certificate choices need no change.

2. **Minor — the bound k ≤ 11 does not hold for every unreduced representation.**

   **Location:** `manuscript/app-local.tex:62`, definitions of the two representations; `app-local.tex:282`, computational subsection `s:localcomp`.

   **Claim:** “In the representations of §D.1, the number of vectors is k ≤ 11.”

   **Counterexample:** Record `pid = 113` in `programs/data/pext/pext7962.json` has all four tip bonds and all four corners incident to present bonds. Its unreduced representation has four tip vectors and eight corner-slot vectors, hence k = 12. The maximum unreduced dimension over the list is 12; the maximum reduced dimension is 11. The production program explicitly skips unreduced choices with more than eleven vectors (`run_prod.py:76–80`).

   **Repair:** Say that the reduced representation always has k ≤ 11 and that every representation actually selected in the two certificate files has k ≤ 11. The operator-only file uses the unreduced representation only at IDs 3596 and 7725, both with k = 11. This correction does not affect the matrix-size claim or the certificates.

3. **Major — exact values for individual patterns do not establish the asserted global “tightest” ranking.**

   **Location:** `manuscript/sec8-computer-assisted.tex:66–73`, Table `tab:H1`; `app-local.tex:270–274`; `app-constants.tex:17`.

   **Claim:** The displayed patterns are the tightest straight and turning patterns of the entire class, and their exact values are the minima over the respective classes.

   **Missing argument:** Proposition D.9 and the exact rational tests establish the three displayed values for the specified individual patterns. The main files certify all other patterns only at 961/1000 or 187/200, which are strictly below the asserted optimal constants. Their stored `float_bound` and numerical minima do not prove inequalities at the stronger constants. An exact certificate at 0.961 does not exclude another straight pattern with c(π) strictly between 0.961 and 3825127/3979368. The same issue applies to turns. The reported second implementation is described as checking the H1 thresholds, not these stronger global thresholds.

   **Repair:** Describe these as the smallest values found numerically, retaining the proved exact values for the named patterns. Alternatively provide exact lower-bound certificates at the claimed global minima for all other patterns. Some inversion matrices can be singular at such a threshold, so that additional check may require positive semidefiniteness rather than the strict positive definiteness used for (H1). The upper-bound assertion in Remark 8.4 remains valid without a global ranking: its single explicit pattern suffices.

4. **Major, reproducibility — several claimed independent validations are not supplied in this bundle.**

   **Location:** `manuscript/app-local.tex:282`, `292–300`, subsection `s:localcomp`.

   **Claims:** A second enumeration giving 106,101 configurations; an all-template evaluator at three random points of every pattern; exact total-spin commutator and mutation checks; the second exact implementation using exchange operators, integer congruence and strict diagonal dominance; and comparison of Bareiss elimination with exact LDLᵀ on 600 matrices.

   **Mismatch:** I could not locate the programs for the second enumeration, total-spin/mutation checks, or the exchange-operator/diagonal-dominance verifier in the frozen bundle. The supplied `crosscheck.py:13–23` uses one random point per pattern per model and compares ratios. `xcheck57.py:31–55` uses one random point and ties each tip's three slot vectors; this does not reproduce the stated three-point full-slot comparison. The supplied `test_bareiss.py:27–38` checks 400 matrices against exact determinants/Sylvester's criterion, not 600 against LDLᵀ. I ran that supplied 400-matrix test successfully.

   The independent enumeration made for this review does recover precisely the supplied 7,962 effective classes. Its raw counts depend on whether outside kept-leg choices and reflection are identified; the manuscript does not specify enough about the second enumeration to identify its 106,101 intermediate objects. Thus that intermediate count should not be treated as independently reproduced here.

   **Repair:** Include the claimed independent programs, their invocation, and their output, or revise the validation description to match the archived evidence. Distinguish the mathematical certificate proof from these additional checks. My own replay, described below, supplies additional exact verification, but uses Lemma D.6 and does not reproduce the claimed all-sector exchange-operator implementation.

5. **Minor — floating-point arithmetic also enters the verification's overflow guards.**

   **Location:** `manuscript/app-local.tex:284–286`, `300`; `programs/h1-local/code/cert.py:45–65`, `76–82`, `162–175`.

   **Claim:** “Floating-point arithmetic is used only for this choice,” referring to the search for an inversion set; overflow is excluded by run-time assertions.

   **Mismatch:** `itensordot` first casts the nonnegative integer inputs to binary64, computes a floating shadow contraction, and compares it with 2^61 before performing the int64 contraction. The check forming the current/next coefficient tensors also uses floating shadows. The comment “relative error ~1e-13” is not an explicit arithmetic bound. The small exact moment tensors are also initially stored in floating arrays, although their entries are small exactly representable integers.

   The large separation between the shadow limit 2^61 and the int64 overflow limit 2^63 is sufficient to make these guards conservative under the usual binary64 error bounds: each contracted output sums at most sixteen nonnegative products. However, this arithmetic fact belongs in the trust argument. A rounded shadow is not literally an exact comparison of an integer entry with 2^61.

   **Repair:** State that positivity is tested in unbounded integer arithmetic, while binary64 is used for search and conservative overflow guards. Give the short error bound for these nonnegative contractions, or replace the guards by exact integer bounds/checked arithmetic. Update `cert.py:4–7`, whose header still describes the former floating-integer tensor implementation. The exact operator replay for this review uses Python integers throughout and avoids this issue.

6. **Minor — the angle parametrization needs a zero-radius convention.**

   **Location:** `manuscript/app-local.tex:263`, proof of Proposition `p:closed` (D.9).

   **Claim:** Set t to the cosine of the angle between μ_f and μ_g; every t in [−1,1] occurs.

   **Problem:** The vectors can be zero, in particular when a root is removed. The third displayed example has ρ_N = 0. An angle with that vector is undefined.

   **Repair:** First write `μ_x = ρ_x d_x` with arbitrary unit d_x when ρ_x = 0, and put t = d_f·d_g; or split off a = ρ_fρ_g = 0. In that case the expression in `e:closed` is independent of t, so the formula and the rational test remain correct. This is a proof-notation correction, not a defect in `closed_exact.py`.

7. **Minor — the stated largest matrix reflects an older combined-sector convention.**

   **Location:** `manuscript/sec8-computer-assisted.tex:73`, caption of `tab:H1`; `app-local.tex:188–190`, `290`; `programs/h1-local/code/cert.py:333–348`, `434–445`.

   **Claim:** “The largest of these matrices has size 245 × 245.”

   **Mismatch:** The current code splits diluted-corner exchange signs before testing. The largest resulting central exchange block among all selected certificates is 179 (for example ID 711), as confirmed by the full replay. The stored 245-dimensional diagnostic at ID 3596 combines four exchange blocks of dimensions 131,48,48,18. There are 141 records with this older combined-sector diagnostic convention. The current checker re-derives the blocks and ignores that stored field, so their positivity tests are valid.

   **Repair:** Describe 245 as a valid historical upper bound, or update the largest-block assertion to 179 for the supplied split-sector checker and explain the older diagnostics. All statements using the upper bound “at most 245” remain true.

## 2. Statement table

“After fix” below refers to the explicit pattern convention in Finding 1 unless another finding is specified. Results elsewhere in the paper are listed as dependencies, not certified beyond the requested lane.

| Number / label | Content | Verdict | Dependencies |
|---|---|---|---|
| 6.6 `d:pattern` | Template, slots, current/next integrals, c(π), and P_ext | correct after fix | `d:domain`; explicit U kept sets (Finding 1); positive normalizers from `l:Iw` |
| 6.7 `h:H1` | Uniform straight/turn lower bounds for c(π) | correct after fix | `d:pattern`, `t:H1`; this is the hypothesis's formulation |
| 6.8 `l:local` | The localized pattern lower bound implies 1/ρ_j^τ ≥ c(π) | correct after fix | `e:IJ`, `l:35`, multiaffinity, positive denominators, tip-field covering |
| 6.9 unlabelled remark, `sec6-walks.tex:129` | Applicability of the pattern bound in the recursion, with up to twelve exceptional steps | correct after fix | `l:local`, `l:closure`, `l:response`, and the stopped-trail argument in `t:rec` |
| 8.1 `t:inputs`, H1 component only | H1 holds at (0.961,0.935) | correct after fix | `t:H1`; H2/H3 components lie outside this audit |
| 8.3 `t:H1` | Z_cur ≥ (961/1000)Z_next or (187/200)Z_next for all twenty slot vectors | correct after fix | finite-family coverage, `p:certificate`, exact operator certificates; alternatively `p:closed` on the decoupled subclass |
| 8.4 `r:H1sharp` | The explicit turn prevents c_t > 416114/444675 | correct after fix | `p:closed`, `e:5469`; global optimality is unnecessary |
| D.1 `l:Iw` | Integrate y to obtain I,J; normalizer positivity, multiaffinity and O(3) invariance | correct after fix | corrected `d:pattern`, `e:moments`, `e:IJ`; full support of the uniform part of each site measure |
| D.2 `l:leaf` | Positive isolated factors; tip radius 3/5; U/D leaf-corner radii 1/2,1/3 | correct | `e:moments`, `l:35`; tips are U; slot vectors are unit |
| D.3 `c:reduce` | Nonnegativity of either reduced polynomial on spheres implies the original inequality | correct | `l:leaf`; no two tips/corners adjacent; separate affinity; positive common factor K |
| D.4 `l:inversion` | Pauli coherent-state expectation identity and the PSD sufficient condition | correct | `e:zeta`, Pauli trace identities, tensor-product expectations, ball convexity |
| D.5 `l:Ostruct` | Reality, SU(2) invariance, U-pair symmetric support, D-pair exchange symmetry | correct | O(3) invariance; SU(2) adjoint action; `e:zeta`; U-corner measure supported on the sphere |
| D.6 `l:sector` | Every eigenvalue occurs in the central spin-component sector | correct | finite-dimensional SU(2) complete reducibility and spin-j weights; “same eigenvalues” means the same set, not multiplicities |
| D.7 `p:certificate` | Positive definiteness on each central exchange sector suffices for F_c ≥ 0 | correct | `l:Ostruct`, `l:sector`, `l:inversion`, `c:reduce`; orthogonal decomposition of V |
| D.8 `l:radius` | Sharp U/D mean bound for three fields of prescribed radii | correct | moments; `l:35`; D.2 for two fields; finite-lattice FKG; continuity at radius endpoints |
| D.9 `p:closed` | Exact scalar minimum and its rational quadratic nonnegativity test | correct after fix | `l:Iw`, `l:radius`, tree pruning, branch independence, multiaffinity; Findings 1 and 6 |

Ancillary claims: the individual fractions in Table 8 are correct for IDs 7645, 1382 and 5469; their asserted ranking over the entire class is **unproved** by the supplied exact certificates (Finding 3). The general unreduced dimension bound is **false** (Finding 2). The archived independent-check claims are only partially reproducible (Finding 4).

### Computations performed for this review

The review artifacts are in this directory. They read the bundle without changing it; Python bytecode writes were disabled.

- `audit_stdlib.py` independently enumerates the intended status/kept-set rules, canonically reflects straight patterns, represents turns with o = e, and deletes isolated-site data. The resulting 7,962 keys agree exactly with the frozen list, with no missing or extra key: 2,696 straight and 5,266 turns. This verifies the effective family without relying on numerical minima in the data.
- It checks both cited certificate files for exactly one occurrence of every ID, the correct type-derived threshold, model `covered`, tip radius 3/5, valid inversion indices and whole-pair inversions, and the selected dimensions. All pass. Stored `sectors` diagnostics in 141 records use an older combined central-sector convention; the sum of their dimensions agrees. The current checker ignores those diagnostics and re-derives the split, as it should.
- It prunes the actual graph with all pendant tips present, uses `Fraction` arithmetic for the messages, and checks the linear/quadratic criterion independently. All 4,735 decoupled patterns pass at the H1 thresholds: 1,553 straight and 3,182 turns. Stored radii agree exactly. For the three named patterns it also checks the criterion at the quoted rational value and an exact attaining configuration, proving equality; the criterion fails at that value plus 10^−12.
- The three exact values are `3825127/3979368` at ID 7645, `1071655/1145463` at ID 1382, and `416114/444675` at ID 5469. Their root radii agree with `app-local.tex:272–274`.
- The supplied Bareiss function was extracted without importing its NumPy-dependent module, and the supplied 400-matrix exact determinant comparison was executed. It gives 235 positive definite and 165 non-positive-definite cases, with all verdicts agreeing. See `bareiss_checks.log`.
- `audit_operator_stdlib.py` reconstructs the selected operators using sparse exact site-moment factors, variable elimination on the ring, a Walsh transform for the Pauli action, integer congruence into the pair basis, and fraction-free elimination with an explicit divisibility check at every division. It imports neither the production coefficient builder nor its matrix builder. It checks the total-Sz block structure before restricting to the central sector, and tests every diluted-pair exchange choice. It relies on the proved Lemma D.6 for the reduction to that sector.

The production `verify_all.py` could not be executed in the provided Python 3.12 environment because NumPy is absent; the failed invocation is recorded in `operator_verify.log`. `audit_verify.py` shows the minimal relocation of `ring.P63` needed to run it when its dependencies are installed. The bundle README already explains the obsolete absolute paths. No package installation or outside-file search was performed.

The complete independent operator replay **passed all 7,962 certificates**, testing **12,173 central exchange blocks** with exact divisions and positive pivots. Its three logs are `operator_all_0.log`, `operator_all_1.log`, and `operator_all_2.log`. Each worker completed 2,654 certificates with exit status zero; their ID union is exactly 0,…,7961, with no duplication. The largest tested block is 179 (Finding 7). The 3,227 operator choices in the mixed file agree with the corresponding operator-only choices, so these results together with the 4,735 rational checks also verify every record in that file. `audit_summary.json` records the coverage, completion lines and hashes of the replay artifacts.

The three workers used at most three cores and each finished within fourteen minutes. The sample log includes both unreduced choices, the two generic eleven-vector patterns, a zero-vector case, and the displayed extremal examples. Floating numerical values quoted from the manuscript remain numerical evidence; the enumeration, radius tests, matrix construction and positivity checks above use integers or rational numbers.

## 3. Formalization notes

1. **Encode the family before proving inequalities.** A status and a kept set are different data. Specify U's kept set, y's arrival exception, D's exactly-two kept bonds, and (C) independently of the rule defining a present bond. A kept bond into an X site need not be present. Outside corner kept-leg choices do not alter the two artificial slot factors of the covered model. The `refined` model in the programs is a different slot model and must not silently replace `covered` in the H1 theorem.

   A useful formal organization is a finite type of canonical encodings together with a coverage theorem for every intended pattern, up to reflection, slot relabelling and positive cancellable factors. There is no need to define a quotient by full extensional equality of ratios. The programs implement particular syntactic identifications; “duplicates” should specify those identifications. Distinct encodings can still have the same constant ratio.

2. **Use the actual spin space and measures.** A U spin lies on S²; a D spin lies on `S² ∪ {0}` with measure `(3/5)λ_U + (2/5)δ_0`; an X site has no variable. The convention in the introduction that all spins are unit vectors has this later exception. Prove O(3) invariance for both measures. The required moments have total degree at most four: zeroth moment 1, odd moments zero, second moment δ/3, fourth moment the sum of three pairings divided by 15; positive-degree D moments are 3/5 times the U moments. Thus the denominators 15 and 25 used in the integer scaling argument are sufficient. An isolated factor of a D site has its atom contribution as well.

3. **Normalizers and continuity are genuine hypotheses.** Every bond/slot factor is nonnegative on the relevant balls. Choose a sphere direction opposite to none of the finitely many slots; all non-removed spins equal to that direction give a strictly positive integrand on a product neighbourhood. Each site measure has a positive uniform component, so every normalizer in D.1 is strictly positive. Compactness and continuity then give a positive minimum for Z_next over the slot configuration space. This justifies ratios, infima attained as minima, linear-fractional arguments, and continuity of the normalized means.

4. **Separate affinity needs an explicit convexity lemma.** For a polynomial affine in each vector, its value at a product of balls is a convex combination of its values at a product of spheres. Each nonzero vector b in the unit ball is the convex combination of ±b/|b| with weights `(1±|b|)/2`; for b = 0 choose any direction. Apply this one coordinate at a time. For ratios, apply the lemma to numerator minus c times the positive denominator, or use the denominator-weighted average formula. This proves D.3 and the ball steps of D.4/D.9 without differentiability or an optimization algorithm.

5. **The leaf replacement is a positive common-factor identity.** For each original slot configuration construct K > 0 and replacement vectors of norm ≤ 1, common to current and next functions. The replaced sites are pairwise nonadjacent and none is incident to y, so their integrations commute with I,J and with each other. The tip bound uses the U three-field lemma; the D leaf-corner bound uses its atom, giving 1/3 rather than 1/2. These are bounds on normalized vector fields, not bounds on an unnormalized numerator.

   For Lemma 6.8, justify that the U tip with three independent unit slots realizes every vector of norm ≤ 3/5. Aligned slots give norm 3/5; three coplanar directions separated by 120 degrees give mean zero. A continuous path between them and rotational covariance give every intermediate norm and direction. Absent exterior bonds and correlated exterior spins can therefore be covered by independent slots. Replacing an absent factor by the average of two opposite slot factors also uses positive denominators.

6. **The operator map uses coefficients on all of `(R³)^k`.** The multi-affine expansion is unique in that ambient polynomial space. Pauli expectation identities hold pointwise on spheres; a globally continuous choice of the phases of ζ is unnecessary. Reality uses the coordinate reflection reversing all second coordinates, hence O(3) invariance. SO(3) invariance supplies SU(2) covariance. A union-of-groups inversion is needed for the support/exchange assertions for pairs; arbitrary independent inversions would not justify D.5(3).

7. **The U-pair kernel must be retained.** The operator is positive definite on V after certification and is zero on V-perpendicular when there are U pairs. On the full Hilbert space the conclusion is positive semidefiniteness. For D pairs retain both symmetric and antisymmetric factors. Their δ_0 contribution prevents the U-pair support argument from applying to them. The counts 4,992 patterns without a U pair and 2,970 with one agree with the actual selected representations.

8. **Central-sector reduction is a spectral-set assertion.** Differentiating the one-parameter SU(2) action gives commutation with Σ_3. Each nonzero eigenspace of the Hermitian operator is a finite-dimensional SU(2) representation and decomposes into spins j. Its weights are j,j−1,…,−j. The parity of the number of single factors forces j integral or half-integral, and hence gives a vector of weight 0 or 1/2 in every such eigenspace. Multiplicities usually change on restriction. A formal statement equating characteristic polynomials or spectra with multiplicity would be false; equality of spectral sets or equivalence of positive definiteness is the appropriate statement.

9. **Matrix entries are quadratic-form matrices in an unnormalized basis.** The middle triplet vector and the singlet have squared norm 2, with corresponding product norms for several pairs. The integer matrix is `B* O B`, a congruence matrix; the coordinate matrix of the operator is instead `Gram(B)⁻¹(B* O B)`. Sylvester's criterion applies to the congruence matrix. Choose p,q with q > 0 and D > 0 in `e:intscale` and `e:Meps`; the sign of the factor 15Dq matters. Coprimality is unnecessary. For Bareiss, prove the minor identity, previous-pivot nonzeroness, and exact divisibility. The checker stops before division when a pivot is nonpositive.

10. **FKG applies to a finite eight-point lattice.** For interior radii all weights `w_T Z^parallel_|T|` are strictly positive. Rank log-convexity follows from the ratios 1,4/3,3/2 and implies the lattice condition for union and intersection. The inclusion-monotonicity proof for L_T uses t ∈ [−1,1] and 3+t > 0 when squaring the displayed inequality. Apply FKG to the increasing function ρ_|T| and to −L_T to obtain the required reverse covariance sign. Both E[L_T] and all Z_T are positive. For D, X/Y and X′/Y′ are nonnegative; this justifies multiplying their inequality by the increasing nonnegative factor Y/(Y+2/3). The case e·V ≤ 0 is immediate. Extend from interior to endpoint radii by continuity on the feasible field balls; no division by r_j is allowed when r_j = 0.

11. **Pruning requires an order, a field-count invariant and attainability.** A vertex attached to a parent has at most three incoming slot/child fields, because its parent occupies one lattice neighbour. Do not assign a parent-message radius to an isolated vertex with four incident child/slot contributions; integrate it as a positive constant. Protected roots have at most three fields because y occupies their fourth neighbour. The radii lie in [0,1], and their rationality is preserved recursively.

   After pruning, any remaining unprotected isolated vertices can also be integrated. Each root has a disjoint pendant tree, so aligning every slot in that tree along d_x attains the full radius ρ_x simultaneously for all roots. Removed roots are assigned zero means. This attainability step is what upgrades a lower bound to the exact infimum in D.9.

   `closed_exact.py:34–42` first drops entire components that have no y-neighbour, whereas the text prunes all vertices. This is valid here: such a component contributes a positive common factor and is a forest. The only cycle possible in the ring-plus-tips graph is the full eight-site ring, which contains the non-removed out-neighbour. Thus an unattached component cannot contain that cycle. This graph fact is an additional Lean node connecting the code's pruning to the stated definition.

12. **The scalar test includes its degeneracies.** The denominator `1 + at/5` is strictly positive since 0 ≤ a ≤ 1. The square-root argument is at least `(ρ_f−ρ_g)²`. Nonnegativity of the affine L follows from its two endpoint values, and only then is squaring reversible. If the quadratic coefficient is zero, Q is affine/constant and endpoints suffice; otherwise test its vertex only when it lies strictly inside the interval. The code handles a = 0, zero root radii, zero leading coefficient, and vertex-at-endpoint cases correctly. Finding 6 concerns only the proof's angle notation.

13. **Turn executable data into a closed finite proposition.** A formal certificate importer should check the complete ID range, uniqueness, the type-derived rational threshold, representation mode, tip radius, valid slot indices and pair inversions, and every exchange sector. `verify_all.py` deliberately checks individual supplied records; it does not enforce coverage, derive the threshold from the pattern, validate the stored tip-radius field, or return a failing exit status merely because its `bad` list is nonempty. The manuscript acknowledges the separate coverage check, and the frozen files satisfy the needed conditions. Include those conditions in the imported theorem rather than interpreting a process exit code as its proof. Historical `sectors` diagnostics are not certificate inputs.

   The coefficient contraction uses nonnegative tensors, so bounds on the exact final contraction bound its partial sums. In the production implementation one must also account for binary64 shadow error, int64 intermediate sums, signed Pauli conversion, the fallback to Python integers, and the use of assertions. Running with `python -O`, using a different tip radius, or treating a refined certificate as a covered certificate changes the trusted computation. A Lean implementation using unbounded integers can avoid these machine-range obligations altogether.

## 4. External inputs

No external manuscript or article was fetched. The following are the exact external or standard mathematical facts consumed in this lane. “Locator” reports what the paper supplies; a bibliography-wide citation does not identify a theorem number.

| Input, exactly as used | Locator supplied by the manuscript | Hypothesis check / limitation |
|---|---|---|
| **Finite-lattice FKG:** On a finite distributive lattice, a strictly positive probability mass π satisfying `π(x∨y)π(x∧y) ≥ π(x)π(y)` has `E[fg] ≥ E[f]E[g]` for increasing real f,g. Consequently an increasing f and decreasing h have nonpositive covariance. | `app-local.tex:225`, citation `[FKG71]`; bibliography `main.tex:84–87`, CMP **22** (1971), 89–103. No theorem/page locator within the article. | Applied to the Boolean lattice of subsets of {1,2,3}. Interior radii give positivity; the rank factors 1,1,4/3,2 are log-convex; f = ρ_|T| increases and h = L_T decreases. All conditions hold. Endpoint radii are obtained by continuity. |
| **Bareiss/Sylvester minor identity:** Fraction-free elimination without pivot exchanges computes the leading principal minors as pivots; an update divides `(pivot·entry − cross-product)` by the previous leading minor, exactly when that minor is nonzero. | `app-local.tex:192`, citation `[Bar68]`; bibliography `main.tex:74–77`, Math. Comp. **22** (1968), 565–578. No algorithm/theorem locator. | The matrices are symmetric integers. The loop continues only through positive pivots, so the previous divisor is nonzero. Python integers avoid arithmetic overflow in elimination. The original code uses `//`; exact divisibility follows from the identity. My replay checks remainders as well. |
| **Sylvester's criterion:** A real symmetric finite matrix is positive definite iff all leading principal minors are strictly positive. | Named at `app-local.tex:192`; no separate citation. | Applied to `5q A_ε − 3p A′_ε`, in a congruence basis and with q,D positive. These hypotheses are satisfied. |
| **SU(2) adjoint/rotation correspondence:** For U ∈ SU(2), conjugation of the Pauli triple is an SO(3) rotation: `Uσ_jU* = Σ_l R_ljσ_l`. | Displayed in `app-local.tex:129–141`; also used in `sec2-frames-Q.tex:15`. No external citation. | The Pauli convention and column indices match the displayed substitution by Rᵀ. Simultaneous rotation invariance is proved from the site measures and scalar products. |
| **Finite-dimensional SU(2) representation theory:** Every finite-dimensional unitary representation decomposes into irreducible spins j ∈ {0,1/2,1,…}; a spin-j representation has component weights j,j−1,…,−j. | Used without a source at `app-local.tex:165`. | The tensor factors C², Sym²C² and wedge²C² are invariant unitary representations. Every eigenspace of the commuting Hermitian operator is invariant. The parity argument supplies the chosen central weight. No irreducibility or multiplicity-one assumption on V′ is required. |
| **Pauli/Bloch coherent-state identity:** For b ∈ S², `(I+b·σ)/2` is a rank-one orthogonal projection, and a unit vector spanning it has expectations `〈ζ(b),σ_jζ(b)〉=b_j`. | `sec2-frames-Q.tex:7–10`, equation `e:zeta`; used at `app-local.tex:101–107`, `151–153`. No separate source. | b is unit whenever rank one is used. For D sites the atom is treated separately and contributes identity; it is not assigned a unit coherent state at zero. |
| **Sphere moments / Gaussian pairing formula:** Uniform S² moments of positive even degree are the sum of Kronecker-delta pairings divided by `3·5·…·(2k+1)`; odd moments vanish. Only degrees 0,2,4 are needed for the local integrations. | Internal equation `e:moments`, `sec5-cut.tex:13–17`, derived there from the Gaussian pairing formula and Gaussian radius moments. The Gaussian formula is folklore with no external citation. | Integrands have degree at most four at each retained spin, including a possible correlation insertion. D moments are 3/5 times the positive-degree U moments. The coefficient construction and the analytic computations use the same normalization. |
| **Finite-dimensional spectral and congruence facts:** Hermitian eigenspaces decompose orthogonally; invariant blocks are positive definite iff each block is; invertible congruence preserves positive definiteness; an operator supported on V and positive on V is PSD on the full space. | Used in `app-local.tex:165`, `168–192`, without external locators. | All spaces are finite-dimensional; the pair basis is linearly independent but not orthonormal. The distinction between restriction and congruence is respected in `e:Meps`. |
| **Integration/convexity facts:** Fubini for bounded functions under finite product probability measures; linear maps commute with these finite coefficient integrals; a separately affine function on balls is a convex combination of its sphere values; continuous positive denominators permit the ratio and endpoint arguments. | Used throughout D.1–D.9 and in Lemma 6.8, generally without citations. | The spin spaces are compact, the integrands are polynomials, and normalizers are strictly positive. The zero-vector and zero-radius choices described above are needed for literal formal statements. |
| **Strict diagonal dominance sufficient condition:** A real symmetric matrix with each diagonal entry strictly larger than the sum of absolute off-diagonal entries in its row is positive definite; an invertible integer congruence can transfer that conclusion. | Claimed as the second implementation's method at `app-local.tex:298`; no citation or implementation locator. | The mathematical fact is standard. The hypotheses for the claimed second implementation cannot be inspected because its code and output are not supplied (Finding 4). It is not needed for the primary certificate argument or my replay. |

Lemma `l:35`, which supplies the three-unit-field estimate in D.2 and D.8, is an internal proved input rather than an external citation. Its hypotheses are exactly three unit vectors under the normalized uniform sphere measure. The identity at `sec5-cut.tex:28–32` has the stated constants and a nonnegative right-hand side, and the extension to fewer factors is a positive-mixture argument. No assumption of independence of the three field directions is required.
