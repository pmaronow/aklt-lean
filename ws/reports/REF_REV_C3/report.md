VERDICT: SOUND

Reviewed input: `part/app-local-operator.tex`, lines 1–896, relative to `/home/ubuntu/aklt/review/REF_REV_C3/`, together with the relevant definitions and available results in `interfaces.tex`. No background manuscript material was needed. The verdict concerns this part's conditional certificate theorem; this part does not claim to supply certificates for all patterns or prove unconditional (H1).

**Findings**

No Critical, Major, or Minor findings. No mathematical repair is required.

**Statement table**

All locations below refer to `part/app-local-operator.tex` unless prefixed by `interfaces.tex`. “Sound” for a definition includes well-posedness and consistency with its subsequent use. All twelve labelled statement bodies agree exactly with their exports in `interfaces.tex`, after whitespace normalization.

| Label and location | Content | Verdict | Dependencies |
| --- | --- | --- | --- |
| `l:Iw`, line 22 | Passage integration gives the stated `I`, `J`, and `I-cJ`; `Z_next>0`; partition polynomials are separately affine and orthogonally invariant. | Sound | Interface `d:pattern` (396), `d:moment` (51), `l:moments` (74), `l:finitefacts` (119). |
| `l:leaf`, line 87 | Positive leaf normalizers; tip radius `3/5`; one-bond corner radii `1/2` and `1/3`. | Sound | Interface `d:pattern`, `l:moments`, `l:35` (133). |
| `d:reduction`, line 146 | The two representations, remaining vectors, radii, and vector groups. | Sound | `l:leaf`; passage representation from `l:Iw`; explicit polynomial extension at lines 160–168. |
| `c:reduce`, line 170 | Reality, separate affineness, orthogonal invariance, common positive factor, and passage from spheres to balls. | Sound | `d:reduction`, `l:leaf`, `l:Iw`, interface `l:moments`; finite convex expansion. |
| `d:Pauli`, line 246 | Unique coordinate-monomial expansion, Pauli map, inversion, densities, and total spin operators. | Sound | Explicit Pauli matrices and identities at lines 234–244; separate affineness. |
| `l:inversion`, line 269 | Product-density trace identity; positivity of one inverted operator implies polynomial nonnegativity on the balls. | Sound | `d:Pauli`; finite-dimensional Hermitian spectral theorem and tensor trace identities. |
| `l:Ostruct`, line 318 | Reality, symmetry, total spin commutation, symmetric support at U-pairs, and exchange commutation at D-pairs. | Sound | `c:reduce`, `d:Pauli`, `l:inversion`; unit support of the U law; groupwise inversion. |
| `d:exchange`, line 416 | Supported space, orthogonal exchange sectors, parity-dependent central weight, and integer-coordinate bases. | Sound | `l:Ostruct`; explicit pair bases and spin actions at lines 432–468. |
| `l:sector`, line 470 | Central-weight restriction has exactly the same eigenvalue set; positive definiteness is equivalent. | Sound | Sector weights, adjoint relations, and commutators at lines 442–468; finite-dimensional Hermitian spectral theorem. |
| `l:gram-residual`, line 525 | Strict row dominance of the integer residual proves positive definiteness of the residual and original matrix. | Sound | Symmetry, positivity of `g,d,S`, and `2ab ≤ a²+b²`; no invertibility assumption on `L`. |
| `l:integercheck`, line 580 | Exact rational reconstruction and denominator; symmetric integer form matrices; positive scaling; optional principal-minor/Bareiss test. | Sound | `l:Iw`, `d:reduction`, `c:reduce`, interface `l:moments`, `d:Pauli`, `d:exchange`, and the reality argument of `l:Ostruct`; determinant identities proved locally. |
| `p:certificate`, line 828 | Residual witnesses on every supported central exchange sector imply the original twenty-slot inequality. | Sound | `l:gram-residual`, `l:integercheck`, `l:Ostruct`, `l:sector`, `l:inversion`, `c:reduce`. |

The unlabelled Pauli identities, tensor-map properties, sector orthogonality, basis norms, and ladder identities used between these statements also check out. None of the part's own exported interface statements was assumed as an external theorem in assessing its proof.

**Proof and hypothesis audit**

1. **Passage deletion and positivity — lines 40–84, `l:Iw`.** The passage is U, has no slots, and has precisely the non-arrival bonds specified by interface `d:pattern`. It is therefore integrated using moments through degree three. In the next template its law is D and its out-bond is absent. Assigning zero to a removed neighbour is only an expansion convention: no removed-site law is introduced. This gives exactly
   \[
   I=1+\frac{P_{fg}+P_{fo}+P_{go}}3,
   \qquad J=1+\frac{P_{fg}}5.
   \]
   The remaining network meets every hypothesis of interface `l:finitefacts`: finite U/D site laws, distinct-endpoint bonds, unit slot pins, and at most four incident factors. All weights are nonnegative, and all remaining spins have norm at most one. Hence `J ≥ 4/5`, including removed-endpoint cases, and `Z_next ≥ (4/5) Z_w[1] > 0`. No normalization by a potentially zero quantity occurs.

2. **Leaf normalizers and common reduction — lines 99–229, `l:leaf` and `c:reduce`.** The tip normalizer is at least `1/2`, so interface `l:35` applies to a well-defined normalized U law with three unit factors. Its radius `3/5` is used with the correct normalization. For a corner, writing `t=a·b`, the formulas are
   \[
   (A,V)=\left(1+\frac t3,\frac{a+b}3\right)
   \quad\text{or}\quad
   \left(1+\frac t5,\frac{a+b}5\right).
   \]
   The two squared-norm differences are exactly `(1-t)²/9` and `(1-t)(7-t)/25`. They are nonnegative throughout `-1 ≤ t ≤ 1`; their positive normalizers justify division. Tips and corners are mutually nonadjacent in the template, and none is the passage. Consequently the same leaf integrations give the same positive `K` and replacement vectors in both partition functions. The two-point decomposition of each ball vector is valid also at zero, with nonnegative weights summing to one. Its finite product proves the asserted implication without any realizability assumption on replacement vectors.

3. **Degree bounds and covariance — lines 72–84 and 185–198.** In the original templates, a tip has three slots and at most one bond; a corner has two slots and at most two internal bonds; each non-arrival neighbour has at most four bonds. After passage deletion, an endpoint of a nonzero pair insertion has at most three remaining factors, and the insertion adds one. The arrival is not an insertion endpoint. A replacement leaf factor substitutes for one bond and does not increase the surviving endpoint's degree. Thus every relevant spin polynomial has separate degree at most four, exactly as required by interface `l:moments`. The argument never assumes rotational invariance of the finite laws on arbitrary functions. This also establishes covariance for arbitrary real values of the remaining vector variables.

4. **Pauli trace and support — lines 234–412, `d:Pauli`, `l:inversion`, and `l:Ostruct`.** Coordinate labels `u_i^j` are used consistently as coordinates rather than powers. The density eigenvalues are `(1±|a|)/2`; tensor trace multiplicativity gives the claimed identity, and positivity of the trace of the product of two positive semidefinite matrices is correctly proved without assuming the matrices commute. Reflection of the second coordinate negates precisely the Pauli words with an odd number of `sigma_2` factors, proving reality. The transpose in `G(R^T u)` is correct. The polynomial family `U_j(t)` lies in SU(2), and coefficient comparison yields the three total spin commutators. Groupwise inversion gives the same sign on both slots of a retained pair. For U, its local tensor square has symmetric range; for D, including the atom at zero, it commutes with exchange. No positivity of the other summand factors is needed.

5. **Exchange and central weight — lines 432–521, `d:exchange` and `l:sector`.** The pair basis is orthogonal with squared norms `1,2,1,2`; its tensor products have integer coordinates and norms that are powers of two. The displayed ladder coefficients agree with the unnormalized basis. Pair weights are integral, so the parity of the singles gives exactly `kappa=0` or `1/2`. For a weight vector, the norm difference is `2m ||v||²`, with the stated sign. When lowering toward `kappa`, every intermediate weight is positive; when raising, every intermediate weight is negative, including the final starting weight `-1/2` in the odd case. Thus no required step vanishes. The argument proves equality of eigenvalue sets, and does not incorrectly assert equality of multiplicities.

6. **Integer reconstruction and scaling — lines 609–764, `l:integercheck`.** All surviving nonremoved passage neighbours remain in `X`. Each term in the coefficient formula uses a radius at most once, one local moment per site, and at most one passage insertion. U moments have denominators dividing `15`, and D moments have denominators dividing `25`, including their zeroth moments. Accordingly
   \[
   D_0=15^{N_{\mathrm U}}25^{N_{\mathrm D}}\prod_i\beta_i
   \]
   clears the claimed scaled coefficients. The insertion denominators are correctly accounted for by the extra `3` or `5`. Gaussian integer Pauli entries become real integers by the proved reflection symmetry. The matrices are form matrices `B_epsilon^* P B_epsilon`, so no division by the nonunit basis norms is missing. The decisive identity is exactly
   \[
   5qA_\epsilon-3pA'_\epsilon
   =15D_0q\,B_\epsilon^*
      \mathcal O(\widehat F_c^{\mathcal I})B_\epsilon.
   \]
   The scale is strictly positive; `p/q` need not be in lowest terms.

7. **Positivity checks and assembly — lines 545–577, 766–825, and 851–894.** The complex quadratic-form estimate for a strictly dominant real symmetric residual is valid. The Gram term is `||L^T z||²` because `L` is real; it requires no rank assumption. The optional determinant test proves both directions of Sylvester's criterion. Its fraction-free invariant is the stated bordered minor, and its denominator is the preceding leading minor, assumed nonzero. A zero pivot cannot be accepted. In the main theorem the single strict row inequality already implies positive diagonal entries. The operator is supported on `V`, preserves each D-exchange sector, and commutes with the restricted ladder operators. Central-sector positive definiteness therefore promotes to each whole supported sector. Orthogonality and zero action on `V`'s complement give full positive semidefiniteness, which yields the claimed original inequality by the trace and leaf reductions.

8. **Boundary conventions.** Unused slots at removed sites cause no extra variable dependence. Empty products of normalizers give `K=1`. With no remaining vector variables, the tensor space is the one-dimensional space `C`, the trace identity is scalar, and the central weight is zero. Empty families of pairs have one exchange-sign assignment. The matrix lemmas also correctly handle size zero with vacuous positive definiteness. All divisions used in leaf normalization, density construction, positive scaling, and the optional recurrence have the required positivity or nonzero guards. The fixed H1 thresholds lie strictly inside this part's stipulated range `0<c<1`.

**Exact computational cross-checks**

Using one Python 3 process with exact `fractions.Fraction` arithmetic, I independently expanded the passage products from the interface moment tensors and checked both corner normalizers and mean vectors. I also compared the fraction-free recurrence and every reachable bordered-minor entry against independent determinant expansion for all `729` symmetric `3×3` matrices whose six independent entries belong to `{-1,0,1}`, stopping at zero pivots. All checks passed. These checks supplement the general arguments; they are not substitutes for them. A separate text comparison verified all twelve exported statement bodies. No input was modified.

**Formalization notes**

- Track the separate spin degree bound in each insertion term, including the inserted observable. Applying moment covariance only to the underlying bond product would be insufficient; the manuscript includes the needed stronger check.
- Define the reduced polynomial on the full real coordinate space before applying the Pauli map. Separate affineness gives monomials indexed by one constant-or-coordinate choice per vector. Moment evaluation then proves rationality and the stated denominator bound without introducing algebraic coordinates of the finite frame into reconstructed matrices.
- Keep the integer-coordinate inclusion matrix `B_epsilon` distinct from an orthonormal change of basis. The certified object is the pulled-back Hermitian form. Its positivity transfers through the injective inclusion even though `B_epsilon^* B_epsilon` is generally not the identity.
- Establish sector invariance before treating compressions as restricted operators. Use disjoint pair projections for the U support and commuting exchanges for the D decomposition. The central-weight lemma can be implemented directly with the explicit ladder identities; no general SU(2) representation decomposition is required.
- For polynomial coefficient comparison in the SU(2) argument, remove the nonzero scalar normalization before comparing the coefficient of `t`. Use the fixed complex Pauli matrices and their integer Gaussian entries to prove exact integrality and reality separately.
- The main residual checker needs only integer operations and strict comparisons. If the optional Bareiss path is implemented, use simultaneous trailing-block updates, prove exact divisibility before integer division, and reject a zero pivot. Do not apply this strict positive-definiteness test to the full operator with its discarded U-pair kernel.
- Preserve empty-index conventions explicitly: empty tensor products are `C`, their identity has trace one, a zero-dimensional matrix has no nonzero test vector, and the empty exchange-sign assignment is a single sector. These conventions agree with the manuscript throughout.
