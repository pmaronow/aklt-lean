VERDICT: SOUND WITH FIXES

Lane R1: Sections 1–2 of the frozen bundle. Locations below are relative to `bundle/manuscript/`, and line numbers refer to the LaTeX sources. I read all section and appendix sources for context. The quantum comparison, its constant, and ground-state uniqueness are sound. The findings below are local corrections; none changes Theorem 2.5 (QD). The uniform-in-volume part of Theorem 1.1 depends on results in the other lanes, as specified below; this report does not independently certify their computer-assisted inputs. No web search or sub-agents were used.

## 1. Findings

1. **Minor — an orientation sign is missing from the factorization in the QD proof.**

   **Location:** `sec2-frames-Q.tex:21`, `:99–103`, and `:110`; Theorem 2.5 (`t:QD`).

   **Exact claim:** “Write `iota B(s) = beta_x(s_x; s_{N(x)}) rho_x(s_{Lambda \setminus x})`, where `rho_x` is the product of the factors of bonds not containing `x`.” Here `beta_x` uses the outward orientations `q_{xy}`, while the factors of `B` have previously been given arbitrary fixed orientations. The equality for `iota psi` at line 110 makes the same identification.

   **Why it fails literally:** Write `q_e = epsilon_{e,x} q_{xy}` for an incident edge `e={x,y}`, where `epsilon_{e,x}` is a sign. The incident product in `B` is `c_x beta_x`, with `c_x = product_{e containing x} epsilon_{e,x}`. There is no requirement that `c_x=1`. Reversing just one incident edge changes the asserted equality's left side and leaves the stated right side unchanged. This affects an equality, not the projection or any estimate.

   **Repair:** Define

   \[
   \rho_x(s_{\Lambda\setminus\{x\}})
   =c_x\prod_{e\not\ni x}q_e(\zeta(s)),
   \]

   and absorb the same constant sign into the quotient `chi` at line 110. Alternatively, for the even-torus argument explicitly orient every bond from the even sublattice to the odd sublattice: then `c_x=1` at every vertex, because its degree is four. The signs disappear from conditional probabilities and rank-one projections, so the intertwining and the factor `g_star/2` are unchanged.

2. **Minor — the last weight bound must refer to individual interaction factors.**

   **Location:** `sec2-frames-Q.tex:137`, following (2.12), `e:muDW`.

   **Exact claim:** “All weights in (2.10) and (2.12) lie in `[1-gamma_+,1+gamma_+]` times the site weights.”

   **Why it fails if read as a bound on configuration weights or probabilities:** These expressions contain products of many interaction factors and a normalization. Even one free site can have four boundary factors. Let `W={x}` be an icosahedron site, and give its four neighbouring dodecahedron sites the same letter `b`. Choose `a` with `a·b=gamma_+`. Exact fourth-moment integration gives

   \[
   Z^\eta_{D,\{x\}}=\sum_{n\in D_{\mathrm I}}w(n)(1+n\cdot b)^4
   =\int(1+n\cdot b)^4\,dn=\frac{16}{5},
   \qquad
   \frac{\mu^\eta_{D,\{x\}}(a)}{w(a)}
   =\frac{5}{16}(1+\gamma_+)^4.
   \]

   The last ratio is approximately `3.24170435`, whereas `1+gamma_+` is approximately `1.79465447`. Thus the literal probability bound is false. The unnormalized product also does not have the asserted single-factor bound.

   **Repair:** Say: “Every internal bond factor and every boundary bond factor lies in `[1-gamma_+,1+gamma_+]`; all site weights are positive.” A product of `k` such factors lies between `(1-gamma_+)^k` and `(1+gamma_+)^k`. All uses of positivity in Sections 2 and 4 require only this corrected assertion.

3. **Minor — the design citation has no precise locator, despite the introduction's promise.**

   **Location:** `sec1-intro-statement.tex:18`; `sec2-frames-Q.tex:63`; citation `DGS77`, bibliographic entry `main.tex:79–82`.

   **Exact claims:** “Everything else is proved here or cited with a precise locator”; both specified polyhedral vertex sets “are spherical 5-designs (see [DGS77]).”

   **Issue:** The citation supplies no theorem, example, table, or page for this assertion. A numerical moment check cannot replace the exact cubature identity needed for an isometry. The design assertion itself is correct: I verified it in exact arithmetic, and the short proof below removes any dependence on identifying a statement in the external paper.

   **Repair:** Supply the exact locator or insert explicit coordinates and the moment calculation in §3 below. Also identify the standard irreducibility and Clebsch–Gordan facts listed in §4, either by citation or by a short representation-theoretic preliminaries paragraph. Their hypotheses are satisfied; their use is not a mathematical gap.

## 2. Statement table

“Correct” for the main theorem's uniform-gap clause means that the in-lane conclusion follows from the listed internal inputs; the certification of those inputs belongs to the other lanes. Theorem and equation numbers use separate counters.

### Numbered theorem, lemma, definition, and remark environments

| Number and label | One-line content | Verdict | Dependencies |
|---|---|---|---|
| Theorem 1.1, `t:main`, `sec1-intro-statement.tex:11–16` | Unique VBS ground state and a uniform positive quantum gap on sufficiently large even tori. | Correct, conditional on the listed later-section inputs for the uniform gap. Uniqueness already follows from Section 2 alone. | `t:inputs` → `t:rec` → `h:P` → `t:cutMOS` → `c:gapcell`, `l:boxcell`, `l:compare` → `t:K` → `t:QD`; proof assembled in `t:mainW` and `sec4-mixing-to-gap.tex:134–135`; MOS94/MO94 as described in §4. |
| Lemma 2.1, `l:edge`, `sec2-frames-Q.tex:27–33` | An edge projector annihilates a state exactly when its polynomial is divisible by `q_e`. | Correct. | `Sym^4(C^2)^*` is spin 2; `Sym^3(C^2)^*` is spin 3/2; Clebsch–Gordan; complete reducibility and multiplicity one; invariance of the determinant; injectivity of multiplication in a polynomial domain. |
| Lemma 2.2, `l:divisibility`, `:35–41` | Edge constraints touching `R` imply divisibility by their product, with quotient independent of spins in `R`. | Correct. | `l:edge`; irreducibility of a rank-four quadratic over `C`; distinct edges give nonassociate factors; polynomial UFD; additivity of multidegrees; simple, degree-four graph. |
| Definition 2.3, `d:frame`, `:51–53` | A frame is a finite positive weighted spherical 4-design. | Correct. | Normalized spherical area measure; testing constant polynomial 1 implies total frame weight 1. |
| Lemma 2.4, `l:tight`, `:55–61` | Weighted coherent-state evaluation preserves the spin-2 norm. | Correct. | `e:zeta`, `e:Vinner`, `d:frame`; each evaluation modulus square has coordinate degree at most four. |
| Theorem 2.5 (QD), `t:QD`, `:91–117` | For even `L,N>=4`, the kernel is `C B` and the quantum gap is at least `g_star lambda(mu^circ)/2`. | Correct after the orientation convention fix in Finding 1. | `l:edge`, `l:divisibility`, `l:tight`, `e:star`, `e:icodod`, `e:qmod`, `e:mucirc`, finite full-support heat-bath Poincaré inequality, unitary multiplication map, and `e:QDcomp`. |
| Remark 2.6, `r:QDgeneral`, `:119–121` | The comparison extends to simple 4-regular graphs when frame evaluations of `B` never vanish. | Correct. | Same proof; fixed five-site star, positive weighted frame isometries, and full-support induced measure. For a gap statement the graph should be nonempty. No bipartite assumption is needed if nonvanishing is independently supplied. |

### Numbered equations and their assertions

| Number and label | Content | Verdict | Dependencies |
|---|---|---|---|
| (1.1), `e:H`, `sec1-intro-statement.tex:6–8` | `H` is the sum of nearest-neighbour total-spin-4 orthogonal projections. | Correct. | Simple torus with `L,N>=3`; spin-2 tensor-product Hilbert space; Clebsch–Gordan specifies the rank-nine summand. |
| (2.1), `e:zeta`, `sec2-frames-Q.tex:8–10` | A unit spinor has rank-one density matrix `(I+a·sigma)/2`. | Correct. | Pauli identities, `norm(a)=1`, and the Bloch-sphere correspondence. |
| (2.2), `e:Vinner`, `:12–14` | The spin-2 inner product is five times the spherical evaluation integral. | Correct. | Phase cancellation, positivity/full support, SU(2) covariance and spherical rotation invariance. |
| (2.3), `e:B`, `:22–24` | `B` is the product of oriented determinant factors. | Correct. | Degree four at each vertex; nonzero polynomial product; arbitrary orientations affect only its global sign. |
| (2.4), `e:star`, `:44–46` | `H_x >= g_star(I-Pi_Sx)` and `sum_x H_x=2H`. | Correct. | Finite-dimensional positive spectral theorem; four distinct neighbours; every edge has two endpoints. |
| (2.5), `e:icodod`, `:64–66` | Cross-frame dot products are `±sqrt((5±2sqrt(5))/15)`. | Correct. | Dual relative placement of the polyhedra; exact coordinate check in §3. |
| (2.6), `e:qmod`, `:76–78` | A determinant's squared modulus is `(1-a·b)/2`. | Correct. | Complex two-dimensional Gram determinant and Pauli trace identities. |
| (2.7), `e:mucirc`, `:80–82` | The frame image of `B` induces the antialigned Gibbs probability. | Correct. | Product frame isometry; `e:qmod`; normalization and positivity. |
| (2.8), `e:lambdaHB`, `:86–88` | The heat-bath gap is the conditional-variance Rayleigh infimum. | Correct. | Complex variance means `mu(abs(F-mu(F))^2)`; conditional expectations are orthogonal projections; full support. |
| (2.9), `e:QDcomp`, `:107–109` | Classical projection distance is no larger than quantum star-kernel distance. | Correct. | `iota(S_x) subset Ran(P_x)`, isometry, and contraction of an orthogonal projection. Finding 1 corrects the preceding identification of its fibre vector. |
| (2.10), `e:muD`, `:126–128` | Checkerboard spin inversion turns minus bond factors into plus factors. | Correct. | Even periods, antipodal frames, antipodally invariant uniform weights. |
| (2.11), `e:QDrot`, `:130–132` | The quantum comparison has the same constant for `mu_D`. | Correct after Finding 1's proof convention fix. | `t:QD`; sitewise bijection conjugates both heat-bath generators. |
| (2.12), `e:muDW`, `:134–136` | Finite-volume frame Gibbs probabilities have the stated internal and boundary factors. | Correct. The following prose needs Finding 2's fix. | Finite `W`; outside letters belong to their assigned frames; each crossing bond appears once; all factors are strictly positive. |

## 3. Formalization notes and detailed checks

### Model, domains, and elementary edge cases

- Use an unordered **set** of nearest-neighbour edges, with no multiplicities. For `L,N>=3`, the neighbours `x±e_1,x±e_2` are pairwise distinct and distinct from `x`; every vertex has degree four and `|E|=2|Lambda|`. This remains true for period 3, although the graph then contains triangles. Period 2 would collapse neighbours and is rightly excluded. The five sites of a star are distinct even when additional edges join some of its leaves; those additional edges are absent from `H_x` and do not affect its identification with `h_star`.
- Specify tensor products over a finite index set, or choose an ordering and prove invariance under reindexing. Extending a two-site projector by the identity and identifying every `H_x` with the same star require unitary tensor-factor permutations.
- The abstract spin-2 Hilbert space in §1 is identified with the polynomial model by an **equivariant unitary** identification, not just by equality of dimensions. All SU(2) representations here are finite-dimensional and continuous; the polynomial representations are smooth. An invariant positive inner product on a five-dimensional representation alone would not imply irreducibility. The additional standard fact is irreducibility of homogeneous binary forms, stated in §4.
- `B` has multidegree four at every vertex and is nonzero in the polynomial domain. Reversing any edge only multiplies `B` by `-1`. No normalization or positivity of polynomial coefficients is required.
- The global quantum gap is the smallest **strictly positive** eigenvalue. In the present nonempty tori this eigenvalue exists: `H` is positive and nonzero, while `H B=0` with `B!=0`.
- Finite-volume `W` need not be connected, and `W=empty` gives a singleton configuration space and partition function 1. A heat-bath gap on a singleton needs a separate convention; Section 2 does not use one. The tori in QD are never singletons.
- The checkerboard is well-defined on residue classes only when both periods are even. Combined with the initial lower bound 3, the phrase “from now on even” at line 71 already means at least 4. A later formal statement should carry these hypotheses explicitly.

### Spinors, inner products, and coherent states

These are separate nodes; none is supplied just by a numerical frame calculation.

1. Define the Pauli matrices, the Hermitian product on `C^2` (conjugate-linear in the first argument), and `I` in (2.1). Prove

   \[
   \sigma_i\sigma_j=\delta_{ij}I+i\sum_k\varepsilon_{ijk}\sigma_k,
   \quad \operatorname{tr}\sigma_i=0,
   \quad \operatorname{tr}(\sigma_i\sigma_j)=2\delta_{ij}.
   \]

   Then `(I+a·sigma)/2` is a positive rank-one projection of trace 1 whenever `a` is real and unit. Its unit-vector representatives differ exactly by a phase.

2. A globally continuous choice `a -> zeta(a)` is unnecessary and should not be postulated. Although a phase choice has been made everywhere, `overline(phi(zeta(a))) psi(zeta(a))` is phase independent and is a continuous polynomial in `a` via products of entries of `zeta zeta*`. Thus the integrand is measurable without any regularity assumption on the chosen section. All frame evaluations themselves occur on finite sets.

3. The inner product is positive definite. Vanishing integral of the nonnegative continuous modulus square implies vanishing on every direction, by full support of spherical area. Phase independence then implies vanishing on the entire unit sphere in `C^2`; homogeneity extends this to all of `C^2`, and polynomial evaluation over the infinite field `C` detects the zero polynomial.

4. For `m_k(z)=z_1^{4-k}z_2^k`, `0<=k<=4`, direct spherical integration gives

   \[
   \langle m_k,m_l\rangle=\frac{\delta_{kl}}{\binom4k}.
   \]

   Hence `sqrt(binomial(4,k)) m_k` is an orthonormal basis. This fixes the normalization in (2.2) and gives an explicit realization for matrix computations.

5. The Riesz vector of evaluation at `zeta(a)` is

   \[
   k_a(z)=(\overline{\zeta_1(a)}z_1+\overline{\zeta_2(a)}z_2)^4,
   \qquad \langle k_a,\varphi\rangle=\varphi(\zeta(a)),
   \quad \|k_a\|=1.
   \]

   These are the normalized spin-2 coherent vectors implicit in the text. Lemma 2.4 and complex polarization imply the operator identity `sum_a 5w(a)|k_a><k_a|=I`. No assertion that distinct coherent states are orthogonal is used.

6. Conjugation by `g in SU(2)` on Pauli matrices defines `R_g in SO(3)`, with `g zeta(a)` a phase times `zeta(R_g a)`. Together with rotation invariance of area this proves unitarity of `U_g phi(z)=phi(g^{-1}z)`. The representation is the dual symmetric fourth power, unitarily equivalent to spin 2. The analogous symmetric third power is spin 3/2.

### Edge divisibility, uniqueness, and the star

- In Lemma 2.1 multiplication by `q_e` is an injective equivariant map from bidegree `(3,3)` forms to bidegree `(4,4)` forms. Clebsch–Gordan gives domain spins `0,1,2,3` (dimensions `1+3+5+7=16`) and codomain spins `0,1,2,3,4` (dimension 25). Multiplicity one identifies its image with the orthogonal complement of the rank-nine spin-4 summand. For the full lattice, tensor the exact kernel/image statement with the remaining site factors. This last tensoring step is implicit at line 32.
- Positivity of projections gives `ker(sum_e P_e)=intersection_e ker P_e`, since `sum_e <phi,P_e phi>=sum_e ||P_e phi||^2`. In particular `ker H_x` imposes **each** incident constraint, as required when Lemma 2.2 is used at line 110.
- The symmetric matrix of the quadratic `q_e=x_1 y_2-x_2 y_1` has rank four over `C`. A reducible homogeneous quadratic over a field of characteristic different from 2 is a product of linear forms and has rank at most two. Irreducibility persists after adjoining all spectator variables. In the ambient polynomial UFD an irreducible is prime, and the factors for distinct edges of a simple graph are nonassociate. Consequently their product divides the state. Distinct factors need not generate comaximal ideals; no such assertion is needed.
- The quotient in Lemma 2.2 is multihomogeneous. One can first prove that division by a multihomogeneous nonzero polynomial preserves multihomogeneity of a homogeneous product, or use additivity of the degree in each variable block. Degree zero in the two-variable block `z_x` means independence of both coordinates. Handle `phi=0` by choosing quotient zero. Handle `R=empty` by product 1 and quotient `phi`.
- There is also a completely algebraic uniqueness proof: apply Lemma 2.2 with `R=Lambda`. Then `b_R=B`, and the quotient is independent of every variable, hence constant. Thus `ker H=C B` on **every** simple 4-regular graph, and in particular on every torus with `L,N>=3`, without frames, a heat-bath gap, or even periods. QD's uniqueness argument is valid but stronger machinery than necessary.
- `h_star` is a nonzero positive operator on dimension `5^5=3125`. For example, the tensor product of five spin-2 highest-weight vectors has each edge pair in spin 4, so is an eigenvector of eigenvalue 4. Its finite positive spectrum is nonempty and has a strictly positive minimum `g_star`. The spectral theorem gives `h_star >= g_star(I-Pi_ker)` exactly. Tensoring by an identity preserves this bound. There is no need to prove a numerical lower bound for `g_star`.
- Every bond belongs to precisely two stars, so the double counting in (2.4) is exact. The denominator 2 in QD comes from this identity, not from a choice of heat-bath rates.

**Numerical check, not a certified eigenvalue bound:** `check_star.c` constructs the rank-nine edge projector from the maximal-spin Clebsch–Gordan coefficients

\[
\langle k_1,k_2\mid 4,M\rangle
=\sqrt{\frac{\binom4{k_1}\binom4{k_2}}{\binom8{k_1+k_2}}},
\qquad M=k_1+k_2-4,
\]

and diagonalizes each total-magnetization block of the five-site star using double precision. The smallest positive value is approximately `0.047238143987519`, reproducing line 47. The numerical zero-eigenvalue count is 256, consistent with the exact star-kernel description `product_{y neighbour x} q_xy` times arbitrary degree-three forms at the four leaves, of dimension `4^4`. The largest diagonalized block has size 381. The source and output are retained as `check_star.c` and `check_star.out`; this computation is not used to justify positivity.

### Exact polyhedral data and frame isometry

Here is an exact replacement for the unlocated citation and the omitted “direct computation.” Put `phi=(1+sqrt(5))/2`. Let `cyc` mean the three cyclic coordinate permutations, with independent indicated signs. Before normalization choose

\[
\begin{aligned}
I_0&=\{\operatorname{cyc}(0,\pm1,\pm\phi)\},
&|a_0|^2&=\phi+2,\\
D_0&=\{(\pm1,\pm1,\pm1)\}
\cup\{\operatorname{cyc}(0,\pm\phi,\pm\phi^{-1})\},
&|b_0|^2&=3.
\end{aligned}
\]

There are 12 and 20 distinct vectors respectively. These specify their **relative** orientation; two independently rotated polyhedra would not suffice for (2.5). For each `b_0`, exactly three vertices of `I_0` have `a_0·b_0=1+phi`, their pairwise dot products are `phi`, and their sum is `(1+phi)b_0`. They are the triangular face whose centre points in direction `b_0`.

Both sets are invariant under coordinate sign changes and cyclic permutations. All moments with an odd coordinate exponent vanish. For their normalized uniform vertex measures the remaining moments through total degree five are exactly

| Monomial | Both vertex averages | Normalized spherical average |
|---|---|---|
| `1` | `1` | `1` |
| `a_i^2` | `1/3` | `1/3` |
| `a_i^4` | `1/5` | `1/5` |
| `a_i^2 a_j^2`, `i!=j` | `1/15` | `1/15` |

This proves the full 5-design assertion, since monomials span polynomials of degree at most five. Only degree four is needed. The computation uses just `phi^2=phi+1`. Moreover, for all 240 vertex pairs,

\[
\frac{(a_0\cdot b_0)^2}{3(\phi+2)}
\in\left\{\frac{5+2\sqrt5}{15},\frac{5-2\sqrt5}{15}\right\}.
\]

Each squared value occurs 120 times; antipodal symmetry gives the two signs equally. Finally `gamma_+<159/200` by exact squaring, so `1-gamma_+>41/200=0.205`. Numerically the two positive constants are `0.7946544722917661` and `0.1875924740850798`, in agreement with (2.5).

The retained `check_frames.py` verifies all 56 monomials of total degree at most five for each frame, all cross-product squares, the face-centre relation, and the rational positivity bound, using `fractions.Fraction` arithmetic in `Q(sqrt(5))`. `check_frames.out` records the results. These checks are **exact arithmetic**, except for the explicitly labelled final decimal displays.

For Lemma 2.4, a monomial in `overline(phi(zeta(a))) phi(zeta(a))` contains four conjugated and four unconjugated spinor coordinates. Pair them into four entries of `zeta zeta*`; each entry is affine in the real coordinates of `a`. Thus the squared modulus is a polynomial of degree at most four, not degree eight in `a`. This supplies exactly the design hypothesis. Polarization gives preservation of all inner products, and finite tensor products give the global isometry.

### Measures, maps, and the QD inequality

- The evaluation map on the whole polynomial ring should be named separately from its restriction `iota` to `H_Lambda`. At line 75 and in `iota(psi)=iota(b_R)iota(chi)`, the factors generally do not belong to `H_Lambda`; as written, these applications of the declared domain of `iota` are ill-typed. The text clearly intends ordinary polynomial evaluation. Define `ev_s` on the ring, prove multiplicativity there, and restrict to the multihomogeneous Hilbert subspace for isometry statements.
- `pi(s)=product_x 5w_x(s_x)` is a positive reference **measure**, of mass `5^{|Lambda|}`, not a probability measure. Weighted `ell^2(Omega,pi)` is perfectly valid. Put `n=|Lambda|`, `m=|E|`; then

  \[
  \|B\|^2=5^n2^{-m}Z^\circ,
  \qquad
  \mu^\circ(s)=\pi(s)|\iota B(s)|^2/\|B\|^2.
  \]

  This checks all factors of 5 and 2 in (2.7). On a four-regular torus `m=2n`. The introduction's “whose square is a Gibbs measure” at `sec1-intro-statement.tex:24` should be understood precisely as this normalized, reference-weighted **squared modulus**; the function itself can have complex phases.
- The identity `|<zeta,zeta'>|^2+|det(zeta,zeta')|^2=1` uses unit norms. The Pauli trace calculation gives the first term `(1+a·b)/2`. Consequently all sampled bond determinants are nonzero, since every edge joins the two **differently placed** frames. This proves both full support of `mu^circ` and the absence of zero denominators in the proof.
- For each nonzero fibre vector `beta`, its projection is

  \[
  (Pf)(t)=\beta(t)
  \frac{\sum_{t'}5w_x(t')\overline{\beta(t')}f(t')}
       {\sum_{t'}5w_x(t')|\beta(t')|^2}.
  \]

  Positivity of the denominator is explicit. Decomposing by outside configurations gives the global orthogonal projection `P_x`; no orthogonality of the frame vectors is assumed.
- `U F=F iota(B)/||B||` is onto the entire weighted function space: the inverse is `U^{-1}f=||B|| f/iota(B)` at each configuration. It is a unitary between two spaces of dimension `|Omega|`. The smaller physical Hilbert space embeds through `iota`; `U` is not claimed to identify it with all classical functions.
- The conditional distribution at `x` is proportional to `5w_x(t)|beta_x(t)|^2`; the 5 cancels. This proves `U E_x=P_x U` using the projection formula. Finding 1's constant sign is absorbed into `rho_x` and cancels throughout.
- Lemma 2.2 and positivity of the star summands give `iota(S_x) subset Ran P_x`. This inclusion is sufficient; neither equality of these subspaces nor preservation of `Ran iota` by `P_x` is needed. Orthogonal projection as best approximation, followed by isometry, gives (2.9).
- For `phi perp B`, define `F=U^{-1}iota(phi)`. Then

  \[
  \mu^\circ(F)=\langle B,\varphi\rangle/\|B\|=0,
  \qquad \operatorname{Var}_{\mu^\circ}(F)=\|\varphi\|^2.
  \]

  For `phi=0` every required inequality is trivial. Otherwise `F` is nonconstant, so the Rayleigh definition applies. The complete comparison is

  \[
  \begin{aligned}
  \lambda(\mu^\circ)\|\varphi\|^2
  &\le\sum_x\|(I-E_x)F\|^2\\
  &=\sum_x\|(I-P_x)\iota\varphi\|^2\\
  &\le\sum_x\langle\varphi,(I-\Pi_{\mathcal S_x})\varphi\rangle\\
  &\le\frac1{g_\star}\sum_x\langle\varphi,H_x\varphi\rangle
  =\frac2{g_\star}\langle\varphi,H\varphi\rangle.
  \end{aligned}
  \]

  Every inequality has the correct direction. The proof does not use a quantum gap or uniqueness before establishing this bound.
- For a finite product space with full-support probability, each single-coordinate replacement has positive heat-bath rate. Replacing coordinates successively connects all configurations. Equivalently, zero conditional variance at every coordinate forces a function to be constant on each fibre, hence everywhere. The positive operator `sum_x(I-E_x)` therefore has exactly the constants as kernel and a strictly positive gap. Individual `E_x` need not commute. The generator in §2 is nonpositive; its gap is the first positive eigenvalue of its **negative**, with rate one per site, not a discrete-time update normalized by the number of sites.
- The preceding bound on `B^perp`, together with `H B=0`, proves uniqueness and the quantum gap claim by the finite-dimensional spectral theorem. It proves the conclusion even if the spectral-gap definition initially allowed a degenerate kernel.
- Checkerboard inversion `R` is a product of sitewise bijections. Uniform weights satisfy `w_x(-a)=w_x(a)`; antipodal invariance of the sets alone would not be sufficient for arbitrary weighted frames. Pullback by `R` is unitary between the two probability `L^2` spaces and conjugates every conditional expectation, proving equality of the gaps. This is a change of classical variables; no physical SU(2) rotation implementing `a -> -a` is required.
- For finite `W`, internal edges and crossing edges in (2.12) are each counted once. Outside spins must belong to the assigned neighbouring frames, which ensures strict positivity. This full-support statement does **not** assert strict pointwise positivity for arbitrary sphere-valued pins in the continuous model of Section 5.

### Additional quantum facts referenced by the introductory certificate summary

The introduction at line 18 refers to exchange-symmetry sectors whose justification is in Appendix D (`app-local.tex`). For completeness, these are the quantum/representation-theoretic facts involved in that reference. Their use is consistent with the preceding conventions; certifying every integer matrix remains outside R1.

1. Pauli tensor products send a real multiaffine polynomial `F` to a Hermitian operator `O(F)`, and `tr(sigma_j zeta(b)zeta(b)*)=b_j` gives its coherent-product expectation. Replacing selected vectors by their negatives twice returns `F`; positivity of the resulting operator is therefore a sufficient condition for nonnegativity of `F` (`l:inversion`, `app-local.tex:82–109`). No converse is asserted.
2. `U sigma_j U* = sum_l R_lj sigma_l` makes this operator construction SU(2)-covariant. Simultaneous rotational invariance of `F` implies commutation with `U^{tensor k}`. Simultaneous reflection of the second coordinate changes the sign of every `sigma_2` and leaves the polynomial invariant, proving that its matrix is real symmetric (`l:Ostruct`, `:116–153`).
3. Two qubits split orthogonally as `Sym^2(C^2)` (spin 1, exchange sign +) and `wedge^2(C^2)` (spin 0, exchange sign −). Identical coherent vectors have tensor square in the symmetric summand. A pair of pure-sphere slot factors therefore annihilates the antisymmetric summand. The atom at zero for a diluted corner instead contributes `I tensor I`, so that support statement is correctly not extended to diluted corners (`l:Ostruct`, parts 3–4).
4. Commutation with the diagonal one-parameter SU(2) subgroup implies commutation with its total component `Sigma_3`. The maximal component `k/2` has one-dimensional eigenspace spanned by the all-up tensor, so an operator commuting with it has that tensor as an eigenvector (`app-local.tex:156–165`).
5. Every finite-dimensional SU(2)-invariant eigenspace of a Hermitian commuting operator splits into irreducibles. A spin-`j` irreducible has weights `j,j-1,...,-j`, each once. A tensor product of spin-1, spin-0, and qubit factors has one fixed weight parity: integral if the number of qubits is even, half-integral otherwise. Every irreducible in it therefore meets respectively the weight-0 or weight-1/2 space. Restriction to that space detects the **set** of operator eigenvalues, though not their full multiplicities (`l:sector`). The text's positivity conclusion uses only the set.
6. Exchange signs for disjoint pairs give an orthogonal invariant direct-sum decomposition. Positivity on all these sectors and the support in their sum implies positive semidefiniteness on the ambient tensor product (`p:certificate`, `:168–179`). Congruence matrices in a nonnormalized integer basis preserve positivity; they need not preserve ordinary matrix eigenvalues (`:188–192`).

## 4. External inputs

The external papers themselves are not included in the bundle. I have not fetched them, in accordance with the brief. “Locator” below records what this manuscript actually provides; a bibliographic page range is not a theorem locator. For the elementary facts I give the exact needed statement and check its hypotheses, rather than pretending an unavailable original has been inspected.

### Inputs to the Section 2 argument

| Input and exact statement as used | Locator supplied by the manuscript | Hypothesis check / role |
|---|---|---|
| **Pauli/Bloch correspondence:** for real unit `a`, `(I+a·sigma)/2` is a rank-one orthogonal projection; every unit spinor's rank-one projection has this form, uniquely in `a`; representatives differ by phase. | (2.1), `sec2-frames-Q.tex:7–15`; no external locator. | Correct for complex two-component spinors of norm 1 and unit real vectors. Follows from the explicit Pauli identities listed above. |
| **SU(2)–SO(3) correspondence:** conjugation on traceless Hermitian matrices gives `R_g in SO(3)` and `g(a·sigma)g*=(R_g a)·sigma`. | `sec2-frames-Q.tex:15`; no external locator. | Applied only to `g in SU(2)`. Ensures the phase relation and invariance of the inner product; no globally chosen lift from SO(3) is needed. |
| **Homogeneous binary forms:** `P_d(C^2)` with pullback action `p(z)->p(g^{-1}z)` is an irreducible complex SU(2) representation of spin `d/2` and dimension `d+1`. | Asserted for `d=4` at `sec2-frames-Q.tex:15`, implicit for `d=3` at `:32`; no source or precise locator. | Correct for the nonnegative integer degrees 3 and 4. A short proof uses the distinct torus-weight monomials and the raising/lowering derivations connecting consecutive monomials. Include this as a Lean node rather than inferring irreducibility from the invariant inner product. |
| **Clebsch–Gordan rule:** for finite-dimensional continuous irreducible complex unitary SU(2) representations of spins `j,k` in the nonnegative half-integers, `V_j tensor V_k` is the orthogonal direct sum of `V_l` for `l=abs(j-k),abs(j-k)+1,...,j+k`, each with multiplicity one. | Named without citation at `sec2-frames-Q.tex:32`. | Applied to `(3/2,3/2)` and `(2,2)`, within all hypotheses. In particular the maximal-spin pair summand has dimension 9 and is uniquely determined. |
| **Complete reducibility and Schur's lemma:** finite-dimensional unitary representations split orthogonally into irreducibles; intertwiners between inequivalent irreducibles vanish; in a multiplicity-one sum the isotypic subspaces are determined. | Implicit in `l:edge`, `sec2-frames-Q.tex:32`; no external locator. | The spaces are finite-dimensional over `C`, the target is unitary, and multiplication by `q_e` is equivariant and injective. Thus it has precisely the indicated lower-spin image. The same facts underlie Appendix D's sector discussion. |
| **Determinant/Gram identity:** for unit `u,v in C^2`, `abs(<u,v>)^2+abs(det(u,v))^2=1`; also `tr(uu*vv*)=abs(<u,v>)^2`. | `sec2-frames-Q.tex:75–77`; no external locator. | Unit norms are supplied by (2.1). Direct two-by-two algebra; gives exactly the factor 1/2 in (2.6). |
| **AKLT88:** the spin-2 square-lattice AKLT interaction is the projection onto total spin 4, and the determinant-product VBS is a zero-energy state. | Cited at `sec1-intro-statement.tex:5` and `sec2-frames-Q.tex:3`; entry `main.tex:69–72`, journal pp. 477–528; no theorem/page locator. | Historical attribution. Both the operator and the state are explicitly defined here, and the zero-energy property is proved by `l:edge`. No theorem from AKLT88 is needed for QD. |
| **KLT88:** coherent-state evaluation of the VBS squared modulus produces nearest-neighbour factors proportional to `1-a·b`. | `sec2-frames-Q.tex:3`; entry `main.tex:99–102`, journal pp. 383–415; no theorem/page locator. | Historical motivation only. Equations (2.6)–(2.7) rederive the identity with all normalization factors, so no external uniqueness or gap claim is imported. |
| **DGS77:** the uniformly weighted 12 icosahedral vertices and 20 dual dodecahedral vertices on the unit two-sphere integrate every polynomial of degree at most 5 exactly. | `sec2-frames-Q.tex:63`; entry `main.tex:79–82`, journal pp. 363–388; no precise locator. | Correct for regular, centred, normalized polyhedra; their relative dual placement is additionally needed for (2.5). Independently proved by the exact moments above. Locator deficiency is Finding 3. |
| **Quadratic irreducibility and polynomial factoriality:** over `C`, a homogeneous quadratic of rank greater than two cannot factor into linear forms; a polynomial ring in finitely many variables is an integral domain and UFD, with irreducibles prime. | `sec2-frames-Q.tex:25,40`; no external locator. | Rank is four, characteristic is zero, variables are finite in number. Simplicity gives distinct nonassociate factors. This is an algebraic input, not a numerical irreducibility test. |
| **Finite positive spectral theorem:** a nonzero positive Hermitian operator has a finite nonempty set of positive eigenvalues; its minimum `g` gives `A>=g(I-Pi_ker A)`. Orthogonal projections have norm at most one and realize distance to their range. | Used at `sec2-frames-Q.tex:43–47,99,108–116`; no external locator. | All spaces are finite-dimensional complex Hilbert spaces with positive weights. Nonzero `h_star` is established above; no limiting or infinite-volume spectral claim occurs. |
| **Finite heat-bath/Poincaré facts:** conditional expectation is the orthogonal projection onto functions measurable off that coordinate; its complement's squared norm is the expected conditional variance. For a full-support probability on a finite nontrivial Cartesian product, rate-one coordinate heat bath is irreducible, has constants as kernel, and has a positive Rayleigh gap. | `sec2-frames-Q.tex:85–89`; no external locator. | Both single-site sets are nonempty and have more than one element; every product configuration has positive probability. The complex-valued version follows from the same Hilbert-space statement or by real and imaginary parts. |
| **Unitary spectral invariance and finite tensor products:** unitary conjugation preserves spectra/gaps, finite products of isometries are isometries, and tensor-factor permutations are unitary. | Used at `sec2-frames-Q.tex:43,75,101–116,129`; no external locator. | All index sets are finite; the multiplication map has no zeros and is onto; the rotation map is a product bijection preserving the frame weights. |
| **Spin weights and singlet/triplet splitting:** spin `j` has weights `-j,-j+1,...,j`, and two qubits split as spin 1 symmetric plus spin 0 antisymmetric. | Needed by the certificate summary in §1 via `app-local.tex:116–179`; no separate external citation. | Correct for finite-dimensional SU(2) modules. Fixed weight parity in each stated tensor product justifies the central-weight-sector positivity test. This is contextual to the introductory certificate reference, not an additional premise of QD. |

### External inputs mentioned in Section 1's later-proof summary

These are not additional hypotheses of QD. The statements below are the forms used in this manuscript, read from Section 4; verification against the original publications belongs to the mixing lane. Their original texts are absent from the permitted inputs.

- **MOS94, Proposition 2.1, p. 39, and (2.8):** the manuscript uses the shell-by-shell coupling construction for a finite-state, finite-range Gibbs field with finite energy. Its actual input is a uniform window coupling probability `p_0>0`, and its conclusion is an exponentially small-in-`M^(1/4)` influence of a single changed exterior letter on the remote marginal. Section 4 reproduces the construction as `p:surgery`, rather than simply asserting that this is the original proposition under changed hypotheses. The required positive finite-energy constant exists here because the blocked alphabet is finite and every elementary factor is positive. This matches the qualification in `sec1-intro-statement.tex:28,40`.
- **MOS94, Theorem 2.1 and (2.2):** as restated in `t:MOS21`, the model has a finite alphabet, a real-valued translation-invariant finite-range potential on `Z^2`, and for some sufficiently large square the remote-marginal total-variation bound is at most `M^(-4)` uniformly over boundary conditions. The conclusion is uniform strong mixing on squares. After blocking, each offset model has 57,600 letters, is translation invariant, and has range one; the checkerboard itself need not be one-site translation invariant. The needed small influence bound is supplied later, not by Section 2.
- **MO94, Theorem 4.1, with rates (4.1):** as restated in `t:MO41`, strong mixing with constants `C,gamma>0` on a sufficiently large square implies a positive uniform rate-one heat-bath gap on sets compatible with that square and all boundary conditions. The application needs a general finite alphabet and no attractiveness assumption. The manuscript expressly acknowledges that the original proof is written with two spin values and gives its claimed extension in `r:finiteS` (`sec4-mixing-to-gap.tex:55–56`); the further locator is MOS94 Theorem 3.2, `(ii)=>(iv)`. This extension is an identified external issue to be checked in that lane, not silently treated as an original theorem already quoted in exactly the needed generality. The actual assembly uses a sequence of compatible squares, which suffices for the finite-size criterion; it need not first prove a bound for every possible side length.
- The **Knabe-type finite-size criterion** referred to at `sec1-intro-statement.tex:26` is proved as `t:K`, not imported as a black-box quantum theorem. Section 3 cites Kna88 and GM16 for the method, but changes the placement argument to avoid translation invariance. The necessary input is a box gap exceeding `1/ell`, uniformly over placements and outside configurations.

For the main theorem the internal assembly is dimensionally consistent: with the positive constants `c_0,m_0` obtained later, choose a compatible even side `ell>=2/(c_0 m_0)` and even `L,N>=ell+2`. Theorem `t:K` yields `lambda(mu_D)>=c_0 m_0/2`, and QD yields `gap(H)>=g_star c_0 m_0/4`. Thus the in-lane reduction introduces no further size, parity, boundary, normalization, or uniqueness obstruction.
