VERDICT: SOUND

# Scope

I read all of the supplied LaTeX sources for context and checked Appendix D (`app-local-operator.tex`, lines 3–897; PDF pp. 73–82) line by line. The verdict concerns Appendix D's mathematical statements and certificate implications. Its external dependencies are the covered-pattern definition, the finite moment identities, finite-network positivity, and the three-field mean bound. Their stated hypotheses suffice at every use.

Appendix D proves a sufficient certificate criterion; it does not assert that the numerical witnesses for all patterns pass. I did not access the archive files mentioned in Section 8, which are outside the permitted inputs. The independent computations below check algebra and regenerate pattern classes from the paper; they do not replace Section 8's witness checks.

# Numbered findings and proof audit

**Critical: 0. Major: 0. Minor: 0. No LaTeX repair is required.** The numbered items record successful checks, not alleged defects.

1. **Passage integration and strict positivity are correct.** Location: `app-local-operator.tex:24`, label `l:Iw` (Lemma D.1), proof through line 87. The exact claim is
   \[
   Z_{\rm cur}=Z_w[1+(P_{fg}+P_{fo}+P_{go})/3],\qquad
   Z_{\rm next}=Z_w[1+P_{fg}/5]>0.
   \]
   The passage has no arrival bond; every other nonremoved neighbour keeps its passage bond. Thus these are precisely the products to integrate. A removed neighbour contributes a constant factor one, without introducing a spin or a law. The second moments are respectively \(1/3\) and \(1/5\), and the odd moments vanish. The subtraction coefficient \(1/3-c/5\) is correct. The remaining weight is nonnegative, and \(J\ge4/5\), so the strict inequality follows from finite-network positivity, including disconnected networks. Every original spin has degree at most four, so the asserted orthogonal covariance uses the moment lemma within its hypotheses.

2. **The leaf radii and common-factor reduction are valid, including endpoints.** Locations: `app-local-operator.tex:89`, `:148`, `:172`; labels `l:leaf`, `d:reduction`, `c:reduce` (D.2–D.4). Tips have the U law and exactly three covered slots. Lemma `l:35` applies with three unit fields; the normalizer is at least \(1/2\). For a corner, writing \(t=a\cdot b\), the displayed identities
   \[
   (1+t/3)^2-4(2+2t)/9=(1-t)^2/9,
   \]
   \[
   (1+t/5)^2-9(2+2t)/25=(1-t)(7-t)/25
   \]
   give precisely the radii \(1/2\) and \(1/3\). Their normalizers are at least \(2/3\) and \(4/5\). These bounds include \(t=-1,1\); zero effective vectors cause no division by zero. Tips and corners form an independent set in the template, and none is incident to the passage. Consequently their integrations give the same positive factor \(K\) and the same effective vectors in both partition functions. The separate degree bound remains four after each passage insertion and leaf replacement. The convex decomposition at lines 220–229 correctly extends separate-affine positivity from spheres to balls, including zero vectors and \(k=0\).

3. **The Pauli trace formula and structural symmetries have the required signs and hypotheses.** Locations: `app-local-operator.tex:248`, `:271`, `:320`; labels `d:Pauli`, `l:inversion`, `l:Ostruct` (D.5–D.7). The Pauli convention agrees with Section 3. The coefficient expansion is on all of \((\mathbb R^3)^k\), so it is unique. Both the polynomial and the density arguments are inverted in D.6; hence the two sign changes cancel exactly. Positivity of a product density and nonnegativity of its trace against a positive operator require no commutation between those operators. Reflection of the second coordinate proves reality; Hermiticity then proves symmetry. The SU(2) conjugation formula has the correct transpose \(R^{\mathsf T}\). Only orthogonality of \(R\) is needed. The polynomial comparison using \(U_j(t)\) correctly yields all three generator commutators, also when \(k=0\).

   The groupwise inversion condition is essential and is present: both slots of a retained pair have the same sign. For a U-corner the tensor square of the rank-one matrix has symmetric range and annihilates the exterior square. For a D-corner its zero-spin summand need not annihilate the exterior square, so retaining both exchange sectors is necessary. The text does so. No positivity of the remaining summands is used to prove these support and exchange identities.

4. **The exchange bases and central-weight ladder argument work for both parities.** Locations: `app-local-operator.tex:418`, `:472`; labels `d:exchange`, `l:sector` (D.8–D.9), including the unnumbered identities at lines 434–470. The listed basis vectors are orthogonal integer-coordinate vectors with squared norms powers of two. Their weights and all four nonzero pair ladder actions are correct. The tensor factors therefore preserve every exchange sector, and all its weights lie in \(\kappa+\mathbb Z\), where \(\kappa\) depends on the number of singles.

   Each eigenspace of the commuting Hermitian operator is invariant under the three spin operators. On a nonzero weight vector,
   \[
   \|S_-v\|^2-\|S_+v\|^2=2m\|v\|^2
   \]
   forces the required next ladder vector to be nonzero. For \(\kappa=0\), raising from below uses negative integer weights. For \(\kappa=1/2\), the last raising step starts at \(-1/2\), also strictly negative. Lowering from above likewise starts at a positive weight at every step. Thus every eigenvalue occurs centrally. Equality of eigenvalue **sets**, rather than multiplicities, is exactly what is proved and needed. Empty tensor products give the one-dimensional scalar case and introduce no exception.

5. **Coefficient reconstruction, integrality, and the positive scale are correct.** Location: `app-local-operator.tex:582`, label `l:integercheck` (Lemma D.11), reconstruction at lines 612–766. All surviving nonremoved passage neighbours are in \(X\); no leaf reduction removes them. A bond, vector factor, or insertion contributes its coordinate exactly once at each indicated endpoint. The formula at lines 677–683 is therefore a complete finite distributive expansion. All local words have length at most four. The U fourth-moment denominator is 15; the D fourth-moment denominator is 25, including when all four coordinate indices coincide.

   Consequently
   \[
   D_0=15^{\#U}25^{\#D}\prod_i\beta_i
   \]
   clears the stated coefficients after the additional factors 3 and 5. The inversion signs and Pauli entries reconstruct the entire matrices. Reality plus Gaussian integrality gives integer entries; alternatively, coordinate reflection excludes every coefficient with an odd number of second-coordinate indices. The basis columns are integral. Most importantly, the exact congruence is
   \[
   5qA_\epsilon-3pA'_\epsilon
   =15D_0q\,B_\epsilon^*
      \mathcal O(\widehat F_c^{\mathcal I})B_\epsilon.
   \]
   Every scale is positive. The use of Hermitian-form matrices, rather than operator-coordinate matrices in an unnormalized basis, is correct.

6. **Both integer positivity tests are sound.** Locations: `app-local-operator.tex:527`, label `l:gram-residual` (D.10), and `:768`, determinant part of `l:integercheck` (D.11). Strict row dominance gives a strictly positive coefficient of every \(|z_i|^2\) in the lower bound for \(z^*Ez\). The additional term is \(g\|L^{\mathsf T}z\|^2\ge0\), so no invertibility of \(L\) is needed, over either field. In D.12 the single row inequality already forces the separately listed condition \(E_{ii}>0\).

   For the fallback, the Schur-complement proof of Sylvester's criterion is correct. The Bareiss invariant is the bordered minor written at lines 797–798. In particular \(p_j=\Delta_{j+1}\) and the divisor is \(p_{j-1}=\Delta_j\), not the current pivot. The bordered-minor identity proves exact divisibility whenever that preceding pivot is nonzero. Positive accepted pivots supply this condition inductively. The last update has no trailing entries; size zero has no pivots and determinant convention one. There is no unguarded zero denominator.

7. **The final certificate implication closes without an additional hypothesis.** Location: `app-local-operator.tex:830`, label `p:certificate` (Proposition D.12), proof through line 897. The U-pair projections commute because their tensor factors are disjoint. Their product has range exactly \(V\), and the operator annihilates its orthogonal complement. Commutation with all D-pair exchanges preserves every \(V_\epsilon\). The preceding spin identities and D.7 give the hypotheses of D.9 on each restriction. Thus central positive definiteness gives positive definiteness on every full supported sector. Orthogonality removes all cross terms. This proves full positive semidefiniteness, allowing the discarded U-antisymmetric spaces to be zero. D.6 and D.4 then give the original twenty-slot inequality. Neither optimality of \(c\), realizability of arbitrary effective ball vectors, nor a full-space strictly positive operator is assumed.

# Statement table

All locations in this table refer to `app-local-operator.tex`. “Sound” for a definition includes well-posedness and consistency with the later uses.

| Label / PDF number | Line | Content | Verdict | Dependencies |
|---|---:|---|---|---|
| `l:Iw` / D.1 | 24 | Passage integration, positive next sum, separate affineness and O(3) invariance | Sound | `d:pattern`, `d:moment`, `l:moments`, `l:finitefacts` |
| `l:leaf` / D.2 | 89 | Isolated factors; tip radius 3/5; U/D corner radii 1/2 and 1/3 | Sound | `d:pattern`, `l:moments`, `l:35` |
| `d:reduction` / D.3 | 148 | Reduced/unreduced polynomials and disjoint vector groups | Sound | `l:leaf`, `l:Iw` |
| `c:reduce` / D.4 | 172 | Common positive factor, effective ball vectors, transfer of positivity | Sound | `l:leaf`, `d:reduction`, `l:moments`; separate-affine convex interpolation |
| `d:Pauli` / D.5 | 248 | Pauli map, inversion, Bloch density and total spin operators | Sound | Explicit Pauli matrices; distinct coordinate monomials |
| `l:inversion` / D.6 | 271 | Trace evaluation; inverted operator positivity implies polynomial positivity | Sound | `d:Pauli`, Pauli anticommutation and trace identities; finite spectral theorem |
| `l:Ostruct` / D.7 | 320 | Real symmetry, SU(2)/spin commutation, U support and D exchange | Sound | `c:reduce`, `d:Pauli`, `l:inversion`, unit U support; groupwise inversion |
| `d:exchange` / D.8 | 418 | Orthogonal exchange sectors, integral bases, central weight | Sound | `d:reduction`, explicit tensor basis and spin actions |
| `l:sector` / D.9 | 472 | Central restriction has the full eigenvalue set; positivity equivalence | Sound | `d:exchange`, adjoint and commutator identities, finite spectral theorem |
| `l:gram-residual` / D.10 | 527 | Integer Gram/residual strict-dominance certificate | Sound | Symmetry, positive scales; \(2ab\le a^2+b^2\) |
| `l:integercheck` / D.11 | 582 | Rational reconstruction, integer forms and scale; exact determinant fallback | Sound | `l:Iw`, `d:reduction`, `c:reduce`, `l:moments`, `l:Ostruct`, `d:exchange`; elementary determinant identities |
| `p:certificate` / D.12 | 830 | Sector certificates imply the original local inequality | Sound | D.4, D.6–D.11; orthogonal sector decomposition |

# External hypothesis checks

- `sec6-walks.tex:488`, `d:pattern`: the arrival bond is absent, the out-neighbour is nonremoved, tips are covering U sites, and both slots at every nonremoved corner are retained regardless of external kept flags. Appendix D uses these exact rules. The two thresholds in `h:H1` at line 531 both lie strictly between zero and one, as required here.
- `sec2-moments.tex:35`, `l:moments`: all uses of rotational/reflection covariance are polynomial uses of separate degree at most four. No invariance of the discrete support under arbitrary rotations is inferred. The D moments used in D.11 are exactly 3/5 times the positive-degree U moments.
- `sec2-moments.tex:126`, `l:finitefacts`: the networks to which strict positivity is applied have distinct-endpoint retained bonds, unit original slot pins, U/D laws, and at most four incident factors. Deleting the passage cannot violate any of these hypotheses.
- `sec2-moments.tex:197`, `l:35`: D.2 uses the normalized mean bound only for a U tip with three unit slot fields and positive normalizer. Its degree-four numerator is within the lemma's scope. No claim about higher moments is needed.
- `sec8-inputs.tex:65`–`:146`, `:246`–`:265`: the described application uses groupwise inversion, unnormalized Hermitian forms, the same positive scale, all supported sectors, and either of the positivity tests justified in D.10–D.11. The fallback application is justified directly by D.11; it need not satisfy the Gram-witness premise of D.12.

# Independent exact computations

All computations used integer/rational arithmetic in single-process Python; symbolic matrix and polynomial checks used SymPy. No floating eigenvalue tests were used. The supplementary scripts are [referee_pattern_enumeration.py](referee_pattern_enumeration.py) and [referee_exact_algebra.py](referee_exact_algebra.py).

1. Exhaustively regenerated the \(2{,}048{,}000\) status/kept-set assignments from `d:pattern`. Obtained **106,101** consistent assignments, **184,914** marked assignments, and **123,339** with marked out-neighbour N or E. Independent canonicalization by the stated reflection produced **7,962** effective keys. The largest site degree was **4**. Both representations admit \(k=0\); their maximum vector counts were 11 (reduced) and 12 (unreduced). This regenerates the mathematical classes; no comparison with the unavailable stored pattern file is claimed.
2. Symbolically checked the Pauli trace/anticommutator identities, \((n\cdot\sigma)^2=|n|^2I\), both corner radius identities, and the three-field norm identity used by the external mean bound. Also checked
   \[
   [(I\pm n\cdot\sigma)\otimes(I\pm n\cdot\sigma)]
   (e_+\otimes e_--e_-\otimes e_+)
   =(1-|n|^2)(e_+\otimes e_--e_-\otimes e_+),
   \]
   which directly distinguishes the U and D support rules.
3. Independently reconstructed two covered turning patterns: arrival and three corners removed; E, N, W neighbours U; NW corner respectively U or D with both its internal bonds; three bonded covering tips. After tip reduction, \(k=5\). Compared the coefficient formula with a separate expansion of the spin polynomial at rational unit slots. Checked the inverted trace identity, real symmetry, spin commutators, pair support/exchange, integrality and the factor \(15D_0q\). The prescribed denominators were **6,328,125** and **10,546,875**. The U supported sector has full/central dimensions **24/7**; the D symmetric and exterior sectors have dimensions **24/7** and **8/3**. Their full and central characteristic polynomials have the same square-free parts. At \(c=187/200\), all 16 groupwise inversions in each example gave positive central forms by exact pivots. These are example checks, not the full archived H1 computation.
4. For a valid zero-vector example with one isolated D out-neighbour after passage deletion, \(\widehat Z_{\rm cur}=\widehat Z_{\rm next}=1\). At \(D_0=25\), \(c=187/200\), the central matrix is the positive **1-by-1** matrix \([4875]\), agreeing with \(15D_0q(1-c)\).
5. Tested the Bareiss recurrence on **56** symmetric integer matrices of sizes 0–6, with seed **271828**. Every computed trailing entry agreed with its bordered determinant and every defined division was exact. Six cases halted on a zero preceding pivot, as required. Checked seven Gram/residual examples of sizes 0–6, including rank-deficient lower-triangular Gram factors; their strictly dominant residuals gave positive exact pivots.

# Formalization notes

- Keep removal status X distinct from the zero letter of the D law. Removed sites have no variable, no law and no slot factor. The convention \(P_{ab}=0\) is a convenient total definition, not an extra integration site.
- Define the reduced polynomials on all vector coordinates before restricting them to spheres or balls. The coefficient tensor must represent genuine separate-affine polynomials. Prove the separate degree bound before using finite-moment covariance.
- Carry a partition into disjoint singleton/pair groups and an inversion bit per group. This makes the common sign on a retained pair explicit. Include both signs for every D-pair; discard only the U exterior factors justified by D.7.
- Embed the unnormalized sector basis into the full tensor basis by \(B_\epsilon\). The certificate matrix is a **form** \(B_\epsilon^*OB_\epsilon\). The operator-coordinate matrix would instead involve the inverse basis Gram matrix. The form needs no such inverse and remains integral. Adjoint identities in these bases use the inherited inner product.
- For D.9, prove eigenspace invariance and the weight-lattice assertion before iterating a ladder. The number of iterations is the nonnegative integer distance to \(\kappa\). The odd case must use \(+1/2\) as stated; the sign argument includes the step from \(-1/2\).
- Preserve the exact positive identity \(M_\epsilon=15D_0q B_\epsilon^*OB_\epsilon\). Validate coefficient integrality for any smaller proposed \(D_0\); integrality of a stored matrix alone would not identify its scale or origin.
- A Bareiss checker should reject a zero required divisor, check integer remainder zero, and update only trailing entries. The previous pivot is the denominator. The bordered-minor invariant in the text supplies the proof without pivoting.
- Distinguish the two empty cases: zero-dimensional matrix tests are vacuous, while \(k=0\) gives a scalar operator on \(\mathbb C\), hence a 1-by-1 central form. Treat empty products, empty sign assignments, disconnected retained networks and singular Gram factors explicitly.
- To obtain the numerical H1 theorem in Lean, the Section 8 coverage and witness assertions still need to be discharged against the regenerated mathematical objects. Appendix D supplies their sound implication and introduces no circular dependence on H1 or on a spectral-gap conclusion.

# ORCH-SUMMARY

- VERDICT: SOUND for Appendix D.
- Critical findings: 0; Major findings: 0; Minor findings: 0.
- All 12 labelled statements and intervening spin identities checked.
- No LaTeX repair required.
- Passage, leaf and covariance steps stay within degree four.
- Removed neighbours, zero effective vectors, k=0 and both weight parities are covered.
- U exterior sectors are killed; D exterior sectors are retained correctly.
- Central-to-full positivity follows from the stated ladder proof.
- Exact matrix scale is 15 D0 q; unnormalized bases are handled as forms.
- Gram/residual and Bareiss arguments are sound, including empty sizes and singular L.
- Independent enumeration reproduced 106101 / 184914 / 123339 and 7962 effective classes.
- Symbolic operator, sample-sector and exact elimination checks passed.
- Archived numerical witness files were not read or independently certified.
