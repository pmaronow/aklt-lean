VERDICT: SOUND WITH FIXES

Lane R2: `sec3-knabe.tex`, `sec4-mixing-to-gap.tex`, and `app-constants.tex`. Line references are to the frozen bundle. I read the remaining manuscript sources for context. The verdict concerns these reductions, conditional on the results from Sections 2 and 5–8 that they explicitly invoke; it does not independently recertify the computer-assisted inputs.

The finite-size inequalities, the cell comparison, and the shell propagation argument are mathematically sound after the local fixes below. In particular, I find the reading of MO94 Theorem 4.1 for a general finite single-spin space justified. It is an extension of the proof, rather than a literal application of its binary-spin statement. The size 57,600 and lack of attractivity create no obstruction. Details of this assessment appear below.

## 1. Findings

1. **Minor — division by zero in the weighted proof.**

   **Location:** `sec3-knabe.tex:105–112`, proof of Theorem 3.1 (`t:K`).

   **Exact claim:** For every function $\varphi$, the displayed Cauchy–Schwarz argument includes
   $$
   \sum_{a:Y_a>0}\frac{X_a^2}{Y_a}
   \ \geq\ \frac{(\sum_a X_a)^2}{\sum_a Y_a}.
   $$

   **Problem:** For $\varphi=1$, every $X_a$ and $Y_a$ is zero, so the quotient on the right is $0/0$. The preceding sentence handles an individual zero component, but not this zero total denominator. Full support does not exclude constant functions.

   **Repair:** First separate $\langle\varphi,\mathcal L\varphi\rangle=0$. Then $\sum_aY_a=0$, all $Y_a=0$, and positivity implies $A_a\varphi=B_a\varphi=0$; the desired operator inequality is immediate. Otherwise $\sum_aY_a>0$ and the displayed calculation is valid, with the individual quotients restricted to $Y_a>0$. This changes neither constant nor conclusion.

2. **Minor — the general finite-state statement needs a convention for trivial state spaces.**

   **Location:** `sec3-knabe.tex:7–14,43–48,119`, setup, Lemma 3.3 (`l:fibre`), and Theorem 3.1 (`t:K`); also `sec4-mixing-to-gap.tex:24` if empty cell sets are allowed.

   **Exact claim:** Arbitrary finite $S_x$ are allowed, and $\gamma(a,\sigma)$ is their conditional generator's spectral gap, used as a finite real number in $g(\ell)$ and the spectral inequalities.

   **Problem:** Taking every $S_x$ to be a singleton satisfies the positive-weight hypothesis but leaves no positive eigenvalue and no nonconstant test function. Even when the global product is nontrivial, a box containing only singleton coordinates has the same problem. The manuscript's gap definitions do not specify a convention for this case. In particular, positivity/irreducibility alone does not manufacture a smallest positive eigenvalue in a one-dimensional function space. The analogous issue occurs for $W=\varnothing$.

   **Repair:** The simplest intended restriction is $|S_x|\geq2$ in Section 3 and nonempty $W$ whenever a gap is a real number. Alternatively define the gap as an extended-real Poincaré constant with value $+\infty$ for a one-state chain, and handle zero generators separately. The frame application already has $|D_x|=12$ or 20 and nonempty boxes, so its conclusion is unaffected.

3. **Minor — the claimed success bound extends one step beyond its hypothesis.**

   **Location:** `sec4-mixing-to-gap.tex:101–103`, proof of Proposition 4.8 (`p:surgery`); compare Definition 4.7 (`d:W`) at line 81.

   **Exact claim:** Step $i$ is defined for $2\leq i\leq i_1=\lfloor s\rfloor+1$, and the last sentence of the step paragraph claims agreement on $D_i$ with probability at least $\delta$, conditionally on any prior configuration.

   **Problem:** The window estimate is assumed only for integer indices $i\leq s$. Always $i_1>s$, so the last step has no such lower bound when its incoming separator disagrees. The parenthetical qualification earlier in line 101 is correct, but it must also qualify the paragraph's concluding claim.

   **Repair:** State the probability lower bound only for $i\notin I_0$ with $i\leq s$. At $i=i_1$, use the described maximal-coupling kernel without asserting a positive success bound, and retain identical resampling when the incoming separator agrees. The proof uses success probabilities only for
   $$
   J=\{i:2\leq i\leq i_1-1,\ i,i+1\notin I_0\},
   $$
   all of whose indices satisfy $i\leq s$. Thus the proposition and its exponent $s-4$ remain valid.

4. **Minor — make the positive integer domain of the geometric parameter explicit.**

   **Location:** `sec4-mixing-to-gap.tex:61,70–81,90`, Lemma 4.6 (`l:shellgeom`), Definition 4.7 (`d:W`), and Proposition 4.8 (`p:surgery`).

   **Exact claim:** Definition 4.7 permits $l_0\in\mathbb N$, and Proposition 4.8 then uses $M_{\mathrm g}(l_0)$ supplied by a lemma whose hypothesis is $l_0\geq1$.

   **Problem:** If $0\in\mathbb N$, as in Lean's `Nat`, the definition does not supply the lemma's hypothesis. The statement also leaves the integer domain of $M$ implicit although the side is called $2M+1$.

   **Repair:** Specify $l_0\in\mathbb Z_{\geq1}$ and integer $M\geq1$, with integer thresholds enlarged when necessary. The actual input $l_0=20$ already satisfies this. No change to the argument is required.

5. **Minor — Appendix A overstates the provenance of the displayed global minima.**

   **Location:** `app-constants.tex:17`, row headed $\min_\pi c(\pi)$; its cited support is `app-local.tex:244–276` (`p:closed` and the three examples). Also compare `app-local.tex:288–303`.

   **Exact claim:** The minimum over straight patterns and the minimum over turning patterns have the displayed values $0.961240\ldots$ and $0.935565\ldots$, with provenance “closed forms.”

   **Problem:** The cited closed forms compute values for the decoupled subclass and the displayed examples. They do not establish lower bounds at these sharper values for every nondecoupled pattern. The exhaustive certificates described in the manuscript prove the weaker thresholds $961/1000$ and $187/200$. Their stored `float_bound` fields are explicitly diagnostic floating-point information, not the exact tests used in the proof. Thus the stated provenance establishes values of particular patterns, not the asserted global minima over the whole class.

   **Repair:** Rename the row “values of the displayed extremal decoupled patterns,” and give their exact fractions $3825127/3979368$ and $1071655/1145463$. If global minimality is intended as a theorem, supply lower-bound certificates at those fractions for the remaining patterns, including an appropriate semidefinite test where an eigenvalue vanishes. The main proof uses only the weaker certified constants and is unaffected.

There is no Critical finding. The finite-spin issue in Remark 4.5 is not a finding of an unproved or false implication: the extension is valid, with the additional formalization obligations recorded below.

## 2. Statement table

“Correct after fix” refers to the numbered findings, not to an additional hypothesis about the AKLT model. All external statements are understood for the fixed finite-state, positive-weight potential specified before them.

| Number and label | Location | Content | Verdict | Dependencies |
|---|---|---|---|---|
| Theorem 3.1, `t:K` | `sec3-knabe.tex:20–25` | Flat and quadratic-weight finite-size bounds without translation invariance | correct after fix | `l:commute`, `l:fibre`, `l:autocorr`, `e:sums`; Findings 1–2 |
| Lemma 3.2, `l:commute` | `sec3-knabe.tex:31–41` | Conditional expectations at nonadjacent distinct sites commute; their complementary projections have positive product | correct | Positive nearest-neighbor factorization `e:MRF`; conditional expectation is an orthogonal projection |
| Lemma 3.3, `l:fibre` | `sec3-knabe.tex:43–49` | Box operator has spectrum in zero together with $[g(\ell),\infty)$ | correct after fix | Conditional box gaps `e:gell`, orthogonal decomposition by exterior configurations, finite-dimensional spectral theorem; Finding 2 |
| Lemma 3.4, `l:autocorr` | `sec3-knabe.tex:53–74` | Autocorrelation monotonicity and periodic displacement bounds for symmetric unimodal integer weights | correct | Layer decomposition into centered intervals, overlap identity `e:T`, zero extension and periodization |
| Remark 3.5, `r:Kpins` | `sec3-knabe.tex:121–123` | Torus-realizable boundary values may be constrained; arbitrary planar boundary bounds suffice | correct | `e:gell`, nearest-neighbor conditional factorization |
| Lemma 4.1, `l:boxcell` | `sec4-mixing-to-gap.tex:15–21` | An even planar lift of a torus box is a square of one of two cell models | correct | `e:muD`, `e:muDW`; even $L,N,\ell$; parity-preserving translation and boundary assignment |
| Lemma 4.2, `l:compare` | `sec4-mixing-to-gap.tex:23–29` | Uniform single-cell gap $c_0>0$ and single-site gap at least $c_0$ times cell gap | correct | Positive weights, finite boundary alphabet, conditional Poincaré inequalities and tower property; nonempty volume convention |
| Theorem 4.3, `t:MOS21` | `sec4-mixing-to-gap.tex:39–47` | A sufficiently large-square window criterion implies strong mixing on all squares | correct | MOS94 Theorem 2.1, equation (2.2), and its Section 1 finite-state hypotheses |
| Theorem 4.4, `t:MO41` | `sec4-mixing-to-gap.tex:49–53` | Strong mixing at a sufficiently large scale gives a uniform heat-bath gap on compatible sets | correct | MO94 Theorem 4.1 with the valid finite-alphabet extension explained in `r:finiteS`; equivalence of gap and reversible $L^2$ decay |
| Remark 4.5, `r:finiteS` | `sec4-mixing-to-gap.tex:55–57` | Justification for using the MO94 argument with 57,600 states | correct | General conditional resampling, finite-energy block comparison, couplings based on equality, local Poisson clocks; MOS94 Section 1 and Theorem 3.2 support this reading |
| Lemma 4.6, `l:shellgeom` | `sec4-mixing-to-gap.tex:70–76` | At most one exceptional shell in the used range; other shells have at most $8l_0$ boundary cells | correct | Integer-radius geometry; $s$ sufficiently large depending on $l_0$ |
| Definition 4.7, `d:W` | `sec4-mixing-to-gap.tex:80–85` | Uniform TV bound below one on the interior part of an admissible shell | correct after fix | `e:shells`, $I_0$, finite-volume cell specifications; Finding 4 |
| Proposition 4.8, `p:surgery` | `sec4-mixing-to-gap.tex:89–104` | One boundary-cell change has TV influence at most $(1-\delta)^{M^{1/4}-4}$ on the remote region | correct after fix | `d:W`, `l:shellgeom`, finite energy, maximal coupling, DLR/tower identity, conditional probability multiplication; Findings 3–4 |
| Corollary 4.9, `c:gapcell` | `sec4-mixing-to-gap.tex:106–116` | Both window estimates imply uniform gaps on the two families of compatible cell volumes | correct | `p:surgery`, TV contraction under marginalization, triangle inequality, `t:MOS21`, `t:MO41` |
| Theorem 4.10, `t:mainW` | `sec4-mixing-to-gap.tex:122–132` | Both window estimates imply uniqueness and a uniform AKLT gap on all sufficiently large even tori | correct | `c:gapcell`, `l:boxcell`, `l:compare`, corrected `t:K`, `t:QD`, `e:QDrot` |

The proof of Theorem 1.1 at `sec4-mixing-to-gap.tex:134–135` introduces no additional numbered statement. Its assembly is correct conditional on `t:inputs`, `t:rec`, `t:cutMOS`, and `t:mainW`: all three computer hypotheses are asserted at the same pair of constants. I found no circular dependency in this assembly.

For completeness, the numbered equations in the lane were also checked:

| Equation label | Content and result of check |
|---|---|
| `e:MRF` (3.1) | A finite, strictly positive nearest-neighbor Gibbs density; normalizer is positive. Use the nontriviality convention of Finding 2 for real-valued gaps. |
| `e:gell` (3.2) | Minimum over finitely many placements and exterior configurations; well-defined after Finding 2. Full support means no conditional exterior event has zero mass. |
| `e:tkappa` (3.3) | Both formulas are correct and all denominators are positive for integer $\ell\geq2$. |
| `e:K` (3.4) | Both bounds follow from the operator argument; a nonpositive right side is harmless. |
| `e:autocorr` (3.5) | Correct also at the smallest circumference $L=\ell+1$, including $\ell=2,L=3$. |
| `e:T` (3.6) | Correct centered-interval overlap formula. Empty layers contribute zero and can be omitted. |
| `e:sums` (3.7) | All three sums are correct; additionally $r(0)-r(1)=\mathsf s$. |
| `e:sumB2` (3.8) | Correct ordered-pair expansions and periodic placement coefficients. |
| `e:Lsquare` (3.9) | Correct Loewner inequality: only nonadjacent, commuting projection products remain in the difference. |
| `e:SM` (4.1) | Correct single-boundary-change strong mixing condition, uniform over the entire marginal set; empty marginal convention needed. |
| `e:MOS22` (4.2) | The finite-scale condition used from MOS94; it is reached uniformly in all boundary conditions. |
| `e:shells` (4.3) | Correct definitions; $D_i$ is the integer-radius sphere with radius $\lfloor is\rfloor$, intersected with the square. |
| `e:W` (4.4) | A legitimate input on arbitrary exterior configurations, stronger than the restricted input needed in the coupling. |
| `e:prop21` (4.5) | Correct TV bound after the final-step qualification in Finding 3. |

Appendix A contains no numbered theorem-like statements. Its entire constant table was checked as follows; checking provenance is distinguished from rerunning the other lanes' computations.

| Appendix A line | Quantity | Assessment |
|---|---|---|
| 7 | $g_\star$ | Positivity follows from the fixed, finite, nonzero positive star operator. The displayed 0.047238 is explicitly numerical and is not needed. |
| 8 | $\gamma_\pm$ | Formula agrees with `e:icodod`; in particular $0<\gamma_-<\gamma_+<1$, as needed for positive cell weights. |
| 9 | $t(\ell),\kappa_\ell$ | Exact formulas verified. They are not used in `t:mainW`. |
| 10 | $c_0,\alpha$ | Positive uniform constants exist for both offsets; an explicit permissible $\alpha$ is given below. |
| 11 | $M_0^{(o)},m_0,C,\gamma$ | Correct existence/provenance. $M_0^{(o)}$ should be recorded as positive integers; constants may depend on the fixed potential and alphabet. |
| 12 | $l_0=20$ | Consistent with `t:cutMOS` and the even-$l_0\geq20$ geometry in Section 5. |
| 13 | 0.0707, 2.73, 1.22 | Rational rounding bounds in `l:removal` are in the safe direction. Their finiteness, rather than smallness, is what the window proof needs. |
| 14 | 0.82, 0.928, 1.36, 1.072 | Correct rational consequences of the $3/5$ mean bound and conditional independence in `l:response`. |
| 15 | $\bar\alpha=0.18094,\bar\beta=0.36751$ | Consistent with the upper bounds displayed in `l:response`. These terminate decimals are the bounds, not claims of equality with the underlying logarithmic expressions. |
| 16 | $c_{\mathrm s}=961/1000,c_{\mathrm t}=187/200$ | Exactly 0.961 and 0.935, and the same pair is used throughout the assembly. Exact certificate coverage is the external-to-R2 input `t:H1`. |
| 17 | Pattern minima | Qualification needed: Finding 5. Exact example values are correct. |
| 18 | $416114/444675$ | Equals $1-(169/385)^2/3$; the example really implies the stated obstruction to increasing $c_{\mathrm t}$. |
| 19 | $3/5,1/2,1/3$ | Agree with the leaf-mean radii; the diluted radius is a mean bound, not a replacement of the single-cell alphabet. |
| 20 | $q\leq0.98075$ | Correctly attributed to H2; the arithmetic comparison $0.85594872\leq0.98075^8$ holds exactly. Full trail certification belongs to Section 8. |
| 21 | $\rho(M_1)\leq0.98779$ | Consistent with the stronger bound 0.98777 asserted in `p:tail`. Full kernel certification belongs to Appendix C. |
| 22 | $\theta,A$ | Correct dependency: choose $q^2<\theta<1$, then the response prefactor $A\geq2$. These precede the window constants and all mixing/gap scales. |
| 23 | $c,L_0$ | Correct: $c=g_\star c_0m_0/4$ and $L_0=\ell+2$ with an admissible even $\ell$. |

## 3. Formalization notes

### Finite-size operator argument

- **State spaces and support.** Use explicitly inhabited finite types with the nontriviality convention in Finding 2. Strictly positive site and bond weights imply a positive partition function and positive mass for every configuration and exterior fiber. These facts are needed before taking conditional expectations or minima of gaps.
- **Generator sign and normalization.** Section 2 calls $\sum_x(E_x-1)$ the Markov generator; Section 3 uses its negative $\mathcal L=\sum_x(1-E_x)$. Gaps here refer to the nonnegative operator. Each site or cell updates at rate one. Replacing a sum by the average over sites or cells would invalidate the scale comparisons without compensating factors.
- **Conditional expectation.** On the finite weighted function space, $E_x^*=E_x=E_x^2$; thus $Q_x=1-E_x$ is an orthogonal projection and $\mu(\operatorname{Var}_xF)=\lVert Q_xF\rVert_2^2$. Conditional independence of nonneighbors proves commutation even when they share neighbors.
- **Fibers.** The subspace supported on an exterior value $\sigma$ is identified with conditional $L^2$ by including a factor $\mu(\sigma)^{-1/2}$. Without this scaling, the natural extension-by-zero map has squared norm multiplied by $\mu(\sigma)$. The orthogonal direct-sum argument is otherwise correct.
- **Kernels.** Positivity gives $\ker(\sum_x a_xQ_x)=\bigcap_x\ker Q_x$ when every $a_x>0$. This supplies equality of the weighted and unweighted box kernels, as well as the zero cases in Finding 1. Full support gives irreducibility by changing one coordinate at a time, hence the global kernel consists of constants.
- **Placement counts.** Formalize the injective embedding of $\{1,\ldots,\ell\}$ into $\mathbb Z_L$ for $L\geq\ell+1$, extension by zero, and convolution on the cyclic group. Then $\sum_aA_a=\ell^2\mathcal L$, $\sum_aB_a=\mathsf s^2\mathcal L$, and $W(d)=r_L(d_1)r_N(d_2)$ follow by finite-sum reindexing. This uses no invariance of the measure.
- **Periodic autocorrelation.** The essential identity is $r_L(k)=r(k)+r(L-k)$ for $0\leq k<L$. Do not replace it with the nonperiodic autocorrelation: for $L=\ell+1$ both terms can be nonzero. In the layer proof restrict to nonempty $I_h$; the other layers vanish. Integer values of $u$ are used for this layer decomposition; both actual weights satisfy that hypothesis.
- **Loewner order.** Adjacent $Q_xQ_y$ need not be positive or selfadjoint. In (3.9) their coefficients cancel exactly. Every remaining product is a commuting projection product with a nonnegative scalar coefficient, so the inequality is justified. Ordered pairs can instead be grouped to make selfadjointness explicit.
- **Complex scalars.** $X_a,Y_a$ are real nonnegative quadratic forms. The Cauchy–Schwarz step should use absolute squares of complex inner products before identifying the inner product with $X_a$.
- **Constants.** Writing $\mathsf s=\ell(\ell+1)(\ell+2)/6$, the identities give $r(0)-r(1)=\mathsf s$. Consequently
  $$
  \frac{\ell^2r(0)(r(0)-r(1))}{\mathsf s^4}=t(\ell),\qquad
  \frac{\mathsf s^4}{\ell^2r(0)r(1)}=\kappa_\ell.
  $$
  All denominators are positive for $\ell\geq2$. At $\ell=2$ the quadratic weights are constant, and both criteria reduce to $2g(2)-1$. Also $t(8)=82/1125=0.072888\ldots$, consistent with the rounded example.

### Cells, finite energy, and the finite-spin extension

- **Two offsets suffice.** A lower-left corner whose second coordinate is odd can be translated by $(1,1)$, preserving checkerboard parity. The parity difference between its coordinates then determines offset 0 or 1. Define the identification of each cell with the four coordinates of $S^{(o)}$ explicitly; this is an identification of tuples, not of individual vectors.
- **Lifting the torus box.** Since $L,N,\ell$ are even, the assumption $\ell\leq\min(L,N)-1$ actually gives $L,N\geq\ell+2$. Hence there are no extra internal wrap bonds or incompatible adjacent exterior letters. Even torus periods also preserve the checkerboard under the lift. The possible repeated exterior images discussed in Remark 3.5 are harmless for the general unblocked criterion.
- **Uniform finite energy can be made explicit.** Put $a=1-\gamma_+$ and $b=1+\gamma_+$. A cell has four internal and eight crossing bonds. Its product of site weights is constant over its 57,600 states. Therefore one may take
  $$
  \alpha=\frac1{57600}\left(\frac ab\right)^{12}\in(0,1).
  $$
  This works for both offsets and every exterior configuration. A bound under conditioning on all other cells also holds under partial conditioning by the tower property. Iterating this proves that a prescribed configuration of a finite cell set $A$ has conditional probability at least $\alpha^{|A|}$.
- **Cell comparison.** A single cell has eight exterior nearest-neighbor sites. There are finitely many boundary tuples, every legal one-coordinate move has positive rate, and each resulting chain is irreducible. Taking the minimum of their positive gaps proves $c_0>0$. Tensorization is not being assumed: apply the conditional single-cell Poincaré inequality, average, and then apply the cell-chain Poincaré inequality. This yields exactly the factor $c_0$, with no volume factor.
- **Assessment of Remark 4.5.** I checked MO94's proof of Theorem 4.1, pp. 471–475. Its equality-based coupling extends to a finite alphabet; its separate remark about attractive couplings is unnecessary for this theorem. The binary logistic rate is replaced by conditional resampling. This supports the manuscript's reading. A Lean development must state the extension, rather than instantiate a theorem whose spin type is fixed to two points. [MO94, author-hosted copy](https://www.researchgate.net/profile/Fabio-Martinelli-3/publication/38331613_Approach_to_equilibrium_of_Glauber_dynamics_in_the_one_phase_region_I_The_attractive_case/links/00463528e86eaf3483000000/Approach-to-equilibrium-of-Glauber-dynamics-in-the-one-phase-region-I-The-attractive-case.pdf).
- **An independent finite-alphabet comparison node.** For the finitely sized cubes $Q$ of a block cover, let $\beta>0$ be the minimum conditional single-site gap over their exterior values. If each site belongs to at most $b_0$ covering cubes, conditional Poincaré inequalities give
  $$
  \sum_Q\mu(\operatorname{Var}_QF)
  \leq\frac{b_0}{\beta}\sum_x\mu(\operatorname{Var}_xF),\qquad
  \operatorname{gap}_{\rm site}\geq\frac{\beta}{b_0}\operatorname{gap}_{\rm block}.
  $$
  Finite energy and finiteness give $\beta>0$ for any finite alphabet. This supplies the needed comparison without a two-spin flip identity. Optimal couplings, their conditional completions, and local clock constructions likewise make sense for every finite alphabet.
- **Metric and threshold conventions.** MOS94 uses the maximum norm, matching this manuscript. MO94's original setup uses Euclidean distance; convert a maximum-norm bound with exponent $\gamma$ to a Euclidean one with exponent $\gamma/\sqrt2$ before applying its threshold, or absorb this into the definition of $M_*$. If the original threshold is strict, choose an integer strictly above it. These changes affect only existence constants.

### Shell surgery and assembly

- **Integer geometry versus real scales.** Treat $s=M^{1/4}$ as real, $i,k_i,i_1$ as integers, and prove $k_i=\lfloor is\rfloor$ directly from $is-1<k_i\leq is$. Choose $M_{\mathrm g}$ large enough to ensure $s\geq4$, $s/3>l_0$, and $s^2+4s/3<M$, as well as $s^2+s<M/2$. Those explicit eventual inequalities justify all the geometry estimates.
- **Exceptional index.** In the used range, any corner approached by a shell has distance less than $M$ from $y$. There is at most one such corner. Distinct radii differ by at least $\lfloor s\rfloor>2s/3$, so this corner cannot create two exceptional indices. For an ordinary shell, parallel sides stay away from the boundary strip. Each perpendicular side/edge pair contributes at most $l_0$ cells; four sides and two perpendicular edges give $8l_0$. Counting multiplicities only increases this upper bound.
- **Separator property.** The exterior cells interacting with $F_i$ belong to $D_{i-1}$ or to the common outside boundary. The changed site $y$ is too far from $F_i$ for $i\geq2$ and large $M$. Thus agreement on $D_{i-1}$ gives identical conditional measures on $F_i$. This is a range-one Markov property, not a mixing assertion.
- **Surgery is a kernel statement.** Define each component's marginal conditional law for every incoming pair, including the completion after coupling $B_i$. Positivity makes every conditioning event possible. Resampling $A_i$ afterward preserves these marginal laws even though it changes their dependence. The DLR/tower identity then preserves the original two full-volume marginals under every surgery.
- **Why the exponent is $16l_0$.** Conditional on agreement on $B_i$, choose one fixed configuration on $A_i$. Each independent last resampling assigns it probability at least $\alpha^{|A_i|}$, so their agreement probability is at least $\alpha^{2|A_i|}$. Hence $\delta=p_0\alpha^{16l_0}$ works. Empty $A_i$ or $B_i$ cause no difficulty. With the displayed choice of $\alpha$, $0<\delta<1$, so all real powers are defined.
- **No independence of trials is needed.** The number of available indices is $i_1-2$. The single exceptional index removes at most two opportunities from $J$, giving $|J|\geq i_1-4\geq s-4$. The conditional failure probability at each index in $J$ is at most $1-\delta$, even conditional on earlier failures. Iterated conditioning proves the product bound.
- **Persistence of agreement.** Success at $i\in J$ followed by step $i+1$ gives agreement throughout $F_{i+1}$. Every later unskipped surgery has an already agreeing separator; skipped surgeries do nothing. Moreover $F_{i_1}\supseteq\mathcal Q$ because $(i_1-1)s\leq s^2$. This verifies both the skipped-index issue and the final-index issue after Finding 3.
- **Arbitrary exterior disagreements.** Only the outer maximum-norm ring matters; its size is $8M+8$. Boundary conditions differing at infinitely many other cells can be replaced on that ring one cell at a time. The fixed target $\mathcal Q_{M,\eta,\eta'}$ is a subset of each relevant one-change remote region, so TV contraction under restriction and the triangle inequality apply. The bound $(8M+8)(1-\delta)^{M^{1/4}-4}\leq M^{-4}$ holds eventually for every fixed $0<\delta<1$; it does not require a usable numerical size threshold.
- **Empty marginal sets.** The law on the empty configuration is a point mass, with TV distance zero. Either exclude empty $\Delta$ in the distance formulation of strong mixing or define its distance to a site as $+\infty$. In particular, if $\eta=\eta'$ the universal condition defining $\mathcal Q$ is vacuous and $\mathcal Q=\mathcal C_M$, which is harmless since the measures coincide.
- **Compatible square sizes.** Write $b_o=2M_0^{(o)}+1$. The product $K=b_0b_1$ is an admissible common multiple; it need not be the least one. A square with $kK$ cells on a side tiles by $b_o$-squares after translation for either offset. With $\ell=2kK\geq2/(c_0m_0)$, all box gaps are at least $c_0m_0$ and
  $$
  \lambda(\mu_D)\geq\frac{\ell}{\ell-1}
       \left(c_0m_0-\frac1\ell\right)
       \geq\frac{c_0m_0}{2}.
  $$
  Combining this with the quantum comparison $g_\star\lambda(\mu_D)/2$ gives $g_\star c_0m_0/4$, exactly as stated. The even-size requirement ensures $L,N\geq\ell+2\geq4$.
- **Dependency order.** The model, $\alpha,c_0,g_\star$ are fixed first. The response constants give the window constants; these give $\delta$, then mixing constants, then compatible scales and $m_0$, and finally $\ell,L_0,c$. Choosing the final box size does not change any earlier constant.

### Small computations

The accompanying `audit_checks.py` ran successfully with Python 3.12; its output is `audit_checks.json`. It used exact integer/rational arithmetic, one process, and no manuscript-program imports. It checked the sum and prefactor identities for 99 sizes, all 246 symmetric unimodal sequences with entries in $\{0,1,2,3\}$ at lengths 2–10, 2,379 corresponding periodic cases, 20,261 shell-index/count cases, and the rational rounding comparisons identified above. These are finite checks supporting the analytic audit, not substitutes for the general proofs. I did not rerun the large H1/H2/H3 computations. No floating-point numerical experiment is used to justify the lane verdict.

## 4. External inputs

The reference papers were checked through the authors' copies, not through any search for the submitted manuscript or its programs. The following states the results as used; short quotations identify the relevant hypotheses.

1. **MOS94: finite-scale criterion and generality.**

   **Paper locator:** Theorem 2.1 and (2.2), p. 38; definitions in Section 1, pp. 35–37, especially (1.10); definition of $Q$ immediately before Proposition 2.1, pp. 37–38.

   **Hypotheses:** finite $S=\{1,\ldots,N\}$, real-valued potential, “Finite range” and “Translation invariance,” on $\mathbb Z^2$. As used: at some sufficiently large $M$, all pairs of exterior configurations have marginal TV distance at most $M^{-4}$ on the region farther than $M^{1/2}$ from every disagreement. Conclusion: constants $C,\gamma>0$ give (4.1) on all squares.

   **Applicability:** The blocked model has exactly this finite-state, real-potential, range-one setting. Corollary 4.9 supplies the criterion uniformly. No weak mixing assumption is additionally required once this criterion is verified. The finite-alphabet statement in Theorem 3.2(ii)$\Rightarrow$(iv), pp. 43–44, also corroborates the intended gap consequence. [MOS94, author-hosted copy](https://www.researchgate.net/profile/Fabio-Martinelli-3/publication/38331702_For_Gibbs_state_of_2D_lattice_spin_systems_weak_mixing_implies_strong_mixing/links/00463528e86eac3c5c000000/For-Gibbs-state-of-2D-lattice-spin-systems-weak-mixing-implies-strong-mixing.pdf).

2. **MO94: mixing to a gap.**

   **Paper locator:** Theorem 4.1, p. 471; heat-bath rates (4.1), p. 470; block comparison (4.5), p. 472; proof through p. 475. The manuscript gives these locators.

   **As used:** For a fixed finite-state positive Gibbs specification, sufficiently large-scale $\mathrm{SM}(\mathcal C_{M_0},C,\gamma)$ implies a uniform positive gap on all $M_0$-compatible finite volumes and all boundary conditions, with rate-one conditional resampling.

   **Applicability:** The printed Section 4 specializes to binary spins “for simplicity”; Theorem 4.1's proof explicitly allows a system “not necessarily ferromagnetic.” Its finite-alphabet extension is valid by the argument in Section 3 of this report. Account for the metric convention there. [MO94, author-hosted copy](https://www.researchgate.net/profile/Fabio-Martinelli-3/publication/38331613_Approach_to_equilibrium_of_Glauber_dynamics_in_the_one_phase_region_I_The_attractive_case/links/00463528e86eaf3483000000/Approach-to-equilibrium-of-Glauber-dynamics-in-the-one-phase-region-I-The-attractive-case.pdf).

3. **MOS94: source of the surgery construction.**

   **Paper locator:** Proposition 2.1, pp. 38–41; surgery on p. 39; the window bound (2.8) on p. 40. These are the manuscript's locators.

   **As used:** A local conditional resampling of the two components of a coupling preserves their Gibbs marginals. A uniform positive chance of matching a separating shell can be iterated to bound remote disagreement.

   **Hypothesis check:** The original proposition obtains its window bound from weak mixing. The present proposition instead assumes `d:W` and proves the necessary implication itself. That substitution is legitimate: the reproduced proof needs no further consequence of weak mixing. The exceptional-index geometry is also proved in the manuscript. Finding 3 is a local qualification of the reproduction, not a failure of this substitution.

4. **Knabe (1988) and Gosset–Mozgunov (2016).**

   **Paper locator given:** Bibliographic citations at `sec3-knabe.tex:3`, without a theorem or equation locator.

   **Use:** Motivation and the weighted-proof template. No published finite-size theorem is imported as a black box. The manuscript derives both required inequalities from the three lemmas and the placement Cauchy–Schwarz argument. Thus a translation-invariance hypothesis of another criterion is not being silently applied to $\mu_D$; the proof here does not need it.

5. **Finite-state conditional expectation and Gibbs consistency — standard input, no external locator given.**

   For a strictly positive probability distribution on a finite product, conditional expectation given the complementary coordinates is an orthogonal projection. Conditional resampling preserves the measure; conditioning successively satisfies the tower identity. A nearest-neighbor positive Gibbs density depends on the exterior only through adjacent exterior coordinates. All these hypotheses hold here, and they prove the commutation, fiber, cell, and surgery identities used in the lane.

6. **Finite-dimensional spectral theory and Poincaré inequalities — standard input, no external locator given.**

   A nonnegative selfadjoint finite-dimensional operator whose kernel consists of constants has gap at least $c>0$ exactly when its quadratic form dominates $c\operatorname{Var}$. Equivalently, its nonzero eigenvalues are at least $c$, or its square dominates $c$ times the operator. For the negative generator this is equivalent to $L^2$ semigroup contraction with factor $e^{-ct}$. Finite positive conditional resampling chains are irreducible. These uses are valid after the trivial-space convention in Finding 2.

7. **Coupling facts — standard input, no external locator given.**

   On a finite set, two laws admit a maximal coupling whose disagreement probability equals their total variation distance. Every coupling gives TV at most its disagreement probability. Marginalization cannot increase TV, and TV satisfies the triangle inequality. Conditional completions of a coupled marginal recover the full prescribed laws. Positive mass makes all the conditional completions in this proof well-defined. The product bound on successive failures follows from conditional probability, with no independence assumption.

8. **Elementary finite sums and eventual inequalities — standard input, no external locator given.**

   Reindexing finite sums, Cauchy–Schwarz with positive denominators, positivity of products of commuting projections, and finite sums of positive operators are used exactly as identified in Section 3. The only asymptotic step in the coupling-to-criterion reduction is that fixed exponential decay in $M^{1/4}$ eventually dominates any fixed power of $M$. These have their usual hypotheses, with the zero-denominator case supplied by Finding 1.

The inputs `t:QD`, `t:cutMOS`, `t:rec`, and `t:inputs` are internal manuscript dependencies, not additional external theorems. Their precise role in this lane is recorded in the statement and constant tables above.
