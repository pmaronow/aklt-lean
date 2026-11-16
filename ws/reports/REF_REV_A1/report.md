VERDICT: GAP

Reviewed `part/check-wrapper.tex`, `part/sec1-result.tex`, and `part/sec3-quantum-frames.tex` against `interfaces.tex`, all under `/home/ubuntu/aklt/review/REF_REV_A1/`. Locations below are relative to that directory. No inputs were modified. No other manuscript material or web sources were needed.

The algebraic uniqueness proof, frame construction, quantum comparison, finite-energy estimates, and square lift survive the checks below. The proof of the uniform-gap clause of `t:main` stops at an unavailable theorem, `t:mainW`. A second unavailable reference, `l:density`, has a short self-contained repair. The verdict concerns missing justification under the supplied interface contract; no false numerical bound or counterexample to the stated conclusions was found.

1. **Major — The uniform-gap conclusion invokes a theorem absent from the permitted inputs.**

   **Location:** `part/sec1-result.tex:30`, label `t:main`, especially `part/sec1-result.tex:50`–`51`; also the corresponding proof outline at `part/sec1-result.tex:73`–`90`.

   **Exact claim:** “Theorem~\ref{t:mainW} supplies \(c>0\) and an integer \(L_0\ge3\) with the asserted spectral bound for all integers \(L,N\ge L_0\).” The conclusion being justified is the existence of one positive lower bound for every nonzero eigenvalue on every sufficiently large torus.

   **Why justification fails:** Neither the assigned part nor any of the 1,188 lines of `interfaces.tex` states `t:mainW`, or an equivalent periodic block/site gap theorem. In particular, the interface's section entitled “Windows, stopped coupling, and the periodic block gap” contains `d:shells` and `d:W`, but no implication from (W) to a torus gap. The permitted chain does give

   \[
   \texttt{t:inputs}\Longrightarrow\texttt{t:rec}
   \Longrightarrow\mathsf P(A,\theta)
   \Longrightarrow\texttt{t:cutMOS}
   \Longrightarrow\mathsf W(64,p_0,M_\star).
   \]

   Those applications respect the supplied hypotheses: the thresholds are exactly \((961/1000,187/200)\), \(C_V=10\ge1\), the supplied rational \(q\) lies in \((0,1)\), and the typed kernel, orderings, and witness are the ones required by `t:rec`. The resulting \(A\ge2\) and \(0<\theta<1\) meet `t:cutMOS`. However, (W) is only a marginal-overlap estimate. The local results in Section 3 establish positivity of each finite torus gap and a quantum/classical comparison; they do not give a lower bound uniform in the periods. In particular, the block estimate \(r_b^{|E(Q)|}\) alone cannot supply the missing global implication.

   **Repair:** Supply a proved result from the responsible other part and include its exact statement in the permitted interface. The following is a sufficient contract. Its assertion here is a specification of the missing result, not a proof of it:

   ```latex
   \begin{theorem}\label{t:mainW}
   Suppose the plane frame family of Definition~\ref{d:framemodel}
   has \(\mathsf W(64,p_0,M_\star)\), where \(0<p_0\le1\) and
   \(M_\star\ge1\) is an integer. There exist \(\gamma>0\) and
   an integer \(L_0\ge3\), depending only on \(p_0,M_\star\)
   and the fixed frames, such that for every pair of integers
   \(L,N\ge L_0\), every proper torus three-colouring \(\kappa\),
   and every complex function \(f\) on its configuration space,
   \[
     \sum_{x\in\Lambda_{L,N}}
       \mu^{\mathrm{af}}_{\kappa,L,N}
          (\operatorname{Var}_x f)
     \ge \gamma\operatorname{Var}_{\mu^{\mathrm{af}}_{\kappa,L,N}}f.
   \]
   \end{theorem}
   ```

   With that contract proved and imported, replace the last two lines of the main proof by:

   ```latex
   Theorem~\ref{t:mainW} gives \(\gamma>0\) and an integer
   \(L_0\ge3\), uniformly in the periods and colouring.
   Lemma~\ref{l:colour} supplies a proper colouring for every
   \(L,N\ge L_0\). Theorem~\ref{t:QD} then gives the asserted
   bound with \(c=g_\star\gamma/2>0\).
   ```

   Alternatively, import a proved theorem with the direct quantum conclusion used by the present text. Adding an unproved statement or assuming (W) alone does not close this finding. The nonvanishing and uniqueness clauses of `t:main` are unaffected.

2. **Minor — The density comparison used for the exported block-gap bound is not supplied.**

   **Location:** `part/sec3-quantum-frames.tex:704`–`705`, label `l:planeenergy`, and its proof at `part/sec3-quantum-frames.tex:762`–`770`, especially the reference at line 764.

   **Exact claim:** “The density comparison of Lemma~\ref{l:density}” gives a conditional block Poincare gap at least \(m_Q/M_Q=r_b^{|E(Q)|}\).

   **Why justification fails:** `l:density` occurs in neither the assigned files nor `interfaces.tex`. Thus the precise comparison being cited, including its hypotheses and constant, is not available under the supplied contract. This concerns an exported statement: `interfaces.tex:270`–`271` repeats the block-gap assertion. The comparison constant used here is correct, and all the needed positivity hypotheses are established. This is a local missing proof/import, repairable without changing the statement or constant.

   **Repair as exact LaTeX:** Insert the following lemma and proof before `l:planeenergy`. Here conditional variances and Dirichlet forms have the rate-one-per-site convention already fixed in the part.

   ```latex
   \begin{lemma}\label{l:density}
   Let \(\Omega=\prod_{x\in Q}A_x\) be a finite product of
   nonempty finite sets, and let \(\nu=\bigotimes_{x\in Q}\nu_x\)
   be a strictly positive product probability. Let \(\mu\) be a
   probability on \(\Omega\) such that
   \[
     0<m\le\frac{\mu(s)}{\nu(s)}\le M<\infty
     \qquad(s\in\Omega).
   \]
   Then, for every complex function \(f\),
   \[
     \mathcal D_\mu(f)\ge\frac mM\operatorname{Var}_\mu f.
   \]
   \end{lemma}

   \begin{proof}
   For any positive finite probability \(\xi\), conditional
   expectation minimizes squared distance to functions of the
   exterior letters. Hence
   \[
     \xi(\operatorname{Var}_x^\xi f)
       =\min_{g=g(s_{Q\setminus\{x\}})}\xi(|f-g|^2),
     \qquad
     \operatorname{Var}_\xi f=\min_{c\in\mathbb C}\xi(|f-c|^2).
   \]
   The density bounds therefore give
   \[
     \mathcal D_\mu(f)\ge m\mathcal D_\nu(f),\qquad
     \operatorname{Var}_\mu f\le M\operatorname{Var}_\nu f.
   \]
   Product probabilities satisfy
   \(\operatorname{Var}_\nu f\le\mathcal D_\nu(f)\).
   To see this, induct on \(|Q|\), using total variance at one
   coordinate \(y\), the induction hypothesis on the other
   coordinates, and
   \[
     \nu(\operatorname{Var}_x^\nu E_y^\nu f)
       \le\nu(\operatorname{Var}_x^\nu f)\quad(x\ne y).
   \]
   The last inequality is Jensen's inequality, since the product
   conditional expectations at distinct coordinates commute.
   Consequently
   \[
     \mathcal D_\mu(f)\ge m\mathcal D_\nu(f)
       \ge m\operatorname{Var}_\nu f
       \ge\frac mM\operatorname{Var}_\mu f.
   \]
   If \(Q=\varnothing\), all these variances and Dirichlet forms
   vanish, so the assertion also holds in that case.
   \end{proof}
   ```

   In the existing application, \(\nu_Q\) is strictly positive because every boundary factor is in \([b,2-b]\). Also \(R>0\), \(\nu_Q(R)>0\), and

   \[
   m_Q=\frac{b^e}{\nu_Q(R)},\qquad
   M_Q=\frac{(2-b)^e}{\nu_Q(R)},\qquad
   \frac{m_Q}{M_Q}=r_b^e,
   \quad e=|E(Q)|.
   \]

   Thus the proposed lemma applies exactly. Fixed sites inside \(Q\) reduce the free edge set, improving this bound since \(0<r_b<1\). Empty blocks and blocks with no internal edges are included.

The statement table follows. “Sound” means sound relative to the explicitly supplied interfaces and ordinary finite-dimensional linear algebra and polynomial algebra. The two unavailable references are assessed separately above. Section labels are structural, and the wrapper introduces no mathematical statement.

| Label and location | Content checked | Verdict | Dependencies |
| --- | --- | --- | --- |
| `d:model`, `part/sec1-result.tex:7` | Simple torus, spin-2 tensor space, oriented determinants, valence-bond polynomial, sum of spin-four projections, positive-eigenvalue gap | Sound; degree-four membership of the polynomial is proved later | `d:poly`; torus periods at least three |
| `t:main`, `part/sec1-result.tex:30` | Nonzero state and unique kernel for all periods at least three; uniform positive spectral bound for all sufficiently large periods | Uniqueness sound; uniform-gap proof has the Major gap in finding 1 | `p:toruskernel`; imported `t:inputs`, `t:rec`, `t:cutMOS`; missing `t:mainW` |
| Unlabelled conventions, `part/sec1-result.tex:100` | Complex inner products, quadratic-form order, empty sets, ambient distances, total variation, complex variances, singleton Poincare convention, site rates | Well-posed and consistent with subsequent uses | Finite sums; extended value for the empty Rayleigh infimum |
| `d:poly`, `part/sec3-quantum-frames.tex:14` | Homogeneous binary polynomials, inverse-binomial squared norms, dual SU(2) action, finite spinor choices | Sound | Nonnegative integer degree; unitary dual tensor action; Pauli identities |
| Unlabelled justification, `part/sec3-quantum-frames.tex:25`–`76` | Symmetric-tensor normalization, irreducibility, spin identification, existence of the finite spinor choices, multihomogeneous tensor realization | Sound, including degree zero | Distinct torus-subgroup eigenvalues; invariant-subspace closedness; the two displayed infinitesimal actions; rank-one Hermitian projection |
| `l:edge`, `part/sec3-quantum-frames.tex:78` | Edge kernel is exactly determinant times endpoint bidegree `(3,3)`, with other degrees four | Sound | `d:poly`; equivariant surjective diagonal map; dimensions 25, 9, 16; polynomial integral domain; unique spin-four copy |
| `l:divisibility`, `part/sec3-quantum-frames.tex:137` | Simultaneous incident-edge divisibility; quotient independent of sites in `R` | Sound for zero vectors and empty `R` as well | `l:edge`; four distinct neighbours for periods at least three; Gauss's lemma, polynomial UFD, nonassociate primes, multigrading |
| `p:toruskernel`, `part/sec3-quantum-frames.tex:191` | Nonzero valence-bond polynomial, one-dimensional kernel, orientation independence | Sound, including either period equal to three | `l:edge`, `l:divisibility`; positivity of orthogonal projections |
| `l:star`, `part/sec3-quantum-frames.tex:223` | Fixed positive local star gap; local projection inequality; sum of stars equals twice the Hamiltonian | Sound | Highest-weight eigenvector of eigenvalue four; finite-dimensional spectral theorem; five distinct star sites; each edge counted twice |
| `d:frame`, `part/sec3-quantum-frames.tex:264` | Positive finite degree-four moment frame | Sound | Imported `d:moment`; complex extension by real and imaginary parts |
| `l:tight`, `part/sec3-quantum-frames.tex:274` | Factor-five tightness and tensor evaluation isometry | Sound with the stated inverse-binomial normalization | `d:poly`, `d:frame`; imported `l:moments` only through degree four; finite tensor products |
| `l:threeframes`, `part/sec3-quantum-frames.tex:341` | Three antipodal frames; exact separation bounds, attainment, disjointness up to signs; `0 < r_b < 1` | Sound | Imported `d:moment`, `l:moments`; explicit orthogonal rotation; vertex dot products and triangle inequality |
| `l:colour`, `part/sec3-quantum-frames.tex:434` | Proper torus three-colouring from the two cycle colourings | Sound for every odd/even combination, including period three | The explicitly defined `a_m`; addition in `Z/3Z` |
| `l:qmod`, `part/sec3-quantum-frames.tex:458` | Determinant squared modulus equals `(1-a·a')/2` | Sound | Unit spinors, their projection identities, Gram determinant, Pauli traces |
| `d:framemodel`, `part/sec3-quantum-frames.tex:490` | Antiferromagnetic torus and positive-interaction plane laws; full support; conditional variance and rate-one site gap | Sound, including the empty plane volume | `l:threeframes`; proper colourings and admissible exterior letters; positive finite sums |
| Unlabelled operator facts, `part/sec3-quantum-frames.tex:519`–`544` | Conditional expectation is an orthogonal projection; Dirichlet norm identity; positivity of each nontrivial finite site gap; nonzero determinant evaluations | Sound; no size-uniform gap is asserted here | Full product support; coordinate paths between configurations; spectral theorem; `l:qmod`, `l:threeframes` |
| `l:quantumfibre`, `part/sec3-quantum-frames.tex:546` | Orientation-correct fibre factorization; unitary ground-state multiplication; heat-bath intertwining; projection norm bound | Sound | `l:tight`, `l:qmod`, `l:threeframes`, `l:divisibility`; strictly positive ground-state weights; inclusion of evaluated local kernel in fibre range |
| `e:frame-ground-weight`, `part/sec3-quantum-frames.tex:583` | Unnormalized weight identity with factor `5^{|Λ|} 2^{-|E|}` | Sound | `l:qmod`; product reference weights; one determinant for each edge |
| `e:frame-ground-law`, `part/sec3-quantum-frames.tex:592` | Normalized squared ground-state evaluations equal the torus probability | Sound | Previous equation; `l:tight`; `||B|| > 0` |
| `t:QD`, `part/sec3-quantum-frames.tex:646` | Quantum gap at least `(g_star/2) λ(μ_af)`, and the ground-state probability identity | Sound | `l:quantumfibre`, `l:star`, `p:toruskernel`; complex Poincare inequality; isometry; positive, finite torus site gap |
| `l:planeenergy`, `part/sec3-quantum-frames.tex:691` | Conditioning consistency, Markov property, one-letter lower bound `α`, assignment bound `α^k`, block gap `r_b^{|E(Q)|}` | First three assertions sound; last assertion has the local missing-reference repair in finding 2 | `d:framemodel`, `l:threeframes`; averaging and chain rule; product density comparison `l:density` absent from inputs |
| `l:boxlift`, `part/sec3-quantum-frames.tex:786` | Injection of the one-neighbourhood, exact internal/crossing bonds, local gauge transport, site-update intertwining, Hamming preservation | Sound at the inclusive threshold `L,N = 2M+3` and for odd periods | Integer radius convention; four distinct torus neighbours; proper pulled-back colouring; antipodal uniform alphabets; parity on the plane lift |

All seven local statement labels also present in `interfaces.tex` match their interface statements exactly after whitespace normalization: `d:model`, `d:poly`, `d:frame`, `l:tight`, `l:threeframes`, `d:framemodel`, and `l:planeenergy`. In particular, there is no silent weakening of an exported boundary or conditioning hypothesis. `l:planeenergy` still needs the missing proof/import identified above. The additional local lemmas and `t:QD` are proved within the assigned part. The only reference targets absent from the union of the part and the interface are the two findings.

The following exact checks support the audit; they supplement the proofs and do not replace arguments quantified over all sizes. They ran in one Python process, using rational arithmetic and exact arithmetic in `Q(sqrt(5))`, within the four-core limit.

- All 864 factors `1 ± a·a'` for the three unordered pairs of frames, their 144 pairs of letters, and both signs satisfy the bounds. The global minimum is exactly \((5-\sqrt5)/505\), and the maximum is exactly \(2-(5-\sqrt5)/505\). For frame pair `(0,2)`, the minimum is \((400-80\sqrt5)/10201\), which is larger than the common bound. Thus “attained” is correctly an assertion about the common bound, not about each pair separately.
- The diagonal coherent-state moments are exactly \((1/5,1/20,1/30,1/20,1/5)\); multiplication by five gives the five inverse binomial coefficients. The required second and fourth coordinate moments were also checked exactly.
- All 169 period pairs \(3\le L,N\le15\) have four distinct neighbours at each vertex, \(2LN\) unordered edges, and a proper colouring from `l:colour`.
- The lift's injection and internal/crossing edge correspondences were checked in 108 finite cases: \(1\le M\le4\), each period between \(2M+3\) and \(2M+5\), and three translations including negative coordinates and a placement across the chosen torus representatives.
- The rational `q` in `t:inputs` satisfies \(0<q<2499/2500<1\) exactly.

Formalization notes:

- Use a polynomial ring with two independent variables for every physical site, and preserve the multigrading when identifying it with the tensor product. In `l:edge`, “degree three in \(z_x,z_y\)” means degree three separately at each endpoint. Handle the zero polynomial before using degree subtraction, as the text already does.
- For the UFD step, determinants are primitive linear polynomials over the ring omitting one endpoint variable. Establish that the two coefficients have gcd one, and that different unordered endpoint sets give nonassociate prime elements. Divisibility by each prime then yields divisibility by their product, including an empty product.
- The SU(2) representation is the dual substitution action \(p(g^{-1}z)\). Retain that convention through the weight and adjoint calculations. The irreducibility proof uses complex invariant subspaces, finite-dimensional closedness when differentiating, and nonzero ladder coefficients only in the displayed index ranges. The degree-zero case is handled separately.
- Apply the imported moment covariance only to polynomials of degree at most four. The tightness proof does this: every \(P_{jk}\) has that degree bound, even though its expression originates from degree-four spinor polynomials and their conjugates. Extend the real moment identities to complex polynomials componentwise.
- Keep the reference measure \(\pi\) distinct from a probability: its mass is \(5^{|\Lambda|}\). The physical map \(\iota\) is an isometric embedding; ground-state multiplication \(U\) is a unitary map between the two full finite function spaces. Evaluation of the residual \(\chi\) is defined polynomial evaluation, not an application of the degree-four isometry to a vector of the wrong degree.
- All divisions in the fibre formulas are legitimate: \(\|B\|>0\), every evaluated determinant has squared modulus at least \(b/2>0\), and every weighted fibre norm of \(\beta_x\) is positive. Only the inclusion \(\iota\mathcal S_x\subset\operatorname{Ran}\mathcal P_x\) is needed; the contraction argument does not require equality of those subspaces.
- The factor in `t:QD` is exactly \(g_\star/2\). The two comes from \(\sum_xH_x=2H\); every site generator has rate one. A star at period three still consists of five distinct tensor factors, even if some of its neighbours are themselves adjacent.
- The singleton convention uses an extended-valued infimum. Express Poincare assertions directly as inequalities in empty/singleton blocks. On the torus, full support on more than one configuration gives a finite positive \(\lambda\), so `t:QD` involves no multiplication of zero by infinity.
- The lower bound under partial conditioning concerns positive events determined off the target site. The assignment bound uses distinct sites and gives probability one when \(k=0\). The block-gap proof fixes all exterior neighbour letters before absorbing boundary factors into product site weights. Its claimed density exponent counts internal edges only. Arbitrary sphere-valued pins are outside the finite-energy lemma's stated scope.
- In `l:boxlift`, treat \(M\) as an integer using the radius convention. Injection holds on \(A'=a+\{-M-1,\ldots,M+1\}^2\), while the induced-edge assertion concerns \(Q'\). At the smallest allowed periods there can be additional wraparound edges between exterior points of \(A'\); no induced-graph assertion for all of \(A'\) should be introduced. The proof only needs internal and crossing edges of \(Q'\).
- Define the gauge sign by the parity of the integer \(z_1+z_2\), including negative lifts. Every internal or crossing plane edge reverses that sign. Antipodality and uniform weights make this a bijection of the same site alphabets. All signs are attached to the plane lift, so the argument imposes no even-period hypothesis.
- Import `t:inputs`, `t:rec`, and `t:cutMOS` as the supplied interface theorems. Their certificate proofs are outside this review. The next global-gap node cannot be created from the supplied interface until finding 1 is resolved.
