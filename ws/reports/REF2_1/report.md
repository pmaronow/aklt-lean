VERDICT: SOUND

Scope: Sections 1 and 3. I read the complete LaTeX source, including the other sections and all four appendices, for context. The assigned sections were checked line by line. Results from other parts are accepted as stated, with their hypotheses and their use in the assigned sections checked. This verdict does not independently certify the computational assertions of Section 8 and Appendices C–D.

Source locations below are relative to `/home/ubuntu/aklt/review/REF2/paper/`.

## Numbered findings

None. Critical: 0; Major: 0; Minor: 0. I found no false statement, missing hypothesis, unjustified implication, or incorrect constant in the assigned sections. No LaTeX repair is required.

## Audit record

**Model and small periods — `sec1-result.tex:15`, `sec3-quantum-frames.tex:137`, labels `d:model`, `l:divisibility`, `p:toruskernel`.** The graph is explicitly simple, with unordered edges counted once. For periods at least three, the four neighbours of a site are distinct, including when one or both periods equal three. Thus every site has degree four and there are \(2LN\) edges. Period-three edges between different neighbours of a site do not enter its star operator. No bipartiteness is used for uniqueness. The valence-bond polynomial has degree four separately at every site, so it belongs to the stated physical Hilbert space. The definition of the quantum gap is well posed: the tensor \(\bigotimes_x z_{x,2}^4\) is fixed by every edge projection and has positive eigenvalue \(|E_{L,N}|=2LN\).

**Polynomial normalization and the edge kernel — `sec3-quantum-frames.tex:14–135`, labels `d:poly`, `l:edge`.** Averaging the distinct coordinate tensors gives precisely the monomial squared norm \(\binom dj^{-1}\). The inverse action \(p(g^{-1}z)\), the displayed weights, and both differentiated operators have consistent signs. The chosen diagonal group element has distinct eigenvalues; its polynomial spectral projections and the two ladder operators prove irreducibility, including the separately handled case \(d=0\).

The diagonal evaluation \(\Delta:V_4\otimes V_4\to V_8\) is equivariant and onto. Its kernel has dimension 16. Multiplication by \(q_{xy}\) is injective on the 16-dimensional space \(V_3\otimes V_3\), lands in that kernel, and therefore exhausts it. Unitarity makes \(\Delta^*\) an intertwiner. Its range is a spin-four copy, and the one-dimensional weight-four space proves uniqueness of that copy. This identifies the orthogonal projection in the model with the complement of the determinant-multiple space. Expanding in the other-site monomial basis legitimately extends the two-site statement to the full tensor product. Orientation reversal changes only a scalar sign.

**Simultaneous divisibility and uniqueness — `sec3-quantum-frames.tex:146–221`, labels `l:divisibility`, `p:toruskernel`.** The coefficient-ring argument for irreducibility of each determinant is valid: the two coefficients have gcd one, and the primitive polynomial is linear over the fraction field. Different unoriented edges give nonassociate primes in the full polynomial ring. Consequently divisibility by each determinant implies divisibility by their product, even for edges sharing a site. The multihomogeneous-component argument rules out cancellation between different quotient multidegrees. Its site degree is \(4-d_R(u)\), which is zero on \(R\). The zero polynomial and \(R=\varnothing\) are handled explicitly. Nonvanishing of \(B\), positivity of the edge projections, and the case \(R=\Lambda\) then give exactly the claimed one-dimensional kernel.

**Star constant — `sec3-quantum-frames.tex:223–253`, label `l:star`.** The five-site operator is positive and has eigenvalue four on the displayed tensor. Its finite positive spectrum is therefore nonempty, and its minimum \(g_\star>0\) is independent of the torus. Relabelling the five distinct site factors identifies each \(H_x\) with this operator tensored with an identity. Extra edges among those factors are irrelevant because they are absent from \(H_x\). Each unordered edge occurs twice in \(\sum_xH_x\), giving the required factor two.

**Tight frames and separation — `sec3-quantum-frames.tex:264–432`, labels `d:frame`, `l:tight`, `l:threeframes`.** The spinor convention gives \(\overline{\zeta_1}\zeta_2=(a_1+i a_2)/2\), with the sign used in \(P_{jk}\). Each \(P_{jk}\) has degree at most four, so the cited polynomial covariance is applicable. The off-diagonal rotation changes its sign; the five diagonal averages are \(1/5,1/20,1/30,1/20,1/5\). Multiplication by five gives exactly the physical monomial norms. Tensorization is valid for the positive reference measure of mass \(5^{|\Lambda|}\); it is not being treated as a probability.

The rotation matrix, the rationalization \(b=2/[101(\phi+2)]\), both rotation-norm estimates, and the strict distinct-vertex estimate are correct. The equal-vertex case attains \(b\). Antipodality transfers the lower bound for \(1-a\cdot a'\) to \(1+a\cdot a'\), and also supplies both upper bounds. Thus all cross-frame interaction factors lie in \([b,2-b]\), with \(0<b<1\), and different frames have no equal or antipodal letters.

**Colouring, determinant modulus, and specifications — `sec3-quantum-frames.tex:434–544`, labels `l:colour`, `l:qmod`, `d:framemodel`.** The exceptional last vertex in an odd cycle has colour two, distinct from the adjacent colours one and zero; the formula also works for a three-cycle. Adding the two cycle colours modulo three preserves a nonzero change along every edge. The determinant Gram identity and the Pauli trace identity yield exactly \(|q|^2=(1-a\cdot a')/2\). Proper colouring therefore gives full support, finite positive normalizers, and nonzero evaluations of every edge determinant. The empty-volume convention agrees with the probability definitions. Conditional expectations are orthogonal projections for the complex inner-product convention. Full support makes the site heat bath irreducible on the product configuration graph, so its gap is positive on every nontrivial finite volume.

**Quantum comparison — `sec3-quantum-frames.tex:546–687`, labels `l:quantumfibre`, `t:QD`, `e:frame-ground-weight`, `e:frame-ground-law`.** The incident-edge orientation signs are correctly collected in \(c_x\). Both residual factors used in the fibre argument are independent of the coordinate at \(x\). The weight identity has the correct constant \(5^{\lvert\Lambda\rvert}2^{-\lvert E\rvert}\), hence \(\|B\|^2=5^{\lvert\Lambda\rvert}2^{-\lvert E\rvert}Z^{\rm af}\). Nonzero pointwise evaluation of \(B\) proves that the multiplication map \(U\) is unitary onto the entire finite function space, with the stated inverse.

The conditional probabilities and the weighted projection onto the span of \(\beta_x\) have the same positive denominator. Substitution proves \(UE_x=\mathcal P_xU\). Divisibility proves the sufficient inclusion \(\iota\mathcal S_x\subset\operatorname{Ran}\mathcal P_x\); equality is not needed. This gives the distance inequality in the correct direction. For \(\varphi\perp B\), the resulting \(f\) has mean zero and variance \(\|\varphi\|^2\). The subsequent comparison is

\[
 \lambda(\mu^{\rm af})\|\varphi\|^2
 \le \sum_x\|(I-\mathcal P_x)\iota\varphi\|^2
 \le \frac1{g_\star}\sum_x\langle\varphi,H_x\varphi\rangle
 =\frac2{g_\star}\langle\varphi,H\varphi\rangle.
\]

Thus the quantum lower bound is \((g_\star/2)\lambda(\mu^{\rm af})\), with rate one per physical site. Invariance of \(B^\perp\) and the already proved kernel identity justify identifying its spectrum with the positive spectrum of \(H\). The zero test vector causes no division.

**Finite energy and block gaps — `sec3-quantum-frames.tex:691–799`, label `l:planeenergy`.** Conditioning a volume on all coordinates off a subset cancels precisely the factors not meeting that subset. This proves consistency and nearest-neighbour dependence. A one-site fibre has at most four factors. Its numerator is at least \(b^{d_x}/12\), and its total unnormalized mass is at most \((2-b)^{d_x}\), so every letter has probability at least \(\alpha=12^{-1}r_b^4\). Finite averaging gives the same bound under partial conditioning; the chain rule gives \(\alpha^k\), including \(k=0\), with positivity at every intermediate stage. These quantifiers are restricted to admissible frame letters, as explicitly stated at lines 796–799; the bound is not being applied to arbitrary unit pins.

For the block gap, all fixed boundary factors are retained in positive one-site weights. The reference law \(\nu_Q\) is consequently a positive product probability. If \(e=|E(Q)|\), the two density bounds have the common denominator \(\nu_Q(R)>0\), and their ratio is \(b^e/(2-b)^e=r_b^e\). Every hypothesis of Appendix A's `l:density` (`app-finite.tex:163–175`) is satisfied. Its three inequalities give the claimed gap with this ratio, without a second loss of that ratio. Fixed sites inside \(Q\) reduce the internal edge set; empty free sets and edgeless blocks are covered. Here a conditional block law means an exterior fibre with its exterior letters fixed, consistently with the definition of \(E_U\).

**Lift and local gauge — `sec3-quantum-frames.tex:801–890`, label `l:boxlift`.** The full square one-neighbourhood has coordinate diameter \(2M+2\), strictly smaller than both periods. This proves injectivity even at the stated minimal periods \(L=N=2M+3\). The internal-edge converse correctly rules out all other representatives of zero and \(\pm1\) in the permitted coordinate-difference interval. Each crossing edge has a unique exterior lift. The pulled-back colouring is proper on the entire plane.

The signs are defined at plane sites, so each internal or crossing nearest-neighbour bond has sign product \(-1\), regardless of torus parity. Each antipodal alphabet and its uniform weight are preserved. All remaining factors in the conditional torus law consequently become exactly those of the displayed plane law, with equal normalizing sums. Site update intertwining and preservation of Hamming distance follow from the same coordinate bijection. No global checkerboard sign on an odd torus is asserted or needed.

## Main-theorem dependency check

The proof at `sec1-result.tex:46–69` uses the other parts within their stated hypotheses:

| Step | Required hypotheses | Supplied data / conclusion | Verdict |
|---|---|---|---|
| `p:toruskernel` | \(L,N\ge3\) | Exactly the periods in `t:main`; gives \(B\ne0\) and the kernel for every such torus | Valid |
| `t:inputs` (`sec8-inputs.tex:270`) to `t:rec` (`sec7-recursion.tex:1008`) | Thresholds \(961/1000,187/200\); H1; H2 with \(C_V\ge1\), \(0<q<1\); H3\(_h\) for the specified kernel and orderings | \(C_V=10\); \(q=1119948287353/1120437614225\in(0,1)\); same type-dependent coefficients, vector, and orderings | Valid |
| `t:rec` to `t:cutMOS` (`sec5-window.tex:696`) | \(A\ge2\), \(0<\theta<1\), and precisely the property P of `h:P` | The recursion theorem supplies exactly these data | Valid |
| `t:cutMOS` to `t:mainW` (`sec4-periodic-gap.tex:404`) | W for the plane frame family, uniformly over proper plane colourings and translates | W\((64,p_0,M_\star)\), with \(0<p_0\le1\), positive integer \(M_\star\), and the required uniformity | Valid |
| `t:mainW` to `t:main` | The frame family of `d:framemodel` | Direct quantum gap conclusion for all integer periods above one threshold; uniqueness for smaller allowed periods is already separate | Valid |

The assembly proof uses `l:boxlift` only at \(M\ge1\), \(L,N\ge2M+3\), and `t:QD` only for proper torus colourings and \(L,N\ge3\). Its choices give, for one fixed \(M=n^8\),

\[
 L_0=2M+3,\qquad
 c=\frac{499}{1000}\,g_\star
       r_b^{\,2(2M+1)(2M)}>0.
\]

These constants precede the choice of periods, colouring, placement, and exterior configuration. The claimed absence of a parity restriction is consistent with this dependency chain. The second proof of `t:main` at `sec4-periodic-gap.tex:537` agrees with the proof in Section 1.

## Statement table

“Sound, dependent” means a correct application of the stated results from other parts, rather than independent verification of those results' numerical witnesses.

| Label and location | Content | Verdict | Dependencies |
|---|---|---|---|
| `d:model`, `sec1-result.tex:15` | Simple torus, physical spin space, oriented determinants, unoriented projection Hamiltonian, quantum gap | Well posed | `d:poly`; unique spin-four subspace established in `l:edge`; \(L,N\ge3\) |
| `t:main`, `sec1-result.tex:38` | Unique nonzero VBS ground state for every allowed torus; uniform gap for sufficiently large periods of either parity | Sound, dependent | `p:toruskernel`, `t:inputs`, `t:rec`, `t:cutMOS`, `t:mainW` |
| Conventions, `sec1-result.tex:117` | Complex inner products, ambient distances, empty-set rules, finite conditioning, Poincare and rate conventions | Consistent | Elementary finite-dimensional conventions; one-point infimum explicitly \(+\infty\) |
| `d:poly`, `sec3-quantum-frames.tex:14` | Weighted homogeneous polynomials, unitary spin-\(d/2\) action, finite spinor choices | Sound | Symmetric dual tensor realization; explicit irreducibility proof; Pauli rank-one identity |
| `l:edge`, `sec3-quantum-frames.tex:78` | Edge-projection kernel equals determinant multiples of endpoint bidegree \((3,3)\) | Sound | `d:poly`; equivariant diagonal evaluation; dimensions \(25,9,16\); integral domain |
| `l:divisibility`, `sec3-quantum-frames.tex:137` | All edges meeting \(R\) divide simultaneously; quotient independent of sites in \(R\) | Sound | `l:edge`; four distinct neighbours; UFD/Gauss; multigrading |
| `p:toruskernel`, `sec3-quantum-frames.tex:191` | \(B\ne0\), unique torus kernel, orientation independence | Sound | `d:model`, `l:edge`, `l:divisibility`; positivity of projections |
| `l:star`, `sec3-quantum-frames.tex:223` | Universal positive star constant; star lower bound; double edge count | Sound | `l:edge`; finite spectral theorem; five distinct site factors |
| `d:frame`, `sec3-quantum-frames.tex:264` | Positive finite quadrature exact through degree four | Well posed | `d:moment`, `l:moments`; complex extension by linearity |
| `l:tight`, `sec3-quantum-frames.tex:274` | Factor-five tight identity and physical evaluation isometry | Sound | `d:poly`, `d:frame`, `l:moments`; explicit \(P_{jk}\); tensorization |
| `l:threeframes`, `sec3-quantum-frames.tex:341` | Three antipodal separated frames with exact \(b,r_b\) | Sound | `d:moment`, `l:moments`; explicit rotation and distance estimates |
| `l:colour`, `sec3-quantum-frames.tex:434` | Proper three-colouring of every allowed torus | Sound | Explicit cycle colouring and addition modulo three |
| `l:qmod`, `sec3-quantum-frames.tex:458` | Squared spinor determinant \((1-a\cdot a')/2\) | Sound | Gram determinant; Pauli trace identities |
| `d:framemodel`, `sec3-quantum-frames.tex:490` | Positive torus/plane laws, conditional variances, rate-one site gap | Well posed | `l:threeframes`; proper colouring; finite positive sums |
| `e:frame-ground-weight`, `sec3-quantum-frames.tex:583` | Exact unnormalized frame image of \(B\), including \(5^{\lvert\Lambda\rvert}2^{-\lvert E\rvert}\) | Sound | `l:qmod`; product reference weights |
| `e:frame-ground-law`, `sec3-quantum-frames.tex:592` | Normalized ground-state image equals the antiferromagnetic law | Sound | Previous weight identity; `l:tight`; \(B\ne0\) |
| `l:quantumfibre`, `sec3-quantum-frames.tex:546` | Ground-state multiplication unitary; site intertwining; projection-distance comparison | Sound | `l:divisibility`, `l:tight`, `l:threeframes`, `l:qmod`; positive fibre sums |
| `t:QD`, `sec3-quantum-frames.tex:646` | Quantum gap at least \((g_\star/2)\lambda(\mu^{\rm af})\) | Sound | `l:quantumfibre`, `l:star`, `p:toruskernel`; classical Poincare definition |
| `l:planeenergy`, `sec3-quantum-frames.tex:691` | Consistency; Markov property; \(12^{-1}r_b^4\) finite energy; assignment and block-gap bounds | Sound | `d:framemodel`, `l:threeframes`; finite averaging/chain rule; `l:density` with verified hypotheses |
| `l:boxlift`, `sec3-quantum-frames.tex:801` | Injective square lift; exact internal/crossing bonds; local gauge, update and Hamming transport | Sound | \(M\ge1\), \(L,N\ge2M+3\); proper colouring; antipodal uniform alphabets; factorized conditional law |

## Exact computation checks

The checks ran sequentially in single-process Python, using exact rational arithmetic and exact arithmetic in \(\mathbb Q(\sqrt5)\). They corroborate the proof audit; the finite torus and lift ranges below are tests, not replacements for the general arguments.

| Check | Coverage and result |
|---|---|
| Two-site diagonal map and determinant multiplication | Constructed the \(9\times25\) diagonal-evaluation matrix and \(25\times16\) determinant-multiplication matrix. Exact ranks are 9 and 16; their product is zero. |
| Physical inner-product normalization | With the paper's diagonal Gram matrices, verified \(\Delta\Delta^*=I_{V_8}\). The \(25\times25\) matrix \(P=\Delta^*\Delta\) is idempotent, self-adjoint in that metric, annihilates determinant multiples, and fixes the weight-four vector. |
| Three actual rotated frame moments | Checked all 35 monomials of total degree at most four on each of the three frames: 105 moment constraints. |
| Tight-frame matrices | Checked all 75 complex Gram entries across the three frames, evaluating 45 upper-triangular/diagonal entries directly and using conjugacy for the rest. All match the stated physical Gram matrix. |
| Separation | Checked all \(3\cdot12^2\cdot2=864\) signed interactions between different frames against \([b,2-b]\). The minimum is exactly \(b\), attained by 16 entries in this enumeration. Comparisons used exact signs in \(\mathbb Q(\sqrt5)\). |
| Small torus graph and colouring | All 441 pairs \(3\le L,N\le23\): four distinct neighbours at every site, exactly \(2LN\) unoriented edges, and proper colouring by the displayed formula. |
| Minimal-period lifts and translated boxes | 162 cases: \(1\le M\le6\); independently \(L,N\in\{2M+3,2M+4,2M+5\}\); three placements including negative and wrapping coordinates. Verified one-neighbourhood injectivity, equality of internal and crossing edge sets, internal edge count, and integer parity signs on every relevant bond. |
| Main numerical interface | Verified exactly \(0<1119948287353/1120437614225<2499/2500<1\). |

## Formalization notes

- **Graph conventions are structural hypotheses.** Use a simple graph on \(\mathbb Z_L\times\mathbb Z_N\), with each unordered edge once. Prove the four-neighbour distinctness lemma before constructing \(B\), the incident-edge products, and the five-factor star identifications. This keeps period three in scope. Extending an endpoint operator to the remaining tensor factors requires the usual tensor permutation identifications.

- **Keep the representation and metric paired.** The physical monomial Gram matrix is \(G_d=\operatorname{diag}(\binom dj^{-1})\), and the action is contragredient. An explicit useful construction is

  \[
   (\Delta^*z_1^{8-\ell}z_2^\ell)
    =\sum_{\substack{0\le j,k\le4\\j+k=\ell}}
      \frac{\binom4j\binom4k}{\binom8\ell}
      m_j(z_x)m_k(z_y),\qquad P_e=\Delta^*\Delta.
  \]

  Vandermonde's identity gives \(\Delta\Delta^*=I\). The identification of this projection with physical total spin four can then be proved once using the paper's weight argument.

- **Divisibility is in the full polynomial ring.** Establish determinant primality and pairwise nonassociation there, then product divisibility. This argument needs pairwise coprime prime elements; it does not need the corresponding polynomial ideals to be comaximal. The quotient's multihomogeneity follows from the graded decomposition and injectivity of multiplication by the nonzero product. Treat the zero quotient and empty edge product explicitly.

- **Use a general evaluation map for residual polynomials.** The quotient \(\chi\) in `l:quantumfibre` is not a vector of the original physical multidegree. Its notation \(\iota\chi\) denotes evaluation only, as the proof explicitly explains. Only the physical-degree restriction of evaluation is asserted to be an isometry.

- **Spinor choices can stay finite.** Choose spinors for the finite union of the three frame sets. Their phases may be arbitrary. The Gram formulas remove these phases. Translate the degree-four moment covariance into polynomial identities, without asserting rotational invariance of the finite probability law on arbitrary functions. A colouring valued in \(\mathbb Z_3\) needs its representative in \(\{0,1,2\}\) when indexing \(T^jD\).

- **Distinguish the three function spaces.** Physical evaluation is an isometric embedding into \(\ell^2(\Omega,\pi)\), whose reference measure has mass \(5^{|\Lambda|}\). Ground-state multiplication \(U\) is a unitary from the full classical \(L^2(\mu^{\rm af})\) onto that weighted function space. The fibre projection has one-dimensional range on each exterior fibre; it is not one global rank-one projection. The proof needs only \(\iota\mathcal S_x\subset\operatorname{Ran}\mathcal P_x\), not invariance of the physical image under every classical update.

- **Keep complex conjugation in the projection formula.** With the first argument conjugate linear, the numerator is \(\sum_t5w_x(t)\overline{\beta_x(t)}h(t)\). The inverse unitary divides by \(\iota B\), not by its conjugate. Every denominator is positive because all frame interaction factors are at least \(b\).

- **Prove existence before defining spectral minima.** The star has the explicit eigenvalue four, and the torus Hamiltonian has the explicit positive eigenvalue \(2LN\). Their positive spectral minima are therefore defined. For empty classical blocks, retain the Poincare-inequality formulation or use an extended-real gap; the paper's \(+\infty\) convention for a one-point configuration space is not a real-valued infimum over an empty set.

- **Separate partial conditioning from a fixed exterior fibre.** The \(\alpha\) and \(\alpha^k\) bounds persist under partial conditioning by averaging. The block-gap proof fixes the exterior and absorbs its factors into product site weights. On further fixing sites inside the block, apply it to the free subset and compare internal edge counts. Arbitrary unit pins from the response model are outside this finite-energy assertion.

- **The lift preserves precisely the edges asserted.** At \(L=2M+3\), there can be additional torus adjacencies between opposite outer boundary sites of the lifted one-neighbourhood. The lemma correctly claims exact internal edges of \(Q'\) and its crossing bonds, not an induced-graph isomorphism on the entire one-neighbourhood. Wholly exterior factors cancel. Encode \(\varepsilon_z\) by integer parity, including negative coordinates, and use it only on the lift. This is a classical relabelling of letters; no global quantum gauge operation is required.

- **Preserve the input interfaces in the main theorem.** H3\(_h\) refers to the fixed type-dependent coefficients and the fixed, \(\theta\)-independent orderings, not an arbitrary response kernel. W is uniform over proper plane colourings and translations. These are exactly the interfaces actually used by Section 1; formalizing weaker versions would not suffice for the stated assembly.

## ORCH-SUMMARY

- Assigned audit: Sections 1 and 3; whole source read for context.
- VERDICT: SOUND for the assigned part, accepting out-of-part results as stated.
- No Critical, Major, or Minor findings; no required LaTeX repairs.
- Polynomial normalization, edge kernel, and uniqueness are valid for every \(L,N\ge3\).
- Three-frame separation constant \(b=(5-\sqrt5)/505\) and factor-five tightness are correct.
- Quantum comparison has the correct factor \(g_\star/2\) at rate one per site.
- Finite energy \(12^{-1}r_b^4\) and conditional block gap \(r_b^{|E(Q)|}\) are justified.
- The gauge is local to an injective lift and works for either torus parity.
- Main-theorem applications match the stated thresholds, kernel, orderings, and uniformity.
- Exact local algebra, frame checks, 441 torus sizes, and 162 lift cases passed.
- Computational witnesses in other parts were not independently certified in this audit.
