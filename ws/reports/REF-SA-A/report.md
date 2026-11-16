VERDICT: SOUND

REF-SA-A: Sections 1–2 and the additional-consequences/small-size statements of `/home/ubuntu/aklt/review/REF-SA/proof.tex`, reviewed against the corrected manuscript and `mosproof.tex`. All source-line locators below refer to those supplied files. No input was modified; no sub-agents were used.

The assigned algebraic assertions are correct as written. Uniqueness for every $L,N\ge3$ is unconditional. The uniform-gap conclusion has the stated dependence on the retained, corrected computer-assisted inputs and the later continuous/window/box estimates. This report checks the proof structure and its interfaces; it does not independently certify the large computations behind (H1), (H2), or (H3′).

**Numbered findings**

1. **Critical: none.** **Location:** replacement `t:main`, proof.tex:60–91 and 968–982. **Exact claim:** uniqueness for every $L,N\ge3$, and a common positive gap when both periods exceed a common threshold, with no parity restriction. **Failure assessment:** no missing algebraic implication or circular dependence was found. The small-size uniqueness statement follows directly from `p:graphkernel`; the large-size gap follows through the explicitly separated classical estimates. **Repair:** none.

2. **Major: none.** **Location:** `p:graphkernel`/`e:graphkernel`, `l:threeframes`, `l:colour`, `e:mucirc`, `t:QD`, and `e:muDW`, proof.tex:98–338. **Exact claims:** the residual-polynomial description of the entire kernel, the sharp common separation constant, proper three-colourings, the positive frame measure, the comparison with factor $g_\star/2$, and the plane-local sign change. **Failure assessment:** the necessary hypotheses are present, including simplicity, degree four for the comparison, adjacent-frame disjointness, and antipodality for the sign change. The orientation factors are correct. **Repair:** none.

3. **Minor: none requiring correction.** **Location:** `c:extras` and the following small-size discussion, proof.tex:988–1033. **Exact claims:** the rectangle and torus classical bounds, $3^4 2^{2r+2s-8}$ for open rectangles, uniqueness including width-three tori, and the listed degeneracies under the explicitly stated extension below period three. **Failure assessment:** all counts and qualifications are correct, including $r=2$, $s=2$, and periods one or two. **Repair:** none. The formalization notes below make conventions explicit without changing the statements.

**Statement table**

| Statement and location | Status | Checked hypotheses and conclusion |
| --- | --- | --- |
| Replacement `t:main`, proof.tex:60–91; completion at 968–982 | Sound with the stated retained inputs | Both periods may be odd. Uniqueness for all periods at least three is independent of mixing; a common gap is asserted only when both periods are sufficiently large. |
| Edge lemma recalled at proof.tex:98–105 | Sound | The degree-$(3,3)$ determinant image is precisely the orthogonal complement of total spin four in degree $(4,4)$, also after tensoring with other sites. |
| `p:graphkernel`, `e:graphkernel`, proof.tex:107–140 | Sound, unconditional | Every finite simple graph with $d_x\le4$; kernel $B_G\mathcal P_{(4-d_x)}$, dimension $\prod_x(5-d_x)$. Isolated vertices and disconnected graphs are included. |
| Torus application, proof.tex:142–146 | Sound, unconditional | For $L,N\ge3$, four neighbours are distinct, every simple bond is counted once, and the graph is four-regular, including $(3,3)$. |
| Three frames and `l:threeframes`, proof.tex:154–213 | Sound, exact | Twelve vertices in each antipodal five-design; $b=(5-\sqrt5)/505=2/[101(\phi+2)]$. The common bound is attained for adjacent powers of $T$. |
| `l:colour`, proof.tex:215–233 | Sound | Wrap-around edges are properly coloured in both coordinate cycles, including length three; summing the two cycle colours modulo three preserves properness. |
| Isometric frame model and `e:mucirc`, proof.tex:235–248 | Sound | The reference measure uses $5w_x$, each physical letter has weight $1/12$, and every antiferromagnetic bond factor lies in $[b,2-b]$. |
| Replacement `t:QD`, proof.tex:252–318 | Sound | Arbitrary edge orientations; every proper torus colouring; one heat-bath update per site; comparison constant $g_\star/2$. |
| General-graph clause of `t:QD`, proof.tex:260–262, 317 | Sound | Nonempty finite simple four-regular graph, positive four-designs, adjacent alphabets disjoint. Antipodality is not needed for this antiferromagnetic comparison. |
| Replacement `e:muDW`, proof.tex:320–338 | Sound | Finite plane domains and admissible frame-valued boundary data; sitewise antipodal bijections give exact equality of transported laws and intertwine conditional expectations. |
| Conditional-box interface, `r:Kpins` and `l:boxcell`, proof.tex:360–367, 446–496 | Sound | $L,N\ge\ell+1$, including equality; no extra internal wrap-around bond; repeated exterior images become separately specified plane pins. |
| Main constants/interface, proof.tex:394–443, 724–756, 1035–1052 | Sound | Common finite-energy bounds depend on $b$, and hence are uniform over colours, translations, and periods. $L_0=\ell+1$, $c=g_\star c_0m_0/4$. |
| `c:extras`(1), proof.tex:992–997, 1007–1009 | Sound given the preceding box theorem | Even physical side lengths $2t_1,2t_2$, with both cell sides at least $L_{\rm cell}$; physical gap at least $c_0m_0$, in either plane convention. |
| `c:extras`(2), proof.tex:998–1000, 1010 | Sound given the preceding box theorem | Torus frame gap at least $c_0m_0/2$ for $L,N\ge\ell+1$, uniformly over all proper three-colourings. |
| `c:extras`(3), proof.tex:1001–1003, 1011–1013 | Sound, unconditional | Open $r\times s$ rectangle, $r,s\ge2$: four degree-two vertices and $2r+2s-8$ degree-three vertices. |
| Remaining small-size statements, proof.tex:1016–1033 | Sound, unconditional | Width-three uniqueness is included. Below period three the formulas apply to the declared simple graph with loops suppressed and repeated bonds identified. No uniform thin-torus gap is claimed. |

**Detailed algebraic verification**

1. **The graph kernel is exactly the stated space.** Work in the polynomial ring with two variables at each vertex. The edge determinant has a rank-four symmetric quadratic-form matrix. A reducible homogeneous quadratic would be a product of two linear forms and have rank at most two, so $q_e$ is irreducible. It is prime in the endpoint polynomial ring, remains prime after adjoining the other variables, and determinants belonging to different edges of a simple graph are nonassociate. Shared vertices cause no problem: distinct edges still have different endpoint-variable supports.

   The edge lemma and positivity give
   \[
   \ker H_G
   =\mathcal H_G\cap\bigcap_{e\in E_G}(q_e)
   =\mathcal H_G\cap(B_G).
   \]
   This uses unique factorization, not an assumption that the ideals are comaximal. Since $B_G$ has degree $d_x$ in $z_x$, multigrading forces a quotient of a ground-state polynomial to have degree exactly $4-d_x$ at every vertex. Distinct multidegrees cannot cancel after multiplication by the nonzero $B_G$. Conversely all such products satisfy all edge constraints. Multiplication is injective because the polynomial ring is an integral domain. Each residual binary homogeneous-polynomial space has dimension $5-d_x$, proving the dimension product. The argument handles the zero polynomial, no-edge graphs, isolated vertices, and disconnected graphs. In a four-regular graph all residual degrees are zero, so the kernel is one-dimensional without a bipartiteness assumption.

   As an independent exact check of the edge lemma, index degree-$(4,4)$ monomials by their two exponents $i,j\in\{0,\ldots,4\}$ of the second spinor coordinates. Their squared norms are
   \[
   G_{ij,ij}=\frac1{\binom4i\binom4j}.
   \]
   The determinant-multiplication matrix from degree $(3,3)$ has rank 16. The nine total-spin-four vectors have coefficients $\binom4i\binom4j\mathbf1_{i+j=m}$, $0\le m\le8$, and rank nine. Their $G$-inner products with all sixteen determinant columns vanish exactly. Thus there is no normalization or orthogonality issue hidden in the Clebsch–Gordan step.

2. **Tori of period three have the required graph and local star.** For $L\ge3$, $i+1\ne i-1\pmod L$, and both differ from $i$; the analogous assertions hold vertically. Horizontal and vertical neighbours also differ from each other. Consequently the graph has $LN$ vertices and $2LN$ simple edges. At period three, neighbours of a vertex can themselves be adjacent. These additional edges are absent from $H_x=\sum_{e\ni x}P_e$, so they do not alter the five-site star operator. It is a fixed nonzero positive finite matrix, hence has a positive smallest nonzero eigenvalue $g_\star$. Summing stars counts each bond twice, exactly as needed. No numerical evaluation of $g_\star$ is required.

3. **The designs and the separation constant are exact.** The independent sign symmetries of $D$ kill all coordinate monomials with an odd exponent. Besides the constant, the remaining types through degree five are $x_i^2$, $x_i^4$, and $x_i^2x_j^2$. Their moments are respectively $1/3$, $1/5$, and $1/15$, using $\phi^2=\phi+1$. The displayed $T$ satisfies $T^\mathsf TT=I$ and $\det T=1$. Rotations preserve these design identities; antipodality and uniform weights are preserved as well.

   For equal underlying vertices, the deficit is
   \[
   1-a\cdot T^ka=(1-\cos k\vartheta)(a_1^2+a_2^2).
   \]
   The minimum transverse squared radius is $1/(\phi+2)$; $1-\cos\vartheta=2/101$ and $1-\cos2\vartheta=800/10201\ge2/101$. Thus the smallest such deficit across the three frames is $b$. For distinct underlying vertices, $a\cdot a'\in\{-1,\pm1/\sqrt5\}$, so $\lVert a-a'\rVert>1$. Also
   \[
   \lVert T-I\rVert=2/\sqrt{101},\qquad
   \lVert T^2-I\rVert=40/101<2/5.
   \]
   The triangle inequality gives $\lVert a-T^ka'\rVert>3/5$ and therefore $1-a\cdot T^ka'>9/50>b$. Antipodality supplies the other signed bound. The specified $a=(0,1,\phi)/r$ and $Ta$ attain $1-a\cdot Ta=b$; taking the negative of the second vertex attains the corresponding ferromagnetic lower bound.

   Exact enumeration additionally gives
   \[
   \max_{D^{(0)}\times D^{(1)}}|a\cdot a'|
   =\max_{D^{(1)}\times D^{(2)}}|a\cdot a'|
   =\frac{100}{101}+\frac{\sqrt5}{505}=1-b,
   \]
   whereas for $D^{(0)}\times D^{(2)}$ the maximum is
   \[
   \frac{9801+80\sqrt5}{10201}<1-b.
   \]
   Thus “the lower bound is attained” correctly means the common bound is sharp over all distinct frame pairs; it need not be attained for every pair of frame indices.

4. **The colouring handles every closing edge.** For even $m$, the alternating cycle colours close with distinct endpoint colours $1,0$. For odd $m\ge3$, the last colour is 2, its previous neighbour has colour 1, and its next neighbour has colour 0. All other edges alternate 0 and 1. For a horizontal or vertical torus edge, exactly one summand of $a_L(i)+a_N(j)\pmod3$ changes, and its change is a nonzero residue. This proves properness including $L=3$ or $N=3$, not just for edges away from the periodic seam.

5. **The frame measure and comparison have the right normalization and signs.** The single-site isometry uses the reference weights $5w_x$, so $\pi$ is a positive reference measure of total mass $5^{LN}$, not a probability measure. There is no requirement that it be normalized. With $n=LN$, direct multiplication gives
   \[
   \pi(s)|\iota B(s)|^2
   =5^n2^{-|E|}\prod_x\frac1{12}
       \prod_{\{x,y\}\in E}(1-s_x\cdot s_y).
   \]
   In particular $Z^{\rm af}=2^{|E|}\lVert B\rVert^2/5^n$, so `e:mucirc` is exactly normalized by the isometry. Every adjacent colour pair is different, every bond factor is in $[b,2-b]$, and $\iota B$ is nowhere zero. The factor $1/2$ in $|q|^2$ is absorbed into the partition function, not into the heat-bath rates.

   For any orientation, write $q_e=\epsilon_{e,x}q_{xy}$ with the centre $x$ first. The product of these signs at $x$ is precisely the $c_x$ in `e:cx`. Including it in $\rho_x$ yields $\iota B=\beta_x\rho_x$. For a local ground vector $\psi$, divisibility by the four incident determinants leaves a quotient independent of $z_x$, and its evaluation is $c_x\beta_x\chi$. Thus both appearances of the sign in the proof agree. Changing an edge orientation changes the global $B$ only by a scalar sign.

   Multiplication by $\iota B/\lVert B\rVert$ is unitary between the two full classical function spaces because the multiplier never vanishes. On a fibre, the projection formula uses weights $5w_x(t)|\beta_x(t)|^2$; its constant factor 5 cancels, giving exactly the single-site conditional distribution. Hence $UE_x=P_xU$. The inclusion $\iota\mathcal S_x\subset\operatorname{Ran}P_x$ and isometry give the stated distance inequality even though $\iota$ is not onto the reference function space. For $\varphi\perp B$, the transported function has zero mean and variance $\lVert\varphi\rVert^2$. Combining these facts gives exactly
   \[
   \lambda(\mu^{\rm af})\lVert\varphi\rVert^2
   \le\sum_x\lVert(1-P_x)\iota\varphi\rVert^2
   \le\frac2{g_\star}\langle\varphi,H\varphi\rangle.
   \]
   Full support makes successive single-coordinate changes possible, proving irreducibility and positive finite-volume classical gap. There is no missing factor of the volume or the degree. On the general graph, disjoint adjacent alphabets suffice because $|q(\zeta(a),\zeta(a'))|^2=0$ only when $a=a'$. Its weights need not be uniform and its frames need not be antipodal for this comparison.

6. **The sign convention is local, including repeated boundary images.** On a finite plane domain, $\varepsilon_z=(-1)^{z_1+z_2}$ changes every internal antiferromagnetic bond into a ferromagnetic one. Assigning $\eta_{z'}=\varepsilon_{z'}s_{z'}$ also changes every crossing bond correctly. Each alphabet and its weights are preserved. A coordinatewise bijection transports the finite conditional probability formula and therefore every conditional expectation and the entire heat-bath generator. No relation between the coherent spinor phases at $a$ and $-a$ is needed for this measure-level assertion.

   For a translated $\ell\times\ell$ box with $L,N\ge\ell+1$, a lift is injective. Its coordinate differences have magnitude at most $\ell-1\le L-2,N-2$, excluding any additional internal bond through the torus seam. Every exterior nearest-neighbour plane site projects outside the torus box, and each such plane site touches exactly one interior site. Thus torus crossing edges and lifted plane crossing edges correspond with their full multiplicities.

   At equality $L=\ell+1$, the plane sites in the missing column on the two sides have the same torus image but are distinct boundary sites. Their horizontal coordinate difference is $L$. When $\ell$ is even, $L$ is odd, and their gauge signs are opposite. These are valid separate letters of the same antipodal alphabet; they are not required to coincide on the plane. For example, with $\ell=2,L=3$, the sites $(-1,j)$ and $(2,j)$ both map to $(2,j)$ on the torus and acquire opposite signs. The factors incident to the two interior sites remain two factors. Exterior-only bond factors are constant under conditioning and cancel from the conditional law. The same reasoning holds vertically and when both periods equal $\ell+1$.

7. **The subsequent uses require exactly what the replacements provide.** The periodic lift $\widetilde\kappa=\kappa\circ p$ is proper on the plane for every proper torus colouring. The later uniform window estimate is quantified over all proper plane colourings and all translates, so it covers this lift without identifying patterns by translation. Antipodal changes in repeated pins remain admissible frame-valued data. The continuous estimates allow arbitrary unit pins, and hence also cover repeated or oppositely signed pins.

   The replacement bond bounds give, uniformly,
   \[
   r_b=\frac b{2-b},\qquad
   \beta=12^{-1}r_b^4,\qquad
   \alpha=12^{-4}r_b^{12},\qquad c_0=\beta^5/4.
   \]
   Four factors depend on a physical site. Four internal and eight crossing factors depend on a $2\times2$ cell. Comparing minimum and maximum unnormalized weights gives these conditional probability lower bounds. The elementary four-site gap estimate and summation over disjoint cells give $c_0$ without an extra factor of four. All constants are independent of colouring and placement; positivity is asserted here for admissible boundary letters, as the supplement explicitly stipulates.

   In the corrected manuscript, the finite-size theorem already allows inhomogeneous nearest-neighbour weights, all $L,N\ge\ell+1$, and twelve-letter alphabets. Its proof uses commuting updates at non-neighbours and autocorrelation counts, not torus bipartiteness. The width-three case $\ell=2,L=3$ also meets these graph assumptions. The replacement of the global rotated torus model by $\mu^{\rm af}$ therefore supplies its actual hypotheses.

   The manuscript's tight-frame proof and partition-function exactness lemma already allow different site designs. The cut argument sums out variables of separate degree at most four and retains the actual window weight, so it does not require equality of window laws across colourings. Subsequent Sections 6–8 and their certificate interfaces concern the continuous plane model and arbitrary unit pins; they do not consume the old $0.205$ bond lower bound, the old cell cardinality, or a periodic torus sign. The old checkerboard-dependent global `e:muD`/`e:QDrot` is explicitly removed from the new chain; it must not be read as a claim on odd tori. The supplement also explicitly removes the translation-invariant mixing theorems and compatible-set scales, using the finite box theorem instead. MOSPROOF's finite-square criterion permits the inhomogeneous use when imposed at every translate, precisely the quantifier supplied here.

   With the resulting common cell gap $m_0$, choose
   \[
   t\ge\max\{L_{\rm cell},\lceil1/(c_0m_0)\rceil,1\},
   \quad\ell=2t,\quad L_0=\ell+1.
   \]
   The lift and comparison give $g(\ell)\ge c_0m_0$, and $1/\ell\le c_0m_0/2$. Therefore
   \[
   \lambda(\mu^{\rm af})
   \ge\frac\ell{\ell-1}\left(c_0m_0-\frac1\ell\right)
   \ge\frac{c_0m_0}{2},\qquad
   \gap(H)\ge\frac{g_\star c_0m_0}{4}.
   \]
   This verifies the constants in the replacement main theorem and `c:extras`(1)–(2). Their choice precedes all periods, colourings, translations, and boundary configurations. The original even-torus quantum conclusion follows by restriction, with possibly different unspecified constants. The derivation of (P) uses neither this gap conclusion nor the new frames, so the proof structure is acyclic.

8. **Every small-size dimension follows from degrees, including the endpoints of the stated ranges.** On an open $r\times s$ rectangle with $r,s\ge2$, there are four distinct degree-two corners. The $2r+2s-8$ other boundary vertices have degree three; the $(r-2)(s-2)$ interior vertices have degree four. These counts still partition all vertices when one side is two. The product formula gives $3^4 2^{2r+2s-8}$, including dimension $81$ for $2\times2$.

   For the extension with loops suppressed and repeated bonds identified, the remaining cases are:

   | Periods, including swapped cases | Simple graph degrees | Kernel dimension |
   | --- | --- | --- |
   | $L=2,N\ge3$ | Degree three at all $2N$ vertices | $2^{2N}$ |
   | $L=N=2$ | Degree two at four vertices | $3^4$ |
   | $L=1,N\ge3$ | Degree two at all $N$ vertices | $3^N$ |
   | $(1,2)$ or $(2,1)$ | Degree one at two vertices | $4^2$ |
   | $(1,1)$ | One degree-zero vertex | $5$ |

   In each case below period three, $B_G$ has degree below four at some vertices and is not by itself a physical spin-two tensor-product vector. The residual factor in `e:graphkernel` is essential. Conversely all $L,N\ge3$, including all infinitely many width-three tori, are four-regular and have a one-dimensional kernel. The supplement correctly refrains from obtaining a uniform thin-torus gap by taking a minimum over those infinitely many sizes.

**Independent exact computations**

[verify_ref_sa_a.py](/home/ubuntu/aklt/reports/REF-SA-A/verify_ref_sa_a.py) is an independent standard-library Python checker. It reads no supplied scripts or other input files and runs in one process. Run `python3 verify_ref_sa_a.py` from this directory. All checks passed; output is recorded in [verification.txt](/home/ubuntu/aklt/reports/REF-SA-A/verification.txt).

- 168 moment identities: all 56 coordinate monomials of total degree at most five for each of the three frames. Odd-degree sums vanish before normalization; every even normalized moment is computed in $\mathbb Q(\sqrt5)$.
- All 432 cross-frame pairs for the three unordered frame pairs, with exact comparisons in $\mathbb Q(\sqrt5)$. This verifies both signed bond bounds and sharpness of the common $b$.
- The two-site ranks and orthogonality described above, in rational arithmetic.
- Simplicity, degree four, edge counts, and the displayed colouring for all 1,444 pairs $3\le L,N\le40$.
- All translations for 1,944 box-lift cases: $\ell\in\{2,4,6,8\}$, independently $L,N\in\{\ell+1,\ell+2,\ell+3\}$. These include 964 cases with repeated exterior images and opposite gauge signs. Internal-edge sets and boundary-edge multisets agree exactly.
- The local sign factorization at every vertex for all 1,024 orientations of the nonbipartite four-regular graph $K_5$, evaluated at integer spinors with nonzero edge determinants.
- The open-rectangle degree formula for $2\le r,s\le20$ and every suppressed-loop/repeated-bond torus degree formula for $1\le L,N\le12$.

The finite geometry and orientation evaluations are supplementary checks. The universal justifications are the polynomial, sign, and lift arguments above; no extrapolation from a bounded size range is used.

**Formalization notes**

- Use a finite loopless simple graph, with each unoriented edge present once. Treat an orientation as an auxiliary choice for its determinant. Repeated constraints must not be treated as distinct prime factors.
- State the edge-kernel equivalence first, then the polynomial ideal/intersection result, then take the multidegree-$(4,\ldots,4)$ component. Separate the no-edge case if a library's finite-product lemma requires nonempty index sets. The empty-vertex graph has Hilbert space $\mathbb C$, and the dimension formula uses empty product one.
- Keep $r=\sqrt{\phi+2}>0$, normalized spherical measure, and positive design weights summing to one. A spherical four-design suffices for the spin-two isometry; five-design exactness is stronger than required.
- Keep distinct the physical edge projectors $P_e$, the fibre projections $P_x$ in the reference function space, the quantum projections $\Pi_{\mathcal S_x}$, and the heat-bath conditional expectations $E_x$. The comparison uses an inclusion of ranges, not equality of the quantum and classical local ground spaces.
- Keep $\pi=\prod_x5w_x$ unnormalized. Define complex variance as $\mu(|F-\mu F|^2)$. The unitary $U$ is between the full classical spaces, while $\iota$ is an isometric embedding of the quantum space.
- For `e:muDW`, make the inherited convention explicit in a formal statement: $W\subset\mathbb Z^2$ is finite, and $\eta_{z'}\in D^{(\kappa(z'))}$ at exterior sites needed by crossing bonds. Boundary letters are arbitrary within these alphabets; they obey no compatibility constraint with each other. The empty-volume partition function is one.
- Define a lifted conditional law using separate plane boundary sites before attaching their torus images. Equality of torus images does not mean equality of the post-gauge letters. Preserve both crossing edge factors even if their exterior torus endpoint is shared.
- Record two different uses of disjointness: adjacent alphabets disjoint implies full support for the antiferromagnetic comparison; the stronger uniform separation and antipodality imply positive ferromagnetic weights and permit the local gauge. Only the latter step needs antipodality.
- Retain the universal quantifiers over proper plane colourings, cell origins, translates, and admissible boundary configurations throughout the window-to-box interface. No choice of a canonical colouring, translation invariance, or global sign function on an odd torus is needed.
- The dependency order is the retained continuous inputs $\Rightarrow(P)\Rightarrow$ uniform windows $\Rightarrow$ uniform cell boxes, followed by the physical comparison, torus finite-size criterion, and quantum comparison. The graph-kernel proof is independent of this chain. Uniform positivity constants alone do not replace the window hypothesis.
