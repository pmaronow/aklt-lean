STATUS: COMPLETE

The evenness restriction can be removed. [proof.tex](proof.tex) contains the replacement and added text, section by section; [proof.pdf](proof.pdf) is its compiled reading copy. Uniqueness holds for **every $L,N\ge3$**, with no exceptions. The uniform gap holds for **every sufficiently large pair $L,N$**, of any parities, with exactly the manuscript's existing computer-assisted inputs, interpreted with the adjudicated corrections.

No new local inequalities, trail enumeration, or kernel certificate are required. The proof keeps the antiferromagnetic measure on the torus, uses a local sign change on each lifted box, and proves the window-to-box implication uniformly for inhomogeneous finite-state specifications. It does not apply a translation-invariant mixing theorem to an inhomogeneous model.

## Strengthened statements

1. **All-parity main theorem (`t:main`, `t:mainW`).** There exist $c>0$ and an integer $L_0$ such that for all integers $L,N\ge L_0$,
   
   \[
   \ker H_{L,N}=\mathbb C B,\qquad \operatorname{gap}(H_{L,N})\ge c.
   \]
   
   The proof gives $c=g_\star c_0m_0/4$ and $L_0=\ell+1$, with an auxiliary even box side $\ell$ chosen in equation `e:ellchoice`. The equality case $L=\ell+1$, previously excluded by the evenness assumptions, is included. These are new positive constants; preservation of the old unspecified numerical values is not claimed.

2. **Uniqueness for every stated size (`p:graphkernel`).** For every $L,N\ge3$, $\ker H_{L,N}=\mathbb C B$. This uses only the polynomial edge lemma and unique factorization, independently of frames, mixing, or computer-assisted inputs. It is already implicit in the manuscript's divisibility lemma with the region equal to the whole graph. A side of length three makes triangles, but still gives a simple graph with four distinct neighbours at every site. No exceptional pair occurs in the requested range.

3. **Exact ground spaces on arbitrary simple graphs (`p:graphkernel`, `e:graphkernel`).** If $G$ is a finite simple graph of maximum degree four, multiplication by $B_G=\prod_{e\in E_G}q_e$ is a linear isomorphism from the polynomials of degree $4-\deg_G(x)$ at each vertex to $\ker\sum_eP_e$. In particular,
   
   \[
   \dim\ker H_G=\prod_x(5-\deg_G(x)).
   \]
   
   Every finite simple 4-regular graph has a unique spin-2 AKLT ground state, including nonbipartite and disconnected graphs. An open $r\times s$ rectangle, $r,s\ge2$, has ground-space dimension $3^4 2^{2r+2s-8}$.

4. **Uniform classical consequences (`c:gapcell`, `c:extras`).** The same window parameters work for every proper plane three-colouring and every origin of the physical $2\times2$ cells. All sufficiently large cell rectangles have cell heat-bath gap at least $m_0$, with arbitrary admissible boundary data. Physical rectangles of even sides $2t_1,2t_2$, $t_1,t_2\ge L_{\mathrm{cell}}$, have physical-site gap at least $c_0m_0$. The corresponding antiferromagnetic statement follows by the plane gauge. On each sufficiently large torus, the antiferromagnetic frame heat bath has gap at least $c_0m_0/2$, uniformly over **every** proper three-colouring, not only the explicit one constructed here.

5. **General frame comparison (`t:QD`).** The frame-to-quantum comparison holds on every nonempty finite simple 4-regular graph assigned positive weighted 4-design frames with disjoint adjacent alphabets. Its constant is still $g_\star/2$. This statement itself asserts no uniform classical gap on arbitrary graphs.

For periods below three the original model was not defined. If it is extended using the **simple-graph convention**, suppressing loops and repeated neighbours, the exact dimensions are: $2^{2N}$ for $L=2,N\ge3$, $3^4$ for $L=N=2$, $3^N$ for $L=1,N\ge3$, $4^2$ for $(1,2)$ or $(2,1)$, and $5$ for $(1,1)$, with the swapped cases identical. These are proved by the same graph formula. In those cases $B_G$ alone is not degree four at each site, so it is not the manuscript's torus state without residual factors. A multigraph interpretation is a different Hamiltonian and is not silently substituted.

## Explicit replacement frames and constants

Put $\phi=(1+\sqrt5)/2$, and take the uniform icosahedral design

\[
D=\frac1{\sqrt{\phi+2}}
\{(0,\pm1,\pm\phi),(\pm1,\pm\phi,0),(\pm\phi,0,\pm1)\}.
\]

Use the three designs $D,T D,T^2D$, where

\[
T=\begin{pmatrix}99/101&-20/101&0\\20/101&99/101&0\\0&0&1\end{pmatrix}.
\]

All have 12 letters, uniform weights $1/12$, and are antipodal 5-designs. Thus the dodecahedron and its separate exact design proof can be removed from the main proof. Lemma `l:threeframes` proves the design identities and the **exact** separation bound

\[
b=\frac{5-\sqrt5}{505}>0,\qquad
b\le1\pm a\cdot a'\le2-b
\]

for every pair of letters in two different designs. The lower bound is attained. The new counterpart of $\gamma_+$ is $\Gamma=1-b$; the old $\gamma_+$ must not be reused in finite-energy estimates for these frames.

A proper torus colouring is explicit: alternate 0 and 1 on each even cycle; on an odd cycle alternate them except at its last vertex, which receives colour 2; then add the two cycle colours modulo 3. An edge changes just one summand by a nonzero residue. This proves three-colourability also at $L=3$ or $N=3$.

Writing $r_b=b/(2-b)$, convenient common bounds are

\[
\beta=12^{-1}r_b^4,\qquad
\alpha=12^{-4}r_b^{12},\qquad
c_0=\beta^5/4.
\]

Here $\beta$ bounds physical-site conditional letter probabilities and $\alpha$ bounds cell conditional letter probabilities. There are $12^4=20{,}736$ cell letters, four internal bonds and eight crossing bonds. Bounds on individual factors are multiplied with the correct powers; a whole weight or normalized probability is not assigned a one-factor bound. These bounds hold for frame-valued admissible boundary conditions. They are not claimed for arbitrary unit pins, which can make a particular finite letter have zero weight.

The continuous proof supplies $A,\theta$ in (P). The cut proof then gives the common window parameters in equations `e:epsilon` and `e:windowconstants`, with $l_0=20$. Set $d=\min\{1/2,p_0\alpha^{320}\}$, choose $n$ as in `e:nchoice`, and put

\[
M=n^8,\quad L_{\mathrm{cell}}=4M+1,\quad v=L_{\mathrm{cell}}^2,
\qquad m_0=\frac{\alpha^{v+1}}{1000v}.
\]

Choose $t\ge\max\{L_{\mathrm{cell}},\lceil1/(c_0m_0)\rceil,1\}$ and $\ell=2t$. This closes the constants before selecting the torus, its colouring, the conditional box or any boundary data. The bounds are deliberately conservative and make no useful numerical prediction for the final quantum gap.

## Inventory of manuscript changes

The baseline for this table is the supplied manuscript **with the existing adjudicated corrections**. Those separate corrections must still be applied; they are not undone by this extension. Source labels are more stable than PDF numbering. Rows group adjacent prose or labels when a single replacement handles them together. The replacement text uses the original labels for retained statements and new labels for genuinely new statements.

| Location / source label | Before | After | Reason / replacement locator |
|---|---|---|---|
| `main.tex`, abstract | Uniform quantum gap and uniqueness for large even periods; cited mixing-theorem route | Uniform gap for all large periods; uniqueness for every period at least three; direct finite-state box argument | New abstract and §1 of `proof.tex` |
| §1 `t:main` | $L,N\ge L_0$, both even | All $L,N\ge L_0$, plus uniqueness for all $L,N\ge3$ | `t:main`; final proof in §6 |
| §1 introductory paragraph after `t:main` | Discloses finite-alphabet extension of MO94; constants unspecified | Same computer-assisted inputs with adjudications; direct finite-state implication; explicit formulas from (P) | §1 and `e:ellchoice`; retain the ADJ-R6 qualification of selected margins |
| §1 `s:intro`, first reduction | Icosahedron/dodecahedron checkerboard and globally rotated torus measure | Three rotated icosahedra, proper colouring, antiferromagnetic torus measure; squared **modulus** and reference weights | §1; `l:threeframes`, `l:colour`, `e:mucirc` |
| §1 `s:intro`, mixing reduction and dependency prose | Two translation-invariant cell models; MOS94 then MO94 | Inhomogeneous plane models; uniform windows at all translates; stopped coupling and finite-square criterion | §1 and §4; no order or attractivity hypothesis |
| §1 cut-reduction prose | Two particular frame types, and the former abbreviated cut-cost description | Arbitrary site frames in quadrature; keep the first-removal additive four-spin cost | §5; `e:epsilon`; consistent with ADJ-MINOR |
| §2 after `l:divisibility` (addition) | Divisibility used locally; no all-graph ground-space formula stated | Exact kernel and dimension on every finite simple graph of maximum degree four | New `p:graphkernel`, `e:graphkernel` |
| §2 `s:tight`, paragraph preceding `e:icodod` | Icosahedron and dual dodecahedron, two frame types | Three explicit rotations of one exact 5-design | `e:threeframes`, `l:threeframes` |
| §2 `e:icodod` | Specific cross-dot values $\pm\gamma_\pm$ and $1-\gamma_+>0.205$ | Bound $\lvert a\cdot a'\rvert\le1-b$, exact minimum factor $b=(5-\sqrt5)/505$ | Retire `e:icodod` from dependencies; use `e:delta`, `e:separation` |
| §2 `s:framemodel` setup | “From now on $L,N$ are even”; checkerboard assignment | Any $L,N\ge3$; assign the designs by a proper three-colouring | `l:colour` and following frame construction |
| §2 `e:mucirc` | $\mu^\circ$ using checkerboard frames | $\mu^{\mathrm{af}}$ using proper-colouring frames; same antiferromagnetic product form | `e:mucirc`; full support follows from the new (b) |
| §2 `t:QD` | Even $L,N\ge4$ | All $L,N\ge3$, and nonempty general 4-regular graph version | `t:QD`, `e:QDall`; star operator unchanged |
| §2 proof of `t:QD` | Missing orientation signs in two factorizations before adjudication | Explicit $c_x=\prod_{e\ni x}\epsilon_{e,x}$ in $\rho_x$ and in evaluation of a local ground vector | `e:cx`; incorporates ADJ-MINOR E07–E08 |
| §2 `r:QDgeneral` | Notes a graph extension but leaves possible zeros untreated | Actual general theorem for adjacent-disjoint frames; independent algebraic uniqueness for all simple 4-regular graphs | `t:QD`, `p:graphkernel` |
| §2 `s:rotated`, `e:muD` | A global checkerboard sign defines a ferromagnetic torus model | Keep the torus antiferromagnetic; use the sign only on a lifted plane box | §2.4 and `e:localgauge`; global `e:muD` is retired |
| §2 `e:QDrot` | Quantum gap compared to the globally rotated $\mu_D$ on even tori | Compare to $\mu^{\mathrm{af}}$ on every torus | `e:QDall` |
| §2 `e:muDW` | Plane ferromagnetic law with fixed checkerboard frames | Same factors, arbitrary proper plane colouring and admissible site-dependent boundary letters | `e:muDW` |
| §2 final bond-weight assertion | Already corrected to a bound on individual factors with $\gamma_+$ | Bound each factor by ([b,2-b]); use the appropriate powers for products | `e:separation`, `e:energy` |
| §3 opening motivation / reference after `e:MRF` | Explains lack of full translation symmetry through the checkerboard | Apply the unchanged criterion to the positive, generally inhomogeneous $\mu^{\mathrm{af}}$ | §3; no change to `t:K` or either threshold |
| §3 `r:Kpins` | Notes repeated torus boundary values at a period $\ell+1$ | Also explains their potentially opposite signs after the local gauge; arbitrary admissible plane pins cover them | New explicit replacement `r:Kpins` |
| §4 `s:cells` | Two offsets, common alphabet 57,600, translation-invariant potential | Any cell origin and proper colouring; site-dependent cell alphabet of size 20,736; uniform energy bounds | §4.1, `e:energy`; fixed abstract alphabet available by enumeration |
| §4 offset-equivalence paragraph | Translation by $(1,1)$ reduces four corner parities to two offsets | Choose cells at the actual box corner; all translates/colourings covered uniformly | §4.1 and `l:boxcell`; no symmetry reduction |
| §4 `l:boxcell` (Lemma 4.1) | Even periods and checkerboard-preserving lift; excludes equality $L=\ell+1$ by parity | All $L,N\ge\ell+1$, arbitrary placement; lift first, then gauge; repeated exterior images permitted | `l:boxcell`, `e:localgauge` |
| §4 `l:compare` | Existence of one finite positive local comparison constant | Uniform explicit choice $c_0=\beta^5/4$, with no invariance assumption | `l:compare`; finite conditional-variance proof |
| §4 `s:cited`, `e:SM`, `e:MOS22`, `t:MOS21`, `t:MO41`, `r:finiteS` | External mixing/gap inputs and compatible-set terminology | Removed from the required proof chain; replaced by the direct finite-square proof | §4.3; these original theorems are not asserted for inhomogeneous models |
| §4 `d:W`, `e:W` | Window estimate for each of two stationary cell models | Same window shapes, uniform parameters over colourings, origins, **all translates**, and admissible boundaries | `d:W`, `e:W` |
| §4 `p:surgery`, `e:prop21` | Original terminal-radius marginal-TV bound | Original bound still holds uniformly; add a stopped full-law coupling needed for Hamming contraction | `l:stopped`, `e:stopped`; no success claim beyond $i\le s$ |
| §4 `c:gapcell` | Gap on arbitrary compatible unions from two cited theorems | Gap on every sufficiently large rectangle, uniformly over the inhomogeneous family | Replacement `c:gapcell`; this is a sufficient replacement, not a claim of the old arbitrary-union conclusion |
| §4 constant-choice paragraph | $\delta\to C,\gamma\to M_0^{(o)}\to m_0$ | $\alpha,p_0,M_\star\to d\to n\to M,L_{\rm cell},m_0$ | `e:nchoice`, `e:cellconstants` |
| §4 `t:mainW` and its proof | Both even periods; common multiple of two compatible scales; $L_0=\ell+2$ | All periods; any sufficiently large auxiliary even box side; $L_0=\ell+1$ | Replacement `t:mainW`, `e:ellchoice` |
| §4 final proof of `t:main` and noncircularity paragraph | (P) gives windows for two fixed models | (P) gives uniform windows for the whole proper-colouring family | Final proof in §6; continuous identities do not depend on the quantum/classical-gap reductions |
| §5 opening paragraph and paragraph after `l:exact` | Window estimate for both checkerboard cell models | Window estimate uniform over arbitrary proper-colouring frame patterns | §5.1 and replacement `t:cutMOS` |
| §5 `l:exact` | Positive-factor quadrature, already with arbitrary site frames | Also permits signs in individual factors; explicitly distinguishes partition functions from window measures | Replacement `l:exact`; positive-factor case unchanged |
| §5 setup of `l:cut`, `e:windowlaw`, `e:cutratio` | Written for the selected rotated frame specification | Same formulas and TV bound for the inhomogeneous frames; full-support reference law checked | §5.2, `e:windowlaw`–`e:cutratio`; no claim that the window law itself is frame-independent |
| §5 `s:cutgeom` setup, quantifiers of `l:cutgeom`, `l:Xconn` | Physical cells of offset $o\in\{0,1}$ | Any translated $2\times2$ cell grid | §5.3; all geometric inequalities, counts and topology proofs remain the same |
| §5 `t:cutMOS` | (P) gives a window bound for the two models | Same $l_0=20$ and common $p_0,M_\star$ for all proper plane colourings and cell origins | Replacement `t:cutMOS`, `e:windowconstants` |
| Appendix A frame and finite-energy rows | $\gamma_\pm$, unspecified $c_0,\alpha$ | $b,\Gamma,\beta,\alpha,c_0$ with exact formulas | New Appendix B of `proof.tex` and equations above |
| Appendix A mixing-scale row | $M_0^{(o)},C,\gamma,m_0$ from MO/MOS | $n,M,L_{\rm cell},m_0$ from the finite-square construction | `e:nchoice`, `e:cellconstants` |
| Appendix A final row | $c=g_\star c_0m_0/4$, $L_0=\ell+2$ | Same expression for the new $c$; $L_0=\ell+1$ | `e:ellchoice` |
| Added consequences after the main proof | No such uniform-family or graph-dimension statements collected | Exact graph ground spaces, rectangular classical gaps, all-colouring torus gaps, small simple-graph cases | `p:graphkernel`, `c:extras`, new Appendix A |

The model definition `e:H`, the edge lemma `l:edge`, the local divisibility lemma `l:divisibility`, the positive-star bound `e:star`, the 4-design definition `d:frame`, and the tight-frame identity `l:tight` retain their statements. The continuous hypothesis `h:P`, three-factor lemma, removal estimate, walk/kernel statements and certified numerical inputs likewise retain their adjudicated statements. These are important unchanged dependencies, not omitted edits.

## Where parity, symmetry and the particular frames were used

The source search is retained in [parity-inventory.txt](parity-inventory.txt). It records all source hits for evenness, parity, checkerboard/sublattice, translations, rotations, frames, offsets and gamma constants across §§1–8 and Appendices A–D. The following audit includes uses whose wording alone can be misleading.

| Place | What the old argument used | Resolution |
|---|---|---|
| §1 statement and abstract | Explicit restriction to even periods | Removed in the statements proved above |
| §2 construction of (B), star and edge lemmas | Degree four and distinct endpoint variables, sometimes obscured by the later parity restriction | Only simplicity and four distinct neighbours matter; valid at every $L,N\ge3$, including triangles |
| §2 checkerboard assignment | Bipartiteness makes every edge join the two particular disjoint frames | Explicit proper three-colouring and three pairwise disjoint designs |
| §2 isometry | Degree-four coherent-state evaluation pairing and design quadrature | All three new designs are exact 5-designs; no sublattice condition |
| §2 $\gamma_+$ and finite energy | The chosen ico/dodeca relative position gives a positive elementary factor bound | Replace by the exact new (b); retain the correct four/twelve factor powers |
| §2 QD orientation | Arbitrary edge orientations cannot all be treated as $q_{xy}$ directed away from the current vertex | Include $c_x$. Signs change neither fibre spans nor squared moduli, on even or odd tori |
| §2 global sublattice rotation | The sign $(-1)^{x_1+x_2}$ is periodic only when both periods are even | Do not use a global torus rotation. Use its ordinary plane version on each lifted conditional box |
| §3 commutation and fibre decomposition | Positive nearest-neighbour Markov field | Already permits inhomogeneity and all periods; odd cycles introduce no extra non-neighbour interaction |
| §3 autocorrelation lemma | Symmetric interval superlevel sets have lengths of the same parity | An integer-interval fact, independent of physical torus parity; wrap-around is already handled by $r_L$ |
| §3 weighted proof | Cauchy–Schwarz over box placements replaces a translation-eigenvector argument | Retain that existing proof and the adjudicated zero-denominator case; no new symmetry assumption |
| §3 / §4 boundary at $L=\ell+1$ | A single outside column/row can pin both sides; parity formerly excluded it in §4 | Separate plane boundary lifts receive their actual signed pins. Equal torus images may give opposite plane letters, both admissible |
| §4 no extra internal bonds | The old evenness conditions implied an extra unused row/column | The actual needed bound is $L,N\ge\ell+1$; coordinate-difference proof excludes extra internal wrap bonds even at equality |
| §4 two cell offsets | Checkerboard-preserving translations, including $(1,1)$, reduce four corner parities to two types | Choose cells at each actual corner; uniform estimates hold for every translated colouring and origin |
| §4 stationarity of potentials and finite energy | One common pattern of frames per offset | Site-dependent potentials with a uniform conditional lower bound. Enumerations identify all cell alphabets with a fixed 20,736-letter set if desired |
| §4 shell geometry and surgeries | Grid geometry, consistency, finite energy, all boundary data | All hold without translation or reflection invariance. Trial indices are limited to $i\le s$; the last step only propagates agreement |
| §4 invocation of MO94/MOS94 | Their stated settings are translation invariant | Replace their use by the finite-square argument. Impose/prove window and Hamming bounds at every translate |
| MOSPROOF window-to-coupling step | Its last sentence transfers a bound by translation invariance | Establish the stopped coupling separately at every translate with the same constants; all preceding steps are unchanged finite operations |
| MOSPROOF Theorem 6.3 | Uniform coupling bounds on every square translate; common finite energy | Exactly these hypotheses are proved. Its clamped-square counts and conditional-variance comparison do not use stationarity or common physical alphabets |
| §5 exactness / fixed window | Degree at most four at each integrated site; specific frames mentioned in the application | Quadrature works site by site for arbitrary designs. The remaining $W_B(s)$ is kept, so there is no false assertion of equal window distributions across frames |
| §5 continuous cut and (P) | Ferromagnetic plus factors, arbitrary unit pins and plane geometry | Apply after the **local** gauge. Repeated signed torus pins are among the arbitrary allowed pins. Uniform constants do not depend on their frame origin |
| §5 even $l_0\ge20$, particularly $l_0=20$ | Convenient cut geometry and integer depths | Retained auxiliary parameter. It puts no restriction on $L,N$ |
| §§6–7 walk expansion and pair recursion | Ferromagnetic continuous spin law on finite subsets of the plane | Remain entirely on that plane. The suprema already include arbitrary domains/pins. No torus frame pattern enters H1, H2 or H3′ |
| §8 translation/rotation of local patterns or trail windows | Symmetries of the infinite square lattice and rotational invariance of spherical integrals | Retained; these are not symmetries of the inhomogeneous finite frame measure |
| Appendix B even edge sets | Mod-two degree parity of finite plane chains | Retained; unrelated to the periods of a physical torus |
| Appendix C even trail lengths | The two kernel endpoints are at distance two in the bipartite **plane** | Retained. The proof never enumerates trails on the physical odd torus |
| Appendix C periodic quotient | Periods $(28,28),(28,-28)$ in a computational domination device | Retained exactly. This auxiliary quotient is independent of physical $L,N$ |
| Appendix D inversion and total-spin sectors | Rotational invariance and integer/half-integer weight parity | Retained representation-theory facts; no parity condition on the torus or the three-colouring |

The auxiliary box side $\ell$ remains even by choice. The physical torus periods, the eventual cell rectangle side lengths, and the radii of shell squares have no imposed parity restriction.

## Existing adjudications incorporated

The available reports were [ADJ-R4](../ADJ-R4/report.md), [ADJ-R5](../ADJ-R5/report.md), [ADJ-R6](../ADJ-R6/report.md), and [ADJ-MINOR](../ADJ-MINOR/report.md), all marked complete when read. Their conclusions preserve the main analytic inputs and constants. The extension is based on that corrected chain, not on the literal uncorrected source. In particular:

| Corrected interface | Treatment here |
|---|---|
| ADJ-MINOR: orientation $c_x$, squared modulus/reference weight, individual-factor bounds and exact designs | Included explicitly in §2; the new designs have their own exact proof |
| ADJ-MINOR: nontrivial alphabets and the weighted finite-size zero-total case | Retained in §3; our alphabets have at least 12 letters |
| ADJ-MINOR: final shell index, integer scales and admissible trial indices | Included in the stopped proof; the final propagation step receives no unsupported new success estimate |
| ADJ-MINOR: positive continuous normalizers and full-support cut reference law | Proved in §5.2 for arbitrary pins and the actual new frames |
| ADJ-MINOR: nonempty cut and corrected coincident-side geometric argument | Retained as unchanged geometric inputs; cut nonemptiness is made explicit in the window proof |
| ADJ-MINOR: first-removal additive four-spin cost and description of auxiliary zero spins | The $0.0707$ term is retained; the continuous U/X model and traced U/D/X networks are distinguished |
| ADJ-MINOR: weakened-response remark and noncircularity | No new weakened-response claim; the proof uses exponential (P). The dependency statement refers to continuous identities rather than claiming there are no cross-section references |
| ADJ-R4: initial two-bond D departure, exposure hypothesis, mass-carrying auxiliary networks, live-endpoint and protected-boundary closure | All retained. No attempt is made to transfer the finite frame alphabets into the traced continuous networks |
| ADJ-R4: corrected common one-point majorant and twelve exceptional departures | Retained with the same $C_T=2(12/5)^{24}(C_V/(1-q))^2$, pair envelopes and kernel |
| ADJ-R5: nonreversing arrival convention in H2 and the missing initial bond in its applications | Retained; the removed pair centre provides the required initial missing bond |
| ADJ-R5: nonnegative sub-invariant vector, zero-support check, corrected memory-walk range, exact assembly/provenance | Retained with the existing $q\le0.98075$, $\rho(M_1)\le0.98779$, $C_V\le153$; no production tail computation was rerun here |
| ADJ-R6: precise local-pattern class, exact H1 thresholds, selected example values, certificate arithmetic/provenance and closed-form boundary cases | Retained. The new frame proof does not enlarge the 7,962-pattern class or ask for a stronger threshold |

These are prerequisites already supplied by the project. `proof.tex` gives complete proofs of the new frame construction, graph theorem, local lift/gauge, uniform window transfer and inhomogeneous window-to-gap bridge. It cites unchanged manuscript geometric/removal/recursion results and reproduces the finite-square gap step using MOSPROOF's geometric count. It is an integration supplement, not a second independent certification of all Sections 6–8 or their programs.

## Expected Lean 4 effect

The clean interface is to formalize the quantum theorem over a finite simple graph first, and the classical estimates over finite product spaces with site-dependent embeddings into the sphere. This separates torus combinatorics from the polynomial and probability arguments.

New definitions and lemmas needed:

- The explicit rotation (T), its orthogonality, rotation preservation of a weighted design, and three-frame separation. All new coordinates and scalar comparisons lie in real algebra with rational coefficients and $\sqrt5$. The proof uses no floating-point fact. Only the first four moments are needed by the quantum/classical reductions, though the text proves the fifth-degree design property as well.
- The proper three-colouring of a cycle and the sum colouring of the Cartesian product, including wrap edges at odd periods.
- The multigraded UFD lemma that pairwise nonassociate bond determinants divide simultaneously, the residual-degree isomorphism, and its dimension formula. These make uniqueness a separate theorem with no mixing hypotheses.
- A plane-box quotient embedding for $L,N\ge\ell+1$, its induced-edge property, the signed boundary assignment on **plane sites or boundary legs**, and transport of conditional expectations under coordinatewise bijections. Exterior image injectivity must not be required.
- Uniform window and finite-energy hypotheses indexed by a colouring and a translate. Prove the stopped finite coupling with fixed local alphabets; comparing letters between different sites is unnecessary.
- The elementary finite-volume Poincaré bound, block variance comparison, Hamming Lipschitz eigenfunction contraction and clamped-square counts, as isolated finite lemmas if MOSPROOF has not yet supplied them.

Statements that become simpler:

- Uniqueness no longer needs full support, frame maps or an irreducible heat bath. Every torus of the stated minimum size is an immediate graph corollary.
- Every physical alphabet can be represented by `Fin 12`; every cell alphabet by four copies of `Fin 12`. The design embedding depends on the site colour. This avoids dependent cardinalities 12 versus 20 and shrinks cells from 57,600 to 20,736 letters.
- Global bipartition witnesses, well-defined checkerboard signs on `ZMod`, the two-offset equivalence argument, compatible scales and their common multiple disappear from the main theorem.
- No imported MO94/MOS94 theorem or informal binary-to-finite-alphabet extension is needed.
- The existing classical Knabe theorem already has the right inhomogeneous statement and is unchanged.

Statements that become harder or need care:

- Local box identification must transport alphabets, spins, pins and update operators explicitly. At a period $\ell+1$, two boundary lifts of the same torus vertex can receive opposite signs. Keeping boundary legs as the primitive data avoids an incorrect consistency constraint.
- The window theorem must quantify over all translates before the box-gap argument. A single origin estimate plus an unproved stationarity step is insufficient.
- A cell potential is a function of the site and its colour pattern. Use a fixed finite index alphabet with site-dependent spin embeddings, or use finite dependent products consistently.
- Polynomial multidegrees, irreducibility after adjoining other variables and tensor/SU$2$ identifications remain substantial algebraic infrastructure. The strengthened graph statement makes those reusable rather than eliminating that work.

The repaired continuous network types and computational certificate interfaces from the adjudications remain necessary. The extension adds no new H1, H2 or H3′ certificate obligation.

## Validation and remaining limits

[check_exact.py]$check_exact.py$ is an independent one-process checker using only Python's standard library and exact pairs of rational numbers for $\mathbb Q(\sqrt5)$. It imports no manuscript or referee code. Its output is [check_exact.out]$check_exact.out$:

```text
Three antipodal uniform 5-designs: 168 exact monomial checks PASS
All 432 cross-frame pairs: 1 +/- dot in [delta,2-delta] PASS
Exact minimum delta = (1/101) + (-1/505)*sqrt(5)
Minimum attained 8 times
Simple degree-four graphs and proper 3-colourings: 1024 tori PASS
Box lifts and local gauges: 395 placements PASS; 279 with repeated exterior images
```

The graph enumeration covers every $3\le L,N\le34$. The lift tests cover auxiliary sides 2, 4 and 6, all combinations $L,N\in\{\ell+1,\ell+2\}$, and every placement. These checks supplement the universal proofs; they are not used to infer infinite families from finite samples. The checker uses one core. The TeX was compiled with `pdflatex -interaction=nonstopmode -halt-on-error` and cross-references were resolved by a second pass.

Both requested goals are proved at the level of the corrected manuscript and its existing computer-assisted inputs. No new parity-dependent estimate remains unproved. This is not a Lean verification, and it does not replace independent refereeing or replay of the manuscript's large numerical certificates. The direct box proof is supplied and its inhomogeneous premises are checked explicitly, so its ongoing independent review does not conceal a translation-invariance assumption in this extension. A uniform gap for the infinitely many thin tori with $3\le\min(L,N)<L_0$ is not established here; only their uniqueness is asserted.

Only files inside `STRENGTHEN-ALL/` were written. No subagents were launched.
