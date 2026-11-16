STATUS: COMPLETE

# Integrated revision contract

This is a complete proof-writing plan, not the revised proof or a Lean verification. Every mathematical assertion to appear in the revised paper is specified below, with an owner, proof source and dependencies. “To be written” assigns a proof obligation; it does not turn an input into an axiom. The final main theorem is unconditional. The separately assigned certificate work must discharge its computational theorems before that theorem is accepted.

The baseline is the corrected manuscript at **9faa0eee768bef27a483cf7469c65c3e9958a84e**. This plan supersedes the incompatible architecture in the strengthening supplement: it keeps the three frames, all-parity torus measure and local gauge, and replaces both its cell/box route and the baseline Knabe route by one periodic block argument on physical sites.

## Sources read and precedence

- [Corrected manuscript main.tex](/home/ubuntu/aklt/manuscript-corrected/main.tex), all eight section files and all four appendix files.
- [STRENGTHEN-ALL proof.tex](/home/ubuntu/aklt/reports/STRENGTHEN-ALL/proof.tex) and [report.md](/home/ubuntu/aklt/reports/STRENGTHEN-ALL/report.md).
- [REF-SA-A](/home/ubuntu/aklt/reports/REF-SA-A/report.md) and [REF-SA-B](/home/ubuntu/aklt/reports/REF-SA-B/report.md).
- [MOSPROOF proof.tex](/home/ubuntu/aklt/reports/MOSPROOF/proof.tex), [report.md](/home/ubuntu/aklt/reports/MOSPROOF/report.md), and [REF-MOS](/home/ubuntu/aklt/reports/REF-MOS/report.md).
- [OPPORTUNITIES](/home/ubuntu/aklt/reports/OPPORTUNITIES/report.md), all entries; the adopted package is the one fixed by the author.
- [AMENDED] [Certificate-feasibility report](/home/ubuntu/aklt/compfeas/report.md), read in full, plus the coefficient checker, raw-window quotient definitions, exact H2 witness, stationary verifier definitions and exact prefix/assembly logs. The orchestrator selects the memory-10, prefix-12, radius-70 stationary route. Native exact checks are evidence, not completed Lean proofs.

The author's decisions take precedence. The two referee repairs are incorporated: every finite-energy hypothesis explicitly has \(\alpha\in(0,1]\); references to the cut construction use labels, not the incorrect “Section 5.4” locator. All retained baseline corrections remain binding, including those whose replacement proof uses a narrower interface.

## Paper order and file ownership

| Order | Contents | Owner / proposed source file |
|---|---|---|
| 1 | Model, unconditional theorem, roadmap, finite conventions | A: sec1-result.tex |
| 2 | Finite fourth moments, pin/removed-site sums, positivity, three-factor mean, quadrature, (P) | C: sec2-moments.tex |
| 3 | Polynomial space, edge lemma, torus uniqueness, frames, quantum comparison, finite energy, local gauge | A: sec3-quantum-frames.tex |
| 4 | Physical windows, stopped coupling, one square scale, direct periodic criterion, main-theorem assembly | A: sec4-periodic-gap.tex |
| 5 | Shared shell geometry, cut factorization, removal, thickened site cut, (P) implies (W) | B: sec5-window.tex |
| 6 | Mass-free trace, pair identity, response coefficients, covered patterns, H1/H2, one-point bound | C: sec6-walks.tex |
| 7 | Ordinary-domain closure, terminal defect, fixed-order kernel, positive witness, renewal, (P) | C: sec7-recursion.tex |
| 8 | Exact computational theorem statements and certification scope | C: sec8-inputs.tex |
| A | Finite conditional expectations, coupling, density/block comparison, finite contraction | A: app-finite.tex |
| B | Star-connected boundary and connected thickening | B: app-topology.tex |
| C | [AMENDED] Memory-6 one-step H2; exact memory-10 quotient; stationary Bellman domination, finite data checks and prefix assembly | C: app-input-contracts.tex |
| D | [AMENDED] Operator-only H1 reduction, ladder sectors, integer matrix reconstruction and division-free Gram/residual positivity; Bareiss fallback only | C: app-local-operator.tex |

The order intentionally permits forward references, as the baseline does. In §4 the final assembly cites §8 and §7, then §5. No proof in §§2 or 5–8 may use a classical or quantum gap conclusion. There is no Knabe section, no cell lattice, no compatible-volume theorem, no rectangular-box-gap detour, and no explicit-constant appendix.

All distances in the analytic part are ambient plane distances. The physical torus is used only in A. Pins in C/B are arbitrary unit vectors on original legs; finite energy in A concerns admissible frame letters. These are different quantifiers and must not be interchanged.

## Mathematical dependency chain and choices

[AMENDED] The computational end of this chain uses the selected Gram/residual, small-H2 and type-dependent stationary-H3 routes. The later implications are unchanged.

\[
 \text{operator-only H1, open-trail H2, type-dependent positive-vector H3}_h
 \Longrightarrow (P)
 \Longrightarrow \text{physical-site windows at every translate}
 \Longrightarrow \text{stopped square coupling with small Hamming cost}
 \Longrightarrow \text{periodic block gap}
 \Longrightarrow \text{physical-site gap}
 \Longrightarrow \text{quantum gap}.
\]

Uniqueness for every \(L,N\ge3\) has a separate algebraic proof. It uses neither the numerical inputs nor frames.

[AMENDED] The frozen choices are the three 12-letter frames; \(b=(5-\sqrt5)/505\); the physical lower bound \(\alpha=12^{-1}(b/(2-b))^4\); \(l_0=64\); \(c_{\mathrm s}=961/1000,c_{\mathrm t}=187/200\); and the exact type-dependent table in l:log-mean-bounds, including turn \(a_{\rm t}=150000/10^6\). The old \(\bar\alpha=18094/100000,\bar\beta=36751/100000\) are retained only as crude summability majorants. The choices proceed as follows:

1. [AMENDED] The selected tests supply \(C_V=10\), \(q=1119948287353/1120437614225<1\), \(h=(1,5404319552844595/4503599627370496)\), \(\rho_0=993015/10^6\), and the fixed cutoff-12 orderings. The shifted-witness and unchanged renewal lemma supply \(\theta,A\).
2. The site cut supplies \(p_0,M_\star\). Independently the frames supply \(\alpha,r_b,g_\star>0\).
3. Choose one integer \(n\) as in l:hamming, and one square radius \(M=n^8\).
4. Only then choose physical torus periods \(L,N\ge2M+3\), any proper colouring, any block placement and any exterior fibre.

The formulas inside statements are proof interfaces and normalization checks. They do not change the author's decision to state the final constants existentially.

# Interface ownership and allowed citations

The companion [interfaces.tex](interfaces.tex) is a standalone amsart statement document, without proofs. Its text is generated from the same statement registry as the inventory below. An export is the entire quantified statement, not a diagram arrow or an informal consequence.

| Boundary | Exact exports / imports |
|---|---|
| Shared notation | d:model, d:moment, d:poly, d:frame, d:framemodel, d:shells; these definitions are frozen before writing |
| C to A | l:moments (for tight frames); t:inputs and t:rec (for final assembly) |
| C to B | d:pinmodel, l:finitefacts, l:35, l:exact, h:P, t:rec |
| A to B | l:threeframes, d:framemodel, l:planeenergy (consistency, positivity and actual alphabets) |
| B to A | l:shellgeom and t:cutMOS, consuming d:W |
| C to computational owner | [AMENDED] Existing domain/pattern and H1/H2 contracts; l:response-typed, d:kernel, d:kernel-order, h:H3 and t:inputs; the new Appendix C automaton, phase, Bellman, data and prefix contracts; and Appendix D p:certificate/l:gram-residual/l:integercheck. All are labelled below and exported. |

A may not cite B's cut/removal/topology proofs or C's closure/expansion proofs directly. B may not cite the walk recursion, individual H1 patterns, or A's periodic argument; it consumes (P) and the common moment/positivity interface. C may not cite a window theorem, frame finite energy or gap. Within its own lane a writer may use every assigned internal statement.

The shared definition of (W) belongs to A's consumer contract, and B proves it. The pure shell-geometry lemma belongs to B and is exported explicitly because A's stopped coupling needs it. The common finite moment functional belongs to C; A's design calculation may cite its exact moment theorem. This arrangement allows all three lanes to write independently without waiting for another lane's proof text.

## Lane A — model, frames, uniqueness, quantum/classical comparison, periodic gap

Write §§1, 3, 4 and Appendix A. Supply every A-owned statement in the inventory. In §4 prove the stopped finite coupling for site-dependent alphabets, the one-radius Hamming estimate, the periodic placement counts, the finite eigenfunction contraction and the fibre comparison; then assemble t:main from the exported C and B theorems.

Allowed cross-lane citations: the shared definitions and C's l:moments, t:inputs, t:rec; B's l:shellgeom and t:cutMOS. A can use d:W as an assumed property while proving t:mainW. No cited MO94/MOS94 theorem is allowed; MOSPROOF supplies proof text, not a black box.

Acceptance criteria:

- The final t:main has no parity condition, no hypothesis, uniqueness for every \(L,N\ge3\), and a volume-independent positive gap once both periods exceed one threshold.
- The algebraic uniqueness proof is torus-only and works at period three. Prove divisibility in a UFD with nonassociate edge determinants; do not require comaximal ideals.
- Use the specified three rotated frames and the new exact \(b\), finite monomial norm, finite spinor choices, squared modulus and reference weights. Preserve both local orientation signs.
- Never gauge an odd torus globally. Lift each actual conditional physical square first. \(L,N\ge2M+3\) guarantees the required one-neighbourhood injection.
- Use \(\alpha=12^{-1}r_b^4\), and density comparison with boundary factors in the product reference law. The block gap is \(g_M=r_b^{2(2M+1)(2M)}\); no cell constant or cell heat bath appears.
- The stopped coupling uses conditional success and keeps both full marginals. Treat empty windows, singleton state spaces, zero residual overlap and \(\delta=1\) explicitly.
- Count block labels at rate one: containing count \(T_M\), boundary overcount \(S_M\), block gap \(T_M-S_MK\), site multiplicity \(T_M\). Recover the factor \(499/1000\) after the quantum comparison.

## Lane B — (P) to physical windows

Write §5 and Appendix B. Establish l:shellgeom independently of mixing, including parallel-side clearance. Redo the taper on physical sites with \(l_0=64\), raw boundary \(X_0\), and nearest-neighbour thickening \(X\). Prove finite partition factorization, common minorization, the one-seed removal bound, the exact geometric statement and t:cutMOS.

Allowed cross-lane citations: C's d:moment/d:pinmodel, l:moments, l:finitefacts, l:35, l:exact and h:P; A's shared frame family, l:threeframes and l:planeenergy. Treat \(\mathsf P(A,\theta)\) as the only analytic response premise. The proof of that premise is not needed.

Acceptance criteria:

- The exported window theorem covers every proper plane colouring, every translate, every indicated nonexceptional integer index and every pair of admissible boundaries. No translation invariance is inferred.
- Preserve original-leg pin conventions; new holes have no pins. Distances in removal are to the original \(S(G)\).
- Prove every stated site-scale depth and count. In particular raw near depth is \(\max(t,16)-2\), not the cell-scale doubled expression. Retain the signed-depth argument excluding coincident sides.
- Prove raw boundary star-connectivity and connectedness of its crosses. Do not use or reintroduce the no-diagonal-only-block test.
- The thickened cut is nonempty, connected, disjoint from the window and protected layer, and separates the pieces required by l:cut.
- Keep one seed with its four-spin cost. Constants \(1,4,2\), the factor \(5/\theta\) for thickening and \(p_0=e^{-2E}\) must match the interfaces.
- Transfer only the summed-out partition functions. The common reference window law retains actual frame weights and is strictly positive.

## Lane C — walk, recursion, (P), operator-only H1, computational contracts

[AMENDED] Write §§2, 6–8 and Appendices C–D. Retain the finite-moment, mass-free walk and ordinary-domain/terminal-defect proofs. Prove the new logarithmic-mean coefficient bounds and use the modified type-dependent kernel, preserving its trail weights, dead-site rule and shifts. Write every new labelled Appendix C lemma: exact raw/quotient automata, one-step H2 domination and explicit C_V, phase identity, permanent-rule stationary domination, Bellman soundness, finite-to-global extension, exact prefix evaluation, B reflection and rational assembly. In Appendix D prove division-free Gram/residual soundness and reconstruct every matrix; Bareiss is only a fallback. Integrate the supplied witnesses without launching a new certificate search.

Allowed cross-lane citations: only the frozen common definitions. C proves (P) before and independently of any use of the physical frame specification, windows or a gap. The explicit base icosahedron coordinates are part of the shared definition, not an imported mixing fact.

Acceptance criteria:

- No surface measure, all-orders moment theorem, continuous-spin disintegration or arbitrary-function rotational invariance is needed. Every used inserted observable meets the separate degree-four bound.
- Only U starts with at most three factors or D starts with at most one present bond are expanded. The second target \(e\in S\) has already lost an arrival bond. There is no silent initial two-bond D case.
- [AMENDED] Show the same coefficient identity, retain zero D response and H2 true revisit weight 1/5. Change only the response coefficients in the closed-trail kernel, with beta-prime for one removed non-outgoing neighbour and turn alpha 0.150000; use l:response-typed in T1. The uniform exceptional-step bound and T2 source constant stay valid.
- Preserve the corrected kept-set condition, full U kept sets, covering U tips, both corner slots, the protected boundary, the live endpoint, and the sole terminal boundary defect.
- Ordinary response suprema remain uniform over all consistent domains and arbitrary unit pins. Auxiliary networks are used only in the two stopped expansions.
- Preserve the absent incoming bond and forbidden initial reversal in every open-trail application, the common sum-of-maxima bound, and the at-most-twelve exceptional U departures anywhere in the second trail.
- The same fixed orderings and positive vector must work at \(\theta=1\) and after shifting. No Perron–Frobenius theorem, spectral-radius continuity or truncated-supremum fixed-point construction is needed.
- [AMENDED] Appendix D keeps one operator path, the elementary leaf bounds, product density matrices and the ladder proof. Its primary positivity certificate is E=d S^2 M-g L L^T strictly diagonally dominant with positive diagonal. A zero L covers a directly dominant block; no invertibility or Cholesky-generation claim is needed.
- [AMENDED] The H1 checker still proves raw-pattern coverage, threshold/type agreement, denominator justification, inversion/Pauli construction and every supported exchange-sector matrix. Check positive g,d,S and the exact Gram/residual inequalities with integer arithmetic. Exact divisions and positive pivots are required only if the optional Bareiss fallback is used.
- [AMENDED] Prove H2 from the memory-6, extension-1, true-revisit vector (115 dihedral classes), with exact q=q_* and C_V=10. Prove the modified H3_h from the memory-10 automaton (3741 states), five stationary m=10,L=12,R=70 potentials, Wz<=z, all caps/terminal values/local rows, and exact prefixes. Require L>=m+2. No periodic walk or remainder remains; no parity improvement is used. Approximate diagnostics or native exit codes are not theorem proofs.


[AMENDED] **Weaker-rate audit.** For the selected test, Lemma alm gives
\[
 C_V^{\rm base}=\max\{\max_{r<6}W_rq^{-r},(\max v/\min v)W_6q^{-6}\}
 \le6(200/(187q))^6<10 .
\]
Thus choose \(C_V=10\). No later result requires \(q\le0.98075\): l:Mtheta only needs \(q<1\) and finite \(C_V\) to choose \(q^2<\theta<1\); l:recineq retains finite \(C_T=2(12/5)^{24}(10/(1-q))^2\); the unchanged l:renewal gives finite \(A=(\max h/\min h)\max\{2,C_T\}/(1-\rho)\). Lane B and Lane A consume only existence of \(A,\theta\), so their statements and final existential \(c,L_0\) are unchanged.

# Full statement inventory

Each entry gives the exact LaTeX text intended for the paper. The “Interface” flag means it is reproduced in interfaces.tex; permitted consumers are specified above. The rest are internal lane statements. Source locators use baseline labels, not historical PDF numbers.


## 1. Result and conventions


### d:model — The torus Hamiltonian


**Owner:** A. **Status:** kept with edits.

**Proof source:** baseline e:H and e:B; STRENGTHEN-ALL §1.

**Dependencies:** definitions and finite elementary algebra only.

**Interface:** yes.


```latex
\begin{definition}\label{d:model}
For integers \(L,N\ge3\), let \(\Lambda=\Lambda_{L,N}=\mathbb Z_L\times\mathbb Z_N\)
with its simple, unoriented nearest-neighbour edge set \(E_{L,N}\).
The Hilbert space is \(\mathcal H_\Lambda=\bigotimes_{x\in\Lambda}V_4\).
Each site carries the spin-\(2\) space \(V_4\), and \(P_{\{x,y\}}\)
is the orthogonal projection onto total spin \(4\) in \(V_4\otimes V_4\).
Fix one orientation of each edge and set
\[
 q_{xy}=z_{x,1}z_{y,2}-z_{x,2}z_{y,1},\qquad
 B_{L,N}=\prod_{e\in E_{L,N}}q_e,\qquad
 H_{L,N}=\sum_{e\in E_{L,N}}P_e.
\]
Every edge is counted once. The spectral gap of \(H_{L,N}\) means its
smallest positive eigenvalue.
\end{definition}
```


### t:main — Unconditional main theorem


**Owner:** A. **Status:** replaces baseline t:main.

**Proof source:** STRENGTHEN-ALL t:main, restricted to the author’s scope.

**Dependencies:** p:toruskernel, t:mainW, t:cutMOS, t:rec, t:inputs.

**Interface:** internal.


```latex
\begin{theorem}\label{t:main}
For every \(L,N\ge3\), \(B_{L,N}\ne0\) and
\(\ker H_{L,N}=\mathbb C B_{L,N}\).
There exist \(c>0\) and an integer \(L_0\ge3\) such that, for all
integers \(L,N\ge L_0\), every nonzero eigenvalue of \(H_{L,N}\)
is at least \(c\).
\end{theorem}
```


Writing constraint / short proof sketch: No hypotheses appear in this theorem. The certified-input theorems must be proved before the manuscript is accepted; this plan is not a claim that their redesigned Lean certificates already exist.


## 2. Finite moment algebra and the response input


### d:moment — The finite fourth-moment functional


**Owner:** C. **Status:** new; replaces spherical integration in the core.

**Proof source:** OPPORTUNITIES #2; STRENGTHEN-ALL e:threeframes.

**Dependencies:** definitions and finite elementary algebra only.

**Interface:** yes.


```latex
\begin{definition}\label{d:moment}
Write \(\mathbb S^2=\{a\in\mathbb R^3:|a|=1\}\), put
\(\phi=(1+\sqrt5)/2\), \(r=\sqrt{\phi+2}\), and set
\[
 D=\frac1r\{(0,\pm1,\pm\phi),(\pm1,\pm\phi,0),(\pm\phi,0,\pm1)\},
 \qquad
 \mathcal M(f)=\frac1{12}\sum_{a\in D}f(a).
\]
All indicated signs are independent. Define finite probability laws
\(\lambda_{\mathrm U}=\frac1{12}\sum_{a\in D}\delta_a\) and
\(\lambda_{\mathrm D}=\frac35\lambda_{\mathrm U}+\frac25\delta_0\).
Products of these functionals always mean finite sums.
For plane sites, \(d\) denotes ambient \(\ell^1\) distance and
\(\operatorname{dist}_\infty\) denotes ambient \(\ell^\infty\) distance.
Distances to an empty set are \(+\infty\); a product over an empty site
set has its one empty configuration. For finite probabilities, use
\[
 d_{\rm TV}(p,p')=\tfrac12\sum_z|p(z)-p'(z)|,\qquad
 \operatorname{Var}_\mu f=\mu(|f-\mu f|^2),\qquad
 d_H(n,n')=\sum_x\mathbf1_{\{n_x\ne n'_x\}} .
\]
\end{definition}
```


### l:moments — Moments and bounded-degree covariance


**Owner:** C. **Status:** replaces baseline e:moments and its all-orders Gaussian proof.

**Proof source:** OPPORTUNITIES #2; STRENGTHEN-ALL l:threeframes.

**Dependencies:** d:moment.

**Interface:** yes.


```latex
\begin{lemma}\label{l:moments}
The set \(D\) has twelve distinct unit vectors and is antipodal.
For \(i,j,k,l\in\{1,2,3\}\),
\[
 \begin{gathered}
 \mathcal M(1)=1,\qquad \mathcal M(n_i)=\mathcal M(n_in_jn_k)=0,\qquad
 \mathcal M(n_in_j)=\delta_{ij}/3,\\
 \mathcal M(n_in_jn_kn_l)=
 (\delta_{ij}\delta_{kl}+\delta_{ik}\delta_{jl}+\delta_{il}\delta_{jk})/15.
 \end{gathered}
\]
For every polynomial \(p\) of total degree at most four and every
\(R\in\mathrm O(3)\), \(\mathcal M(p\circ R)=\mathcal M(p)\).
The same covariance holds for \(\lambda_{\mathrm D}\); its constant
moment is one and its moments of positive degree at most four are
\(3/5\) times those displayed above.
These assertions hold site by site for polynomials of separate degree
at most four in a finite product of spins.
\end{lemma}
```


Writing constraint / short proof sketch: Covariance is a polynomial identity on the stated degree range. It is not invariance of the finite law for arbitrary functions.


### d:pinmodel — Original legs, removals, and finite partition sums


**Owner:** C. **Status:** kept with edits.

**Proof source:** baseline s:contmodel, e:Zpin; OPPORTUNITIES #2.

**Dependencies:** d:moment.

**Interface:** yes.


```latex
\begin{definition}\label{d:pinmodel}
For finite \(G\subset\mathbb Z^2\), let
\[
 \mathcal L(G)=\{(x,z):x\in G,\ z\notin G,\ d(x,z)=1\},\qquad
 S(G)=\{x\in G:d(x,\mathbb Z^2\setminus G)\le2\}.
\]
A pin assignment is \(\tau\in(\mathbb S^2)^{\mathcal L(G)}\).
For \(Y\subset G\), write \(D_Y=G\setminus Y\) and define
\[
 Z^\tau_{D_Y}[f]=
 \sum_{n\in D^{D_Y}}12^{-|D_Y|}f(n)
 \prod_{\substack{\{x,y\}\subset D_Y\\d(x,y)=1}}(1+n_x\cdot n_y)
 \prod_{\substack{(x,z)\in\mathcal L(G)\\x\in D_Y}}
       (1+\tau_{xz}\cdot n_x).
\]
The free sum \(Z^0_{D_Y}[f]\) omits all leg factors.
Write \(Z^\bullet_{D_Y}=Z^\bullet_{D_Y}[1]\),
\(\mathbb E^\bullet_{D_Y}f=Z^\bullet_{D_Y}[f]/Z^\bullet_{D_Y}\),
and \(\Psi_{D_Y}(\tau)=Z^\tau_{D_Y}/Z^0_{D_Y}\).
Here and below \(\bullet\) is either \(\tau\) or \(0\).
The empty partition sum is one. There are no new factors on legs into \(Y\).
Different original legs may carry unrelated unit pins, even if their
outside endpoints coincide.
\end{definition}
```


### l:finitefacts — Positivity and the admissible free-positivity statement


**Owner:** C. **Status:** kept with edits; narrows unused observable generality.

**Proof source:** baseline s:contmodel and s:domains; OPPORTUNITIES #2.

**Dependencies:** d:moment, l:moments, d:pinmodel.

**Interface:** yes.


```latex
\begin{lemma}\label{l:finitefacts}
Consider a finite network with site laws \(\lambda_{\mathrm U}\) or
\(\lambda_{\mathrm D}\), retained distinct-endpoint bonds
\(1+n_x\cdot n_y\), and retained original unit-pin factors
\(1+\tau_\ell\cdot n_x\), with at most four factors incident to each site.
Its pinned and free partition sums are strictly positive, including
the empty network. Non-neighbours are conditionally independent given
the other spins on every conditioning event of positive probability.
If \(f\) is a product of scalar products of spins and the product of
\(f\) with the bond factors has separate degree at most four at every
site, then \(Z^0[f]\ge0\), hence \(\mathbb E^0 f\ge0\).
All normalized spins have norm at most one.
\end{lemma}
```


Writing constraint / short proof sketch: A finite positivity proof selects unit letters successively: each incident factor forbids at most one of twelve letters. Free positivity uses only the displayed second and fourth moment tensors.


### l:35 — The three-factor mean bound and covering tips


**Owner:** C. **Status:** kept with edits.

**Proof source:** baseline l:35 and the tip-covering argument in l:local; OPPORTUNITIES #2/#21.

**Dependencies:** l:moments, l:finitefacts.

**Interface:** yes.


```latex
\begin{lemma}\label{l:35}
For \(0\le k\le3\) and \(|a_j|\le1\), the probability law proportional to
\(\prod_{j=1}^k(1+n\cdot a_j)\lambda_{\mathrm U}(\mathrm dn)\)
has mean of norm at most \(3/5\). The same bound holds with
\(\lambda_{\mathrm D}\) in place of \(\lambda_{\mathrm U}\).
Moreover,
\[
 \left\{
 \frac{\mathcal M\!\left(n\prod_{j=1}^3(1+n\cdot a_j)\right)}
      {\mathcal M\!\left(\prod_{j=1}^3(1+n\cdot a_j)\right)}
       :a_1,a_2,a_3\in\mathbb S^2
 \right\}=\{b\in\mathbb R^3:|b|\le3/5\}.
\]
Consequently an unpinned site having at most three present factors
has conditional mean of norm at most \(3/5\), on every positive
conditioning fibre.
\end{lemma}
```


Writing constraint / short proof sketch: Keep the elementary sum-of-squares proof of the 3/5 bound. The range assertion uses the degree-four mean formula, a zero-mean triple, an aligned triple, continuity, and polynomial covariance. It does not use the deleted FKG radius lemma.


### l:exact — Finite quadrature, with its precise degree limit


**Owner:** C. **Status:** kept with edits.

**Proof source:** baseline l:exact; STRENGTHEN-ALL l:exact; OPPORTUNITIES #2.

**Dependencies:** l:moments.

**Interface:** yes.


```latex
\begin{lemma}\label{l:exact}
At each site of a finite set choose any positive weighted unit-vector
law whose moments through degree four equal those of \(\mathcal M\).
A polynomial of separate degree at most four has the same product
functional under these laws as under \(\lambda_{\mathrm U}\) at all
sites. The analogous assertion holds after replacing any chosen site
laws by \(3/5\) times that law plus \(2/5\,\delta_0\).
In particular this applies to partition products of factors
\(1\pm n_x\cdot n_y\) and \(1\pm n_x\cdot a\), \(|a|=1\), whenever
each variable occurs at most four times, and to inserted observables
only when their degrees are included in this same bound.
\end{lemma}
```


Writing constraint / short proof sketch: This transfers summed-out partition functions. It does not identify window laws on different alphabets or arbitrary observable expectations.


### h:P — The response statement passed from C to B


**Owner:** C. **Status:** kept with edits.

**Proof source:** baseline h:P/e:P; OPPORTUNITIES #2/#20.

**Dependencies:** d:pinmodel.

**Interface:** yes.


```latex
\begin{definition}[(P)]\label{h:P}
For \(A\ge2\) and \(0<\theta<1\), property \(\mathsf P(A,\theta)\)
means that, for every finite \(G\subset\mathbb Z^2\), every unit-pin
assignment on \(\mathcal L(G)\), every
\(Y\subset G\setminus S(G)\), and all \(u,v\in G\setminus Y\) with
\(d(u,v)=2\) and a common neighbour in \(Y\),
\[
 \left|\mathbb E^\tau_{G\setminus Y}(n_u\cdot n_v)
             -\mathbb E^0_{G\setminus Y}(n_u\cdot n_v)\right|
 \le A\theta^{\min\{d(u,S(G)),d(v,S(G))\}} .
\]
The distances are ambient plane distances to the original \(S(G)\);
removed sites are not added to the boundary.
\end{definition}
```


## 3. The quantum model, uniqueness, and positive frames


### d:poly — Polynomial normalization without a sphere integral


**Owner:** A. **Status:** replaces baseline e:Vinner and the global spinor choice.

**Proof source:** OPPORTUNITIES #2/#6; baseline s:poly.

**Dependencies:** definitions and finite elementary algebra only.

**Interface:** yes.


```latex
\begin{definition}\label{d:poly}
Let \(V_d\) be the homogeneous binary polynomials of degree \(d\).
Its monomials \(z_1^{d-j}z_2^j\), \(0\le j\le d\), are orthogonal with
squared norms \(\binom dj^{-1}\). The action is
\((U_gp)(z)=p(g^{-1}z)\). Use \(V_4\) at each physical site.
For each of the finitely many frame letters \(a\) choose one unit
spinor \(\zeta(a)\in\mathbb C^2\) with
\(\zeta(a)\zeta(a)^*=(I+a\cdot\sigma)/2\).
No spinor choice on the whole sphere is part of the definitions.
\end{definition}
```


### l:edge — The edge kernel


**Owner:** A. **Status:** kept as is (with the torus understood).

**Proof source:** baseline l:edge; Cartan proof from OPPORTUNITIES #6.

**Dependencies:** d:model, d:poly.

**Interface:** internal.


```latex
\begin{lemma}\label{l:edge}
For \(e=\{x,y\}\) and \(\varphi\in\mathcal H_\Lambda\),
\(P_e\varphi=0\) if and only if
\(\varphi=q_e\chi\), where \(\chi\) is homogeneous of degree three
in \(z_x,z_y\) and degree four in every other site variable.
\end{lemma}
```


Writing constraint / short proof sketch: Use the Cartan map p(z_x,z_y) -> p(z,z): it is onto V_8, its kernel is the 16-dimensional determinant image, and its adjoint image is the total-spin-4 space. This is the chosen proof path; no full Clebsch–Gordan decomposition is required.


### l:divisibility — Local divisibility on the torus


**Owner:** A. **Status:** kept with edits (torus scope only).

**Proof source:** baseline l:divisibility; STRENGTHEN-ALL p:graphkernel algebra.

**Dependencies:** l:edge.

**Interface:** internal.


```latex
\begin{lemma}\label{l:divisibility}
Let \(L,N\ge3\), \(R\subset\Lambda_{L,N}\), and
\(E_R=\{e\in E_{L,N}:e\cap R\ne\varnothing\}\).
If \(\varphi\in\mathcal H_\Lambda\) and \(P_e\varphi=0\)
for every \(e\in E_R\), then
\(\varphi=(\prod_{e\in E_R}q_e)\chi\), where \(\chi\) is independent
of every \(z_x\), \(x\in R\).
\end{lemma}
```


### p:toruskernel — Uniqueness at every stated size


**Owner:** A. **Status:** new; replaces the all-graph strengthening by its torus specialization.

**Proof source:** STRENGTHEN-ALL p:graphkernel; REF-SA-A.

**Dependencies:** l:divisibility.

**Interface:** internal.


```latex
\begin{proposition}\label{p:toruskernel}
For every \(L,N\ge3\), the torus is simple and has four distinct
neighbours at each site, \(B_{L,N}\ne0\), and
\(\ker H_{L,N}=\mathbb C B_{L,N}\).
Changing edge orientations does not change this one-dimensional space.
\end{proposition}
```


Writing constraint / short proof sketch: Take R equal to the torus. This proof has no frame, mixing, or computer-assisted premise. State no general-graph ground-space theorem.


### l:star — The fixed star comparison


**Owner:** A. **Status:** kept as is (promoted from e:star).

**Proof source:** baseline e:star; REF-SA-A finding 2.

**Dependencies:** l:edge.

**Interface:** internal.


```latex
\begin{lemma}\label{l:star}
Let \(h_\star=\sum_{j=1}^4P_{\{0,j\}}\) on \(V_4^{\otimes5}\).
Its smallest positive eigenvalue \(g_\star\) exists and is positive.
For \(L,N\ge3\), set \(H_x=\sum_{e\ni x}P_e\) and
\(\mathcal S_x=\ker H_x\). Then
\[
 H_x\ge g_\star(I-\Pi_{\mathcal S_x}),\qquad
 \sum_xH_x=2H_{L,N}.
\]
\end{lemma}
```


### d:frame — Finite moment frames


**Owner:** A. **Status:** kept with edits.

**Proof source:** baseline d:frame; OPPORTUNITIES #2.

**Dependencies:** d:moment.

**Interface:** yes.


```latex
\begin{definition}\label{d:frame}
A frame is a finite set \(A\subset\mathbb S^2\) with positive weights
\(w(a)\) summing to one such that
\(\sum_{a\in A}w(a)p(a)=\mathcal M(p)\)
for every real polynomial \(p\) of degree at most four.
\end{definition}
```


### l:tight — The coherent-state tight frame identity


**Owner:** A. **Status:** kept as is.

**Proof source:** baseline l:tight, with algebraic norm verification from OPPORTUNITIES #2.

**Dependencies:** d:poly, d:frame, l:moments.

**Interface:** yes.


```latex
\begin{lemma}\label{l:tight}
For every frame \((A,w)\) and every \(p\in V_4\),
\[
 \sum_{a\in A}5w(a)|p(\zeta(a))|^2=\|p\|_{V_4}^2.
\]
For site frames \((D_x,w_x)\), set \(\Omega=\prod_xD_x\),
\(\pi(s)=\prod_x5w_x(s_x)\), and
\(\iota\varphi(s)=\varphi((\zeta(s_x))_x)\).
Then \(\iota:\mathcal H_\Lambda\to\ell^2(\Omega,\pi)\) is an isometry.
\end{lemma}
```


### l:threeframes — The three rotated icosahedra


**Owner:** A. **Status:** replaces baseline e:icodod and the dodecahedral construction.

**Proof source:** STRENGTHEN-ALL l:threeframes; REF-SA-A.

**Dependencies:** d:moment, l:moments, d:frame.

**Interface:** yes.


```latex
\begin{lemma}\label{l:threeframes}
Let
\[
 T=\begin{pmatrix}99/101&-20/101&0\\20/101&99/101&0\\0&0&1\end{pmatrix},
 \quad D^{(j)}=T^jD\ (j=0,1,2),\quad
 b=\frac{5-\sqrt5}{505},\quad r_b=\frac b{2-b}.
\]
The matrix \(T\) is in \(\mathrm{SO}(3)\).
Each \(D^{(j)}\), with uniform weights \(1/12\), is an antipodal frame.
For \(i\ne j\), \(a\in D^{(i)}\), \(a'\in D^{(j)}\),
\[
 0<b<1,\qquad b\le1\pm a\cdot a'\le2-b,\qquad0<r_b<1.
\]
The common lower bound \(b\) is attained, and distinct frames are
disjoint even up to antipodal signs.
\end{lemma}
```


### l:colour — A proper colouring for all tori


**Owner:** A. **Status:** new.

**Proof source:** STRENGTHEN-ALL l:colour; REF-SA-A.

**Dependencies:** d:model.

**Interface:** internal.


```latex
\begin{lemma}\label{l:colour}
For \(m\ge3\) and representatives \(0\le i<m\), put
\[
 a_m(i)=\begin{cases}2,&m\text{ odd and }i=m-1,\\i\bmod2,&\text{otherwise}.
 \end{cases}
\]
Then \(\kappa(i,j)=a_L(i)+a_N(j)\pmod3\) is a proper
three-colouring of \(\Lambda_{L,N}\) for every \(L,N\ge3\).
\end{lemma}
```


### l:qmod — The determinant modulus identity


**Owner:** A. **Status:** kept as is (promoted from e:qmod).

**Proof source:** baseline e:qmod.

**Dependencies:** d:poly.

**Interface:** internal.


```latex
\begin{lemma}\label{l:qmod}
For unit spinors \(\zeta,\zeta'\) with
\(\zeta\zeta^*=(I+a\cdot\sigma)/2\) and
\(\zeta'\zeta'^*=(I+a'\cdot\sigma)/2\),
\[
 |\zeta_1\zeta'_2-\zeta_2\zeta'_1|^2=(1-a\cdot a')/2 .
\]
\end{lemma}
```


### d:framemodel — The torus and plane frame specifications


**Owner:** A. **Status:** kept with edits; replaces e:muD and e:QDrot.

**Proof source:** STRENGTHEN-ALL e:mucirc/e:muDW; OPPORTUNITIES #16.

**Dependencies:** l:threeframes, d:model, d:poly, l:tight.

**Interface:** yes.


```latex
\begin{definition}\label{d:framemodel}
Given any proper three-colouring \(\kappa\) of a plane or torus,
put \(D_x=D^{(\kappa(x))}\), with weights \(1/12\).
On the torus define
\[
 \mu^{\mathrm{af}}_{\kappa,L,N}(s)=
 \frac1{Z^{\mathrm{af}}}\prod_x\frac1{12}
       \prod_{\{x,y\}\in E_{L,N}}(1-s_x\cdot s_y).
\]
On the plane, for finite \(W\subset\mathbb Z^2\) and
\(\eta_z\in D_z\) at exterior neighbour sites, define
\[
 \mu^{+,\eta}_{\kappa,W}(n)=\frac1{Z^{+,\eta}_{\kappa,W}}
 \prod_{x\in W}\frac1{12}
 \prod_{\substack{\{x,y\}\subset W\\d(x,y)=1}}(1+n_x\cdot n_y)
 \prod_{\substack{x\in W,z\notin W\\d(x,z)=1}}(1+n_x\cdot\eta_z).
\]
Only the finitely many needed exterior letters are specified.
These laws have full support. Write \(E_U\) for conditioning off \(U\),
\(\operatorname{Var}_U f=E_U|f-E_Uf|^2\), and
\[
 \mathcal D_\mu(f)=\sum_x\mu(\operatorname{Var}_x f),\qquad
 \lambda(\mu)=\inf_{\operatorname{Var}_\mu f>0}
             \frac{\mathcal D_\mu(f)}{\operatorname{Var}_\mu f}.
\]
All generators have one update per physical site. A gap lower bound is
always equivalently a Poincare inequality, including one-point spaces.
\end{definition}
```


### l:quantumfibre — The signed local comparison


**Owner:** A. **Status:** kept as is (promoted from the corrected proof and e:QDcomp).

**Proof source:** baseline t:QD proof/e:QDcomp; STRENGTHEN-ALL e:cx.

**Dependencies:** l:qmod, l:divisibility, l:tight, d:framemodel.

**Interface:** internal.


```latex
\begin{lemma}\label{l:quantumfibre}
Fix \(x\), write \(q_e=\epsilon_{e,x}q_{xy}\) for \(e=\{x,y\}\),
and set
\[
 c_x=\prod_{e\ni x}\epsilon_{e,x},\quad
 \beta_x(t;\sigma)=\prod_{y\sim x}q_{xy}(\zeta(t),\zeta(\sigma_y)),
 \quad \rho_x=c_x\prod_{e\not\ni x}q_e .
\]
All products are evaluated at the corresponding frame spinors.
Then \(\iota B=\beta_x\rho_x\), and if
\(\psi=(\prod_{e\ni x}q_e)\chi\) with \(\chi\) independent of \(z_x\),
then \(\iota\psi=c_x\beta_x\,\iota\chi\).
Let \(\mathcal P_x\) be the fibrewise orthogonal projection in
\(\ell^2(\Omega,\pi)\) onto the span of \(\beta_x\), and put
\(Uf=f\,\iota B/\|B\|\).
The map \(U:L^2(\mu^{\rm af})\to\ell^2(\Omega,\pi)\) is unitary,
\(UE_x=\mathcal P_xU\), and
\[
 \|(I-\mathcal P_x)\iota\varphi\|
            \le\|(I-\Pi_{\mathcal S_x})\varphi\|.
\]
\end{lemma}
```


Writing constraint / short proof sketch: The notation iota chi means evaluation even though the residual polynomial is not itself a full-degree physical state. Its evaluation is multiplicative; no isometry for that residual degree is asserted.


### t:QD — Quantum to classical comparison on every torus


**Owner:** A. **Status:** kept with edits.

**Proof source:** baseline t:QD/e:QDcomp; STRENGTHEN-ALL t:QD; REF-SA-A.

**Dependencies:** l:star, l:divisibility, l:tight, d:framemodel, l:threeframes, l:quantumfibre.

**Interface:** internal.


```latex
\begin{theorem}\label{t:QD}
For every \(L,N\ge3\) and every proper torus three-colouring,
\[
 \mu^{\mathrm{af}}(s)=
 \frac{\pi(s)|\iota B_{L,N}(s)|^2}{\|B_{L,N}\|^2},\qquad
 H_{L,N}\big|_{B_{L,N}^{\perp}}\ge
       \frac{g_\star}{2}\lambda(\mu^{\mathrm{af}})I .
\]
In particular
\(\operatorname{gap}(H_{L,N})\ge(g_\star/2)\lambda(\mu^{\mathrm{af}})\).
\end{theorem}
```


Writing constraint / short proof sketch: Retain the orientation factor c_x = product of epsilon_{e,x} in both local factorizations, the squared modulus, unnormalized reference measure pi, and the inclusion of quantum local ground vectors in the classical fibre range. Do not strengthen that inclusion to equality.


### l:planeenergy — Uniform finite energy and conditional consistency


**Owner:** A. **Status:** replaces the cell finite-energy and local comparison constants.

**Proof source:** STRENGTHEN-ALL e:energy; OPPORTUNITIES #7/#16; MOSPROOF lem:spec.

**Dependencies:** d:framemodel, l:threeframes, l:density.

**Interface:** yes.


```latex
\begin{lemma}\label{l:planeenergy}
All the frame specifications above are consistent under conditioning
and have nearest-neighbour Markov dependence. Uniformly over proper
colourings, finite volumes, admissible frame-valued boundaries, and
fully specified one-site fibres, every letter has conditional
probability at least
\[
 \alpha=\frac1{12}r_b^4\in(0,1].
\]
The same lower bound holds after conditioning on fewer letters.
Any prescribed assignment on \(k\) sites, under arbitrary consistent
partial conditioning off those sites, has conditional probability
at least \(\alpha^k\).
For a finite plane block \(Q\), the single-site heat bath of every conditional block law in \(Q\) has Poincare gap at least
\(r_b^{|E(Q)|}\), where \(E(Q)\) is its internal edge set.
\end{lemma}
```


Writing constraint / short proof sketch: Use the density comparison of l:density: absorb all boundary factors into a positive product reference law. Only internal bonds enter the density ratio. No finite-energy bound is claimed for arbitrary unit-vector pins.


### l:boxlift — Local gauge for a lifted physical square


**Owner:** A. **Status:** replaces baseline l:boxcell and r:Kpins.

**Proof source:** STRENGTHEN-ALL l:boxcell/e:localgauge; OPPORTUNITIES #1/#16.

**Dependencies:** d:framemodel, l:threeframes.

**Interface:** internal.


```latex
\begin{lemma}\label{l:boxlift}
Let \(Q'=a+\{-M,\ldots,M\}^2\subset\mathbb Z^2\), \(M\ge1\),
and \(L,N\ge2M+3\). Reduction modulo the periods is injective
on the \(\ell^\infty\) one-neighbourhood of \(Q'\), preserves exactly
the internal nearest-neighbour edges of \(Q'\), and identifies all its
crossing bonds with the torus crossing bonds of its image \(Q\).
For every torus outside configuration \(\sigma\), pull back the
colouring and set
\[
 n_z=(-1)^{z_1+z_2}s_{p(z)}\quad(z\in Q'),\qquad
 \eta_z=(-1)^{z_1+z_2}\sigma_{p(z)}
       \quad(z\notin Q',\ d(z,Q')=1).
\]
This coordinatewise bijection carries the conditional
antiferromagnetic law in \(Q\) to
\(\mu^{+,\eta}_{\kappa\circ p,Q'}\), intertwines every site update,
and preserves Hamming distances between configurations in each fibre.
\end{lemma}
```


Writing constraint / short proof sketch: No global sign function on an odd torus is defined. The two spare sites per coordinate deliberately avoid exterior identifications; no parity assumption or 2 by 2 cell is used.


## 4. Windows, stopped coupling, and the periodic block gap


### d:shells — Physical-site shells and exceptional indices


**Owner:** A (frozen shared definition). **Status:** kept with edits.

**Proof source:** baseline e:shells; MOSPROOF eq:shells; OPPORTUNITIES #16.

**Dependencies:** d:moment.

**Interface:** yes.


```latex
\begin{definition}\label{d:shells}
For \(a\in\mathbb Z^2\), integer \(u\ge1\), put
\(C_u(a)=a+\{-u,\ldots,u\}^2\).
For \(\operatorname{dist}_\infty(y,C_u(a))=1\), let
\(s=u^{1/4}\), \(k_i=\lfloor is\rfloor\), \(i_1=\lfloor s\rfloor+1\).
For an integer \(l_0\ge1\) define
\[
 \begin{split}
 F_i&=\{x\in C_u(a):|x-y|_\infty>(i-1)s\},\\
 D_i&=\{x\in C_u(a):|x-y|_\infty=k_i\},\\
 A_i&=\{x\in D_i:\operatorname{dist}_\infty
                    (x,\mathbb Z^2\setminus C_u(a))\le l_0\},\qquad
 B_i=D_i\setminus A_i .
 \end{split}
\]
Let \(I_0\) consist of the integers \(2\le i\le i_1\) for which
some point of \(D_i\) is at distance strictly less than \(s/3\)
from a corner site of \(C_u(a)\).
All these are sets of physical sites.
\end{definition}
```


### d:W — The uniform window interface


**Owner:** A (contract); B (establishes it). **Status:** kept with edits.

**Proof source:** baseline d:W; STRENGTHEN-ALL d:W; OPPORTUNITIES #16/#20.

**Dependencies:** d:framemodel, d:shells.

**Interface:** yes.


```latex
\begin{definition}[(W)]\label{d:W}
The family of plane frame specifications has \(\mathsf W(l_0,p_0,M_\star)\)
if \(l_0,M_\star\) are positive integers, \(0<p_0\le1\), and,
for every proper plane three-colouring, every translate \(C_u(a)\)
with integer \(u\ge M_\star\), every \(y\) as in Definition~\ref{d:shells},
every integer \(2\le i\le u^{1/4}\) outside \(I_0\), and every two
admissible frame-valued boundary conditions \(\eta,\xi\) for \(F_i\),
\[
 d_{\mathrm{TV}}\!\left(
       \mu^{+,\eta}_{\kappa,F_i,B_i},
       \mu^{+,\xi}_{\kappa,F_i,B_i}\right)\le1-p_0 .
\]
The subscript \(B_i\) denotes a marginal. Boundaries are arbitrary
within their site alphabets; they need not agree anywhere.
\end{definition}
```


### l:stopped — The stopped coupling at site scale


**Owner:** A. **Status:** replaces the coupling proof behind baseline p:surgery.

**Proof source:** MOSPROOF lem:stopped; STRENGTHEN-ALL l:stopped; OPPORTUNITIES #16.

**Dependencies:** d:W, l:shellgeom, l:planeenergy, l:finitecoupling, l:surgery.

**Interface:** internal.


```latex
\begin{lemma}\label{l:stopped}
Suppose a consistent positive plane specification with site-dependent
finite alphabets has range one in \(\ell^\infty\), one-site probabilities
at least \(\alpha\in(0,1]\), and the window bound (W) at every translate.
Put \(\delta=p_0\alpha^{16l_0}\) and
\(M_{\mathrm g}(l_0)=\max\{16,6(l_0+1)\}^4\).
For \(u\ge\max\{M_\star,M_{\mathrm g}(l_0)\}\), boundaries of \(C_u(a)\)
agreeing off one exterior site \(y\), and any integer
\(4\le h\le\lfloor u^{1/4}\rfloor\), there is a coupling of the
full laws such that
\[
 \mathbb P(n_{Q_h}\ne n'_{Q_h})\le(1-\delta)^{h-3},
 \qquad Q_h=\{x\in C_u(a):|x-y|_\infty>hu^{1/4}\}.
\]
If \(y\) is farther than range one, the full laws are equal.
\end{lemma}
```


Writing constraint / short proof sketch: Use trials 2 through h and propagation through h+1. Independently resample A_i after coupling/completing B_i. Multiply conditional failure bounds, not unconditional probabilities. No success estimate at an index above s is used.


### p:surgery — The corrected original terminal-radius conclusion


**Owner:** A. **Status:** kept with edits (as a short corollary).

**Proof source:** baseline p:surgery; MOSPROOF cor:originalprop.

**Dependencies:** l:stopped.

**Interface:** internal.


```latex
\begin{corollary}\label{p:surgery}
Under the hypotheses and size threshold of Lemma~\ref{l:stopped},
the same two laws have marginal total variation at most
\((1-\delta)^{u^{1/4}-4}\) on
\(\{x\in C_u(a):|x-y|_\infty>u^{1/2}\}\).
When \(\delta=1\), this upper bound is zero.
\end{corollary}
```


Writing constraint / short proof sketch: This corollary is retained but is not the input to periodic contraction. The earlier stopped coupling is essential.


### l:hamming — One square scale with small Hamming cost


**Owner:** A. **Status:** new; narrows MOSPROOF lem:windowK to one radius.

**Proof source:** MOSPROOF lem:tail/lem:windowK; OPPORTUNITIES #1/#16.

**Dependencies:** l:stopped, l:finitecoupling.

**Interface:** internal.


```latex
\begin{lemma}\label{l:hamming}
Assume (W) and \(\alpha\in(0,1]\) as above, and put
\(d_0=\min\{1/2,p_0\alpha^{16l_0}\}\).
Choose an integer \(n\) satisfying
\[
 n\ge44,\quad n^8\ge M_\star,\quad
 n^2\ge\max\{50000,6(l_0+1)\},\quad
 n^{12}d_0^{20}\ge50000\,2^{20}\,20!.
\]
Such an integer exists. Set \(M=n^8\).
Every translated \(C_M(a)\), with any two admissible boundaries
agreeing off one exterior site, admits a full-law coupling with
expected Hamming distance at most \(M/1000\).
One sufficient bound is
\[
 25n^6+25n^{16}(1-d_0)^{n-3}\le M/1000.
\]
\end{lemma}
```


Writing constraint / short proof sketch: Keep n and M as existence scales. The finite binomial estimate (1-d_0)^(n-3) <= 2^20 20!/(d_0^20 n^20) proves the displayed claim. No clamped squares or interval of block radii is needed.


### t:periodic — Direct periodic physical-site block criterion


**Owner:** A. **Status:** new; replaces baseline t:K and c:gapcell.

**Proof source:** OPPORTUNITIES #1/#16; MOSPROOF lem:contraction/lem:comparison.

**Dependencies:** l:contraction, l:comparison.

**Interface:** internal.


```latex
\begin{theorem}\label{t:periodic}
Let \(M\ge1\), \(L,N\ge2M+3\), and let \(\mu>0\) be a
probability on a finite product over \(\Lambda_{L,N}\) whose
conditional law on any set depends only on letters in its exterior
\(\ell^\infty\) one-neighbourhood.
For every translated square \(Q\) of side \(2M+1\), suppose that:
the single-site heat bath of every conditional law on \(Q\) has Poincare gap at least
\(g>0\); and any two conditional block laws whose outside
configurations agree off one site admit a coupling with expected
Hamming distance in \(Q\) at most \(K\ge0\), whenever that site is
outside and at \(\ell^\infty\) distance one from \(Q\).
Put \(T_M=(2M+1)^2\), \(S_M=8M+8\), and suppose \(S_MK<T_M\).
Then
\[
 \sum_{Q}(I-E_Q)\text{ has Poincare gap at least }T_M-S_MK,\qquad
 \lambda(\mu)\ge g\left(1-\frac{S_MK}{T_M}\right).
\]
The sum is over all torus translates, each at rate one.
In particular, \(K\le M/1000\) implies
\(\lambda(\mu)\ge(499/500)g\).
\end{theorem}
```


Writing constraint / short proof sketch: A fixed site belongs to exactly T_M translated blocks; exactly S_M blocks exclude it at infinity-distance one (this includes four harmless corner positions for nearest-neighbour fields). Counts use labels/placements, never invariant eigenvectors. The block gap and its comparison must both use unnormalized rates.


### t:mainW — Assembly from the physical window estimate


**Owner:** A. **Status:** replaces baseline t:mainW.

**Proof source:** OPPORTUNITIES #1/#7/#16; STRENGTHEN-ALL local gauge and comparison.

**Dependencies:** l:hamming, l:boxlift, l:planeenergy, t:periodic, t:QD, p:toruskernel.

**Interface:** internal.


```latex
\begin{theorem}\label{t:mainW}
If the plane frame family satisfies (W), there exist \(c>0\) and
an integer \(L_0\ge3\) such that
\(\ker H_{L,N}=\mathbb C B_{L,N}\) and every nonzero eigenvalue is
at least \(c\), for all integers \(L,N\ge L_0\).
\end{theorem}
```


Writing constraint / short proof sketch: For the existence scale M, use g_M = r_b^[2(2M+1)(2M)], take L_0=2M+3, and use the quantum comparison with c=(499/1000) g_star g_M. These are symbolic normalization checks in the proof; the theorem and abstract keep c and L_0 existential. There is no explicit-constant appendix.


## 5. The cut and the site-scale window theorem


### l:shellgeom — Shared shell geometry, including parallel clearance


**Owner:** B. **Status:** kept with edits.

**Proof source:** baseline l:shellgeom; MOSPROOF lem:geometry; REF-MOS insertion note.

**Dependencies:** d:shells.

**Interface:** yes.


```latex
\begin{lemma}\label{l:shellgeom}
For \(u\ge M_{\mathrm g}(l_0)=\max\{16,6(l_0+1)\}^4\),
\(|I_0|\le1\), and \(D_i\subset F_i\) for \(2\le i\le i_1\).
For \(2\le i\le i_1\) outside \(I_0\), \(|A_i|\le8l_0\).
Every side of \(y+[-k_i,k_i]^2\) parallel to an edge of \(C_u(a)\)
and meeting \(C_u(a)\) is at distance at least \(s/3\) from the
exterior half-plane beyond that edge.
For \(i\ge2\), every point of \(C_u(a)\setminus F_i\)
within \(\ell^\infty\) distance one of \(F_i\) lies in \(D_{i-1}\);
\(y\) is not within that distance of \(F_i\).
\end{lemma}
```


Writing constraint / short proof sketch: This pure geometry lemma is B’s second export to A. Include the parallel-side clearance in the statement, since the cut count consumes it. Coordinate reflections do not assert symmetry of any Gibbs specification.


### l:cut — Factorization and common minorization


**Owner:** B. **Status:** kept with edits; replaces the tanh conclusion.

**Proof source:** baseline l:cut; STRENGTHEN-ALL e:windowlaw–e:cutratio; OPPORTUNITIES #10.

**Dependencies:** l:exact, l:finitefacts, d:framemodel.

**Interface:** internal.


```latex
\begin{lemma}\label{l:cut}
Let \(F\subset\mathbb Z^2\) be finite, \(B\subset F\) have no
neighbour outside \(F\), and \(G=F\setminus B\).
Suppose \(X\subset G\) and \(G\setminus X=G_1\sqcup G_2\), with
no bond between the pieces, no site of \(G_1\) adjacent to \(F^c\),
and no site of \(G_2\) adjacent to \(B\).
For the original legs of \(G\), use pins \(\eta\) into \(F^c\)
and window letters \(s\) into \(B\). Put
\[
 e(\eta,s)=\log\Psi_{G\setminus X}(\eta s)-\log\Psi_G(\eta s).
\]
If \(|e(\eta,s)|\le E<\infty\) for all admissible \(\eta,s\),
then there is a strictly positive probability \(\nu\) on window
configurations, independent of \(\eta\), such that
\[
 e^{-2E}\nu(s)\le\mu^{+,\eta}_{\kappa,F}(n_B=s)
                         \le e^{2E}\nu(s).
\]
Consequently any two window laws have total variation at most
\(1-e^{-2E}\).
One may take \(\nu(s)\) proportional to \(W_B(s)Z_{G_1}^{s}\),
where \(W_B\) is the actual product of frame site weights and
internal window bond weights. Only original legs are retained in
the partition functions after removing \(X\).
\end{lemma}
```


Writing constraint / short proof sketch: Keep the full-support check for nu and every normalizer. The overlap identity with the common minorization replaces likelihood-ratio optimization; no hyperbolic function is required.


### l:removal — One seed and a connected removal order


**Owner:** B. **Status:** replaces baseline l:removal constants.

**Proof source:** baseline l:removal/e:Ij/e:telescope; OPPORTUNITIES #10.

**Dependencies:** h:P, l:35, l:finitefacts, l:moments.

**Interface:** internal.


```latex
\begin{lemma}\label{l:removal}
Assume \(\mathsf P(A,\theta)\), and put
\(\mathsf F(d)=A\theta^{\max\{d,0\}}\).
Let \(x_1,\ldots,x_p\) be distinct points of \(G\), \(p\ge1\),
with \(b_G(x_j)=d(x_j,G^c)\ge3\), such that each \(x_j\), \(j\ge2\),
has a nearest neighbour among its predecessors.
For \(X=\{x_1,\ldots,x_p\}\) and every original unit-pin assignment,
\[
 |\log\Psi_{G\setminus X}(\tau)-\log\Psi_G(\tau)|
 \le1+4\mathsf F(b_G(x_1)-3)
                  +2\sum_{j=2}^p\mathsf F(b_G(x_j)-3).
\]
\end{lemma}
```


Writing constraint / short proof sketch: The first four-neighbour removal remains a seed. Its raw four-spin bracket costs at most 1 after logarithmic comparison; do not drop this additive term. Later removals have at most three neighbours. It suffices to bound every integrated factor below by 1/2.


### d:thickcut — The tapered site set and thickened cut


**Owner:** B. **Status:** replaces baseline e:Ucut/e:Xcut (no cells).

**Proof source:** OPPORTUNITIES #3/#16; baseline s:cutgeom.

**Dependencies:** d:shells.

**Interface:** internal.


```latex
\begin{definition}\label{d:thickcut}
Fix \(l_0=64\), a nonexceptional shell with \(2\le i\le s\),
and write \(k=k_i\), \(F=F_i\), \(B=B_i\), \(G=F\setminus B\).
For \(z\in\mathbb Z^2\), set
\[
 t(z)=\big||z-y|_\infty-k\big|,\qquad
 h(z)=\operatorname{dist}_\infty(z,C_u(a)^c)\quad
        (h(z)=0\text{ outside }C_u(a)).
\]
Define
\[
 \begin{gathered}
 U=\{z\in C_u(a):t(z)\le\min(h(z)-32,s/12)\},\\
 X_0=\{z\notin U:\operatorname{dist}_\infty(z,U)=1\},\qquad
 X=\{z:d(z,X_0)\le1\}.
 \end{gathered}
\]
Set \(G_1=(U\setminus B)\setminus X\) and
\(G_2=G\setminus(U\cup X)\).
\end{definition}
```


### l:cutgeom — The physical geometry and summable cut cost


**Owner:** B. **Status:** replaces baseline l:cutgeom.

**Proof source:** baseline l:cutgeom with OPPORTUNITIES #3/#16; to be written at site scale.

**Dependencies:** d:thickcut, l:shellgeom.

**Interface:** internal.


```latex
\begin{lemma}\label{l:cutgeom}
There exists \(s_0\ge\max\{16,6(64+1)\}\) such that, uniformly
in the translate, \(y\), and nonexceptional integer \(2\le i\le s\),
the following hold for \(s=u^{1/4}\ge s_0\).
The set \(U\) is finite, nonempty, and star-connected, and \(U^c\)
is star-connected. We have \(B\subset U\subset F\), all neighbours
of \(B\) lie in \(U\), and no site of \(U\) is adjacent to \(F^c\).
The set \(X_0\) is nonempty and lies in \(G\). For \(x\in X_0\),
\[
 b_G(x)\ge
 \begin{cases}\max\{t(x),16\}-2,&t(x)\le s/12,\\s/12-1,&t(x)>s/12,
 \end{cases}
 \qquad b_G(x)\ge14 .
 \]
For each integer \(j\ge0\), there are at most \(48\) sites of
\(X_0\) with \(t(x)=j\le s/12\).
For \(0<\vartheta<1\), put
\[
 C_{\rm near}(\vartheta)=48\vartheta^{14}
                \left(17+\frac1{1-\vartheta}\right).
\]
Then
\[
 \sum_{x\in X_0}\vartheta^{b_G(x)}
 \le C_{\rm near}(\vartheta)
                 +4(2u+1)^2\vartheta^{s/12-1}.
\]
The thickened set \(X\) lies in \(G\), has \(b_G\ge13\), and
\(G\setminus X=G_1\sqcup G_2\) satisfies all separation and
no-adjacency assumptions of Lemma~\ref{l:cut}. Moreover
\[
 \sum_{z\in X}\vartheta^{b_G(z)}
       \le5\vartheta^{-1}\sum_{x\in X_0}\vartheta^{b_G(x)} .
\]
\end{lemma}
```


Writing constraint / short proof sketch: The site-scale near estimate loses the baseline factor two. Count intersections of the two square boundaries using signed inward depths and the exported parallel clearance; retain the corrected coincident-side argument. Radial paths prove connectivity of U and its complement. The deleted no-diagonal-only-block argument is not needed.


### l:Xconn — Connectedness of the thickened cut


**Owner:** B. **Status:** replaces baseline l:Xconn.

**Proof source:** OPPORTUNITIES #3; baseline topology Steps 1–2.

**Dependencies:** l:cutgeom, l:boundaryconn, l:thicken.

**Interface:** internal.


```latex
\begin{lemma}\label{l:Xconn}
Under Lemma~\ref{l:cutgeom}, the finite nonempty cut \(X\) is
nearest-neighbour connected. Hence it can be ordered so that every
site after the first has a previously listed nearest neighbour.
\end{lemma}
```


### t:cutMOS — The interface from (P) to physical windows


**Owner:** B. **Status:** replaces baseline t:cutMOS.

**Proof source:** baseline t:cutMOS; STRENGTHEN-ALL uniformity; OPPORTUNITIES #3/#10/#16.

**Dependencies:** h:P, l:cut, l:removal, l:cutgeom, l:Xconn, d:W.

**Interface:** yes.


```latex
\begin{theorem}\label{t:cutMOS}
If \(\mathsf P(A,\theta)\) holds, then the family of plane frame
specifications has \(\mathsf W(64,p_0,M_\star)\), with common
\(p_0\in(0,1]\) and integer \(M_\star\ge1\) depending only on
\(A,\theta\). The constants work for every proper plane
three-colouring and every translate.
Specifically, let
\[
 E=1+4A+10A\theta^{-4}
       \left[48\theta^{14}\left(17+\frac1{1-\theta}\right)+1\right],
 \qquad p_0=e^{-2E}.
\]
There exists an integer \(M_\star\ge1\) for which (W) holds
with this displayed choice of \(p_0\).
\end{theorem}
```


Writing constraint / short proof sketch: The proof uses only the common finite moment/partition interface and actual positive window weights. It must not infer equality of discrete marginals across colourings. Refer to source labels, correcting the REF-SA-B subsection-locator defect. Choose M_star so that every later u meets the geometric s_0 threshold and 4(2u+1)^2 theta^(u^(1/4)/12-1) <= 1.


## 6. Walk expansion without scalar trace masses


### d:domain — Ordinary domains and auxiliary terminal networks


**Owner:** C. **Status:** kept with edits; removes only the scalar mass field.

**Proof source:** baseline d:domain with corrected auxiliary networks; OPPORTUNITIES #2/#4.

**Dependencies:** d:pinmodel, d:moment.

**Interface:** yes.


```latex
\begin{definition}\label{d:domain}
Fix finite \(G\), \(S=S(G)\), and original unit pins \(\tau\).
A domain assigns statuses \(\mathrm U,\mathrm D,\mathrm X\);
\(\mathrm X\) sites are removed. Each nonremoved site has a kept
subset of its incident bonds inside \(G\). A bond is present if both
ends are nonremoved and both keep it. A \(\mathrm D\) site has at
most two present bonds. Protected sites in \(S\) have status
\(\mathrm U\) and keep every incident bond inside \(G\).
Use \(\lambda_{\mathrm U},\lambda_{\mathrm D}\) at the corresponding
sites and define
\[
 Z_D^\tau[f]=\sum_n f(n)
       \prod_{\text{present }\{x,y\}}(1+n_x\cdot n_y)
       \prod_{\substack{(x,z)\in\mathcal L(G)\\x\in S}}
                   (1+\tau_{xz}\cdot n_x)
       \prod_{x:\,\mathrm{st}(x)\ne\mathrm X}\lambda_{\mathrm{st}(x)}(n_x).
\]
The sum is over the product of the supports \(D\) at \(\mathrm U\)
sites and \(D\cup\{0\}\) at \(\mathrm D\) sites.
Define the free sum, normalized expectations and \(\Psi_D\) as before.
The class \(\mathcal D_{\mathrm{cons}}(G)\) consists of domains in
which every \(\mathrm U\) site keeps all its bonds, every \(\mathrm D\)
site keeps exactly two, and every bond between nonremoved sites is
kept by both ends or by neither.
An auxiliary network has the same data but permits protected
\(\mathrm U\) sites to have arbitrary kept subsets. It retains every
original leg factor. Neither domains nor auxiliary networks carry
a scalar trace mass. Only the networks occurring below, with at most
four factors at each site, are used.
\end{definition}
```


### d:trace — Restricted starts, tracing, and the new coefficient


**Owner:** C. **Status:** replaces the trace definition and scalar mass convention in baseline §6.

**Proof source:** OPPORTUNITIES #4/#20; baseline corrected trace definition.

**Dependencies:** d:domain.

**Interface:** internal.


```latex
\begin{definition}\label{d:trace}
A trail uses distinct present unoriented bonds. Its prefixes are
\(w_j=(v_0,\ldots,v_j)\), and \(\mathcal T_D(u,T)\) denotes trails
starting at \(u\) and stopping at their first hit of \(T\).
No trail departs from \(S\).
At departure from \(y=v_{j-1}\), drop \(\{y,v_j\}\) at both ends.
If \(y\) is \(\mathrm U\), change it to \(\mathrm D\), keeping its
other kept bonds. If \(y\) is \(\mathrm D\), remove it.
Call the resulting network \(D[w_j]\), with \(D[w_0]=D\).
Admissible initial starts are unpinned sites outside \(S\) of status
\(\mathrm U\) with at most three present bonds, or status \(\mathrm D\)
with at most one. The same restrictions then hold at every later
departure. Set
\[
 a_D(w)=3^{-N_{\mathrm U}(w)}5^{-N_{\mathrm D}(w)},\qquad
 R_D^\bullet(w)=Z^\bullet_{D[w]}/Z^\bullet_D,
\]
where the counts record the status at departure, not the original status.
Original legs are always unchanged, including at a terminal hit of \(S\).
\end{definition}
```


### l:stepid — The two used step identities


**Owner:** C. **Status:** replaces baseline l:stepid by its used degree range.

**Proof source:** OPPORTUNITIES #2/#4.

**Dependencies:** l:moments.

**Interface:** internal.


```latex
\begin{lemma}\label{l:stepid}
For vectors \(a,u_1,\ldots,u_k\in\mathbb R^3\),
\[
 \mathcal M\!\left((a\cdot n)\prod_{i=1}^k(1+n\cdot u_i)\right)
 =\frac13\sum_{i=1}^k(a\cdot u_i)
       \lambda_{\mathrm D}\!\left(\prod_{i'\ne i}(1+n\cdot u_{i'})\right)
       \quad(0\le k\le3),
\]
and
\[
 \lambda_{\mathrm D}\!\left((a\cdot n)\prod_{i=1}^k(1+n\cdot u_i)\right)
       =\frac15\sum_{i=1}^k a\cdot u_i\quad(0\le k\le1).
\]
An empty sum is zero. The second identity removes the departure site
with no residual scalar mass.
\end{lemma}
```


Writing constraint / short proof sketch: Do not keep the old k=4 U identity when only fourth moments are specified. The initial two-bond D case is outside this new lemma and outside every application.


### p:pairwalk — The pair expansion on its narrowed domain


**Owner:** C. **Status:** kept with edits.

**Proof source:** baseline p:pairwalk; OPPORTUNITIES #2/#4/#20.

**Dependencies:** d:trace, l:stepid, l:finitefacts.

**Interface:** internal.


```latex
\begin{proposition}\label{p:pairwalk}
Let \(D\) be a domain or auxiliary network, and let \(u\) be an
admissible initial start. Let \(v\ne u\) be nonremoved; if it is
\(\mathrm U\), assume at most three incident factors, counting
original legs; if it is \(\mathrm D\), assume at most one present bond.
Put \(T=S\cup\{v\}\). For \(\bullet=\tau,0\),
\[
 \mathbb E_D^\bullet(n_u\cdot n_v)=
 \sum_{w\in\mathcal T_D(u,T)}a_D(w)R_D^\bullet(w)
           \mathbb E_{D[w]}^\bullet(n_{v_{|w|}}\cdot n_v).
\]
If the endpoint is \(v\), its last factor is independent of the
choice of \(\bullet\): it is \(1\) for status \(\mathrm U\),
and \(3/5\) for status \(\mathrm D\).
Every partition product with an inserted observable used in this
identity has separate degree at most four.
\end{proposition}
```


Writing constraint / short proof sketch: Prove the expansion first for unnormalized numerators and divide once. The second expansion’s target is the already defective terminal site e in S, which has lost its arrival bond and therefore has at most three factors. This is why the endpoint restriction is sufficient.


### d:ratios — Ratios after moving revisit mass


**Owner:** C. **Status:** replaces baseline §6 step-ratio formulas.

**Proof source:** OPPORTUNITIES #4; baseline e:IJ.

**Dependencies:** d:trace.

**Interface:** internal.


```latex
\begin{definition}\label{d:ratios}
At a step \(j\), put
\(\rho_j^\bullet=Z^\bullet_{D[w_j]}/Z^\bullet_{D[w_{j-1}]}\).
At a \(\mathrm D\) departure \(\rho_j^\tau=\rho_j^0=1\).
At a \(\mathrm U\) departure from \(y\) to \(o\), let \(E'\)
be the pre-step network with \(y\) removed.
If the other present neighbours are \(f,g\), set
\[
 I=1+\tfrac13(P_{fg}+P_{fo}+P_{go}),\quad
 J=1+\tfrac15P_{fg},\quad P_{ab}=n_a\cdot n_b,\qquad
 (\rho_j^\bullet)^{-1}=\mathbb E_{E'}^\bullet I/
                                      \mathbb E_{E'}^\bullet J.
\]
With only one other neighbour \(f\), use \(I=1+P_{fo}/3,\ J=1\);
with no other neighbour, \(\rho_j^\bullet=1\).
Straight/turning refers to the incoming direction, with a designated
absent incoming bond at the first step.
\end{definition}
```


### l:response — [AMENDED] Uniform response identity and exceptional-step bounds


**Owner:** C. **Status:** retained uniform identity/bounds; type-dependent main-line bounds added separately.

**Proof source:** baseline l:response; OPPORTUNITIES #4.

**Dependencies:** d:ratios, l:35, l:finitefacts.

**Interface:** yes.


```latex
\begin{lemma}\label{l:response}
At a \(\mathrm U\) departure \(y\notin S\), write
\(r_{ab}=\mathbb E^\tau_{E'}P_{ab}-\mathbb E^0_{E'}P_{ab}\).
With three present neighbours,
\[
 \log\rho_j^0-\log\rho_j^\tau
       =\alpha_jr_{fg}+\beta_j(r_{fo}+r_{go}),\qquad
 0<\alpha_j\le\bar\alpha=\frac{18094}{100000},\quad
 0<\beta_j\le\bar\beta=\frac{36751}{100000}.
\]
With two present neighbours the response is \(\beta_j'r_{fo}\),
where \(0<\beta_j'\le35510/100000\le\bar\beta\);
with one it is zero. Also \(\rho_j^0\le1\) and
\(\rho_j^\tau\le12/5\).
A \(\mathrm D\) departure has zero logarithmic response.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: The statement remains valid. Its uniform bar-alpha and bar-beta remain convenient summability majorants, and 12/5 still controls exceptional departures in the boundary-hit term. The main closed-trail recursion now uses l:response-typed, not these uniform response coefficients.

### l:exposure — Exposure for the new ratio convention


**Owner:** C. **Status:** kept with edits.

**Proof source:** baseline l:exposure; OPPORTUNITIES #4.

**Dependencies:** d:trace, l:response.

**Interface:** internal.


```latex
\begin{lemma}\label{l:exposure}
For an admissibly started stopped trail, let \(\Phi\) be its
\(\mathrm U\) departures, and suppose \(\rho_j^\tau\le x_j\),
\(x_j\ge1\), for \(j\in\Phi\).
For every ordering \(\sigma\) of \(\Phi\),
\[
 |R_D^\tau(w)-R_D^0(w)|
 \le\sum_{k=1}^{|\Phi|}
       |\log\rho_{\sigma(k)}^0-\log\rho_{\sigma(k)}^\tau|
                         \prod_{l\le k}x_{\sigma(l)}.
\]
Multiplication by \(a_D(w)\) gives the corresponding bound on the
coefficient in the pair expansion.
\end{lemma}
```


Writing constraint / short proof sketch: There is no extra (3/5) factor in this formula: it is already in a_D(w). Every D departure has ratio one for both pin choices.


### d:pattern — The corrected covered pattern class


**Owner:** C. **Status:** kept with edits (finite functional, no infimum).

**Proof source:** baseline d:pattern, including every covered-tip and slot correction; OPPORTUNITIES #20.

**Dependencies:** d:domain.

**Interface:** yes.


```latex
\begin{definition}\label{d:pattern}
Let \(\mathsf T=\{z:d(z,0)\le2\}\), with passage site \(0\),
arrival site \(\mathsf s=(0,-1)\), other neighbours
\(\mathsf e=(1,0),\mathsf N=(0,1),\mathsf W=(-1,0)\),
four corners \((\pm1,\pm1)\), and tips \((\pm2,0),(0,\pm2)\).
The external slots are the two external bonds at each corner and
the three at each tip, twenty in total.
A pattern chooses an out-neighbour \(o\in\{\mathsf e,\mathsf N,\mathsf W\}\)
and statuses/kept sets with the following rules.
The passage site is \(\mathrm U\) and keeps precisely its three
non-arrival bonds. The arrival site is removed or is \(\mathrm D\)
keeping two of its three non-passage bonds.
Each other neighbour is \(\mathrm U,\mathrm X\), or \(\mathrm D\)
keeping its passage bond and one other bond; \(o\) is not removed.
Each corner is \(\mathrm U,\mathrm X\), or \(\mathrm D\) keeping
two of its four bonds. Every \(\mathrm U\) site other than the
passage site keeps all four bonds.
Between nonremoved non-tip sites, a bond is kept by both ends or
by neither. Tips are covering \(\mathrm U\) sites; their bond to
a neighbour \(z\) is present exactly when \(z\) is nonremoved and
keeps that bond. No consistency condition with a global tip kept
set is imposed.
For \(m\in(\mathbb S^2)^{20}\), include every external slot factor
at every nonremoved corner and tip, including both corner slots
when the corresponding actual external bonds are missing.
Let \(Z_{\rm cur}(\pi;m)\) be the finite product functional of
all present template bonds and these slots, using the status laws.
Let \(Z_{\rm next}(\pi;m)\) change the passage law to
\(\lambda_{\mathrm D}\) and drop its out-bond.
The resulting class is \(\mathcal P_{\rm ext}\); it is straight
when \(o=\mathsf N\), and turning otherwise.
\end{definition}
```


Writing constraint / short proof sketch: These are covered local integrals, not protected-boundary domains. Missing actual external factors are filled by convex averaging. Do not reinstate the older uncorrrected pattern class.


### h:H1 — [AMENDED] The precise local computational contract


**Owner:** C. **Status:** kept with edits (inequalities rather than optimization).

**Proof source:** baseline pointwise H1; OPPORTUNITIES #20/#21; COMPFEAS H1 certificate recommendation.

**Dependencies:** d:pattern.

**Interface:** yes.


```latex
\begin{definition}[(H1)]\label{h:H1}
For \(c_{\mathrm s},c_{\mathrm t}\in(0,1]\), (H1) means that
for every \(\pi\in\mathcal P_{\rm ext}\) and every
\(m\in(\mathbb S^2)^{20}\),
\[
 Z_{\rm cur}(\pi;m)\ge c_{\rm type(\pi)}Z_{\rm next}(\pi;m).
\]
In the paper the fixed thresholds are
\(c_{\mathrm s}=961/1000\), \(c_{\mathrm t}=187/200\).
No minimum, minimizing pins, or optimal inversion is asserted.
\end{definition}
```


[AMENDED] Writing constraint / short proof sketch: The unit-vector quantifier and two rational thresholds are unchanged. The primary Appendix D proof now accepts division-free Gram/residual witnesses for the reconstructed exchange-sector matrices; Bareiss is only a fallback.

### l:local — Local covering implies the step bound


**Owner:** C. **Status:** kept with edits.

**Proof source:** baseline l:local; OPPORTUNITIES #2/#20.

**Dependencies:** l:35, h:H1, d:ratios.

**Interface:** internal.


```latex
\begin{lemma}\label{l:local}
At any \(\mathrm U\) departure outside \(S\) whose normalized
non-tip template data belong to \(\mathcal P_{\rm ext}\), (H1)
implies \(\rho_j^\tau\le1/c_{\rm type}\).
The conclusion is uniform in all original unit pins, all outside
spins of norm at most one, all missing external factors, and all
actual tip statuses and kept sets allowed by the ordinary-domain rules.
\end{lemma}
```


Writing constraint / short proof sketch: Ratios of positive averages preserve lower bounds; fill missing slots by averaging opposite unit pins and use l:35 to replace any tip field by a covering U tip. Use polynomial covariance of the mean, not invariance of the finite law.


### d:weights — The unchanged dominating lattice weights


**Owner:** C. **Status:** kept as is.

**Proof source:** baseline s:H2def; OPPORTUNITIES #4/#20.

**Dependencies:** h:H1.

**Interface:** yes.


```latex
\begin{definition}\label{d:weights}
Put \(x_{\mathrm s}=1/c_{\mathrm s}\), \(x_{\mathrm t}=1/c_{\mathrm t}\).
A lattice trail \(w=(v_0,\ldots,v_n)\) has distinct unoriented
nearest-neighbour bonds. Give it a designated unit incoming direction
\(a\), and forbid \(v_1-v_0=-a\) when \(n\ge1\); the virtual
incoming bond is not itself a used bond of the trail.
For departure \(i\), \(0\le i<n\), give weight \(1/5\) if \(v_i\)
has been departed from earlier, and otherwise weight \(x_{\mathrm s}/3\)
for continuing in the incoming direction and \(x_{\mathrm t}/3\)
for a turn. Let \(\mathsf W(w)\) be the product, with
\(\mathsf W(\varnothing)=1\).
\end{definition}
```


### h:H2 — [AMENDED] The open-trail computational contract


**Owner:** C. **Status:** kept with edits (explicit positive rate).

**Proof source:** baseline h:H2; COMPFEAS memory-6 one-step true-revisit test.

**Dependencies:** d:weights.

**Interface:** yes.


```latex
\begin{definition}[(H2)]\label{h:H2}
For \(C_V\ge1\) and \(0<q<1\), (H2) means that for every
integer \(n\ge0\), every start and every designated incoming direction,
\[
 \sum_{\substack{|w|=n\\\text{initial reversal forbidden}}}
                      \mathsf W(w)\le C_Vq^n .
\]
The sum is over plane lattice trails with those specified initial data.
\end{definition}
```


[AMENDED] Writing constraint / short proof sketch: The all-length interface already needs only C_V>=1 and 0<q<1, so its formula is unchanged. The adopted test supplies q=1119948287353/1120437614225<2499/2500 and C_V=10 by p:H2-test and l:H2-CV; see the explicit base-sum derivation below.

### l:onepoint — A common majorant for both pin choices


**Owner:** C. **Status:** kept with edits (mass-free coefficient and restricted D start).

**Proof source:** baseline l:onepoint with its corrected maximum; OPPORTUNITIES #4/#20.

**Dependencies:** h:H1, h:H2, l:local, l:response, d:trace.

**Interface:** internal.


```latex
\begin{lemma}\label{l:onepoint}
Assume (H1) and (H2). Start a trace at an admissible \(x\notin S\)
with incoming direction \(a\) such that \(\{x-a,x\}\) is absent.
Suppose each stopped trail from \(x\) to \(S\) has at most twelve
\(\mathrm U\) departures whose templates are not covered patterns.
Then
\[
 \sum_{w\in\mathcal T_D(x,S)}a_D(w)
                  \max\{R_D^\tau(w),R_D^0(w)\}
 \le (12/5)^{12}\frac{C_V}{1-q}\,q^{d(x,S)}.
\]
Pointwise the summand is at most \((12/5)^{12}\mathsf W(w)\).
\end{lemma}
```


Writing constraint / short proof sketch: An initially D site with two present bonds is excluded. For an initially D site treated as a lattice first visit, 1/5 <= x_type/3 supplies domination. Prove the pointwise bound for the maximum before summing; separate sums do not imply this statement.


## 7. Pair closure, a positive-vector witness, and renewal


### d:pairenv — The two response envelopes


**Owner:** C. **Status:** kept as is.

**Proof source:** baseline s:pairclass/e:FX; OPPORTUNITIES #20.

**Dependencies:** d:domain.

**Interface:** internal.


```latex
\begin{definition}\label{d:pairenv}
For \(D\in\mathcal D_{\rm cons}(G)\), let \(P_B(D)\) and \(P_C(D)\)
be the ordered nonremoved pairs \((u,v)\) at distance two,
collinear or diagonal respectively, with a designated common neighbour
\(c\) of status \(\mathrm X\). Each endpoint is \(\mathrm U\),
or \(\mathrm D\) with at most one present bond.
For integer \(d\ge0\), let \(F_X(d)\) be the supremum of
\[
 \left|\mathbb E_D^\tau(n_u\cdot n_v)
                    -\mathbb E_D^0(n_u\cdot n_v)\right|
\]
over every finite \(G\), every original unit-pin assignment,
every \(D\in\mathcal D_{\rm cons}(G)\), and every pair in \(P_X(D)\)
with \(\min\{d(u,S(G)),d(v,S(G))\}\ge d\).
Use supremum zero for an empty class, and set \(F_X(d)=F_X(0)\)
for negative integers. Thus \(0\le F_X\le2\), and \(F_X\)
is nonincreasing.
\end{definition}
```


### l:closure — The corrected closure invariant


**Owner:** C. **Status:** kept with edits (no mass-reset language).

**Proof source:** baseline l:closure; OPPORTUNITIES #4/#20.

**Dependencies:** d:pairenv, d:trace, d:pattern.

**Interface:** internal.


```latex
\begin{lemma}\label{l:closure}
Let \(D\in\mathcal D_{\rm cons}(G)\), \((u,v)\in P_X(D)\) have
centre \(c\), and \(u\notin S\). Before tracing, if \(u\) is
\(\mathrm U\), drop its kept bond to the removed \(c\); this changes
no partition function. Trace any trail from \(u\) without visiting
\(S\) before its last site; it need not avoid \(v\).
After every prefix ending at the live endpoint \(y\):
all departed sites are \(\mathrm D\) or \(\mathrm X\);
consistency between nonremoved sites holds; all nonlive
\(\mathrm U\) sites have full kept sets and all nonlive \(\mathrm D\)
sites have exactly two kept bonds.
After a positive-length prefix a live \(\mathrm U\) site has lost
only its arrival bond, and a live \(\mathrm D\) site keeps one bond;
the arrival site's other endpoint is \(\mathrm D\) or \(\mathrm X\).
At length zero a live \(\mathrm U\) site has its three non-\(c\)
kept bonds, while a live \(\mathrm D\) site retains its two kept
bonds but has at most one present bond.
Whenever \(y\notin S\), removing \(y\) yields an ordinary member
of \(\mathcal D_{\rm cons}(G)\). Every \(\mathrm U\) departure
before stopping has a covered pattern, and its nonremoved neighbour
pairs belong to \(P_B\) or \(P_C\) of that ordinary domain.
If the endpoint is \(e\in S\), it is \(\mathrm U\) with just its
arrival bond lost. This is the sole kept-set defect in the terminal
auxiliary network; all original legs remain. No removal of \(e\)
or ordinary-domain membership after removing \(e\) is asserted.
\end{lemma}
```


### l:terminalcover — The second expansion and its twelve exceptions


**Owner:** C. **Status:** new explicit statement of the corrected T2 argument.

**Proof source:** baseline t:rec, term T2; corrected unlabelled remark after l:local.

**Dependencies:** l:closure, l:local, l:onepoint.

**Interface:** internal.


```latex
\begin{lemma}\label{l:terminalcover}
In the first expansion of a pair of Definition~\ref{d:pairenv},
suppose the trail avoids its target \(v\) and stops at \(e\in S\).
In the terminal auxiliary network, start a second expansion from \(v\)
to \(S\), again dropping its kept bond to \(c\) if it is \(\mathrm U\).
The starts of both expansions have their designated incoming bond
absent and are admissible in Definition~\ref{d:trace}.
Before the second trail hits \(S\), a \(\mathrm U\) departure
outside \(\{y':0<d(y',e)\le2\}\) has a covered pattern.
There are at most twelve exceptional \(\mathrm U\) departures
on each second trail. Both expansions satisfy Lemma~\ref{l:onepoint}.
\end{lemma}
```


Writing constraint / short proof sketch: The twelve exceptions may occur anywhere along the second trail. They are not asserted to be its final twelve steps. No response supremum is taken over auxiliary terminal networks.


### l:log-mean-bounds — [AMENDED] Analytic and rational logarithmic-mean bounds


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS report.md (read in full), coefficient-refinement and stationary-certificate sections; experiments/coeff_bounds.py.

**Dependencies:** definitions and finite elementary algebra only.

**Interface:** yes.


```latex
\begin{lemma}\label{l:log-mean-bounds}
Let \(\mathcal L(x,y)=(x-y)/(\log x-\log y)\) for \(x\ne y\)
and \(\mathcal L(x,x)=x\), for positive \(x,y\).
Put \(f(s)=1/\mathcal L(s,1)\), so \(f(1)=1\).
For \(3/5\le c\le1\), the function
\[
 G_c(x,y)=\frac1{3\mathcal L(cx,y)}-\frac1{5\mathcal L(x,y)}
\]
is nonincreasing in each positive variable. In particular,
for \(x\ge a=116/125\), \(y\ge1\),
\[
 G_c(x,y)\le f(ac)/3-f(a)/5.
\]
For rational \(0<s<1\), put \(t=(1-s)/(1+s)\) and
\[
 f_-(s)=\frac2{1-s}\sum_{k=0}^{7}\frac{t^{2k+1}}{2k+1},
 \qquad
 f_+(s)=f_-(s)+\frac{2t^{17}}{17(1-t^2)(1-s)}.
\]
Then \(f_-(s)\le f(s)\le f_+(s)\).
For the two rows of the following table, all numbers are exact rationals:
\[
 \begin{array}{c|c|ccc}
 \tau&c_\tau&a_\tau&b_\tau&b'_\tau\\ \hline
 {\rm s}&961/1000&145217/10^6&352782/10^6&340008/10^6\\
 {\rm t}&187/200&150000/10^6&357549/10^6&344661/10^6
 \end{array}
\]
They satisfy
\[
 \frac{f_+(ac_\tau)}3-\frac{f_-(a)}5\le a_\tau,\qquad
 \frac{f_+(ac_\tau)}3\le b_\tau,\qquad
 \frac{f_+(c_\tau)}3\le b'_\tau,\qquad
 0<b'_\tau\le b_\tau .
\]
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: Prove monotonicity using the reciprocal-logarithmic-mean integral and 5c>=3; prove the eight-term enclosure with its displayed remainder. These small rational endpoint checks are proof obligations, not imported decimal logarithms. This argument does not prove the old turn-alpha value 0.149953.


### l:response-typed — [AMENDED] The type-dependent main-line response bound


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS report.md (read in full), coefficient-refinement and stationary-certificate sections; baseline l:response and r:typedep (with corrected turn alpha).

**Dependencies:** l:response, l:log-mean-bounds, h:H1, l:local.

**Interface:** yes.


```latex
\begin{lemma}\label{l:response-typed}
Fix \(c_{\rm s}=961/1000\), \(c_{\rm t}=187/200\) and assume (H1).
At a covered \(\mathrm U\) departure of type \(\tau\in\{{\rm s},{\rm t}\}\),
the response coefficients in Lemma~\ref{l:response} satisfy
\[
 0<\alpha_j\le a_\tau,\qquad 0<\beta_j\le b_\tau
       \quad\hbox{with three present neighbours},\qquad
 0<\beta'_j\le b'_\tau\quad\hbox{with two}.
\]
Here the exact constants are those of Lemma~\ref{l:log-mean-bounds};
in particular \(a_{\rm t}=150000/10^6\).
With \(a=116/125\), their analytic bounds are
\[
 \beta_j\le f(ac_\tau)/3,\qquad
 \beta'_j\le f(c_\tau)/3,\qquad
 \alpha_j\le f(ac_\tau)/3-f(a)/5.
\]
These follow using \(I^\tau\ge c_\tau J^\tau\),
\(I^0\ge J^0\ge1\), and \(J^\tau\ge a\).
Also \(a_\tau\le18094/100000\) and
\(b_\tau,b'_\tau\le36751/100000\).
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: Use the local H1 ratio bound in the ordinary domain of each response. The two-neighbour bound is essential when one of the two non-outgoing neighbours is known removed. The uniform response identity, zero D response and exceptional-step 12/5 bound are retained.

### d:kernel — [AMENDED] The type-dependent closed-trail shift kernel


**Owner:** C. **Status:** replaces the former fixed-coefficient kernel; trail weights, shifts and dead-site rules retained.

**Proof source:** COMPFEAS report.md (read in full), coefficient-refinement and stationary-certificate sections; baseline e:kernel and r:typedep, with new rigorous bounds.

**Dependencies:** d:weights, l:response-typed.

**Interface:** yes.


```latex
\begin{definition}\label{d:kernel}
For \(X=B,C\), fix \(c=0\), \(u=(-1,0)\), and \(v=(1,0)\)
for \(B\), \(v=(0,1)\) for \(C\).
Let \(\mathcal T_n^X\) be the length-\(n\) plane trails avoiding \(c\),
from \(u\) to their first hit of \(v\), with incoming direction \(u-c\).
A departure is a lattice revisit when its site was departed from earlier.
At a lattice first visit \(i\), put \(x_i=x_{\tau_i}\) according to
its straight/turn type. Of the three neighbours other than the arrival
site, write \(o\) for the outgoing neighbour and \(f,g\) for the others.
A neighbour is dead if it is \(c\) or was departed from twice before \(i\).
The outgoing neighbour of a true trail is not dead.
If \(f,g\) are both live, assign coefficient \(a_{\tau_i}\) to
\(\{f,g\}\), and \(b_{\tau_i}\) to each of \(\{f,o\},\{g,o\}\).
If exactly one of \(f,g\) is live, assign \(b'_{\tau_i}\) to its
pair with \(o\); if neither is live there is no response pair.
The constants are those of Lemma~\ref{l:log-mean-bounds}.
A live pair \(p\) has type \(Y=B,C\) and shift
\[
 s(p)=\max_{z\in p}\min\{d(z,u),d(z,v)\}.
\]
Let \(\kappa_{Y,s}(i)\) sum its assigned coefficients.
For any fixed, \(\theta\)-independent orderings \(\sigma_w\) of lattice
first visits, define
\[
 \begin{split}
 M_{XY,s}
 &=\sum_{n\ge1}\sum_{w\in\mathcal T_n^X}
     3^{-n}(3/5)^{\operatorname{rev}(w)}
     \sum_k\kappa_{Y,s}(\sigma_w(k))
                   \prod_{l\le k}x_{\sigma_w(l)},\\
 M_\theta[X,Y]&=\sum_{s\ge0}M_{XY,s}\theta^{-s}.
 \end{split}
\]
These are nonnegative series. The identity
\(3^{-n}(3/5)^r=3^{-(n-r)}5^{-r}\) retains the mass-free
trace coefficients. This \(M\) is the modified type-dependent kernel,
not the original uniform-coefficient matrix.
\end{definition}
```


[AMENDED] Writing constraint / short proof sketch: Keep the actual dead-site rule and shifts. Use beta-prime when exactly one non-outgoing neighbour survives. Forgetting a dead neighbour is an upper relaxation because b-prime<=b and the added coefficients are nonnegative. Initially D sites still have zero response and are dominated by lattice first visits.

### d:kernel-order — [AMENDED] The fixed short-prefix ordering and rational witness


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS report.md (read in full), coefficient-refinement and stationary-certificate sections; experiments/exact_stationary_prefix.py.

**Dependencies:** d:kernel.

**Interface:** yes.


```latex
\begin{definition}\label{d:kernel-order}
Fix
\[
 h=(1,h_C),\quad h_C=\frac{5404319552844595}{4503599627370496},
 \qquad \rho_0=\frac{993015}{10^6},\qquad L=12 .
\]
For a first visit set \(\kappa_h(i)=\sum_{Y,s}\kappa_{Y,s}(i)h_Y\).
For a closed trail of length \(n\le L\), let \(\sigma_w\) order its
first visits by increasing
\((x_i-1)/(x_i\kappa_h(i))\), with value \(+\infty\) when
\(\kappa_h(i)=0\), breaking ties by increasing path index.
For \(n>L\), list straight first visits in path order and then
turning first visits in path order.
Hereafter \(M_{XY,s}\) and \(M_\theta\) use exactly these orderings.
They do not depend on \(\theta\).
\end{definition}
```


[AMENDED] Writing constraint / short proof sketch: h_C is the exact dyadic value entered as 1.20, not the rational 6/5. Both rows use memory 10, prefix 12 and radius 70. Do not substitute the report’s memory-9 route or the old short cutoff 20.

### h:H3 — [AMENDED] The positive-vector contract for the modified kernel


**Owner:** C. **Status:** replaces the former fixed-coefficient H3_h premise by the type-dependent stationary route.

**Proof source:** COMPFEAS report.md (read in full), coefficient-refinement and stationary-certificate sections.

**Dependencies:** d:kernel, d:kernel-order.

**Interface:** yes.


```latex
\begin{definition}[(H3\(_h\))]\label{h:H3}
For the type-dependent kernel and fixed orderings of
Definitions~\ref{d:kernel}--\ref{d:kernel-order}, (H3\(_h\)) is the
following mathematical assertion, with the specified \(h,\rho_0\):
for \(X=B,C\) and every integer \(R_0\ge0\),
\[
 \sum_{n=1}^{R_0}\sum_{w\in\mathcal T_n^X}
 3^{-n}(3/5)^{\operatorname{rev}(w)}
 \sum_k\kappa_h(\sigma_w(k))\prod_{l\le k}x_{\sigma_w(l)}
       \le\rho_0h_X .
\]
Equivalently, the full nonnegative sums satisfy \(M_1h\le\rho_0h\).
No bound for the former uniform-coefficient matrix is part of this
contract. Its proof in this revision uses the stationary lattice
Bellman certificates, with no periodic spatial walk or remainder.
\end{definition}
```


[AMENDED] Writing constraint / short proof sketch: The semantic input remains an all-length row inequality. The stationary finite checks prove it; a numerical spectral radius or a finite prefix alone does not. The new certified target is 0.993015, not the old 0.98779.

### l:Mtheta — [AMENDED] Transport the same witness to a shifted kernel


**Owner:** C. **Status:** retained analytic argument for the modified kernel and new witness.

**Proof source:** baseline shift estimate; OPPORTUNITIES #9; COMPFEAS weaker-H2 discussion.

**Dependencies:** h:H2, h:H3, d:kernel.

**Interface:** yes.


```latex
\begin{lemma}\label{l:Mtheta}
Assume (H2) and (H3\(_h\)) for the type-dependent kernel.
For every \(q^2<\theta\le1\), all entries of \(M_\theta\) are
finite. There exist \(q^2<\theta<1\) and \(\rho_0<\rho<1\)
such that the same vector \(h\) satisfies \(M_\theta h\le\rho h\).
Every shift of a length-\(n\) trail is at most \(n/2+1\), and
each matrix entry is bounded by
\[
 \sum_{n\ge1} n(\bar\alpha+2\bar\beta)
                      C_V q^n\theta^{-n/2-1}.
\]
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: Only 0<q<1 and finite C_V are used. The old uniform bar-alpha=18094/100000 and bar-beta=36751/100000 remain valid crude majorants by l:response-typed, so the displayed summability bound is unchanged. With q=1119948287353/1120437614225 and C_V=10, choose theta sufficiently close to one in (q^2,1); transport the same fixed h and orderings. No spectral-radius argument is needed.

### l:recineq — [AMENDED] The type-dependent response recursion with the retained source constant


**Owner:** C. **Status:** replaces the fixed-coefficient recursion by the type-dependent kernel.

**Proof source:** baseline e:recineq and corrected T1/T2 proof; COMPFEAS coefficient refinement.

**Dependencies:** l:closure, l:terminalcover, l:exposure, l:response-typed, l:onepoint, d:kernel, d:kernel-order, d:pairenv.

**Interface:** internal.


```latex
\begin{lemma}\label{l:recineq}
Fix the two H1 thresholds above. Assume (H1) and (H2), use
the bounds of Lemma~\ref{l:response-typed}, and use the
type-dependent kernel with the fixed orderings of
Definition~\ref{d:kernel-order}.
For \(X=B,C\) and every integer \(d\ge1\),
\[
 F_X(d)\le\sum_{Y=B,C}\sum_{s\ge0}M_{XY,s}F_Y(d-s)+C_Tq^{2d},
 \qquad
 C_T=2(12/5)^{24}\left(\frac{C_V}{1-q}\right)^2 .
\]
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: In T1 use a_type,b_type with three live neighbours and b-prime_type with two; prove the comparison under additional removals using b-prime_type<=b_type. The T2 two-walk argument is unchanged, hence C_T=2(12/5)^24(C_V/(1-q))^2 remains valid for the weaker q. Do not infer contraction of the original larger matrix.

### l:renewal — Bounded nonnegative renewal


**Owner:** C. **Status:** replaces the truncated-supremum/fixed-point end of baseline t:rec.

**Proof source:** OPPORTUNITIES #9.

**Dependencies:** definitions and finite elementary algebra only.

**Interface:** internal.


```latex
\begin{lemma}\label{l:renewal}
Let \(m_{XY,s}\ge0\), \(h_X>0\), \(0<q^2<\theta<1\),
\(0<\rho<1\), and
\(\sum_{Y,s}m_{XY,s}h_Y\theta^{-s}\le\rho h_X\).
Suppose \(0\le F_X(d)\le2\) on \(\mathbb Z\), with
\(F_X(d)=F_X(0)\) for \(d<0\), and, for integers \(d\ge1\),
\[
 F_X(d)\le\sum_{Y,s}m_{XY,s}F_Y(d-s)+C_Tq^{2d},
 \qquad C_T\ge0.
\]
Writing \(H=\max_Xh_X/\min_Xh_X\), one has, for \(d\ge0\),
\[
 F_X(d)\le A\theta^d,\qquad
 A=\frac{H\max\{2,C_T\}}{1-\rho}\ge2 .
\]
\end{lemma}
```


Writing constraint / short proof sketch: Extend the source as 2 on nonpositive integers, iterate a finite number of times, bound the remainder by 2 h_X rho^k/min h, and sum the geometric source bound. No fixed-point theorem is an input.


### t:rec — [AMENDED] The export of (P) from the type-dependent contracts


**Owner:** C. **Status:** modified recursion theorem for the adopted computational route.

**Proof source:** baseline t:rec; OPPORTUNITIES #9/#20; COMPFEAS coefficient refinement.

**Dependencies:** l:recineq, l:Mtheta, l:renewal, d:pairenv, h:P.

**Interface:** yes.


```latex
\begin{theorem}\label{t:rec}
Fix \((c_{\rm s},c_{\rm t})=(961/1000,187/200)\).
Assume (H1), (H2) with any \(C_V\ge1\), \(0<q<1\), and
(H3\(_h\)) for the type-dependent kernel and fixed orderings above.
Then there exist \(A\ge2\) and \(0<\theta<1\) such that
\(\mathsf P(A,\theta)\) holds.
One may take the \(\theta,\rho,h\) supplied by the shifted-witness
lemma and
\[
 A=\frac{\max h}{\min h}\,
       \frac{\max\{2,\,2(12/5)^{24}(C_V/(1-q))^2\}}{1-\rho}.
\]
\end{theorem}
```


[AMENDED] Writing constraint / short proof sketch: The ordinary-domain closure and final U/X specialization are unchanged. Every step downstream uses only finite C_V and some q<1: Mtheta gives theta in (q^2,1), the same C_T is finite, and l:renewal gives the displayed finite A. No old rate bound 0.98075 or old C_V=153 is required.

## 8. Exact statements of the computational inputs


### t:H1 — [AMENDED] The operator-only local input theorem


**Owner:** C. **Status:** operator-only theorem with Gram/residual positivity certificates.

**Proof source:** baseline operator-only family; COMPFEAS H1 exact reconstruction and Gram/residual checks.

**Dependencies:** p:certificate, l:integercheck, l:gram-residual, h:H1.

**Interface:** yes.


```latex
\begin{theorem}\label{t:H1}
For every \(\pi\in\mathcal P_{\rm ext}\) and every
\(m\in(\mathbb S^2)^{20}\),
\[
 Z_{\rm cur}(\pi;m)\ge
 \begin{cases}
 (961/1000)Z_{\rm next}(\pi;m),&\pi\text{ straight},\\
 (187/200)Z_{\rm next}(\pi;m),&\pi\text{ turning}.
 \end{cases}
\]
\end{theorem}
```


[AMENDED] Writing constraint / short proof sketch: Keep the theorem’s pointwise statement unchanged. Reconstruct each matrix from the corrected pattern, chosen representation/inversion and moment contractions, then check its Gram/residual witness. The study exactly checked all 12,173 exchange-sector blocks outside Lean: 8,439 accept L=0 (direct strict diagonal dominance), 3,734 use nonzero factors. Full factor export/reconstruction and a kernel proof remain obligations; only representative factors were retained by the study.

### t:inputs — [AMENDED] The exact numerical theorem for the adopted three certificate routes


**Owner:** C (theorem text and proof account); separate certificate owner supplies H2/H3 witnesses. **Status:** replaces the earlier flexible-witness statement by the selected COMPFEAS route.

**Proof source:** COMPFEAS report.md; H1 Gram/residual study; H2 exact memory-6 test; stationary m=10,L=12,R=70 summary.

**Dependencies:** t:H1, p:H2-test, l:H2-CV, p:automaton10, p:stationary-check, l:stationary-assembly, h:H3.

**Interface:** yes.


```latex
\begin{theorem}\label{t:inputs}
At \(c_{\rm s}=961/1000\), \(c_{\rm t}=187/200\), (H1) holds
by the operator-only Gram/residual certificates of Appendix D.
Property (H2) holds with
\[
 q=\frac{1119948287353}{1120437614225}<\frac{2499}{2500}<1,
 \qquad C_V=10 .
\]
For the type-dependent coefficients of Lemma~\ref{l:log-mean-bounds},
the orderings and vector \(h\) of Definition~\ref{d:kernel-order},
and \(\rho_0=993015/10^6\), property (H3\(_h\)) holds.
The latter assertion is supplied by five stationary lattice Bellman
certificates with memory \(m=10\), exact prefix \(L=12\ge m+2\),
radius \(R=70\), value scale \(2^{16}\), and coefficient scale
\(2^{48}\), using the checked 3741-state automaton quotient.
\end{theorem}
```


[AMENDED] Writing constraint / short proof sketch: These are targets for proofs in the revised paper, not claims of completed Lean checks. The exact checks in the study establish native feasibility. The numerical theorem now concerns the modified kernel and the weaker H2 rate; no original uniform-kernel spectral-radius claim or periodic remainder is imported.

## Appendix A. Finite probability and operator tools


### l:CE — Finite conditional expectations


**Owner:** A. **Status:** new explicit consolidation.

**Proof source:** MOSPROOF lem:CE; baseline e:lambdaHB.

**Dependencies:** definitions and finite elementary algebra only.

**Interface:** internal.


```latex
\begin{lemma}\label{l:CE}
For a positive probability \(\mu\) on a finite product
\(\Omega=\prod_{x\in V}S_x\), with nonempty finite alphabets,
\(E_U\) is a self-adjoint orthogonal projection preserving constants
and \(\mu\). For real or complex \(f\),
\[
 \langle f,(I-E_U)f\rangle_\mu
   =\mu(\operatorname{Var}_U f)=\|f-E_Uf\|_\mu^2,\qquad
 \operatorname{Var}_\mu f=\mu(\operatorname{Var}_U f)
                          +\operatorname{Var}_\mu(E_Uf).
\]
A finite sum \(\sum_a(I-E_{B_a})\), allowing repeated blocks,
has quadratic form \(\sum_a\mu(\operatorname{Var}_{B_a}f)\).
\end{lemma}
```


### l:finitecoupling — Couplings, overlap, and Hamming distance


**Owner:** A. **Status:** new explicit consolidation.

**Proof source:** MOSPROOF lem:coupling; OPPORTUNITIES #10.

**Dependencies:** definitions and finite elementary algebra only.

**Interface:** internal.


```latex
\begin{lemma}\label{l:finitecoupling}
For probabilities \(p,p'\) on a finite set,
\[
 d_{\rm TV}(p,p')=\tfrac12\sum_z|p(z)-p'(z)|
          =1-\sum_z\min\{p(z),p'(z)\}.
\]
There exists a coupling with disagreement probability equal to this
quantity; every coupling has at least that disagreement probability.
Marginalization cannot increase total variation.
For laws on configurations in a finite \(V\), a marginal coupling
on \(Q\subset V\) can be completed to a coupling of the full laws.
If its disagreement probability on \(Q\) is at most \(\varepsilon\),
the completion can have expected Hamming cost at most
\(|V\setminus Q|+|V|\varepsilon\).
If both laws dominate \(p_0\nu\) for a common probability \(\nu\)
and \(0\le p_0\le1\), their total variation is at most \(1-p_0\).
\end{lemma}
```


### l:surgery — Preservation under pair-dependent surgery


**Owner:** A. **Status:** new explicit consolidation.

**Proof source:** MOSPROOF lem:surgery; corrected baseline p:surgery.

**Dependencies:** l:CE.

**Interface:** internal.


```latex
\begin{lemma}\label{l:surgery}
Let \(\nu\) couple two positive finite-volume specification laws.
Fix a set \(F\) in the volume. For every input pair, resample \(F\)
from any coupling whose first and second marginals are the two
respective conditional laws given their own complements, and keep
the complements fixed. The resulting law still couples the original
two laws. The chosen coupling may depend on the entire input pair.
A finite composition of such kernels has the same property.
\end{lemma}
```


### l:density — Density comparison with a product law


**Owner:** A. **Status:** new; replaces four-site minimum/path constants.

**Proof source:** OPPORTUNITIES #7, adapted to the three new frames.

**Dependencies:** l:CE.

**Interface:** internal.


```latex
\begin{lemma}\label{l:density}
Let \(\pi\) be a positive product probability on a finite product,
and \(d\mu=\varrho\,d\pi\), with \(0<m\le\varrho\le M<\infty\).
Then for every \(f\),
\[
 \mathcal D_\mu(f)\ge m\mathcal D_\pi(f),\qquad
 \operatorname{Var}_\mu f\le M\operatorname{Var}_\pi f,\qquad
 \mathcal D_\pi(f)\ge\operatorname{Var}_\pi f .
\]
Thus \(\lambda(\mu)\ge m/M\).
In a conditional frame block, absorbing site weights and every
fixed boundary factor into \(\pi\) gives
\(\lambda(\mu)\ge r_b^{|E(Q)|}\).
\end{lemma}
```


Writing constraint / short proof sketch: Use the variational formula for each integrated conditional variance; comparing only pointwise conditional densities would introduce an unnecessary second density-ratio loss.


### l:comparison — Block-to-site comparison


**Owner:** A. **Status:** replaces baseline l:compare by the general finite lemma.

**Proof source:** MOSPROOF lem:comparison.

**Dependencies:** l:CE.

**Interface:** internal.


```latex
\begin{lemma}\label{l:comparison}
Let \(\mu>0\) be on a finite product, and let \((B_a)\) be a
nonempty finite labelled family of nonempty blocks.
Suppose the single-site heat bath of every conditional law on each
\(B_a\) has Poincare gap at least \(g>0\), uniformly in its exterior fibre,
and \(\sum_a(I-E_{B_a})\) has Poincare gap at least \(c>0\).
If \(t_{\max}=\max_x\#\{a:x\in B_a\}\), then
\[
 \operatorname{Var}_\mu f\le
             \frac{t_{\max}}{cg}\mathcal D_\mu(f).
\]
Repeated blocks are counted with multiplicity.
\end{lemma}
```


### l:contraction — Finite Hamming contraction gives a block gap


**Owner:** A. **Status:** new.

**Proof source:** MOSPROOF lem:contraction; OPPORTUNITIES #1.

**Dependencies:** l:CE.

**Interface:** internal.


```latex
\begin{lemma}\label{l:contraction}
Let \(P=A^{-1}\sum_aE_{B_a}\), where \(A\ge1\) is the number
of labels. Suppose \(0<c\le A\) and that for every two input
configurations at Hamming distance one, their \(P\)-output laws
have a coupling of expected Hamming distance at most \(1-c/A\).
Then \(\sum_a(I-E_{B_a})=A(I-P)\) has Poincare gap at least \(c\).
This applies to site-dependent finite alphabets and also to a
one-point product space.
\end{lemma}
```


Writing constraint / short proof sketch: Use the Hamming Lipschitz seminorm and a finite self-adjoint eigenbasis. There is no continuous-time Markov process or path-coupling mixing-time theorem to cite.


## Appendix B. The weakened planar topology lemma


### l:boundaryconn — Only star-connectivity of the boundary is needed


**Owner:** B. **Status:** replaces baseline l:boundaryconn.

**Proof source:** baseline topology Steps 1–2; OPPORTUNITIES #3.

**Dependencies:** definitions and finite elementary algebra only.

**Interface:** internal.


```latex
\begin{lemma}\label{l:boundaryconn}
If \(A\subset\mathbb Z^2\) is finite, nonempty and star-connected,
and \(A^c\) is star-connected, then
\(\partial_\infty A=\{z\notin A:\operatorname{dist}_\infty(z,A)=1\}\)
is nonempty and star-connected.
Here star-neighbours differ by \(\ell^\infty\) distance one.
\end{lemma}
```


Writing constraint / short proof sketch: Retain the finite mod-two even-edge/triangle argument. Delete the no-diagonal-only-block hypothesis and the nearest-neighbour conclusion for the raw boundary. Neither of those is required after thickening.


### l:thicken — Nearest-neighbour connected crosses


**Owner:** B. **Status:** new.

**Proof source:** OPPORTUNITIES #3.

**Dependencies:** definitions and finite elementary algebra only.

**Interface:** internal.


```latex
\begin{lemma}\label{l:thicken}
If \(X_0\) is finite, nonempty and star-connected, then
\(X=\{z:d(z,X_0)\le1\}\) is nearest-neighbour connected.
For any finite \(G\) containing \(X\), every \(0<\vartheta<1\)
satisfies
\[
 \sum_{z\in X}\vartheta^{d(z,G^c)}
       \le5\vartheta^{-1}
                      \sum_{x\in X_0}\vartheta^{d(x,G^c)}.
\]
\end{lemma}
```


## Appendix C. [AMENDED] The small H2 test and stationary H3 certificates

[AMENDED] This appendix now contains the selected memory-6 one-step H2 proof and the stationary lattice H3 proof. The old periodic-tail Appendix C lemmas l:CW, l:memdom and l:remainder, its p:tail numerical theorem and r:tailtypedep variant are removed, with the new domination/Bellman/assembly lemmas below as replacements. The preceding REV-PLAN's separate l:kernelcontract is also removed; its nonnegative-series equivalence is retained in h:H3. Lemma l:alm is the H2 growth lemma, retained under its name and specialized to the true revisit weight and extension length one. It is not a periodic-tail lemma.

[AMENDED] No parity improvement is used. The Bellman supersolution bounds all suffix horizons directly; no even-time remainder factor, periodic rule release, spatial quotient, or long-time walk iteration enters this route. Ordinary path parity, if used to omit unreachable prefix coordinates in an implementation, must be justified as part of the exact-prefix enumeration proof; it gives no extra numerical factor here.


### d:memory-automaton — [AMENDED] Raw trail windows with absolute directions


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS exact automaton section; experiments/minimize_windows.py.

**Dependencies:** d:weights.

**Interface:** yes.


```latex
\begin{definition}\label{d:memory-automaton}
Let \(\mathcal E=\{{\rm E}=(1,0),{\rm N}=(0,1),
{\rm W}=(-1,0),{\rm S}=(0,-1)\}\).
For \(m\ge1\), \(\Omega_m\) consists of sequences
\(\omega=(d_1,\ldots,d_m)\in\mathcal E^m\) whose path from zero
uses distinct unoriented bonds. Write \(z_0=0\),
\(z_j=\sum_{i\le j}d_i\), and \(a(\omega)=d_m\).
A direction \(d\) is admissible if \(d\ne-d_m\) and
\(\{z_m,z_m+d\}\) is not a used bond of this window.
Its successor is \(\omega d=(d_2,\ldots,d_m,d)\).
Its kind \(k(\omega,d)\) is \({\rm r}\) if
\(z_m\in\{z_0,\ldots,z_{m-1}\}\), otherwise \({\rm s}\)
if \(d=d_m\), and \({\rm t}\) otherwise.
Direction labels remain absolute lattice directions.
\end{definition}
```


### d:memorygrowth — [AMENDED] The one-step H2 matrix with true revisit weight


**Owner:** C. **Status:** replaces the general extension test by the selected one-step test.

**Proof source:** COMPFEAS small H2 test; baseline l:alm permits revisit 1/5.

**Dependencies:** d:memory-automaton, d:weights.

**Interface:** yes.


```latex
\begin{definition}\label{d:memorygrowth}
On \(\Omega_m\), define the nonnegative one-step matrix
\[
 \mathsf A_m(\omega,\omega')=
 \sum_{\substack{d\ {\rm admissible}\\\omega d=\omega'}}
 \gamma(\omega,d),\qquad
 \gamma(\omega,d)=
 \begin{cases}1/5,&k={\rm r},\\
 x_{\rm s}/3,&k={\rm s},\\x_{\rm t}/3,&k={\rm t}.
 \end{cases}
\]
For a prescribed start and incoming direction with initial reversal
forbidden, let \(A_n(\omega)\) be the true total \(\mathsf W\)-weight
of length-\(n\) trails whose last \(m\) steps form \(\omega\),
for \(n\ge m\), and let \(W_n=\sum_{|w|=n}\mathsf W(w)\).
The adopted finite test is \(m=6\) and extension length \(1\).
\end{definition}
```


[AMENDED] Writing constraint / short proof sketch: The true revisit weight is 1/5, not the former 1/4 relaxation. This is a one-step matrix; no extension-eight enumeration or power iteration belongs in the check.


### l:alm — [AMENDED] The one-step witness implies all-length H2


**Owner:** C. **Status:** specializes Lemma alm to extension length one and true revisit weight.

**Proof source:** baseline l:alm with k=1; COMPFEAS small H2 test.

**Dependencies:** d:memorygrowth.

**Interface:** yes.


```latex
\begin{lemma}\label{l:alm}
For \(n\ge m\),
\[
 A_{n+1}(\omega')\le\sum_\omega A_n(\omega)\mathsf A_m(\omega,\omega').
\]
If \(v_\omega>0\), \(0<q<1\), and \(\mathsf A_mv\le qv\),
then (H2) holds with
\[
 C_V=\max\left\{
      \max_{0\le r<m}W_rq^{-r},\
      \frac{\max v}{\min v}W_mq^{-m}\right\}.
\]
Any larger finite constant is also valid.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: The window retains less history, so true revisits forgotten by it have weight 1/5 <= x_type/3; detected revisits have exactly 1/5. This gives the same domination as the baseline lemma. The small test need not reproduce q=0.98075 or C_V=153.


### l:H2-dihedral — [AMENDED] Soundness of the 115-row dihedral reduction


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS small H2 test; experiments/exact_h2.py.

**Dependencies:** d:memorygrowth.

**Interface:** yes.


```latex
\begin{lemma}\label{l:H2-dihedral}
The dihedral group of the square acts on \(\Omega_m\) by applying
the same lattice symmetry to every direction. This action preserves
admissibility, kind, successor and the weights of \(\mathsf A_m\);
thus \(\mathsf A_m(g\omega,g\omega')=\mathsf A_m(\omega,\omega')\).
For any positive vector constant on these orbits, a row inequality
\((\mathsf A_mv)_\omega\le qv_\omega\) checked at one representative
of every orbit holds on every raw window.
For \(m=6\), \(|\Omega_6|=916\) and there are \(115\) orbits.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: Prove completeness of generated raw windows and of the orbit representatives. The H2 dihedral reduction is separate from the H3 automaton quotient and is not a dihedral reduction of the spatial Bellman problem.


### p:H2-test — [AMENDED] The exact rational memory-6 vector certificate


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS data/h2_exact_m6k1_r5.json and data/h2_fifth_m6k1_vector.txt.

**Dependencies:** d:memorygrowth, l:H2-dihedral.

**Interface:** yes.


```latex
\begin{proposition}\label{p:H2-test}
At the two fixed H1 thresholds there exists a positive integer
vector \(v\) on \(\Omega_6\), constant on dihedral orbits, with
\[
 \frac{\max v}{\min v}=\frac{250000000000}{46594269069}<6,\qquad
 \max_\omega\frac{(\mathsf A_6v)_\omega}{v_\omega}
       =q_*:=\frac{1119948287353}{1120437614225}<\frac{2499}{2500}.
\]
The weights have common denominator \(D_2=2695605\), with
numerators \(935000,961000,539121\) for \({\rm s},{\rm t},{\rm r}\).
For \(q_*=q_{\rm num}/q_{\rm den}\), the required row test is
\[
 q_{\rm den}\sum_{d\ {\rm admissible}}n_{k(\omega,d)}v_{\omega d}
          \le q_{\rm num}D_2v_\omega .
\]
It suffices to check the \(115\) orbit rows after proving
Lemma~\ref{l:H2-dihedral}; checking all \(916\) raw rows is also valid.
\end{proposition}
```


[AMENDED] Writing constraint / short proof sketch: Reconstruct the transitions from the bond-trail definition, rather than trust a stored matrix or orbit list. The report supplies the positive rational/integer witness and exactly checks the displayed maximum outside Lean. Formal proof of the row checks remains a Lane C obligation.


### l:H2-CV — [AMENDED] An explicit C_V for the weaker rate


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** Lemma alm specialized to the COMPFEAS witness; elementary finite prefix bound.

**Dependencies:** l:alm, p:H2-test, d:weights.

**Interface:** yes.


```latex
\begin{lemma}\label{l:H2-CV}
With \(m=6\), \(q=q_*\), and the vector in Proposition~\ref{p:H2-test},
the constant supplied by Lemma~\ref{l:alm} is at most \(10\).
Indeed, uniformly over the prescribed start and incoming direction,
\[
 W_r\le x_{\rm t}^r\quad(0\le r\le6),\qquad
 \max\left\{\max_{r<6}W_rq^{-r},\
                 \frac{\max v}{\min v}W_6q^{-6}\right\}
 \le6\left(\frac{200}{187q}\right)^6<10.
\]
Consequently (H2) holds with the explicit rational constants
\(q=q_*\) and \(C_V=10\).
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: At most three continuations are available and every step weight is at most x_t/3, including the initial nonreversing step. This is a finite base-sum majorant, not a new walk search. The last strict inequality is an exact rational comparison.


### l:automaton-quotient — [AMENDED] Exact quotienting of a labelled memory automaton


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS automaton section; experiments/minimize_windows.py and compress_c.py.

**Dependencies:** d:memory-automaton.

**Interface:** yes.


```latex
\begin{lemma}\label{l:automaton-quotient}
Let \(\pi:\Omega_m\to Q\) be a surjection onto a finite set.
Suppose that windows with the same image have, for each absolute
direction, identical admissibility and kind, and their admissible
successors have the same image. Suppose also that two such windows
have the same final direction whenever their class has an admissible
non-revisit transition.
Then admissibility, kind and successor define a well-defined automaton
on \(Q\). Every phase-and-position transition whose coefficients
depend only on the absolute direction, kind, position, and final
direction on non-revisit edges factors through this automaton.
For every function \(G(\varphi,q,x)\), its pullback by \(\pi\)
intertwines the raw and quotient backward operators. This
intertwining also holds for each finite stopped continuation sum.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: Verify all hypotheses on generated raw windows, including final-direction agreement. Merging distinct arrivals is permitted only in classes having exclusively revisit transitions. Prove aggregation by finite induction, not by trusting a minimization algorithm or a hash.


### p:automaton10 — [AMENDED] The checked memory-10 automaton


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS data/windows_m10_min.txt; exact direct transition checks.

**Dependencies:** l:automaton-quotient.

**Interface:** yes.


```latex
\begin{proposition}\label{p:automaton10}
There are \(60092\) raw windows in \(\Omega_{10}\).
The supplied map to \(Q=\{0,\ldots,3740\}\), with its supplied
representative per class, is surjective and satisfies every
hypothesis of Lemma~\ref{l:automaton-quotient}.
Its admissible labelled edges consist of \(2516\) straight,
\(5032\) turning and \(1872\) revisit edges.
\end{proposition}
```


[AMENDED] Writing constraint / short proof sketch: The theorem is a finite reconstruction/check obligation. No assertion of minimality of the 3741 states is needed. Geometry remains on Z^2, with no spatial quotient.


### d:phaseweights — [AMENDED] The four exact phase weights


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS stationary construction; baseline phase identity with type-dependent rewards.

**Dependencies:** d:kernel, d:kernel-order, d:memory-automaton.

**Interface:** yes.


```latex
\begin{definition}\label{d:phaseweights}
The phases are \({\rm A},{\rm B},{\rm C},{\rm D}\). Their
diagonal transition weights, in kind order \({\rm s},{\rm t},{\rm r}\), are
\[
 \begin{array}{c|ccc}
 {\rm A}&x_{\rm s}/3&x_{\rm t}/3&1/5\\
 {\rm B}&x_{\rm s}/3&1/3&1/5\\
 {\rm C}&x_{\rm s}/3&1/3&1/5\\
 {\rm D}&1/3&1/3&1/5
 \end{array}
\]
At a first visit with reward \(\kappa_h\), additionally allow
\({\rm A}\to{\rm C}\) with weight \(x_{\rm t}\kappa_h/3\) on a turn,
or \({\rm B}\to{\rm D}\) with weight \(x_{\rm s}\kappa_h/3\)
on a straight passage. No other phase change is allowed.
At a revisit there is no phase change.
Start with weight one in each of \({\rm A},{\rm B}\);
the terminal reward is \(g=(0,0,1,1)\).
For a true trail, use its actual revisit kinds and its actual
type-dependent live-pair reward from Definition~\ref{d:kernel}.
\end{definition}
```


### l:phase-expansion — [AMENDED] The phase representation of the long-trail reward


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** baseline phase argument, with COMPFEAS type-dependent reward rule.

**Dependencies:** d:phaseweights, d:kernel.

**Interface:** yes.


```latex
\begin{lemma}\label{l:phase-expansion}
For a true closed trail \(w\) ordered with straight first visits
before turning first visits, its \(h\)-weighted contribution to
\(M_1\) equals the sum over phase histories starting in
\({\rm A}\) or \({\rm B}\) and ending in \({\rm C}\) or \({\rm D}\)
of the products of the weights in Definition~\ref{d:phaseweights}.
Equivalently this sum is
\[
 3^{-|w|}(3/5)^{\operatorname{rev}(w)}
       \sum_k\kappa_h(\sigma_w(k))\prod_{l\le k}x_{\sigma_w(l)}.
\]
Splitting such a phase history at any prefix length gives the
product of its exact prefix weight and its corresponding suffix weight.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: The expression is the modified kernel, including beta-prime when only two neighbours are live. This replaces the old phase identity only in its response rewards, not its diagonal weights.


### d:stationary-walk — [AMENDED] The stationary relaxation on the actual lattice


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS recommended stationary route; check_stationary_integer.c and stationary_weights.h.

**Dependencies:** d:phaseweights, p:automaton10.

**Interface:** yes.


```latex
\begin{definition}\label{d:stationary-walk}
Fix \(X=B,C\), \(d_0\in\{{\rm N},{\rm W},{\rm S}\}\),
the sites \(u,c,v\) of Definition~\ref{d:kernel}, and \(a=u+d_0\).
The state space is
\(\{{\rm A},{\rm B},{\rm C},{\rm D}\}\times Q\times\mathbb Z^2\).
At positions \(c,v\) there are no outgoing transitions.
At any other position \(x\), an admissible automaton direction \(d\)
goes to position \(x+d\) and the quotient successor window.
At \(x=u\) or \(a\), forbid reuse of \(\{u,a\}\) in either
direction and kill every memory-detected revisit departure;
every other allowed departure there has weight \(1/5\),
in the same phase and with no response.
At other positions use the automaton kind and the phase weights.
For a non-revisit response, declare only \(c\) dead among the three
neighbours other than the arrival site, and use the type-dependent
three-neighbour or two-neighbour reward rule of Definition~\ref{d:kernel}.
A transition into \(c\) has zero contribution.
Let \(T_{X,d_0}\) be this nonnegative backward operator, with zero
terminal rows, and \(g(\varphi,q,x)=\mathbf1_{\{x=v\}}g_\varphi\).
The free operator \(\mathsf W\) omits positions and special-site
rules, uses the same quotient automaton and phase weights, and
treats all three response neighbours as live.
\end{definition}
```


[AMENDED] Writing constraint / short proof sketch: All known-site and initial-bond rules remain active forever; there is no rule-release time. Only memory is quotiented. Killing the centre via value zero is equivalent to deleting transitions into it.


### l:stationary-domination — [AMENDED] Domination of every true continuation


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS stationary relaxation discussion; to be written from the trail definitions.

**Dependencies:** d:stationary-walk, l:phase-expansion, l:automaton-quotient.

**Interface:** yes.


```latex
\begin{lemma}\label{l:stationary-domination}
Let \(P=(v_0,\ldots,v_L)\) be a true prefix avoiding \(c,v\),
with \(v_0=u\), \(v_1=u+d_0\), and \(L\ge m+2\), \(m=10\).
Every true continuation to its first hit of \(v\), together with
each phase history, is dominated by the corresponding path of
\(T_{X,d_0}\) from its prefix phase, last-window class and endpoint.
The comparison holds for every finite suffix horizon and hence
for their nonnegative suprema.
In this comparison:
forgotten true revisits have weight \(1/5\) no greater than any
relaxed first-visit diagonal weight; forgetting dead non-outgoing
neighbours only increases the reward, using \(b'_\tau\le b_\tau\);
and the known-site killing rules cannot kill a true continuation.
Indeed, the known initial departures at times \(0,1\) are outside
the memory at every suffix time, and a memory-detected additional
departure at \(u\) or \(u+d_0\) would be a forbidden third departure.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: Prove the degree/bond counting at both known sites and the initial-bond exclusion. The hypothesis L>=m+2 is indispensable. Do not extend this claim to L=m. First-hit stopping, centre exclusion and the exact phase identity are part of the domination proof.


### l:Bellman-soundness — [AMENDED] A supersolution bounds all stopped paths


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS stationary Bellman argument; to be written.

**Dependencies:** definitions and finite elementary algebra only.

**Interface:** yes.


```latex
\begin{lemma}\label{l:Bellman-soundness}
Let \(T\) be a nonnegative, finitely branching weighted transition
operator on a set of states, with zero rows on a terminal set.
Let \(g\ge0\) be supported on that terminal set.
If a finite-valued function \(F\ge0\) satisfies
\(g+TF\le F\), then for every integer \(n\ge0\),
\[
 \sum_{j=0}^{n}T^jg\le F .
\]
Consequently the nonnegative sum of all finite first-hit path
weights times their terminal rewards is finite and at most \(F\).
It suffices that \(F=g\) on terminal states and \(TF\le F\)
elsewhere.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: This is finite induction followed by a supremum of nonnegative partial sums. No stochastic normalization, resolvent equality, spectral radius, convergence rate or infinite-time Markov process is an input.


### d:stationary-certificate — [AMENDED] The finite integer supersolution contract


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS stationary integer format; exact rational coefficient ceilings.

**Dependencies:** d:stationary-walk.

**Interface:** yes.


```latex
\begin{definition}\label{d:stationary-certificate}
For a case \((X,d_0)\), fix \(R=70\),
\(B_R=\{-R,\ldots,R\}^2\), \(V=2^{16}\), and \(D_3=2^{48}\).
Supply integers \(Z_{\varphi,q}>0\) and
\(U_{\varphi,q,x}\ge0\), \(x\in B_R\).
Set \(\widetilde U_{\varphi,q,x}=U_{\varphi,q,x}\) inside \(B_R\)
and \(Z_{\varphi,q}\) outside, and \(F=\widetilde U/V\), \(z=Z/V\).
For each individual transition coefficient \(t\) of the exact
stationary or free operator, use the proved rational ceiling
\(\widehat t=p(t)/D_3\), \(p(t)=\lceil D_3t\rceil\);
zero coefficients may be omitted.
The certificate checks all the following:
\[
 \begin{gathered}
 \sum_{\text{free edges }e\text{ from }(\varphi,q)}
       p(t_e)Z_{\operatorname{dest}(e)}
       \le D_3Z_{\varphi,q},\qquad Z_{{\rm C},q},Z_{{\rm D},q}\ge V,\\
 0\le U_{\varphi,q,x}\le Z_{\varphi,q},\qquad
 U_{\varphi,q,c}=0,\qquad U_{\varphi,q,v}=Vg_\varphi,\\
 \sum_{\text{stationary edges }e\text{ from }(\varphi,q,x)}
       p(t_e)\widetilde U_{\operatorname{dest}(e)}
       \le D_3 U_{\varphi,q,x}
       \quad(x\in B_R\setminus\{c,v\}).
 \end{gathered}
\]
All tests are integer inequalities on the regenerated automaton,
directions, phases and lattice sites, not on a trusted supplied matrix.
\end{definition}
```


[AMENDED] Writing constraint / short proof sketch: The data are four phase/window Z arrays and four phase/window/position U arrays. The retained uint32 values use value scale 2^16; the independent coefficient scale is 2^48. Terminal rewards are 0,0,1,1, so the stored C,D target values are exactly 2^16. Prove every ceiling bounds its exact rational coefficient.


### l:stationary-local-global — [AMENDED] Finite caps and free rows imply a global Bellman inequality


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS finite-square-to-lattice extension argument; to be written.

**Dependencies:** d:stationary-certificate, l:Bellman-soundness.

**Interface:** yes.


```latex
\begin{lemma}\label{l:stationary-local-global}
Every certificate of Definition~\ref{d:stationary-certificate}
defines a finite-valued \(F\) on the entire lattice with
\(F=z\) outside \(B_R\), \(F\le z\), and
\[
 g+T_{X,d_0}F\le F .
\]
For an inside site this follows from its checked integer row and
coefficient ceilings. For an outside site every successor value
is at most its corresponding \(z\), and the exact stationary row
is dominated by the free row; the checked free inequality
implies \(\mathsf Wz\le z\).
Thus \(F\) bounds every stopped continuation as in
Lemma~\ref{l:Bellman-soundness}.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: The cap U<=Z is needed at every stored site, not just on its boundary. This is the proof that finite data control every lattice position; a spatially periodic aliasing argument is not used.


### d:prefix-bound — [AMENDED] Exact short trails and exact prefix evaluation


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS experiments/exact_stationary_prefix.py; exact prefix logs.

**Dependencies:** d:kernel-order, d:phaseweights, d:stationary-certificate.

**Interface:** yes.


```latex
\begin{definition}\label{d:prefix-bound}
For each case \((X,d_0)\), let \(S_{X,d_0}\) be the exact
\(h\)-weighted kernel sum over closed trails of lengths \(1\le n\le L=12\)
with first direction \(d_0\), using their prescribed short-trail orderings.
Let \(\mathcal P_{X,d_0,L}\) be all true length-\(L\) prefixes
avoiding \(c\) and \(v\), with first direction \(d_0\).
For \(P\) in this set, let \(p_\varphi(P)\) be the sum of its
exact phase-history products ending in phase \(\varphi\), starting
with weights one in A and B. Use actual trail revisits, actual dead
neighbours and the type-dependent rewards, with the long-trail
straight-first phase weights.
Write \(x(P)\) for its endpoint and \(q(P)\) for its last-window class.
For the potential of its case define the rational number
\[
 J_{X,d_0}=S_{X,d_0}
       +\sum_{P\in\mathcal P_{X,d_0,12}}\sum_\varphi
                    p_\varphi(P)F(\varphi,q(P),x(P)).
\]
A hit at time \(12\) is in \(S_{X,d_0}\), not in the prefix sum.
\end{definition}
```


[AMENDED] Writing constraint / short proof sketch: Generate prefixes from distinct unoriented bonds and departure counts; prove enumeration completeness, exact short ordering and exact phase weights. A compact endpoint table is allowed only after checking its equality with the full potential at each referenced coordinate. No imported C prefix result may replace this evaluation.


### l:prefix-domination — [AMENDED] The stationary bound covers the complete row


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS stationary prefix argument; to be written.

**Dependencies:** l:stationary-domination, l:stationary-local-global, d:prefix-bound.

**Interface:** yes.


```latex
\begin{lemma}\label{l:prefix-domination}
For every case whose integer certificate passes, the \(h\)-weighted
contribution of all true closed trails of that first direction,
over every length, is at most \(J_{X,d_0}\).
This holds uniformly for every finite length cutoff, with the same
upper bound. The short part uses the exact order through \(12\);
all longer trails split uniquely into a surviving length-\(12\)
prefix and a dominated stopped suffix.
\end{lemma}
```


### l:kernel-reflection — [AMENDED] The one reflection used in row B


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** baseline B north/south reflection; COMPFEAS five-case assembly.

**Dependencies:** d:kernel, d:kernel-order.

**Interface:** yes.


```latex
\begin{lemma}\label{l:kernel-reflection}
For row B, reflection \((x_1,x_2)\mapsto(x_1,-x_2)\) fixes
\(c,u,v\), interchanges the first directions N and S, and preserves
every trail weight, type, dead pair, shift, \(h\)-reward and
prescribed ordering. Hence the true B/N and B/S kernel contributions
are equal at every length and every finite cutoff.
No corresponding reduction is asserted for row C.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: This is a bijection of true lattice trails. It requires no equivariance of the compressed automaton or of the supplied potential and makes no symmetry assumption about the physical frame models.


### p:stationary-check — [AMENDED] The five finite stationary data checks and exact prefixes


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS data/stationary_{B,C}_m10_R70_d*_coarse.bin.gz; logs/final_stationary_summary.json.

**Dependencies:** p:automaton10, d:stationary-certificate, d:prefix-bound.

**Interface:** yes.


```latex
\begin{proposition}\label{p:stationary-check}
For the five cases B/N, B/W, C/N, C/W, C/S, there exist
integer arrays \(Z,U\) satisfying every check in
Definition~\ref{d:stationary-certificate}, with
\(m=10,L=12,R=70\) and the specified scales.
Their regenerated quotient has \(3741\) states and the spatial
square has \(19881\) sites. Their exact rational prefix evaluations obey
\[
 \begin{array}{c|ccccc}
 (X,d_0)&(B,{\rm N})&(B,{\rm W})&(C,{\rm N})&(C,{\rm W})&(C,{\rm S})\\ \hline
 10^9J_{X,d_0}\ \le&
 351207554&290599163&527872005&380754375&273048088
 \end{array}
\]
Each displayed upper bound denotes an exact integer inequality
after clearing the rational prefix denominator.
\end{proposition}
```


[AMENDED] Writing constraint / short proof sketch: The table uses nine-decimal ceilings of the exact logged fractions. The report’s six-decimal component bounds are too coarse to recover 0.993015 in row B. These are finite verification targets, not a claim that the C checks or gzip hashes are Lean proofs. Prove that each file is related to the regenerated mathematical index sets and coefficients.


### l:stationary-assembly — [AMENDED] The stationary certificates imply H3_h


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS exact five-case rational assembly.

**Dependencies:** p:stationary-check, l:prefix-domination, l:kernel-reflection, h:H3.

**Interface:** yes.


```latex
\begin{lemma}\label{l:stationary-assembly}
With the five certified potentials and their exact prefix bounds,
\[
 (M_1h)_B\le2J_{B,{\rm N}}+J_{B,{\rm W}}\le\rho_0h_B,\qquad
 (M_1h)_C\le J_{C,{\rm N}}+J_{C,{\rm W}}+J_{C,{\rm S}}
                                      \le\rho_0h_C ,
\]
where \(h_C=5404319552844595/4503599627370496\) and
\(\rho_0=993015/10^6<1\).
The same inequalities hold for every finite true-trail cutoff;
therefore (H3\(_h\)) holds for the modified kernel.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: Use exact rational values or the safe nine-decimal ceilings, not sums of six-decimal displayed components. No parity improvement is used: the Bellman proof covers all suffix horizons. In particular no factor lambda^2/(1-lambda^2), periodic rule-release bound or old remainder lemma is needed.

## Appendix D. Operator-only verification of (H1)


### l:Iw — [AMENDED] Integrating out the passage site


**Owner:** C. **Status:** kept with edits.

**Proof source:** baseline l:Iw/e:IcJ; OPPORTUNITIES #2.

**Dependencies:** d:pattern, l:moments, l:finitefacts.

**Interface:** yes.


```latex
\begin{lemma}\label{l:Iw}
Let \(Z_w\) be the finite template functional after deleting
the passage site and its incident factors, retaining all other
present bonds and all covered slot factors. Put \(P_{ab}=n_a\cdot n_b\)
for nonremoved sites and zero if either is removed.
For the out-neighbour \(o\) and the other two neighbours \(f,g\),
\[
 Z_{\rm cur}=Z_w[I],\qquad Z_{\rm next}=Z_w[J]>0,\qquad
 I=1+\tfrac13(P_{fg}+P_{fo}+P_{go}),\quad J=1+\tfrac15P_{fg}.
\]
For \(0<c<1\), \(F_c=Z_{\rm cur}-cZ_{\rm next}=Z_w[I-cJ]\), with
\[
 I-cJ=(1-c)+\tfrac13(P_{fo}+P_{go})+(\tfrac13-\tfrac c5)P_{fg}.
\]
Both partition polynomials are affine in each slot vector and
invariant under simultaneous orthogonal transformations of the slots.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: The mathematical statement is unchanged; it is now exported to make the Gram/residual certificate interface self-contained.

### l:leaf — [AMENDED] Only the elementary leaf reductions


**Owner:** C. **Status:** kept with edits.

**Proof source:** baseline l:leaf; OPPORTUNITIES #2/#21.

**Dependencies:** l:35, l:moments, l:finitefacts.

**Interface:** yes.


```latex
\begin{lemma}\label{l:leaf}
In a covered template, integrating a nonremoved tip or corner
with no present internal bond gives a positive factor depending
only on its own slots.
A tip with its one internal bond to \(x\) gives
\(A(1+(3/5)u\cdot n_x)\), \(A>0,\ |u|\le1\).
A corner with exactly one internal bond to \(x\) gives
\(A(1+\rho u\cdot n_x)\), \(A>0,\ |u|\le1\), where
\(\rho=1/2\) for status \(\mathrm U\) and \(\rho=1/3\)
for status \(\mathrm D\).
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: The mathematical statement is unchanged; it is now exported to make the Gram/residual certificate interface self-contained.

### d:reduction — [AMENDED] The two allowed representations and vector groups


**Owner:** C. **Status:** kept as is.

**Proof source:** baseline e:hatF and its representation definitions.

**Dependencies:** l:leaf, l:Iw.

**Interface:** yes.


```latex
\begin{definition}\label{d:reduction}
Delete tips and corners with no present internal bond, dropping
their common positive factors. Replace every bonded tip by a
single vector and radius \(3/5\).
In the reduced representation also replace each one-bond corner
by a single vector of radius \(1/2\) or \(1/3\) according to
Lemma~\ref{l:leaf}; in the unreduced representation retain its spin
and two slots. Other bonded corners retain their two slots.
Let \(u=(u_1,\ldots,u_k)\) list these remaining vectors, and define
\(\widehat Z_{\rm cur},\widehat Z_{\rm next}\) by these replacements,
\(\widehat F_c=\widehat Z_{\rm cur}-c\widehat Z_{\rm next}\).
A group is one single vector or the two slots of a retained corner.
\end{definition}
```


[AMENDED] Writing constraint / short proof sketch: The mathematical statement is unchanged; it is now exported to make the Gram/residual certificate interface self-contained.

### c:reduce — [AMENDED] Reduction to unit-vector positivity


**Owner:** C. **Status:** kept as is.

**Proof source:** baseline c:reduce.

**Dependencies:** d:reduction, l:leaf.

**Interface:** yes.


```latex
\begin{corollary}\label{c:reduce}
In either representation, \(\widehat F_c\) is real, affine in
each vector and invariant under simultaneous \(\mathrm O(3)\).
If \(\widehat F_c\ge0\) on \((\mathbb S^2)^k\), then
\(F_c\ge0\) on \((\mathbb S^2)^{20}\).
For each original slot assignment there are a common \(K>0\)
and vectors \(\widehat u\) in the closed unit ball such that
\(Z_{\rm cur}=K\widehat Z_{\rm cur}(\widehat u)\) and
\(Z_{\rm next}=K\widehat Z_{\rm next}(\widehat u)\).
\end{corollary}
```


[AMENDED] Writing constraint / short proof sketch: The mathematical statement is unchanged; it is now exported to make the Gram/residual certificate interface self-contained.

### d:Pauli — [AMENDED] The Pauli operator and product densities


**Owner:** C. **Status:** kept with edits; replaces coherent spinors on the whole sphere.

**Proof source:** baseline e:Fexp/e:OF; OPPORTUNITIES #2.

**Dependencies:** definitions and finite elementary algebra only.

**Interface:** yes.


```latex
\begin{definition}\label{d:Pauli}
For a real polynomial affine in each vector, expand uniquely
\[
 F(u)=\sum_{a\in\{0,1,2,3\}^k}f_a\prod_i u_i^{a_i},
 \qquad u_i^0=1,\qquad
 \mathcal O(F)=\sum_a f_a\bigotimes_i\sigma_{a_i},\quad\sigma_0=I.
\]
For \(\mathcal I\subset\{1,\ldots,k\}\), invert those vectors,
writing \(u^{\mathcal I}\) and \(F^{\mathcal I}(u)=F(u^{\mathcal I})\).
For \(|a|\le1\), put \(\rho(a)=(I+a\cdot\sigma)/2\).
Set \(S_z=\frac12\sum_i\sigma_3^{(i)}\) and
\(S_\pm=\sum_i(\sigma_1^{(i)}\pm\mathrm i\sigma_2^{(i)})/2\).
\end{definition}
```


[AMENDED] Writing constraint / short proof sketch: The mathematical statement is unchanged; it is now exported to make the Gram/residual certificate interface self-contained.

### l:inversion — [AMENDED] Positivity from a supplied inversion


**Owner:** C. **Status:** kept with edits.

**Proof source:** baseline l:inversion; OPPORTUNITIES #2/#21.

**Dependencies:** d:Pauli.

**Interface:** yes.


```latex
\begin{lemma}\label{l:inversion}
For \(|u_i|\le1\), each \(\rho(u_i)\) is positive semidefinite
of trace one, and
\[
 F(u)=\operatorname{Tr}\!\left[
      \mathcal O(F^{\mathcal I})
                 \bigotimes_i\rho((u^{\mathcal I})_i)\right].
\]
Thus a single inversion \(\mathcal I\) with
\(\mathcal O(F^{\mathcal I})\ge0\) implies \(F\ge0\)
on the product of closed unit balls, in particular on unit vectors.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: The mathematical statement is unchanged; it is now exported to make the Gram/residual certificate interface self-contained.

### l:Ostruct — [AMENDED] The retained operator symmetries


**Owner:** C. **Status:** kept with edits (finite polynomial covariance).

**Proof source:** baseline l:Ostruct; OPPORTUNITIES #2/#5.

**Dependencies:** c:reduce, d:Pauli.

**Interface:** yes.


```latex
\begin{lemma}\label{l:Ostruct}
For \(\mathcal I\) a union of vector groups and
\(\mathcal O=\mathcal O(\widehat F_c^{\mathcal I})\),
the matrix in the standard tensor basis is real symmetric.
It commutes with \(U^{\otimes k}\) for every \(U\in\mathrm{SU}(2)\)
and with \(S_z,S_+,S_-\).
For a retained \(\mathrm U\)-corner pair, if \(\Pi\) projects that
pair onto \(\operatorname{Sym}^2\mathbb C^2\), then
\(\mathcal O=\Pi\mathcal O\Pi\).
For a retained \(\mathrm D\)-corner pair, \(\mathcal O\) commutes
with exchange of its two factors.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: The mathematical statement is unchanged; it is now exported to make the Gram/residual certificate interface self-contained.

### d:exchange — [AMENDED] Exchange sectors and the central weight


**Owner:** C. **Status:** kept as is.

**Proof source:** baseline definitions preceding l:sector and p:certificate.

**Dependencies:** d:reduction, d:Pauli.

**Interface:** yes.


```latex
\begin{definition}\label{d:exchange}
Let \(V\) be the tensor product of \(\mathbb C^2\) for singles,
\(\operatorname{Sym}^2\mathbb C^2\) for retained \(\mathrm U\)-pairs,
and \(\mathbb C^2\otimes\mathbb C^2\) for retained \(\mathrm D\)-pairs.
For each assignment \(\epsilon\) of exchange signs to the
\(\mathrm D\)-pairs, let \(V_\epsilon\) replace each of those
pair factors by its symmetric or exterior square.
If there are \(t\) singles, let \(\kappa=0\) for even \(t\),
\(\kappa=1/2\) for odd \(t\), and
\(V_\epsilon^\circ=\ker(S_z-\kappa I)|_{V_\epsilon}\).
The standard sector basis uses \(e_\pm\) for singles and
\(e_+\otimes e_+\), \(e_+\otimes e_-+e_-\otimes e_+\),
\(e_-\otimes e_-\) for symmetric pairs, with
\(e_+\otimes e_--e_-\otimes e_+\) for antisymmetric pairs.
\end{definition}
```


[AMENDED] Writing constraint / short proof sketch: The mathematical statement is unchanged; it is now exported to make the Gram/residual certificate interface self-contained.

### l:sector — [AMENDED] Ladder-operator detection of every eigenvalue


**Owner:** C. **Status:** kept with edits (weaker concrete commutation hypothesis).

**Proof source:** baseline l:sector; OPPORTUNITIES #5.

**Dependencies:** d:exchange.

**Interface:** yes.


```latex
\begin{lemma}\label{l:sector}
Let \(V'\) be any tensor sector formed from singles and
symmetric or exterior pair factors as above.
If a Hermitian \(\mathcal O'\) on \(V'\) commutes with
\(S_z,S_+,S_-\), then it preserves the central-weight space
\(V'^\circ\), and its restriction there has the same set of
eigenvalues as \(\mathcal O'\).
In particular \(\mathcal O'\) is positive definite if and only if
that restriction is positive definite.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: Use S_+^*=S_-, [S_+,S_-]=2S_z and the norm identity for lowering at positive weight (raising at negative weight). A finite ladder reaches 0 or 1/2 without vanishing. Do not assert equality of multiplicities or invoke a decomposition of arbitrary SU(2) representations. The mathematical statement is unchanged; it is now exported to make the Gram/residual certificate interface self-contained.

### l:gram-residual — [AMENDED] Division-free Gram/residual positivity


**Owner:** C. **Status:** new Lane C proof obligation.

**Proof source:** COMPFEAS H1 recommendation; exact checks of all exchange-sector blocks.

**Dependencies:** definitions and finite elementary algebra only.

**Interface:** yes.


```latex
\begin{lemma}\label{l:gram-residual}
Let \(M\) be a symmetric integer matrix of size \(n\).
Let \(g,d,S\) be positive integers and \(L\) an integer
lower-triangular \(n\times n\) matrix; no invertibility is required.
Define the symmetric integer residual
\[
 E=dS^2M-gLL^{\mathsf T}.
\]
If, for every row,
\[
 E_{ii}>0,\qquad E_{ii}>\sum_{j\ne i}|E_{ij}|,
\]
then \(E\) and \(M\) are positive definite over \(\mathbb R\)
and, as Hermitian matrices, over \(\mathbb C\).
The case \(L=0\), \(g=d=S=1\), is the direct strict
diagonal-dominance certificate.
All hypotheses can be checked with integer sums, products,
absolute values and comparisons, without division or determinants.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: Prove strict diagonal dominance with positive diagonal gives a positive quadratic form, and add the positive-semidefinite Gram term. No gcd, factorization accuracy, Cholesky identity, shift estimate or numerical eigenvalue enters the certificate.

### l:integercheck — [AMENDED] Exact reconstruction of the integer sector matrix; Bareiss fallback only


**Owner:** C. **Status:** reconstruction retained; Bareiss explicitly demoted to optional fallback.

**Proof source:** baseline e:intscale/e:Meps; COMPFEAS H1 Gram/residual recommendation.

**Dependencies:** l:Ostruct, d:exchange, l:moments.

**Interface:** yes.


```latex
\begin{lemma}\label{l:integercheck}
For \(c=p/q\in(0,1)\) rational with positive integers \(p,q\),
choose a positive integer \(D_0\) clearing the coefficients of
\(3D_0\widehat Z_{\rm cur}\) and \(5D_0\widehat Z_{\rm next}\).
In the integer-coordinate central-sector basis, let \(A_\epsilon\)
and \(A'_\epsilon\) be the Hermitian-form matrices of their
inverted Pauli operators. These are symmetric integer matrices.
The form of \(\mathcal O(\widehat F_c^{\mathcal I})\) on the sector
is positive definite if and only if
\[
 M_\epsilon=5qA_\epsilon-3pA'_\epsilon
\]
is positive definite. The primary verification uses the integer
Gram/residual witness of Lemma~\ref{l:gram-residual}.
As an optional fallback only, positivity is equivalent to positivity of all its
leading principal minors. More explicitly, for a size-\(t\) matrix
set \(A^{(0)}=M_\epsilon\), \(p_{-1}=1\), and for \(0\le j<t\)
set \(p_j=A^{(j)}_{jj}\) and update the trailing entries by
\[
 A^{(j+1)}_{il}
    =\frac{p_jA^{(j)}_{il}-A^{(j)}_{ij}A^{(j)}_{jl}}{p_{j-1}}
       \quad(i,l>j).
\]
As long as preceding pivots are nonzero, each division is exact
in the integers and \(p_j\) is the leading principal minor of
order \(j+1\). Acceptance requires every division exact and every
pivot positive.
\end{lemma}
```


[AMENDED] Writing constraint / short proof sketch: Reconstruct the actual matrix M_epsilon=5q A_epsilon-3p A-prime_epsilon from pattern data. It is 15 D_0 q times the Hermitian-form matrix in the unnormalized integer-coordinate basis, a positive congruence scale. The stated Bareiss recurrence remains sound but is not the main certificate proposition or required primary checker. Do not make a stored matrix or stored pivots an axiom.


### p:certificate — [AMENDED] The operator-only Gram/residual certificate proposition


**Owner:** C. **Status:** replaces the positive-definite-sector premise by the adopted integer witness format.

**Proof source:** baseline p:certificate reduction; COMPFEAS H1 Gram/residual witness.

**Dependencies:** l:integercheck, l:gram-residual, l:Ostruct, l:sector, l:inversion, c:reduce, d:exchange.

**Interface:** yes.


```latex
\begin{proposition}\label{p:certificate}
Let \(c=p/q\in(0,1)\), with \(p,q\in\mathbb Z_{>0}\).
Choose either allowed representation, an inversion which is a
union of groups, and a justified positive denominator \(D_0\).
For every supported central exchange sector reconstruct
\(M_\epsilon=5qA_\epsilon-3pA'_\epsilon\) as in
Lemma~\ref{l:integercheck}.
Suppose that for each sector there are positive integers
\(g_\epsilon,d_\epsilon,S_\epsilon\) and an integer lower-triangular
matrix \(L_\epsilon\) of its dimension such that
\[
 E_\epsilon=d_\epsilon S_\epsilon^2M_\epsilon
                  -g_\epsilon L_\epsilon L_\epsilon^{\mathsf T},
 \qquad
 (E_\epsilon)_{ii}>
          \sum_{j\ne i}|(E_\epsilon)_{ij}|\quad\text{for every }i.
\]
Then \(F_c(m)\ge0\) for every \(m\in(\mathbb S^2)^{20}\).
The operator may vanish on the discarded antisymmetric
\(\mathrm U\)-pair subspaces; positive definiteness is required
only on the supported exchange sectors.
\end{proposition}
```


[AMENDED] Writing constraint / short proof sketch: The residual condition already forces a positive diagonal. The 8,439 directly dominant blocks can use L=0 and g=d=S=1; the remaining 3,734 use factors. Every sector matrix must be reconstructed and every supported sector checked. This is the main Appendix D certificate statement; Bareiss is a fallback, not a second premise.

# Exhaustive baseline statement audit


Each labelled theorem-like environment in the baseline is covered below; the sole unlabelled §6 remark is handled separately. Removed assertions are replaced or omitted for the adopted package, not silently reverted to an earlier version.


| Baseline label | Disposition | Exact revised target / reason |
|---|---|---|

| l:boundaryconn | replace | l:boundaryconn gives star-connectivity; l:thicken gives nearest-neighbour connectivity |

| l:Iw | edit | l:Iw, finite functional |

| l:leaf | edit | l:leaf, finite functional |

| c:reduce | keep | c:reduce |

| l:inversion | edit | l:inversion, product density matrices |

| l:Ostruct | edit | l:Ostruct, polynomial covariance and concrete commutators |

| l:sector | edit | l:sector, ladder-operator proof |

| p:certificate | replace | [AMENDED] p:certificate with per-sector integer Gram/residual witnesses |

| l:radius | remove | replaced by operator-only H1; elementary l:35 and l:leaf remain |

| p:closed | remove | replaced by operator-only H1; closed-form/pruning/FKG branch omitted |

| l:CW | remove | [AMENDED] h:H3 and stationary assembly replace spectral-radius theory |

| l:memdom | remove | [AMENDED] l:stationary-domination and l:automaton-quotient; no periodic spatial walk |

| l:remainder | remove | [AMENDED] l:Bellman-soundness and l:stationary-local-global; no late-time remainder |

| p:tail | replace | [AMENDED] p:stationary-check, l:stationary-assembly and t:inputs for the modified kernel |

| r:tailtypedep | replace | [AMENDED] rigorous type-dependent bounds and stationary main line; no old 0.91825 assertion |

| t:main | replace | t:main |

| l:edge | keep | l:edge |

| l:divisibility | edit | l:divisibility (torus scope) |

| d:frame | edit | d:frame |

| l:tight | keep | l:tight |

| t:QD | edit | t:QD and l:quantumfibre |

| r:QDgeneral | remove | author scope: no general-graph theorem or extension remark |

| t:K | remove | replaced by t:periodic; OPPORTUNITIES #1 |

| l:commute | remove | old Knabe proof no longer used; replaced by finite block contraction |

| l:fibre | remove | old Knabe proof no longer used; replaced by l:comparison |

| l:autocorr | remove | old Knabe proof no longer used; replaced by periodic placement counts |

| r:Kpins | replace | l:boxlift uses two spare sites; its stronger size hypothesis avoids repeated exterior images |

| l:boxcell | replace | l:boxlift, without cells |

| l:compare | replace | l:density and l:comparison, at physical-site scale |

| t:MOS21 | remove | replaced by l:stopped/l:hamming/t:periodic; no cited mixing theorem |

| t:MO41 | remove | replaced by l:stopped/l:hamming/t:periodic; no compatible-union theorem |

| r:finiteS | remove | the finite proof treats site-dependent alphabets directly |

| l:shellgeom | edit | l:shellgeom, including clearance |

| d:W | edit | d:W, all colourings and physical translates |

| p:surgery | edit | p:surgery as corollary of l:stopped |

| c:gapcell | replace | t:periodic; no box-gap detour |

| t:mainW | replace | t:mainW |

| l:35 | edit | l:35, finite functional and explicit tip range |

| l:exact | edit | l:exact |

| l:cut | edit | l:cut with common minorization |

| h:P | edit | h:P, same quantifiers and distances, finite functional |

| l:removal | replace | l:removal with constants 1,4,2 and one seed |

| l:cutgeom | replace | l:cutgeom, site scale and thickening |

| l:Xconn | replace | l:Xconn and l:thicken; no diagonal-block test |

| t:cutMOS | replace | t:cutMOS with l_0=64 and p_0=exp(-2E) |

| r:Pweak | remove | replaced by the adopted narrowed exponential interface h:P; no polynomial-decay corollary |

| d:domain | edit | d:domain, no scalar mass but protected-boundary distinction retained |

| l:stepid | replace | l:stepid, U k<=3 and D k<=1 only |

| p:pairwalk | edit | p:pairwalk, admissible starts and endpoint degree bound |

| l:response | edit | [AMENDED] uniform identity retained; l:response-typed supplies the main coefficients |

| l:exposure | edit | l:exposure; revisit coefficient moved to a_D |

| d:pattern | edit | d:pattern, corrected covered rules retained |

| h:H1 | edit | h:H1, direct inequalities, no infimum |

| l:local | edit | l:local, finite polynomial tip covariance |

| h:H2 | edit | [AMENDED] same all-length property; exact memory-6 rate q_* and C_V=10 |

| l:onepoint | edit | l:onepoint; preserve the sum of maxima |

| l:closure | edit | l:closure; no mass-reset phrase |

| h:H3 | replace | [AMENDED] fixed type-dependent kernel/order/vector contract proved by stationary certificates |

| l:Mtheta | edit | [AMENDED] same analytic argument for q_*<1 and the modified kernel |

| t:rec | edit | [AMENDED] type-dependent l:recineq and t:rec; unchanged renewal and source form |

| r:typedep | replace | [AMENDED] l:log-mean-bounds/l:response-typed; turn alpha corrected to 0.150000 |

| t:inputs | replace | [AMENDED] exact Gram, small-H2 and stationary-H3 theorem |

| l:alm | edit | [AMENDED] one-step true-revisit specialization with explicit base constant |

| t:H1 | edit | [AMENDED] same H1 conclusion, operator-only Gram/residual route |

| r:H1sharp | remove | replaced by operator-only H1; no c(pi) optimization/closed-form branch |


## Equation-only material and unnumbered baseline assertions

The following mapping supplements the numbered-statement audit; it prevents losing corrected definitions that happened not to be theorem environments.

| Baseline material | Revised location / disposition |
|---|---|
| e:H, e:B | d:model; nonzero B and frustration-freeness in p:toruskernel |
| e:zeta, e:Vinner | d:poly; finite spinor choices and monomial norm replace the sphere definition |
| e:star | l:star |
| e:icodod, old ico/dodeca design proof | replaced by d:moment, l:moments and l:threeframes |
| e:qmod | l:qmod, with no global spinor selection |
| e:mucirc, e:lambdaHB | d:framemodel and t:QD; reference pi remains unnormalized |
| e:QDcomp and corrected c_x factorizations | l:quantumfibre |
| e:muD, e:QDrot | removed global gauge; replaced by the antiferromagnetic torus law and l:boxlift |
| e:muDW | d:framemodel, all proper plane colourings |
| all §3 criterion equations e:MRF–e:Lsquare | removed with Knabe, including t(ell), kappa_ell and weighted/flat autocorrelations; the positive torus product law remains d:framemodel |
| cell definitions, offsets and compatible scales; e:SM/e:MOS22 | removed; no cells, compatible volumes or strong-mixing assertion remain |
| e:shells/e:W | d:shells/d:W, now physical sites |
| e:prop21 | p:surgery, retained as a short corollary; l:stopped is the consumed stronger statement |
| e:Zpin, original S(G), positivity/conditional independence | d:pinmodel, l:finitefacts; pins stay unit vectors |
| e:moments and arbitrary-order free positivity | replaced by l:moments and degree-admissible l:finitefacts; no assertion for arbitrary high-degree inserted observables |
| e:cutcost/e:windowlaw/e:cutratio | l:cut, including actual W_B, factorization, full support and common minorization |
| e:P | h:P |
| e:removal/e:Ij/e:telescope | l:removal; same integration/telescoping with coarser constants and seed retained |
| e:Ucut/e:Xcut/e:Ualt/e:cutsum | d:thickcut/l:cutgeom; no U-prime expansion to cells |
| e:ZD and scalar trace mass | d:domain/d:trace; mass field replaced by a_D |
| e:pairwalk/e:IJ/e:lambda/e:exposure | p:pairwalk/d:ratios/l:response/l:exposure |
| e:cpi and numerical minimization claims | removed; h:H1 is the direct pointwise inequality |
| unlabelled covered-pattern/terminal-defect remark in §6 | l:terminalcover, with the twelve-exception correction retained |
| e:FX/e:kernel/e:recineq | [AMENDED] pair envelopes unchanged; d:kernel and l:recineq use the rigorous type-dependent coefficients |
| fixed-point/truncated Phi_N calculation | replaced by l:renewal |
| e:mT, phase weights, old memory quotient implementation | [AMENDED] d:phaseweights and stationary lattice Bellman contracts replace the periodic spatial walk; only the memory automaton is quotiented |
| tab:tail and its exact assembly | [AMENDED] replaced by the five exact stationary prefix bounds and rho_0=0.993015 for the modified kernel |
| e:Fc/e:Zw/e:IcJ/e:hatF | l:Iw/d:reduction |
| e:Fexp/e:OF/e:inversion | d:Pauli/l:inversion, using product density matrices |
| e:intscale/e:Meps | [AMENDED] l:integercheck retains positive scale 15 D_0 q; p:certificate uses l:gram-residual, with Bareiss fallback only |
| e:rhoUD/e:ZVbeta/e:subsets/e:FKGstep/e:closed/e:Rmu/e:5469 | removed with the closed-form/FKG branch; not needed to prove operator-only H1 |
| tab:H1, selected minima/margins, sharpness diagnostics | omit from the revised proof; no global optimum was certified. If ever restored as remarks, all baseline qualifications must be restored verbatim |
| app-constants.tex | removed; useful constants are defined at their point of use; no explicit-constant appendix |
| historical arithmetic/provenance paragraphs | [AMENDED] use the selected COMPFEAS witnesses and exact reconstruction/coverage/soundness account; native exact verification and kernel verification remain distinct |

The supplement's general-graph kernel/dimension theorem, general-graph QD clause, small sizes below three, classical rectangle corollaries, and open-boundary dimensions are not imported. Neither are infinite-volume, thin-torus, skew-quotient, clustering, perturbation or explicit-numerical-gap additions. These omissions implement the author's scope, not contrary mathematical claims.

## Baseline statements removed as separate assertions

The audit table above gives the replacement for every removed numbered statement. In particular the removed set comprises t:K, l:commute, l:fibre, l:autocorr, r:Kpins, l:boxcell, l:compare, t:MOS21, t:MO41, r:finiteS, c:gapcell, r:QDgeneral, r:Pweak, [AMENDED] r:typedep (replaced by the rigorous main-line bounds), r:H1sharp, l:CW, l:memdom, l:remainder, p:tail, r:tailtypedep (replaced by the new stationary route), l:radius and p:closed. Some have direct replacement statements under new labels; the table distinguishes replacements from omissions.

No other baseline theorem, lemma, definition, hypothesis or corollary is silently dropped. “Kept with edits” means exactly the statement printed in this inventory, with the specified finite-functional or narrowed-domain change. [AMENDED] Closed forms and unused historical numerical variants stay archived. The rigorous type-dependent coefficients specified above are now the assigned main line, not an unused variant.


# Risks and completion checks

The adopted-item risk register is [RISKS.md](RISKS.md). [AMENDED] It includes the selected feasibility route and assigns every new domination, quotient, Bellman and prefix proof obligation; no permission or scope choice is pending.


This plan is accepted when the inventory and exported statements agree, all baseline environments have a disposition, all lane boundaries are explicit, the theorem graph is acyclic, and interfaces.tex compiles without unresolved references. Proof acceptance is a later milestone: each lane must meet its criteria, and the computational inputs must be proved, before t:main is published or formalized as unconditional.

[AMENDED] Validation completed: 105 exact statement entries and 65 verbatim interface exports; all 65 baseline audit rows retained; every changed or new mathematical statement has an [AMENDED] heading. The dependency graph is acyclic, all 60 untouched statement entries remain verbatim, and both the interface document and the full statement collection compile without warnings, overfull boxes or unresolved references. Small exact-rational checks confirmed the conservative C_V=10 bound, the 60 regenerated stationary response ceilings and the safe nine-decimal row assembly; no large certificate verification or new search was run.
