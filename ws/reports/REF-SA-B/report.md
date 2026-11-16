VERDICT: SOUND WITH FIXES

The assigned analytic argument is sound, conditional on the retained computer-assisted inputs in the corrected manuscript. I found no substantive gap, incorrect constant, parity restriction, or unverified use of translation invariance in Sections 3–5. The one fix identified below is a source locator. It changes neither an estimate nor a theorem statement.

This review covers [proof.tex](/home/ubuntu/aklt/review/REF-SA/proof.tex), lines 340–982 and 1035–1065, including its interfaces with Sections 1–2. I read the remainder for context, the corrected manuscript supplied as commit `9222abe`, and [mosproof.tex](/home/ubuntu/aklt/review/REF-SA/mosproof.tex). I did not inspect the adjudication reports, certificate archives, or other project files outside the authorized inputs. The corrected manuscript itself contains the relevant adjudicated formulations. This is an audit of the added analytic implications and the retained interfaces, not an independent replay of the large certificates.

**Numbered findings**

1. **Minor — incorrect subsection locator for the cut construction.**

   **Location:** proof.tex:868–870, proof of `t:cutMOS`.

   **Exact claim:** “Use exactly the cell sets \(U,F_i,B_i\) and physical cut \(X=\partial_\infty U'\) of manuscript Section 5.4.”

   **Why it fails:** In the supplied corrected manuscript, §5.4 is “Hypothesis (P) and the cost of removing a cut.” The construction being invoked is in §5.5, “The cut for the shells of the coupling argument,” at [sec5-cut.tex:136](/home/ubuntu/aklt/manuscript-corrected/sec5-cut.tex:136), specifically `e:Ucut`, `e:Xcut`, `l:cutgeom`, and `l:Xconn`. The intended results exist and have the properties used, so this is a citation defect only.

   **Repair:** Replace “manuscript Section 5.4” by “manuscript §5.5 (`s:cutgeom`, equations `e:Ucut`–`e:Xcut` and Lemmas `l:cutgeom`, `l:Xconn`).” Using the source labels also avoids dependence on subsection numbering.

There are no Critical or Major findings in the assigned material. In particular, the generalization of the MOSPROOF argument is proved with the necessary hypotheses on every translate; it is not an application of its translation-invariant main theorem to an inhomogeneous model.

**Statement table**

Locations below refer to the replacement proof unless a manuscript file is named. “Sound” for an implication includes its displayed hypotheses.

| Statement / location | Claim and hypotheses checked | Assessment |
|---|---|---|
| Section 3, lines 343–358; manuscript `t:K` | Positive nearest-neighbour product law, nontrivial site alphabets, \(\ell\ge2\), \(L,N\ge\ell+1\); both finite-size bounds and their constants | Sound, including periods three and equality at the size threshold |
| `r:Kpins`, lines 360–368 | Only actual torus exterior configurations enter \(g(\ell)\); repeated exterior images are covered by independent plane pin locations | Sound |
| Cell specification, lines 375–392 | \(2\times2\) physical cells, \(12^4=20736\) letters, four internal and eight crossing bonds, range one, arbitrary colouring and origin | Sound; the abstract alphabet identification preserves same-site equality |
| `e:energy`, lines 394–414 | Uniform lower bounds \(\beta=12^{-1}r_b^4\), \(\alpha=12^{-4}r_b^{12}\), and assignment bound \(\alpha^k\) | Sound for admissible frame-valued boundary data |
| `l:compare`, lines 416–444 | Physical gap at least \(c_0=\beta^5/4\) times the cell gap on a finite union of cells | Sound; no extra factor four |
| `l:boxcell`, `e:localgauge`, lines 446–496 | Every conditional even-sided torus box with \(L,N\ge\ell+1\) transports to a properly coloured plane cell box; all single-site expectations intertwine | Sound, including simultaneous repeated horizontal and vertical boundary images |
| `d:W`, lines 500–524 | Common parameters for every specification and translated square, every relevant exterior site and integer \(2\le i\le u^{1/4}\) outside \(I_0\), and every pair of admissible boundaries | Sound and sufficiently strong for the later coupling |
| `e:shellfacts`, lines 526–538 | Explicit geometric threshold, \(\lvert I_0\rvert\le1\), \(\lvert A_i\rvert\le8l_0\), separators and exclusion of \(y\) | Sound; reflection is used only for geometry |
| `l:stopped`, lines 540–590 | Full-volume coupling with failure on \(Q_h\) at most \((1-p_0\alpha^{16l_0})^{h-3}\), for integer \(4\le h\le\lfloor u^{1/4}\rfloor\) | Sound with site-dependent alphabets and potentials |
| Retained `p:surgery` conclusion, lines 592–596 | Original far-region TV estimate with exponent \(u^{1/4}-4\) | Sound consequence of stopping at \(h=\lfloor u^{1/4}\rfloor\) and restricting the coupling |
| `e:nchoice`, lines 609–614 | Simultaneous finite integer choice of \(n\); applicability of the geometric and window thresholds | Sound |
| `e:Kbound`, lines 624–646 | Hamming cost \(K_n\le M/1000\), \(M=n^8\), with the stated binomial bound and powers of \(n,d\) | Sound |
| `e:counts`, block contraction, lines 648–694 | Clamped full squares with multiplicities; bounds on \(T_x,S_x\); unnormalized block gap at least \(M^3\) | Sound, including points on a rectangle boundary and coincident clamp endpoints |
| `c:gapcell`, `e:cellconstants`, lines 600–715 | Every rectangle with both cell sides at least \(4M+1\) has gap at least \(m_0=\alpha^{v+1}/(1000v)\), \(v=(4M+1)^2\) | Sound uniformly in the family, translate and boundary |
| Removal of old mixing theorems, lines 717–722 | Compatible-union and strong-mixing conclusions are no longer required | Sound for the remaining proof uses |
| `t:mainW`, `e:ellchoice`, lines 726–756 | \(t\ge\max\{L_{\rm cell},\lceil(c_0m_0)^{-1}\rceil,1\}\), \(\ell=2t\), \(L_0=\ell+1\), \(c=g_\star c_0m_0/4\) | Sound for all periods at least \(L_0\), without a parity restriction |
| `l:exact`, lines 763–789 | Separate-degree-four quadrature with arbitrary site designs, signs and unit pins | Sound; only summed-out partition functions are identified |
| `e:windowlaw`, `e:nu`, lines 808–842 | Factorization with original legs retained and new legs into removed sites omitted; common positive reference window law | Sound for the actual site frames |
| `e:cutratio`, lines 843–856 | Density bounds \(e^{\pm2\epsilon}\) and TV bound \(\tanh(2\epsilon)\) | Sound |
| `t:cutMOS` geometry and `e:cutsum`, lines 858–882 | The unchanged cut is nonempty, nearest-neighbour connected, buffered from all original pins, with the stated geometric sum | Sound; correct the locator in Finding 1 |
| `e:epsilon`, lines 884–897 | Removal lemma applies to all required continuous pin assignments, including the first four-spin contribution | Sound with the exact stated rational upper bounds |
| `e:windowconstants`, lines 899–917 | A single eventual threshold \(M_\star\), finite \(\epsilon_{\max}\), and \(p_0=2/(e^{4\epsilon_{\max}}+1)>0\) | Sound; common to all colourings, origins and translates |
| Retained-input interfaces, lines 919–966 | Corrected continuous walk/recursion/certificate inputs retain their domains, pins, constants and planar parity conventions | Sound; no new frame-dependent certificate or odd-torus walk expansion is needed |
| Completion, lines 968–982 | Retained inputs imply (P), then uniform windows, box gaps, and the claimed main-theorem gap; small-size uniqueness uses Section 2 independently | Sound as a dependency chain |
| Replacement constants, lines 1035–1065 | New finite-energy/window/scale constants replace the old frame separation and compatible-set constants; the retained continuous coefficients do not change | Sound, subject to the supplied computational trust assumptions |

**Details of the analytic checks**

**Finite-size criterion and small periods.** The manuscript theorem is already stated for arbitrary positive site and bond potentials. Its commutation lemma uses conditional independence of non-neighbours, not bipartiteness. Its box-fibre decomposition uses the conditional measure with the actual fixed exterior, so it does not require independently choosable torus boundary spins.

For \(L,N\ge3\), the four offsets \((\pm1,0),(0,\pm1)\) are distinct. At period three, a coordinate cycle is a triangle, but the proof still cancels exactly all neighbouring ordered pairs and uses positivity only for commuting non-neighbour pairs. The circular correlations satisfy \(r_L(0)=r(0)\), \(r_L(\pm1)=r(1)\) even at \(L=\ell+1\); the missing residue keeps a neighbouring overlap from wrapping. The other overlaps are bounded by \(r(1)\) by the manuscript's interval argument. The parity used there is that of two intervals with the same centre, and is unrelated to either torus period.

For the weighted sequence, writing \(S=\sum_j j(\ell+1-j)\), the explicit sums give

\[
r(0)-r(1)=S,\qquad
\kappa_\ell=\frac{S^4}{\ell^2r(0)r(1)},\qquad
t(\ell)=\frac{\ell^2r(0)(r(0)-r(1))}{S^4}.
\]

These yield exactly the retained formulas. The corrected zero-total-Dirichlet-form branch prevents division by zero; in the other branch, terms with \(Y_a=0\) also have \(X_a=0\). No stationarity of the operator coefficients is used in summing over placements.

**Lifting, wrap-around bonds and signs.** After choosing a lift of the box, coordinate differences between its vertices have absolute value at most \(\ell-1\le L-2,N-2\). Consequently the torus bonds internal to the box are precisely its plane nearest-neighbour bonds. Exterior plane neighbours map outside the box, and each boundary bond has one lift incident to its lifted interior endpoint. Distinct boundary bonds can share their torus exterior endpoint without becoming the same bond.

At the smallest case, take \(\ell=2\), \(L=3\), and horizontal box coordinates \(0,1\). The exterior coordinates \(-1\) and \(2\) both map to column \(2\). Their plane signs are opposite, so the gauged pins at the two locations are opposite letters of the same antipodal frame. They are admissible separate plane pins. Each of the two original antiferromagnetic boundary factors is exactly its corresponding ferromagnetic factor. The same reasoning applies in both coordinate directions simultaneously when \(L=N=3\), and at arbitrary translates.

The pulled-back colouring \(\widetilde\kappa=\kappa\circ p\) is proper on the whole plane, including over a torus seam. Antipodality preserves each alphabet and its weight under the local sign change. The coordinatewise bijection transports the full law and each conditional resampling kernel. This uses no spinor phase convention and no global gauge on an odd torus. The orientation signs in the separate quantum comparison affect neither this classical transport nor its constants.

**Finite energy and the physical/cell comparison.** Since \(0<b<1\), \(r_b=b/(2-b)\) is in \((0,1)\). At most four factors change with a physical letter, and at most twelve factors change with a whole cell letter. Equal reference weights at each site give the exact lower bounds in `e:energy`. Restricting to a finite-volume exterior fibre preserves these bounds. Conditional probabilities given fewer letters are convex combinations of fully specified conditional probabilities; iterating this fact proves the assignment bound even with different alphabets at different cells. Arbitrary unit pins are deliberately excluded from these finite-energy claims.

For the elementary bound on \(k\) sites, the chain rule gives \(\mu(\sigma)\ge\beta^k\). The conditional Dirichlet form has coefficient at least \(\beta^{k+1}/2\) on every directed single-coordinate edge. The ordered-pair expansion of variance, followed by a path of at most \(k\) coordinate changes, gives coefficient at most \(k/2\) after bounding the total probability of pairs using an edge by one. Thus

\[
\operatorname{Var}_\mu f\le k\beta^{-k-1}\sum_x\mu(\operatorname{Var}_x f).
\]

Putting \(k=4\) gives \(c_0=\beta^5/4\). Integrating the cell inequality and summing over disjoint cells counts each physical site once. This proves the claimed normalization of `l:compare`.

**Uniform windows and the stopped coupling.** For integral radii, the inner neighbours of \(F_i\) have radius exactly \(\lfloor(i-1)s\rfloor\), hence lie in \(D_{i-1}\). The changed exterior site \(y\) cannot be such a neighbour when \(i\ge2\). The explicit threshold ensures \(s\ge16\), \(s/3>l_0\), the separation of shell radii, and the stated exceptional-index count. Reflections in this argument classify positions on the grid and do not identify probability laws at different sites.

Each surgery is a coupling of the two correct conditional resampling laws on a fixed exterior fibre; summing over that fibre preserves the two full-volume marginals. After coupling \(B_i\), resampling \(A_i\) leaves that agreement unchanged. A fixed assignment on \(A_i\) has probability at least \(\alpha^{|A_i|}\) in each independent resampling, even after all other letters are specified. Therefore agreement on \(D_i\), conditional on the complete previous history, has probability at least

\[
p_0\alpha^{2|A_i|}\ge p_0\alpha^{16l_0}=\delta.
\]

If the incoming separator already agrees, the identical-sampling branch succeeds with probability one. Among indices \(2,\ldots,h\), at most two trials lose an adjacent pair of unskipped steps, leaving at least \(h-3\) trials. Success at one of these trials forces identical resampling at the next step. The subsequent separators lie inside the region of agreement because \(\lfloor(j-1)s\rfloor>is\) for \(j\ge i+2\). Conditional failure bounds multiply without any independence assertion. The step \(h+1\) requires propagation only, so no window hypothesis beyond \(i\le s\) is used. The endpoint case \(\delta=1\) is harmless since all relevant exponents are positive.

**The box-gap constants and boundary blocks.** For \(u\in[n^8,2n^8]\), \(h=n\) is permitted because \(u^{1/4}\ge n^2\). The near region has at most \((4n^3+1)^2\le25n^6\) cells, and the square has at most \(25n^{16}\). With \(d\le\delta\), the actual stopped coupling therefore has Hamming cost at most the displayed \(K_n\).

For \(n\ge44\), every factor in the numerator of \(\binom{n-3}{20}\) is at least \(n-22\ge n/2\). Since \((1-d)^{-1}\ge1+d\), this proves the claimed finite binomial tail bound. The two numerical requirements give, respectively,

\[
25n^6\le n^8/2000,\qquad
\frac{25\,2^{20}20!}{d^{20}n^4}\le n^8/2000.
\]

Thus `e:nchoice` proves exactly \(K_n\le M/1000\), including its exponent twelve and coefficient 50000.

All update blocks are full squares contained in the rectangle, since \(2u+1\le4M+1\). Clamping is not truncation. For each side length the \(l\) nominal starts containing a given coordinate remain containing starts after clamping, proving \(T_x\ge4M^3\). The preimage estimates also allow coincident clamp endpoints. For \(S_x\), regular directed-side cases contribute at most \(16(M+1)L\); endpoint cases can occur at only one side length per directed side and contribute at most \(32L^2\). Their sum is at most \(960M^2\), so the stated 1000 is valid.

Choosing the same label for a pair of configurations differing at \(x\), the outside disagreement persists precisely when the block omits \(x\). The additional expected block disagreements are at most \(K_nS_x/A\). Hence

\[
T_x-K_nS_x\ge3M^3\ge M^3,
\]

and the asserted Hamming contraction follows. The product configuration space is connected by single-coordinate changes. A nonconstant real eigenfunction has positive Lipschitz seminorm, so the contraction bounds its eigenvalue. Self-adjointness follows from conditional expectation; this argument does not require an invariant spatial pattern. It gives the gap \(M^3\) for the **unnormalized** block generator, not for the averaged transition kernel.

Every block has at most \(v=(4M+1)^2\) cell sites, so its conditional single-cell gap is at least \(g=\alpha^{v+1}/v\). The block-to-site comparison incurs multiplicity at most \(1000M^3\). Cancelling \(M^3\) gives \(g/1000\), exactly `e:cellconstants`. All thresholds are chosen from positive common parameters and are finite. The argument is uniform over the whole family of potentials because every probabilistic estimate was imposed or proved at each actual translate.

**Closing the finite-size argument.** With `e:ellchoice`, every lifted conditional \(\ell\)-box is a \(t\times t\) cell box meeting the rectangle threshold. Therefore

\[
g(\ell)\ge c_0m_0,\qquad
\frac1\ell\le\frac{c_0m_0}{2},\qquad
\lambda(\mu^{\rm af})\ge\frac{c_0m_0}{2}.
\]

The quantum factor \(g_\star/2\) gives \(c=g_\star c_0m_0/4\). None of the invoked results needs \(L,N\ge\ell+2\); \(\ell+1\) is sufficient because `l:boxcell` handles its repeated pins. The evenness of the auxiliary \(\ell\) only permits the selected cell partition. It restricts neither period nor the parity of the number of cells.

**Different frames, partition functions and the cut ratio.** With distinct endpoints, each factor has degree at most one in a given spin, and at most four factors involve it. A different four-design can thus be summed at each successive variable. Other sums or integrations do not raise its degree. A self-factor, if allowed by the general wording, is constant on the sphere and can be removed first. This proves `l:exact` without equal frame cardinalities or rotational alignment assumptions.

For a fixed window configuration, summing only the complement gives `e:windowlaw`. In the cut domain the pins are those on the **original** legs of \(G\); no factor is inserted on a newly exposed leg into \(X\). This is why the factorization into a window-side and an exterior-side partition function is exact. Its window weight \(W_B(s)\) remains the actual frame weight and is not replaced by a continuous marginal. The reference law \(\nu\) may depend on the frames but is the same for the two boundary conditions being compared.

The continuous normalizers are positive for arbitrary unit pins: finitely many forbidden antipodes cannot exhaust the sphere, and a small product neighbourhood of a common permitted direction has positive integrand and positive product measure. The actual discrete window weights are positive by cross-frame separation. The empty-domain normalizer is one. These facts justify every logarithm, normalization and density ratio.

Normalization of \(c(\eta)\nu(s)e^{-e(\eta,s)}\) gives \(e^{-\epsilon}\le c(\eta)\le e^\epsilon\), hence the two-sided density estimate. The two window laws have likelihood ratios bounded by \(\rho=e^{4\epsilon}\) in both directions. Maximizing the resulting bound \(\min\{(\rho-1)x,(\rho-1)(1-x)/\rho\}\) yields \((\rho-1)/(\rho+1)=\tanh(2\epsilon)\). No comparison between different window sample spaces is made.

**Cut geometry, removal costs and window constants.** I checked the retained proofs of `l:cutgeom`, `l:Xconn` and the boundary-connectivity lemma, including the inward-depth exclusion of coincident square sides. Their assertions are geometric and remain true for every cell origin and translate. The radial-path argument makes \(U'\) nonempty, its complement is connected, and the excluded diagonal block configuration supplies the required nearest-neighbour connectivity of \(X=\partial_\infty U'\). The buffer places every cut site in \(G\setminus S(G)\), with \(b_G(x)\ge3\).

The conversion from cell separation to physical separation is \(2r-1\) in the infinity metric, followed by graph distance at least infinity distance. With \(l_0=20\), the retained short-ring bound is \(b_G(x)\ge2\max(j,5)-5\), at most 48 cells or 192 physical sites per ring parameter. Substitution gives exactly the first term of `e:cutsum`. The long-part estimate is used with the weaker, hence safe, exponent \(s/6-7\).

Order the connected nonempty cut by a spanning tree. The first removal has four neighbours; every later removal has at most three surviving neighbours. Each removed set is contained in the interior of the original \(G\), so (P) applies to all surviving distance-two neighbour pairs. Their distance to \(S(G)\) is at least \(b_G(x)-3\), explaining \(\theta^{-3}\).

The conditional-mean estimate gives the first integral lower bound

\[
1-\frac46\frac9{25}-\frac3{15}\left(\frac9{25}\right)^2
=\frac{2294}{3125}=0.73408\ge0.734.
\]

The later lower bound is \(0.82\). The exact rational comparisons

\[
1/0.82\le1.22,\qquad 2/0.734\le2.73,
\qquad (0.7776/15)/0.734\le0.0707
\]

verify all three removal constants. The last term bounds the first four-spin response; it occurs once and is retained in the replacement. Bounding the first pair contribution by \(2.73A\) and adding the first site to the remaining nonnegative sum only enlarges the bound. Thus `e:epsilon` is valid.

For fixed \(0<\theta<1\), \(4(2u+1)^2\theta^{u^{1/4}/6-7}\) tends to zero for all real \(u\to\infty\). A single integer threshold makes it at most one for every later integer \(u\), as well as meeting the fixed geometric thresholds. This proves the stated \(\epsilon_{\max}\) and

\[
1-p_0=\frac{e^{4\epsilon_{\max}}-1}{e^{4\epsilon_{\max}}+1}
=\tanh(2\epsilon_{\max}).
\]

No finite-energy claim for arbitrary continuous pins is used here. Independence of \(p_0,M_\star\) from alphabet cardinality is justified by the partition-function argument; it does not assert that the later finite-energy constant or final gap is independent of cardinality for arbitrary new frame families.

**Retained inputs and compatibility with the rest of the manuscript.** The corrected Section 6 definitions include the covering-tip and missing-slot rules, scalar trace masses, preserved original boundary legs, the initial two-bond \(\mathrm D\) bound \(3/4\), the later \(\mathrm D\) value \(3/5\), the exposure restriction, and a common majorant for the maximum of pinned/free ratios. The nonreversing initial-arrival convention and missing initial bond used in (H2) are retained. The corrected closure lemma distinguishes the live endpoint, the terminal boundary defect and the underlying mass-one consistent domains. These are the interfaces described by the replacement text.

All suprema and local inequalities in that recursion concern finite **plane** domains and arbitrary unit pins. New frame-valued pins, even when tied by torus images before lifting, are special cases of those inputs. The auxiliary quotient in the tail argument remains a device for bounding plane trails. Even trail length between distance-two endpoints, the mod-two boundary argument, and total-spin weight parity do not impose a condition on physical torus periods. No certificate is evaluated on an inhomogeneous finite-state model.

The old corollary's claim on arbitrary compatible unions is not reproved, and the replacement explicitly removes it. This causes no loss in the proof uses: the main theorem only needs large square box gaps, now supplied by the stronger-in-size rectangle conclusion. The revised `t:mainW` removes the compatible-set divisibility argument and its offset constants. The remaining continuous sections do not use those constants or the deleted mixing theorems. The generic statement of `t:K` remains available with its weighted version, and the original `p:surgery` conclusion is still implied.

The final order of choices is acyclic: retained continuous inputs supply \(A,\theta\); the explicit frames supply \(b,\beta,\alpha,c_0\); the cut supplies \(p_0,M_\star\); then choose \(n,M,L_{\rm cell},m_0,t,\ell,L_0,c\). All are chosen before torus periods, a torus colouring, any box placement, or its exterior configuration. The original star constant and continuous removal/response/kernel constants remain applicable. The small-period uniqueness statement uses the simple four-regular graph ground-space computation, independently of this choice of scales; this argument does not assert a uniform gap for all thin tori.

**Exact computations**

The independent, single-process checker [audit_exact.py](/home/ubuntu/aklt/reports/REF-SA-B/audit_exact.py) uses the Python standard library, integers, fractions and exact arithmetic in \(\mathbb Q(\sqrt5)\). It was run with `OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 python3 audit_exact.py`. All checks passed; full counts and source hashes are in [audit_results.json](/home/ubuntu/aklt/reports/REF-SA-B/audit_results.json).

- Checked all 56 monomials of total degree at most five for the base design and all 144 cross-frame vertex pairs for each of the three frame pairs. Their minimum bond weight is the stated \(b=(5-\sqrt5)/505\); antipodality covers either sign. Rotation transfers design exactness to the other frames.
- Checked 1,872 circular autocorrelations for flat and parabolic weights, \(2\le\ell\le40\), and every period from \(\ell+1\) through \(2\ell+3\). Also checked both weighted constant identities for all these \(\ell\).
- Checked 1,944 translated box lifts for \(\ell=2,4,6,8\) and independently chosen periods \(\ell+1,\ell+2,\ell+3\). Compared internal and boundary **bond multisets**, checked proper lifted colours and all edge gauge signs, and checked that every lifted exterior neighbour maps outside the box. There were 964 cases with repeated exterior images, all with opposite-sign repeated pins. This includes \((L,N)=(3,3)\).
- Checked the clamped-square counts at every site of the sampled rectangles: 187,496 cases with \(1\le M\le8\), each side chosen independently from \(L,L+1,L+2,2L,2L+3\), \(L=4M+1\). All three inequalities passed, including \(N_j=L\).
- Checked the removal decimals as rational upper bounds and 628 rational instances of the finite binomial tail inequality for \(44\le n\le200\).
- Checked 60 nonexceptional cut configurations, with \(u=132^4-1,132^4,132^4+1\), shell indices 2, 3, 4, and positions at a side midpoint, outside a corner, and around the exact exceptional-distance threshold. Thirty-nine have noninteger fourth roots. Checked \(|I_0|\le1\), nonempty star connectivity of \(U\), absence of diagonal-only cell blocks, nearest-neighbour connectivity of the physical \(X\), its actual graph distance to the complement of \(G\), and the short-ring counts and depth bounds. Twelve exceptional shells were correctly excluded.

These are finite adversarial checks, not substitutes for the universal geometric and probabilistic proofs above. In particular, no exhaustive numerical test over all colourings or all boundary spin assignments is claimed.

**Formalization notes**

- Use a dependent finite product \(\prod_xS_x\), with a positive probability on every configuration. Conditional expectations can then be defined on every exterior fibre without null-event choices. A specification must include consistency under conditioning and the stated range-one Markov property; arbitrary unrelated positive volume laws would not suffice.
- Keep torus edges as unordered pairs in a simple edge set. For the lift, prove bijections for internal bonds and for boundary bonds separately; do not require injectivity on the exterior vertex set. Distinct exterior plane sites are separate pin arguments even when their torus images coincide. Treat the gauge as a product of coordinate bijections, then prove conditional-kernel intertwining.
- Distinguish physical graph distance \(d\), physical infinity distance, and cell infinity distance. Distances in (P) are ambient plane graph distances to the original \(S(G)\), not distances to a set enlarged by removed sites. New boundary edges into removed sites carry no pins.
- Integer shell comparisons need no approximate fourth root: \(\lfloor i u^{1/4}\rfloor\) is the integer fourth root of \(i^4u\), and \(r<s/3\) is equivalent to \((3r)^4<u\) for nonnegative integral \(r\). Preserve strict versus weak inequalities at the exceptional-shell threshold.
- Construct the surgery kernels on finite sets explicitly. At each trial use a maximal coupling of the two marginals, their finite conditional completions, and independent conditional resamplings on \(A_i\). The history-dependent selection preserves each prescribed marginal because its marginal kernel is the corresponding conditional resampling kernel. Only conditional failure estimates are multiplied.
- Retain block labels with multiplicities and distinguish the averaged operator \(P\) from \(A(I-P)\). The Lipschitz seminorm argument is finite-dimensional, works on different alphabets at different sites, and gives a spectral bound using self-adjointness. If every alphabet is a singleton, its Poincaré assertion is automatic, as in MOSPROOF.
- Quadrature is a statement about separately bounded polynomial degree, not about equality of Gibbs marginals on different frame alphabets. Positivity of the continuous partition functions and actual window weights must be established before taking logarithms and density ratios.
- Interpret terminating decimals in removal and response estimates as exact rationals. Define \(p_0\) by its exact exponential expression: floating-point underflow is not a mathematical zero. The very large scales and tiny gap constants remain finite and positive; numerical evaluation of their decimal expansions is unnecessary.
- A formal proof of the extension may take the corrected continuous implication `(H1), (H2), (H3′) => (P)` and its certificate trust assumptions as retained inputs. It must not infer spatial invariance of the new frame specification from invariance of the continuous integrals. The all-translates quantifier in `d:W` is the precise replacement for that invariance.
