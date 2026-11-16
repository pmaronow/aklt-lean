VERDICT: SOUND WITH FIXES

# Lane R7: integration referee report

I read all LaTeX sources in the frozen bundle and checked the interfaces in the proof of Theorem 1.1. The principal implications match after the local range and presentation corrections below. I found no Critical or Major integration defect and no circular choice of constants. In particular, the passage from the two cell models to boxes at every placement, and then to all sufficiently large even rectangular tori, is correctly handled.

This is an integration verdict: it takes the section-local analytic and computer-assisted results at their stated strength, rather than recertifying their proofs or rerunning the large computations. I inspected relevant program definitions and certificate parameters to check their interfaces. The cited MOS94, MO94 and DGS77 source texts are not in the bundle; their original statements and the claimed finite-spin extension of MO94 were not independently source-verified. The external-input assessment below distinguishes that limitation from checking the applications against the statements supplied by the manuscript. No files outside the bundle and this report directory were read, and no web searches or subagents were used.

## 1. Findings

### 1. Minor — the closure lemma includes a terminal case in which its conclusion is false

**Location:** `sec7-recursion.tex:17`, Lemma 7.1 (`l:closure`), especially lines 18–24; compare `sec6-walks.tex:10`, Definition 6.1 (`d:domain`), and `sec7-recursion.tex:80`, the use of a terminal traced domain in Theorem 7.4 (`t:rec`).

**Exact claim:** A trail is allowed to visit $S\cup\{v\}$ at its last site, and the conclusions, including “the domain $E'_{j+1}$ obtained from $D_j$ by removing $v_j$ belongs to $\mathcal D_{\rm cons}(G)$,” are asserted “for every $j$.” Definition 6.1 requires every site of $S$ to have status U and keep all its bonds.

**Failure:** Take $G=\{-4,\ldots,4\}^2$, remove $c=(0,0)$, and take the collinear pair $u=(-1,0),v=(1,0)$. The initial domain $D=G\setminus\{c\}$ is consistent. The trail

\[
w=((-1,0),(-2,0),(-3,0))
\]

has no earlier visit to $S\cup\{v\}$, and its last site $e=(-3,0)$ belongs to $S$. At its last prefix, removing $v_j=e$ removes a protected site, so $E'_{j+1}\notin\mathcal D_{\rm cons}(G)$. Moreover, the rule in Section 6 that drops an arrival bond at both ends produces an endpoint that fails the “keeps all its bonds” condition on $S$. These are literal counterexamples to the universal range, not counterexamples to decay or to the main theorem.

**Repair:** Assert the ordinary closure conclusions for prefixes whose live endpoint is outside $S$, and separately state the terminal-boundary case: the trace can have a marked endpoint $e\in S$ with its arrival bond dropped, but it is never departed from. Extend the partition-function notation to these marked terminal traces. The proof of the $T_2$ bound already identifies this single defect and permits at most twelve exceptional first-visit templates in the second expansion. State explicitly that Proposition 6.3 and Lemma 6.11 apply to this terminal-trace class. No new quantitative estimate is needed: departures remain outside $S$, the leg factors are unchanged, and the existing twelve-exception argument is exactly the needed extension. The counterexample above was also checked by a small exact finite-set computation.

### 2. Minor — Section 1 omits terms that are retained in the actual reductions

**Location:** `sec1-intro-statement.tex:30` and `:32`, overview of `l:removal`, `p:pairwalk` and `t:rec`.

**Exact claims:** (i) “$\varepsilon$ is bounded by a sum over the cut of pair-correlation responses”; (ii) “A pair correlation is a sum over trails from one site of the pair to the other.”

**Mismatch:** The actual cut-removal bound, `sec5-cut.tex:104`, has an additional $0.0707$, arising from the four-point term at the first removal; it is not solely a sum of pair responses. The actual walk identity, `sec6-walks.tex:40`–44, stops at $S\cup\{v\}$, not just at $v$. The proof in `sec7-recursion.tex:68`–82 separates the trails ending at $v$ from trails ending at $S$, and the latter contribute the indispensable error $C_Tq^{2d}$. Thus Section 1 describes stronger exact identities than the paper uses.

**Repair:** Say that the cut cost is bounded by a fixed additive constant plus a sum of pair responses. Say that the walk expansion stops either at the other endpoint or at the protected boundary layer; the first class gives the closed-trail kernel and the second gives an exponentially decaying error. The abstract and Theorem 1.1 need no change to their size, parity or gap claims.

### 3. Minor — the global unit-spin convention excludes auxiliary spins used by the recursion

**Location:** `sec1-intro-statement.tex:44`, Conventions; `sec6-walks.tex:10`, Definition 6.1 (`d:domain`).

**Exact claim:** “All spin configurations are of unit vectors.”

**Failure:** A D site has measure $(3/5)\,dn+(2/5)\delta_0$; its spin can be zero. The recursion and localization correctly use the bound $|n|\le1$, including this atom. A literal global unit-vector type is incompatible with those definitions.

**Repair:** Restrict the convention to physical frame spins, ordinary continuous spins and pins, and explicitly allow auxiliary traced spins in $\mathbb S^2\cup\{0\}$. Preserve unit pins throughout. This is a type correction, with no changed estimate.

### 4. Minor — the explanation of noncircularity asserts an incorrect absence of dependencies

**Location:** `sec4-mixing-to-gap.tex:138`, after the proof of Theorem 1.1.

**Exact claim:** The proofs of Sections 5–8 “do not use §§2–4.”

**Failure:** Lemma 5.2 uses the frame definition from Section 2. The cut construction uses the cells, shells and exceptional index set from Section 4; in particular, `sec5-cut.tex:179` invokes Lemma 4.6 (`l:shellgeom`) explicitly. The lower sections therefore do use earlier material.

**Repair:** Replace this with the more precise, true assertion that Sections 5–8 do not use the main theorem, the conclusion of Theorem 4.10, or the consequences of the window estimate. Their dependencies on earlier frame definitions and shell geometry are acyclic. The actual constant order is valid; see Section 3 below.

### 5. Minor — the promise of precise locators has an exception at a necessary frame input

**Location:** `sec1-intro-statement.tex:18`; `sec2-frames-Q.tex:63`, preceding (`e:icodod`).

**Exact claims:** “Everything else is proved here or cited with a precise locator,” whereas the necessary spherical-design fact is supported only by “see [DGS77]” and a numerical moment check.

**Issue:** No theorem, example, table or page locator is given for the assertion that both vertex sets are spherical 5-designs. Exactness through degree four is an essential input to both the quantum-frame isometry and the transfer of partition functions. A numerical moment check does not establish that input exactly.

**Repair:** Add a precise DGS77 locator for these two designs, or supply an exact coordinate/moment verification through degree four. Alternatively qualify the blanket locator promise, while retaining an exact justification of the design fact. This finding concerns documentation of a standard input; I do not claim the design assertion is false.

## 2. Statement table

The tables include every numbered theorem-style statement, definition, hypothesis and remark, so that supporting interface statements are not silently omitted. “Correct” means that its exported statement has the required scope and is used consistently in this integration audit; it is not a second certification of a section-local proof. Unlabelled Remark 6.9 is identified by its source line. The external results are assessed on the basis described at the start of this report.

### Sections 1–4

| Statement / label | One-line content | Verdict | Dependencies and interface assessment |
|---|---|---|---|
| Theorem 1.1 `t:main` | Uniform positive quantum gap and unique ground state on sufficiently large even tori. | correct after fix | `t:inputs` → `t:rec` → `h:P` → `t:cutMOS` → `t:mainW`; Finding 1 requires the corrected terminal-trace formulation. |
| Lemma 2.1 `l:edge` | A bond constraint is equivalent to divisibility by its singlet polynomial. | correct | Clebsch–Gordan rule; exports the exact degree-three quotient used by `l:divisibility`. |
| Lemma 2.2 `l:divisibility` | Star constraints force the product of incident bond factors. | correct | `l:edge`, polynomial UFD, simple 4-regular graph; even tori of sides at least four satisfy these hypotheses. |
| Definition 2.3 `d:frame` | A frame is a positive weighted spherical 4-design. | correct | Exact quadrature, not numerical approximate quadrature. |
| Lemma 2.4 `l:tight` | Degree-four coherent-state evaluations give an isometry. | correct | `d:frame`, `e:zeta`, `e:Vinner`; product isometries are available. |
| Theorem 2.5 `t:QD` | Uniqueness and $\operatorname{gap}H\ge(g_\star/2)\lambda(\mu^\circ)$. | correct | `l:divisibility`, `l:tight`, strictly positive checkerboard bond weights, finite star gap; assumes even $L,N\ge4$, satisfied later. |
| Remark 2.6 `r:QDgeneral` | The comparison extends to simple 4-regular graphs when frame evaluations do not vanish. | correct | Same divisibility and positivity inputs; no extension is needed for Theorem 1.1. |
| Theorem 3.1 `t:K` | Flat and weighted box-gap criteria on $L,N\ge\ell+1$. | correct | Positive nearest-neighbour finite-state field, `l:commute`, `l:fibre`, `l:autocorr`; only the flat criterion is used. |
| Lemma 3.2 `l:commute` | Non-neighbouring heat-bath projections commute. | correct | Strictly positive nearest-neighbour factorization `e:MRF`; holds for the frame field. |
| Lemma 3.3 `l:fibre` | Each box operator has nonzero spectrum bounded by $g(\ell)$. | correct | Conditional fibres and minimum over all actual torus exterior configurations. |
| Lemma 3.4 `l:autocorr` | Periodic autocorrelation bounds for symmetric unimodal weights. | correct | $L\ge\ell+1$; both weights used by `t:K` meet its hypotheses. |
| Remark 3.5 `r:Kpins` | Correlated opposite-side pins on a very narrow exterior are covered by arbitrary box boundary conditions. | correct | `e:gell`, Markov property; final even sizes actually have at least two exterior columns/rows. |
| Lemma 4.1 `l:boxcell` | Every even-side torus box is a square of one of the two cell models with an exterior condition. | correct | `e:muD`, `e:muDW`, parity-preserving translations, $\ell\le\min(L,N)-1$; arbitrary cell exteriors can realize the required box boundary data. |
| Lemma 4.2 `l:compare` | Single-site gap is at least $c_0$ times cell gap, uniformly in boundary conditions. | correct | Finitely many strictly positive four-site chains and conditional Poincaré inequalities; rate one per site and per cell as defined. |
| Theorem 4.3 `t:MOS21` | One sufficiently accurate large-square estimate implies strong mixing on all squares. | correct | MOS94 Theorem 2.1 as restated; translation-invariant finite-state real finite-range potential after blocking. |
| Theorem 4.4 `t:MO41` | Strong mixing at a sufficiently large scale gives a uniform gap on compatible unions. | correct | MO94 Theorem 4.1 with the finite-spin extension explained in `r:finiteS`; no attractivity is claimed for the cell model. |
| Remark 4.5 `r:finiteS` | Explains using MO94 with 57,600 cell states. | correct | The extension is explicitly disclosed; cited MOS94 general-finite-$S$ setting and the proof ingredients listed there. Source verification limitation noted above. |
| Lemma 4.6 `l:shellgeom` | At most one exceptional shell and bounded boundary segment $A_i$. | correct | Fixed $l_0$, sufficiently large $M$, $2\le i\le\lfloor s\rfloor+1$; supplies exactly the geometric input used in Section 5. |
| Definition 4.7 `d:W` | Uniform window TV bound below one for all exteriors and all required shells. | correct | Fixed $l_0,p_0,M_\star$, $2\le i\le s$, $i\notin I_0$; Section 5 supplies this full quantifier range. |
| Proposition 4.8 `p:surgery` | A one-site exterior change has exponentially small influence beyond distance $M^{1/2}$. | correct | `d:W`, `l:shellgeom`, finite energy $\alpha$, DLR and finite maximal couplings; success estimates are needed only at indices $i\le s$. |
| Corollary 4.9 `c:gapcell` | Both cell offsets have uniform gaps on their compatible sets. | correct | `p:surgery`, triangle inequality over (8M+8) cells, `t:MOS21`, `t:MO41`; take the minimum of the two positive gaps. |
| Theorem 4.10 `t:mainW` | Window estimates for both offsets imply the main quantum result. | correct | `c:gapcell`, `l:boxcell`, `l:compare`, flat `t:K`, `e:QDrot`; common multiple $K$ handles the two compatible scales. |

### Sections 5–8

| Statement / label | One-line content | Verdict | Dependencies and interface assessment |
|---|---|---|---|
| Lemma 5.1 `l:35` | A site with at most three factors has conditional mean norm at most $3/5$. | correct | Uniform sphere moments; used only at sites with no more than three relevant factors, including the stated mixture extension in Section 6. |
| Lemma 5.2 `l:exact` | Frame sums and sphere integrals agree for products of degree at most four at each site. | correct | `d:frame`, finite Fubini; applies to window partition functions, without inserting a pair observable. |
| Lemma 5.3 `l:cut` | A uniformly bounded cut cost gives window density ratios and TV at most $\tanh(2\varepsilon)$. | correct | Positive partition functions, `l:exact`, no exterior neighbour of the window, separation into $G_1,G_2$; all supplied by `l:cutgeom`. |
| Hypothesis 5.4 `h:P` | Uniform pinned/free pair-response decay for arbitrary interior removed sets. | correct | Independent unit pins on original legs; the removed set is not part of the distance boundary. This is the version deduced from `e:FX`. |
| Lemma 5.5 `l:removal` | Connected ordered removal has bounded cost from (P), with one fixed four-point allowance. | correct | `h:P`, `l:35`, free positivity; $b(x_j)\ge3$ and earlier-neighbour ordering are supplied by the cut lemmas. |
| Lemma 5.6 `l:cutgeom` | The tapered cut separates the window and has controlled weighted distance sum. | correct | Cells/shells from Section 4, `l:shellgeom`, even $l_0\ge20$, sufficiently large $s$; both offsets are covered. |
| Lemma 5.7 `l:Xconn` | The cut is nearest-neighbour connected. | correct | `l:cutgeom`, `l:boundaryconn`; gives the required ordering for `l:removal`. |
| Theorem 5.8 `t:cutMOS` | (P) gives the window estimate for both cell offsets, with $l_0=20$. | correct | `l:removal`, `l:cutgeom`, `l:Xconn`, `l:cut`; only a finite uniform cost, not a small cost, is required. |
| Remark 5.9 `r:Pweak` | Summable responses with an appropriate polynomial bound can replace exponential responses. | correct | Requires the indicated finer long-side count; the crude count requires the stronger stated decay. Not used in the main chain. |
| Definition 6.1 `d:domain` | U/D/X domains, diluted site measure, and the consistent subclass. | correct after fix | Finding 1: distinguish ordinary domains from marked terminal traces. Finding 3 corrects the introductory convention. |
| Lemma 6.2 `l:stepid` | Exact integration identities for departure and revisit steps. | correct | Sphere moments and the stated diluted measure; $k\le4$ or $k\le2$ respectively. |
| Proposition 6.3 `p:pairwalk` | Pair expansion over trails stopped at $S\cup\{v\}$. | correct after fix | `l:stepid`, trace mass convention; include the marked terminal traces of Finding 1. In the recursion $v$ is U or D with at most one bond, so its terminal factor is boundary-condition independent. |
| Lemma 6.4 `l:response` | Log step-ratio response is a bounded positive combination of neighbour-pair responses. | correct | `l:35`, free positivity, non-adjacency; $y\notin S$ keeps its neighbours free of original legs. Constants match the certified kernel. |
| Lemma 6.5 `l:exposure` | Product differences telescope in any fixed ordering of first visits. | correct | `l:response`, $x_j\ge1$; permits exactly the orderings used in Appendix C. |
| Definition 6.6 `d:pattern` | Radius-two templates and the consistent covered pattern class. | correct | Kept-bond consistency, unit slots, U tips; relevant ordinary trace templates are covered by corrected `l:closure`. |
| Hypothesis 6.7 `h:H1` | Straight/turn template ratios are at least $c_s,c_t$. | correct | Exact ratio with positive denominator; `t:H1` supplies (961/1000,187/200). |
| Lemma 6.8 `l:local` | A covered template bounds the inverse departure ratio. | correct | `d:pattern`, `l:35`, linear-fractional localization; used only when the template has the required form. |
| Remark 6.9, `sec6-walks.tex:129` | Closure supplies covered patterns except boundedly many terminal-defect exceptions. | correct after fix | `l:closure`, `l:response`; clarify the terminal-trace class as in Finding 1. |
| Hypothesis 6.10 `h:H2` | All weighted lattice-trail sums decay uniformly in length, start and arrival direction. | correct | Weights $x_s/3,x_t/3,1/5$; `l:alm` supplies a dominating finite-memory estimate. |
| Lemma 6.11 `l:onepoint` | Boundary-hitting trail mass is at most a constant times $q^{d(x,S)}$. | correct after fix | `h:H1`, `h:H2`, `l:local`, `l:response`; make its permitted terminal traces explicit as in Finding 1. Twelve exceptions only enlarge the prefactor. |
| Lemma 7.1 `l:closure` | Trace closure and closure of response pairs. | correct after fix | Finding 1 supplies the missing prefix restriction and terminal case; initial interior removal domains belong to the consistent class. |
| Hypothesis 7.2 `h:H3` | For fixed trail orderings, $\rho(M_1)<1$. | correct | Same $c_s,c_t,\bar\alpha,\bar\beta$ as the analytic recursion; orderings are existential and fixed before choosing $\theta$. |
| Lemma 7.3 `l:Mtheta` | An exponentially weighted kernel remains finite and contracting for some $q^2<\theta<1$. | correct | `h:H2`, `h:H3`, shift bound $s\le n/2+1$, continuity; the chosen Appendix C orderings do not depend on $\theta$. |
| Theorem 7.4 `t:rec` | The two response envelopes decay exponentially and imply (P). | correct after fix | Corrected `l:closure`, `p:pairwalk`, `l:response`, `l:exposure`, `l:onepoint`, `l:Mtheta`; includes the $C_Tq^{2d}$ error. |
| Remark 7.5 `r:typedep` | Sharper coefficients can be obtained from (H1). | correct | Refinement of `l:response`; explicitly unused by the main proof and its stated $0.98779$ input. |
| Theorem 8.1 `t:inputs` | The three hypotheses hold at the common pair ((0.961,0.935)). | correct | `t:H1`, `l:alm` and Section 8.1 certificate, `p:tail`/`l:CW`; the quantitative outputs are strictly below one. |
| Lemma 8.2 `l:alm` | A finite-memory positive-vector bound implies full trail growth decay. | correct | True revisit weight $1/5\le1/4$ in the certificate; arbitrary positive test vector; initial lengths absorbed into $C_V$. |
| Theorem 8.3 `t:H1` | Every covered pattern obeys the two exact local inequalities. | correct | `p:certificate`, `c:reduce`, `l:Iw`, enumeration/certificates in Appendix D; optional closed-form certificates are additional, not needed for coverage. |
| Remark 8.4 `r:H1sharp` | The local constants have small margins and a concrete upper obstruction. | correct | `p:closed`, `e:5469`, Table 8.1; no stronger constants enter the main chain. |

### Appendices

Appendix A has a constants table, not numbered theorem-style statements. Its entries agree with the main proof. The two minima recorded there are not substituted for the conservative certified constants.

| Statement / label | One-line content | Verdict | Dependencies and interface assessment |
|---|---|---|---|
| Lemma B.1 `l:boundaryconn` | A finite nonempty set with the specified connectivity and no diagonal-only block has connected outer boundary. | correct | Proof supplied; `l:Xconn` supplies all three hypotheses, and even proves ordinary connectivity of the complement. |
| Lemma C.1 `l:CW` | Positive-vector row quotients upper-bound a nonnegative matrix's spectral radius. | correct | Finite nonnegative matrix and strictly positive vector; the same $h$ must be used throughout each kernel bound. |
| Lemma C.2 `l:memdom` | Modes A/B dominate closed trails in their respective length ranges. | correct | Straights-first order, quotient minimum period $P=56$, exact initial history; mode A only through 107 and mode B above 53. |
| Lemma C.3 `l:remainder` | A positive left sub-invariant vector bounds the remaining point-to-point mass. | correct | $t_*<T$, $0<\lambda<1$, verified $z\mathbb W\le\lambda z$, and uniform $V_T\le az$; the stated $53<260$ satisfies the range. |
| Proposition C.4 `p:tail` | Certified row bounds imply the advertised kernel spectral-radius bound. | correct | `l:memdom`, `l:remainder`, `l:CW`, fixed short/long orderings and directed-rounding computations; even-length split has no omitted range. |
| Remark C.5 `r:tailtypedep` | An unused refined-coefficient computation gives a smaller bound. | correct | `r:typedep`, variant program; no main conclusion relies on its less extensively checked variant. |
| Lemma D.1 `l:Iw` | Integrating the passage site gives (I,J), positive denominator and multi-affinity. | correct | `d:pattern`, sphere moments; supplies denominator positivity for `t:H1` → `h:H1`. |
| Lemma D.2 `l:leaf` | Tips and leaf corners can be replaced by fields with exact radius bounds. | correct | `l:35`, moments, and the stated U/D site measure. |
| Corollary D.3 `c:reduce` | Nonnegativity on reduced unit vectors proves the original slot inequality. | correct | `l:leaf`, positive common factors, separate affinity and convexity; balls need not be transferred as extra hypotheses to (H1). |
| Lemma D.4 `l:inversion` | A positive coherent-state operator certifies the corresponding multi-affine polynomial. | correct | `e:zeta`, Pauli expectation identity; inversion sets affect success, not validity. |
| Lemma D.5 `l:Ostruct` | The operator is real, rotation invariant and has the required pair-sector structure. | correct | Orthogonal invariance and U/D measures; D pairs are split into both symmetry sectors rather than discarding the atom at zero. |
| Lemma D.6 `l:sector` | Testing the central spin-component sector detects every eigenvalue. | correct | Finite SU(2) representation decomposition; parity is determined by the number of single-vector factors. |
| Proposition D.7 `p:certificate` | Positive definiteness on every required sector proves each original inequality. | correct | `l:Ostruct`, `l:sector`, `l:inversion`, `c:reduce`; zero complementary U-pair sectors only require semidefiniteness of the whole operator. |
| Lemma D.8 `l:radius` | The aligned-field value bounds a U/D spin mean. | correct | `l:35`, `l:leaf`, FKG on a finite subset lattice with checked lattice condition; used only for the supplementary closed-form proof. |
| Proposition D.9 `p:closed` | Decoupled pattern ratios reduce to a one-variable exact minimization. | correct | `l:radius`, `l:Iw`, pruning and independent branches; not used to replace the operator proof for non-decoupled patterns. |

### Numbered equations that carry cross-section interfaces

| Label | Interface conclusion |
|---|---|
| `e:Zpin`, `e:ZD` | The original legs of $G$ carry pins; bonds into removed sites do not acquire new pins. The U/X restriction agrees exactly. |
| `e:muD`, `e:muDW`, `e:MRF` | The rotated checkerboard model is a strictly positive nearest-neighbour finite-state field. |
| `e:QDrot` | Sitewise sign rotation preserves conditional expectations and the heat-bath gap. |
| `e:gell`, `e:K` | A minimum over all actual conditional boxes is bounded by the uniform arbitrary-exterior estimate; use the first inequality only. |
| `e:SM`, `e:MOS22`, `e:W`, `e:prop21` | The all-exterior window bound yields the one-site influence bound, then the many-site TV estimate required by MOS94. |
| `e:cutcost`, `e:cutratio`, `e:windowlaw` | Window probabilities use exact partition functions; a common boundary-independent reference law yields the TV estimate with the stated factors of two. |
| `e:P`, `e:FX` | Every pair required by (P) is among the B/C envelopes, with the same protected layer and graph distance. |
| `e:cpi`, `e:IJ`, `e:IcJ` | Local certified ratios have the inverse orientation needed for the upper bounds on departure factors. |
| `e:kernel`, `e:mT` | The scalar tail sums are $(M_1h)_X$, not individual matrix entries; division by $h_X$ is necessary and is performed. |
| `e:recineq` | The kernel term is supplemented by $C_Tq^{2d}$; it is not a homogeneous contraction without an error. |
| `e:cutsum`, `e:removal` | The cut distance is measured in sites, while shells are in cells; the factors of two and the three-layer loss are explicitly present. |
| `e:Meps`, `e:intscale` | The certificates test positive integer multiples of congruence matrices for the exact rational thresholds. |

## 3. Formalization notes and explicit interface checks

### Dependency and constant order

There is a valid acyclic order, despite the inaccurate sentence identified in Finding 4:

1. Fix the two frames, their positive local weights, and the finite star operator. This fixes positive $g_\star,c_0,\alpha$ independently of all large scales.
2. Fix $c_s=961/1000,c_t=187/200$, hence $x_s=1/c_s,x_t=1/c_t\ge1$. Fix $\bar\alpha=0.18094,\bar\beta=0.36751$. These are the same numbers in the recursion and the main tail computation.
3. Obtain (H1), (H2) with some finite $C_V$ and $0<q\le0.98075$, and (H3') for one fixed family of trail orderings. The closed-form refinement and the type-dependent kernel are not inputs to the main chain. In particular, an ordering optimized at $\theta=1$ is then held fixed; it is not reoptimized as $\theta$ varies.
4. Choose $q^2<\theta<1$ with $\rho(M_\theta)<1$, then $\rho(M_\theta)<\rho''<1$, a positive vector $\mathsf x$, and $A\ge2$ from the fixed-point bound. The $A$ actually displayed in Theorem 7.4 is at least two, as required by (P).
5. Set $l_0=20$. Enlarge the geometric threshold and $M_\star$ so the residual $4(2M+1)^2\theta^{M^{1/4}/6-7}$ is bounded, for example by one. This fixes a finite $\varepsilon_{\max}$ and a positive $p_0=1-\tanh(2\varepsilon_{\max})$, uniformly for both offsets and all pins.
6. Set $\delta=p_0\alpha^{320}>0$. Choose a sufficiently large integer $M$ so that it meets the window/geometric/MOS thresholds and $(8M+8)(1-\delta)^{M^{1/4}-4}\le M^{-4}$. Only existence is needed; an extremely small $\delta$ does not invalidate this step.
7. Apply MOS94 separately to the two fixed cell models, obtaining $C^{(o)},\gamma^{(o)}$. Choose compatible scales $M_0^{(o)}\ge M_*(C^{(o)},\gamma^{(o)})$, then gaps $m_0^{(o)}>0$, and set $m_0=\min_o m_0^{(o)}$.
8. Put $K=(2M_0^{(0)}+1)(2M_0^{(1)}+1)$. Choose a **positive** integer $k$ such that $\ell=2kK\ge2/(c_0m_0)$. Set $L_0=\ell+2$ and $c=g_\star c_0m_0/4$.

No $A,\theta,l_0,p_0$ or earlier input is chosen using $m_0,\ell,c$ or a torus size. Appendix A records the same order-compatible constants. Use a different Lean name for the finite-memory eigenvalue parameter $\lambda$, the heat-bath gap and the diluted site measures; the manuscript uses this symbol in several local roles.

### Hypotheses and quantifiers at the principal arrows

- **Computer inputs → recursion.** The local claim is $Z_{\rm cur}\ge c_{\rm type}Z_{\rm next}$ with $Z_{\rm next}>0$. Its consequence is $\rho_j^\tau=Z_{\rm next}/Z_{\rm cur}\le1/c_{\rm type}$, not $\rho_j^\tau\le c_{\rm type}$. The paper uses the inverse correctly. The memory certificate uses revisit weight $1/4$ only as an upper bound on the actual $1/5$. The main kernel uses $\bar\alpha=0.18094,\bar\beta=0.36751$, not the smaller historical rounded values or the optional type-dependent values.
- **Recursion → (P).** For any allowed $G,Y,\tau$ in (P), make all sites of $G\setminus Y$ U and all sites of $Y$ X, retaining the original legs only. This belongs to the consistent class because $Y\cap S(G)=\varnothing$. A distance-two pair with a removed common neighbour is collinear or diagonal and its U endpoints meet the pair-class conditions. Designating one of two possible centres for a diagonal pair is permitted. The supremum in `e:FX` is over all these $G,Y,\tau$, so the resulting $A,\theta$ are uniform.
- **(P) → removal.** Each prefix $Y_j$ of the cut ordering stays outside the original $S(G)$, since $b(x_j)\ge3$. Every responding pair consists of surviving neighbours of $x_j\in Y_j$, has graph distance two, and satisfies $d(u,S(G))\ge b(x_j)-3$. The protected layer is not recomputed after removal. The first removal is allowed four neighbours and the later removals have at most three by nearest-neighbour connectivity of the ordering.
- **Removal → window.** Here $G=F\setminus B$, so both the original outside condition and the window letters become unit pins on the original legs of this $G$. Shared external frame letters give a special case of the arbitrary independent leg pins allowed by (P). The cut geometry gives $B\subset U'\subset F$, no exterior adjacency of $B$, $X\subset G$, separation, and the distance bound needed for every removal. Lemma B.1 is applied to a nonempty finite $U'$; its three topological conditions are supplied. Bounded cut cost is enough: the proof never needs it to tend to zero or to be less than $1/2$.
- **Window → MOS input.** Definition 4.7 quantifies over every exterior of the notched region, including the random exteriors generated by surgery. It is stronger than agreement away from one original exterior site. The window estimate is needed only for success indices $i\in J\subset\{2,\ldots,\lfloor s\rfloor\}$; the final propagation step may have index $\lfloor s\rfloor+1$ and needs only identical resampling when the previous shell agrees. The proof's unconditional-success sentence at line 101 should be read with its stated $i\le s$ restriction. Losing at most two indices adjacent to the one exceptional shell leaves $|J|\ge s-4$. Changing the exterior one site at a time and marginalizing to the common set $\mathcal Q_{M,\eta,\eta'}$ gives precisely the MOS bound. Remote exterior sites do not matter because the cell interaction range is one.
- **Cell gaps → box gaps.** Every even-side microscopic square is reduced by a parity-preserving translation to offset 0 or 1. Only these two offsets are required; an additional vertical offset is not missing. A square of $kK$ cells per side is a translate of a compatible union for either compatible scale. Arbitrary torus exterior configurations are represented by suitable cell exterior configurations. The comparison is $\gamma(a,\sigma)\ge c_0m_0$, with no factor of four: both dynamics resample each of their respective sites/cells at rate one, and the conditional four-site Poincaré inequality supplies the comparison.
- **Box gaps → torus → quantum.** $\ell\ge2$ is even, and even $L,N\ge\ell+2$ satisfy both the box-cell requirement and Theorem 3.1's $L,N\ge\ell+1$. Thus $g(\ell)\ge c_0m_0$, $1/\ell\le c_0m_0/2$, and $\lambda(\mu_D)\ge c_0m_0/2$. The sign rotation is sitewise and preserves both frames, hence also the heat-bath gap. Theorem 2.5 applies because $L,N\ge4$, and gives $c=g_\star c_0m_0/4$. It already establishes ground-state uniqueness for every even $L,N\ge4$, independently of mixing. Stating uniqueness only for the larger range in the abstract and Theorem 1.1 is valid.

### Objects and standard facts that need explicit Lean nodes

1. **Different spin types.** Keep frame configurations finite, ordinary continuous spins on the unit sphere, traced spins on sphere-plus-zero, and leg pins on the unit sphere. Do not identify the finite and continuous Gibbs expectations. Only partition functions are transferred. Inserting a pair observable could increase local polynomial degrees, and is not licensed by Lemma 5.2.
2. **Trace mass.** A revisit contributes an additional scalar $3/5$ to the traced partition function. A status/kept-bond assignment by itself does not encode the accumulated scalar. Represent a trace as an underlying modified domain plus its positive mass, or define traced partition functions recursively on the history. Normalized expectations discard this scalar; the ratios $R_D(w)$ retain it. Removing the responding site to obtain an ordinary consistent domain is an operation on the underlying domain. This makes the convention at `sec6-walks.tex:37` precise.
3. **Terminal objects.** Implement the corrected ordinary-prefix/marked-boundary-endpoint distinction in Finding 1. The second expansion at $v$ may start in a trace with the defect at $e\in S$, and must have a lemma that at most twelve first-visit templates can see it.
4. **Positive denominators.** For every finite choice of pins, each continuous partition function is positive: its integrand is nonnegative and is positive on a nonempty open neighbourhood of an aligned spin choice avoiding the finitely many antipodal pins. D measures have a positive uniform component. The same argument applies to the template denominators, with the explicit proof in Lemma D.1. Empty residual domains have partition function one. Trace scalar factors are positive. These facts justify every normalization, ratio and logarithm, even for disconnected domains or degenerate pins.
5. **Boundary notions.** Store the original finite $G$, its legs and $S(G)=\{x\in G:d(x,G^c)\le2\}$ as fixed data. An X site is a removal, not a new boundary condition. Distances are ambient lattice graph distances, not intrinsic distances in a disconnected remaining domain. Cell geometry uses the cell $\ell^\infty$ distance; site graph distance is restored before using (P).
6. **Integral and discrete indices.** Declare $M,M_0,\ell,k,n$ and shifts as integers/naturals where appropriate; $s=M^{1/4}$ is real and shell radii use $k_i=\lfloor is\rfloor$. The formulas $h(c)=M+1-|c|_\infty$ inside the square presuppose integer $M$. “For all sufficiently large $M$” can and should be a quantifier over integer square sizes. It is enough for MOS and the final theorem.
7. **Spectral conventions.** Section 2 uses the Markov generator $\mathcal L=\sum(E_x-1)$; Section 3 reuses $\mathcal L$ for its nonnegative negative. Use distinct names $\mathcal L_{\rm HB}$ and $A=-\mathcal L_{\rm HB}$. All cited gaps and semigroup decay rates must use the same rate-one convention. Conditional fibres inherit the original single-site conditional expectations. Strict positivity implies irreducibility and constants as the zero eigenspace.
8. **Suprema and contraction.** Define response envelopes with a bounded supremum (or include zero explicitly for empty indexing sets), show monotonicity and the bound two, and extend them constantly to negative arguments. Show kernel summability using (H2), continuity by a common summable majorant near $\theta=1$, and convergence of the positive matrix resolvent defining $\mathsf x$. The truncated quantities $\Phi_N$ avoid assuming in advance the exponential bound being proved; their uniform bound then gives the result for each fixed $d$. There is no contraction circularity.
9. **Finite probability operations.** Supply maximal coupling on finite spaces, TV monotonicity under marginalization, the triangle inequality, DLR consistency after conditional resampling, and the chain-rule lower bound $\alpha^{|A_i|}$ under partial conditioning. A single-site finite-energy lower bound persists under such partial conditioning by averaging.
10. **Asymptotics and thresholds.** Prove polynomial times stretched exponential tends to zero, both for the cut cost and for the MOS smallness condition. Choose one integer threshold above all needed thresholds for each fixed model. Translation invariance gives compatible translates; a common multiple of the two odd compatible side lengths gives the required squares. No explicit numeric value of the final scale is claimed.

### Small computational checks and certificate interfaces

These checks are supplementary computational evidence, not a rerun of the certificates.

- Exact rational arithmetic gives $0.98075^2=0.9618705625$ and verifies $0.85594872<0.98075^8$. Thus the displayed (H2) quotient really permits the quoted $q$.
- Adding the **rounded upper entries** of Table C.1 gives row B at most $0.987764$ and the row C numerator at most $1.191410$, with quotient about $0.968626017$ after division by $1.23$. Both are below $0.98779$. The last-digit discrepancy with the table's tighter final rows is explicitly explained by its use of unrounded outputs. Even the coarser printed entries suffice for (H3'). The double-precision choice of $h_C$ differs negligibly from $1.23$; equivalently one can use its exact positive dyadic value in the row-quotient check, with the same strict margin.
- The tail split covers every possible length: B/C endpoints have the same lattice parity, so lengths are even; $n\le20$, $n=22$, $24\le n\le106$, $108\le n\le260$, and $n>260$ exhaust them. Mode A's valid upper endpoint 107 is never exceeded. Mode B is valid for all lengths above 53, and its remainder uses $53<260$.
- The local certificate reader distinguishes covered and refined models. The main theorem names the covered operator-only file, not a refined or level-1-plus file. The covered model has two slots at every live corner, and the tip radius defaults to $3/5$, matching Definition 6.6 and Appendix D. The assertions/parameter conditions stated in Appendix D remain part of the computer-input trust boundary.
- The bundle contains the tail source programs, but does not identify the seven raw mode-A/mode-B production outputs behind Table C.1 by filename. I did not reproduce those large runs. Attaching a run manifest and the directed-rounding outputs would make the main numerical input easier to independently audit; this is a reproducibility recommendation, not a claim that the analytic interface or table is false.

## 4. External inputs

The following gives the content **as used**, the locator actually supplied, and the scope check. Original external texts are unavailable under the read-only input restriction. Consequently “matches” below concerns the stated hypotheses in the manuscript; it does not certify the accuracy of the quotations from those external texts.

| Input and exact use | Locator supplied by the paper | Hypothesis/scope assessment |
|---|---|---|
| **MOS94 large-square criterion:** For a fixed translation-invariant real finite-range potential on a finite spin space in dimension two, there is a threshold $\bar M$ such that one $M>\bar M$ with $\sup_{\eta,\eta'}d_{\rm TV}(\hat\mu^\eta_{\mathcal C_M,\mathcal Q},\hat\mu^{\eta'}_{\mathcal C_M,\mathcal Q})\le M^{-4}$ yields constants $C,\gamma>0$ giving `e:SM` on every square. | MOS94 Theorem 2.1, equation (2.2), and the definition of $Q$ before Proposition 2.1; restated as Theorem 4.3. | Matches the blocked models: finite $S^{(o)}$, real potential, translation invariance and range one. Proposition 4.8 plus the finite telescoping sum gives exactly this all-boundary marginal estimate. Separate thresholds for the two fixed models are harmless. |
| **MO94 compatible-domain gap:** For fixed strong-mixing constants and sufficiently large $M_0$, strong mixing on $\mathcal C_{M_0}$ gives $m_0>0$ uniformly over all $M_0$-compatible finite unions and all exteriors for the rate-one heat bath. Equivalently its centred semigroup contracts in $L^2$ at rate $m_0$. | MO94 Theorem 4.1 and rates (4.1); restated as Theorem 4.4. The adaptation also refers to MO94 (4.2), (4.5), and MOS94 Theorem 3.2, (ii)⇒(iv). | This is the one explicitly disclosed extension: MO94's proof is written for two-valued spins, while the application has 57,600 states. Remark 4.5 identifies the general-finite-$S$ reading and the proof ingredients claimed independent of binary spins and attractivity. Do not formalize it as direct application of a binary-spin theorem. Treat the general-$S$ version as an external theorem requiring validation, or supply the adaptation as separate nodes. Once that version is granted, the compatible-set and boundary quantifiers match exactly. |
| **MOS94 surgery argument:** Repeated finite couplings across shells convert a uniform interior-shell agreement probability and finite energy into the influence bound of Proposition 4.8. | MOS94 Proposition 2.1, p. 39, especially equation (2.8). | The manuscript reproduces the needed argument and replaces the original mixing-derived window bound by its own stronger all-exterior bound. A success probability $p_0>0$, rather than the original $1/2$, suffices. No direct application of a proposition with unmatched weak-mixing assumptions is being made. |
| **Spherical designs:** Uniform averages over the icosahedron and dual dodecahedron vertices equal normalized sphere integrals of every polynomial of degree at most five; only degree four is required. | DGS77, without a precise locator, in `sec2-frames-Q.tex:63`. | These are the precise sets and weights used for the frames. This is a necessary exact input; see Finding 5. Numerical moment agreement does not replace it. |
| **Clebsch–Gordan and finite SU(2) representation facts:** The tensor product of two spin-$j$ irreducibles decomposes into spins $0,\ldots,2j$, each once; finite unitary representations decompose into irreducibles; spin-$j$ weights are $j,j-1,\ldots,-j$. | No external locator; named standard facts in Lemmas 2.1 and D.6. | Used with spin $3/2$ and 2 for divisibility, and tensor products of spins 0, $1/2$, 1 for central-sector testing. The necessary parity is supplied. These are explicit formalization dependencies. |
| **Polynomial UFD and irreducibility facts:** Distinct irreducible, nonassociate bond polynomials divide a constrained polynomial jointly; a rank-four quadratic form over $\mathbb C$ is irreducible. | No external locator; `sec2-frames-Q.tex:40`. | The graph is simple and the torus has degree four. These assumptions hold at every size used by the quantum comparison. |
| **Gaussian moment formula:** Wick pairings for a standard three-dimensional Gaussian, independent radial/directional decomposition, and $\mathbb E\vert g\vert ^{2k}=3\cdot5\cdots(2k+1)$. | No external locator; `sec5-cut.tex:13`–17. | Produces normalized uniform-sphere moments used throughout the ordinary and diluted domains. Local degree limits are respected at the frame-transfer interface. |
| **FKG:** For a strictly positive probability on the subset lattice satisfying $\pi(A\cup B)\pi(A\cap B)\ge\pi(A)\pi(B)$, increasing functions have nonnegative covariance; hence increasing and decreasing functions have nonpositive covariance. | FKG71, no theorem/page locator; `app-local.tex:225`. | Applied on the finite lattice of subsets of three elements after restricting to $0<r_j<1$; the lattice condition is checked, and boundary radii are obtained by continuity. This supports the additional closed-form proof, not a required attractive-spin assumption for the cell dynamics. |
| **Sylvester/Bareiss:** A real symmetric integer matrix is positive definite iff all its leading principal minors are positive; fraction-free elimination computes these minors with exact divisions when preceding pivots are nonzero. | Bareiss, Bar68, without theorem/page locator; `app-local.tex:192`; Sylvester's criterion is named without citation. | Integer matrices are congruence matrices in a nonorthonormal basis, scaled by a positive integer. Positivity is invariant under that congruence. Positive pivots avoid the zero-pivot case. Exact computation, sector coverage and overflow checks remain section-local certificate obligations. |
| **Finite spectral/probability facts:** Spectral theorem, variational Poincaré principle, irreducibility from full support, finite optimal coupling, reversible semigroup/gap equivalence, and spectral-radius continuity/positive-matrix resolvent. | Standard facts without separate locators; used in Sections 2–7 and Lemma C.1. | All operators at these interfaces are finite dimensional except the explicitly summable trail kernels; positivity, reversibility and the relevant convergence conditions are stated or have the nodes listed above. |

AKLT88 and KLT88 provide background for the model and representation; the required nonzero frustration-free vector and the quantum comparison are established in Section 2. Knabe and Gosset–Mozgunov motivate Section 3, but its finite-size inequality is proved there rather than imported with a translation-invariance hypothesis. Timár motivates Appendix B, whose needed topology statement is also proved in the paper. Kesten appears in the bibliography but supplies no step of the main integration chain.

The remaining external trust boundary is therefore explicit: exact design quadrature, the stated general-finite-spin mixing/gap results (including the disclosed MO94 adaptation), standard representation/algebra/probability facts, and the separately certified numerical inputs. Subject to those inputs and the local corrections above, the abstract's and Theorem 1.1's final uniform-gap conclusion has the hypotheses and quantifiers supplied by the assembled proof.
