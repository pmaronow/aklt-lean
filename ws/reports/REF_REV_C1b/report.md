VERDICT: GAP

Reviewed the whole of [part/sec7-recursion.tex](/home/ubuntu/aklt/review/REF_REV_C1b/part/sec7-recursion.tex), lines 1–936, against the allowed [interfaces.tex](/home/ubuntu/aklt/review/REF_REV_C1b/interfaces.tex). No other manuscript material or external sources were used. Line references below are to these supplied files.

The numerical logarithm bounds, the kernel summability and witness transport, and the abstract renewal argument check out. The main implication is nevertheless not established relative to the supplied interfaces: six essential referenced definitions/results are absent. The findings below separate the missing expansion, local comparison, and quantitative estimates. They are proof/contract gaps, not counterexamples to the intended implication.

The seven declarations exported here and repeated in the interfaces (`l:log-mean-bounds`, `l:response-typed`, `d:kernel`, `d:kernel-order`, `h:H3`, `l:Mtheta`, `t:rec`) match exactly after whitespace normalization. Those repeated declarations are the targets being checked, and cannot serve as independent proofs of themselves.

1. **Critical — The trace expansion and its ratios have no supplied definitions or theorem.**

   **Locations:** `part/sec7-recursion.tex:39`, `l:closure`, especially lines 78–100; `:144`, `l:terminalcover`, especially lines 150–183; `:389`, `l:response-typed` and `:395`, `e:rec-typed-coefficients`; `:650`, `l:recineq`, especially lines 655–671 and 729–731; also lines 769–787. The absent labels are `d:trace`, `d:ratios`, and `p:pairwalk`.

   **Exact claims requiring justification:** the trace operations used in the kept-set induction; the admissibility and target-degree restrictions; the pinned/free expansions with a common trail class and common coefficients; the terminal constant \(\eta_v\in\{1,3/5\}\);
   \[
   a_D(w)=3^{-n}(3/5)^{N_{\mathrm D}(w)};
   \]
   and the exact logarithmic-mean formulas for the response coefficients.

   **Why this is a gap:** neither these labels nor their statements occur in either supplied file. `interfaces.tex:348–377` defines networks, but does not define tracing or its transition coefficients. `interfaces.tex:379–394` gives a coarse response identity and bounds, without defining the ratios or identifying its coefficients by logarithmic means. In particular, that statement does not contain the identity attributed to it at part lines 393–399, or the assertion that every D departure has ratio one. `interfaces.tex:993–1009` gives local template polynomials, not a global pair-walk expansion. Thus the variables \(D[w],a_D,R_D,\rho_j\) and the relevant trail classes lack their required contracts. The status induction is consistent with the operations described informally in its proof, but an induction about an undefined expansion does not establish the expectation identity used in the recurrence.

   **Repair:** include and prove the missing definitions and expansion proposition here, or supply them as actual interfaces from the part responsible for tracing. They must specify the following operations: at an unprotected live U site choose a present out-bond, change its law to D and drop the out-bond; at a live D site with at most one present bond, traverse that bond and remove the site; on arrival drop the arrival flag. No protected site is departed from. In particular, the existing normalization of the initial U flag must be retained for the ordinary-domain closure claim.

   An adequate expansion contract must explicitly include admissibility of the start, the initially absent designated incoming bond, first stopping in a set containing \(S\) and the target, the target-degree restrictions, and separate degree at most four for inserted observables. Its substantive conclusion should include the following exact formulas (with \(E_j^+\) the network after the chosen trace step and \(B\) the stopping set):

   ```latex
   \[
   \rho_j^\bullet=\frac{Z_{E_j^+}^\bullet}{Z_{E_j}^\bullet},
   \qquad
   a_E(w)=3^{-N_{\mathrm U}(w)}5^{-N_{\mathrm D}(w)},
   \qquad R_E^\bullet(w)=\prod_j\rho_j^\bullet,
   \qquad \rho_j^\bullet=1\quad\text{at a D departure}.
   \]
   \[
   \mathbb E_E^\bullet(n_a\cdot n_t)
   =\sum_{w\in\mathcal T_E(a,B)}a_E(w)R_E^\bullet(w)
   \begin{cases}
   \eta_t,&w_{|w|}=t,\\
   \mathbb E_{E[w]}^\bullet(n_{w_{|w|}}\cdot n_t),
       &w_{|w|}\ne t,
   \end{cases}
   \qquad
   \eta_t=\begin{cases}1,&\mathrm{st}(t)=\mathrm U,\\
                       3/5,&\mathrm{st}(t)=\mathrm D.
          \end{cases}
   \]
   ```

   Take \(a\notin B\) and \(S\cup\{t\}\subseteq B\); in particular the starting and target sites are distinct. In the uses in this part, the unpinned start is U with at most three present bonds or D with at most one. A U target has at most three incident factors before its first arrival, and a D target has at most one present bond. The proposition must justify the terminal constants under these assumptions, finiteness of the expansion, and independence of its trail class and coefficients from the choice \(\bullet=\tau,0\). These conclusions can be proved by the finite moment identities, but they are not stated in the available interfaces.

   For the typed response proof, also identify the canonical coefficients explicitly. At a U step, let \(E'=E\setminus\{y\}\), set a scalar product to zero when either of its indicated bonds from y is absent, and use

   ```latex
   \[
   I=1+\frac{P_{fg}+P_{fo}+P_{go}}3,\qquad
   J=1+\frac{P_{fg}}5,\qquad
   I^\bullet=\mathbb E_{E'}^\bullet I,\quad
   J^\bullet=\mathbb E_{E'}^\bullet J,\qquad
   \rho_j^\bullet=\frac{J^\bullet}{I^\bullet}.
   \]
   \[
   \beta_j=\frac1{3\mathcal L(I^\tau,I^0)},\qquad
   \alpha_j=\frac1{3\mathcal L(I^\tau,I^0)}
             -\frac1{5\mathcal L(J^\tau,J^0)}.
   \]
   ```

   With two present neighbours, \(J=1\) and the corresponding coefficient is \(\beta'_j=1/(3\mathcal L(I^\tau,I^0))\). The coefficient positivity imported from `l:response` must refer to these same coefficients. A coarse identity with unspecified admissible coefficients does not, by itself, imply this identification or the sharper bounds.

2. **Major — Template (H1) is applied to global trace networks without an available covering theorem.**

   **Locations:** `part/sec7-recursion.tex:127–132`, `l:closure`; `:195–200`, `l:terminalcover`; `:392–393` and `:431–434`, `l:response-typed`; `:677–679`, `l:recineq`. The missing label is `l:local`.

   **Exact claim:** a departure with the asserted local non-tip pattern satisfies
   \[
   I^\tau\ge c_{\mathrm{type}}J^\tau,
   \qquad \rho_j^\tau\le c_{\mathrm{type}}^{-1},
   \]
   despite missing external factors, actual removed or D tips, and the allowed discrepancy between actual tip kept sets and covering tip data.

   **Why this is a gap:** (H1), `interfaces.tex:429–439`, quantifies over the particular templates of `d:pattern`, with twenty unit slot vectors and covering U tips. It does not quantify over arbitrary global auxiliary networks. Matching the non-tip statuses is necessary, but does not itself extend the inequality to omitted slots or replace actual tip data. The text delegates precisely these operations to `l:local`, which is absent. The improved typed coefficients and both walk estimates consequently lack their local partition-ratio bound.

   **Repair:** provide a covering lemma with the full scope actually used. One suitable conclusion is:

   ```latex
   Assume (H1). Let \(E\) be a finite auxiliary network with at most
   four incident factors at every site, and let \(y\notin S\) be
   an admissible U departure with chosen present out-bond to \(o\).
   Suppose its radius-two non-tip data satisfy Definition~\ref{d:pattern}.
   Actual tips may have either site law, be removed, or have
   missing incident factors; no consistency with covering tip
   kept sets is required. Missing external factors, including
   either or both corner slots, are allowed.
   If \(E^+\) is the chosen trace successor, then
   \[
      Z_E^\bullet\ge c_{\mathrm{type}}Z_{E^+}^\bullet
           \qquad(\bullet\in\{\tau,0\}).
   \]
   ```

   This needs a proof, not an additional assumption in `t:rec`. The available ingredients suggest the following proof: condition on spins outside the radius-two template; extend the slot inequality from spheres to closed unit balls by separate affinity; encode an omitted factor by the zero vector; integrate each actual tip to a positive scalar times \(1+b\cdot n_z\), with \(|b|\le3/5\); use the surjectivity assertion of `l:35` to realize that mean by three unit slots of a covering U tip; and cancel the common positive scalars in current and next partition sums. Removed tips require mean zero. The proof must explicitly cover both missing corner slots and the original leg factors. This is also the scope needed when a defect at \(e\) is outside a second departure's template but affects an external factor.

3. **Major — The exposure and one-point estimates used to prove the recurrence are not supplied.**

   **Locations:** `part/sec7-recursion.tex:155` and `:209–213`, `l:terminalcover`; `:684–691`, `e:rec-exposed`; `:774–803`, `l:recineq`. The missing labels are `l:exposure` and `l:onepoint`.

   **Exact claims:** arbitrary prescribed exposure order gives the prefix-product bound in `e:rec-exposed`; the second expansion is bounded by
   \[
   K_*q^{d(v,S)},\qquad K_*=(12/5)^{12}\frac{C_V}{1-q};
   \]
   and the first expansion obeys the same bound for the **sum of pointwise maxima** of pinned and free ratios. These yield the particular exported constant \(C_T=2K_*^2\).

   **Why this is a gap:** neither estimate is stated in the interfaces. (H2) bounds lattice weights \(\mathsf W\), not the products \(a_E(w)R_E^\bullet(w)\), so a comparison is indispensable. The verified geometric exception count alone does not establish this comparison. Also, separate upper bounds on two sums do not imply the same upper bound on the sum of their pointwise maxima. Thus lines 797–803 require either the stated stronger common majorant or a different final estimate.

   **Repair for exposure:** insert the following elementary lemma and proof, or make it an actual permitted import:

   ```latex
   Let \(p_i,r_i,x_i>0\) with \(r_i\le1\) and \(p_i\le x_i\),
   where \(x_i\ge1\). For every permutation \(\sigma\),
   \[
   \left|\prod_i p_i-\prod_i r_i\right|
   \le\sum_k |\log p_{\sigma(k)}-\log r_{\sigma(k)}|
                        \prod_{l\le k}x_{\sigma(l)}.
   \]
   ```

   Telescoping in the order \(\sigma\) gives a product of preceding \(p\)'s, the difference of the current factors, and succeeding \(r\)'s. Use
   \(|p-r|\le\max\{p,r\}|\log p-\log r|\) and \(\max\{p_i,r_i\}\le x_i\). This proves exactly the required order-sensitive inequality, including zero-response steps. The ratio and response contracts from finding 1 are still needed to instantiate it.

   **Repair for the one-point bound:** under (H1), (H2), admissibility, and at most \(k\) exceptional U departures on every trace, prove the pointwise comparison and its summation:

   ```latex
   \[
   a_E(w)\max\{R_E^\tau(w),R_E^0(w)\}
       \le (12/5)^k\mathsf W(w),
   \]
   \[
   \sum_{w\in\mathcal T_E(a,S)}
       a_E(w)\max\{R_E^\tau(w),R_E^0(w)\}
   \le (12/5)^k\frac{C_V}{1-q}\,q^{d(a,S)}.
   \]
   ```

   At a covered U departure use \(\rho^\tau\le x_{\mathrm{type}}\), at an exceptional U departure use \(\rho^\tau\le12/5\), and use \(\rho^0\le1\). D departure ratios are one. A true D departure at a lattice first visit has coefficient \(1/5\le x_{\mathrm{type}}/3\); revisits have coefficient \(1/5\). Since \(x_{\mathrm{type}}\ge1\), each exceptional U departure costs at most the displayed extra factor. Summing lengths \(n\ge d(a,S)\) with (H2) gives the geometric-series bound. This proof must apply to exceptions at arbitrary trail positions and to the larger first-trail class that no longer avoids \(v\).

   Alternatively, once the **individual** one-point estimates are supplied, the stronger sum-of-maxima statement is unnecessary for \(T_2\). Lines 789–803 can be replaced by the following exact estimate, preserving the stated constant:

   ```latex
   \begin{align*}
   |T_2|
   &\le K_*q^{d(v,S)}
       \sum_{w\in\mathcal W_S}a_D(w)
                     \bigl(R_D^\tau(w)+R_D^0(w)\bigr)\\
   &\le 2K_*^2q^{d(u,S)+d(v,S)}
    \le C_Tq^{2d}.
   \end{align*}
   ```

   I do not find an arithmetic error in \(C_T\): the constant follows from either repaired route. Both routes currently rely on an unprovided one-point estimate.

**Statement table.** “Conditional” identifies a step whose internal argument checks but whose named prerequisites are missing as recorded above. “Sound” for an implication means sound under its stated hypotheses; it does not assert (H1)–(H3) unconditionally.

| Label and location in `part/sec7-recursion.tex` | Content | Verdict | Dependencies |
|---|---|---|---|
| `d:pairenv`, line 14 | Ordinary-domain pair envelopes; empty supremum and constant negative extension; bounds and monotonicity | Sound | `d:domain`, `d:pinmodel`, `l:finitefacts`; endpoints have norm at most one |
| `l:closure`, line 39 | Kept-set induction, removal of an interior live endpoint, ordinary response pairs, terminal protected defect | Conditional; findings 1–2 | Missing `d:trace`, `l:local`; `d:domain`, `d:pattern`; ambient distance to the original boundary |
| `l:terminalcover`, line 144 | Admissible second start, target-degree check, at most twelve exceptional U departures | Geometry and degree checks sound; estimate application has gaps 1–3 | `l:closure`; missing `d:trace`, `p:pairwalk`, `l:local`, `l:onepoint` |
| Unlabelled remark, line 216 | Box example showing the second endpoint can lie in the protected set | Example geometry and membership sound; exclusion as a trace start depends on missing `d:trace` | `d:pinmodel`, `d:domain`, `d:pairenv`, missing start convention |
| `l:log-mean-bounds`, line 230 | Monotonicity of the difference of reciprocal means, logarithm enclosure, all rational coefficients | Sound | Elementary integration, differentiation on compact positive rectangles, exact rational arithmetic |
| `e:rec-log-integral`, line 269 | Reciprocal logarithmic mean as an integral, including equal arguments | Sound | Positive arguments; direct integration and the separately defined diagonal value |
| `e:rec-log-table`, line 314 | Five exact rational enclosures for the truncated logarithm expressions | Sound; independently checked | Definitions of `f_-`, `f_+`; integer formula with `D_*=45045` |
| `l:response-typed`, line 365 | Sharper straight/turn response coefficients under (H1) | Gap; findings 1–2 | Missing ratio/covering contracts and canonical coefficient identities; otherwise `l:finitefacts`, `l:35`, `l:log-mean-bounds` apply correctly |
| `e:rec-typed-coefficients`, line 395 | Exact formulas for canonical alpha and beta | Correct if the missing ratio definition is supplied; not contained in the cited interface | `rho=J/I`, the definitions of `I,J`, logarithmic divided differences |
| `d:kernel`, line 444 | Nonnegative type/shift kernel with dead-neighbour rules and mass-free weights | Sound as a definition of possibly infinite nonnegative sums | `d:weights`, rational coefficient table; edge-simple trails and a first hit of the target |
| `d:kernel-order`, line 495 | Fixed rational witness and deterministic, theta-independent exposure order | Sound | Positive `x_s,x_t`, positive `h`; zero-reward branch and index tie-break |
| `h:H3`, line 517 | Finite-cutoff positive-vector condition and equivalence with the full sum | Sound definition and equivalence | Nonnegative summands, finitely many trails per length, positive `h` |
| `l:Mtheta`, line 542 | Shift bound, summability for `q^2<theta<=1`, transport of the same witness | Sound under (H2), (H3) | `d:weights`, (H2), `h:H3`, rational comparisons with `bar alpha,bar beta`, geometric series |
| `e:rec-shift-choice`, line 593 | Explicit positive epsilon, theta and rho | Sound | `0<q<1`, `C_V>=1`, positive `h`, `rho_0<1`; `B_*>0` |
| `l:recineq`, line 625 | Pair-envelope recursion with the stated terminal constant | Gap; findings 1–3 | Missing expansion, local comparison, exposure and one-point estimates; closure and typed coefficients |
| `e:rec-exposed`, line 686 | Arbitrarily ordered exposure with prefix products | Gap in supplied proof; valid with the explicit lemma in finding 3 | Missing `l:exposure`; canonical response identities and ratio bounds |
| `e:rec-pair-envelope`, line 715 | Response bounded by `F_Y(d-s)` using the original protected set | Sound conditional on closure | `l:closure`, `d:pairenv`, triangle inequality, constant extension for negative arguments |
| `e:rec-T1`, line 759 | Domination of the closed-trail response by the modified kernel | Conditional; gaps 1–3 | Exposure and envelope bounds; true-U/first-visit comparison; `b'_type<=b_type`; kernel definition |
| `l:renewal`, line 814 | Bounded nonnegative shift recursion implies exponential decay with the displayed A | Sound | Stated weighted row inequality, positivity, finite unweighted row sums, geometric series |
| `e:rec-renewal-iterate`, line 849 | Finite iteration of `F<=KF+g` | Sound | Positive bounded-function operator; finite row sums |
| `e:rec-renewal-remainder`, line 856 | Unweighted remainder bounded by `2 rho^k h/h_min` | Sound | `F<=2`, `Kh<=rho h`, positivity; includes shifts to negative arguments |
| `t:rec`, line 891 | (H1), (H2), (H3) imply the exact property P and the displayed A | Gap downstream of `l:recineq`; final conversion and export strength are correct | `l:Mtheta`, `l:recineq`, `l:renewal`, `h:P`, ordinary-domain embedding |

**Verification and boundary checks.** All computations used a single process, hence no more than one core.

- Checked with exact Python `Fraction` arithmetic all five rows of `e:rec-log-table`, both integer formulas for `f_-` and `f_+`, all three coefficient inequalities in both type rows, and `0<b'_type<=b_type`. The products `a c_s=27869/31250` and `a c_t=5423/6250` are correct. The displayed residual numerators `13215,1425,1692` and `259510,2684,2235` are correct. No floating logarithms were used.
- Checked the missing-reference inventory directly: precisely `d:ratios`, `d:trace`, `l:exposure`, `l:local`, `l:onepoint`, and `p:pairwalk` are referenced but unlabelled in both files. This is a missing-statement issue, not merely a different spelling of an available label.
- Independently enumerated every edge-simple, centre-avoiding first-hit kernel trail of length at most 12: 2,796 for B and 2,612 for C. Each passed the outgoing-neighbour, at-most-two-departures, and response-shift tests. This is a finite diagnostic; the general geometric arguments are also valid. For a non-start site, two departures already use all four incident bonds; for the start, exclusion of the centre leaves only three available bonds. In either case a further visit cannot be an intermediate continuation or a first visit to the target.
- Empty pair classes, zero response rewards in the ordering, zero shifts, the logarithmic-mean diagonal, `R_0=0` in (H3), and the integer boundary value `d=0` in the final conclusion are handled. A nonempty finite G has a nonempty original protected set, so every distance evaluated for an actual pair is finite. Empty G has no pairs.
- For an interior departure `y` outside S, its lattice neighbours have distance at least two from the complement of G and therefore have no original legs. After removing y they have at most three incident factors. Inserting one scalar product consequently has separate degree at most four, as required by `l:finitefacts`. Pairwise nonadjacency gives the conditional independence used with `l:35`; conditioning is only on positive fibres. Thus `J^tau>=116/125` and the free positivity argument are valid once `I,J` and the ratios are defined.
- The exceptional set has four sites at distance one and eight at distance two from e. Each can be departed from as U only once. The first arrival at the protected target e drops a present bond and leaves at most three total factors, including original legs; a later terminal scalar-product insertion respects degree four. The extra assumption `v notin S` is used correctly for the second start.
- The shift estimate is `s<=n/2+1`. The entry majorant has ratio `q/sqrt(theta)<1`; its displayed sum is correct. For witness transport, `q<b<theta<1`, every denominator in `B_*` and epsilon is positive, and `sum n(n+1)r^n=2r/(1-r)^3` gives exactly the stated margin.
- The renewal proof correctly controls the remainder without an exponential weight and applies the weight only to the source. Thus arbitrarily large shifts into negative integers cause no circularity. The constant extension and `theta^d>=1` for `d<=0` are sufficient. The resulting A is finite and at least two.
- The final ordinary domain has all sites of Y removed and all other sites U with full kept sets. Because `Y cap S` is empty, it retains exactly the original leg factors. Every pair in property P is in one of the two envelope classes. There is no mismatch in boundary convention, quantifiers, pair orientation, or the exported value of A.

**Formalization notes.**

- Restore the missing contracts before formalizing the recurrence. In particular, give `rho`, `a_E`, `R_E`, the trace successor and the stopping class actual definitions, and make the canonical coefficient identities part of the response API. Same-label declarations of this part in the interface file must not become axioms used to prove themselves.
- Represent a response pair together with its designated removed centre. A diagonal pair has two possible common neighbours, and the chosen one determines the initial incoming direction. Fix one lattice symmetry for the original pair before mapping all of its trails into the canonical kernel; this preserves injectivity of the trail comparison. No spatial rotation of spin vectors is required.
- Distinguish ordinary consistent domains, a live-defect trace network, and the terminal protected defect. The normalized U start need not itself be in the ordinary consistent class. Partition-function invariance on dropping a flag to a removed site is the bridge. Never apply an ordinary-domain envelope to the live-defect network before removing its live interior endpoint, and never remove the protected terminal site to claim ordinary membership.
- Record separate-degree bounds for every inserted observable. The finite moment law is only covariant through degree four; there is no unrestricted rotational-invariance assumption. At conditional expectations, use only positive conditioning fibres.
- Initially interpret kernel sums as nonnegative extended sums, or as suprema of finite partial sums. Establish finiteness before replacing them by real-valued infinite sums. A real `tsum` without a summability proof is not an adequate definition of a possibly divergent nonnegative series. Use positivity/Tonelli for regrouping by type and shift.
- Keep shift indices natural and arguments of F integer. Implement the negative extension explicitly, including the case `d-s=0`. The exact integer inequality `2*s<=n+2` avoids an accidental natural-number division in the geometric shift bound.
- Define the ordering key by a separate zero-reward branch, rather than evaluating its zero denominator. An extended nonnegative real or an option type can represent infinity. Resolve all remaining ties by the original path index. The chosen order is independent of theta.
- Use the integral definition of the reciprocal logarithmic mean to handle coincident arguments uniformly. All tabulated comparisons reduce to rational or integer arithmetic with proved positive denominators; the exact checks above can be reproduced without numerical analysis.
- Define K on nonnegative functions with possibly infinite values, or explicitly maintain finiteness of every application used. It maps bounded functions to bounded functions, while `e_X(d)=h_X theta^d` is unbounded as `d` tends to minus infinity. The stated weighted row hypothesis makes `K e` finite pointwise. The proof's unweighted remainder estimate should be preserved.
- Package the elementary facts `G nonempty => S(G) nonempty`, interior sites have a full radius-two diamond, and neighbours of an interior site have no original legs. These discharge recurring finiteness, geometry and degree obligations without enlarging the protected set.
