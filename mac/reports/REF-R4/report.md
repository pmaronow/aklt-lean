VERDICT: ERROR

The exposure lemma is false under its stated generality, and the closure lemma contains false invariants. These are local defects: the pair class used in the main recursion excludes the counterexample to exposure, and the remaining defects can be repaired without changing the kernel or its constants. I found no counterexample to Hypothesis (P) or to the intended conditional implication (H1)+(H2)+(H3') => (P). That implication needs the repairs below before it is a valid chain of statements suitable for formalization.

Scope: I read all manuscript source files for context and checked Sections 6 and 7 in detail. Locations below are source lines in the frozen bundle, relative to `bundle/manuscript/`. The computer-assisted assertions of Section 8 and the appendices are identified as inputs; this report does not independently certify all their programs or certificates. No subagents or web searches were used.

## 1. Findings

### 1. Critical — the exposure lemma fails for an initially diluted site with two present bonds

**Location:** `sec6-walks.tex:53–55`, the revisit-ratio assertion; `sec6-walks.tex:84–96`, Lemma 6.5 (`l:exposure`, `e:exposure`). The same incorrect ratio is used in the proof of Lemma 6.11 at `sec6-walks.tex:149`.

**Exact claim:** “for a revisit, rho_j^tau = rho_j^0 = 3/5,” and consequently

\[
|R_D^\tau(w)-R_D^0(w)|\le (3/5)^{|w|-|\Phi|}
\sum_k |\lambda_{\sigma(k)}|\prod_{l\le k}x_{\sigma(l)}.
\]

Here “revisit” means that the departure site currently has status D, including a site already of status D in the initial domain. Definition 6.1 and Proposition 6.3 allow the initial departure site to have **two** present bonds. The proof's integral with only one bond does not cover that case.

**Failure:** Suppose the initial site y has status D and present neighbours f,o. Put E'=D with y removed. Direct integration gives

\[
Z_D^\cdot=Z_{E'}^\cdot\left(1+\frac15\mathbb E_{E'}^\cdot[n_f\cdot n_o]\right),
\qquad
Z_{D;[(y,o)]}^\cdot=\frac35 Z_{E'}^\cdot.
\]

Thus

\[
\rho_1^\cdot=\frac{3/5}{1+\frac15\mathbb E_{E'}^\cdot[n_f\cdot n_o]},
\]

which generally depends on the pins. For a one-step trail starting at this D site there are no first-visit steps, so Phi is empty and the claimed exposure bound has right-hand side zero.

Here is a fully specified counterexample, with an interior terminal site, so it does not rely on Finding 3's boundary defect:

- Let G={z in Z²: |z|_1 <= 3}; then S(G)={z: 2 <= |z|_1 <= 3}.
- Give y=(0,0) status D, keeping precisely its bonds to f=(-1,0) and o=(1,0).
- Remove (0,1) and (0,-1).
- Give f,o status U. Each keeps only its bond to y and its bond to the axial site (-2,0) or (2,0), respectively.
- Every site of S has status U and keeps all its bonds. This is a domain of Definition 6.1; membership in D_cons is not required by Lemma 6.5.
- Set every boundary pin to (0,0,1). Choose u=y, v=o, T=S union {o}, and w=(y,o).

Exact rational integration gives

\[
\mathbb E_{E'}^0[P_{fo}]=\frac{243}{7174454},\qquad
\mathbb E_{E'}^\tau[P_{fo}]=\frac{162376940888609}{7284251314603125},
\]

and hence

\[
R_D^0(w)=\frac{21523362}{35872513},\qquad
R_D^\tau(w)=\frac{21852753943809375}{36583633513904234}.
\]

These unequal rational numbers contradict the zero right-hand side of Lemma 6.5. Their numerical approximations are 0.599995935607 and 0.597336892070.

The exact calculation is reproduced by [check_r4.py](check_r4.py), with output in [check_r4.out](check_r4.out). It uses only rational arithmetic and the sphere moment formula. After integrating the outer sites, E' consists of an eight-vertex ring with four attached tips and the two leaves f,o. Each leaf supplies the factor 1/3 in the correlation. This gives a small transfer-matrix calculation, described further below.

**Repair:** State the constant-revisit formula and Lemma 6.5 for trails whose initial D site has at most one present bond. Subsequent D departures automatically have at most one present bond, because arrival has already deleted one of the at most two present bonds. This restriction holds in Theorem 7.4: `P_X(D)` explicitly imposes it on u, and on v when the second expansion starts there. No change to the kernel is necessary.

Lemma 6.11 can retain its broader statement, but its proof must treat an initial two-bond D site separately. The displayed formula gives rho_1^tau <= (3/5)/(4/5)=3/4, using P_fo >= -1. Therefore (1/3)rho_1^tau <= 1/4 <= omega_1, since a first departure in the lattice history has omega_1 >= 1/3. All later D departures have the claimed factor 1/5. This proves the original domination with the original constant. The same bound also handles the free ratio.

### 2. Critical — the closure lemma's universal invariants are false as written

**Location:** `sec7-recursion.tex:18–24`, Lemma 7.1 (`l:closure`), especially items (2) and (3); proof at lines 28–30.

**Exact claims:** “every site of status D keeps exactly two bonds”; the live endpoint “has dropped exactly its arrival bond”; and, “for every j,” removing the live endpoint gives E'_{j+1} in D_cons(G).

**Failure at a live D endpoint:** Take G=[-4,4]², remove c=(0,0), and give all other sites status U with all bonds kept. This is in D_cons(G). Let u=(-1,0), v=(1,0), and consider the stopped trail

\[
u,\ (-1,1),\ (-2,1),\ (-2,0),\ u,\ (-1,-1),\ (0,-1),\ (1,-1),\ v.
\]

It avoids S union {v} before its final site. Normalize the first step by dropping u's bond to c, as the lemma requests. After the first departure, u has status D and keeps its west and south bonds. At j=4 the trail returns to u from the west and drops that arrival bond. The live endpoint u is now D with **one kept bond**, not two. This occurs even for trails in the T1 term of the main theorem. The exact combinatorial check is included in `check_r4.py`.

**Failure at j=0:** For an initial U site u, D_0=D still keeps the bond to c. The text says this bond is additionally dropped “at the first step,” so item (2)'s assertion that the live endpoint has already dropped its arrival bond is not true of D_0. Removing a bond to an X site has no effect on partition functions, but the kept-set assertion still needs a convention.

**Failure at a terminal S site:** In the same G and D, take w=(u,(-2,0),(-3,0)). Its endpoint e=(-3,0) lies in S. If “for every j” includes the final prefix, item (3) removes e, contradicting Definition 6.1's requirement that every S site have status U. The proposed E' is not in D_cons(G).

**Repair:** Make the live endpoint an exception in both kept-set assertions. For a positive-length prefix, all non-live D sites keep two bonds; the live endpoint keeps three if U and one if D. Treat the initial prefix separately, or normalize the bond to the removed centre before forming D_0 when u is U. Assert item (3), and the response-pair conclusions, only for departures from sites outside S, in particular for the prefixes j<|w| used by the expansion. At a terminal S site record the endpoint defect rather than claiming admissibility after its removal. With these corrections, the inductive argument establishes precisely the closure needed for T1.

### 3. Major — a trace stopped at S is outside the declared domain class, yet another proposition is applied to it

**Location:** `sec6-walks.tex:10,37,42`, Definition 6.1 (`d:domain`), tracing and Proposition 6.3 (`p:pairwalk`); `sec6-walks.tex:142`, Lemma 6.11 (`l:onepoint`); `sec7-recursion.tex:80–82`, the T2 proof of Theorem 7.4 (`t:rec`).

**Exact claims:** A domain must have every S site “keep all their bonds.” A trace drops every traversed bond “by both ends.” The T2 proof then invokes Proposition 6.3 “in D;[w]” for a trail ending at e in S.

**Missing argument/type mismatch:** At arrival at e, the construction deletes e's arrival bond from its kept set. Thus D;[w] is not a domain of Definition 6.1. The example in Finding 2 makes this explicit. The T2 proof recognizes this as the “only violation” but does not state an extension of either the partition-function definition or Proposition 6.3 to such objects. Nor does the alternative D=D_0;[w_0] in Lemma 6.11 resolve the mismatch with Proposition 6.3's original domain hypothesis.

There is a second bookkeeping omission: D;[w] includes a scalar mass (3/5) for each D-to-X departure, whereas Definition 6.1 encodes only statuses and kept sets. The underlying domain alone does not determine its trace partition function. This mass cancels from expectations but must be retained in R and in its stepwise factorization.

**Repair:** Define a traced object as a weighted spin network: statuses, kept sets, unchanged boundary-leg factors, and a positive scalar mass. Allow the U sites in S to lose traversed bonds, while keeping all their pin factors; reserve “admissible/consistent domain” for the original protected-boundary class. State the walk identity for these networks, assuming only that departure sites lie outside S, have no legs, and satisfy the degree bounds. Its existing algebraic proof then applies. Use D_cons membership only for the underlying consistent domains E' obtained at nonterminal departures of the first expansion.

For T2, state the one-defect closure argument explicitly: initially the sole defect is the deleted arrival bond at e. Normalize v's bond to its removed centre before its first departure. Every first visit of the second trail whose local internal bonds avoid this defect has the ordinary P_ext pattern; a defective passage site y' is in the radius-two ball about e, excluding e. There are 12 such sites, and a U site can be left as a first visit at most once. Missing external-slot bonds are handled by Lemma 6.8's averaging argument. This proves the required 12-exception hypothesis without extending F_X or enlarging P_ext.

The first walk's closure argument also works when its stopping set is just S: the exclusion of the distinguished target v plays no role in that induction. State this variant when applying Lemma 6.11 to the sum over all trails from u to S at line 82. Alternatively bound the original subset W1 directly by the same pointwise weight domination.

These repairs preserve C_T=2(12/5)^24(C_V/(1-q))². They do not require an additional computer estimate.

### 4. Minor — the endpoint explanation in the pair-walk proof needs its qualification

**Location:** `sec6-walks.tex:44,48`, Proposition 6.3 (`p:pairwalk`).

**Exact claim in the proof:** “if v has status D its only remaining bond was the arrival bond, so after arrival n_v is independent of the rest with law lambda_D.”

**Failure:** Proposition 6.3 allows v to have status D with two present bonds in the initial domain. It then has one bond after arrival and need not be independent of the remaining spins. The statement at line 44 correctly qualifies its isolated-site explanation by requiring one present bond in D; the proof sentence drops that qualification.

**Repair:** Repeat “with one present bond in D” in the proof. In fact the conclusion E|n_v|²=3/5 holds even with two initial bonds: after arrival there is at most one bond, and integration gives both int(1+n·a)lambda_D(dn)=1 and int |n|²(1+n·a)lambda_D(dn)=3/5. This stronger version is available without asserting independence. The main theorem's pair class already gives at most one initial present bond.

### 5. Minor — specify the U kept sets in the local pattern class

**Location:** `sec6-walks.tex:103–111`, Definition 6.6 (`d:pattern`) and the count of P_ext; compare `sec6-walks.tex:10,14`, Definition 6.1 (`d:domain`).

**Exact specification:** Patterns have statuses and kept bonds “as in Definition [6.1]”; the passage site has status U and its arrival bond is dropped, while other sites may have status U. Definition 6.1 permits arbitrary kept sets at a U site in a general domain; only D_cons requires U sites to keep all bonds.

**Imprecision:** The pattern definition does not explicitly impose the intended full U kept sets, or specify the passage site's other three kept bonds. Condition (C) alone does not impose full kept sets: two U endpoints could both drop their common bond. The integral formula in `app-local.tex:26` and the supplied consistent-pattern enumerator instead assume that every U site other than the passage site keeps all its bonds, and that the passage site keeps precisely its three non-arrival bonds. See `programs/h1-patterns/code/pext.py:49–53,109–122`.

**Repair:** Add those requirements to Definition 6.6. They are exactly what corrected closure supplies, so this clarification matches the computer input and requires no additional patterns. State separately that absent external corner-slot factors may be filled by the convex-averaging enlargement, and that tips are the covering U tips rather than sites constrained by the original global consistency rule.

## 2. Statement table

“Correct after fix” means the identified local repair suffices; it does not mean that the printed proof is already complete. Hypotheses are assessed as well-posed assumptions, separately from their computer-assisted verification.

| Number / label | Content | Verdict | Dependencies and qualifications |
|---|---|---|---|
| 6.1 `d:domain` | U/D/X networks, partition functions, consistent domains | correct after fix | Positive product measures and finite bond sets; separate trace scalar mass and protected-boundary admissibility (Finding 3). Original untraced definition is usable. |
| 6.2 `l:stepid` | Exact U-to-D and D-to-(3/5)delta_0 integration identities | correct | `e:moments`; k is a nonnegative integer, k<=4 or k<=2 respectively. Includes k=0. |
| 6.3 `p:pairwalk` | Finite stopped-trail expansion of a pair correlation | correct after fix | `l:stepid`, positive partition functions, induction on unused bonds; traced-network extension in Finding 3 and endpoint explanation in Finding 4. |
| 6.4 `l:response` | First-U-passage logarithmic response and uniform coefficients | correct | `e:IJ`, `l:35`, free positivity, joint conditional independence of the remaining neighbours, logarithmic-mean bounds. Only U departures are asserted in the statement. |
| 6.5 `l:exposure` | Arbitrarily ordered product exposure bound | false | Fails for an initial D site with two bonds (Finding 1). Correct with the additional initial-degree restriction used by the recursion. |
| 6.6 `d:pattern` | Radius-two template, slot ratio c(pi), P_ext | correct after fix | Specify the U kept sets and slot conventions (Finding 5); use generalized local networks, not protected global domains. |
| 6.7 `h:H1` | c(pi)>=c_s or c_t for every appropriate P_ext pattern | correct | Assumption with 0<c_s,c_t<=1; computer theorem `t:H1` and Appendix D supply the claimed instance. |
| 6.8 `l:local` | A matching local pattern bounds the inverse step ratio | correct | Positive denominators (`l:Iw`), independent-slot enlargement, `l:35`, attainable tip-mean ball, ratio-of-averages inequality. See the explicit details below. |
| 6.9 Remark, no label | All recursion passages have covered patterns, with at most 12 exceptions in T2 | correct after fix | Corrected `l:closure` and the one-defect extension in Finding 3. The exceptions are near the first trail's stopped endpoint e, not necessarily the final 12 passages of the second trail. |
| 6.10 `h:H2` | Uniform geometric bound on weighted lattice-trail sums | correct | Assumption; weights are defined for all starts and designated arrival directions. Positivity at lengths 0 and 1 forces C_V>=1 and 0<q<1. Claimed verification is `l:alm` / Section 8.2. |
| 6.11 `l:onepoint` | Exponentially small total weight of trails reaching S | correct after fix | `l:local`, H1, H2, crude 12/5 ratio bound; initial D two-bond case needs the separate 3/4 bound in Finding 1, and trace objects need Finding 3. |
| 7.1 `l:closure` | Consistency and pair-class closure under tracing/removing the live site | false | Live-D and prefix-end exceptions are missing (Finding 2). The corrected induction yields the required nonterminal closure. |
| 7.2 `h:H3` (H3') | Some fixed exposure orderings give rho(M_1)<1 | correct | `e:kernel`, nonnegative coefficients, common c_s,c_t; finiteness follows from H2 as in `l:Mtheta`. Computer input: Section 8.3 / Appendix C. |
| 7.3 `l:Mtheta` | Exponential shift moment exists and a nearby tilted kernel contracts | correct | H2, H3', shift<=n/2+1, geometric-series convergence, continuity of finite-matrix spectral radius. |
| 7.4 `t:rec` | Common H1,H2,H3' imply exponential decay of F_B,F_C and (P) | correct after fix | Corrected `p:pairwalk`, `l:exposure`, `l:closure`, `l:onepoint`; `l:response`, `l:local`, `l:Mtheta`; positive Neumann-series vector and truncated weighted supremum. The repairs do not change M or C_T. |
| 7.5 `r:typedep` | Optional type-dependent response coefficients | correct | H1 for the step, `l:response`, free positivity, and a sharper joint lower bound on E^tau[I]. All six stated constants can be justified as detailed below; not used by `t:rec`. |

## 3. Formalization notes

### Domains, masses, and stopping

1. **Use ambient lattice distance.** All distances to S are in Z², ignoring removed sites and deleted bonds. Neither an intrinsic distance in D nor a boundary enlarged by X/D sites gives the theorem stated in (P).

2. **S is the two-layer set.** The needed definition is `sec5-cut.tex:90`: S(G)={z in G: d(z,Z²\G)<=2}. If y is outside S, its entire radius-two template lies in G. Every neighbour of y has distance at least two from the complement, hence has no pinned leg. In E'=D\{y}, each has at most three present bonds. These facts are essential to Lemma 6.4; an ordinary one-layer boundary would not suffice.

3. **Types of spins differ.** U spins are on S²; D spins are on S² union {0}. Uniform bounds use |n|<=1. Every positive-degree D moment is 3/5 of the sphere moment; the degree-zero moment is 1. X sites have no variable. Define P_ab=0 when an endpoint is removed only as an explicit extension, not as evaluation of a nonexistent variable.

4. **Retain scalar trace mass.** A convenient object is `(underlying network, positive mass)`. A D-to-X departure multiplies the mass by 3/5. Expectations ignore this mass, whereas Z and R retain it. Membership statements about D_cons should refer to the underlying network.

5. **Strict positivity is needed repeatedly.** For every fixed finite set of unit pins, choose a common unit direction different from the finitely many antipodal pins. The integrand is strictly positive in a neighbourhood of the all-equal configuration. Every nonremoved site measure has positive uniform component, so Z^tau,Z^0>0. This proves that expectations, ratios and logarithms are defined, including in traced networks and artificial local templates. The empty product has partition function 1, apart from any separately stored positive trace mass.

6. **The walk sum is finite on a finite graph.** Induct on the number of unused present bonds; every step deletes its chosen bond. At a nonterminal U departure there are at most three present factors; at a D departure there are at most two initially, and at most one after an arrival. A branch without an outgoing bond is zero by the odd first moment. Show that the recursively generated completed trails coincide with the stopped trails in the original graph; removal of a D site does not discard a completed trail needing an unused incident bond. A two-bond initial D site cannot be returned through and then left again by an edge-simple trail.

7. **Boundary endpoints are retained.** A stopped endpoint e in S is never integrated by a step identity and never removed in a response-domain argument. It may lose the arrival bond. In fact first entry into S from G\S occurs at its inner layer d(e,Z²\G)=2, which has no pinned leg; nevertheless all specified leg factors should be preserved by the generalized trace convention.

8. **Specify integer domains.** Let length n, shift s, distance index d, and truncation N be natural numbers, with the F_X extension to negative integer arguments as printed. The theorem concerns integer distances. H2 as printed implies q>0 because its length-one sum is positive; state 0<q<1 directly for subsequent powers and geometric sums. Zero-length trails do not occur from x outside S to S, or between distinct u,v.

### Local patterns and ratios

9. **Make kept sets explicit.** The centre of a pattern has status U and keeps exactly the three lattice bonds other than its dropped arrival bond; present bonds among those three depend on the other ends. This is used in `app-local.tex:26` and should be explicit in Definition 6.6. Ignore slot factors at removed sites. Slots are independent boundary vectors, including artificial replacements for absent external bonds; they are not required to obey condition (C). Tips are replaced by U tips for the local comparison only, regardless of their actual status. Pattern equivalence must be equality of the two integrals up to a common positive factor and permutation/reflection of slot arguments. A D corner's dropped external leg may be filled by the averaging enlargement; do not silently identify an absent factor with a fixed unit pin.

10. **Slot enlargement has a direct inequality proof.** If Z_next>0, the inequality Z_cur>=c Z_next on all sphere-valued slots extends to ball-valued slots by separate affinity of Z_cur-c Z_next. A ball point, including zero, is a convex combination of two sphere points. This proves the ratio bound for arbitrary outside spins of norm at most one and for missing slots. Shared outside spins may be replaced by independent slots because this enlarges the feasible set. This avoids an unnecessary theorem about minimizing a multivariable linear-fractional function.

11. **The tip ball is exactly attainable.** With three unit fields, the normalized U-tip mean depends continuously on the fields, since its normalizer is at least 1/2. Three equal fields give norm 3/5. Three coplanar unit fields at 120-degree angles give zero mean. A continuous path between these triples gives every intermediate norm, and rotation covariance gives every direction. Together with `l:35`, this proves that the image is the closed ball of radius 3/5. The positive scalar normalizer factors from each tip cancel from both template integrals. The actual tips are mutually nonadjacent, so their integration can be performed separately.

12. **Free positivity extends to D sites.** Expand in Cartesian coordinates, use the even moment pairing formula at each site, and multiply positive-degree contributions by 3/5 at D sites. All surviving coefficients remain nonnegative. This supplies E^0[P_ab]>=0 and products thereof, without importing an FKG assertion for the continuous spin model.

### Response coefficients and optional refinement

13. **Conditional independence is joint here.** The remaining neighbours of y are pairwise nonadjacent, and their joint conditional density factors given all other spins. If their means have norm at most 3/5, then

\[
-27/50\le\sum_{a<b}m_a\cdot m_b\le27/25.
\]

This gives the exact intervals I in [41/50,34/25] and J in [116/125,134/125]; in the two-neighbour case I is in [22/25,28/25]. Free positivity gives I_0,J_0>=1. Pointwise I>=1/2 and J<=6/5 give the crude U-step ratio 12/5. These arguments also cover zero-valued neighbouring D spins by convex decomposition.

14. **The numerical coefficients have rigorous slack.** If L is the logarithmic mean, monotonicity gives

\[
\beta\le\frac1{3L(41/50,1)}=0.367501738\ldots,
\]

\[
\alpha\le\frac1{3L(41/50,1)}-\frac{25}{134}
=0.180934574\ldots,
\]

\[
\alpha\ge\frac{25}{102}-\frac1{5L(116/125,1)}
=0.037532633\ldots>0.0375,
\qquad
\beta'\le\frac1{3L(22/25,1)}=0.355092698\ldots.
\]

The four decimal comparisons in the manuscript were also checked with exact rational logarithm enclosures in `check_r4.py`, not just evaluated in floating point. The logarithmic mean is increasing because L(a,b)=int_0^1 a^t b^(1-t)dt. Its reciprocal also has the useful representation 1/L(a,b)=int_0^1((1-t)a+tb)^(-1)dt.

15. **The optional turn alpha bound needs more than the two separate interval bounds.** Here is a derivation of sufficient extra constraints. Set p=E^tau[P_fg] in [-9/25,9/25] and t=E^0[P_fg] in [0,9/25]. Conditional independence and Cauchy–Schwarz give

\[
I_\tau\ge I_{\min}(p):=1+\frac{p-(3/5)\sqrt{18/25+2p}}3,
\quad I_0\ge1+t/3,
\quad J_\tau=1+p/5,\quad J_0=1+t/5.
\]

Also I_tau>=c J_tau by H1. In the resulting upper bound for alpha use X(p)=max(I_min(p),c(1+p/5)). One has X(p)<=1+p/5. The reciprocal-log-mean integral shows that the upper bound decreases with t, so set t=0. For c>=3/5 the function

\[
g_c(J)=\frac1{3L(cJ,1)}-\frac1{5L(J,1)}
\]

decreases with J. For straights this gives alpha<=g_(961/1000)(116/125)<0.145217 directly. For turns take p_*=-1119/3125. On [-9/25,p_*], I_min is decreasing and I_min(p_*)>=(187/200)(1+p_*/5); on [p_*,9/25], H1 and monotonicity of g suffice. Consequently alpha<=g_(187/200)(1+p_*/5)<0.149953. The comparison at p_* follows by squaring two nonnegative rational quantities. The corresponding beta and beta' bounds follow from I_tau>=0.928c and I_tau>=c respectively. All six stated inequalities pass exact rational logarithm enclosures in `check_r4.py`. The supplied `coef.py` could not be rerun because python-flint is unavailable, but this independent argument verifies the six constants without that dependency.

### The recursion, kernel and fixed point

16. **Pair membership after removal is the substantive closure assertion.** At a regular U departure, a remaining neighbour of status D keeps its bond to y by (C), hence has at most one present bond after y is removed. U neighbours are allowed unchanged. Any two remaining neighbours are at ambient distance two with removed centre y. This establishes the exact hypotheses of P_B(E') or P_C(E'), once the corrected consistency invariant is proved. For a straight passage the non-out pair is B; for a turn it is C. With two neighbours the surviving pair contains the out-neighbour and its coefficient beta'<=bar_beta is dominated correctly by the kernel.

17. **Preexisting D sites are safely overcounted by the kernel in the recursion.** A D departure with at most one bond has lambda=0 and factor 3/5. If the lattice-history kernel calls it a first visit, it instead supplies a factor x>=1 and nonnegative response coefficients. Restrict the prescribed ordering sigma_w to the actual U departures; discarded x factors can only decrease its prefix products. The kernel revisit count is no larger than the actual D-departure count. A kernel-dead pair contains the originally removed centre or a site already left twice, so it cannot be an actual response pair. Additional initially removed sites only remove further actual pairs.

18. **The spatial shift is correct.** For any response site z,

\[
d(z,S)\ge d_0-\min(d(z,u),d(z,v)).
\]

Taking the minimum over the pair gives the shift exactly as defined in Section 7.3. Along an n-step u-to-v trail, a passage site has min(distance to u, distance to v)<=n/2, and its neighbours have this minimum <=n/2+1. Thus the shift bound used by Lemma 7.3 is valid, including pairs near an endpoint. B trails have even length at least 4 and C trails even length at least 2; no length-zero or odd-length kernel terms are needed.

19. **Kernel finiteness and continuity require a summable majorant.** For theta>q², every entry is bounded by

\[
(\bar\alpha+2\bar\beta)C_V\theta^{-1}
\sum_{n\ge1}n(q/\sqrt\theta)^n<\infty.
\]

On any closed theta interval contained in (q²,1], the same bound at its left endpoint proves uniform convergence and continuity. The orderings must be fixed independently of theta, as H3' and the programs' description require. Continuity of the spectral radius of a finite matrix then gives a theta<1 with rho(M_theta)<1.

20. **The T2 constants are adequate.** Let K=(12/5)^12 C_V/(1-q). The corrected one-point weight domination holds pointwise for each trail for both pinned and free ratios, so it also bounds max(R^tau,R^0) before summing. The first and second walks then give |T2|<=2K²q^{d(u,S)+d(v,S)}<=2K²q^{2d}. This is the displayed C_T. Bounding two separate sums alone would not justify a sum of maxima; the pointwise domination supplies the missing link.

21. **The fixed-point argument is valid without an assumed decaying supremum.** For rho(M_theta)<r<1, the vector x=sum_(k>=0)(M_theta/r)^k 1 is finite, positive, and satisfies M_theta x=r(x-1)<=r x. The truncation by min(d,N) makes Phi_N finite using F_X<=2. The inequality Phi_N<=max(2/x_min,r Phi_N+C_T/x_min) gives the claimed uniform bound. For each fixed integer d one can simply choose N>=d; no interchange of suprema and limits is necessary. The resulting A is at least 2, and theta is positive, so the exact requirements of (P) are met. Pairs at distance zero from S use the trivial bound 2.

22. **There is no additional monotonicity assumption about correlations.** Only absolute responses, free positivity, and nonnegative majorants are used. Neither pinned pair positivity nor monotonicity in pins is required. No FKG theorem for vector spins or boundary uniqueness theorem is used in Sections 6–7.

### Reproducibility of the small checks

`check_r4.py` uses Python's standard-library `Fraction`, exact sphere moments, and four-by-four matrix multiplication. For the counterexample without a boundary defect, use the basis phi=(1,n_1,n_2,n_3). A pinned outer two-leg site contributes the matrix

\[
C=\begin{pmatrix}
4/3&0&0&2/3\\
0&2/5&0&0\\
0&0&2/5&0\\
2/3&0&0&8/15
\end{pmatrix}.
\]

An axial tip contributes, after removal of its positive scalar normalizer, the field 1+(3/5)n_3. The ring's vertex matrices alternate between V_ab=int phi_a phi_b(1+(3/5)n_3)dn and V0_ab=int phi_a phi_b dn. If T=VCV0C, the normalizer is tr(T^4). With V^(i)_ab=int n_i phi_a phi_b(1+(3/5)n_3)dn and T_i=V^(i)CV0C, the leaf correlation is (1/9)sum_i tr(T_i T T_i T)/tr(T^4). Removing the fields and using C=diag(1,1/3,1/3,1/3) gives the free value. This proves the displayed rational values by finite exact arithmetic.

For the coefficient checks the script bounds -log(1-z) between sum_(k=1)^20 z^k/k and that sum plus z^21/(21(1-z)); all comparisons use rational endpoints. Decimal evaluations in its output are **numerical approximations** only; the counterexample fractions and asserted coefficient inequalities are exact. The combinatorial closure checks are exact. No full-scale certificate or memory-walk computation was rerun.

## 4. External inputs

There is no direct bibliography citation in Sections 6 or 7. Their inputs are earlier internal results, the three explicitly named computer-assisted hypotheses, and standard analysis/linear algebra. The precise uses are as follows; the original external papers and their bibliography locators are not substituted for the internal statements actually used here.

| Input, stated as used | Locator supplied by the paper | Hypotheses/use audit |
|---|---|---|
| Sphere moments: odd moments vanish; the degree-2k tensor equals the sum over pairings divided by 3·5·...·(2k+1). | `sec5-cut.tex:13–17`, `e:moments`; derived there from a standard Gaussian formula, with no external locator. | Correct for normalized uniform measure on S². The step identity needs degrees through five (odd degree five vanishes); D positive-degree moments are multiplied by 3/5. |
| Free expectations of products of scalar products are nonnegative. | `sec5-cut.tex:19`; extension at `sec6-walks.tex:21`. | Applied only to free laws, with nonnegative bond expansion coefficients and uniform/D site moments. No arbitrary-pin positivity is assumed. |
| A U-site law with at most three factors 1+n·a, |a|<=1, has mean of norm at most 3/5; the D analogue is a convex mixture with an atom at zero. | Lemma `l:35`, `sec5-cut.tex:23–32`; extension at `sec6-walks.tex:21`. | The lemma is written for unit fields and fewer factors; ball fields follow by convex decomposition. Response neighbours have no legs and degree at most three because y lies outside the two-layer S. Actual tips have at most three factors besides their bond to the template. These uses stay within the extended hypotheses. |
| Nonadjacent spins are jointly conditionally independent given the other spins in a product-factor nearest-neighbour Gibbs measure. | `sec5-cut.tex:21`; `sec6-walks.tex:21`. | Correct by factorization. Remaining neighbours of one square-lattice site are pairwise nonadjacent; zero atoms and trace scalar masses cause no difficulty. |
| H1: for every P_ext pattern and every one of its twenty independent unit slot vectors, Z_cur >= (961/1000)Z_next for straights or (187/200)Z_next for turns. | `t:H1`, `sec8-computer-assisted.tex:51–59`; proof `app-local.tex:302–304`, positivity `l:Iw` at lines 17–26. | The local-ratio use is within the claimed pattern class after the corrected closure/slot conventions. Ball fields, missing slots and actual tip statuses are reduced by `l:local`; no claim of matching arbitrary global configurations to a fixed list without that reduction is needed. Full certificate verification belongs to this computer input and was not rerun here. |
| H2: sum of W(w) over all n-step lattice trails with fixed start and designated arrival direction is <=C_V q^n, uniformly, for 0<q<1. | `h:H2`, `sec6-walks.tex:137–139`; `l:alm` and certificate, `sec8-computer-assisted.tex:13–33`; claimed q<=0.98075. | Domain trails form a subset of lattice trails. Initial D two-bond departures require Finding 1's extra comparison; then the stated weights dominate. The convergence proof uses only existence of finite C_V and q<1, not the optional numeric C_V<=153. |
| H3': with the same c_s,c_t and bar_alpha=0.18094, bar_beta=0.36751, some theta-independent family of orderings has rho(M_1)<1. | `h:H3`, `sec7-recursion.tex:45–47`; `sec8-computer-assisted.tex:35–45`; `p:tail`, `app-tail.tex:94–115`, claimed rho<=0.98779. | Correct input for the kernel defined in `e:kernel`. The main proof uses the uniform coefficients, not Remark 7.5's smaller values. Short-trail optimal orderings and longer-trail straights-first orderings are fixed independently of theta. The tail calculation itself was not recertified in this lane. |
| Positive logarithmic mean is increasing in both variables; |a-b|<=|log a-log b|max(a,b) for a,b>0. | Used without external citation at `sec6-walks.tex:73–79,96`. | Correct under the strict positivity established above. Exact rational decimal-bound checks are supplied in the audit script. |
| A positive weighted ratio of integrals is at least the infimum of the pointwise ratios; separate affine inequalities extend from products of spheres to products of balls. | Used without external citation at `sec6-walks.tex:124–126`; also `c:reduce`, `app-local.tex:68–77`. | Requires strictly positive local denominators and nonnegative exterior weights. Both hold; zero exterior weights may be discarded. The tip normalizers are positive. |
| Spectral radius of a finite matrix is continuous in its entries; rho(A)<1 implies convergence of sum A^k. | Used without external citation at `sec7-recursion.tex:54,86`. | Applies to finite real 2×2 matrices after the H2 summability proof. Nonnegative entries make the Neumann-series vector positive; irreducibility is unnecessary. |
| Fubini/Tonelli, finite-dimensional conditional densities, elementary geometric-series and Lipschitz distance inequalities. | Used throughout the two sections, without external locators. | Finite-volume densities are bounded and integrable; trace sums in a domain are finite and kernel majorants are nonnegative. The only infinite series used analytically have the explicitly proved geometric majorant. |

The MOS94/MO94 mixing theorems, FKG71 in the optional closed-form H1 proof, representation-theoretic H1 certificate lemmas, and the Knabe criterion are background or upstream/downstream results, not additional direct premises in the conditional pair-recursion proof. Their independent validity is outside this lane. Acceptance of the Section 8 computer inputs is separate from repairing the false auxiliary assertions above.
