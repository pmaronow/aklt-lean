VERDICT: SOUND

# Scope

I read all LaTeX sources of the paper and consulted the PDF for context. I checked Section 4 (`sec4-periodic-gap.tex`) and Appendix A (`app-finite.tex`) line by line, including the concluding proof of the main theorem in Section 4. File and line references below refer to the supplied source, under `/home/ubuntu/aklt/review/REF2/paper/`.

The verdict covers these statements and their proofs, and the use of results from the rest of the paper under their stated hypotheses. It does not independently verify the computational witnesses underlying Section 8: those results are outside the assigned part, and their archived data are not among the permitted inputs. No additional file outside the supplied paper was read. Inputs were not modified; computations used one process.

# Numbered findings

1. **No Critical, Major, or Minor defect identified.** The statements in the assigned part are well posed under the paper's conventions, and their conclusions follow from the stated hypotheses. In particular, I found no failed claim requiring a LaTeX repair. The important proof obligations and boundary cases are recorded below so that this verdict is auditable.

# Detailed audit

## Windows and the stopped coupling

**Definitions 4.1–4.2:** `sec4-periodic-gap.tex:10`, `d:shells`; `sec4-periodic-gap.tex:31`, `d:W`. The shells and windows are finite subsets of the same physical square, and comparisons always use each site's own alphabet. The metric for corner proximity is explicitly identified as ambient infinity distance in `sec5-window.tex:11`. Property (W) covers arbitrary admissible boundaries for the shell volume, including the random induced boundaries used later. It does not require those boundaries to agree. Indices above the real number `s` are not covered by (W), and the proof respects that restriction.

**Lemma 4.3:** `sec4-periodic-gap.tex:56`, `l:stopped`.

- The bound on `u` implies exactly the size hypothesis of Lemma `l:shellgeom` (`sec5-window.tex:27`). Its conclusions apply through `i_1`, including the final surgery index `h+1`. The separator assertion applies to all indices, while the estimate on `A_i` is used only at nonexceptional indices.
- Partial one-site conditionals are averages of fully conditional probabilities. The chain rule therefore gives assignment probability at least `alpha^{|A|}`. Full support supplies every denominator; the empty assignment has probability one.
- For every fixed input pair, maximal coupling on `B_i`, conditional completion, and the subsequent independent heat-bath resampling of `A_i` have the two required conditional marginals on `F_i`. The branch chosen using agreement on the preceding separator has those same marginals. Lemma A.3 therefore preserves the original full laws at every step, despite dependence of the joint coupling on both input configurations.
- When the preceding separator agrees, consistency and range one identify the two laws on `F_i`: every relevant interior exterior site is in `D_{i-1}`, and the changed original exterior site `y` is too far away. This uses precisely the stated infinity-range assumption.
- At a nonexceptional trial index `i <= h <= s`, (W) gives agreement on `B_i` with probability at least `p_0`. Independently resampling the two copies of `A_i` to one fixed assignment costs at most the factor `alpha^{2|A_i|}`. Since `|A_i| <= 8 l_0` and `alpha <= 1`, the resulting success probability is at least `delta = p_0 alpha^{16 l_0}`.
- The trial set excludes both an exceptional trial and its predecessor. Thus at least `h-3` trials have an unskipped successor. A successful separator at index `i` is followed by identical resampling on `F_{i+1}`. For every later index `j >= i+2`, the inequality `floor((j-1)s) > is` puts `D_{j-1}` inside that already agreeing region. Consequently agreement there persists through every later surgery.
- The construction at `h+1` needs no success estimate from (W). In particular, the proof remains valid when `h+1 > s`. Conditional failure estimates are applied successively to histories; independence between trials is not assumed.

The endpoint cases `h=4`, `delta=1`, empty `A_i` or `B_i`, an empty resampled volume, singleton alphabets, and a changed exterior site beyond range one are all covered. Since `h-3 >= 1`, the case `delta=1` introduces no zero-to-zero power.

**Corollary 4.4:** `sec4-periodic-gap.tex:200`, `p:surgery`. With `h=floor(s)`, the target set at distance greater than `s^2` is contained in `Q_h` because `hs <= s^2`. Coupling bounds total variation, and `h-3 >= s-4` has the correct direction for a base between zero and one. The separate treatment of `delta=1` is valid because `s-4 > 0`.

**Lemma 4.5:** `sec4-periodic-gap.tex:230`, `l:hamming`. The four scale conditions are simultaneous lower bounds by finite constants, so an integer `n` exists before any torus or boundary is chosen. With `M=n^8`, one has `s=n^2` and the permitted choice `h=n`. The proof uses one full-law coupling to bound the entire Hamming cost. Its near region has radius `n^3`; its exceptional-event probability is at most `(1-d_0)^{n-3}`.

The degree-20 binomial estimate is valid for `n >= 44`: all twenty factors in the binomial coefficient are positive and at least `n-22 >= n/2`. The numerical conditions give, separately,

\[
25n^6\le n^8/2000,\qquad
25n^{16}(1-d_0)^{n-3}
 \le \frac{25\,2^{20}20!}{d_0^{20}n^4}
 \le n^8/2000.
\]

Thus their sum is at most `M/1000`. Truncating `d_0` at `1/2` keeps all reciprocal operations legitimate even when `delta=1`.

## Periodic block criterion and assembly

**Theorem 4.6:** `sec4-periodic-gap.tex:314`, `t:periodic`. Reduction modulo each period is injective on the offset square of side `2M+3`, including at the smallest allowed period. The exact multiplicities are

\[
T_M=(2M+1)^2,\qquad
S_M=(2M+3)^2-(2M+1)^2=8M+8.
\]

These count centre labels; no invariance of the probability law is required. Corner offsets are legitimately included for an infinity-range specification. For a single initial discrepancy, the three classes of labels have output costs zero, at most `1+K`, and one. Hence the averaged cost is at most `1-(T_M-S_M K)/(LN)`. The required contraction parameter lies in `(0,LN]`, as Lemma A.6 requires.

Lemma A.5 compares the unnormalized block generator with the conditional single-site generators using multiplicity `T_M`. This gives precisely `g(1-S_M K/T_M)`, with no missing number-of-blocks or block-volume factor. The constant calculation is exact:

\[
\frac{S_M K}{T_M}
 \le \frac1{500}\left(1-\frac1{(2M+1)^2}\right)<\frac1{500}
 \quad\text{if }K\le M/1000.
\]

The case `L=N=2M+3`, where every centre is in one of the first two classes, is included. One-point product spaces satisfy both Poincare conclusions by the stated convention.

**Theorem 4.7:** `sec4-periodic-gap.tex:404`, `t:mainW`. All external results are invoked within their hypotheses:

| External result | Hypotheses checked at the use in Section 4 |
|---|---|
| `l:planeenergy`, `sec3-quantum-frames.tex:691` | The boundaries are admissible letters of proper-colouring frames. Its finite-energy bound is not applied to arbitrary unit pins. Consistency, positivity, nearest-neighbour dependence and `alpha=12^{-1}r_b^4` are uniform over precisely the needed family. |
| `l:colour`, `sec3-quantum-frames.tex:434` | Both periods are at least `L_0=2M+3 >= 3`. The explicit colouring is valid for either parity. Its periodic pullback is proper on the plane. |
| `l:boxlift`, `sec3-quantum-frames.tex:801` | The radius is an integer `M >= 1`, and both periods are at least `2M+3`. Thus the entire one-neighbourhood injects, internal and crossing bonds correspond, and every affected exterior site has a unique exterior lift. |
| `l:threeframes`, `sec3-quantum-frames.tex:341` | The alphabets are the prescribed uniform antipodal frames. The local sign change stays within each alphabet and preserves its weight. Also `0<r_b<1`. |
| `l:star`, `sec3-quantum-frames.tex:223`; `t:QD`, `sec3-quantum-frames.tex:646` | The periods are at least three and the torus colouring is proper. The rate convention is one heat-bath update per site, so `sum_x H_x=2H` gives the stated factor `g_star/2`. |
| `p:toruskernel`, `sec3-quantum-frames.tex:191` | Its only period requirement, `L,N >= 3`, holds; it supplies nonzero `B` and identifies the positive spectrum with the restriction to `B` perpendicular. |

The gauge is defined on each lifted square, so no global bipartite colouring of an odd torus is used. Identical extensions of unneeded exterior plane letters are allowed by the finite alphabets and range one. The sign map for the two compared boundary fibres is the same coordinatewise map, so it preserves their coupling's Hamming cost.

The internal edge count is `2(2M+1)(2M)`. Boundary factors are absorbed into positive site weights, giving the conditional block gap `g_M=r_b^{2(2M+1)(2M)}`. The final constants are therefore

\[
L_0=2n^8+3,\qquad
c=\frac{499}{1000}g_\star r_b^{2(2n^8+1)(2n^8)}>0.
\]

They depend only on the fixed frames and the constants witnessing (W).

**Assembly of Theorem 1.2:** `sec4-periodic-gap.tex:537`, proof of `t:main`. Theorem `t:inputs` (`sec8-inputs.tex:270`) supplies the same thresholds `961/1000` and `187/200` used by `t:rec` (`sec7-recursion.tex:1008`), with `C_V=10 >= 1`, positive `q<1`, and the specified type-dependent kernel and fixed orderings. Its conclusion has exactly `A >= 2` and `0<theta<1`, the hypotheses of `t:cutMOS` (`sec5-window.tex:696`). That theorem gives one `W(64,p_0,M_star)` uniformly over all proper plane colourings and translates, as Theorem 4.7 requires. There is no missing uniformity or parity hypothesis in this chain.

## Appendix A

**Lemma A.1:** `app-finite.tex:22`, `l:CE`. The fibre sums establish idempotence, self-adjointness, preservation of constants and expectation. Orthogonal decomposition proves both variance identities with complex conjugation in the proper place. Empty coordinate sets and the empty product obey the same identities. Repeated block labels contribute repeatedly to the quadratic form.

**Lemma A.2:** `app-finite.tex:68`, `l:finitecoupling`. The explicit residual coupling is nonnegative, has the claimed marginals and has zero residual diagonal mass. Division by `1-t` occurs only for `t<1`. Zero-probability values in a sampled marginal cannot occur and can be assigned arbitrary conditional completions. The pointwise Hamming bound is coarse but valid. Marginal contraction and common-probability domination are proved correctly, including endpoint values of the domination parameter.

**Lemma A.3:** `app-finite.tex:132`, `l:surgery`. For a first-output test function, the conditional expected value depends only on the first input's complement; integrating the coupling gives the original first marginal. The second marginal is identical in form. Dependence of the joint resampling kernel on both full inputs does not invalidate this argument. Finite compositions and the empty resampling are covered.

**Lemma A.4:** `app-finite.tex:163`, `l:density`. Both conditional variance and full variance are expressed as minima over the appropriate complex function spaces. Taking a minimum after the lower density comparison proves the Dirichlet inequality in the stated direction. The upper variance comparison uses the admissible constant `pi(f)`. For a product law, the commuting conditional projections give orthogonal increments whose squared norms sum to the variance. Thus the comparison factor is `m/M`. In the frame application, the reference measure is a normalized product probability and all fixed boundary factors are positive. Only internal edges enter the density ratio, which is exactly `r_b^{|E(Q)|}`.

**Lemma A.5:** `app-finite.tex:253`, `l:comparison`. Further conditioning inside a fixed block fibre fixes exactly the original complement of a site. Integrating its Poincare inequality therefore gives the original one-site Dirichlet term. Summing over labels gives multiplicity `t_max`; division is by the strictly positive `c g`. Nonempty blocks ensure that `t_max` is defined. Singleton fibres and repeated blocks cause no exception.

**Lemma A.6:** `app-finite.tex:297`, `l:contraction`. Coordinate-change paths exist for the full product even with site-dependent alphabets. On a nontrivial product, a nonconstant real function has strictly positive Hamming Lipschitz seminorm. The assumed couplings contract this seminorm. The mean-zero subspace has a real orthonormal eigenbasis for the reversible operator `P`; each eigenvalue there satisfies `|lambda| <= 1-c/A`. Expansion in that basis yields the asserted unnormalized Poincare gap. The proof handles `c=A`, the one-point product, and complex functions separately and correctly.

# Statement table

“Sound” in this table includes checking the stated external dependencies, rather than independently reproving the other sections' theorems.

| Label; source | Content | Verdict | Dependencies |
|---|---|---|---|
| `d:shells`; `sec4-periodic-gap.tex:10` | Physical square, shells, strip split and exceptional indices | Sound definition | Plane lattice and distance conventions; corner metric specified in Section 5 |
| `d:W`; `sec4-periodic-gap.tex:31` | Uniform total-variation window inequality | Sound definition | `d:shells`, `d:framemodel`, full support |
| `l:stopped`; `sec4-periodic-gap.tex:56` | Full-law coupling with failure at most `(1-delta)^{h-3}` on `Q_h` | Sound | (W), finite energy, consistency, range one, `l:shellgeom`, A.1–A.3 |
| `p:surgery`; `sec4-periodic-gap.tex:200` | Outer marginal TV at most `(1-delta)^{u^{1/4}-4}` | Sound | `l:stopped`, A.2, floor and power monotonicity |
| `l:hamming`; `sec4-periodic-gap.tex:230` | A fixed radius `M=n^8` with full-law Hamming cost at most `M/1000` | Sound | `l:stopped`, positive `d_0`, finite binomial estimate, Archimedean scale choice |
| `t:periodic`; `sec4-periodic-gap.tex:314` | Block gap `T_M-S_MK`; site gap at least `g(1-S_MK/T_M)` | Sound | Exact torus label counts, conditional range one, A.5–A.6 |
| `t:mainW`; `sec4-periodic-gap.tex:404` | (W) implies a uniform positive quantum gap and the kernel identity | Sound | `l:hamming`, `t:periodic`, frame finite energy and antipodality, colouring, box lift, `t:QD`, `l:star`, `p:toruskernel` |
| `t:main`, concluding proof; `sec4-periodic-gap.tex:537` | Exact inputs imply the main theorem for all stated periods | Sound assembly | `t:inputs` → `t:rec` → `t:cutMOS` → `t:mainW`; independent `p:toruskernel` |
| Appendix preamble; `app-finite.tex:4` | Positive finite-product conditionals, conditional variance and operator Poincare convention | Sound definitions | Nonempty finite alphabets; positive complement marginals |
| `l:CE`; `app-finite.tex:22` | Conditional expectations are orthogonal projections; variance identities | Sound | Finite fibre sums and orthogonal decomposition |
| `l:finitecoupling`; `app-finite.tex:68` | Maximal coupling, marginal contraction, completion, Hamming and overlap bounds | Sound | Finite probabilities; residual coupling and finite conditioning |
| `l:surgery`; `app-finite.tex:132` | Conditional resampling preserves full marginals, also under composition | Sound | `l:CE`, consistency, stipulated conditional output marginals |
| `l:density`; `app-finite.tex:163` | Density comparison, product Poincare inequality, internal-edge frame bound | Sound | Variational projections, product commutation; `d:framemodel`, `l:threeframes` for the application |
| `l:comparison`; `app-finite.tex:253` | Conditional site gaps plus block gap imply site gap at least `c g/t_max` | Sound | Conditional Poincare hypotheses, `l:CE`, labelled incidence count |
| `l:contraction`; `app-finite.tex:297` | Adjacent-output Hamming contraction implies block gap at least `c` | Sound | Product-coordinate paths, `l:CE`, finite real spectral theorem |

# Exact checks performed

These finite checks supplement the proofs; they do not establish universal statements by sampling.

- **Shell geometry:** 741 exterior boundary placements, covering 182,913 shell indices. Integer radii included the thresholds for `l_0=1` and `l_0=64`, values immediately above and below perfect fourth powers, exterior corners, and positions around the strict exceptional-index boundary. Computations used `k_i=floor((i^4 u)^{1/4})` by integer square roots. Corner distance `j<s/3` was tested exactly by `81 j^4<u`. Every case satisfied `|I_0|<=1`, `D_i` contained in `F_i`, the nonexceptional parallel-side clearance and `|A_i|<=8 l_0`.
- **Torus geometry:** all 192 choices with `1<=M<=12` and each period in `{2M+3,...,2M+6}`. Exact enumeration verified block incidence, exterior one-neighbour incidence, and internal nearest-neighbour edge counts. This includes minimum periods and all parity combinations. Fraction arithmetic verified the displayed `1/500` identity.
- **Tail arithmetic:** exact binomial and rational tail inequalities for `n=44,45,224,1000` and `d=1/2,1/10,1/100`; also checked the assembly input ranges and the factor `(1/2)(499/500)=499/1000`.
- **References:** all 48 cross-references in the two assigned source files resolve, and the supplied paper has no duplicate LaTeX labels.

# Formalization notes

1. **Use Poincare inequalities as the primary statements.** A one-point product has no positive-variance function. Encoding its gap as an ordinary real infimum without the paper's `+infinity` convention changes the statement. The universal quadratic-form inequalities avoid this issue throughout Appendix A and Theorem 4.6.
2. **Separate the generic finite tools from their frame application.** Section 3 uses A.4's generic density comparison, while A.4's final frame application uses frame facts from Section 3. The generic proof is independent of those facts, so there is no mathematical cycle. Lean modules should reflect that separation. The coherent-state reference weight of total mass `5^{|Lambda|}` is also distinct from A.4's normalized product probability.
3. **Model alphabets as a dependent finite product.** Every equality in a Hamming comparison is at the same site. Reindexing the lifted block and applying the antipodal permutation are explicit equivalences; comparing letters at different colours is unnecessary.
4. **Construct the stopped process with a deterministic number of kernels.** Each kernel must have the required marginals for every input pair. Prove the success estimate pointwise in that pair, then sum over histories of positive mass. This avoids assuming that conditioning on earlier coupling successes preserves the original volume marginals.
5. **Retain the extra surgery and the trial set.** The final kernel is indexed by `h+1`, and trials require both `i` and `i+1` to be nonexceptional. Omitting either detail would lose the persistence argument or the exponent. The construction at `h+1>s` uses existence of a maximal coupling, not (W).
6. **Keep the integer/real distinctions explicit.** Shell indices, radii and lattice coordinates are integers; `s=u^{1/4}` is real. General Lemma 4.3 uses floors, while the assembly specialization `M=n^8` has `s=n^2` and integral radii `k_i=i n^2`. Split off `delta=1` before using real powers or reciprocal tail bounds.
7. **Count labelled translates.** Use the injective offset maps on intervals of lengths `2M+1` and `2M+3`, without assuming any symmetry of the law. Keep the normalized averaging operator `P` separate from the generator `LN(I-P)` until applying A.6, and use multiplicity `T_M` in A.5.
8. **The Lipschitz maximum needs the nontrivial-product case.** For `|Omega|>1`, the set of distance-one pairs is nonempty and coordinate paths prove that zero seminorm means constancy. Diagonalize on the real mean-zero space; extend the resulting inequality to complex functions afterward.
9. **Keep all scales as arbitrary-precision mathematical numbers.** The selected `n`, hence `M` and `L_0`, can be extremely large. Their role is existential and their positivity is established before the periods are chosen. No feasible machine-size interpretation of these bounds is required.
10. **The final Lean theorem still has the stated external dependencies.** The numerical witness proofs in Sections 8 and Appendices C–D are separate obligations. In the present part, their thresholds, kernel, orderings, `C_V`, `q`, and the uniformity of the resulting (W) match correctly. The two written proofs of `t:main` can be represented by one theorem after its dependencies are available.

# ORCH-SUMMARY

- Verdict: SOUND for Section 4 and Appendix A, with external theorems used as stated.
- Critical: 0; Major: 0; Minor: 0. No LaTeX repair required.
- Read the whole paper; checked every assigned statement and proof.
- Stopped coupling preserves marginals and supplies at least `h-3` persistent trials.
- The extra surgery at `h+1` needs no window estimate beyond its stated index range.
- Hamming bound, degree-20 tail estimate and `M/1000` constants are valid.
- Periodic label counts and rate normalization give the claimed `499/500` factor.
- Local lifted gauges handle odd periods under exactly `L,N>=2M+3`.
- Assembly yields `c=(499/1000)g_star g_M>0` with period-independent constants.
- Appendix A includes complex functions, empty products and singleton spaces correctly.
- Exact checks: 182,913 shell indices, 192 torus cases, rational constants and all assigned references.
- Computational witness data outside the permitted paper inputs were not independently checked.
- Principal Lean issues: one-point gap convention, finite coupling kernels, floors, and dependency/module order.
