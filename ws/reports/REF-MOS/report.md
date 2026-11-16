VERDICT: SOUND WITH FIXES

The proof of the main implication, including its constants and its application to manuscript Theorem 4.10, is sound. One minor hypothesis omission in the standalone Theorem 6.3 should be corrected: explicitly require a positive lower bound $\alpha$. Theorem 1.1 already supplies this hypothesis, so the correction changes no constants, argument, or application. I found no Critical or Major defect.

The replacement supplies exactly the uniform box input used by Section 3. It does not prove the full statements of manuscript Theorems 4.3–4.4 or its present Corollary 4.9 for arbitrary compatible sets. The appendix correctly acknowledges this distinction. The statement of manuscript Theorem 4.10 survives unchanged; Corollary 4.9 and the proof of Theorem 4.10 require the edits described below.

Local references below distinguish appendix statement numbers from manuscript numbers. The inputs reviewed were [proof.tex](/home/ubuntu/aklt/review/REF-MOS/proof.tex), all of [manuscript Section 4](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec4-mixing-to-gap.tex), [Section 3](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec3-knabe.tex), [Section 5](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec5-cut.tex), and the model definitions, positivity, normalization, and comparison statements needed from [Section 2](/home/ubuntu/aklt/manuscript/bundle/manuscript/sec2-frames-Q.tex). No other local source material was read. No sub-agents were used; computations ran serially on one core.

**Numbered finding.**

1. **Minor — make positivity explicit in the standalone square criterion.** Location: appendix Theorem 6.3, [lines 678–691](/home/ubuntu/aklt/review/REF-MOS/proof.tex:678), especially its opening sentence and equation (21).

   **Exact claim:** “Let a strictly positive range-one specification on $\mathbb Z^2$ have uniform single-site conditional lower bound $\alpha$,” followed by $g=\alpha^{v+1}/v$ and $\operatorname{Var}_\mu f\le(1000/g)\mathcal D_W(f)$.

   **Why the literal statement fails:** positivity of the probabilities does not make an arbitrary stated lower bound positive. Zero is also a uniform lower bound. For independent fair binary spins, $\mathcal K(M,0)$ holds, and $\alpha=0$ satisfies the lower-bound wording, but $g=0$. The displayed reciprocal is then undefined in ordinary real arithmetic; with Lean's totalized real division it becomes zero, making the asserted inequality false for a nonconstant function. This is a missing hypothesis in a standalone statement, rather than a defect in the argument at its intended inputs.

   **Repair:** write “with uniform single-site conditional lower bound $\alpha\in(0,1]$.” The upper bound is automatic once $\alpha>0$ is a lower bound for probabilities, but stating the interval makes every subsequent application direct. Theorem 1.1 already assumes precisely this interval, and every application of Theorem 6.3 here uses it. With this amendment, its proof is complete.

The following statement table covers all 23 numbered theorem, lemma, corollary, definition, and remark statements in the appendix. “Sound” for a downstream statement includes the explicit hypothesis amendment in Finding 1; its actual applications already meet that hypothesis.

| Appendix statement; source label; lines | Content | Verdict | Dependencies |
| --- | --- | --- | --- |
| Theorem 1.1; thm:main; 56–91, 778–785 | Window estimate implies a gap at least $m=\alpha^{(4n^8+1)^2+1}/[1000(4n^8+1)^2]$ on every translated rectangle with both sides at least $4n^8+1$, under every boundary condition. | Sound. All scale and positivity conditions are sufficient. | Lemma 2.1; Lemma 7.2; Theorem 6.3 with positive $\alpha$; the explicit scale choice. |
| Lemma 2.1; lem:spec; 134–162 | Positivity, finite-volume consistency, range-$r$ Markov property, $\alpha_\Phi=q^{-1}e^{-2B}$, and assignment probability at least $\alpha^{\#A}$ under partial conditioning. | Sound. | Finite alphabet, real finite-range potential, translation invariance for the common $B$, cancellation of constant terms, finite conditioning and chain rule. |
| Lemma 2.2; lem:CE; 175–208 | Conditional expectations are self-adjoint orthogonal projections; Dirichlet form and total-variance identities; summing over a block list allows repetitions. | Sound. | Strictly positive probability on a finite product; grouping sums by the complement of a block. |
| Lemma 2.3; lem:coupling; 225–254 | Maximal coupling, minimal disagreement characterization of TV, marginalization, and the TV-to-Hamming bound. | Sound, including zero residual mass and empty marginals. | Finite probability sums; conditional completion on sampled fibers. |
| Lemma 2.4; lem:surgery; 256–271 | Pair-dependent conditional resampling on a fixed set preserves both prescribed Gibbs marginals. | Sound. The freedom to choose the coupling separately for each input pair is legitimate. | Lemmas 2.1–2.2; each marginal of the kernel depends only on its own input. |
| Lemma 3.1; lem:smallgap; 276–318 | A $t$-site positive product-space law with finite energy $\alpha$ has single-site gap at least $\alpha^{t+1}/t$. | Sound; conservative bound. | Partial-conditioning/chain-rule argument from Lemma 2.1; conditional variance expansion; ordered coordinate paths; Cauchy–Schwarz. |
| Lemma 3.2; lem:comparison; 320–342 | Fiberwise block gaps at least $g$ and unnormalized block gap at least $c$ imply single-site gap at least $cg/t_{\max}$. | Sound, including repeated blocks. | Lemma 2.2; fiber Poincaré inequalities; equality of the fiber and original one-site conditional kernels. |
| Definition 4.1; def:window; 371–382 | Uniform window TV bound for integer $u\ge M_\star$, $2\le i\le u^{1/4}$ outside $I_0$, and arbitrary exterior letters. | Well-posed and matches manuscript d:W in the application. | Shell definitions (13); finite-boundary specification. Restricting full exterior configurations to the finite boundary is equivalent by Lemma 2.1. |
| Lemma 4.2; lem:geometry; 389–441 | Explicit threshold $M_{\rm g}=\max(16,6(l_0+1))^4$ gives at most one exceptional index, $\#A_i\le8l_0$, shell containment, and the precise internal boundary of $F_i$. | Sound, including nonintegral $u^{1/4}$, corner exterior sites, and diagonal range-one interactions. | Integer radii; the $\ell^\infty$ geometry; $s\ge16$ and $s\ge6(l_0+1)$. No mixing input. |
| Lemma 4.3; lem:stopped; 443–517 | A coupling agrees outside radius $hs$ except with probability at most $(1-\delta)^{h-3}$, where $\delta=p_0\alpha^{16l_0}$ and $4\le h\le\lfloor s\rfloor$. | Sound. No independence of successive successes is assumed. | Lemmas 2.1, 2.3, 2.4, 4.2; Definition 4.1; a finite sequence of history-dependent kernels and conditional failure bounds. |
| Corollary 4.4; cor:originalprop; 519–533 | Recovers the manuscript surgery proposition with radius $u^{1/2}$ and exponent $u^{1/4}-4$. | Sound, including $\delta=1$ and an exterior disagreement beyond range one. | Lemma 4.3 with $h=\lfloor s\rfloor$; marginalization; monotonicity of powers with base in $(0,1)$; equality of the measures in the far case. |
| Lemma 5.1; lem:contraction; 547–581 | An adjacent-input coupling with one-step Hamming contraction $1-c/A$ yields unnormalized block gap at least $c$. | Sound. Also covers a one-point product space. | Lemma 2.2; coordinate-path Lipschitz bound; finite-dimensional real self-adjoint diagonalization. |
| Lemma 6.1; lem:count; 590–667 | Clamped, untruncated squares of radii $M,\ldots,2M$ have $4M^3\le T_x\le1000M^3$, $S_x\le1000M^2$, and $A=(M+1)(N_1+L)(N_2+L)$. | Sound at minimal side lengths, at coincident clamping endpoints, and without divisibility assumptions. | Integer interval counts, endpoint preimages, injectivity of $u\mapsto2u+1$. |
| Definition 6.2; def:Kcriterion; 669–676 | $\mathcal K(M,K)$ asks for a Hamming-cost bound on every translated square of every integer radius in $[M,2M]$, for one exterior-site disagreement. | Well-posed. The radius interval and all placements are essential. | Finite Gibbs laws and Hamming distance. |
| Theorem 6.3; thm:criterion; 678–721 | $\mathcal K(M,K)$ with $K\le M/1000$ gives rectangle gap at least $g/1000$. | Sound after the explicit positivity hypothesis in Finding 1. Proof and constants are correct at positive $\alpha$. | Consistency and range-one Markov property; Lemmas 3.1, 3.2, 5.1, 6.1; Definition 6.2. |
| Lemma 7.1; lem:tail; 726–742 | $(1-d)^{n-3}\le2^{20}20!/(d^{20}n^{20})$ for $0<d\le1/2$ and integer $n\ge44$. | Sound, including $n=44$. | Finite binomial expansion; $n-22\ge n/2$. |
| Lemma 7.2; lem:windowK; 744–776 | The main theorem's scales give $\mathcal K(n^8,n^8/1000)$. | Sound. Referring to Theorem 1.1's hypotheses does not use its conclusion. | Lemmas 4.3, 2.3, 7.1; all four scale conditions in (1); translation invariance. |
| Remark 7.3; rem:stopping; 787–798 | Earlier stopping improves the exceptional-region area from order $u$ to order $n^6$ at $u$ of order $n^8$. | Correct. The original surgery proposition alone does not give the Hamming estimate needed here. | Lemmas 4.3 and 7.2; area bounds for $\ell^\infty$ balls. |
| Corollary 8.1; cor:range; 803–847 | Blocking into $r\times r$ cells gives range one and, assuming the blocked window estimate, physical-site gap at least $(\alpha^{r^2+1}/r^2)\widehat m$ on translated rectangles with sides divisible by $r$. | Sound. It explicitly assumes the window estimate for the actual blocked specification. | Lemma 2.1; regrouping interaction terms; Theorem 1.1; Lemmas 3.1–3.2 with multiplicity one; translation invariance. |
| Corollary 9.1; cor:twooffsets; 859–882 | Uniform gaps on every sufficiently large translated cell rectangle, simultaneously for both offsets, using a maximum threshold and minimum gap. | Sound. | Theorem 1.1 twice; the manuscript's real, translation-invariant range-one cell potentials with alphabet size $57600$. |
| Lemma 9.2; lem:physical; 884–914 | For either fixed cell partition, physical-site gap is at least $c_0=\beta^5/4$ times cell gap. | Sound. All physical letters and all permitted neighboring letters have positive weights. | Manuscript e:icodod and e:muDW; Lemmas 3.1–3.2 on disjoint four-site cells. |
| Corollary 9.3; cor:boxinput; 916–960 | Every placement and exterior configuration of the chosen even physical box has gap at least $c_0m_0$; hence $\lambda(\mu_D)\ge c_0m_0/2$ and the quantum gap is at least $g_\star c_0m_0/4$. | Sound. The kernel conclusion follows from the already separate manuscript t:QD. | Corollary 9.1; Lemma 9.2; torus lifting and parity identification; manuscript Theorem 3.1 (t:K), t:QD, and e:QDrot. |
| Remark 9.4; unlabelled; 962–976 | Replaces the combined dependency chain, not the full individual mixing/compatible-set theorems; explains the changed box-size choice. | Correct and necessary for insertion. | Corollaries 9.1 and 9.3; inspection of the actual use of manuscript c:gapcell in t:mainW. |

For completeness, the following register covers every numbered equation. Equation numbering is global in this source, not section-based.

| Equation; source label | Content checked | Verdict and dependencies |
| --- | --- | --- |
| (1); eq:nchoice | Four scale requirements on $n$. | Sufficient and simultaneously satisfiable; the displayed ceiling formula is valid because all arguments are positive and all constraints increase with positive $n$. |
| (2); eq:constants | $M=n^8$, $L=4M+1$, $v=L^2$, $g=\alpha^{v+1}/v$, $m=g/1000$. | Correct; $g,m>0$ under Theorem 1.1's hypotheses. |
| (3); eq:mainPI | Final rectangle Poincaré inequality. | Correct consequence of Lemma 7.2 and Theorem 6.3 at positive $\alpha$. |
| (4); eq:B | $B$, $q$, and the explicit lower bound $\alpha_\Phi$. | Correct; only finitely many nonzero terms contain a given site. |
| (5); eq:spec | Finite-volume Hamiltonian and Gibbs law. | Correct, with zero interaction terms omitted from the written sum; only letters in $V\cup\partial_rV$ are needed. |
| (6); eq:assignment | Conditional prescribed-assignment bound. | Correct by averaging full one-site conditionals and the finite chain rule. |
| (7); eq:projection | Dirichlet form equals expected conditional variance and squared projection error. | Correct finite-sum identity. |
| (8); eq:totalvariance | Total variance. | Correct finite-sum identity. |
| (9); eq:TVHamming | Cost at most $\#(V\setminus Q)+\#V\,\varepsilon$. | Correct; deliberately weaker than the bound using $\#Q\,\varepsilon$. |
| (10); eq:smallgap | Gap at least $\alpha^{t+1}/t$. | Correct; Lemma 3.1's ordered-pair and directed-edge factors agree. |
| (11); eq:edgeD | Directed single-site edge expansion of the Dirichlet form. | Correct, including the factor $1/2$; unchanged-letter terms vanish. |
| (12); eq:blockcompare | Poincaré constant $t_{\max}/(cg)$. | Correct; multiplicities are counted in both the block generator and comparison. |
| (13); eq:shells | $F_i,D_i,A_i,B_i$ and integer-radius equality for $D_i$. | Correct; the interval $(is-1,is]$ contains precisely the integer $\lfloor is\rfloor$. |
| (14); eq:geomscale | Explicit geometry threshold. | Sufficient for all inequalities used in Lemma 4.2. |
| (15); eq:window | TV at most $1-p_0$. | The input hypothesis, with exactly the manuscript's required indices, shapes, and arbitrary boundary conditions. |
| (16); eq:Acount | $\#A_i\le8l_0$. | Correct outside $I_0$, for $2\le i\le i_1$; Lemma 4.2. |
| (17); eq:stopped | Failure probability $(1-\delta)^{h-3}$ and $Q_h=F_{h+1}$. | Correct; Lemma 4.3. |
| (18); eq:contractgap | Unnormalized block gap at least $c$. | Correct; the normalized update's contraction loss is $c/A$, not $c$. |
| (19); eq:counts | Bounds on $T_x,S_x$. | Correct; the proof actually gives $T_x\le450M^3$ and $S_x\le960M^2$. |
| (20); eq:Ksmall | $\mathcal K(M,K)$ with $K\le M/1000$. | Correct sufficient hypothesis. |
| (21); eq:criterionPI | Rectangle Poincaré constant $1000/g$. | Correct for $\alpha>0$; Finding 1. |
| (22); eq:tail | Finite binomial tail estimate. | Correct; Lemma 7.1. |
| (23); eq:rangegap | Original-site gap after finite-range blocking. | Correct; the extra factor is the lower bound for a single $r^2$-site cell, with multiplicity one. |
| (24); eq:chooseell | $t\ge\max(L_{\rm cell},\lceil1/(c_0m_0)\rceil,1)$ and $\ell=2t$. | Correct; produces an even $\ell\ge2$ meeting the local gap threshold. |
| (25); eq:gell | $g(\ell)\ge c_0m_0$ and $\ell\ge2/(c_0m_0)$. | Correct uniformly in all torus box placements and exterior configurations. |

**Finite energy and local gaps.** For a site $x$, translation invariance identifies the sum of norms of terms containing $x$ with $B$. Changing its letter changes the energy by at most $2B$. Dividing a proposed weight by the sum of at most $q$ weights therefore gives $\alpha_\Phi=q^{-1}e^{-2B}\in(0,1]$. No hard constraints are allowed here: real potentials and finite alphabets give full support. The manuscript cell potentials meet this requirement because every site and crossing bond weight is positive.

The partial-conditioning assertion really follows from a finite weighted average of fully conditioned probabilities; it does not assume independence. Successive conditioning then gives $\mu(\sigma)\ge\alpha^t$. In Lemma 3.1, the two relevant factors of $1/2$ match:

$$
\operatorname{Var}_\mu f
\le \frac t2\sum_{\text{directed edges }e}(\nabla_e f)^2,
\qquad
\mathcal D_V(f)\ge\frac{\alpha^{t+1}}2
\sum_{\text{directed edges }e}(\nabla_e f)^2.
$$

Each ordered coordinate path uses a directed edge at most once, and the sum of ordered-pair weights using any fixed edge is at most one. Thus no omitted congestion or alphabet-size factor is needed. The bound $\alpha^{v+1}/v$ for all $1\le t\le v$ has the correct monotonicity. Singleton alphabets cause no exception: the Poincaré inequality is automatic and the stipulated gap is $+\infty$.

**Geometry and stopped coupling.** At the geometry threshold, $s\ge16$ and $s\ge6(l_0+1)$ imply all four inequalities at lines 403–404. The estimate $k_i\le s^2+s$ is used only for $i\le i_1$. The last internal-boundary assertion in Lemma 4.2 is valid for all $i\ge2$: an integer-radius point outside $F_i$ and within one of $F_i$ must have radius $\lfloor(i-1)s\rfloor$. This remains valid for diagonal interactions. Also $y$ is outside the one-neighborhood of $F_i$.

At most one corner can have radius less than $u$ from $y$ in the chosen coordinate normalization. Any corner close to one of the shells has such radius, and the separation of distinct integer radii is at least $\lfloor s\rfloor>2s/3$. Consequently the same corner cannot contribute two exceptional indices. The coordinate normalization is used only for counting geometry; it makes no reflection or rotation assumption about the interaction.

Outside $I_0$, parallel shell sides are farther than $l_0$ from the corresponding exterior half-planes. Counting at most $l_0$ sites per perpendicular side/edge pair yields $8l_0$. Corner sites may be overcounted, which is harmless.

For each input pair, the two-stage marginal coupling/completion followed by independent $A_i$ resampling has the required two conditional marginals. Lemma 2.4 therefore applies despite the kernel's dependence on both inputs. Conditional on agreement on $B_i$ and on the sampled complements of $A_i$, forcing the same fixed assignment in the two independent last draws has probability at least $\alpha^{2\#A_i}$. Thus

$$
\Pr(\text{agreement on }D_i\mid\text{past})
\ge p_0\alpha^{2\#A_i}
\ge p_0\alpha^{16l_0}=\delta.
$$

The exponent $16l_0$ is correct. The extra independent resampling of $A_i$ is important for the stated argument.

There are $h-1$ candidate trial indices $2,\ldots,h$. A single exceptional index removes at most two of them from $J$, so $\#J\ge h-3$. A success at $i\in J$ is followed by an unskipped identical resampling on $F_{i+1}$. All later changed sets lie inside that common region, and their controlling shells do as well: $\lfloor(j-1)s\rfloor>is$ for $j\ge i+2$. Agreement therefore persists.

The product failure estimate uses conditional bounds given the complete past, not a product of unconditional probabilities. Its finite induction is valid even for adjacent trials. No window estimate is needed at step $h+1$ when that index exceeds $s$: this step is only needed to propagate a previous success by the identical-law branch. When $\delta=1$, $\#J\ge1$ and failure probability is zero; the separate treatment of a real power of zero in Corollary 4.4 is also correct.

**Square counts and normalization.** For a fixed side length $l=2u+1$, the $l$ nominal starts in $[x_j-l+1,x_j]$ all produce a clamped interval containing $x_j$. They all belong to the given label range. This gives the lower bound on $T_x$ without discarding repeated labels.

For the upper bound, the left endpoint has $L$ extra preimages, and the right endpoint has $l-1$ extra preimages. The left endpoint thus has $L+1$ preimages in total, which is consistent with the proof's wording about extra preimages. If both endpoints coincide, every nominal start is mapped to that single endpoint; its $N_j+L=l+L$ preimages obey the stated bounds.

For $S_x$, at least one coordinate has start $x_j+1$ or $x_j-l$. An interior prescribed start has one preimage. A permissible endpoint coincidence for this prescribed start requires $l=N_j-x_j$ or $l=x_j-1$, giving at most one radius for each of four directed sides. This is why varying the square size removes a potential extra factor of $M$ at the boundary. In the other coordinate the preimage count is at most $2l+L+1\le4L$. The resulting arithmetic is

$$
T_x\le(M+1)(3L)^2\le450M^3,\qquad
S_x\le16(M+1)L+32L^2\le960M^2\le1000M^2.
$$

All blocks remain full squares contained in $W$. There is no hidden use of an estimate on clipped squares, rectangles, or irregular domains.

For adjacent input configurations, a block containing the disagreement removes it; a distant block leaves exactly one disagreement; an exterior-neighbor block has cost at most $1+K$. Hence

$$
\mathbb E d_H\le1-\frac{T_x-KS_x}{A},\qquad
T_x-KS_x\ge4M^3-M^3=3M^3\ge M^3.
$$

Since $A=(M+1)(N_1+L)(N_2+L)\ge M^3$, Lemma 5.1 applies with $c=M^3$. The block generator is $A(I-P)$, so its gap is at least $M^3$, without a leftover factor $A^{-1}$. Comparing its blocks to single-site updates, with $t_{\max}\le1000M^3$ and within-block gap at least $g$, gives $m=g/1000$ exactly. This matches the manuscript's rate-one-per-site/cell Dirichlet forms.

**Closing the scales.** The quantity $\delta$ lies in $(0,1]$ and $d=\min(1/2,\delta)$ lies in $(0,1/2]$. For $M=n^8$ and every integer $u\in[M,2M]$,

$$
s\ge n^2\ge\max(16,6(l_0+1)),\quad
u\ge M_\star,\quad
4\le n\le\lfloor s\rfloor,\quad
ns\le2n^3.
$$

Thus all stopped-coupling hypotheses hold, including the geometry threshold and the integer restriction on $h=n$. The near-region cardinality is at most $(4n^3+1)^2\le25n^6$, using the integer lattice ball bound; the whole square has at most $(4n^8+1)^2\le25n^{16}$ sites. The square criterion can therefore use

$$
K_n=25n^6+25n^{16}(1-d)^{n-3}.
$$

For the tail bound, $N=n-3$ gives $N-19=n-22\ge n/2$ exactly when $n\ge44$. Keeping the twentieth binomial term yields the stated $2^{20}20!$ constant; no exponential limiting estimate is needed. The two parts of $K_n$ satisfy

$$
25n^6\le\frac{n^8}{2000}
\quad\Longleftrightarrow\quad n^2\ge50000,
$$

and

$$
25n^{16}(1-d)^{n-3}
\le\frac{25\,2^{20}20!}{d^{20}n^4}
\le\frac{n^8}{2000}
$$

by the last condition of (1). Therefore $K_n\le M/1000$. Replacing $\delta$ by $d$ enlarges the failure bound in the correct direction. The ceiling-of-a-maximum formula supplies an integer meeting every constraint, including $n^8\ge M_\star$. There is no implicit dependence on a gap subsequently being proved.

**Finite range and the physical comparison.** In Corollary 8.1, cells whose indices differ by at least two in a coordinate are separated by at least $r+1$ physical lattice units in that coordinate. An original term of diameter at most $r$ therefore meets a set of cells of diameter at most one. Grouping all terms by that cell set gives a real finite-range cell potential and exactly the same Gibbs law on a union of cells. The bound $\widehat\alpha=\alpha^{r^2}$ follows under full outside conditioning by the assignment bound. The extra factor $\alpha^{r^2+1}/r^2$ is a valid lower bound for the original-site dynamics inside a cell; disjoint cells have multiplicity one. Translation invariance permits shifting the entire cell partition to any translated rectangle of the stated divisible side lengths. The corollary makes no assertion for other side lengths and requires its own blocked window input. It is not needed for the manuscript, whose cell models already have range one.

For Lemma 9.2, let $w_\pm$ and $b_\pm$ have the meanings specified in the proof. Every physical site has four neighbors, including pinned exterior neighbors, and at most twenty letters. Therefore

$$
\beta\ge\frac{w_-b_-^4}{20w_+b_+^4}>0.
$$

This argument covers every configuration, not only typical ones. A four-site cell then has gap at least $\beta^5/4$, and the conditional-variance comparison gives the asserted physical-site bound on any finite set of cells of either fixed partition. If retaining the manuscript's definition of $c_0$ as the exact minimum of cell gaps, $\beta^5/4$ is a certified lower bound for that minimum; either constant works.

**Formalization notes.** The following are explicit Lean nodes that the prose uses. They are standard finite facts rather than additional mixing assumptions.

- Define a finite configuration type for each finite region, with restriction, disjoint gluing, coordinate replacement, and nonemptiness. Permit nonuniform finite alphabets for the general comparison lemmas and physical spins.
- Restrict interaction sums to their finite support. Prove that a term meeting $V$ lies in $V\cup\partial_rV$, and that the terms meeting $U\subset V$ are precisely the nonconstant terms in conditioning on $V\setminus U$. Prove positivity of every normalizing constant.
- Prove covariance of the finite specification, conditional kernels, marginals, and Hamming distance under translations. Use coordinate symmetries only for pure geometric statements, not for Gibbs laws.
- Establish the finite conditional chain rule, the tower/averaging identity for conditioning on fewer coordinates, and positive mass of every consistent partial assignment. These yield both assignment bounds and lower bounds in conditional fibers.
- Construct $E_U$ as a finite matrix; prove invariance, self-adjointness, idempotence, preservation of constants, the conditional variance formula, and the two variance decompositions used here.
- Establish the variational Poincaré formulation of a gap. An extended-real convention is needed if defining the gap on a one-point state space; alternatively formulate every comparison directly as a real Poincaré lower bound and avoid an empty infimum.
- Construct maximal couplings with a separate zero-residual-mass branch. Prove the TV overlap identity, coupling inequality, contraction under marginalization, and reconstruction of a joint law by conditional completion.
- Treat surgery as a finite kernel with specified first and second marginals for every input pair. Prove invariance after composition, including the second conditional-resampling operation on $A_i$. This avoids any unproved claim about preserving a marginal after a sample-dependent branch.
- Prove the directed-edge expansion, the pairwise expression for variance, coordinate-path construction, absence of repeated directed edges on those paths, and the finite weighted Cauchy–Schwarz bound.
- Prove the fiberwise block comparison with a finite label type, retaining repetitions. Record that one-site kernels in a block fiber equal the corresponding kernels of the original law.
- Use integer-valued $\ell^\infty$ radii and explicit floor lemmas. In particular: $(t-1,t]\cap\mathbb Z=\{\lfloor t\rfloor\}$; $\lfloor is\rfloor>(i-1)s$ for $s>1$; adjacent radii differ by at least $\lfloor s\rfloor$; and $\lfloor(j-1)s\rfloor>is$ for $j\ge i+2$, $s\ge16$.
- Handle empty shells and empty windows explicitly. The geometric distance to an empty set is $+\infty$ here. Lean's usual real-valued infimum distance has a different empty-set convention, so encode proximity as existence of a shell point within a radius, or use an extended distance. The geometry arguments themselves do not require a probabilistic choice on an empty state type.
- Encode the stopped coupling as a finite recursion on kernels/history. Prove a uniform conditional success bound, the persistence invariant after success, $\#J\ge h-3$, and the conditional product-of-failures bound. Handle $\delta=1$ without dividing by $1-\delta$.
- Prove the Hamming coordinate-path Lipschitz estimate and that a zero seminorm implies constancy. Use the finite real self-adjoint spectral theorem on $L^2(\mu)$, or the symmetric matrix obtained using the positive diagonal matrix with entries $\sqrt{\mu(\omega)}$. No infinite-time convergence theorem is required.
- Formalize clamping preimage counts, including a one-point interval of allowable starts. Prove the four directed-side decomposition as an overcount and the at-most-one exceptional radius for each directed side. Keep a label type rather than replacing the block list by a set of distinct squares.
- Separate the integer scale arguments from real fourth roots and reciprocals. Required facts are positivity, monotonicity of natural powers, the Archimedean ceiling bound, the finite binomial theorem, the lower bound on $\binom{n-3}{20}$, and cardinalities of integer squares. Finding 1 supplies the missing positive denominator in Theorem 6.3.
- For finite-range blocking, construct the cell/site bijection, regroup the finite Hamiltonian sum, and identify cell and physical conditional expectations. For the frame application, use the two permitted checkerboard site alphabets rather than assuming all physical sites share one alphabet.
- For the torus application, prove injectivity on the lifted box, absence of additional internal wrap-around edges, consistency of the lifted exterior letters, preservation of site types because the torus periods are even, and equality of the conditional probability laws. Relabeling configurations then conjugates the heat-bath operators and preserves gaps.
- Split real and imaginary parts to pass a real Poincaré inequality to the complex functions in the manuscript. Record explicitly that all generator normalizations are sums of site projections.

These nodes suffice for the appendix's claimed self-contained finite proof. The spectral theorem, finite Cauchy–Schwarz, and ordinary facts about finite sums and positive real exponentials remain mathematical library dependencies; neither of the cited mixing theorems is such a dependency.

**Insertion into the manuscript.** The relevant source-label map is: t:MOS21 = Theorem 4.3; t:MO41 = Theorem 4.4; d:W = Definition 4.7; p:surgery = Proposition 4.8; c:gapcell = Corollary 4.9; t:mainW = Theorem 4.10; and t:K = Theorem 3.1.

The appendix's window sets and exceptional indices agree with d:W, including the strict inequalities, the cutoff $i_1=\lfloor s\rfloor+1$, the restriction $i\le s$ on actual uses of the window bound, and the freedom to choose arbitrary boundary configurations on $F_i$. Requiring $M_\star$ to be a positive integer merely rounds up an existing threshold. If a convention allows $l_0=0$ in the manuscript's notation $\mathbb N$, its actual Section 5 supplies $l_0=20$; more generally increasing $l_0$ to one only shrinks $B_i$ and preserves the TV bound by marginalization.

For each offset, take

$$
\alpha_o=57600^{-1}e^{-2B_o},\quad
L_0^{(o)}=4n_o^8+1,\quad
m_0^{(o)}=\frac{\alpha_o^{(L_0^{(o)})^2+1}}
{1000(L_0^{(o)})^2}.
$$

Their maximum threshold $L_{\rm cell}$ and minimum positive gap $m_0$ work simultaneously. There is no restriction that a cell box side be odd or a multiple of a fixed block side: the squares used inside the comparison have odd side, but the enclosing rectangle may have any integer side at least $L_{\rm cell}$. This is important for the proposed choice of $t$.

For an arbitrary physical box placement, even torus periods preserve the checkerboard when coordinates are lifted. If the lifted lower-left corner has odd second coordinate, a translation by $(1,1)$ makes it even and preserves the frame pattern. Translations by even amounts in the coordinates then identify the box with the offset-zero cells when the original corner parities agree, and offset-one cells otherwise. Thus every even physical box of side $\ell=2t$ becomes a $t\times t$ cell square for one of the two models. The boundary condition is arbitrary in the resulting plane law. No assumption about the parity of $t$, a special placement, or a constant boundary is introduced.

For $L,N\ge\ell+2$, the lifted box sites are distinct modulo the periods, and no additional torus bond joins nonadjacent lifted box sites. Assigning each exterior neighbor the letter of its torus image gives exactly the torus conditional law; any superfluous exterior cell letters can be filled arbitrarily. Hence all of the conditional gaps $\gamma(a,\sigma)$ in manuscript equation e:gell are at least $c_0m_0$, uniformly over both minima.

The first bound in manuscript Theorem 3.1 then gives

$$
\lambda(\mu_D)\ge
\frac{\ell}{\ell-1}
\left(c_0m_0-\frac1\ell\right)
\ge\frac{c_0m_0}{2},
$$

because $\ell\ge2/(c_0m_0)$. Here $\ell\ge2$ and $L,N\ge\ell+2\ge4$, so both the finite-size criterion and the frame-to-quantum comparison have their required sizes. Manuscript e:QDrot and t:QD give the claimed quantum gap $g_\star c_0m_0/4$ and the one-dimensional kernel.

Consequently the final theorem plugs in **without a change to its conclusion**, but **not by leaving the present Section 4 text unchanged**. Replace the present compatible-set Corollary 4.9 by appendix Corollary 9.1. In the proof of Theorem 4.10, delete $K=(2M_0^{(0)}+1)(2M_0^{(1)}+1)$ and the compatible-set divisibility argument, and choose $t,\ell$ by (24). The preliminary explanation that the two cited theorems are the main tools and the subsequent constant-dependency sentence must also be updated. The stronger cited statements can be removed from the proof's dependency chain, and the finite-alphabet extension discussion in Remark 4.5 is unnecessary.

Keep the manuscript's independent shell-geometry lemma l:shellgeom, or promote its parallel-side clearance assertion into the statement of appendix Lemma 4.2 if consolidating the two proofs: Section 5's l:cutgeom uses that assertion, not merely the cardinality bound on $A_i$. The appendix proves the clearance assertion in its proof, so this consolidation requires no new mathematics.

There is **no circularity with Section 5**. Its t:cutMOS supplies d:W from Hypothesis (P), using the cut/removal results and independent shell geometry. The window-to-gap proof uses d:W, finite energy, and geometry; it uses neither (P)'s proof nor any quantum gap to establish a classical gap. Geometry has no window or gap hypothesis. The constants can be chosen in the order: cell potentials and finite energy; window parameters from Section 5; $d,n,M,L,g,m$ for each offset; common $L_{\rm cell},m_0$; physical $c_0$; and finally $t,\ell$ and the torus threshold. No later constant is needed to define an earlier one.

This audit treats (P) and Section 5's window theorem as the manuscript's upstream input; it does not certify all of Section 5's independent analytical and topological results. The checks of Section 5 here concern matching hypotheses, shapes, boundary quantifiers, and absence of a dependency on a gap.

**Exact checks and external sources.** Small computations corroborated, rather than replaced, the preceding proofs:

- Exhaustive site counts for $M=1,\ldots,12$ and all 25 ordered rectangle-size pairs from $\{L,L+1,L+2,2L-1,3L+1\}$: 721,964 site/rectangle/scale cases. All three claimed counting inequalities passed. Coordinate counts enumerated every nominal clamping label; square counts used the exact product formula, with exterior-distance-one count equal to the enlarged-interval product count minus $T_x$. The largest observed $S_x/M^2$ was $206$.
- Exact integer geometry checks for $l_0=1,2,20$, at $u=a^4$, $a^4+1$, and $(a+1)^4-1$, using critical offsets around each corner-crossing radius and centered/end exterior positions: 890,448 shell cases, including 593,632 with nonintegral fourth root. All shell containment, exceptional-index, and $A_i$ bounds passed. Floors of $i u^{1/4}$ were computed as integer fourth roots of $i^4u$, and strict comparisons with $s/3$ were checked by fourth powers, avoiding floating point.
- Thirty-six rational tail checks used $n\in\{44,45,46,64,100,223,224,500,1000\}$ and $d\in\{1/2,1/3,1/10,1/1000\}$. All passed.
- Exact scale-closure checks with $l_0=20$, $M_\star=1$, and $d=1/2,1/10,1/10000$ gave least permitted $n=846,12364,1236349369$, respectively. In each case both contributions to the proven upper bound on $K_n/M$ were at most $1/2000$. The last case used the rational binomial bound, not an expansion of an enormous power.

The original shell/surgery construction was checked against the [MOS author version, Section 2](https://web.ma.utexas.edu/mp_arc-bin/mpa?yn=93-154). The heat-bath rates, compatible-volume scope, block comparison discussion, and general-system proof language were checked against the [MO author version, Section 4](https://web.ma.utexas.edu/mp_arc-bin/mpa?yn=92-186). These are provenance checks. Every implication needed for the new window-to-box-gap route is proved in the appendix itself; the other alternative approaches listed in its bibliography are not dependencies.
