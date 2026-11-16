STATUS: COMPLETE

The requested Section 4 implication has a complete finite-state proof in [proof.tex](proof.tex). It uses the permitted replacement route: **the existing window estimate implies a uniform heat-bath gap on large square boxes directly**. No theorem of MO94 or MOS94 is assumed. The full strong-mixing conclusion of MOS94 and the arbitrary-compatible-union conclusion of MO94 are not needed and are not claimed as additional results.

This is a mathematical appendix prepared for formalization, not a Lean implementation or a claim that Lean has checked the proofs. The model-specific window estimate remains the input already proved separately in manuscript Section 5; no additional mixing hypothesis is introduced.

## Exact statements proved

All dynamics use the unnormalized Dirichlet form `sum_x μ(Var_x f)`, corresponding to one update per site, as in the manuscript.

1. **Window estimate ⇒ uniform rectangular-box gap, arbitrary finite alphabet** (`thm:main`, Theorem 1.1). Let `S` be any nonempty finite set, and let the potential on Z² be real, translation invariant, and of range one in ℓ∞. Diagonal and many-body range-one terms are allowed. Assume exactly the window estimate `d:W`, with parameters `l₀ ≥ 1`, `p₀ > 0`, and `M⋆`. Then all rectangular boxes whose two sides exceed one fixed threshold have a strictly positive single-site heat-bath gap, uniformly over all boundary conditions. There are no parity or divisibility restrictions on those boxes.

   Explicit constants: let `B = sum_{A containing 0} ||Φ_A||∞`, `α = |S|⁻¹ exp(-2B)`, and `d = min(1/2, p₀ α^(16l₀))`. Choose an integer `n` satisfying

   ```text
   n ≥ 44
   n^8 ≥ M⋆
   n² ≥ max(50000, 6(l₀ + 1))
   n^12 d^20 ≥ 50000 · 2^20 · 20!
   ```

   Set `M = n^8`, `L = 4M + 1`, `v = L²`. The gap lower bound is

   ```text
   m = α^(v+1) / (1000v) > 0.
   ```

   The theorem includes a closed formula for choosing `n`, so the existence assertion uses no asymptotic estimate.

2. **A finite family of square coupling bounds ⇒ box gap** (`thm:criterion`, Theorem 6.3). It suffices that, for every integer square radius `u ∈ [M,2M]`, every translate, and boundary conditions differing at one exterior site, a coupling of the full square laws has expected Hamming distance at most `M/1000`. The gap is then at least `α^((4M+1)²+1)/(1000(4M+1)²)` on every rectangle with both sides at least `4M+1`. This theorem itself needs no translation invariance if the coupling bounds are imposed at every translate.

3. **Stopped shell coupling** (`lem:stopped`, Lemma 4.3). For each admissible square radius `u`, put `s = u^(1/4)` and `δ = p₀ α^(16l₀)`. For every integer `4 ≤ h ≤ floor(s)`, boundary conditions differing at one exterior site `y` can be coupled to agree simultaneously on

   ```text
   {x in C_u : |x-y|∞ > hs}
   ```

   except with probability at most `(1-δ)^(h-3)`. The threshold is explicitly `u ≥ max(M⋆, max(16,6(l₀+1))^4)`. Boundary changes farther than range one have no effect. This uses exactly the manuscript's `F_i`, `D_i`, `A_i`, `B_i`, and exceptional index set `I₀`.

4. **The manuscript's original surgery bound** (`cor:originalprop`, Corollary 4.4). Taking `h = floor(s)` recovers the stated estimate beyond radius `sqrt(u)`, with exponent `u^(1/4)-4` and the same `δ`. Thus the original proposition is also proved with an explicit geometric threshold.

5. **General finite-range version** (`cor:range`, Corollary 8.1). For any integer interaction range `r ≥ 1`, block into `r × r` cells with alphabet `S^(r²)`. The induced potential has range one, and cell conditional probabilities are at least `α^(r²)`. If that actual blocked specification has the stated window estimate, the original single-site gap on all sufficiently large translated rectangles with side lengths divisible by `r` is at least

   ```text
   [α^(r²+1)/r²] · m_block.
   ```

   This is an explicit statement about which specification must satisfy the window estimate. Finite range and finite energy alone are not asserted to imply a gap. The manuscript is already at range one after its own blocking, so this corollary adds no assumption to its application.

6. **Both offsets and the physical-site comparison** (`cor:twooffsets`, Corollary 9.1; `lem:physical`, Lemma 9.2). Apply the theorem separately to the two alphabets of 57,600 cell letters, take the maximum threshold and minimum gap, and obtain a common cell gap `m₀`. If `β` is the finite positive minimum of all physical one-site conditional probabilities, one can take `c₀ = β^5/4` for the four-site-to-cell comparison. This supplies a quantitative proof of the positivity used in manuscript Lemma 4.2.

7. **Exactly the input consumed by Theorem 4.10** (`cor:boxinput`, Corollary 9.3). Choose an integer `t ≥ max(L_cell, ceil(1/(c₀m₀)), 1)` and put `ℓ = 2t`. For every even torus with `L,N ≥ ℓ+2`, every translated `ℓ × ℓ` box, and every outside configuration, its conditional physical-site gap is at least `c₀m₀`. Consequently `g(ℓ) ≥ c₀m₀`, while `ℓ ≥ 2/(c₀m₀)`. Substitution into the manuscript's independent finite-size and frame comparisons gives exactly its existing conclusion, with `λ(μ_D) ≥ c₀m₀/2` and quantum gap at least `g⋆c₀m₀/4`.

## Why this route closes the argument

Stopping the surgery at radius `sqrt(u)` only gives an elementary expected Hamming cost of order `u`. That does not suffice for the direct contraction below. The actual window hypothesis permits an earlier stopping time: for `u ∈ [n^8,2n^8]`, stop after `n` shells. The near region then has at most `25n^6` sites. The remaining Hamming contribution is at most `25n^16(1-d)^(n-3)`, bounded by `n^8/2000` using a finite binomial expansion. The near region contributes at most the same amount. This proves the square coupling criterion above.

The remaining difficulty is the boundary of the large box. Updating intersections of translated squares with that box would create nonsquare regions, for which the input supplies no estimate. Instead, use squares of every odd side `2u+1`, `u=M,…,2M`, move them into the large rectangle by clamping their lower left corners, and retain the multiplicities of the nominal placements. For every site `x`, the number of blocks containing it is at least `4M³`; the number excluding it but adjacent to it is at most `1000M²`; the containing multiplicity is at most `1000M³`. The proof includes the endpoint cases and corner overcounting explicitly.

A pair differing at one site therefore contracts in expected Hamming distance under one averaged block update. The averaged update is a positive self-adjoint finite matrix. Its contraction on the Hamming Lipschitz seminorm bounds each nonconstant eigenvalue and gives an unnormalized block gap at least `M³`. Conditional variance comparison then gives the claimed single-site gap. There is no continuous-time construction, time limit, infinite-volume limit, finite-speed estimate, or recursive gap theorem in this route.

## Insertion into Section 4

The supplied `main.pdf` and the user's numbering differ at one point: the PDF has **Lemma 4.6** (`l:shellgeom`), **Definition 4.7** (`d:W`), and **Proposition 4.8** (`p:surgery`). The request's “Proposition 4.7” is understood as `p:surgery`. Theorem 4.10 and Corollary 4.9 have the requested numbers. Use source labels for edits.

The precise dependency in the current text is:

```text
§5 Theorem t:cutMOS
  → window estimate d:W
  → p:surgery
  → telescope exterior boundary changes
  → one-box condition e:MOS22
  → t:MOS21 (Theorem 4.3)
  → SM on every square
  → t:MO41 (Theorem 4.4)
  → c:gapcell on arbitrary compatible unions
  → square box used in t:mainW
  → physical-site comparison l:compare
  → finite-size criterion t:K.
```

Only the final square-box gap is consumed by `t:mainW`. Neither strong mixing itself nor a compatible union of a nonsquare shape occurs in that application.

The replacement dependency is:

```text
§5 t:cutMOS → d:W
  → stopped version of the same surgery
  → square Hamming coupling bounds
  → clamped-square block contraction
  → uniform square box gap
  → l:boxcell and l:compare
  → t:K.
```

The manuscript files have not been modified. The following are concrete replacement passages.

### Opening paragraph and cited-results subsection

Replace the sentence identifying the two cited main tools by:

> The main tool is a finite-state square-block criterion proved in the accompanying appendix. The window estimate gives a stopped shell coupling on large squares; a family of square updates of varying sizes then gives a uniform heat-bath gap on all sufficiently large square boxes. The shell construction follows Martinelli, Olivieri and Schonmann, but all ingredients needed here are proved directly for arbitrary finite single-cell spaces.

The subsection headed “The cited results,” including `t:MOS21`, `t:MO41`, and `r:finiteS`, can be removed from the proof dependency. Its definitions of `SM`, `Q_{M,η,η′}`, and `M₀`-compatibility are then unnecessary. No proof of those stronger statements is required for the resulting Section 4.

Keep `d:W`, the shell geometry, and `p:surgery`. Add the stopped lemma from the appendix, or cite the appendix's proved window-to-box-gap theorem after the existing proposition. The old proposition's conclusion alone is not the hypothesis of our direct block criterion; the appendix uses its stronger stopped version, proved from the same `d:W` input.

### Replacement for `c:gapcell`

```latex
\begin{corollary}\label{c:gapcell}
Assume that the window estimate holds for both cell models.
Then there exist $m_0>0$ and $L_{\mathrm{cell}}\in\mathbb N$
such that for either offset $o$, every translated square of
$t\times t$ cells with $t\ge L_{\mathrm{cell}}$, and every
boundary condition, the cell heat bath of $\hat\mu^{(o)}$
has spectral gap at least $m_0$.
\end{corollary}
\begin{proof}
Apply the appendix's window-to-box-gap theorem separately to the
two real, translation-invariant, range-one cell potentials.
Take the maximum of the two size thresholds and the minimum of
the two positive gap bounds.
\end{proof}
```

The old arbitrary-compatible-union conclusion is deliberately replaced by this sufficient box statement. The original proof of `c:gapcell`, including the boundary telescoping and both cited theorem applications, is deleted.

The sentence ordering the constants can be replaced by:

> For each offset the constants are chosen in the order `(l₀,p₀,M⋆,α) → d → n → (L_cell^(o),m₀^(o))`; then take their maximum threshold and minimum gap. The physical-cell constant `c₀` is fixed independently. None depends on the later choice of the physical box side.

### Replacement proof of `t:mainW`

The statement of Theorem 4.10 stays unchanged. Replace its proof by:

```latex
\begin{proof}
Let $m_0,L_{\mathrm{cell}}$ be as in Corollary~\ref{c:gapcell},
and let $c_0>0$ be as in Lemma~\ref{l:compare}.
Choose an integer
\[
 t\ge\max\{L_{\mathrm{cell}},\lceil1/(c_0m_0)\rceil,1\},
 \qquad \ell=2t,
\]
and let $L,N\ge\ell+2$ be even.
For every placement $a$ and every configuration $\sigma$ outside
$R+a$, Lemma~\ref{l:boxcell} identifies the conditional law with
a square of $t\times t$ cells of one of the two offsets.
Corollary~\ref{c:gapcell} and Lemma~\ref{l:compare} give
$\gamma(a,\sigma)\ge c_0m_0$, so $g(\ell)\ge c_0m_0$.
Since $\ell\ge2/(c_0m_0)$, Theorem~\ref{t:K} gives
\[
 \lambda(\mu_D)\ge
 \frac{\ell}{\ell-1}\left(c_0m_0-\frac1\ell\right)
 \ge\frac{c_0m_0}{2}.
\]
Equation~\eqref{e:QDrot} and Theorem~\ref{t:QD} then give
$\ker H_{L,N}=\mathbb C B$ and
$\operatorname{gap}(H_{L,N})\ge g_\star c_0m_0/4$.
Take $c=g_\star c_0m_0/4$ and $L_0=\ell+2$.
\end{proof}
```

The compatibility scale `K=(2M₀^(0)+1)(2M₀^(1)+1)` disappears. The concluding proof of the manuscript's main theorem, using `t:inputs → t:rec → t:cutMOS → t:mainW`, is unchanged. Its final sentence about absence of circular dependencies remains valid.

## Complete lemma dependency list

Numbers below refer to the standalone appendix. Labels provide stable Lean-facing names. “Elementary” means the proof is supplied in the appendix, using finite sums, elementary inequalities, integer geometry, or finite real symmetric-matrix diagonalization; it does not designate a theorem assumed from a paper.

| Result | Label | Direct dependencies |
|---|---|---|
| 2.1: specification consistency, Markov property, finite energy, chain-rule assignment bound | `lem:spec` | Finite Gibbs definition; cancellation of constant energy terms; finite chain rule |
| 2.2: conditional projections, variance identities, block form | `lem:CE` | Explicit finite conditional sums |
| 2.3: maximal TV coupling, marginalization, TV-to-Hamming completion | `lem:coupling` | Finite overlap/residual construction; conditional sums |
| 2.4: surgery preserves both Gibbs marginals | `lem:surgery` | 2.1, 2.2 |
| 3.1: explicit gap `α^(t+1)/t` on `t` sites | `lem:smallgap` | Chain-rule part of 2.1; expansion of conditional variance; coordinate paths; Cauchy–Schwarz |
| 3.2: block/single-site comparison with multiplicities | `lem:comparison` | 2.2; the stated conditional Poincaré bounds |
| 4.1: exact window definition | `def:window` | Manuscript `d:W`; no changed windows |
| 4.2: shell geometry, `|I₀| ≤ 1`, `|A_i| ≤ 8l₀`, separator property | `lem:geometry` | Integer ℓ∞ geometry; explicit size threshold |
| 4.3: stopped shell coupling | `lem:stopped` | 2.1–2.4, 4.1, 4.2; finite induction over trial failures |
| 4.4: original manuscript surgery estimate | `cor:originalprop` | 4.3, marginalization in 2.3; `h=floor(s)` |
| 5.1: Hamming contraction ⇒ block gap | `lem:contraction` | 2.2; coordinate-path Lipschitz bound; finite symmetric-matrix eigenbasis |
| 6.1: clamped-square counting | `lem:count` | Finite interval counts, endpoint cases, four directed sides |
| 6.2: square Hamming criterion definition | `def:Kcriterion` | Explicit finite quantifiers over radii, translates, boundary letters |
| 6.3: direct square criterion ⇒ rectangular-box gap | `thm:criterion` | 2.1, 3.1, 3.2, 5.1, 6.1, 6.2 |
| 7.1: finite polynomial tail bound | `lem:tail` | Finite binomial theorem and `n-22 ≥ n/2` |
| 7.2: window estimate ⇒ square Hamming criterion | `lem:windowK` | 2.3, 4.3, 7.1; explicit choice of `n`; translation invariance |
| 1.1: main window-to-box theorem | `thm:main` | 2.1, 6.3, 7.2; explicit choice of `n` |
| 8.1: arbitrary finite range by blocking | `cor:range` | 2.1, 3.1, 3.2, 1.1; exact regrouping of finite interaction terms |
| 9.1: two offset models | `cor:twooffsets` | 1.1 applied twice; minimum and maximum over two constants |
| 9.2: physical-site/cell comparison | `lem:physical` | Positivity of the manuscript's finite site/bond weights; 3.1, 3.2 |
| 9.3: the exact square input for Theorem 4.10 | `cor:boxinput` | 9.1, 9.2; torus-to-plane boundary lift and checkerboard parity argument, both proved there |

The last two gap substitutions in Corollary 9.3 use the separate finite-size theorem `t:K` and frame comparison `t:QD` already belonging to the manuscript. They are not dependencies of the mixing-to-box-gap theorem, and this appendix does not reprove the rest of the AKLT argument.

## Sources and precise locators

The cited literature provides provenance and alternative routes. Every mathematical step used in the replacement is proved in the appendix.

- **MOS94 original:** Martinelli–Olivieri–Schonmann, *For 2-D lattice spin systems weak mixing implies strong mixing*, CMP **165** (1994), 33–47. [Project Euclid record](https://projecteuclid.org/euclid.cmp/1104271032), [publisher record](https://link.springer.com/article/10.1007/BF02099735), [full author archive](https://web.ma.utexas.edu/mp_arc-bin/mpa?yn=93-154). Inspected the full author TeX and PostScript. Exact locators: §1, finite-alphabet specification; §2, Proposition 2.1; Theorem 2.1 and (2.2), the one-box criterion; surgery construction (2.4)–(2.9); success estimate (2.10); iteration (2.11)–(2.12). In the archived typeset version, §2 occupies internal pages 8–12, with shell definitions on internal page 10 and success/iteration on pages 11–12. These are **archive internal pages**, not claimed as published pagination. Used for the shell mechanism in appendix Lemmas 2.4 and 4.3. The earlier stopping time and explicit conservative geometry bound are proved here.

- **MO94 original:** Martinelli–Olivieri, *Approach to equilibrium of Glauber dynamics in the one phase region. I. The attractive case*, CMP **161** (1994), 447–486. [Project Euclid record](https://projecteuclid.org/euclid.cmp/1104270006), [publisher record](https://link.springer.com/article/10.1007/BF02101929), [full author archive](https://web.ma.utexas.edu/mp_arc-bin/mpa?yn=92-186). Inspected the full author TeX and PostScript. Exact locators: §4 opening, the restriction to two spin values for exposition; (4.1), heat-bath rates; (4.2), the small remote-marginal bound; Theorem 4.1; block sampler (4.3)–(4.4); comparison (4.5). The remark between (4.4) and (4.5) explains why truncating cube updates is problematic when mixing is known only on cubes. The following paragraph says the proof treats a general system without a ferromagnetic assumption. In the archived typeset version these passages are on internal pages 33–36. Used for auditing the manuscript's cited statement and boundary-shape issue; no MO94 theorem is a proof dependency.

  Project Euclid's public links were located, but its PDF requests returned an access-challenge page in this environment. The full author archive versions, rather than an unreadable response mislabeled as a PDF, were used for inspection. Published bibliographic data were checked against the publisher records. Numbered theorem/equation locators above are those actually inspected in the author versions.

- **Martinelli lecture notes:** *Lectures on Glauber dynamics for discrete spin models*, Saint-Flour 1997, LNM **1717** (1999), 93–191. [DOI](https://doi.org/10.1007/978-3-540-48115-7_2), [full lecture archive](https://web.ma.utexas.edu/mp_arc-bin/mpa?yn=97-578), [direct PostScript](https://web.ma.utexas.edu/mp_arc/c/97/97-578.ps.gz). Inspected the full lecture version. §3.6, (3.28), defines block dynamics. §3.7, Proposition 3.4, (3.29)–(3.32), gives the conditional-variance comparison reproduced in appendix Lemma 3.2; these occupy internal pages 26–28. §4.2, Theorem 4.5 and proof (4.14)–(4.16), internal pages 43–46, give the simpler recursive spectral-gap route on fat rectangles. That route requires estimates on rectangle laws, so it was not silently applied to the square-only input.

- **DSVW:** Dyer–Sinclair–Vigoda–Weitz, *Mixing in time and space for lattice spin systems: a combinatorial view*, RSA **24** (2004), 461–479. [DOI](https://doi.org/10.1002/rsa.20004), [full author PDF](https://people.eecs.berkeley.edu/~sinclair/st_full.pdf). Inspected the author version dated February 19, 2003. Exact locators: Theorem 2.5 and §6, proof of that theorem, for strong spatial mixing implying contraction of sufficiently large block updates in a general system; Lemma 3.1 for a combinatorial propagation bound; §3 for coupling tools. This is an alternative viewpoint, not an invoked result. Its spatial-mixing hypotheses and region requirements must not be identified automatically with the manuscript's window estimate.

- **Cesi:** *Quasi-factorization of the entropy and logarithmic Sobolev inequalities for Gibbs random fields*, PTRF **120** (2001), 569–584. [Publisher record](https://link.springer.com/article/10.1007/PL00008792), [full author archive](https://web.ma.utexas.edu/mp_arc-bin/mpa?yn=00-284), [direct PostScript](https://web.ma.utexas.edu/mp_arc/c/00/00-284.ps.gz). Inspected the full author version. §2, Proposition 2.1, (2.8)–(2.10), gives the entropy quasi-factorization criterion; §4, Theorem 4.1 and its preceding decomposition lemma, give its Gibbs-field application. Relevant archive internal pages are 4 and 10 onward. This route calls for relative conditional-density estimates; it is not needed for the present gap-only result.

- **Bertini–Cancrini–Cesi:** *The spectral gap for a Glauber-type dynamics in a continuous gas*, AIHP PR **38** (2002), 91–108. [Full published PDF](https://www.numdam.org/item/AIHPB_2002__38_1_91_0.pdf). Inspected the published paper. §3.3, pp. 99–102, proves Theorem 2.2 by recursion; Lemma 3.1, (3.7)–(3.8), pp. 99–100, is a direct two-block variance lemma without a semigroup proof; (3.11)–(3.15) and Proposition 3.2 control the overlapping decompositions. Considered as a simpler variance route, but not needed after the direct square construction.

- **Ott, later alternative:** *A new perspective on the equivalence between Weak and Strong Spatial Mixing in two dimensions*, [arXiv:2502.04117](https://arxiv.org/abs/2502.04117), inspected v2, April 2026. §3, Theorem 3.1, p. 25, treats finite-range Gibbs specifications; its proof uses the percolation comparison developed in Theorems 1.1–1.2. It provides a later proof of the full weak-to-strong implication. Recovering that stronger conclusion adds machinery unnecessary for the box gap here.

For steps without an imported theorem: Gibbs cancellation and finite-energy bounds are proved in Lemma 2.1; maximal coupling is explicitly constructed in Lemma 2.3; the small-volume bound is a complete coordinate-path proof in Lemma 3.1; the finite-matrix argument is proved in Lemma 5.1; the variable-size clamped-square construction and endpoint counting are proved in Lemma 6.1; the tail estimate is a finite binomial calculation in Lemma 7.1. None has an uncited proof obligation hidden behind a phrase such as “standard mixing theorem.”

## Audit of the manuscript's current use

- **The finite-alphabet extension was a proof obligation, not a proof in the manuscript.** The current Remark `r:finiteS` explains why the MO94 argument should extend, but the imported statement is proved there in two-spin notation. This appendix resolves the needed implication directly for arbitrary finite alphabets. It does not rely on that remark as an assumption or assert that cardinality alone disproves the original theorem.
- **No incorrect downstream use of compatible sets was found.** The current product `K` makes the chosen cell square compatible with either offset's scale, as intended. The replacement avoids this restriction because it proves the gap for all large square sides. It does not preserve an unused claim about arbitrary unions.
- **All boundary conditions are essential.** The window hypothesis used here is exactly the uniform one in `d:W`, supplied by `t:cutMOS`; typical-boundary or averaged-boundary estimates would not suffice. The proof checks the conditional laws encountered during surgery and block updates explicitly.
- **The original terminal-radius statement is insufficient for this elementary contraction shortcut by itself.** The stopped coupling must be proved from the window input; it is included in full. No claim is made that a single occurrence of the MOS one-box criterion, without the all-large-scale window input, implies our finite family of Hamming bounds by the argument here.
- **Boundary shapes require care.** Intersections of square update blocks with the large box are generally rectangles. Square mixing does not authorize replacing them by square laws. The clamped construction keeps every updated domain square and handles the clamping atoms by varying the size. The proof explicitly treats both large-box corners and side endpoints.
- **No parity or normalization factor has been dropped.** The two cell offsets remain separate until their constants are combined. Physical box side `ℓ` is even, torus sizes are even and at least `ℓ+2`, and the conditional law is lifted to a plane box before the cell comparison. All gaps have the manuscript's rate-one-per-site or rate-one-per-cell normalization; the `M³` block gap is compared against the `≤1000M³` block multiplicity before taking the physical-site factor.
- **Numbering correction:** the supplied PDF calls `p:surgery` Proposition 4.8 and `d:W` Definition 4.7. The task's proposition number should not be used as a stable identifier for formalization.

Apart from that numbering mismatch and the formal proof obligation removed above, this audit did not establish a false claim in the manuscript's Section 4 application. It replaces the two cited implications with a fully proved sufficient statement; it is not an audit of the separate computer-assisted estimates or all other sections.

## Validation

- `proof.tex` is a standalone `amsart` document, with a self-contained bibliography and all internal references resolved by repeated `pdflatex -interaction=nonstopmode -halt-on-error` compilation. The final run has no warnings or overfull boxes; the compiled 12-page appendix is also provided as [proof.pdf](proof.pdf).
- The new block-count inequalities were additionally checked in exact integer arithmetic for `M=1,…,16`, five rectangular side lengths per scale, and every site of each resulting rectangle: 1,629,584 site/rectangle/scale cases. These checks are supplementary; the general inequalities are proved without computation in Lemma 6.1.
- The probability tail and all chosen constants are justified by the displayed finite inequalities, not floating-point calculations or an unproved “exponential beats polynomial” assertion.
- No sub-agents were launched and no manuscript files were changed.
