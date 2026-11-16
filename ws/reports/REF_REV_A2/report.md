VERDICT: GAP

I checked all statements and proofs in `part/sec4-periodic-gap.tex` and `part/app-finite.tex`, and the wrapper `part/check.tex`, against the supplied `interfaces.tex`. Locations below are relative to `/home/ubuntu/aklt/review/REF_REV_A2/`. The original `main.pdf` was consulted only for background. Interface statements are treated as permitted results; their proofs and computational certificates are outside this audit.

The finite probability tools, stopped coupling, Hamming estimate, and periodic classical gap criterion are sound under their stated hypotheses and the supplied shell-geometry interface. The quantum conclusion is not established from the available contracts: three essential quantum results are neither stated nor proved in the permitted inputs. Two elementary geometric imports and the final target statement are also missing. I found no counterexample to the substantive inequalities proved locally.

1. **Critical — the quantum comparison, star constant, and kernel theorem have no supplied contracts.** Locations: `part/sec4-periodic-gap.tex:461` (`t:mainW`, invocation of `t:QD`), `:467` (`l:star`), `:468` and `:476` (`p:toruskernel`).

   **Exact claims.** The proof asserts that every eigenvalue of $H_{L,N}$ on $B_{L,N}^{\perp}$ is at least
   \[
   \frac{g_\star}{2}\lambda(\mu^{\mathrm{af}}_{\kappa,L,N}),
   \]
   that $g_\star>0$ is universal, and that $B_{L,N}\ne0$ and $\ker H_{L,N}=\mathbb C B_{L,N}$ for every $L,N\ge3$.

   **Why the proof does not close.** None of the labels `t:QD`, `l:star`, or `p:toruskernel` occurs as a definition or result anywhere in the part or `interfaces.tex`. In particular, $g_\star$ is not defined there. The available tight-frame isometry (`interfaces.tex:200`, `l:tight`) and classical finite-energy result (`interfaces.tex:257`, `l:planeenergy`) do not state a comparison between $H_{L,N}$ and the classical heat bath. The bound on the latter at lines 456–459 therefore does not, with the available imports, imply the claimed bound on the former. Nor is the asserted kernel theorem an available interface result.

   The background PDF does not provide the missing contract for the new setting: its Theorem 2.5, on pages 5–6, is stated for even $L,N\ge4$ with the then-current two-frame checkerboard construction. The present proof requires a result for arbitrary proper three-colourings using the three rotated twelve-letter frames, including odd periods. An extension may follow by adapting that proof, but it must be proved or explicitly supplied as an interface theorem.

   **Repair.** Prove the following contracts in the responsible part and include them in `interfaces.tex`, or insert their proofs here. These statements specify the scope and normalization needed by the current argument; merely adding unproved assertions to this part would leave the mathematical gap.

   ```latex
   \begin{lemma}\label{l:star}
   On $V_4^{\otimes5}$, with sites numbered $0,1,2,3,4$, set
   \[
      h_\star=\sum_{j=1}^4 P_{\{0,j\}}.
   \]
   This is a nonzero positive operator. Its smallest positive
   eigenvalue $g_\star$ exists, is strictly positive, and satisfies
   \[
      h_\star\ge g_\star(I-\Pi_{\ker h_\star}).
   \]
   \end{lemma}

   \begin{proposition}\label{p:toruskernel}
   For all integers $L,N\ge3$, the polynomial $B_{L,N}$ belongs
   to $\mathcal H_{\Lambda_{L,N}}$, is nonzero, and
   \[
      \ker H_{L,N}=\mathbb C B_{L,N}.
   \]
   \end{proposition}

   \begin{theorem}\label{t:QD}
   For all integers $L,N\ge3$ and every proper three-colouring
   $\kappa$ of $\Lambda_{L,N}$, use the site frames and
   antiferromagnetic probability of Definition~\ref{d:framemodel}.
   For every $\psi\in\mathcal H_{\Lambda_{L,N}}$ with
   $\langle B_{L,N},\psi\rangle=0$,
   \[
      \langle\psi,H_{L,N}\psi\rangle
        \ge \frac{g_\star}{2}
          \lambda(\mu^{\mathrm{af}}_{\kappa,L,N})\|\psi\|^2.
   \]
   \end{theorem}
   ```

   The normalization $1/2$ requires counting each edge twice in the sum of site-star Hamiltonians, while each heat-bath site is updated at rate one. With this contract, the multiplication at lines 464–465 is correct: $\tfrac12\cdot\tfrac{499}{500}=\tfrac{499}{1000}$. Positivity of a fixed nonzero positive finite-dimensional star operator requires no numerical lower bound, but the quantum comparison and the kernel identification still require proofs.

2. **Major — torus colouring and the local lift/sign change are invoked without definitions or proofs.** Locations: `part/sec4-periodic-gap.tex:415` (`t:mainW`, `l:colour`), `:426` and `:443` (`l:boxlift`).

   **Exact claims.** A proper three-colouring is available for every torus under consideration. Each conditional antiferromagnetic block law is identified, by a local sign change, with a ferromagnetic plane block law in the same alphabets; the identification preserves Hamming distances and single-site Dirichlet forms, and an exterior torus site has at most one lift in the block's one-neighbourhood.

   **Why the proof does not close.** Neither `l:colour` nor `l:boxlift` is in `interfaces.tex` or proved in the part. The sign change referred to at line 427 is not defined in the supplied text. These facts are true and elementary, but they are the steps that justify applying a plane theorem to a torus fibre, particularly for odd periods. They cannot be replaced by a global torus checkerboard sign convention on an odd torus.

   **Repair for `l:colour`.** The following can be inserted before `t:mainW`; identify residues modulo three with the three colour labels.

   ```latex
   \begin{lemma}\label{l:colour}
   Every $\Lambda_{L,N}$ with integers $L,N\ge3$ has a proper
   three-colouring.
   \end{lemma}
   \begin{proof}
   For $m\ge3$ and the representative $0\le j<m$, put
   \[
     c_m(j)=
     \begin{cases}
       2,&m\text{ is odd and }j=m-1,\\
       j\bmod2,&\text{otherwise}.
     \end{cases}
   \]
   Adjacent vertices of the cycle $\mathbb Z_m$, including its
   closing edge, have distinct $c_m$ values modulo three.
   Therefore
   \[
     \kappa([i]_L,[j]_N)=c_L(i)+c_N(j)\pmod3
   \]
   is proper: along each edge precisely one summand changes by
   a nonzero residue modulo three.
   \end{proof}
   ```

   **Repair for `l:boxlift`.** Here is an explicit statement and proof using only the available frame properties.

   ```latex
   \begin{lemma}\label{l:boxlift}
   Let $M\ge1$, $L,N\ge2M+3$ be integers, and let
   $p:\mathbb Z^2\to\Lambda_{L,N}$ be reduction. Put
   \[
     Q'=a+\{-M,\ldots,M\}^2,\qquad Q=p(Q'),\qquad
     Q'^+=a+\{-M-1,\ldots,M+1\}^2.
   \]
   The map $p$ is injective on $Q'^+$. Every torus
   nearest-neighbour bond meeting $Q$ has a unique lift to a
   plane nearest-neighbour bond meeting $Q'$.
   Let $\kappa$ be a proper torus three-colouring and
   $\bar\kappa=\kappa\circ p$. Given an exterior configuration
   $\beta$ for $Q$, put
   \[
     \varepsilon_z=(-1)^{z_1+z_2},\qquad
     n_z=\varepsilon_z s_{p(z)}\quad(z\in Q'),\qquad
     \eta_z=\varepsilon_z\beta_{p(z)}
       \quad(z\in Q'^+\setminus Q').
   \]
   This coordinatewise bijection carries the conditional law
   of $\mu^{\mathrm{af}}_{\kappa,L,N}$ on $Q$, given $\beta$,
   to $\mu^{+,\eta}_{\bar\kappa,Q'}$ (using only the needed
   exterior nearest neighbours). It preserves Hamming distances
   and conjugates the corresponding single-site conditional
   expectations.
   \end{lemma}
   \begin{proof}
   Coordinate differences in $Q'^+$ have absolute value at
   most $2M+2$, strictly below either period, proving
   injectivity. A nearest neighbour of a lift in $Q'$ belongs
   to $Q'^+$, so injectivity also proves the bond assertion.
   In particular no additional internal wrapping bond occurs.
   Antipodality makes every displayed sign change a bijection
   of the relevant site alphabet, preserving its uniform weight.
   For plane nearest neighbours $z,w$,
   $\varepsilon_z\varepsilon_w=-1$. Thus each internal bond
   factor becomes $1+n_z\cdot n_w$, and each crossing bond
   factor becomes $1+n_z\cdot\eta_w$. Normalization gives
   the asserted conditional law. A coordinatewise bijection
   preserves the set of disagreeing coordinates and carries
   conditioning off a site to conditioning off its image site.
   \end{proof}
   ```

   For a changed exterior site at torus distance one, the image of $Q'^+$ is the full torus one-neighbourhood of (Q), so the lift used at lines 443–445 exists and is unique. A corner exterior site supplies no crossing nearest-neighbour factor and has no effect on the block law, as the current proof correctly observes. These repairs also justify the claimed preservation of variances and Dirichlet forms by a finite change of variables.

3. **Minor — the final theorem being proved is not stated.** Location: `part/sec4-periodic-gap.tex:475` (`t:main`).

   **Exact issue.** The part ends with “Proof of Theorem `t:main`”, but neither the part nor `interfaces.tex` contains that theorem's statement or label. Thus the final proof cannot be compared with an exact export, as requested. The displayed proof establishes a clear candidate conclusion once Findings 1–2 are repaired.

   **Repair.** Include the intended theorem statement in the interface. If the intended conclusion is precisely the one used here, the following matches the proof's quantifiers:

   ```latex
   \begin{theorem}\label{t:main}
   For all integers $L,N\ge3$, $B_{L,N}\ne0$ and
   $\ker H_{L,N}=\mathbb C B_{L,N}$.
   There exist $c>0$ and an integer $L_0\ge3$ such that,
   for all integers $L,N\ge L_0$, every nonzero eigenvalue
   of $H_{L,N}$ is at least $c$.
   \end{theorem}
   ```

   If the intended main theorem has further conclusions, they require a separate comparison with this proof. The missing statement itself does not show a false inequality.

The statement table covers every mathematical environment in the assigned part, together with the final main-theorem proof. “Sound” below uses the expressly permitted interface results. Section labels `s:periodic-gap` and `a:finite` identify sections and make no additional claims. `check.tex` is a typesetting wrapper with no independent mathematical statement.

| Label and location | Content | Verdict | Dependencies |
| --- | --- | --- | --- |
| `d:shells`, `sec4-periodic-gap.tex:10` | Physical square, shell, boundary-strip, and exceptional-index definitions | Well posed for lattice exterior sites; agrees with the interface | Integer $u,l_0\ge1$, ambient lattice distances; `interfaces.tex:277` |
| `d:W`, `sec4-periodic-gap.tex:31` | Uniform window-marginal overlap for arbitrary admissible boundaries | Well posed; agrees with the interface | `d:shells`, `d:framemodel`; `interfaces.tex:298` |
| `l:stopped`, `sec4-periodic-gap.tex:56` | Full-law coupling with disagreement on $Q_h$ at most $(1-\delta)^{h-3}$ | Sound | Consistency, positivity, range one, finite energy, (W); imported `l:shellgeom`; local `l:CE`, `l:finitecoupling`, `l:surgery` |
| `p:surgery`, `sec4-periodic-gap.tex:198` | Far-set total variation at most $(1-\delta)^{u^{1/4}-4}$ | Sound, including $\delta=1$ | `l:stopped`, marginalization, coupling inequality, floor bound |
| `l:hamming`, `sec4-periodic-gap.tex:222` | Existence of a fixed integer radius $M=n^8$ and expected Hamming cost $\le M/1000$ | Sound under the preceding specification hypotheses denoted “as above” | `l:stopped`, finite Hamming bound, binomial tail inequality, Archimedean choice of $n$ |
| `t:periodic`, `sec4-periodic-gap.tex:306` | Block gap $T_M-S_MK$, site gap $g(1-S_MK/T_M)$, and factor $499/500$ | Sound | Range one, assumed block coupling and fibre gaps; exact torus label counts; `l:contraction`, `l:comparison` |
| `t:mainW`, `sec4-periodic-gap.tex:394` | (W) implies a uniform AKLT gap and one-dimensional kernel for all sufficiently large periods | GAP | Available `l:planeenergy`, `l:threeframes`, `l:hamming`, `t:periodic`; unavailable `l:colour`, `l:boxlift`, `t:QD`, `l:star`, `p:toruskernel` |
| `t:main` proof, `sec4-periodic-gap.tex:475` | Computational inputs imply response, then (W), then the quantum conclusion | GAP; target statement missing | Available `t:inputs`, `t:rec`, `t:cutMOS`; `t:mainW` and unavailable `p:toruskernel`; see Findings 1–3 |
| `l:CE`, `app-finite.tex:22` | Conditional expectation is an orthogonal projection; conditional and total variance identities | Sound for real and complex functions | Positive finite probability, nonempty alphabets, grouping finite sums |
| `l:finitecoupling`, `app-finite.tex:68` | Maximal coupling, marginalization, completion, Hamming bound, and common-measure domination | Sound | Finite probability identities; residual-mass construction with separate $t=1$ case |
| `l:surgery`, `app-finite.tex:132` | Pair-dependent resampling kernels preserve both full marginals | Sound | Per-input conditional marginals, `l:CE`; consistency for the specification interpretation |
| `l:density`, `app-finite.tex:163` | Density comparison, product tensorization, gap $m/M$, and frame-block gap $r_b^{\lvert E(Q)\rvert}$ | Sound | `l:CE`, positive normalized probabilities, commuting product projections; `d:framemodel`, `d:frame`, `l:threeframes` |
| `l:comparison`, `app-finite.tex:253` | Block-to-site comparison with multiplicity $t_{\max}/(cg)$ | Sound | Uniform fibre Poincare inequalities, block Poincare inequality, `l:CE` |
| `l:contraction`, `app-finite.tex:297` | Hamming contraction gives gap $c$ for the unnormalized block sum | Sound | `l:CE`, coordinate paths, finite real symmetric diagonalization, $0<c\le A$ |

The supplied interface results that are actually available are used within their hypotheses:

| Interface result | Application and hypothesis check |
| --- | --- |
| `l:shellgeom`, `interfaces.tex:317` | In `l:stopped`, $u\ge M_{\mathrm g}(l_0)$ and all construction indices satisfy $2\le i\le h+1\le\lfloor s\rfloor+1=i_1$. The proof uses the shell inclusion, separator property, exceptional-set count, and strip cardinality exactly as stated. |
| `l:threeframes`, `interfaces.tex:211` | Supplies $0<r_b<1$, positive edge factors in $[b,2-b]$, and antipodality. The density application uses distinct frames at every internal and crossing bond, guaranteed by proper colouring. |
| `l:planeenergy`, `interfaces.tex:257` | Supplies consistency, full support, nearest-neighbour dependence, and uniform $\alpha=12^{-1}r_b^4$. Its plane block-gap clause is applied after the proposed local lift, with exactly $2(2M+1)(2M)$ internal edges. It does not itself supply that lift or a quantum comparison. |
| `t:inputs`, `interfaces.tex:642` | The final chain uses the same fixed pair $(961/1000,187/200)$, $C_V=10\ge1$, and the stated type-dependent (H3\(_h\)). The exact rational $q$ is strictly between zero and one. |
| `t:rec`, `interfaces.tex:613` | Its three hypotheses are exactly those supplied by `t:inputs`; its conclusion gives $A\ge2$, $0<\theta<1$, and $\mathsf P(A,\theta)$. |
| `t:cutMOS`, `interfaces.tex:329` | Applies to that response property and supplies (W) with $l_0=64$, $p_0\in(0,1]$, positive integer $M_\star$, and the required uniformity in colouring and translation. |

For formalization, take the shell point $y$ in $\mathbb Z^2$, the radii and indices in the indicated integer domains, and the shell parameter $s$ in $\mathbb R$. In `l:hamming`, “as above” must retain all of `l:stopped`'s specification hypotheses, including the uniform fully conditional one-site bound. The following details are material.

- **Conditional laws and empty products.** Positivity makes every complement-fibre denominator positive, including when the updated set or its complement is empty. For a completed coupling of laws with possible zero masses in `l:finitecoupling`, conditionals on zero-mass marginal values can be chosen arbitrarily; those values are never sampled. The empty product has its one configuration. For singleton products, express the lower bound as a Poincare inequality, as the text prescribes, or use an extended-real variational gap with infimum of the empty set equal to infinity; a real-valued empty infimum cannot be used for this convention.

- **The resampling construction is valid without conditioning the output law on success.** At each fixed input pair, both branches have precisely the required $F_i$ marginals. Completing the $B_i$ coupling and then resampling $A_i$ preserves those marginals. The common assignment on $A_i$ is chosen using each site's own alphabet; no identification of alphabets at distinct sites is needed. The independent resamplings hit it with probability at least $\alpha^{2|A_i|}\ge\alpha^{16l_0}$, while leaving $B_i$ fixed.

- **Shell indices and persistence.** The proof uses (W) only for trial indices $i\le h\le\lfloor s\rfloor$, never for the possibly larger propagation index $h+1$. At most one exceptional index excludes at most two trial indices, giving $|J|\ge h-3\ge1$. A successful trial is followed by an unskipped identical resampling. For every later $j\ge i+2$, $s\ge16$ implies $\lfloor(j-1)s\rfloor>is$; hence the later separator lies in the region already coupled identically. Conditional failure bounds are applied to finite histories; independence between trials is unnecessary. Empty shells and $\delta=1$ are covered by the proof's explicit branches.

- **Real powers and integer choices.** In `p:surgery`, $s\ge16$, $h=\lfloor s\rfloor\ge4$, $hs\le s^2$, and $h-3\ge s-4>0$. Handle $\delta=1$ separately before using logarithms or real-power monotonicity. In `l:hamming`, $d_0>0$, $d_0\le1/2$, $n\ge44$, and all reciprocals are positive. The factorial estimate uses $n-22\ge n/2$. No enumeration at the enormous chosen radius is needed: an Archimedean integer above the displayed finite maximum suffices.

- **Hamming constants.** For the same full-law coupling from `l:stopped`, disagreement is confined to at most $25n^6$ sites unless the far-set event fails. The total volume is at most $25n^{16}$. The two numerical conditions on $n$ give separately
  \[
    25n^6\le\frac{n^8}{2000},\qquad
    25n^{16}(1-d_0)^{n-3}
      \le\frac{25\,2^{20}20!}{d_0^{20}n^4}
      \le\frac{n^8}{2000}.
  \]
  Thus the asserted $M/1000$ bound follows with the stated constants.

- **Label counts and update rates.** Count centre labels with multiplicity, even if blocks or conditional operators repeat. The offset squares have injective reductions because $2M+2<\min(L,N)$, including equality $L=2M+3$ or $N=2M+3$ in the theorem's lower bounds. Thus a site belongs to exactly $T_M$ labels and is outside but at distance one for exactly $S_M$ labels. The normalized kernel is $A^{-1}\sum_a E_{Q_a}$, whereas the block generator is $A(I-P)$. Its gap is $c=T_M-S_MK$; block-to-site comparison divides by $T_M$. This yields the claimed $g(1-S_MK/T_M)$, with no missing $LN$ factor.

- **Density comparison and complex functions.** The variational formulas use squared absolute values and the complex orthogonal projection. Taking minima preserves the lower density comparison. The commuting product projections give mutually orthogonal increments, including with singleton alphabets. In a frame block, absorbing all positive fixed boundary factors into the product probability leaves only internal bond factors in the density ratio. The normalization $\pi(\psi)$ cancels from the ratio of bounds, giving exactly $r_b^{|E(Q)|}$, with no boundary-edge exponent.

- **Contraction to a Poincare inequality.** On a nontrivial product, Hamming-neighbour pairs exist and their coordinate paths connect the whole space, so a nonconstant real function has positive Lipschitz seminorm. The weighted conditional-expectation matrix is similar to a real symmetric matrix; the mean-zero subspace is invariant. Its real eigenvectors satisfy $|\lambda|\le1-c/A$. The real and imaginary parts then give the complex Poincare inequality. The separate one-point case and $c=A$ case are valid.

- **Uniformity and parity.** The chosen $n,M,L_0,g_M$ precede all periods, block placements, boundary fibres, and colourings. After the repairs in Finding 2, the gauge is defined separately on each lifted block and its exterior neighbours, so odd periods introduce no inconsistency. The resulting $g_M=r_b^{2(2M+1)(2M)}>0$ is uniform. The passage from this classical bound to $c=499g_\star g_M/1000$ remains dependent on the missing quantum contract in Finding 1.

Exact supplementary computations used one Python process with integer arithmetic and `fractions.Fraction`. They confirmed the six absent reference labels listed in Findings 1–3; $0<1119948287353/1120437614225<2499/2500<1$; the factor $499/1000$; and the identity
\[
 \frac{(8M+8)M}{1000(2M+1)^2}
   =\frac1{500}\left(1-\frac1{(2M+1)^2}\right)
   <\frac1{500}
\]
for $1\le M\le40$, alongside its direct algebraic verification. The falling-factorial estimates were checked for $44\le n\le100$. The proposed explicit colouring was checked for all 121 pairs $3\le L,N\le13$. Halo injection, nearest-neighbour lifting, and the local parity signs were checked in 80 small configurations with $1\le M\le5$ and $2M+3\le L,N\le2M+6$, including the minimal odd periods. These finite checks supplement the general arguments above; they do not supply the missing quantum theorems.
