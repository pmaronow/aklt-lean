VERDICT: ACCEPT WITH FIXES

| Finding ID | Implemented correctly? | Evidence in commit `9222abe`, and check |
|---|---|---|
| R4-1 | yes | [sec6-walks.tex:90](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:90), :99–109, :139–144, :254–276; [sec7-recursion.tex:126](/home/ubuntu/aklt/manuscript-corrected/sec7-recursion.tex:126). Direct integration gives \(\rho_1=(3/5)/(1+\mathbb E P_{fo}/5)\le3/4\) at an initial two-bond D site. Later D departures have ratio \(3/5\). Exposure has the required initial-degree restriction; both recursion starts satisfy it. The exceptional initial factor is at most \(1/4\), below the first lattice weight. |
| R4-2 | yes | [sec7-recursion.tex:17](/home/ubuntu/aklt/manuscript-corrected/sec7-recursion.tex:17)–89. Initial U normalization occurs before the empty prefix. The induction distinguishes the live D endpoint, with one kept bond after arrival, from non-live D sites, with two. Removing an interior live endpoint restores the consistent-domain rules. The eight-step returning trail checks these assertions and accumulates mass \(3/5\). |
| R4-3 | yes | [sec6-walks.tex:18](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:18)–31, :51–78, :213–222, :238–276; [sec7-recursion.tex:138](/home/ubuntu/aklt/manuscript-corrected/sec7-recursion.tex:138)–170. Auxiliary networks retain original pins and positive scalar mass. The step identity and pair expansion extend to them. The second expansion carries one fixed defect at its first boundary endpoint. Only the twelve other sites within graph distance two can be exceptional. The common pointwise majorant bounds the sum of pinned/free maxima and gives the unchanged \(C_T=2(12/5)^{24}(C_V/(1-q))^2\). |
| R4-4 | yes | [sec6-walks.tex:82](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:82)–85. Endpoint independence is now asserted only for a D target with one initial present bond. Arrival removes that bond, leaving precisely \(\lambda_D\), whose squared-norm mean is \(3/5\). |
| R4-5 | yes | [sec6-walks.tex:163](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:163)–191. The passage site keeps its three non-arrival bonds; other U sites are full. Covering tips and both corner slots are explicitly distinguished from global domain data. Filling an absent factor by the average of opposite unit-slot factors is valid for both integrals. The reconstructed effective keys equal all 7,962 supplied keys, including the 2,696/5,266 type split. |
| R7-1 | yes | [sec7-recursion.tex:39](/home/ubuntu/aklt/manuscript-corrected/sec7-recursion.tex:39)–52 and :138–170; [sec6-walks.tex:18](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:18)–31. Consistent-domain removal is restricted to endpoints outside S; local-pattern assertions concern actual departures. A terminal protected U site retains its pins and loses only its arrival bond. No removal of that protected site is claimed. Its subsequent use is through the auxiliary-network proposition. |
| R5-1 | yes | [app-tail.tex:75](/home/ubuntu/aklt/manuscript-corrected/app-tail.tex:75)–96, :120–123, :151–164, :186. The remainder lemma allows nonnegative z. Its induction uses no division and remains valid at zero coordinates. The window graph has exactly 64 zero-indegree windows; all four vector phases vanish exactly there, and no update can deposit terminal mass there. Positive-support ratios and rejecting guards are specified. The regenerated dyadic vector satisfies the exact rational sub-invariance test. |
| R5-2 (CONFIRMED-MODIFIED) | yes | [app-tail.tex:128](/home/ubuntu/aklt/manuscript-corrected/app-tail.tex:128)–174; [sec8-computer-assisted.tex:3](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:3). The seven production files, commands, source provenance, rational assembler and exact dyadic denominator are identified accurately. Independent rational assembly reproduces all fourteen table entries. The old B ceiling is correctly raised to 0.987731 and the comparison interval to [1.0000322,1.0000333]. The sufficient scaled old bound is strictly below 0.98779. See minor residual description/layout issues D1–D2 below. |
| R5-3 | yes | [sec8-computer-assisted.tex:33](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:33)–41. The text names the existing `reports/ADJ-R5/audit/alm8_checked.c`, rather than attributing its repairs to the original `alm8.c`. It validates the fixed instance and computes powers only through \(4^8\). A fresh UBSan build/run succeeds and regenerates the archived integer certificate byte for byte. Fixed-instance codes, grid positions, CSR sizes and integer sums fit their types. |
| R5-4 | yes | [sec8-computer-assisted.tex:36](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:36)–41. Certified output uses upward decimal rounding and an exact hexadecimal value. The decisive comparison \(0.85594872<(3923/4000)^8\) holds in rational arithmetic; a numerical root is not used. |
| R5-5 | yes | [sec6-walks.tex:227](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:227)–235, :239–254; [sec8-computer-assisted.tex:16](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:16), :41–45. Only initial reversal is forbidden; the virtual incoming bond is not otherwise marked used. The one-point lemma explicitly requires that bond absent. Both recursion starts and the kernel have the removed center as this neighbor. Fresh integer trail histograms give normalized base maxima 1.472242… and 1.505152…, hence \(C_V\le153\) with the ratio-100 vector. |
| R5-6 | yes | [app-tail.tex:129](/home/ubuntu/aklt/manuscript-corrected/app-tail.tex:129)–146, :179–187. Mode A contributes only through even length 106; mode B begins at 108. The 108-step witness really produces a false-image deletion at passage 54. The additional unsplit start-site deletion is disclosed, distinguished from the defined walk, and justified by the three available bonds at u. Actual mode-B table records use `tailmem4.c`. The optional variant's seven records and stronger rule are identified. |
| R6-1 | yes | [sec6-walks.tex:163](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:163)–191. Shared with R4-5. Full U kept sets, the three passage-site bonds and both covered corner slots are explicit. Exact enumeration gives 106,101 site assignments before choosing an out-neighbor and exactly the supplied 7,962 effective classes. The broader-reading counterexample is excluded without changing H1's thresholds. |
| R6-2 | yes | [app-local.tex:282](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:282). The uniform reduced bound is \(k\le11\); unreduced configurations can have 12 vectors. All actually selected representations have at most 11. Graph-derived counts confirm the counterexample ID 113 has unreduced/reduced dimensions 12/9 and confirm both files' selected dimensions. |
| R6-3 | yes | [sec1-intro-statement.tex:18](/home/ubuntu/aklt/manuscript-corrected/sec1-intro-statement.tex:18); [sec8-computer-assisted.tex:78](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:78)–89; [app-constants.tex:17](/home/ubuntu/aklt/manuscript-corrected/app-constants.tex:17); [app-local.tex:196](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:196), :270–296. The fractions are exact individual example values, with IDs retained. Global optimality is explicitly uncertified. Rational branch integration and the L,Q test establish all three named example values, with equality attained at t=1. No certificate claims the larger global minima. |
| R6-4 (CONFIRMED-MODIFIED) | yes | [app-local.tex:282](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:282), :292–300. The cited full-archive programs and records exist and concern the same pattern data and certificate choices. The comparison is correctly described as a ratio comparison: 23,893 points, maximum discrepancy 2.341836…×10⁻¹⁵. The other excess is rounded upward to 2.5×10⁻¹⁵. The precise negative-control thresholds, independent verifier records and 600-case test provenance are supplied; the missing mutation driver is disclosed. See layout issues D3–D4 below. |
| R6-5 | yes | [app-local.tex:284](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:284), :286, :300. The description acknowledges binary64 shadows and exact small moment tensors. With the stated eta, a passing contraction guard gives \(s<2^{61}/\eta\), three contractions fit below \(2^{63}\), and the independent coefficient shadows give sums below \(2^{58}/\eta<2^{59}\). Inspecting `cert.py` confirms contraction sizes, nonnegativity, the independent shadow construction and the later unbounded-integer steps. Accepted computations cannot hide wrapped coefficients. |
| R6-6 | yes | [app-local.tex:263](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:263). Unit directions are chosen freely at zero radii. The dot-product and sum-norm identities hold without dividing by a radius. The denominator is positive, and when either radius vanishes the scalar expression is independent of t. The removed-root example 5469 is covered. |
| R6-7 | yes | [sec8-computer-assisted.tex:85](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:85). The largest tested exchange-split block is correctly 179×179. Counting central weights in every selected representation gives 12,173 exchange blocks and maximum 179, including ID 711. The historical 245 at ID 3596 is the sum 131+48+48+18. The unchanged upper bounds “at most 245” remain true. |
| R1-1 | yes | [sec2-frames-Q.tex:114](/home/ubuntu/aklt/manuscript-corrected/sec2-frames-Q.tex:114)–128. The product of incident orientation signs is absorbed into rho_x and also appears in the star-kernel factorization. This makes both polynomial identities exact. The sign is constant on the conditional fiber, so the projection/intertwining and gap comparison are unchanged. |
| R1-2 | yes | [sec2-frames-Q.tex:155](/home/ubuntu/aklt/manuscript-corrected/sec2-frames-Q.tex:155). The interval bounds each individual internal or boundary bond factor, with positive site weights. It no longer purports to bound a product or normalized probability by one factor. Strict positivity and finite energy still follow. |
| R1-3 | yes | [sec2-frames-Q.tex:63](/home/ubuntu/aklt/manuscript-corrected/sec2-frames-Q.tex:63)–80. The explicit dual coordinates give an internal exact proof. Sign symmetry kills odd monomials; the second/fourth moments are 1/3, 1/5 and 1/15. Exact arithmetic verifies all 112 monomial comparisons, all twenty face triples, and the 240 cross-frame dot-product squares. The retained gamma values agree. |
| R2-1 | yes | [sec3-knabe.tex:105](/home/ubuntu/aklt/manuscript-corrected/sec3-knabe.tex:105)–117. Zero total energy is treated before division. Positivity then annihilates every Q_x and both sides of the required inequality. In the remaining branch \(\sum_aY_a>0\); individual zero summands are omitted as before. Both finite-size prefactors are retained. |
| R2-2 | yes | [sec3-knabe.tex:7](/home/ubuntu/aklt/manuscript-corrected/sec3-knabe.tex:7); [sec4-mixing-to-gap.tex:7](/home/ubuntu/aklt/manuscript-corrected/sec4-mixing-to-gap.tex:7). Nontrivial single-site spaces and nonempty volumes ensure the asserted gaps are finite positive real numbers. All actual frame/cell applications already satisfy these conditions. Partition functions and probability marginals on empty sets remain well defined. |
| R2-3 | yes | [sec4-mixing-to-gap.tex:101](/home/ubuntu/aklt/manuscript-corrected/sec4-mixing-to-gap.tex:101)–103. A new success probability is asserted only for unskipped i≤s. The final step only preserves agreement already achieved. Every i in the propagation set J lies in the valid range, and \(|J|\ge\lfloor s\rfloor-3\ge s-4\); conditional failure probabilities give the same exponent without independence. |
| R2-4 | yes | [sec4-mixing-to-gap.tex:37](/home/ubuntu/aklt/manuscript-corrected/sec4-mixing-to-gap.tex:37), :68, :81. Square sizes and thresholds are integral, l₀ is a positive integer and shell indices are integers, while s=M¹/⁴ remains real. This validates the cell counts, shell radii and subsequent cut-depth identities. |
| R2-5 | yes | [app-constants.tex:17](/home/ubuntu/aklt/manuscript-corrected/app-constants.tex:17) and the example passages listed under R6-3. The unsupported class-minimum row is replaced by the two exact example fractions; the introduction and repeated “tightest” labels are qualified consistently. H1 and the obstruction 416114/444675 retain their established meanings. |
| R3-1 | yes | [sec5-cut.tex:11](/home/ubuntu/aklt/manuscript-corrected/sec5-cut.tex:11), :79. Choosing a common unit spin away from finitely many antipodal pins gives an open product set of positive density and positive measure. Boundedness gives finiteness. Empty ordinary domains have normalizer one; positive uniform components and scalar trace masses preserve positivity. Positive frame weights also give full support to the reference window law, so the displayed ratios and logarithms are defined. |
| R3-2 | yes | [sec5-cut.tex:102](/home/ubuntu/aklt/manuscript-corrected/sec5-cut.tex:102), :221. The removal formula now requires p≥1. At its application, finite nonempty U′ has an exterior nearest neighbor, so X is nonempty; its established connectivity supplies a rooted spanning-tree ordering. |
| R3-3 | yes | [sec5-cut.tex:179](/home/ubuntu/aklt/manuscript-corrected/sec5-cut.tex:179). Signed depths cover the three cases: original side meets the square, lies beyond the chosen edge, or lies beyond the opposite edge. Their shifted depths are respectively above, below, or above the forbidden depth interval. The strict near-side comparison follows from j≤s/12 and s>3l₀. Thus no sides coincide and the conservative 48-cell/192-site count remains valid. |
| R3-4 | yes | [sec5-cut.tex:229](/home/ubuntu/aklt/manuscript-corrected/sec5-cut.tex:229). With M=s⁴ the crude count is O(s⁸), at depth at least cs−C. Therefore F(d)=O(d⁻⁸) gives a uniform bound; little-o makes this contribution vanish. The revised remark correctly separates these conclusions. |
| R7-2 | yes | [sec1-intro-statement.tex:30](/home/ubuntu/aklt/manuscript-corrected/sec1-intro-statement.tex:30), :32. The overview includes the first-removal additive residual and both stopping classes with terminal factors. The quartic bracket has magnitude at most 243/625, with response at most 486/625; its contribution is covered by 0.0707. Boundary-stopped trails give the T₂ error rather than a kernel term. |
| R7-3 | yes | [sec1-intro-statement.tex:44](/home/ubuntu/aklt/manuscript-corrected/sec1-intro-statement.tex:44). Unit physical/continuous spins and pins are distinguished from auxiliary sphere-plus-zero spins. This agrees with the D atom of mass 2/5 and the squared-norm expectation 3/5. |
| R7-4 | yes | [sec4-mixing-to-gap.tex:138](/home/ubuntu/aklt/manuscript-corrected/sec4-mixing-to-gap.tex:138). The corrected dependency claim allows earlier frame definitions and shell geometry. The cut proof assumes P; Sections 6–8 establish P independently of the mixing/gap conclusions. The scale and constant choices remain acyclic. |
| R7-5 | yes | [sec2-frames-Q.tex:63](/home/ubuntu/aklt/manuscript-corrected/sec2-frames-Q.tex:63)–80. The same internal exact coordinate proof implements this duplicate of R1-3 once. No unlocated design assertion remains necessary. |
| FN-R1-square | yes | [sec1-intro-statement.tex:24](/home/ubuntu/aklt/manuscript-corrected/sec1-intro-statement.tex:24). The introductory claim now uses normalized squared modulus, frame reference weights and the checkerboard map. This is exactly \(\mu^\circ(s)=\pi(s)|\iota B(s)|^2/\|B\|^2\), followed by the sitewise change of variables. |

All 36 adjudicated corrections, including both CONFIRMED-MODIFIED findings, are mathematically implemented. The fixes below concern one inherited quantitative description and three new typesetting defects. No change to a theorem, hypothesis constant, kernel entry or proof estimate is required.

**D1 — Minor: the memory description assigns the two-array storage to one array.** Location: [app-tail.tex:149](/home/ubuntu/aklt/manuscript-corrected/app-tail.tex:149), inherited from frozen line 119.

There are exactly 376,897,024 entries in one time layer. One binary32 array occupies 1,507,588,096 bytes, approximately 1.51 GB. The original C programs allocate both V and Nv, giving approximately 3.02 GB for these two arrays. The existing parenthetical “three gigabytes in single precision” follows the single-array entry count and is therefore inaccurate as written. This is an inherited archive-description issue, not a new mathematical error.

Replace exactly:

```latex
(three gigabytes in single precision)
```

with:

```latex
(about $1.51$ GB for one binary32 array, or $3.02$ GB for the two successive-time arrays)
```

**D2 — Minor: new archive-list overflow.** Location: [app-tail.tex:183](/home/ubuntu/aklt/manuscript-corrected/app-tail.tex:183), PDF page 40.

The optional-variant record list produces a new overfull box of 10.16882 pt. Replace this exact fragment:

```latex
\texttt{c961\_\allowbreak 935\_\allowbreak B\_\allowbreak C.txt} in
```

with:

```latex
\texttt{c961\_\allowbreak 935\_\allowbreak B\_\allowbreak C.txt}\linebreak
in
```

**D3 — Minor: new negative-control citation overflow.** Location: [app-local.tex:296](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:296), PDF page 49.

The two archive paths produce a new overfull box of 1.81375 pt. Replace:

```latex
\texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak code/\linebreak[1]negctl.py} and
```

with:

```latex
\texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak code/\linebreak[1]negctl.py}\linebreak
and
```

**D4 — Minor: new independent-implementation citation overflow.** Location: [app-local.tex:298](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:298), PDF page 49.

The opening program list produces a new overfull box of 30.32309 pt. Replace:

```latex
\texttt{73-\allowbreak reimplement-\allowbreak H1/\allowbreak code/\linebreak[1]wick.py}, \texttt{opcert.py}
```

with:

```latex
\texttt{73-\allowbreak reimplement-\allowbreak H1/\allowbreak code/\linebreak[1]wick.py},\linebreak
\texttt{opcert.py}
```

These four replacements are also supplied as [proposed-fixes.patch](/home/ubuntu/aklt/reports/DELTA-1/proposed-fixes.patch). I applied them only in [fixes-preview/](/home/ubuntu/aklt/reports/DELTA-1/fixes-preview). That copy builds successfully, eliminates all three new overfull boxes, and preserves all 180 compiled label numbers. The ten overfull boxes already present in the frozen manuscript remain; their exact widths are unchanged. They are recorded as inherited layout debt rather than attributed to the correction edit.

**Review scope and mathematical verification.** I reviewed `git diff 32487a2 9222abe` and the four successive parent-to-commit diffs: `32487a2→ade1a62`, `ade1a62→13b8ecf`, `13b8ecf→720cfb7`, and `720cfb7→9222abe`. They are retained in [evidence/](/home/ubuntu/aklt/reports/DELTA-1/evidence). The first checkpoint implements all sixteen ADJ-R4 replacements byte for byte. Later checkpoints correctly merge the overlapping full-U, zero-support, initial-arrival and example-value corrections. All changed frozen source lines belong to adjudicated corrections or the necessary update of the tail trust paragraph to identify the guarded implementations. Remaining differences within the new text are copyediting and path wrapping. I found no unrelated substantive edit.

I re-derived the affected identities from the spherical second/fourth moments, the kept-set trace rules and the finite-volume definitions. In particular:

- At D departure, the two-bond integral is \(1+P_{fo}/5\), while removal contributes scalar mass \(3/5\). At U departure, the three-bond and two-bond integrals are the unchanged I and J. These establish the revised ratios and the applicability of the unchanged response bounds. The exposure telescope then holds with equal D factors. The normalized closure induction gives every T₁ response pair the original envelope class; the marked boundary defect in T₂ stays outside every template at distance greater than two. With \(K=(12/5)^{12}C_V/(1-q)\), each one-point expansion is bounded by \(Kq^{d(\cdot,S)}\), and the two boundary conditions contribute exactly \(2K^2\).
- The nonnegative remainder induction is valid because a target state has the unique predecessor quotient site \(\xi'-d'_m\). Thus \(V_{t+1}\le a\lambda^{t-T}z\mathbb W\le a\lambda^{t+1-T}z\), including at zero coordinates, with no quotient-volume factor. The exact window-graph check gives 60,092 windows, 169,092 edges, and the stated 64 zero columns. The actual dyadic candidate passes all four phase inequalities.
- For the local examples, exact branch integrations give the radii \((\rho_o,\rho_f,\rho_g)=(7/24,740/2193,3/25)\), \((112/275,112/275,3/25)\), and \((169/385,169/385,0)\). Substitution at t=1 gives exactly 3825127/3979368, 1071655/1145463 and 416114/444675. The rational endpoint/vertex tests of L and Q prove the corresponding lower bounds; aligned branches attain them. This proves the individual values without assuming global optimality or relying on a finite failed test just above them.
- For the shadow guard, \(\eta=(1-2^{-53})^2(1-32\,2^{-53}/(1-32\,2^{-53}))>1-10^{-12}>3/4\). Nonnegative contractions have at most sixteen products. This gives the stated conversion/rounding lower bound, fits each sum of three contractions in signed int64, and makes the later independent shadows sufficient even if a rejected candidate coefficient array had wrapped. The signed Pauli operations retain their guards/fallback; final positivity uses Python integers.
- The minor proof repairs preserve the positive-normalizer argument, the zero-energy branch of the weighted criterion, the valid surgery index range, and the signed-depth exclusion. Integer M and positive integer l₀ are used consistently at subsequent applications. The complete chain still gives \(\lambda(\mu_D)\ge c_0m_0/2\) and \(\operatorname{gap}(H_{L,N})\ge g_\star c_0m_0/4\).

The retained adjudicator arithmetic/geometry scripts were inspected and replayed as corroboration; their output is distinguished from the delta-specific checks in [audit_delta.py](/home/ubuntu/aklt/reports/DELTA-1/audit_delta.py). That script independently checks source scope, numbered objects, the freshly generated H2 certificate, restricted base sums, all table entries, the revised old-run interval/scaling, and the optional aggregate. Its [complete output](/home/ubuntu/aklt/reports/DELTA-1/evidence/delta-checks.log) passes.

**Archive verification.** The repaired H2 source was compiled locally with `gcc -O2 -g -frounding-math -ffp-contract=off -fsanitize=undefined -fno-sanitize-recover=undefined`. The fresh run at `8 8 9610 9350` produced upward bound `0x1.b63ee8cbca081p-1`, displayed as 0.85594871032391507, and regenerated the archived integer/vector data exactly. Rational evaluation gives

\[
\lambda=\frac{6108544377608925591520707327811288131392849080}{7136577582199331027120815376144776530746764161}
\le0.8559487104<0.85594872<(3923/4000)^8.
\]

The fresh length-15 histogram enumeration gives \(100\max_{8\le n<16}\mathsf W_nq^{-n}=150.5152837\ldots<153\) under the corrected initial convention. The optional 1/5-window certificate also satisfies \(\lambda<(0.97606)^8\) by exact evaluation. See [H2 run](/home/ubuntu/aklt/reports/DELTA-1/evidence/h2-rerun.log), [base sums](/home/ubuntu/aklt/reports/DELTA-1/evidence/H2-base-sums.log), and [additional checks](/home/ubuntu/aklt/reports/DELTA-1/evidence/final-extra-checks.log).

Parsing the actual full-tree tail outputs as decimal rationals, with the correct disjoint length ranges and class multiplicities, gives total numerators 0.987762443170525 and 1.1914067844431. The latter divided by the stated dyadic h_C is 0.968623401986260… . Each of the fourteen displayed table entries is its specified six-decimal ceiling. The old bounds and optional bounds also reproduce exactly. The exact source hashes and invocation records support the coefficient inputs and compiler flags. The identified H1 archive records cover the same 7,962 data/certificate choices and support the amended validation descriptions; they do not supply sharper global local minima. See [archive inventory/hashes](/home/ubuntu/aklt/reports/DELTA-1/evidence/provenance-checks.log), [H1 archive checks](/home/ubuntu/aklt/reports/DELTA-1/evidence/R6-archives-replay.log), and [tail support/geometry](/home/ubuntu/aklt/reports/DELTA-1/evidence/tail-support-geometry.log).

This review checks the existing production-output certificate under its stated directed-arithmetic/implementation assumptions. I did not rerun the full H1 operator suite or the memory-10 production time evolution. The terminal production arrays and unrounded terminal maxima are not archived; the manuscript identifies the original production records separately from the guarded audit copies and does not claim a new production rerun. The new archive references are real locations in the supplied project, including `reports/ADJ-R5/audit/`; the unchanged smaller frozen program bundle is not a standalone copy of every cited validation file.

**Build and preservation.** `latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex` succeeds in [build/](/home/ubuntu/aklt/reports/DELTA-1/build), extracted from `9222abe` under this working directory, and produces [main.pdf](/home/ubuntu/aklt/reports/DELTA-1/build/main.pdf), 50 pages. The [converged build log](/home/ubuntu/aklt/reports/DELTA-1/evidence/latexmk.log) has no build errors, undefined references/citations or pending label reruns. A separate frozen build gives 47 pages. All 180 source labels, all 180 compiled label numbers, every numbered-environment count, and all ten theorem-environment statements are preserved. The main theorem, Hamiltonian, response envelopes, hypothesis P, kernel and recursion display are unchanged byte for byte. The initial-arrival restriction added to H2 is satisfied at every analytic use, so it does not weaken the main result.

No input repository or archive file was modified, and no sub-agents were launched. All generated files are under `/home/ubuntu/aklt/reports/DELTA-1/`.
