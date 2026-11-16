VERDICT: GAP

This verdict concerns the supplied certificate for (H3′), not a counterexample to the claimed spectral-radius bound. The analytic trail domination and remainder arguments are sound under their stated hypotheses. However, the vector actually constructed by the tail programs does not satisfy the remainder lemma's strict-positivity hypothesis, and the production outputs and exact assembly needed to check Table 2 are absent from the frozen bundle. These issues need resolution before I would accept Theorem 8.1's (H3′) part as certified. The H2 bound is recoverable by local code corrections; I reproduced a sufficiently strong directed-rounding bound.

I read all the manuscript's TeX sources for context and checked the assigned parts of Section 8 and Appendix C against `alm8.c`, `tailmem4.c`, and `tailmem5.c`. I also inspected the nearby certificate-assembly scripts and the changes in `tailmem6.c` relevant to the optional refinement. H1 and the derivation of the response coefficients elsewhere in the paper are outside this lane. Locations below are relative to `bundle/`, unless prefixed by `audit/`. No web sources or subagents were used. The bundle was not modified.

## 1. Findings

### 1. Major — The constructed tail vector has zero entries, so the stated remainder lemma cannot be applied to it

**Location:** `manuscript/app-tail.tex:76` (`l:remainder`), `:90`, `:114` (`p:tail`); `programs/h3-tail/code/tailmem4.c:245`, `:319`, `:336`, `:340`; corresponding `tailmem5.c:254`, `:330`, `:347`, `:351`.

**Exact claim.** Lemma `l:remainder` assumes

\[
z:\Omega\times\{A,B,C,D\}\longrightarrow(0,\infty),
\qquad z\mathbb W\le\lambda z.
\]

The proof of Proposition `p:tail` invokes that lemma with the programs' vector and \(a=\max V_{260}/z\).

**Failure.** Some windows have no predecessor. For example, the ten directions

\[
E,E,N,W,W,S,W,S,E,N
\]

form a trail that returns to its starting site after using all four incident bonds there. No step can be prepended to this window without repeating a bond. Consequently its column in every relevant transition block is zero. The left power iteration sets its coordinate to zero immediately; the post-response iterations also give zero there.

An actual memory-10 enumeration found **60,092 windows, including 64 with zero indegree and 64 with zero outdegree**. Running the vector construction at the paper's constants produced **64 zero coordinates in each of A, B, C, D**. All other coordinates were positive and finite. The directed sub-invariance check passed. Thus the problem is specifically the strict-positivity hypothesis, not a failure of the checked inequality.

On these coordinates the loops computing `worst` and `alpha` perform `0/0`. Under the assumed IEEE behavior this produces NaNs which comparisons silently ignore. A printed `check=OK` therefore does not establish all the hypotheses of the stated lemma.

**Repair.** The proof of the lemma works unchanged for **nonnegative** \(z\), provided \(V_T\le a z\) is established without dividing by a zero coordinate. Change its codomain to \([0,\infty)\), and have the programs:

- verify \(V_T(\omega,\xi,\varphi)=0\) wherever \(z(\omega,\varphi)=0\);
- take the maximum ratio only over positive coordinates;
- reject nonfinite values and failed inequalities explicitly.

Alternatively restrict the state space to the appropriate support. For the 64 windows above, zero terminal mass follows exactly from zero indegree: no update can put mass there, irrespective of the initial vector. This supplies a local repair without an apparent change to the numerical bounds. A positive left Perron vector on the **whole** state space must not be assumed from Perron–Frobenius theory: the graph has isolated states.

Evidence: [window_check.c](/Users/paronow/aklt-lean/reports/REF-R5/audit/window_check.c), [window_check.txt](/Users/paronow/aklt-lean/reports/REF-R5/audit/window_check.txt).

### 2. Major — The final H3′ numerical certificate cannot be reconstructed from this bundle, and the bundled assemblers do not implement the stated exact assembly

**Location:** `manuscript/sec8-computer-assisted.tex:3`, `:45` (`t:inputs`, H3′ part); `manuscript/app-tail.tex:95` (`p:tail`), `:110` (`tab:tail`), `:119`, `:121`, `:123`. Relevant auxiliary code: `programs/h3-tail/code/assemble_split.py:16`, `:38`, `:43`; `assemble_gen.py:25`, `:50`, `:55`; `assemble.py:14`, `:18`, `:62`, `:73`.

**Exact claim.** The table entries are upper bounds obtained by exact rational summation of upward-printed outputs, giving row quotients at most \(0.987763\) and \(0.968624\). The text also asserts a recomputation using the corrected coefficients \(0.18094,0.36751\).

**Missing evidence.** The supplied `programs/data/tail-out/` contains older symbolic/enumeration data, but no production output of `tailmem4.c` or `tailmem5.c` for the stated memory-10, \(K=28\) computation. In particular, the five split mode-A logs, two mode-B logs, terminal maxima, and remainder-check records underlying the table are absent. The older `k2_*` files are not those logs; their headers use the earlier coefficients \(0.18093,0.36750\). The optional \(0.91825\) computation also lacks its production logs.

The available assemblers do something different from the claimed exact operation:

- `assemble_split.py` and `assemble_gen.py` parse decimals as binary64 `float`, add and divide in ordinary rounding, and print nearest-rounded results.
- They obtain the valid mode-A portion by subtracting upward-printed out-of-range terms from an upward-printed total. An upper bound minus another upper bound need not upper-bound the difference. If the two upward errors are \(\varepsilon_0\) and \(\varepsilon_1\), the subtraction error is \(\varepsilon_0-\varepsilon_1\), with no guaranteed sign. Exact rational subtraction alone would not fix that issue.
- The older `assemble.py` additionally loads `k2_*_22_T_alm.txt` and takes minima with those values. Those files have \(c_s=0.97\) and the old coefficients, so that script is not a checker for the present constants.

I do **not** infer that these legacy scripts were used for the claimed recomputation, or that the table's numbers are false. Rather, the exact assembly described in the paper is not supplied, and the scripts supplied cannot substitute for it. I did not run the seven production jobs; the small checks below do not verify their final row bounds.

**Repair.** Archive the seven complete stdout logs, exact commands, compiler/options, and a small checker using exact decimal rationals and the exact binary64 value of \(h_C\). Sum **per-length** mode-A outputs only for \(22\le n\le106\), rather than subtracting an invalid tail from a rounded total. Sum mode-B outputs for \(108\le n\le260\), then add its upward remainder bound. Verify `check=OK`, finiteness, the repaired zero-support condition in Finding 1, and \(0<\lambda<1\). Record the exact assembled totals before decimal ceilings.

For example, the intended mode-A parameters are `m=10 L=20 K=28 T=109 AT=109 NEX=22`, with classes B:N (multiplicity two), B:W, C:N, C:W, C:S. For mode B, `m=10 L=20 K=28 T=260 AT=53` and an allowed `NEX` suffice if assembly uses the printed per-length values directly.

There is no arithmetic contradiction in the displayed table: its displayed B subtotals sum to \(0.987764\), and its C subtotals to \(1.191410\); the smaller final rows can result from summing before taking individual decimal ceilings, as the caption says. This is precisely why the underlying outputs are needed. The proposed old-coefficient scaling is also algebraically valid: exact rational arithmetic gives

\[
0.987730\,\frac{0.18094}{0.18093}
=0.987784591831094\ldots<0.98779.
\]

Its premise, the certified old row bound, still needs a production record.

### 3. Major — `alm8.c` executes signed-integer overflow before building the certificate

**Location:** `programs/h2-trails/alm8.c:27`, `:59`; `manuscript/sec8-computer-assisted.tex:33` (H2 certificate).

**Exact claim.** The supplied C program is a rigorous implementation of the finite nonnegative transfer calculation.

**Failure.** `pw4` has type `int`, and the initialization computes powers of four through index 23, even for `m=8`. With the actual 32-bit `int`, computing \(4^{16}\) overflows. This is undefined C behavior, independently of the floating-point rounding assumptions. An undefined-behavior-sanitized run of the stated `8 8 9610 9350` instance aborts at line 59 with `1073741824 * 4 cannot be represented in type 'int'`. The fact that only earlier entries are subsequently used does not remove the undefined behavior.

**Repair.** Compute only the powers needed for the validated value of `m`, using a suitably sized unsigned/size type with a checked range, and validate the other fixed-array bounds. For this certificate, initializing through index 8 suffices.

I made that local change in an audit copy, clipped/quantized the heuristic vector to obtain an exact positive binary64 rational vector with \(\max h/\min h\le100\), and reevaluated the quotient upward. It gave

\[
\max_i\frac{(\widehat{\mathsf M}_8h)_i}{h_i}
\le 0.85594871032391507
<0.8559487104<0.98075^8.
\]

Here \(\widehat{\mathsf M}_8\) denotes the upward-computed matrix. The corrected, sanitized run completed. Thus this defect is locally repairable while retaining the stated H2 rate. This is a directed-rounding computation, not a reimplementation of the claimed independent exact-rational certificate.

Evidence: [original sanitizer diagnostic](/Users/paronow/aklt-lean/reports/REF-R5/audit/alm8_ubsan.txt), [audit-copy generator](/Users/paronow/aklt-lean/reports/REF-R5/audit/make_alm_checked.py), [corrected output](/Users/paronow/aklt-lean/reports/REF-R5/audit/alm8_checked.txt).

The asserted independent 938-class exact-rational checker and its test vector were not located in the bundle. The supplied `h1-patterns/code/alm_rig.py` instead constructs the full window matrix and evaluates it with 80-bit Arb ball arithmetic. This does not prevent the corrected directed-rounding calculation from proving H2.

### 4. Minor — `alm8.c` does not print its bound with upward rounding, and its printed root is not a certified operation

**Location:** `programs/h2-trails/alm8.c:108`, `:109`, `:110`; `manuscript/sec8-computer-assisted.tex:33`.

**Exact claim.** The output is described as an upward-rounded upper bound, and the program labels its printed values `rho(M_k)<=` and `rate<=`.

**Failure.** The program switches to `FE_TONEAREST` before printing `best`. An eight-decimal printed value can therefore be smaller than the certified internal value. The supplied run printed `rho(M_k)<=0.85594871`. Also, `exp(log(best)/k)*(1+1e-12)` has no supplied rigorous error bound for the library functions; this inflation is not a proof that the printed root is an upper bound.

**Repair.** Print the quotient upward, preferably also as an exact hexadecimal float, and certify the desired rational rate by comparing the quotient with \((3923/4000)^8\). That comparison is sufficient here:

\[
0.85594872<0.98075^8
=0.855985749174334\ldots.
\]

The paper's more conservative decimal \(0.85594872\) is safe for the reproduced calculation, so this does not undermine the recovered H2 rate. Distinguish the nearest-rounded search for an arbitrary test vector from the directed verification of that fixed vector; not every number in the program needs to be an upper bound.

### 5. Minor — The initial-arrival convention is needed to justify the quoted \(C_V\le153\)

**Location:** `manuscript/sec6-walks.tex:135`, `:138` (`h:H2`, contextual definition); `manuscript/sec8-computer-assisted.tex:16`, `:18` (`l:alm`), `:33`.

**Exact claim.** With the exact \(\mathsf W_n\), \(n<16\), and a vector having \(\max h/\min h=100\), the displayed constant of Lemma `l:alm` is at most 153.

**Ambiguity and check.** A designated arrival direction does not, by itself, make the incoming bond a used bond of the finite trail. The definition should explicitly say whether the first step may reverse that direction. If reversal is allowed, its type also needs specification. Under the natural extension in which it is a nonstraight step, an independent integer histogram followed by exact rational weighting gives

\[
\mathsf W_{10}(0.98075)^{-10}
=2.011436308787\ldots.
\]

The displayed formula, with ratio 100 and its actual rate \(q\le0.98075\), then gives a constant at least \(201.1436308787\ldots\), not at most 153. This does not disprove the existence of some better H2 constant 153; it contradicts this particular calculation under that convention.

If the initial reverse step is forbidden, the analogous maximum over \(8\le n<16\), at rate \(0.98075\), is \(1.505152837665\ldots\), consistent with the intended assertion. In the recursion the arrival neighbor is the removed center, so that restriction is natural.

**Repair.** Explicitly forbid the initial reverse step and state this in the base-sum enumeration. Alternatively, define its weight and use the larger base constant; the exact histogram together with the checked ratio-100 vector gives \(C_V\le202\) at rate \(0.98075\) for the four-initial-direction convention. Only finiteness of \(C_V\) is needed downstream.

Evidence: [independent integer histogram](/Users/paronow/aklt-lean/reports/REF-R5/audit/trail_hist.c), [exact rational evaluation](/Users/paronow/aklt-lean/reports/REF-R5/audit/trail_hist.py), [results](/Users/paronow/aklt-lean/reports/REF-R5/audit/trail_hist.txt).

### 6. Minor — Stale validity claims and an unused unsplit branch differ from the current memory-walk description

**Location:** `programs/h3-tail/code/tailmem4.c:6`, `:20`, `:21`, `:313`; `tailmem5.c:10`, `:24`, `:25`, `:229`, `:230`, `:324`; compare `manuscript/app-tail.tex:46`, `:51`, `:56`, `:114` (`l:memdom`, `p:tail`).

**Exact claims.** The source comments claim mode-A validity through \(2P-3\); the printed mode-A `TAIL` total includes all lengths through `T=109`. The unsplit option of `tailmem5.c` is also described as selecting all first directions.

**Mismatch.** The manuscript correctly restricts mode-A domination to \(n\le2P-5=107\), while the program's summary includes length 108. That summary must not be accepted directly as a trail-tail certificate. The source comments also retain obsolete square-torus formulas involving \(K\) instead of the diagonal quotient's period \(P=2K\).

The obstruction at 108 is real at the level of the proof's stepwise comparison. In row C, the direction word

\[
N^{28}W^{26}SE^{27}S^{26}
\]

is a length-108 trail from \((-1,0)\) to \((0,1)\), avoiding \(c\) and first hitting the target at its end. At passage 54 it is at \((-27,28)\), with arrival W and departure S. The unvisited neighbor \((-28,28)\) is an image of \(c\). Rule R2 drops the pairs containing this neighbor although they are live in the true kernel. Thus the proof's comparison cannot simply be extended to 108. The current table's cut is correct.

Separately, `tailmem5.c` with `D0=-1` kills a window-detected revisit at \([u]\), whereas R1 for \(D_0=*\) retains it with weight \(1/5\). The production mode-B program `tailmem4.c` implements the stated rule correctly. The extra deletion can be justified for genuine trails by the same start-site degree argument, but it computes a different auxiliary walk and should not be called literally the walk defined in the appendix.

**Repair.** Update the comments and output labels to distinguish the computed memory-walk mass from the proved trail bound, and enforce the valid summation cutoff in the checker. Align the unused unsplit `tailmem5` branch with R1, or document its stronger rule separately.

Evidence for the exact trail and window/orbit counts: [geometry_check.py](/Users/paronow/aklt-lean/reports/REF-R5/audit/geometry_check.py), [results](/Users/paronow/aklt-lean/reports/REF-R5/audit/geometry_check.txt).

### Checks that passed and the scope of the numerical evidence

The following checks support the reductions; they do not replace the missing production certificate in Finding 2.

- **Lemma `l:alm`.** The prefix/suffix map is injective. A revisit forgotten by the window has true weight \(1/5\), at most the window's first-visit weight because \(x_s,x_t\ge1\). A detected revisit receives \(1/4\ge1/5\). During a block of eight new steps the C code retains the entire initial window and all earlier new steps, as the definition of \(\mathsf M_8\) requires. It does not mistakenly reset to a sliding eight-step history inside that block. The positive-vector induction and the residue classes \(m\le n<m+k\) give the displayed base-constant formula.
- **Finite state counts.** Exact enumeration reproduced 7,500 length-8 windows and 938 dihedral classes. The tail window construction reproduced 60,092 length-10 windows.
- **True-revisit H2 variant.** The corrected audit copy with revisit weight `0.2` (a binary64 upper bound for \(1/5\)) gave an upward quotient at most \(0.82376383062893244\). An exact rational comparison of the stored quotient with \(0.97606^8\) passed. This supports the final, optional rate assertion at `sec8-computer-assisted.tex:33`; it is not a result of the unmodified `alm8.c`, whose revisit weight is fixed at \(1/4\). See [variant output](/Users/paronow/aklt-lean/reports/REF-R5/audit/alm8_revisit5.txt).
- **Orderings and phases.** The adjacent-exchange criterion has the correct sign. The four phases give exactly one response, with all straight first visits included before a turning response in the exposure ordering, including straights later along the path. Floating score comparisons need not find the exact optimal order: the cost for any permutation, evaluated upward, still upper-bounds the exact minimum. Thus inexact sorting alone is not a gap in the bound.
- **Lemma `l:memdom`.** The lower bounds on distances to nontrivial images are sufficient. A false marked-site or marked-neighbor encounter forces \(n\ge108\); it also occurs no earlier than time 54, after the mode-B rules have stopped. R1's third-visit deletion is justified: the start has degree three after deleting \(c\), and the second site has degree four and is not the target. An additional visit detected in a window beginning at time at least 10 would require too many distinct incident bonds. At a true responding first visit, dropping only image-\(c\) pairs during the safe range cannot remove a live true pair. State sequences determine all continuation directions, so grouping prefixes does not invalidate the final summation over \((w,j)\).
- **Lemma `l:remainder`.** Its induction is correct under its hypotheses, and also after the nonnegative-vector repair. Every predecessor of a fixed target window has the same last direction, hence the same predecessor quotient site. This explains why the bound has no factor \(|\mathsf Q|\).
- **Code paths for the stated modes.** The prefix DFS enforces distinct undirected bonds, avoidance of \(c\), and first arrival at \(v\); its departure counters implement the exact dead pairs. The quotient map, window shift, three kinds, phase response coefficients, first-bond exclusion, record-before-delete order, and rule cutoff `t+1 <= AT` match the definitions. In particular the latter is exactly the text's departure condition \(t<t_*\). The left-vector check has the correct orientation and rounds its two sides in the required directions. The constants are perturbed in the safe directions.
- **Small exact comparisons.** An independent Python implementation using rational arithmetic, dual quotient coordinates, and direct per-response products checked split mode A at \(m=4,L=8,K=9\), for all five production classes (B:N/W and C:N/W/S), through length 12. Every printed C bound was above the corresponding exact rational result. It also checked unsplit mode B through length 18, including the release of the rules, at \((c_s,c_t)=(1,0.99)\); all checked bounds passed. These are finite numerical checks, not verification of memory-10 terminal masses. The latter auxiliary run also passed its remainder inequality check.

For reference, at the paper's constants the isolated window/vector check found

\[
\lambda_A\approx0.97953278636589092,\qquad
\lambda_{\rm check}\approx0.97953278832495638,
\]

and zero failures in the upward-left/downward-right check. This is compatible with the paper's conservative \(0.97953279\). It does not compute \(a=\max V_{260}/z\).

Small-check artifacts: [independent checker](/Users/paronow/aklt-lean/reports/REF-R5/audit/small_memory_check.py), [B split results](/Users/paronow/aklt-lean/reports/REF-R5/audit/small_memory_check.txt), [C split results](/Users/paronow/aklt-lean/reports/REF-R5/audit/small_memory_check_C_N.txt), [mode-B results](/Users/paronow/aklt-lean/reports/REF-R5/audit/small_memory_check_modeB.txt).

## 2. Statement table

The labels are authoritative; the theorem numbers follow the supplied source. H1's subsection is excluded from this lane.

| Label / location | One-line content | Verdict | Dependencies |
|---|---|---|---|
| `t:inputs`, Theorem 8.1, `sec8-computer-assisted.tex:5` | H1, H2 with \(q\le0.98075\), and H3′ with \(\rho(M_1)\le0.98779\) | **Unproved as supplied for H3′**; H2 correct after code fixes; H1 outside R5 | `t:H1` (outside lane), `l:alm`, finite H2 certificate, `l:CW`, `l:memdom`, `l:remainder`, `p:tail` |
| `l:alm`, Lemma 8.2, `sec8-computer-assisted.tex:15` | Window transfer domination implies an exponential weighted-trail bound with an explicit base constant | **Correct**, with the inherited range \(0<c_s,c_t\le1\) and a precise initial-step convention | Definition of \(\mathsf W\), finite windows, nonnegative matrix multiplication, positive test vector; no external enumeration theorem |
| `e:mT`, (C.1), `app-tail.tex:8` | Scalar trail masses sum to \((M_1h)_X\) | **Correct** | `e:kernel`, the definition of \(\kappa_h\), nonnegative summation; finiteness follows from H2 or a successful tail certificate |
| `l:CW`, Lemma C.1, `app-tail.tex:13` | \(\rho(M)\le\max_X(Mh)_X/h_X\) | **Correct** | Finite nonnegative matrix, strictly positive \(h\); weighted-norm argument or Gelfand formula |
| `e:phaseweights`, (C.2), `app-tail.tex:24` | Four-phase product representation of straights-first exposure | **Correct** | `e:mT`, path kinds, \(3^{-n}(3/5)^{\mathrm{rev}}\), one response |
| `l:memdom`, Lemma C.2, `app-tail.tex:53` | Mode A dominates through 107; mode B dominates every length above 53 | **Correct** | Memory-walk definition I–III, \(m=10,L=20,P=56\), positive coefficients, \(x_s,x_t\ge1\), first-hit trails, lattice distance bounds, degree bounds |
| `l:remainder`, Lemma C.3, `app-tail.tex:75` | A uniform terminal bound and a left sub-invariant vector give the geometric remainder | **Correct**; application requires Finding 1's repair | No rules after \(T\), unique predecessor displacement, \(V_T\le az\), \(z\mathbb W\le\lambda z\), \(a\ge0\), \(0<\lambda<1\) |
| `p:tail`, Proposition C.4, `app-tail.tex:94` | Table entries and row bounds imply \(\rho(M_1)\le0.98777\) | **Unproved as supplied** | Previous three lemmas, exact short enumeration, five valid mode-A sums, two mode-B sums/remainders, rigorous assembly; Findings 1–2 |
| `tab:tail`, Table 2, `app-tail.tex:98` | Certified short/intermediate/long contributions | **Unproved as supplied** | Production outputs and exact assembly described at `:119–123`; see Finding 2 |
| `r:tailtypedep`, Remark C.5, `app-tail.tex:127` | Type-dependent coefficients give \(\rho(M_1)\le0.91825\) | **Unproved as supplied**, optional and not used in the main line | Six coefficient bounds of `r:typedep`, their stated interval checks, `tailmem6.c`, analogous production outputs, remainder repair, \(h_C=1.20\) |

## 3. Formalization notes

1. **Fix the trail and arrival conventions.** A trail is a finite vertex sequence with unit increments and injective **unordered** bonds; vertices may repeat. Passage \(i\) means departure from \(v_i\), and a revisit means an earlier departure from that same vertex. For internal vertices, earlier arrival and earlier departure agree for this purpose. The designated incoming bond at the start must either be forbidden explicitly or assigned a rule for reversal. It is not automatically part of a finite trail. Include \(\mathsf W_0=1\).

2. **Windows are direction strings, not dihedral classes.** The main transfer matrix uses all orientations and identifies only translations. A separate equivariance lemma is needed before using a 938-class quotient. For H2 a block extension remembers \(m\) old steps **plus every new step of that block**; it is not the \(k\)-th power of the one-step, sliding-memory transfer matrix.

3. **State the parameter ranges where domination is proved.** The proofs use \(x_s,x_t\ge1\), following from \(0<c_s,c_t\le1\); in particular \(1/5\le1/3\le x/3\). The positive test vector, finite index set, and hence positive minimum are essential in `l:alm`. Its \(\lambda\) is positive because there are extendible straight windows; choose an upper rational rate by proving \(\mathsf M_kh\le q^kh\), rather than formalizing an approximate root.

4. **Keep matrix orientations explicit.** \(\mathsf A_n\) and \(z\) are row vectors; the H2 test vector \(h\) is a column vector. The H2 argument is a row-vector domination followed by multiplication by a positive column. The remainder uses a left sub-invariant vector, not the H2 right-vector inequality.

5. **Define the kernel before applying finite-matrix spectral statements.** Its entries begin as countable nonnegative sums. Show they are finite before invoking `l:CW`. H2 already gives this: each entry is bounded by a constant times \(\sum_n nC_Vq^n\). Alternatively the successful tail certificate itself establishes finiteness. Interchanges of the sums over shifts, passages, trails, and lengths are justified by nonnegative summation.

6. **Make the short ordering a definite function.** For positive \(x_i\kappa_i\), the exchange inequality is equivalent to increasing \((x_i-1)/(x_i\kappa_i)\). At the stated parameters \(x_i>1\). Specify a deterministic tie rule and put zero-response passages at the end. All pair-death information is evaluated in the trail's original time order, even when exposure terms are permuted. A checker can avoid formalizing floating score comparisons: whichever permutation the code returns has cost at least the exact minimum, and its upward evaluation bounds that cost.

7. **Separate the phase from the lattice position.** Start in A or B; a response switches A to C at a turn, or B to D at a straight. Count only C and D at the target. The phase is recorded *after* the indexed number of passages. This makes prefix responses before time 20 part of the initial C/D mass, while a response at passage 20 is a later transition. No response is attached to the endpoint \(v_n\).

8. **Formalize the quotient and its exact distances.** The subgroup has determinant 1,568 and
   \[
   |(28(a+b),28(a-b))|_1=56\max(|a|,|b|).
   \]
   Prove the image-distance bounds for \(c,v,u,u+D_0\) and neighbors of images of \(c\), not just a generic injectivity-radius statement. The relevant two-ended threshold is 108, while the earliest false rule event is at time 54. In code, rules on departure use `t+1 <= AT`, equivalent to \(t<t_*\); deletion uses arrival time at most \(t_*\).

9. **The marked-site degree arguments are separate nodes.** For a split trail, the known first bond is already used. At \(u\), the deleted center leaves degree three; at \(u+D_0\), degree is four and parity ensures it is not \(v\). Once a recent window visit is added to the known time-0/time-1 visit, a further departure would require too many distinct incident edges. This justifies the special R1 deletion, rather than a generic assertion that trail vertices are visited at most twice in every possible endpoint convention.

10. **Prove the summation injection in `l:memdom`.** Fixing a state sequence after time 20 fixes all subsequent directions because each target window contains the appended last direction. A response after time 20 is recoverable from its switch time. Responses before 20 are already summed in the initial C/D entry. Only the prefix and its earlier response can be lost by grouping, exactly the terms present in \(V_{20}\).

11. **Use a support-aware remainder lemma.** Strict positivity on all windows is not supplied. The natural statement is \(z\ge0\), \(V_T\le az\), \(z\mathbb W\le\lambda z\). Its proof needs no division by \(z\). Every predecessor of \((\omega',\xi',\varphi')\) has site \(\xi'-d'_m\), giving the uniform-in-site induction. This is a pointwise/L-infinity argument, not a total-mass estimate; introducing a quotient-size factor would unnecessarily destroy its strength.

12. **The diagonal-block spectral claim does not require irreducibility.** In phase order, the matrix is block triangular, with B and C having identical diagonal blocks and all diagonal blocks entrywise dominated by A. Thus the full spectral radius equals that of A. Existence of a strictly positive Perron eigenvector on the full window set, however, does not follow and is false for these blocks. Use the directly checked sub-invariance inequality on the appropriate support.

13. **Give floating-point computation a precise trust boundary.** The exact mathematical walk and its stored upper approximation are different objects. An upper terminal array bounds the exact \(V_T\); the remainder then evolves with the exact mathematical matrix. It is unnecessary to prove that the future rounded implementation itself contracts at \(\lambda\). Treat the stored finite floats used for \(h,z,\lambda\) as exact dyadic rationals. In particular
   \[
   h_C=\frac{2769713770832855}{2251799813685248},
   \]
   not exactly \(123/100\). The check proves its inequality by upward evaluation of the left side and downward evaluation of \(\lambda z\). The denominator \(1-\lambda\) must be a positive lower bound. Reject failed checks and nonfinite values; a zero process exit code alone does not certify success.

14. **Heuristic arithmetic is not certificate arithmetic.** Sorting subtracts `xx-1`, comparators subtract scores, and the Perron/fixed-point searches subtract iterates and use nearest rounding. This contradicts a literal reading of “no subtraction occurs” / “before any computation” at `app-tail.tex:121`, but is harmless when these stages merely choose an arbitrary candidate or ordering. State the upward invariant only for bound-producing evaluations and the final directed checks.

15. **Complete the finite computation separately from decimal presentation.** Binary32 storage and binary64 enumeration can provide upper bounds under directed rounding and gradual underflow. Proving combinatorial enumeration exact is a separate task from proving those evaluations outward. The table checker must use exact printed decimals, the exact chosen \(h_C\), certified remainders, and only valid length ranges. Reflection \((x,y)\mapsto(x,-y)\) fixes the B endpoints and the subgroup and interchanges N/S classes, giving the multiplicity two; it does not fix the C target, so three C classes are needed.

## 4. External inputs

No outside mathematical paper is directly cited as a necessary theorem in the assigned part of Section 8 or Appendix C. “Alm-type” and “Collatz–Wielandt” name methods, but the required inequalities are proved in the manuscript. The following internal inputs and standard facts nevertheless need explicit treatment in a formal proof.

| Input, stated as used | Locator supplied by the paper | Hypothesis check / assessment |
|---|---|---|
| **H1, external to R5:** for every pattern in \(\mathcal P_{\rm ext}\) and every assignment of its 20 unit slot vectors, \(Z_{\rm cur}\ge(961/1000)Z_{\rm next}\) for a straight pattern and \(Z_{\rm cur}\ge(187/200)Z_{\rm next}\) for a turn. The fixed-template sharpness example has ratio \(416114/444675\). | `t:H1`, `sec8-computer-assisted.tex:51`; `r:H1sharp` at `:76`, referring to `e:5469`, `app-local.tex:275` | H1's proof is excluded from this lane. The references specify the same template, slots, and constants. The H2/H3′ trail computations use only the numerical pair, so they do not additionally assume the local polynomial inequalities while certifying their scalar bounds. |
| **Weighted trail definition:** each repeated departure has weight \(1/5\); first departures have \(1/(3c_s)\) or \(1/(3c_t)\), with fixed start and incoming direction. | `sec6-walks.tex:135`, `h:H2` at `:137` | Correct parameter range inherited from H1. Initial reversal needs the choice in Finding 5. No self-avoiding-vertex assumption may be substituted for bond injectivity. |
| **Kernel definition:** trails in \(\mathbb Z^2\setminus\{c\}\) from \(u\) to \(v\), stopped at the first hit of \(v\); three neighbor pairs per first visit; coefficients \(\bar\alpha\) and \(\bar\beta\); pairs containing \(c\) or a vertex departed twice earlier are dead. | `sec7-recursion.tex:37`, `e:kernel` at `:40` | The assigned reductions and exact DFS use these definitions correctly. Shifts disappear only because \(\theta=1\), not because the shifted kernel is being computed. |
| **Response bounds:** at a first-visit passage away from \(S\), the logarithmic ratio response is \(\alpha r_{fg}+\beta(r_{fo}+r_{go})\), with \(0<\alpha\le0.18094\), \(0<\beta\le0.36751\); with two remaining neighbors the surviving coefficient is at most \(\bar\beta\). | `l:response`, `sec6-walks.tex:64` | These are internal inputs, derived elsewhere under the no-leg, at-most-three-factor and conditional-independence conditions. R5 uses only their stated numerical upper bounds. Their full derivation is outside this lane. |
| **Exposure may be ordered arbitrarily:** the response bound contains prefix products for any permutation of the first visits, with \(x_i\ge1\). | `l:exposure`, `sec6-walks.tex:84` | Applies to both proposed orderings. A per-trail ordering depending on fixed \(h\) and the constants is allowed. It must be fixed independently of \(\theta\), as required at `l:Mtheta`, `sec7-recursion.tex:54`. |
| **Collatz–Wielandt upper inequality:** for finite nonnegative \(M\) and strictly positive \(h\), \(\rho(M)\le\max_i(Mh)_i/h_i\). | `l:CW`, `app-tail.tex:13`, proof at `:17`; used in `sec8-computer-assisted.tex:37` | Within hypotheses once finiteness is established. Irreducibility is unnecessary. A direct proof uses the norm \(\|v\|_h=\max_i|v_i|/h_i\), so no Perron-vector existence theorem is needed. |
| **Gelfand formula:** for a finite complex matrix and a submultiplicative matrix norm, \(\rho(M)=\lim_{k\to\infty}\|M^k\|^{1/k}\). | Invoked without bibliographic locator at `app-tail.tex:18` | Valid. Passing from entry bounds to a matrix norm can introduce a fixed dimension factor, whose \(k\)-th root tends to one. The weighted-norm proof avoids this implicit step. Handle \(\mu=0\) by \(M=0\). |
| **Finite-matrix spectral facts:** a block-triangular matrix has the union of the diagonal-block spectra; if \(0\le A\le B\), then \(\rho(A)\le\rho(B)\). A nonnegative matrix has a nonnegative Perron eigenvector, but strict positivity requires additional assumptions such as irreducibility. | Used without a separate locator at `app-tail.tex:90` | The block/spectral comparison is valid since \(x_s,x_t\ge1\). Strictly positive Perron eigenvectors on the complete window set are unavailable; Finding 1 applies. Approximate vector construction is acceptable only because the inequality is checked directly. |
| **Nonnegative summation and geometric series:** countable nonnegative sums may be rearranged; for \(0<\lambda<1\), \(\sum_{j\ge1}\lambda^j=\lambda/(1-\lambda)\). | `e:mT`, `l:remainder`, `app-tail.tex:87` | Valid. The program does not enforce \(\lambda<1\), as `:121` acknowledges; acceptance must check it. |
| **Directed IEEE arithmetic and conversions:** each bound-producing addition, multiplication, division and binary32 conversion rounds upward; lower-side products and \(1-\lambda\) round downward; positive underflow rounds to a positive subnormal. Correct decimal output honors the active rounding mode. | `app-tail.tex:121`, `:125`; `alm8.c:5–9`; compilation with `-frounding-math` | This is an explicit computational trust assumption, not an external mathematical theorem supplied with a locator. It also requires gradual underflow, no unsafe compiler reassociation, correct rounding-mode control, and defined integer/index operations. H2 violates the last condition before Finding 3's repair and changes to nearest rounding before output. Tail certificate blocks otherwise use the intended directions. |
| **Optional type-dependent bounds:** straight \((\alpha,\beta,\beta')\le(0.145217,0.352782,0.340008)\); turn \((\alpha,\beta,\beta')\le(0.149953,0.357549,0.344661)\), with the extra H1-derived lower bound on the local denominator. | `r:typedep`, `sec7-recursion.tex:97`; invoked by `r:tailtypedep`, `app-tail.tex:127` | Conditional on those coefficient certificates, `tailmem6.c` makes the expected substitutions, including the surviving-pair coefficient. The assigned text gives no production record for the final \(0.91825\) bound. It is optional and cannot repair the main certificate's missing records. |

The independent checks asserted at `app-tail.tex:123` are useful diagnostics, but the manuscript itself correctly says they are not rigorous substitutes for the domination proof, directed arithmetic, and final certificate. I used them as claims to compare with the supplied artifacts, not as additional verified inputs.
