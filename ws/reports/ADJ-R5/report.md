STATUS: COMPLETE

All six findings are adjudicated below. Finding 2 is **CONFIRMED-MODIFIED**: the frozen program bundle lacks the production records, but the full project archive contains them and an exact assembler. My own rational assembly reproduces **every numerical entry of Table C.1 and both bounds of Proposition C.4**. The other five findings are confirmed. The repairs preserve the main theorem, `(cs,ct)=(0.961,0.935)`, `q≤0.98075`, `ρ(M₁)≤0.98779`, and `C_V≤153`.

All commands below run in `/home/ubuntu/aklt/reports/ADJ-R5`. Inputs were read only; all generated files are under this directory. No subagents or production tail jobs were launched. The largest new computations were the memory-10 **window/vector calculation without quotient-site arrays**, and the memory-8 H2 calculation. Computations used at most two concurrent single-core processes and stayed well below 16 GB. Environment: x86_64, GCC 13.3.0, Python 3.12.3. [Input hashes](audit/input-sha256.txt), [audit programs](audit/), and copies of the relevant [archived records](audit/archive/) accompany this report. Decimal approximations in explanatory prose are distinguished from exact rational comparisons in the checkers.

Manuscript line ranges below refer to the frozen files in `/home/ubuntu/aklt/manuscript/bundle/manuscript/`. Proposed source changes are not changes to that frozen input. The substantive conclusions about numerical certificates retain the manuscript's explicit trust in the implementation and directed IEEE arithmetic; exact assembly of output strings is not an independent rerun of the production computation.

## FINDING 1: CONFIRMED

The application of Lemma C.3 (`l:remainder`) violates its written strict-positivity hypothesis. The correct repair is to allow a nonnegative vector and check its zero support. Neither a positive Perron vector on the full state space nor a change to the tail constants is needed.

**Independent mathematical check.** For the direction word `E E N W W S W S E N`, the vertices are

```text
(0,0),(1,0),(2,0),(2,1),(1,1),(0,1),(0,0),
(-1,0),(-1,-1),(0,-1),(0,0).
```

Its ten unordered bonds are distinct. All four bonds incident to its starting site occur. Thus it cannot be preceded by a step in an 11-step trail, and its window has indegree zero. It also ends at that site with all four bonds used, so it has outdegree zero. In particular its column in every block of `W` is zero. Multiplication of any row vector by any of these blocks gives zero there.

I enumerated the window graph independently with integer coordinates and unordered bonds in [geometry_windows.py](audit/geometry_windows.py). I separately used the bundled program's small window, power-iteration and post-response routines in [window_vector.c](audit/window_vector.c), without allocating any production walk arrays. The resulting dyadic vector was then checked against the **exact mathematical** matrix using `Fraction`, exact `cs=961/1000`, `ct=187/200`, `α=9047/50000`, `β=36751/100000`, and the exact binary64 `h_C`. This check does not rely on the original `worst` division.

```sh
gcc -O2 -frounding-math -ffp-contract=off \
  -o audit/window_vector audit/window_vector.c -lm
./audit/window_vector > audit/window_vector.txt
python3 audit/geometry_windows.py > audit/geometry_windows.txt
```

Selected actual outputs:

```text
windows=60092 zero_indegree=64 zero_outdegree=64
lamA=0.97953278636589092 lamB=0.94059961636208644
lcheck=0.97953278832495638 lcheck_hex=0x1.f58552566e461p-1
phase=A zero=64 nonfinite_or_negative=0 zero_with_incoming=0
phase=B zero=64 nonfinite_or_negative=0 zero_with_incoming=0
phase=C zero=64 nonfinite_or_negative=0 zero_with_incoming=0
phase=D zero=64 nonfinite_or_negative=0 zero_with_incoming=0

independent windows=60092 zero_indegree=64 zero_outdegree=64
edges=169092 zero_in_and_out=64
exact rational zW <= lambda z failures=0 zero coordinates with incoming=0
zero counts=[64,64,64,64]
lambda=8822847000994913/9007199254740992
lambda < .97953279: True
```

Spacing in the second group is normalized here; the complete outputs are in [window_vector.txt](audit/window_vector.txt) and [geometry_windows.txt](audit/geometry_windows.txt). The vector itself is archived as exact hexadecimal floats in [window_vector.tsv](audit/window_vector.tsv).

**Why terminal mass is zero, without a production rerun.** Any update after time 20 writes only to target windows of graph edges. A window of indegree zero is never a target. Thus `V_t(ω,ξ,φ)=0` at these windows for every `t≥21`, for every site and phase, even if the initial array were arbitrary. The actual length-20 trail prefixes also have zero there, since their last 11 steps would otherwise give an incoming edge. In the C implementation the next arrays are zeroed before each update, so this reasoning also establishes exact stored zeros. All zeros of the regenerated `z` are precisely these windows.

At `tailmem4.c:336,340` and `tailmem5.c:347,351`, the written loops divide zero by zero. IEEE NaNs are ignored by `>` comparisons. The sub-invariance comparison `l[p][w] > lcheck*z[p][w]` itself remains meaningful at these coordinates (both sides are zero); the ratios and terminal-maximum loop lack the required support checks.

**Remainder proof, re-derived.** The predecessor site of `(ω′,ξ′,φ′)` is always `ξ′−d′_m`. From `V_t≤a λ^(t−T)z` and nonnegativity,

`V_(t+1)≤a λ^(t−T)(zW)≤a λ^(t+1−T)z`.

There is no division by `z`, and no factor equal to the number of quotient sites. The geometric-series proof works for `z≥0` exactly as written. To establish its initial hypothesis, bound ratios only where `z>0` and verify `V_T=0` on its zero set.

**Minimal LaTeX correction.** Target: `app-tail.tex:76` (replace this statement paragraph; keep `l:remainder` and the displayed conclusion at lines 77–79).

```latex
Let $V_t$ be a memory walk with $t_* < T$, and let $\mathbb W$ be its weight matrix on $\Omega \times \{\mathrm A, \mathrm B, \mathrm C, \mathrm D\}$ without rules, $\mathbb W((\omega, \varphi), (\omega \cdot d, \varphi'))$ the weight of the step $d$ from phase $\varphi$ to phase $\varphi'$ in (II). Suppose that $z \colon \Omega \times \{\mathrm A, \mathrm B, \mathrm C, \mathrm D\} \to [0, \infty)$, $\lambda \in (0, 1)$ and $a \ge 0$ satisfy $z \mathbb W \le \lambda z$ and $V_T(\omega, \xi, \varphi) \le a \, z(\omega, \varphi)$ for all $\omega, \xi, \varphi$. Then
```

The induction at `app-tail.tex:83–87` needs **no change**: it already proves this stronger statement. Target: `app-tail.tex:90`, replace the second sentence and append the support explanation, leaving the block-triangular spectral statement unchanged.

```latex
A nonnegative candidate $z$ is obtained by power iteration in the diagonal blocks and approximate solution of
$z_{\mathrm C}(\lambda-\mathbb W_{\mathrm{CC}})=z_{\mathrm A}\mathbb W_{\mathrm{AC}}$ and
$z_{\mathrm D}(\lambda-\mathbb W_{\mathrm{DD}})=z_{\mathrm B}\mathbb W_{\mathrm{BD}}$;
only the inequality $z\mathbb W\le\lambda z$ is used, and it is checked directly.
The constructed vector is zero in each phase at exactly the $64$ windows of indegree zero, and positive at every other window.
No update can put mass at a window of indegree zero, so $V_T$ vanishes there for $T\ge21$.
In applying Lemma~\ref{l:remainder}, we check this zero-support condition and take ratios only where $z>0$.
```

Target: `app-tail.tex:114`, replace the sentence beginning “For `$n>260$`” and keep the final sentence about §`s:tailtrust`.

```latex
For $n>260$ we use Lemma~\ref{l:remainder} with $T=260$ for the walk of mode B, taking $\lambda$ to be the stored binary64 value \texttt{lcheck} used in both the sub-invariance check and the remainder calculation, with $0<\lambda\le0.979532789<0.97953279$.
The nonnegative vector $z$ satisfies the directly checked inequality $z\mathbb W\le\lambda z$.
We verify $V_{260}(\omega,\xi,\varphi)=0$ whenever $z(\omega,\varphi)=0$, and choose $a$ as an upward-rounded upper bound for
$\max_{z(\omega,\varphi)>0}V_{260}(\omega,\xi,\varphi)/z(\omega,\varphi)$.
```

Using the actual checked `lcheck`, rather than substituting the larger display value `0.97953279` into an already computed remainder, is necessary for a literal account of the archived calculation.

The arithmetic/acceptance paragraph at `app-tail.tex:121` must change as specified under Finding 2. It must require finiteness, nonnegativity, `0<λ<1`, sub-invariance, and the zero-support condition. Reviewable source repairs are generated by [repair_tail_sources.py](audit/repair_tail_sources.py) into `audit/tailmem{4,5,6}_checked.c`: zero denominators are handled explicitly and failed/nonfinite checks reject the certificate. A reduced mode-B run of the guarded `tailmem4` produced byte-identical stdout to the original on that instance (commands under Finding 6).

**Consequences elsewhere.** Proposition C.4, Table C.1, Theorem 8.1, the abstract, and the constants appendix keep their numerical statements. The optional Remark C.5 must use the same support-aware remainder check. A merely positive Perron-vector assertion cannot replace this repair.

## FINDING 2: CONFIRMED-MODIFIED

The frozen bundle is incomplete, and the referee correctly identifies defects in its legacy assemblers. The stronger conclusion that the final numerical certificate cannot be reconstructed from the available project evidence is false once the full tree supplied for this adjudication is inspected. Production outputs, exact commands, source hashes, and a valid exact-summation assembler exist. My independent assembly reproduces all of Table C.1, with the support repair in Finding 1 supplying the missing mathematical hypothesis. I also found two small inaccuracies in the old-run comparison prose.

**What exists.** The following paths are relative to `/home/ubuntu/aklt/source-full/agents/`:

| Purpose | Archived records |
|---|---|
| Corrected uniform coefficients, five split mode-A runs | `75-audit-tail/out/rerun/r961A_B_1.txt`, `r961A_B_2.txt`, `r961A_C_1.txt`, `r961A_C_2.txt`, `r961A_C_3.txt` |
| Corrected uniform coefficients, two mode-B runs | `75-audit-tail/out/rerun/r961B_B.txt`, `r961B_C.txt` |
| Exact decimal-rational assembler | `75-audit-tail/code/assemble75.py` |
| Production invocation records | `75-audit-tail/code/run_all.sh`, `run_rest1.sh`, `run_rest2.sh` |
| Build flags and hashes linking the rerun to source | `75-audit-tail/NOTES.md:303–307`, `LOG.md`, final entry |
| Old uniform-coefficient logs | `62-kernel-tail/out/s961A_{B_1,B_2,C_1,C_2,C_3}.txt`, `s961B_{B,C}.txt` |
| Optional type-dependent logs | `62-kernel-tail/out/c961_935_A_{B_1,B_2,C_1,C_2,C_3}.txt`, `c961_935_B_{B,C}.txt` |

The seven corrected logs have `m=10,L=20,K=28`; mode A has `T=AT=109,NEX=22`, and mode B has `T=260,AT=53,NEX=109`. They include every nonzero per-length output, plus remainder diagnostics for both mode-B runs. All `D/F` lengths are exactly the expected even lengths. The mode-B records say `check=OK` and `lcheck=0.979532789<1`. They print `alpha=1.373004e-10` / `1.270492e-10`, `|zC+zD|=9.433735e+05`, and remainders `6.198914e-03` / `5.736087e-03`.

The command records use the corrected coefficients **entered directly** as `0.18094,0.36751`. Their six-decimal header values are `a=0.180941,b=0.367511`: this is consistent with one-ulp enlargement followed by upward decimal formatting, and does not mean the command used `0.180941,0.367511`. The headers alone are insufficient to recover the input constants; the archived commands resolve that issue.

The bundled and full-tree source files are byte-identical. Command and actual SHA-256 output:

```sh
sha256sum /home/ubuntu/aklt/manuscript/bundle/programs/h3-tail/code/tailmem{4,5,6}.c \
  /home/ubuntu/aklt/source-full/agents/62-kernel-tail/code/tailmem{4,5,6}.c
```

```text
tailmem4.c: 9a8410802158c2f905177afd045547485cd2c35ec9477a2b469961ad75607360
tailmem5.c: 070f1bf697ccd9dd51ee0ba55ff549f6f10201411553caf6c28637144c386118
tailmem6.c: b258088ead0bdad4dd46cab41a4c52c3abe7ee0beb77a77e5ab8f4d5ee9de01c
```

Each hash occurs twice, once for each tree. The first two hashes also match the archived rerun log. These records settle provenance; their authors' mathematical conclusions were not used as premises of this adjudication.

**Exact assembly I ran.** My checker [assemble_exact.py](audit/assemble_exact.py) parses decimal strings directly as `Fraction`, validates run parameters, duplicate/missing lengths, mode tags, completion records and remainder status, and sums these disjoint pieces:

1. All `E n` values with `n≤20` from mode A, with class multiplicities `B:N×2,W×1`, `C:N,W,S×1`.
2. The same class sum of `D 22`.
3. The same class sum of the per-length values at even `24≤n≤106`.
4. Mode-B per-length values at even `108≤n≤260`.
5. The mode-B **printed upward remainder**, used as its own upper bound.

It does not subtract any rounded quantities and does not use the printed `TAIL` totals. In particular, `D 108` from mode A is discarded, and `F 108` from mode B is included even though that run's `NEX=109` summary omits it. Division for row C uses

`h_C = 2769713770832855/2251799813685248`,

the exact binary64 value chosen by the programs. The optional variant uses the exact binary64 value `5404319552844595/4503599627370496` of `1.20`.

```sh
python3 audit/assemble_exact.py > audit/assembly_exact.txt
```

The following are **exact decimal rationals**, not nearest-rounded presentations of longer sums:

| Component | Exact assembled B bound | Exact assembled C bound | Printed ceilings in Table C.1 |
|---|---:|---:|---|
| `n≤20` | 0.594579954688466 | 0.841680362081012 | 0.594580 / 0.841681 |
| `n=22` | 0.0266686902787 | 0.0226434200175 | 0.026669 / 0.022644 |
| `24≤n≤106` | 0.30293122758854 | 0.26802813590277 | 0.302932 / 0.268029 |
| `108≤n≤260` | 0.057383656614819 | 0.053318779441818 | 0.057384 / 0.053319 |
| `n>260` remainder output | 0.006198914 | 0.005736087 | 0.006199 / 0.005737 |
| Total numerator | **0.987762443170525** | **1.1914067844431** | **0.987763 / 1.191407** |

Exact quotient outputs/comparisons:

```text
B quotient exact = 39510497726821/40000000000000
               = 0.987762443170525
C quotient exact = 3274914032266007086628864/3380998255411199951171875
               = 0.96862340198626017659041304814172...
B Table C.1 entry comparisons: [True, True, True, True, True, True, True]
C Table C.1 entry comparisons: [True, True, True, True, True, True, True]
```

Every table entry is exactly the six-decimal ceiling of the corresponding assembled rational, including the last two rows. Thus all numerical assertions in `p:tail:95`, all fourteen numerical entries at `app-tail.tex:102–108`, and the implications `ρ(M₁)≤0.98777≤0.98779` are recovered from the archived outputs. Summing the rounded displayed subtotals instead would give `0.987764` and `1.191410`; that is not the specified assembly and creates no contradiction.

The archived `assemble75.py` already performs the essential valid rational assembly; it sums per-length mode-A values rather than subtracting an invalid tail. It uses `Fraction(float(hCs))` appropriately to obtain the chosen dyadic denominator. Its intermediate decimal presentation uses `float`, but its final six-decimal ceiling is taken from the exact rational. It is distinct from the three legacy bundled assemblers criticized by the referee. My checker supplies stricter header/length checks and prints the actual rational sums. The old `assemble_split.py`, `assemble_gen.py`, and `assemble.py` are unsuitable as proof checkers for the present table for the reasons the referee gives: ordinary floating sums, subtraction of upper bounds, and, in the last case, minima involving data for different constants. These defects cannot be repaired merely by changing subtraction to rational arithmetic.

**Old run: two necessary prose corrections.** Exact assembly of the seven old uniform logs gives

```text
B = 0.987730102795067       ceiling to 6 decimals = 0.987731
C/hC = 0.96859152491234147740296081189558...   ceiling = 0.968592
```

Consequently the printed old B value `0.987730` is a nearest-rounded summary, not the certified upper bound claimed in the last sentence of `app-tail.tex:123`. The referee's hypothetical scaling calculation is algebraically correct, but its premise with that decimal is not supplied by the actual exact assembly. The repaired scaling is still sufficient:

```text
(987731/1000000)*(18094/18093)
 = 8936002357/9046500000
 = 0.98778559188636489249986182501520... < 0.98779 : True
```

The minimum and maximum new/old ratios over all printed per-length `E/D/F` values are

```text
minimum = 1.0000322098949719070838089555003...
maximum = 1.0000332031789831954210951519899...
```

The maximum occurs at mode A, row C, class N, `E 2`, with printed operands `0.2562867139467 / 0.2562782046956`. It slightly exceeds `1.0000332`. The outward interval `[1.0000322,1.0000333]` contains every ratio. These comparisons are exact fractions in the checker. The scaling proof itself only needs the larger of `α_new/α_old` and `β_new/β_old`, which is `18094/18093`; it does not need the empirical per-length interval.

**Optional Remark C.5.** Exact assembly of the seven archived `c961_935_*` logs, conditional on the type-dependent coefficient bounds already stated elsewhere in the manuscript, gives

```text
B numerator = 0.913009554182608 <= 0.91301
C numerator = 1.101894699682346
C/hC = 0.91824558306862170064857961943785... <= 0.91825
```

The optional numerical bound is therefore also reconstructed from archived outputs. Its original unsplit implementation has the stronger start rule discussed under Finding 6; the degree argument justifies that rule for genuine trails. The support repair of Finding 1 applies to its remainder too. I did not rederive or rerun the coefficient interval certificates; they are inputs outside these six findings.

**What this does and does not reproduce.** The exact operation requested in the question reproduces the short, intermediate, long and remainder **archived upper bounds**, their totals, their quotients, the corrected-coefficient recomputation, and the optional type-dependent aggregate. It does not rerun the length-20 production DFS or the memory-10/site-1568 evolution, reconstruct the entire `V_260` arrays, independently recompute the production maxima `a`, or recover an unrounded remainder from the separately rounded diagnostic `alpha` and `zsum` strings. Those arrays and exact terminal-maximizer records are not archived in the identified datasets. The printed remainder is the bound-producing output used in assembly. My separate small vector calculation verifies the support and sub-invariance issue; it does not replace the terminal evolution. Accordingly this is recovery of the stated certificate under its declared computational trust boundary, not a wholly rational reconstruction of every production operation. The strict-positivity application as frozen remains wrong until Finding 1 is repaired.

**Minimal LaTeX correction.** No numerical change is needed in `app-tail.tex:95,102–110`, `sec8-computer-assisted.tex:6,45`, or `app-constants.tex:21`. The missing records and exact checker should accompany the program bundle; copies are provided in this report's `audit/archive/`. Target: `sec8-computer-assisted.tex:3`, replace only the final sentence.

```latex
The programs and output files are kept with the project; the production records and exact rational assembly for (H3$'$) are identified in \S\ref{s:tailtrust} and are to be included with the accompanying programs.
```

Target: `app-tail.tex:119`, replace “The table is assembled by summing the printed per-`$n$` values” with the following text. Other sentences of that paragraph remain, subject to Finding 6's explicit implementation note.

```latex
The table is assembled from the five files
\texttt{r961A\_B\_1.txt}, \texttt{r961A\_B\_2.txt},
\texttt{r961A\_C\_1.txt}, \texttt{r961A\_C\_2.txt},
\texttt{r961A\_C\_3.txt} and the two files
\texttt{r961B\_B.txt}, \texttt{r961B\_C.txt}, archived in
\texttt{agents/75-audit-tail/out/rerun/} in the full project.
The commands are recorded in \texttt{agents/75-audit-tail/code/run\_all.sh}
and \texttt{run\_rest1.sh}, \texttt{run\_rest2.sh}; the rerun used
\texttt{gcc -O2 -frounding-math -ffp-contract=off}.
The exact assembly is implemented in \texttt{agents/75-audit-tail/code/assemble75.py}:
sum the printed decimals as rational numbers, using the class multiplicities in the caption,
the mode-A values for $22\le n\le106$, the mode-B values for $108\le n\le260$,
and the printed mode-B remainder, without subtracting any rounded tail totals.
The denominator is the exact binary64 number $h_C=2769713770832855/2251799813685248$.
The assembled numerators are $0.987762443170525$ and $1.1914067844431$;
their quotients are at most $0.987763$ and $0.968624$.
```

For a standalone distributed bundle, place these identified records, commands and checker alongside its programs and adjust their archive prefix consistently. Merely citing an absent file or the old floating assemblers would not complete this packaging repair.

Target: `app-tail.tex:121`, replace the arithmetic paragraph. This incorporates Finding 1's acceptance conditions and corrects the literal “no subtraction”/“before any computation” claims without altering the trust assumption.

```latex
\emph{Arithmetic.}
The enumeration and walk bounds are evaluated as sums of products of nonnegative quantities.
The constants $\cs,\ct$ are decreased and $\bar\alpha,\bar\beta$ increased by one unit in the last place after decimal conversion;
$1/3$, $1/5$, $1/\cs$ and $1/\ct$ are computed by upward division.
The walk arrays are stored in binary32 and the enumeration in binary64.
Bound-producing products, sums and conversions, and their output decimals, are rounded upward, with gradual underflow.
The ordering search and the construction of a candidate $z$ need not use upward rounding: any chosen ordering gives an upper bound for the per-trail minimum, and the stored candidate is subsequently treated as an exact dyadic vector.
In checking $z\mathbb W\le\lambda z$, the left side is rounded upward and the right side downward; $1-\lambda$ is rounded downward in the remainder formula.
Acceptance requires finite nonnegative data, $0<\lambda<1$, the checked sub-invariance inequality, and $V_T=0$ wherever $z=0$.
Ratios defining $a$ are taken only at positive coordinates of $z$, with upward rounding; nonfinite values or failed checks reject the certificate.
The table uses exact rational sums of the upward-printed per-length bounds and the upward-printed remainder, followed by decimal ceilings.
The programs must be compiled with \texttt{-frounding-math}, without unsafe reassociation; the archived rerun also used \texttt{-ffp-contract=off}.
Correct directed arithmetic, conversions and decimal output, and gradual underflow, are part of the computational trust assumption.
```

Target: `app-tail.tex:123`, replace only item (4), leaving items (1)–(3) unchanged.

```latex
(4) The numbers of Table~\ref{tab:tail} come from the archived recomputation with
$\bar\alpha=0.18094$, $\bar\beta=0.36751$ entered directly, as identified above.
Exact assembly of the earlier outputs with $0.18093$, $0.36750$ gives the row bounds
$0.987731$ and $0.968592$.
Every printed per-$n$ output of the two runs differs by a factor in
$[1.0000322,1.0000333]$.
Since every term of \eqref{e:mT} carries exactly one response coefficient, linearly and with a nonnegative weight,
and the earlier orderings may be kept, the earlier run alone also gives
$\rho(M_1)\le0.987731\cdot0.18094/0.18093<0.98779$.
```

**Consequences elsewhere.** Proposition C.4 and Table C.1 are retained, with the repaired remainder application. Remark C.5 retains `0.91825`; its archive locator and stronger unsplit rule are clarified under Finding 6. Theorem 8.1 and the main theorem retain their constants. The numerical errors just corrected occur in the comparison prose, not in the corrected-coefficient certificate.

## FINDING 3: CONFIRMED

`alm8.c:59` computes `4^i` in signed `int` for all `i<24`, regardless of `m=8`. On this platform `4^15=1073741824` fits, and its multiplication by four for index 16 overflows a 32-bit `int`. This is undefined C behavior. Later non-use of those entries does not cure it.

**Reproduction.**

```sh
gcc -O1 -g -frounding-math -fsanitize=undefined \
  -fno-sanitize-recover=undefined -o audit/alm8_ubsan \
  /home/ubuntu/aklt/manuscript/bundle/programs/h2-trails/alm8.c -lm
./audit/alm8_ubsan 8 8 9610 9350 > audit/alm8_ubsan.txt 2>&1
```

Actual diagnostic:

```text
.../h2-trails/alm8.c:59:64: runtime error: signed integer overflow:
1073741824 * 4 cannot be represented in type 'int'
```

**Recovery, including an exact rational check.** [build_h2.py](audit/build_h2.py) creates an audit copy restricted to the stated instance `m=k=8,cs4=9610,ct4=9350`, initializes powers only through index 8, and constructs a positive test vector quantized to integers between `10^10` and `10^12`, constant on D4 orbits. It also enumerates the block continuations with **integer** accumulation: for each representative window, each monomial `(s,t,r)` records the sum of the target integer vector entries, with `s+t+r=8`. There are at most `3^8=6561` continuations per row, so each accumulated sum is at most `6561·10^12`, within `uint64_t`. No rounded matrix coefficients enter the final rational evaluation. The original matrix construction, heuristic vector search and upward verification are retained as a separate check.

The DFS holds the eight old bonds and all earlier new bonds throughout each block. Its final window is the last eight directions of the resulting 16-step path. Rotation and reflection preserve bond distinctness, straight/turn types and departure revisits; thus the matrix is equivariant under D4 and checking the orbit representatives proves the inequality on all 7,500 windows. The independent geometry enumerator also found 7,500 windows and 938 orbits. Grid positions remain within distance 16 of the center of a `64×64` grid, powers stop at `4^8`, and array bounds are safe for the fixed instance.

```sh
python3 audit/build_h2.py
gcc -O2 -g -frounding-math -ffp-contract=off \
  -fsanitize=undefined -fno-sanitize-recover=undefined \
  -o audit/alm8_checked audit/alm8_checked.c -lm
./audit/alm8_checked 8 8 9610 9350 \
  > audit/h2_checked.txt 2> audit/h2_checked.stderr.txt
python3 audit/h2_exact.py > audit/h2_exact.txt
```

The corrected sanitizer run completes. Outputs:

```text
m=8 k=8 windows=7500
directed quotient_up=0.85594871032391507 hex=0x1.b63ee8cbca081p-1
integer vector min=10000000000 max=1000000000000 orbits=938
orbits=938 hmax/hmin=100 argmax code=1
exact lambda=
6108544377608925591520707327811288131392849080/
7136577582199331027120815376144776530746764161
lambda decimal=0.85594871032375311686608612715471206...
lambda <= .8559487104: True
.85594872 < (3923/4000)^8: True
lambda > .9807^8: True
```

Full exact data and positive vector are in [h2_integer_certificate.tsv](audit/h2_integer_certificate.tsv); [h2_exact.py](audit/h2_exact.py) evaluates them with `Fraction`. The matrix weights used there are exactly `1000/2883`, `200/561`, and `1/4`. The displayed exact lambda is the quotient for the integer vector; the upward float check uses binary64 approximations to its scaled entries. Each is independently a valid positive-vector certificate, so they need not give identical last bits.

I also checked the final sentence of `sec8-computer-assisted.tex:33` rather than deleting it as collateral damage. Repeating the vector search with window revisit weight `1/5` and rationally evaluating its integer certificate gives

```text
exact lambda =
5416384655347347130837965158766968106343518899532800000000/
6575166879095725543694859235683487677318385244517008927319
lambda = 0.8237638306287757...
lambda < .97606^8: True
```

See `audit/alm8_checked_fifth.c`, [h2_fifth_exact.txt](audit/h2_fifth_exact.txt), and `audit/h2_integer_certificate_fifth.tsv`. Both rates can therefore be kept.

**Archival qualification to the referee's ancillary observation.** An independent orbit/rational implementation **does** exist in the full project: `76-audit-trail-count/code/almbig.rs`, `alm_big_exact.py`, and `alm_exact.py`; `out/cert_m8_almbig_exact.txt` records the claimed 938-class, ratio-100 bounds. The frozen bundle omits these. I did not treat the summary output as a checkable test vector: the full generated monomial/vector input is not present among that folder's supplied files. The new integer certificate above supplies an independently runnable check of the same asserted inequalities. This modifies the completeness observation, but not the confirmed C overflow.

**Minimal source correction.** For this certificate it suffices to validate the fixed instance and initialize only `pw4[0..8]`; the audit copy does exactly that. A general-purpose version needs checked integer/code/grid/CSR bounds for its allowed arguments. Replacing `int` by unsigned while retaining unchecked powers through 23 would still produce invalid capacities, so that alone is not the repair.

**Minimal LaTeX correction.** Target: `sec8-computer-assisted.tex:33`, replace its first sentence only. The next sentence is replaced under Finding 4, and the base-sum sentence under Finding 5. The existing independent rational-certificate assertion can remain, with the actual checker/vector supplied alongside the programs.

```latex
\emph{Certificate.}
For the certified instance, \texttt{alm8.c} first validates $m=k=8$ and the integer parameters $9610,9350$, and initializes only the powers $4^i$ for $0\le i\le8$; all integer codes and array indices in this instance are within their checked ranges.
It computes $\mathsf M_8$ on the $7{,}500$ windows with weights given by exact integer quotients rounded upward.
The matrix sums and products and the final Collatz--Wielandt verification use upward rounding; the intervening power iteration only chooses a test vector.
```

This text describes the repaired implementation, which must replace the defective distributed source. The exact checker and vector should also be included in the program package; merely asserting that an independent check once existed does not supply it.

**Consequences elsewhere.** H2's rate in Theorem 8.1, the constants appendix, the main theorem, and the optional `0.97606` rate remain unchanged. The proof of Lemma 8.2 is sound: its prefix/suffix map is injective, forgotten revisits have true weight `1/5≤x/3`, and detected revisits have `1/5≤1/4`. No mathematical transfer lemma needs replacement.

## FINDING 4: CONFIRMED

The original program sets `FE_TONEAREST` at line 108 and prints `best` with eight decimal places at line 110. An upper dyadic value can have a smaller nearest-rounded printed decimal. For example, the recovered upper value `0x1.b63ee8cbca081p-1` is about `0.855948710323915`, so the eight-decimal string `0.85594871` is below it. Likewise, `exp(log(best)/k)*(1+1e-12)` has no proved library-function error bound in the supplied computation and is not a root certificate.

This is a certificate-output defect, not a contradiction to the manuscript's conservative `0.85594872`. The corrected run under Finding 3 prints upward at 17 digits and prints the exact hexadecimal dyadic. More decisively, `audit/h2_exact.py` makes the comparison entirely rational:

```sh
python3 audit/h2_exact.py
```

```text
.85594872 < (3923/4000)^8: True
(3923/4000)^8 = 0.85598574917433487829016497315979004...
```

No logarithm, exponential or root routine is needed to deduce `q≤3923/4000=0.98075`. The exact comparison is against the certificate value or a rational upper bound for it; nearest-rounding a comparison threshold into binary64 would not by itself implement this rational test.

**Minimal LaTeX correction.** Target: `sec8-computer-assisted.tex:33`, replace only the sentence beginning “Every computed number is therefore …” (which follows the first sentence replaced under Finding 3).

```latex
The final upward evaluation bounds
$\max_\varsigma(\mathsf M_8h)_\varsigma/h_\varsigma$ by $0.85594872$.
Its upper bound is printed with upward rounding, together with the exact hexadecimal representation of the stored binary64 bound.
The desired rate is certified by the exact rational comparison
$0.85594872<(3923/4000)^8$, giving $q\le0.98075$;
no printed value obtained by taking a numerical root is used as a certificate.
```

The corresponding source change is to keep upward rounding for certified decimal output (and emit `%a`) and remove the certification label from any heuristic root. The audit copy already does this, and the separate rational checker verifies the rate.

**Consequences elsewhere.** No rate or theorem changes. The phrase “every computed number” is removed because the heuristic vector search need not produce upper bounds. The analogous distinction in the tail arithmetic paragraph is made under Finding 2.

## FINDING 5: CONFIRMED

The definition at `sec6-walks.tex:135,138` does not explicitly prohibit reversing the designated incoming direction at the first step. A direction alone is not an already used bond of a finite trail. With all four initial directions and a reverse step assigned the stated “otherwise turn” weight, the particular ratio-100 base-sum calculation cannot give `C_V≤153`. Explicitly forbidding just that initial step is enough to preserve the constant and matches the recursion's missing incoming bond.

**Independent exact calculation.** [trails_integer.c](audit/trails_integer.c) enumerates unordered-bond trails through length 15, retaining departure counts to distinguish true revisits. It records integer histograms by `(n,number of straight first departures,number of turning first departures)` for both initial conventions. [trails_exact.py](audit/trails_exact.py) evaluates them at exact weights `1000/2883`, `200/561`, `1/5` and exact `q=3923/4000`.

```sh
gcc -O2 -fsanitize=undefined -fno-sanitize-recover=undefined \
  -o audit/trails_integer audit/trails_integer.c
./audit/trails_integer > audit/trails_integer.csv
python3 audit/trails_exact.py > audit/trails_exact.txt
```

Selected outputs (comparisons use fractions, not these decimal presentations):

```text
Convention: all
max_(n<8) W_n/q^n = 1.9674554105303416022490324768369... at n=7
max_(8<=n<16) W_n/q^n = 2.0114363087879582443273481476839... at n=10
C = 201.14363087879582443273481476839... <=153: False; <=202: True

Convention: forbid
max_(n<8) W_n/q^n = 1.4722420397813478149883409602732... at n=7
max_(8<=n<16) W_n/q^n = 1.5051528376655832121642833048541... at n=10
C = 150.51528376655832121642833048541... <=153: True
C at smaller rate .9807 = 150.59204007372481335600087892736... <=153: True
```

The last check addresses the lemma's literal choice `q=λ^(1/8)`, which is slightly smaller than `0.98075`: Finding 3's exact lambda is greater than `0.9807^8`, so even evaluating all base sums at the smaller rational `0.9807` leaves the displayed constant below 153. Alternatively, the lemma's induction works directly with the chosen rational rate `q=0.98075` because `M_8h≤q^8h`.

**Downstream convention check.** In the kernel, `c` is deleted and the initial direction is from `c` to `u` (`sec7-recursion.tex:37`), so the forbidden first step would enter `c`. For Lemma `l:onepoint`, the stated assumption “at most three present bonds” guarantees an absent lattice bond can be designated, but its current “with a designated arrival direction” does not explicitly require this choice. Its statement and first proof sentence must say that the designated incoming bond is absent. In the two applications at `sec7-recursion.tex:80–82`, both starts `u,v` are neighbors of the removed center, so this stronger explicit hypothesis holds. In the kernel finiteness argument at `sec7-recursion.tex:54` it holds for the same reason. No recursion estimate changes.

The repair only prohibits immediate initial reversal. It does not declare the virtual incoming bond used for all later times, which would define a different family and is not required by this histogram computation.

**Minimal LaTeX correction.** Target: `sec6-walks.tex:135`, replace the definition paragraph.

```latex
Let $x_{\mathrm s}=1/\cs$ and $x_{\mathrm t}=1/\ct$.
For a trail $w=(v_0,\dots,v_m)$ of $\Z^2$ with a designated unit arrival direction $a$ at $v_0$, we require $v_1-v_0\ne-a$ when $m\ge1$.
The arrival direction is used to classify the first passage; its virtual incoming bond is not otherwise included among the bonds of $w$.
Let $\mathsf W(w)=\prod_{j=1}^m\omega_j$, with the empty product equal to $1$,
where $\omega_j=1/5$ if step $j$ leaves a site among $v_0,\dots,v_{j-2}$,
and otherwise $\omega_j=x_{\mathrm s}/3$ if $v_j-v_{j-1}$ equals the arrival direction ($a$ for $j=1$, $v_{j-1}-v_{j-2}$ for $j>1$), and $\omega_j=x_{\mathrm t}/3$ otherwise.
```

Target: `sec6-walks.tex:138`, replace only its final clause defining the sum.

```latex
where the sum runs over the trails of $\Z^2$ of length $n$ with that start and arrival direction and with initial reversal forbidden as above.
```

Target: `sec6-walks.tex:142`, replace “with a designated arrival direction” by:

```latex
with a designated arrival direction $a$ such that the bond $\{x-a,x\}$ is absent in $D$
```

Target: `sec6-walks.tex:149`, replace its first sentence only.

```latex
Every trail of $D$ is a trail of $\Z^2$ with initial reversal forbidden for the designated arrival direction, since the bond $\{x-a,x\}$ is absent in $D$.
```

Target: `sec8-computer-assisted.tex:16`, replace only “with a fixed start and arrival direction” by:

```latex
with a fixed start and arrival direction and with initial reversal forbidden as in \S\ref{s:H2def}
```

Target: `sec8-computer-assisted.tex:33`, replace only the sentence beginning “With the exact numbers …”.

```latex
The base sums use the initial-step convention of \S\ref{s:H2def} and $\mathsf W_0=1$.
At the rational rate $q=0.98075$ they satisfy
$\max_{n<8}\mathsf W_nq^{-n}<1.473$ and
$\max_{8\le n<16}\mathsf W_nq^{-n}<1.506$.
Together with $\max h/\min h=100$ and $\mathsf M_8h\le q^8h$, the induction of Lemma~\ref{l:alm} therefore gives $C_V\le153$.
```

**Consequences elsewhere.** `l:onepoint` gains the explicit absent-bond hypothesis above; its existing applications satisfy it. The kernel definition, its finiteness proof, Theorem 8.1, and every numerical constant can be retained. If four initial directions were retained instead, `C_V=202` would suffice for the reproduced certificate and downstream finiteness would survive, but that change is unnecessary and is not the correction proposed here.

## FINDING 6: CONFIRMED

The manuscript's safe range is correct. The stale claims are in the program comments and mode-A summary labels; the unsplit `tailmem5` branch also differs from the auxiliary walk literally defined in the appendix. These are documentation/implementation mismatches, not reasons to change the valid table cutoff.

**Exact geometry at the boundary.** I checked the direction word

`N^28 W^26 S E^27 S^26`

with integer coordinates and unordered bonds in `audit/geometry_windows.py`. It is a length-108 trail from `u=(-1,0)` to the C target `(0,1)`, avoids `c=(0,0)`, and hits the target only at its last vertex. Its first direction is N. At passage 54 it is at `(-27,28)`, with arrival W and departure S. The remaining other neighbors are west and north. Its west neighbor `(-28,28)` is the nonzero image of `c` obtained from `(a,b)=(0,-1)`. It is unvisited. Neither the north nor the out-neighbor is removed at that passage either, so all three true pairs are live. Rule R2 incorrectly deletes the west/north pair carrying `α` and the west/south pair carrying `β` at that image.

```sh
python3 audit/geometry_windows.py > audit/geometry_windows.txt
```

```text
boundary length=108; endpoint=(0,1); first target hit=108
passage54=(-27,28)
all three pairs live; R2 deletes W/N (alpha) and W/S (beta)
image(c)=(-28,28)
```

For completeness, the geometry proving the existing cutoff is sound: every nonzero quotient period has length at least `P=56`. A false image event at a site subject to deletion/R1, or adjacent to an image of `c` for R2, costs at least `2P−4=108` along a trail from `u` to `v`; the earliest relevant false event time is `P−2=54`. Consequently mode A is safe through `2P−5=107`, and mode B's rules stop before a false image event. In code, `t+1<=AT` is precisely the departure condition `t<t_*`. Arrival recording precedes deletion as required. Parity makes 106 the largest even length retained from mode A.

The source comments at `tailmem4.c:6,20–21` and `tailmem5.c:10,24–25` claim the obsolete range or obsolete square-torus formulas. Their `TAIL` summaries include `n=108`. That is memory-walk mass, not a certified trail contribution at every included length. The exact assembly under Finding 2 discards it and uses mode B beginning at 108.

**Unsplit branch.** `tailmem5.c:229–232` applies `if(k==2) continue` at the start site even when `D0=-1`. R1 at `app-tail.tex:46` instead keeps such a transition with weight `1/5` when `D0=*`. In `tailmem4.c:224–227` the revisit branch is retained and implements the written unsplit rule.

The stronger deletion still dominates genuine trails in the valid active-rule range. Such a trail has the known visit at time 0. A revisit detected by a memory-10 window at time at least 20 gives another visit at time at least 10. A further departure at `u` would require more than its three distinct incident bonds after deleting `c`. Thus the deleted transition cannot be part of the true trail. The same explanation applies to the archived unsplit `tailmem6` variant. It does not make those programs literally identical to the defined auxiliary walk; their stronger rule must be identified or the branch corrected.

**Reduced reruns I actually performed.** These use at most about 0.6 MB of walk arrays per run (`m=4`, 108 windows, 162 sites), not the production arrays.

```sh
gcc -O2 -frounding-math -ffp-contract=off -o audit/tailmem4_small \
  /home/ubuntu/aklt/manuscript/bundle/programs/h3-tail/code/tailmem4.c -lm
gcc -O2 -frounding-math -ffp-contract=off -o audit/tailmem5_small \
  /home/ubuntu/aklt/manuscript/bundle/programs/h3-tail/code/tailmem5.c -lm
./audit/tailmem4_small B 4 8 9 40 15 33 1 .99 .18094 .36751 1 1.23 \
  > audit/tail4_small.txt 2> audit/tail4_small.stderr.txt
./audit/tailmem5_small B 4 8 9 40 15 33 1 .99 .18094 .36751 1 1.23 -1 \
  > audit/tail5_unsplit_small.txt 2> audit/tail5_unsplit_small.stderr.txt
./audit/tailmem5_small C 4 8 9 33 33 8 .961 .935 .18094 .36751 1 1.23 1 \
  > audit/tail5_split_small.txt 2> audit/tail5_split_small.stderr.txt
```

The first different unsplit printed contribution is at `n=14`:

```text
tailmem4       = 54148949363/1000000000000
tailmem5(-1)   = 54145206523/1000000000000
difference    = 93571/25000000000 > 0
All printed tailmem5 values <= tailmem4: True
```

This is a discrepancy between auxiliary walks, not a trail counterexample. I also reran the referee's supplied rational small-walk checker against these **fresh** outputs after reviewing its direct per-response prefix products, dual-coordinate quotient map and transition rules:

```sh
python3 /home/ubuntu/aklt/referee/REF-R5/audit/small_memory_check.py \
  B -1 1 .99 B audit/tail4_small.txt > audit/small_modeB_exact.txt
python3 /home/ubuntu/aklt/referee/REF-R5/audit/small_memory_check.py \
  C 1 .961 .935 A audit/tail5_split_small.txt > audit/small_modeA_exact.txt
```

Both completed with `All checked upper bounds passed.` This is corroboration using the reviewed referee checker, separate from my own exact geometry and assembly. Examples:

```text
split C:N, D 12: exact ≈0.0245623382247368; printed 0.024562352405; upper=True
unsplit B, F 18: exact ≈0.0908939656769942; printed 0.090894095717; upper=True
```

The unsplit test crosses the rule-release time 15. Its remainder diagnostic has `check=OK`, `lcheck=0.973809635<1`. These tests establish no memory-10 terminal bounds.

For a concrete program repair, `audit/repair_tail_sources.py` corrects the comments/labels and changes the `tailmem5` deletion to `if(D0>=0 && k==2) continue`, in addition to Finding 1's support guards. On the same reduced unsplit instance, all its `E/D/F` outputs then equal those of `tailmem4`; the guarded `tailmem4` stdout is byte-identical to the original. The archived optional `tailmem6` stronger rule is retained and documented, so its existing production outputs remain the ones assembled above.

```sh
python3 audit/repair_tail_sources.py
gcc -O2 -frounding-math -ffp-contract=off -o audit/tailmem4_guarded \
  audit/tailmem4_checked.c -lm
./audit/tailmem4_guarded B 4 8 9 40 15 33 1 .99 .18094 .36751 1 1.23 \
  > audit/tail4_guarded_small.txt 2> audit/tail4_guarded_small.stderr.txt
cmp audit/tail4_guarded_small.txt audit/tail4_small.txt
gcc -O2 -frounding-math -ffp-contract=off -o audit/tailmem5_guarded \
  audit/tailmem5_checked.c -lm
./audit/tailmem5_guarded B 4 8 9 40 15 33 1 .99 .18094 .36751 1 1.23 -1 \
  > audit/tail5_guarded_unsplit_small.txt 2> audit/tail5_guarded_unsplit_small.stderr.txt
```

`cmp` returned 0. Filtering each run to `E/D/F` lines gave equality for the guarded `tailmem5` and original `tailmem4`.

**Minimal LaTeX correction.** The definitions at `app-tail.tex:46,51`, Lemma C.2 at `:56–57`, and its proof are retained. Target: `app-tail.tex:119`, insert the following implementation note after the program descriptions, coordinated with Finding 2's archive/assembly text.

```latex
The archived mode-A summary through $109$ is a memory-walk mass, and includes the unproved-for-trails value at $108$; only its per-length outputs through $106$ are used in Table~\ref{tab:tail}.
The unsplit mode-B production runs use \texttt{tailmem4.c}.
The archived unused unsplit option of \texttt{tailmem5.c} additionally deletes a window-detected revisit at $[u]$ while the rules act, whereas (R1) with $D_0=\ast$ retains it with weight $1/5$.
This additional deletion cannot remove a genuine trail in the valid range: the known time-$0$ visit, a window-detected later visit, and another departure would exceed the three available bonds at $u$.
It defines a stronger auxiliary rule and is not used for the mode-B entries of the table.
The obsolete validity comments and summary labels in the archived sources must not be used in place of Lemma~\ref{l:memdom}.
```

Target: `app-tail.tex:128`, append the following before “This variant is not used in the main line,” leaving `r:tailtypedep` and its numerical bounds intact.

```latex
The seven production records for this variant are
\texttt{c961\_935\_A\_B\_1.txt}, \texttt{c961\_935\_A\_B\_2.txt},
\texttt{c961\_935\_A\_C\_1.txt}, \texttt{c961\_935\_A\_C\_2.txt},
\texttt{c961\_935\_A\_C\_3.txt}, \texttt{c961\_935\_B\_B.txt},
\texttt{c961\_935\_B\_C.txt} in \texttt{agents/62-kernel-tail/out/}.
Their exact assembly, using the binary64 value of $1.20$, gives row bounds
$0.913009554182608$ and a quotient less than $0.918245584$.
The unsplit implementation uses the additional start-site deletion described in \S\ref{s:tailtrust}, justified by the same degree argument, and the remainder uses the nonnegative-vector formulation of Lemma~\ref{l:remainder}.
```

**Consequences elsewhere.** No numerical changes to Proposition C.4, Table C.1, `sec8-computer-assisted.tex:41,43,45`, Remark C.5, or the main theorem. The stale comments/output labels should be corrected in distributed source, and the table checker must enforce the proven cutoff. The archived unsplit type-dependent walk is documented separately so the original production output is not silently reinterpreted as output of a changed walk.

## Consolidated manuscript edits in file order

The file order is the manuscript's input order. Edits within a single original long line are disjoint replacements/insertions, intended to be applied together. All labels and numbering are retained.

1. **`sec6-walks.tex:135`** — explicit initial non-reversal convention, passage types, and empty product; Finding 5.
2. **`sec6-walks.tex:138`** — restrict H2's trail sum to that convention; Finding 5.
3. **`sec6-walks.tex:142`** — require the designated incoming bond absent in `l:onepoint`; Finding 5.
4. **`sec6-walks.tex:149`** — state why domain trails satisfy the initial restriction; Finding 5. The two applications at `sec7-recursion.tex:80–82` already meet the added hypothesis; no edit there is needed.
5. **`sec8-computer-assisted.tex:3`** — identify Appendix C's production-record locator and supply the records with the programs; Finding 2.
6. **`sec8-computer-assisted.tex:16`** — make the base trail convention explicit in `l:alm`; Finding 5.
7. **`sec8-computer-assisted.tex:33`** — replace the first certificate sentence with checked instance/integer bounds and distinguish heuristic search from verification (Finding 3); replace the “Every computed number …” sentence with upward output and rational rate comparison (Finding 4); replace the base-constant sentence with the restricted exact base sums (Finding 5). Keep the supported independent rational bound, ratio 100, and `1/5` refinement, supplying the checker/vector files.
8. **`app-tail.tex:76`** — `[0,∞)` in `l:remainder`; Finding 1. Its proof at 83–87 is unchanged.
9. **`app-tail.tex:90`** — candidate-vector construction, exact zero support and support-aware acceptance; Finding 1.
10. **`app-tail.tex:114`** — actual stored `lcheck`, nonnegative vector, zero-support verification and ratios on positive support; Finding 1.
11. **`app-tail.tex:119`** — identify all seven corrected production outputs, commands, compiler flags, exact assembly and exact dyadic denominator (Finding 2); insert the mode-A cutoff/unsplit-branch clarification (Finding 6).
12. **`app-tail.tex:121`** — replace arithmetic/trust paragraph, including explicit zero/nonfinite/rejection checks; Findings 1–2.
13. **`app-tail.tex:123`, item (4)** — old B upper bound `0.987731`, outward per-length ratio interval, corrected still-sufficient scaling; Finding 2.
14. **`app-tail.tex:128`** — locate the optional archived outputs and state its stronger start rule and support-aware remainder; Findings 1, 2 and 6.

No edits to the main theorem, Theorem 8.1, Proposition C.4's numerical statement, Table C.1's entries, the constants appendix, or the mathematical domination cutoff are required. Accompany the manuscript edits with the fixed H2 source, support-aware tail checks, corrected program comments/labels, production logs and exact assemblers identified above. The source inputs to this adjudication remain untouched.
