VERDICT: PROVED WITH REPAIRS (explicit cap interfaces; terminal convention; new-h prefix and file contracts)

The proposed certificate is sound for the paper's true-trail definitions. All finite assertions pass an independent exact replay. No witness value, local coefficient, radius, prefix cutoff, or claimed contraction constant needed changing. The repairs below complete underspecified parts of the report's contract; no mathematical obstruction or counterexample was found.

The proof is [h3line.tex](h3line.tex), compiled as [h3line.pdf](h3line.pdf) using the minimal [main.tex](main.tex). Run `bash build.sh` to compile it. The independent replay is [replay.cpp](replay.cpp); run `bash replay.sh`. It reads the original MATH_FIT data without modifying it, and neither includes nor invokes the existing checker/generator programs. Its full exact fractions and receipts are in [replay.log](replay.log). The primary agent wrote all work, without subagents. Only this directory was written.

The theorem establishes, for the kernel with the newly fixed `h=(1,6/5)` short ordering,

\[
(M_1h)_B\le967724846/10^9<967725/10^6,
\qquad
(M_1h)_C\le1159917640/10^9<(6/5)(967725/10^6).
\]

The strict margins in the cleared comparisons are 154 and 1,352,360 in units of `10^-9`. The unrounded replay gives row ratios approximately `0.9677248435916523` and `0.9665980319004569`. The theorem holds uniformly for every finite true-trail length cutoff and hence for the full nonnegative sums.

The necessary repairs and qualifications are:

1. **Specify both cap interfaces.** Stored line values are at most the exact cap floors, including at `k=±70`. Rows at these endpoints use exact cap ceilings at `±71`. The infinite line outside the interval is the exact rational minimum of exponentials, with no rounding. The stored-side upper cap controls the first exterior row, while the ceiling controls the first outgoing interior row. The supplied files already satisfy these requirements. We check all interior cap inequalities as the original construction does.
2. **Use the stopped terminal convention.** The finite statement exempts C/D rows at coordinate zero. Away from the target, a minimizing zero-coordinate C/D line has value one; the other, nonzero-coordinate line has value at most one and must also minimize, so its available row proves the bound. At the target the reward is dominated directly and the stationary row is zero. The centre is a separate zero-reward terminal. The proof establishes the free inequality off the target and `g+TF≤F` everywhere.
3. **Keep the patch cap and permanent initial rules.** All patch values obey `U/V≤F∞`, including every boundary and terminal value. Every inside boundary row uses `F∞` at outside successors; every outside row uses monotonicity at inside successors. The initial edge and two known sites depend on the first direction and remain in force throughout the suffix. The proof checks the `L=m+2` timing and shows that the known-site killing rule cannot kill a true continuation. It keeps B/N and B/W separate and all three C cases; B/S follows only from a bijection of true trails.
4. **Recompute the exact prefix contract for the new h.** All rewards, response ceilings, ordering keys, and the common phase denominator use exact `6/5`. The denominator is `Δ=13478025000`, replacing the old dyadic-h denominator. Hits at time twelve belong to the sorted short sum. Surviving prefixes use the long-order phase propagation and the full radius-20 patch values. The extra vector in each patch file copies the x-line at zero; it is not an exterior cap vector. Its entries are checked against the line array. The kernel formula is retained, with the newly specified short ordering; equality with the old numerical matrix is not asserted.

No changes to H1 or Appendix D are required. This work does not establish the separate H1-tree proposal. It gives the complete H3-line implication and optionally deduces H2 from the tilted vectors. The retained-H2 closing calculation assumes the paper's existing H2 certificate; the folded-H2 alternative is proved and checked here. This is a written proof with an exact native replay, not a claim that a new Lean formalization has been completed.

The finite inputs are listed below. “Row checks” counts component Bellman inequalities, except where an indexing/identity test is explicitly indicated. Nonnegative payloads are stored in 32 bits; the width column gives the largest actual value width. Paths are relative to `/home/ubuntu/aklt/reports/MATH_FIT/data`.

| Input | Shape / value count | Row checks / other required tests | Actual value width | Source bytes |
|---|---:|---:|---:|---:|
| `windows_m10_min.txt` | 60,092 map pairs; 3,741 rows of 9 integers; 63,834 text rows including header | 240,368 raw direction comparisons; representatives, exhaustive enumeration, successor/kind/incoming checks | codes 20 bits; classes 12 bits; kinds 2 bits, plus `-1` sentinel | 772,897 |
| `axis_z_integer.bin` | `4×4×3741 = 59,856` | 59,856 tilted rows; positivity; 29,928 C/D lower bounds; exact tail comparison | 27 bits, max 83,704,870; min 10,486 | 239,424 |
| `line_integer.bin` | `2×4×3741×141 = 4,219,848`, plus five 64-bit header words | 4,204,884 line rows, including 59,856 endpoint rows; 4,219,848 caps; 14,964 C/D zero values; 2,094,960 C/D off-zero upper bounds | 24 bits, max 10,768,774 | 16,879,432 |
| `line_init_integer.bin` (derived) | 4,219,848 cap floors | every entry regenerated exactly | 27 bits, max 77,996,688 | 16,879,392 |
| `line_tails_integer.bin` (derived) | `2×4×3741×2 = 59,856` cap ceilings | every entry regenerated exactly | 19 bits, max 284,867 | 239,424 |
| `line_B_m10_R20_d1_integer.bin.gz` | 25,154,484 patch values; 14,964 redundant line-zero values; nine header words | 25,124,556 rows; 25,154,484 caps; 29,928 terminals; metadata identities | 21 bits, max 1,057,671 | 58,274,180 |
| `line_B_m10_R20_d2_integer.bin.gz` | same shape | same checks | 21 bits, max 1,066,965 | 58,289,102 |
| `line_C_m10_R20_d1_integer.bin.gz` | same shape | same checks | 21 bits, max 1,048,576 | 58,307,096 |
| `line_C_m10_R20_d2_integer.bin.gz` | same shape | same checks | 21 bits, max 1,048,576 | 58,846,079 |
| `line_C_m10_R20_d3_integer.bin.gz` | same shape | same checks | 21 bits, max 1,048,576 | 58,919,730 |

The five patches contain 125,772,420 U values and require 125,622,780 nonterminal component rows. Each includes 2,394,240 spatial boundary rows and 29,928 known-site component rows. The five compressed files total 292,636,187 bytes; each decompressed file is 100,677,864 bytes including header and redundant vector. The main finite row total is **129,887,520**, plus the stated cap, terminal, quotient, and prefix checks. Derived floor/ceiling tables are checked conveniences, not independent mathematical witnesses.

The exact tilted residual minimum is `η=2951081685866839636` (62 bits). Individual finite row sums use at most 75 bits for tilts, 72 for lines, and 69 for patches. Every row has at most six edges, each coefficient numerator is below `2^48`, and payload values are 32-bit, so the 128-bit row arithmetic has a rigorous bound below `2^83`. Cap rationals and prefix accumulators use arbitrary precision.

| Case | Prefix nodes | Surviving length-12 prefixes | Short first hits | Tail accumulator bits | Ceiling for `10^9 J` |
|---|---:|---:|---:|---:|---:|
| B/N | 139,985 | 89,150 | 937 | 422 | 343,236,463 |
| B/W | 161,929 | 103,257 | 922 | 422 | 281,251,920 |
| C/N | 105,025 | 66,947 | 715 | 421 | 522,717,990 |
| C/W | 155,673 | 99,168 | 1,036 | 422 | 372,660,908 |
| C/S | 145,485 | 92,748 | 861 | 422 | 264,538,742 |

The replay tests exact short sorting with path-index ties, phase propagation, every full-patch lookup, and the cleared rational comparison for each case. It reproduces all five supplied exact rational J values. It does not reuse the old grouped prefix evaluation, supplied fractions, or existing automaton-generation logic.

The doubtful interface steps were also tested directly. All **119,712 exact rational free rows at `k=−100,−71,71,100`**, over both axes and every phase/class, pass. This includes exterior rows whose successors are stored values at `±70`. All **14,964 omitted C/D coordinate-zero free rows** were evaluated with unrounded coefficients: these happen to pass too, with maximum ratio `328000259/377880576<1` (axis x, phase C, class 0). This extra property is not used by H3-line or its minimizing-line proof. The exhaustive finite boundary checks and analytical exponential proof establish the all-distance statement; the samples at 100 are supplementary.

The optional H2 removal passes the exact comparisons

\[
8000\eta\ge 2^{48}Z_{\max},\qquad Z_{\max}<8000Z_{\min},\qquad
1600000^{10}<2\,1495813^{10}.
\]

The proof takes the geometric mean of opposite x-tilted A vectors, uses Cauchy–Schwarz to produce an untilted open-trail supersolution, then applies true-window domination including all short lengths. It yields **`q=7999/8000`, `C_V=16000`** without the separate H2 numerical witness.

For either H2 choice, the modified Section 7 constants are explicit: `H=6/5`, `C=22899/25000`, `ρ=78709/80000`, `B*=16HCC_V q/(1−q)^3`, `ε=min((1−q)/4,1291/(80000 B*))`, `θ=1−ε`, `C_T=2(12/5)^24(C_V/(1−q))^2`, and `A=(96000/1291)C_T`. The exact replay gives:

| H2 choice | q; C_V | Exact ε | Approximate C_T; A |
|---|---|---|---|
| Retained | `1119948287353/1120437614225`; 10 | `295429241889217285418799689/38634126128180928127866293784580458800250` | `1.39855×10^18`; `1.03997×10^20` |
| Folded | `7999/8000`; 16000 | `1291/11524003395010560000000` | `4.37039×10^25`; `3.24986×10^27` |

The text proves `q²<θ<1`, `M_θh≤ρh`, the same Section 7 recursion, and renewal with these constants. It also states the ensuing Section 5 constants.

The Appendix C changes are specified by source label in the proof's last subsection. Raw-memory and quotient material remains. The phase, stationary-domination, Bellman, prefix enumeration/domination, and true-trail reflection arguments remain with the new h and potential. The constant-exterior certificate and its local-to-global application are replaced by the tilted/line/patch construction. The old binary contract, dyadic-h denominator, five numerical prefix evaluations, and numerical assembly are replaced. If H2 is retained, its existing portion remains; if folded, its general lemmas remain but the separate memory-six numerical witness is unnecessary.

Validation completed with no failed required comparisons. The final build-plus-replay used **35.92 user seconds, 0.92 system seconds, 36.84 seconds elapsed, and 590,776 KiB peak RSS** on one process; see [replay.time](replay.time). The proof compiles with the minimal wrapper. Resource use is within the requested limits.
