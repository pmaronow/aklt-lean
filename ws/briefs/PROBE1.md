# PROBE1 — kernel computation speed for exact certificates (Lean 4.35.0-rc2 + Mathlib 065356127b)

**Context.** We will formalize a computer-assisted proof to Palomar standards: every computation must be checked
by the Lean kernel. Forbidden: `native_decide`, `implemented_by`, `extern`, `unsafe`, `axiom`, `sorry`, `opaque`;
allowed axioms only propext, Classical.choice, Quot.sound (check with `#print axioms`). The inputs are:
(H1) positive definiteness of about 7,962 × (a few) symmetric integer matrices of size up to 245, by fraction-free
(Bareiss) elimination, the matrices themselves computed inside Lean from small combinatorial data;
(H2) a sum over ~7,500 trail windows × 3^8 continuations of products of rationals; (H3′) larger weighted-walk sums.
We need measured speeds to design certificates.

**Workspace.** Your worktree is `/home/ubuntu/aklt/wt/PROBE1` (a Lake project; Mathlib is prebuilt and linked —
never run `lake update`, never build Mathlib, never touch `.lake/packages`). Write only inside this worktree and
`/home/ubuntu/aklt/reports/PROBE1/`. Put Lean files under `AKLT/Probe/`. Compile single files with
`lake env lean AKLT/Probe/File.lean` (time with `/usr/bin/time -v`). Use at most 8 Lean processes at once and at
most 64 GB RAM in total; other agents share this machine. PATH needs `$HOME/.elan/bin`.

**Measure** (each with wall time, max RSS, and `#print axioms` of the final theorem):
1. Raw kernel throughput: a structurally recursive Nat loop (e.g. sum of `(i*i) % p` for `i < N`) proved equal to
   its value by `decide`, by `decide +kernel` (or the equivalent option in this Lean version), and by `rfl`
   (`Nat.decEq`), for N = 10^3, 10^4, 10^5, 10^6. Note which tactic avoids elaborator-side evaluation.
2. Big integers: the same with numbers of 100, 1,000 and 10,000 bits (GMP acceleration of `Nat.mul`, `Nat.div`,
   `Nat.gcd`, `Nat.ble`).
3. Bareiss: implement fraction-free elimination for a symmetric integer matrix (represent it as `List (List Int)`
   or another kernel-friendly structure you choose; also try a flat `List` or a balanced tree if lists are slow)
   returning `true` iff all leading pivots are positive; prove `pdCheck M = true` by kernel reduction for random
   symmetric positive definite integer matrices (entries about 10^6 in size) of sizes 10, 25, 50, 100, 150 and,
   if feasible, 245. Report time vs size and the fitted exponent. Also try an LDLᵀ certificate variant: given
   rational (or scaled integer) L and D, check M = L D Lᵀ and D > 0 — compare cost.
4. Rationals: kernel cost of Mathlib's `ℚ` arithmetic (normalization by gcd) vs. a hand-rolled representation with
   a common power-of-two denominator (dyadic upper bounds), for a sum of 10^4 and 10^5 products.
5. Does `Array` help in the kernel, or is it list-backed? Does `Nat.rec`-compiled structural recursion beat
   well-founded recursion (which often does not reduce in the kernel at all)? Show one example of each.
6. Parallelism: can independent `example`s in separate modules be checked concurrently by `lake build -j`?
   (Measure 4 modules × one medium Bareiss each, built together.)

**Deliverable.** `/home/ubuntu/aklt/reports/PROBE1/report.md`, first line `STATUS: COMPLETE` or
`STATUS: PARTIAL (reason)`; then a table of every measurement (exact command, wall time, RSS), the fitted cost
model (seconds per elementary operation for small and big integers, per Bareiss pivot step at size n), and concrete
coding recommendations for certificate checkers (data representation, recursion style, tactic, module sizing).
Keep the Lean probe files in the worktree. Do not launch sub-agents. Do not stop before the report exists.
