STATUS: PROVED

# GEN-PACKED

The reusable library is in namespace `AKLT.Gen.Packed`. Import `AKLT.Gen.Packed.All`.
The library proves extraction, packing as a sum, reconstruction, no-carry arithmetic,
masked lane selection, zero-filled square-grid translations, and the guarded comparison
**equivalence**. All certificate bounds are kernel checked in the worked example.
This is a generic arithmetic library and demonstration, not a stationary AKLT witness or a proof of H3′.

No sub-agents were used, and none of PROBE2's raw feasibility probes were executed.
I read the H3′/stationary and ranked-probe sections of `/home/ubuntu/aklt/compfeas/report.md`,
and the `Packed{1,16,128}` / `BellmanGuard{1,16}` source files without running them.

## Files

| File under `AKLT/Gen/Packed/` | Purpose |
|---|---|
| `Basic.lean` | `lane`, list/function packing, `Fits`, reconstruction, no-carry addition and scalar multiplication, GMP-friendly constant-plane formula |
| `Construction.lean` | Packing equals the finite sum; list concatenation equals shifted addition |
| `Routing.lean` | Bitwise extraction, whole-lane shifts, lane masks, row/column masks, four square translations |
| `Grid.lean` | Coordinate-level zero-fill semantics for all four translations |
| `Guard.lean` | Guard mask, exact subtraction digits, bounded and all-index comparison equivalences, Boolean checker equivalence |
| `Check.lean` | Proved mask-based cap checker, two-term row checker, structurally recursive multirow checker and soundness |
| `All.lean` | Public library entry point, without literal data |
| `Example.lean` | Two nonuniform literal planes with 10,000 lanes, one kernel decision, and the all-lane conclusion |
| `Audit.lean` | Signatures and `#print axioms` for every public library theorem and both example theorems |
| `Bench/Scale*` | Literal-bearing width/row benchmarks |
| `Bench/Kernel*` | The same arithmetic with already compiled literal inputs; kernel profiling |
| `Bench/Literal{1,10,50}MB.lean` | Single-literal loading attempts (decimal MB of binary payload, twice as many hex source characters) |
| `Bench/ImportOnly.lean` | Import baseline |

Raw outputs, time/RSS records, JSON summaries, reproducible Python generators/runners,
and the successful benchmark `.olean` files are in this report directory.

## Semantics and hypotheses

`lane P b s = (P >>> (b*s)) % 2^b`, least significant lane first.
`pack b [u₀,u₁,…] = u₀ + 2^b*(u₁ + …)`; `packFn_eq_sum` proves the sum
`Σ s < n, f s * 2^(b*s)` without a bound hypothesis. Correct extraction requires
`f s < 2^b`, and reconstruction requires `Fits P b n := P < 2^(b*n)`.

`lane_add` assumes that both inputs fit and that each lane sum is below `2^b`.
`lane_mul` assumes that the input fits and each scalar product is below `2^b`.
The semantic lemmas do not silently reduce the result modulo a lane base.

For guards, `g` is the bit position and **the total lane width is `g+1`**.
`guardMask g n` has value `2^g` in each of the first `n` lanes. Given `Fits` for
both operands and `A_s,B_s < 2^g`, `guard_compare_all` proves

```lean
Nat.land (guardMask g n + B - A) (guardMask g n) = guardMask g n ↔
  ∀ s, lane A (g+1) s ≤ lane B (g+1) s
```

The guarded digit is exactly `2^g+B_s-A_s`, and is below `2^(g+1)`.
Thus no cross-lane borrow or carry is assumed. There is also a bounded-index
version `guard_compare` and a Boolean equivalence `guardCheck_iff`.
The constant mask uses the closed form
`repeatLane b n v = ((2^(b*n)-1)*v)/(2^b-1)`, proved equal to the recursive
packer when `b>0`; kernel checks therefore avoid traversing a list of mask digits.

Grid index is `row*w+column`. `moveRight` shifts left by `b` bits and masks
out the first output column; `moveLeft` shifts right and masks the last column.
`moveDown`/`moveUp` shift by `b*w` bits and truncate to the square. Coordinate
lemmas prove the four boundary cases. `moveUp_grid` requires the finite input
width, so bits above the stored square cannot enter the last row. Predicate masks
are proved by complete-lane selection; row and column selection have separate lemmas.

`rowCheck` verifies both input caps with repeated low-bit masks, checks
`k ≤ g` and `(c₁+c₂)*2^k < 2^g`, and runs the guarded comparison against
`c₁*(B >>> (g+1))+c₂*B`. Its soundness theorem includes the no-carry argument.
The coefficient bound is sufficient and deliberately conservative.
`rowsCheck` recursively shifts **both** input planes by one lane between rows;
each check has distinct operands, with shared masks and coefficients.
These are overlapping shifted rows, not 100 separately supplied witness planes.

## Worked end-to-end certificate

The example has `b=80`, `n=10000`, `k=24`, `c₁=3`, `c₂=2`.
The inputs are independently nonuniform (deterministic seed `76161+n`);
`B_s` is in `[2^20,2^21)` and `A_s` in `[2^19,2^20)`.
The example is synthetic; its inequality is intentionally easy and is not a Bellman witness.
It checks both literal caps, the coefficient bound and the masked comparison with exactly
one decision call:

```lean
theorem checked : rowCheck 79 10000 24 3 2 A B = true := by decide +kernel

theorem all_lanes : ∀ s,
    lane A 80 s ≤ 3 * lane B 80 (s+1) + 2 * lane B 80 s :=
  rowCheck_sound checked
```

The conclusion holds for all natural indices, with zero fill past the finite inputs.
`checked` depends only on `propext`; `all_lanes` depends on
`propext, Classical.choice, Quot.sound`.

Measured source run: 34.308 s wall, 6.468 GiB peak RSS; source 400,385 bytes; `.olean` 214,952 bytes.

## Scaling measurements

Lean `4.35.0-rc2`, commit `11acb17ec6b07a8f9e9173e6845197929540936b`;
Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55` (prebuilt).
CPU: Intel Xeon Platinum 8488C (64 logical CPUs exposed).
All measurements are on this machine, fresh Lean processes, `-j 1` for timed runs.
At most eight Lean processes were permitted; the explicit benchmark runners use
at most three in parallel, alongside library builds, within the 128 GB budget.
RSS below is process peak including imports, not incremental proof memory.

The import-only baseline was 2.92 s wall and 6.449 GiB peak RSS.
Rows are width-80 fields, so the three bit widths have 1,250 / 12,500 / 25,000 lanes.
All checks include caps and coefficient checks as well as the weighted comparison.

| Plane bits | Rows in module | Kernel decision (ms) | Imported-data process wall (s) | Peak RSS (GiB) | Exit |
|---:|---:|---:|---:|---:|---:|
| 100,000 | 1 | 0.772 | 3.499 | 6.456 | 0 |
| 100,000 | 10 | 1.937 | 3.527 | 6.458 | 0 |
| 100,000 | 100 | 14.508 | 3.531 | 6.468 | 0 |
| 1,000,000 | 1 | 1.835 | 3.499 | 6.459 | 0 |
| 1,000,000 | 10 | 8.522 | 3.485 | 6.470 | 0 |
| 1,000,000 | 100 | 74.311 | 3.603 | 6.566 | 0 |
| 2,000,000 | 1 | 2.951 | 3.559 | 6.471 | 0 |
| 2,000,000 | 10 | 15.469 | 3.470 | 6.492 | 0 |
| 2,000,000 | 100 | 145.337 | 3.628 | 6.694 | 0 |

The kernel column is the `[Kernel] typechecking …checked._proof_1_1` interval
from `trace.profiler`, which is the proof introduced by `decide +kernel`.
It excludes literal elaboration, imports and semantic-theorem application; it is
not native execution. Kernel-profile modules import a successful ordinary `.olean`
containing the literal inputs and still make a fresh decision proof of each row count.
All these `checked` declarations print `[propext]`.

The literal-bearing source modules expose the much larger input-construction cost:

| Plane bits | Rows | Fresh source wall (s) | Peak RSS (GiB) | `.olean` bytes | Result |
|---:|---:|---:|---:|---:|---|
| 100,000 | 1 | 4.149 | 6.457 | 40944 | pass |
| 100,000 | 10 | 3.948 | 6.460 | 41080 | pass |
| 100,000 | 100 | 3.922 | 6.471 | 41080 | pass |
| 1,000,000 | 1 | 52.103 | 6.469 | 265952 | pass |
| 1,000,000 | 10 | 52.113 | 6.479 | 266088 | pass |
| 1,000,000 | 100 | 52.233 | 6.578 | 266096 | pass |
| 2,000,000 | 1 | 196.471 | 6.470 | 515952 | pass |
| 2,000,000 | 10 | 199.608 | 6.463 | 516088 | pass |
| 2,000,000 | 100 | 199.192 | 6.671 | 516096 | pass |

The original 2,000,000-bit source attempts had a 180 s limit. All three retries use a 300 s limit; all row counts also have separately measured
imported-data kernel checks. Thus a source timeout is an elaboration result, not a failed inequality.
Each source module contains two literal planes and one structurally recursive
checker call; it does not emit one theorem per row.

## Single-literal loading / serialization

MB means 1,000,000 bytes of packed binary data. A hex numeral therefore has
2,000,000 / 20,000,000 / 100,000,000 source digits in these three attempts.
The literal is a nonuniform repeated 64-bit pattern, and the following theorem
would check its low 16 bits. All attempts use ordinary definitions and kernel proofs.

| Packed payload | Source bytes | Direct Lean wall (s) | User CPU (s) | Peak RSS (GiB) | Result |
|---:|---:|---:|---:|---:|---|
| 1 MB | 2,000,204 | 60.626 | 59.26 | 6.451 | timeout at 60 s |
| 10 MB | 20,000,206 | 60.592 | 59.27 | 6.525 | timeout at 60 s |
| 50 MB | 100,000,206 | 60.595 | 59.20 | 6.818 | timeout at 60 s |

These direct measurements place `/usr/bin/time` **inside** `lake env`, around
`timeout … lean`, so that the killed Lean process is reaped and its CPU/RSS counted.
Earlier exploratory measurements wrapped `timeout lake env lean` and lost child
resource statistics on timeout; those logs are retained but excluded from the tables.
The 1 MB attempt also had exploratory 120/240 s censored runs, without trustworthy
child RSS. The direct logs show import completion but no completed literal definition,
no kernel theorem and no `.olean` serialization. Elaboration of the numeral is already
the bottleneck; there is no demonstrated hard memory/olean size ceiling at these sizes.

At 100,000 bits, each input numeral holds 12,500 bytes and elaborates in about
0.25 s; at 1,000,000 bits, each holds 125,000 bytes and elaborates in about 24.5 s.
The approximately 100-fold time increase for tenfold payload is consistent with
quadratic numeral conversion. This is an empirical scaling observation, not a
proved complexity bound. At 2,000,000 bits each numeral holds 250,000 bytes.
The largest completed individual numeral in these tests holds 250,000 bytes;
the two-numeral module holds 500,000 bytes of packed input.
The `.olean` payload size of successful modules is close to the binary data size;
serialization itself is milliseconds in the profiling logs. No claim is made that
1/10/50 MB single literals cannot eventually compile: those are explicitly censored tests.

Use smaller numeric chunks, join them by proved shift/add construction, and shard
witness rows across modules. `pack_append` provides the mathematical concatenation
identity. The library does not include a production chunk exporter or the actual H3′ data.

## Build and reproduction

No `lake update`, Mathlib build, or edits to `.lake/packages` were performed.
All source edits are under `AKLT/Gen/Packed/`; report/generator files are in the assigned report directory.
`source-audit.json` records a scan of every delivered Lean file for forbidden constructs; it found none.

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build AKLT.Gen.Packed.All
lake build AKLT.Gen.Packed.Example
lake build AKLT.Gen.Packed.Audit

# Full source measurement (example):
lake env /usr/bin/time -v -o /tmp/packed.time \
  lean -j 1 --profile -o /tmp/packed.olean AKLT/Gen/Packed/Example.lean

# Existing runners, from the worktree:
python3 /home/ubuntu/aklt/reports/GEN_PACKED/scaling.py
python3 /home/ubuntu/aklt/reports/GEN_PACKED/retry_2m.py
python3 /home/ubuntu/aklt/reports/GEN_PACKED/kernel_bench.py
python3 /home/ubuntu/aklt/reports/GEN_PACKED/literal_direct.py
```

`scaling.py` regenerates all width/row modules and uses the initial 180 s limit;
`retry_2m.py` retries the three 2M source modules at 300 s (up to two processes), skipping successful retries.
`kernel_bench.py` installs the successful data `.olean` in the worktree build tree
so its modules can import it. The `.olean` files come only from ordinary successful Lean runs.
`literal_bench.py` is the original source generator and exploratory runner; prefer
`literal_direct.py` for the trustworthy resource measurements above.

Final Lake build wall times:

- `lake build AKLT.Gen.Packed.All`: 16.092 s, exit 0.
- `lake build AKLT.Gen.Packed.Example`: 67.439 s, exit 0.
- `lake build AKLT.Gen.Packed.Audit`: 10.572 s, exit 0.

## Exported declaration statements

The following are the exact public theorem signatures from the delivered source.
Definitions, their computational equations, and theorem signatures appear below;
`Audit.lean` also checks the public declaration types.
All theorem names are relative to `AKLT.Gen.Packed`.

### Basic

```lean
def lane (P b s : Nat) : Nat := (P >>> (b * s)) % 2 ^ b

def packFn (b : Nat) : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, f => f 0 + 2 ^ b * packFn b n (fun s => f (s + 1))

def pack (b : Nat) : List Nat → Nat
  | [] => 0
  | a :: as => a + 2 ^ b * pack b as

def Fits (P b n : Nat) : Prop := P < 2 ^ (b * n)

def repeatLane (b n v : Nat) : Nat := (2 ^ (b * n) - 1) * v / (2 ^ b - 1)

@[simp] theorem lane_zero (P b : Nat) : lane P b 0 = P % 2 ^ b

@[simp] theorem lane_succ (P b s : Nat) :
    lane P b (s + 1) = lane (P / 2 ^ b) b s

@[simp] theorem lane_lt (P b s : Nat) : lane P b s < 2 ^ b

theorem lane_packFn (b n : Nat) (f : Nat → Nat)
    (hf : ∀ s < n, f s < 2 ^ b) (s : Nat) :
    lane (packFn b n f) b s = if s < n then f s else 0

theorem packFn_lt (b n : Nat) (f : Nat → Nat)
    (hf : ∀ s < n, f s < 2 ^ b) : Fits (packFn b n f) b n

theorem packFn_lanes (P b n : Nat) (hP : Fits P b n) :
    packFn b n (lane P b) = P

theorem lane_eq_zero_of_fits {P b n : Nat} (hP : Fits P b n) (s : Nat) (hs : n ≤ s) :
    lane P b s = 0

theorem lanes_ext {P Q b n : Nat} (hP : Fits P b n) (hQ : Fits Q b n)
    (h : ∀ s < n, lane P b s = lane Q b s) : P = Q

theorem packFn_add (b n : Nat) (f g : Nat → Nat) :
    packFn b n (fun s => f s + g s) = packFn b n f + packFn b n g

theorem packFn_mul (b n c : Nat) (f : Nat → Nat) :
    packFn b n (fun s => c * f s) = c * packFn b n f

theorem lane_add {P Q b n : Nat} (hP : Fits P b n) (hQ : Fits Q b n)
    (h : ∀ s < n, lane P b s + lane Q b s < 2 ^ b) (s : Nat) (hs : s < n) :
    lane (P + Q) b s = lane P b s + lane Q b s

theorem lane_mul {P b n c : Nat} (hP : Fits P b n)
    (h : ∀ s < n, c * lane P b s < 2 ^ b) (s : Nat) (hs : s < n) :
    lane (c * P) b s = c * lane P b s

theorem packFn_congr (b n : Nat) (f g : Nat → Nat)
    (h : ∀ s < n, f s = g s) : packFn b n f = packFn b n g

theorem pack_eq_packFn (b : Nat) (xs : List Nat) :
    pack b xs = packFn b xs.length (fun s => xs[s]?.getD 0)

theorem lane_pack (b : Nat) (xs : List Nat)
    (h : ∀ a ∈ xs, a < 2 ^ b) (s : Nat) :
    lane (pack b xs) b s = xs[s]?.getD 0

theorem repeatLane_eq (b n v : Nat) (hb : 0 < b) :
    repeatLane b n v = packFn b n (fun _ => v)

```

### Construction

```lean
theorem packFn_eq_sum (b n : Nat) (f : Nat → Nat) :
    packFn b n f = ∑ s ∈ Finset.range n, f s * 2^(b*s)

theorem pack_append (b : Nat) (xs ys : List Nat) :
    pack b (xs ++ ys) = pack b xs + 2^(b*xs.length) * pack b ys

```

### Routing

```lean
def laneMask (b n : Nat) (p : Nat → Bool) : Nat :=
  packFn b n (fun s => if p s then 2 ^ b - 1 else 0)

def gridIndex (w row col : Nat) : Nat := row*w+col

def rightMask (b w : Nat) : Nat := laneMask b (w*w) (fun s => decide (0 < s % w))
/-- Output mask for a leftward move: remove the rightmost column. -/
def leftMask (b w : Nat) : Nat := laneMask b (w*w) (fun s => decide (s % w + 1 < w))
/-- Output mask selecting exactly row `r`. -/
def rowMask (b w r : Nat) : Nat := laneMask b (w*w) (fun s => decide (s / w = r))
/-- Output mask selecting exactly column `c`. -/
def columnMask (b w c : Nat) : Nat := laneMask b (w*w) (fun s => decide (s % w = c))

def moveRight (P b w : Nat) : Nat := Nat.land (P <<< b) (rightMask b w)
def moveLeft (P b w : Nat) : Nat := Nat.land (P >>> b) (leftMask b w)
def moveDown (P b w : Nat) : Nat := Nat.land (P <<< (b*w)) (2 ^ (b*(w*w))-1)
def moveUp (P b w : Nat) : Nat := Nat.land (P >>> (b*w)) (2 ^ (b*(w*w))-1)

theorem testBit_lane (P b s i : Nat) :
    (lane P b s).testBit i = (decide (i < b) && P.testBit (b*s+i))

theorem lane_land (P Q b s : Nat) :
    lane (Nat.land P Q) b s = Nat.land (lane P b s) (lane Q b s)

theorem lane_shiftRight (P b k s : Nat) :
    lane (P >>> (b*k)) b s = lane P b (s+k)

theorem lane_shiftLeft (P b k s : Nat) (hb : 0 < b) :
    lane (P <<< (b*k)) b s = if k ≤ s then lane P b (s-k) else 0

theorem lane_laneMask (b n : Nat) (p : Nat → Bool) (s : Nat) :
    lane (laneMask b n p) b s = if s < n ∧ p s = true then 2 ^ b - 1 else 0

theorem lane_mask (P b n : Nat) (p : Nat → Bool) (s : Nat) :
    lane (Nat.land P (laneMask b n p)) b s =
      if s < n ∧ p s = true then lane P b s else 0

theorem lane_moveRight (P b w s : Nat) (hb : 0 < b) :
    lane (moveRight P b w) b s =
      if s < w*w ∧ 0 < s % w then lane P b (s-1) else 0

theorem lane_moveLeft (P b w s : Nat) :
    lane (moveLeft P b w) b s =
      if s < w*w ∧ s % w + 1 < w then lane P b (s+1) else 0

theorem lane_truncate (P b n s : Nat) (hb : 0 < b) :
    lane (Nat.land P (2^(b*n)-1)) b s = if s < n then lane P b s else 0

theorem lane_moveDown (P b w s : Nat) (hb : 0 < b) :
    lane (moveDown P b w) b s =
      if s < w*w ∧ w ≤ s then lane P b (s-w) else 0

theorem lane_moveUp (P b w s : Nat) (hb : 0 < b) :
    lane (moveUp P b w) b s = if s < w*w then lane P b (s+w) else 0

theorem lane_rowMask (P b w r s : Nat) :
    lane (Nat.land P (rowMask b w r)) b s =
      if s < w*w ∧ s / w = r then lane P b s else 0

theorem lane_columnMask (P b w c s : Nat) :
    lane (Nat.land P (columnMask b w c)) b s =
      if s < w*w ∧ s % w = c then lane P b s else 0

```

### Grid

```lean
theorem moveRight_grid {P b w r c : Nat} (hb : 0 < b) (hr : r < w) (hc : c < w) :
    lane (moveRight P b w) b (gridIndex w r c) =
      if 0 < c then lane P b (gridIndex w r (c-1)) else 0

theorem moveLeft_grid {P b w r c : Nat} (hr : r < w) (hc : c < w) :
    lane (moveLeft P b w) b (gridIndex w r c) =
      if c+1 < w then lane P b (gridIndex w r (c+1)) else 0

theorem moveDown_grid {P b w r c : Nat} (hb : 0 < b) (hr : r < w) (hc : c < w) :
    lane (moveDown P b w) b (gridIndex w r c) =
      if 0 < r then lane P b (gridIndex w (r-1) c) else 0

theorem moveUp_grid {P b w r c : Nat} (hb : 0 < b) (hr : r < w) (hc : c < w)
    (hP : Fits P b (w*w)) :
    lane (moveUp P b w) b (gridIndex w r c) =
      if r+1 < w then lane P b (gridIndex w (r+1) c) else 0

```

### Guard

```lean
def guardMask (g n : Nat) : Nat := repeatLane (g+1) n (2^g)

def guardCheck (g n A B : Nat) : Bool :=
  Nat.land (guardMask g n + B - A) (guardMask g n) == guardMask g n

theorem lane_guardMask (g n s : Nat) (hs : s < n) :
    lane (guardMask g n) (g+1) s = 2^g

theorem guardMask_fits (g n : Nat) : Fits (guardMask g n) (g+1) n

theorem lane_guard_sub {A B g n : Nat} (hA : Fits A (g+1) n) (hB : Fits B (g+1) n)
    (ha : ∀ s < n, lane A (g+1) s < 2^g)
    (hb : ∀ s < n, lane B (g+1) s < 2^g) (s : Nat) (hs : s < n) :
    lane (guardMask g n + B - A) (g+1) s =
      2^g + lane B (g+1) s - lane A (g+1) s

theorem guard_compare {A B g n : Nat} (hA : Fits A (g+1) n) (hB : Fits B (g+1) n)
    (ha : ∀ s < n, lane A (g+1) s < 2^g)
    (hb : ∀ s < n, lane B (g+1) s < 2^g) :
    Nat.land (guardMask g n + B - A) (guardMask g n) = guardMask g n ↔
      ∀ s < n, lane A (g+1) s ≤ lane B (g+1) s

theorem guard_compare_all {A B g n : Nat} (hA : Fits A (g+1) n) (hB : Fits B (g+1) n)
    (ha : ∀ s < n, lane A (g+1) s < 2^g)
    (hb : ∀ s < n, lane B (g+1) s < 2^g) :
    Nat.land (guardMask g n + B - A) (guardMask g n) = guardMask g n ↔
      ∀ s, lane A (g+1) s ≤ lane B (g+1) s

theorem guardCheck_iff {A B g n : Nat} (hA : Fits A (g+1) n) (hB : Fits B (g+1) n)
    (ha : ∀ s < n, lane A (g+1) s < 2^g)
    (hb : ∀ s < n, lane B (g+1) s < 2^g) :
    guardCheck g n A B = true ↔ ∀ s < n, lane A (g+1) s ≤ lane B (g+1) s

```

### Check

```lean
def capMask (b n k : Nat) : Nat := repeatLane b n (2^k-1)
def capCheck (b n k P : Nat) : Bool := Nat.land P (capMask b n k) == P

def linearRHS (B b c₁ c₂ : Nat) : Nat := c₁ * (B >>> b) + c₂ * B

def rowCheck (g n k c₁ c₂ A B : Nat) : Bool :=
  decide (k ≤ g) && decide ((c₁+c₂)*2^k < 2^g) &&
  capCheck (g+1) n k A && capCheck (g+1) n k B &&
  guardCheck g n A (linearRHS B (g+1) c₁ c₂)

def rowsCheck (g n k c₁ c₂ : Nat) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | r+1, A, B => rowCheck g n k c₁ c₂ A B && rowsCheck g n k c₁ c₂ r (A >>> (g+1)) (B >>> (g+1))

theorem capCheck_sound {P b n k : Nat} (hb : 0 < b) (hk : k ≤ b)
    (h : capCheck b n k P = true) : Fits P b n ∧ ∀ s < n, lane P b s < 2^k

theorem linearRHS_pack {B b n : Nat} (hB : Fits B b n) (c₁ c₂ : Nat) :
    linearRHS B b c₁ c₂ =
      packFn b n (fun s => c₁ * lane B b (s+1) + c₂ * lane B b s)

theorem rowCheck_sound {g n k c₁ c₂ A B : Nat}
    (h : rowCheck g n k c₁ c₂ A B = true) :
    ∀ s, lane A (g+1) s ≤ c₁ * lane B (g+1) (s+1) + c₂ * lane B (g+1) s

theorem rowsCheck_sound {g n k c₁ c₂ r A B : Nat}
    (h : rowsCheck g n k c₁ c₂ r A B = true) (j : Nat) (hj : j < r) :
    ∀ s, lane A (g+1) (s+j) ≤
      c₁ * lane B (g+1) (s+j+1) + c₂ * lane B (g+1) (s+j)

```


## Axioms audit

Every exported theorem has a `#print axioms` invocation. `Audit.lean` imports the
public library and the example and repeats the complete audit. Successful outputs
are copied below; only `propext`, `Classical.choice`, and `Quot.sound` occur.
The audit covers 47 public library/example theorems.
No forbidden proof escape or effectful Lean command is used. Literal benchmark
attempts that timed out have no successful theorem claim.

```text
'AKLT.Gen.Packed.lane_zero' depends on axioms: [propext]
'AKLT.Gen.Packed.lane_succ' depends on axioms: [propext]
'AKLT.Gen.Packed.lane_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_packFn' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.packFn_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.packFn_lanes' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_eq_zero_of_fits' depends on axioms: [propext]
'AKLT.Gen.Packed.lanes_ext' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.packFn_add' depends on axioms: [propext]
'AKLT.Gen.Packed.packFn_mul' depends on axioms: [propext]
'AKLT.Gen.Packed.lane_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.packFn_congr' depends on axioms: [propext, Quot.sound]
'AKLT.Gen.Packed.pack_eq_packFn' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_pack' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.repeatLane_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.packFn_eq_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.pack_append' depends on axioms: [propext]
'AKLT.Gen.Packed.testBit_lane' depends on axioms: [propext, Quot.sound]
'AKLT.Gen.Packed.lane_land' depends on axioms: [propext, Quot.sound]
'AKLT.Gen.Packed.lane_shiftRight' depends on axioms: [propext]
'AKLT.Gen.Packed.lane_shiftLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_laneMask' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_mask' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_moveRight' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_moveLeft' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_truncate' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_moveDown' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_moveUp' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_rowMask' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_columnMask' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.moveRight_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.moveLeft_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.moveDown_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.moveUp_grid' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_guardMask' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.guardMask_fits' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.lane_guard_sub' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.guard_compare' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.guard_compare_all' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.guardCheck_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.capCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.linearRHS_pack' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.rowCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.rowsCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Gen.Packed.Example.checked' depends on axioms: [propext]
'AKLT.Gen.Packed.Example.all_lanes' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Open issues / limits

- The full stationary Bellman certificate, automaton/trail semantics, exceptional sites,
  outside-square supersolution and rational prefix are outside this generic-library brief.
- Huge single numerals were measured with explicit time limits. There is no completed
  1/10/50 MB `.olean` result and no claimed hard maximum literal size.
- The measured multirow case shares masks/coefficients and shifts two input planes;
  it does not estimate import/storage costs for 100 independent large witness planes.
- Predicate row/column masks have proved semantics but use the recursive packer;
  an actual exporter should emit or verify efficient literal/closed-form boundary masks.
- All RSS includes a large Mathlib import baseline. Kernel caches retain temporaries;
  shard production checks and do not extrapolate the tiny synthetic row to an entire case.
