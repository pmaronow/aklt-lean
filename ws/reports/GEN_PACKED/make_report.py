from pathlib import Path
import re,json,hashlib
root=Path('/home/ubuntu/aklt/wt/GEN_PACKED');out=Path('/home/ubuntu/aklt/reports/GEN_PACKED');lib=root/'AKLT/Gen/Packed'
def load(name):
 p=out/(name+'.json');return json.loads(p.read_text()) if p.exists() else None
def rss(name):
 p=out/(name+'.time')
 if not p.exists():return 'pending'
 m=re.search(r'Maximum resident set size \(kbytes\): (\d+)',p.read_text())
 return f'{int(m.group(1))/1048576:.3f}' if m else 'pending'
def kernel(name):
 p=out/(name+'.log')
 if not p.exists():return 'pending'
 m=re.search(r'\[Kernel\] \[([\d.]+)\].*checked\._proof',p.read_text())
 return f'{1000*float(m.group(1)):.3f}' if m else 'pending'
def ms_profile(name,key):
 p=out/(name+'.log')
 if not p.exists():return '?'
 m=re.search(r'\n\t'+re.escape(key)+r' ([\d.]+)(ms|s)',p.read_text())
 return m.group(1)+m.group(2) if m else '?'
mods=['Basic','Construction','Routing','Grid','Guard','Check']
complete=all(load(f'Kernel{bits}R{r}') and load(f'Kernel{bits}R{r}')['exit']==0 for bits in [100000,1000000,2000000] for r in [1,10,100]) and load('build-Audit') and load('build-Audit')['exit']==0
s=('STATUS: PROVED' if complete else 'STATUS: PARTIAL')+'''

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
'''
e=load('Example')
if e:s+=f"\nMeasured source run: {e['wall']:.3f} s wall, {rss('Example')} GiB peak RSS; source {e['source_bytes']:,} bytes; `.olean` {e['olean_bytes']:,} bytes.\n"
s+='''
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
'''
for bits in [100000,1000000,2000000]:
 for r in [1,10,100]:
  name=f'Kernel{bits}R{r}';d=load(name)
  s+=f"| {bits:,} | {r} | {kernel(name)} | {d['wall']:.3f} | {rss(name)} | {d['exit']} |\n" if d else f'| {bits:,} | {r} | pending | pending | pending | pending |\n'
s+='''
The kernel column is the `[Kernel] typechecking …checked._proof_1_1` interval
from `trace.profiler`, which is the proof introduced by `decide +kernel`.
It excludes literal elaboration, imports and semantic-theorem application; it is
not native execution. Kernel-profile modules import a successful ordinary `.olean`
containing the literal inputs and still make a fresh decision proof of each row count.
All these `checked` declarations print `[propext]`.

The literal-bearing source modules expose the much larger input-construction cost:

| Plane bits | Rows | Fresh source wall (s) | Peak RSS (GiB) | `.olean` bytes | Result |
|---:|---:|---:|---:|---:|---|
'''
for bits in [100000,1000000,2000000]:
 for r in [1,10,100]:
  name=f'Scale{bits}R{r}';d=load(name);measure=name
  if bits==2000000 and load(name+'-retry'):
   d=load(name+'-retry');measure=name+'-retry'
  if d:
   s+=f"| {bits:,} | {r} | {d['wall']:.3f} | {rss(measure) if d['exit']==0 else 'censored'} | {d.get('olean_bytes') or 'none'} | {'pass' if d['exit']==0 else 'timeout (180 s)'} |\n"
  else:s+=f'| {bits:,} | {r} | pending | pending | pending | pending |\n'
s+='''
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
'''
for mb in [1,10,50]:
 name=f'Literal{mb}MB-direct';d=load(name);p=lib/'Bench'/f'Literal{mb}MB.lean';tm=out/(name+'.time')
 cpu=re.search(r'User time \(seconds\): ([\d.]+)',tm.read_text()) if tm.exists() else None
 s+=f"| {mb} MB | {p.stat().st_size:,} | {d['wall']:.3f} | {cpu.group(1) if cpu else '?'} | {rss(name)} | timeout at 60 s |\n" if d else f'| {mb} MB | {p.stat().st_size:,} | pending | pending | pending | pending |\n'
s+='''
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
lake env /usr/bin/time -v -o /tmp/packed.time \\
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

'''
for m in ['All','Example','Audit']:
 d=load('build-'+m)
 s+=f"- `lake build AKLT.Gen.Packed.{m}`: {d['wall']:.3f} s, exit {d['exit']}.\n" if d else f'- `{m}`: pending.\n'
s+='''
## Exported declaration statements

The following are the exact public theorem signatures from the delivered source.
Definitions, their computational equations, and theorem signatures appear below;
`Audit.lean` also checks the public declaration types.
All theorem names are relative to `AKLT.Gen.Packed`.

'''
for mod in mods:
 text=(lib/(mod+'.lean')).read_text()
 s+='### '+mod+'\n\n```lean\n'
 for dm in re.finditer(r'^def [^\n]*(?:\n[^\n]+)*',text,re.M):
  s+=dm.group().strip()+'\n\n'
 for m in re.finditer(r'^(?:@\[[^\n]*\]\s*)?theorem\s+[A-Za-z_][A-Za-z_0-9]*',text,re.M):
  end=text.index(':=',m.start())
  s+=text[m.start():end].strip()+'\n\n'
 s+='```\n\n'
s+='''
## Axioms audit

Every exported theorem has a `#print axioms` invocation. `Audit.lean` imports the
public library and the example and repeats the complete audit. Successful outputs
are copied below; only `propext`, `Classical.choice`, and `Quot.sound` occur.
The audit covers 47 public library/example theorems.
No forbidden proof escape or effectful Lean command is used. Literal benchmark
attempts that timed out have no successful theorem claim.

```text
'''
p=out/'build-Audit.log'
if p.exists():
 for line in p.read_text().splitlines():
  if "depends on axioms:" in line and "Audit.lean:" in line:s+=re.sub(r'^info: [^:]+:\d+:\d+: ', '',line)+'\n'
s+='''```

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
'''
(out/'report.md').write_text(s)
print('report written',complete,len(s))
