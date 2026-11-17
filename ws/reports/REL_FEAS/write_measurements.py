import pathlib,json
R=pathlib.Path('/home/ubuntu/aklt/reports/REL_FEAS')
rows=[]
for p in (R/'measurements').glob('*/result.json'):
 d=json.loads(p.read_text())
 if d.get('family') in ['H1','H3']:rows.append(d)
rows.sort(key=lambda x:x['id'])
def fmt(x):
 if not x:return 'pending'
 mem=max(x.get('sampled_peak_bytes',0)/2**30,x.get('rss_kib',0)/2**20)
 return f'{x["wall_s"]:.2f} / {mem:.3f}'
def verdict(x):
 if not x:return 'pending'
 return 'ACCEPT' if x.get('accepts') else x.get('limit') or f'exit {x["exit"]}'
s='''STATUS: PARTIAL (largest prefix and row measurements pending; full release unavailable)

# REL_FEAS

Measurement snapshot written before recommendation or release-script implementation.
Machine: 64 logical threads (32 physical cores), Xeon Platinum 8488C, 495 GiB RAM.
Worktree commit: 973919fab9f115631dc07f81f23bb5c91404e777.
Production worktrees remain read-only. All builds/exports use copies under this report directory.
No producer build, generator edit, dependency build or lake update was performed.

## 1. Measurements

Times are wall seconds; memory is GiB (GNU-time maximum RSS or sampled process-tree RSS, whichever is larger).
Lean uses one thread and includes imports, elaboration and kernel checking: these are not pure reduction timings.
Existing Mathlib/main ordinary oleans were reused. Checker slowdown against Lean includes its substantial import floor.
Both checkers use one worker, 20 GiB RSS cap, 80 GiB address-space backstop. Polling at 0.1 s floors tiny timings.
Exact commands, CPU time, RSS, timeout, export SHA256 and requested names are retained under measurements/.
Sample builds are not claimed as a clean build of all certificate libraries.

Each export requests exactly roots.txt and includes its transitive closure, including internal proof helpers.
H1 single-declaration samples preserve the original name, statement and proof in an isolated module importing original data owners.
They establish acceptance of those declarations, not every theorem in the original bundle.
H3 rows/prefixes/raw checks are original complete modules.

| Sample | Lean s / GiB | Export s / GiB | con-ron s / GiB | Verdict | NanoDa s / GiB | Verdict | con-ron / Lean | NanoDa / Lean |
|---|---:|---:|---:|---|---:|---|---:|---:|
'''
for d in rows:
 l=d['lean'];c=d.get('conron');n=d.get('nanoda')
 cs=f'{c["wall_s"]/l["wall_s"]:.2f}x' if c else '—'
 ns=f'{n["wall_s"]/l["wall_s"]:.2f}x' if n else '—'
 s+=f'| {d["id"]} | {fmt(l)} | {fmt(d.get("export"))} | {fmt(c)} | {verdict(c)} | {fmt(n)} | {verdict(n)} | {cs} | {ns} |\n'
s+='''
Largest B1 prefix P0106: Lean 93.00 s / 15.35 GiB; con-ron timed out at 180.05 s / 16.39 GiB, with no verdict.
Original R0233/R0026/R0011 row builds: 7.46/8.25/8.86 s, sampled RSS 8.46/9.13/9.13 GiB. Full row export pending.
P0106 has the pilot maximum 7,459 nodes; P0043 is empty; P0116 is near median.
R0233 has 52 planes; other row batches have 64. Raw R0008 is empty/invalid; R0063 is the largest-cost raw batch.
H1 P0000 is smallest; P0711/P7237 stress large matrices and packed rows. Full pilot Gramrows0000 is checked additionally.
Full Constructorrows0000 exceeded a 300 s Lean cap; the separately timed single declarations avoid bundling many reductions.

All completed sample axiom prints are subsets of [propext, Classical.choice, Quot.sound].
H3 finite checks/Gram checks generally report []; H1 packed checks report all three.
Exact output is in lean.log. NanoDa permits only those three axioms and must exit zero with "no typechecker errors".
Its "Unable to print axioms" pretty-printer warning does not mean a typechecker failure.
Con-ron must exit zero with its (--verified) acceptance marker. Censored runs are never acceptance or rejection.

### Export bottleneck and minimal probes

Stock exporter raw-small and empty-prefix runs both timed out at 240 s, using 6.51/6.63 GiB.
They stop on the shared 12,582,912-bit CertData.H3.Graph.denseClass literal.
It is retained inside PackedGraph although graph execution uses the block tree.
Stock LeanExport.Basic calls Nat.repr, implemented by digit-at-a-time division by ten.
A scratch copy of that pinned upstream exporter changes only decimal rendering to balanced division.
On five probes (Nat/Int multiplication, right shift, power, list) its output is byte-identical to stock:
exporter-validation.json. Original raw export now completes in 19.33 s and both checkers accept.
The empty prefix exports 248 MB of endpoint literals despite its zero result, in 73.62 s.
A digit-only JSON fast path is also being validated. These are untrusted serialization changes, not proof shortcuts.

Minimal probes cover 128-bit Nat/Int multiplication, a 100,000-bit power, Nat.rec at 10,000,
a 1,000-element list literal, a million-position right shift, and AND up to 65,536 bits.
Both checkers accept them (probes.jsonl, bit-probes.jsonl).
A minimal left-shift-only export is DECLINED by con-ron for an incomplete primitive pin environment before typechecking.
Changing its proof using Nat.shiftLeft_eq does not remove the shift from the theorem's type.
This is distinct from a false theorem and from memory growth. Release exports need Comparator's primitive roots.
Neither --no-pins nor --trusted is an acceptable workaround.

## 2. Full-release extrapolation

Producer inputs: H3 5,035 modules / 19.8 forecast Lean CPU-hours, approximately six hours numerical checks;
H1 7,964 owners, 7,962 patterns / 12,173 blocks, 115.35 forecast CPU-hours.
H1 stage CPU: constructors 79.64 h, Gram 8.51 h, local parameters 15.30 h.
These are forecasts, not completed full releases. Brief's proof-tree baseline is about 82,000 declarations / two minutes
for con-ron, excluding two known memory failures. Those failures prevent an unconditional proof-tree forecast.
Final headline proof and aggregation are not yet available.

No finite upper bound follows from censored samples. The following are explicit planning scenarios, not acceptance forecasts:

| Checker | Monolithic CPU/wall scenario | Memory scenario on 495 GiB | Complete-closure shards |
|---|---|---|---|
| con-ron | H1 at 1.5–5x Lean plus H3 numerical checks at 2–8x: roughly 180–600 CPU-h; ideal 64-way 2.8–9.4 h, effective 24-way 7.5–25 h. Longest declaration remains serial. | Allow 20–80 GiB installed environment, unmeasured. Add worker reduction memory. Sixteen reductions at the observed 16.4 GiB give 282–342 GiB total; 64 exceed machine RAM. | Same computation plus repeated parse/install. Groups of 16–64 owners amortize closure cost. No justified <12 h guarantee. |
| NanoDa | H1 at 0.4–1.5x and H3 at 0.5–2x: roughly 50–190 CPU-h; ideal 64-way 0.8–3.0 h, effective 24-way 2.1–7.9 h. Large prefix/row unresolved. | Lower memory than con-ron on completed samples; no measured full-environment or worst-prefix bound. Reserve the same 20–80 GiB base until measured. | Additional parsing per group. Conditional 2–10 h planning range; no validated upper bound. |

These multipliers are sensitivity bands, not fitted confidence intervals.
Use time = parse + install + sum(reductions)/effective_jobs + serial tail, and
memory = shared installed environment + concurrent reduction workspaces.
Separate shard processes repeat their installed environments.
At a 20 GiB process reservation, 22 workers occupy 440 GiB, leaving 55 GiB; this is a budget, not demonstrated scalability.

Five spatial catalogs alone contain 14,964*5 literals of 1,590,480 bits.
Their decimal digits occupy about 35.8 GB, plus endpoints, H1, graph, syntax and proofs.
The monolithic export exceeds this study's 30 GB disk budget even before oleans.
One export per row is wasteful: 1,170 row exports each capture an entire case catalog.
Group exports share catalogs within a group. Keep hashes/receipts and delete large exports only after checks.
Clean Lean builds add roughly 135 certificate CPU-hours plus ordinary proof-tree work, with producers' memory-limited wall forecasts
approximately 5–10 h combined. Serialization is additional and stock decimal rendering is an unresolved serial cost.

### What sharding proves; Comparator compatibility

An accepted shard proves its requested declarations and full closure in the environment actually consumed.
Combining evidence requires one source commit/toolchain and identical canonical declaration contents on every overlap.
Root names or olean filenames alone do not establish this.
Certificate shards plus a Lean build do not independently check the final headline assembly.
Today any shard requesting the headline includes all its certificate proof dependencies, making that shard monolithic again.
Replacing certificate proofs with extra axioms changes the standard; it does not meet the permitted three-axiom release.
A genuine incremental union needs checker support, declaration/closure binding and a validated composition procedure.

The installed lake comparator accepts ONE challenge export and ONE solution export, not a shard manifest.
Sources inspected: pinned toolchain src/lean/lake/Lake/CLI/Check.lean and Lake/Check/Compare.lean.
Concatenated NDJSON is invalid because indices are local. Canonical merging produces a monolithic environment again,
with its original memory/checking costs. A self-comparison stand-in tests plumbing, not the author's independent statement audit.

## Measurement snapshot boundary

Items 1–2 above were saved before recommendations and release-tool implementation.
Pending measurements will be incorporated without converting censored outcomes into success.

## ORCH-SUMMARY
- Measurement snapshot delivered before recommendation/script work.
- Both checkers accept sampled H1 Gram/packed and H3 empty/median prefixes and small/large raw checks.
- Largest prefix con-ron is censored; full row export pending.
- Stock export has a giant-literal bottleneck; balanced serialization preserves tested bytes.
- Final headline, full attachments, two proof-tree memory failures remain release prerequisites.
- Shards alone do not satisfy monolithic headline/Comparator verification.
'''
(R/'report.md').write_text(s)
print('wrote',len(rows),'sample rows')
