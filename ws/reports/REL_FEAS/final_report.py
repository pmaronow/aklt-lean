import json,pathlib,time
R=pathlib.Path('/home/ubuntu/aklt/reports/REL_FEAS')
def load(p):
 p=R/p
 return json.loads(p.read_text()) if p.exists() else None
def peak(d):
 return max(d.get('sampled_peak_bytes',d.get('peak_tree_rss_bytes',0))/2**30,d.get('rss_kib',0)/2**20)
def val(d):
 if not d:return 'pending'
 return f'{d["wall_s"]:.2f} / {peak(d):.3f}'
def verdict(d):
 if not d:return 'PENDING'
 return 'ACCEPT' if d.get('accepts') else d.get('limit') or f'exit {d["exit"]}'
def link(p):return '['+p+']('+p+')'
ids=['h3-raw-small','h3-raw-large','h3-reps','h3-prefix-empty','h3-prefix-mid','h3-prefix-large',
     'h1-gram-small','h1-gram-heavy','h1-gram-0','h1-gram-711','h1-gram-7237','h1-packed-0','h1-packed-711','h1-packed-7237','h1-packed-owner']
data=[load('measurements/'+i+'/result.json') for i in ids]
extended=load('measurements/h3-prefix-large-extended/result.json')
longc=load('measurements/h3-row-group-long/conron-result.json')
longn=load('measurements/h3-row-group-long/nanoda-result.json')
complete=bool(longc and longn and load('measurements/h1-packed-owner/result.json') and (load('measurements/h3-row-group-shift-v2/result.json') or load('measurements/h3-row-group-shift-v2/aborted.json')))
s=('STATUS: COMPLETE\n' if complete else 'STATUS: PARTIAL (final capped conversion experiment still running; measurement tables, extrapolation, release script and stand-in tests delivered)\n')
s+='''\n# REL_FEAS — release feasibility

**Decision:** the current strict monolithic release procedure is not a 12-hour procedure. The decisive additional bottleneck is the Comparator's **sequential Lean kernel replay**, not just its independent kernels. H1 alone forecasts about 115 kernel CPU-hours. Small real H1 exports confirm that replay repeats their computations. The current large decimal data also causes long export/reader times. Balanced **shift** encoding fixes that representation cost on a converted 64-plane sample, but does not eliminate H1's numerical replay work.

This is a feasibility/tooling delivery, not an unconditional AKLT proof or completed full release. The actual closed proof of AKLT.Challenge.MainStatementV2, complete attachment and independently frozen challenge remain release prerequisites. The brief's ordinary-proof failures have documented repairs; release commit selection must include them (details below). No generated production source, generator, .olean or production cache was written. No subagents, lake update or Mathlib build were used.

Machine: 64 logical / 32 physical cores, Xeon Platinum 8488C, 495 GiB RAM. Worktree pin: 973919fab9f115631dc07f81f23bb5c91404e777; Lean 4.35.0-rc2; Mathlib 065356127b1dc0016f66b7283ce0ce2c4055aa55. Concurrent production load was not controlled; raw CPU/wall/RSS records permit that limitation to be assessed.

## Files and reproducibility

- [release runner](/home/ubuntu/aklt/wt/REL_FEAS/release/run-release.sh), [implementation](/home/ubuntu/aklt/wt/REL_FEAS/release/release.py), [instructions and attachment schema](/home/ubuntu/aklt/wt/REL_FEAS/release/README.md).
- [reproducible fast serializer builder](/home/ubuntu/aklt/wt/REL_FEAS/release/build-fast-exporter.py). This copies the pinned upstream serializer into a new scratch directory and changes formatting only. It records all source/binary hashes.
- Measurement drivers: measure.py, probes.py, h1_samples.py, full_packed.py, native_rows.py, long_rows.py, literal_probe.py, data_parse.py, macro_limbs_v2.py, shift_limbs.py, shift_equiv_pins.py, lean_replay.py, comparator_sample.py, comparator_shift.py, reencoded_rows_v2.py.
- Per-run commands, CPU/wall time, peak RSS, exit/cap, stdout/stderr and export hashes are under measurements/. Exact requested declaration names are in roots.txt or result.json. copied-artifacts.json records copied dependency hashes.
- [measurement-snapshot.md](measurement-snapshot.md) preserves the measurements/extrapolation written **before** recommendation and release-script implementation. This final report incorporates later results.

## 1. Measurements

Times are seconds; memory is GiB. Each cell is **wall / peak RSS**. RSS is the larger of GNU-time peak and sampled owned process-tree RSS. Sampling every 0.1 s floors very short runs. A normal sample build includes imports, elaboration and kernel checking, with prebuilt dependencies; it is not a pure reduction timer. The separate Lean replay measurements below put that distinction on an empirical basis.

All checkers are capped, with an address-space backstop. Standard measurements use one checker worker, a 20 GiB RSS cap and 180 s cap; larger runs have explicit longer caps. Long original row runs use 20 GiB / 5,400 s. Converted row checker runs use 15 GiB; the V2 re-encoding exporter uses 20 GiB. The complete H1 packed owner uses **two workers per checker**, 15 GiB and 1,800 s; its wall slowdown is not a single-worker comparison. Both successful exit and the appropriate acceptance marker are required. A timeout/cap is **not** a rejection or acceptance.

Each export requests exactly the listed public sample declarations and their full closure, including private proof helpers. H3 samples are original complete modules. H1 single-declaration samples preserve the original name, statement and proof in a copied module importing the original data owners. They do not certify the rest of an owner bundle. Full Gramrows0000, the later Gramrows0005 chunk and the complete original packed Constructorrows0029 owner are additionally measured.

| Sample | Lean module s / GiB | Export s / GiB | con-ron verified s / GiB | Verdict | NanoDa s / GiB | Verdict | Slowdowns C / N versus module |
|---|---:|---:|---:|---|---:|---|---:|
'''
for ident,d in zip(ids,data):
 if not d:continue
 c=extended if ident=='h3-prefix-large' else d.get('conron');n=d.get('nanoda');l=d['lean']
 ratios=(f'{c["wall_s"]/l["wall_s"]:.2f}x / ' if c else '— / ')+(f'{n["wall_s"]/l["wall_s"]:.2f}x' if n else '—')
 s+=f'| {ident} | {val(l)} | {val(d.get("export"))} | {val(c)} | {verdict(c)} | {val(n)} | {verdict(n)} | {ratios} |\n'
s+='''\nP0043 is empty, P0116 is near the B1 median, P0106 is the maximum-work pilot prefix (7,459 nodes). The initial 180 s P0106 con-ron run was censored; the table uses its successful extended run. Raw R0008 is empty/invalid, R0063 is the largest-cost raw batch; the representative batch is R0000. P0000 is the smallest H1 case; P0711/P7237 exercise large Gram/packed rows. Gramrows0005 checks a later row group starting at 96, where dot products are more expensive.

### Original B1 row modules and their large closure

The three original modules are R0233 (52 planes, start 14,912), R0026 (64 planes, start 1,664), R0011 (64 planes, start 704).
Their individual clean source timings were 7.46 / 8.25 / 8.86 s and 8.46 / 9.13 / 9.13 GiB sampled RSS.
All three checked proofs were exported together to share their identical full spatial/endpoint catalog closure. This is exactly those three modules' public declarations, not a broader all-module export.

The native formatting-only serializer took **1,236.15 s / 9.447 GiB**, producing approximately **7.0 GiB**.
One export per row would repeat that catalog each time. The original con-ron run was censored at **900.01 s / 1.018 GiB while parsing**, before installation/checking.
The final extended runs are:

| Checker | Seconds / GiB | Outcome |
|---|---:|---|
'''
s+=f'| con-ron --verified, jobs=1 | {val(longc)} | {verdict(longc)} |\n| NanoDa, threads=1 | {val(longn)} | {verdict(longn)} |\n'
s+='''\nThese are group costs, not invented per-module costs. Both original runs timed out before any acceptance or con-ron parse-complete/declaration-progress message. No kernel rejection or unbounded-memory claim follows. The Lean sum is 24.57 s but repeats imports three times: each checker has an aggregate wall slowdown **greater than 219.8x**, including the reader. Exact parse completion and kernel time are unknown.\n\nThe complete H1 packed owner Constructorrows0029 ACCEPTS in both kernels: Lean 166.50 s, con-ron 162.40 s (two workers; 320.59 CPU s), NanoDa 66.74 s (two workers; 133.09 CPU s). Against Lean's 166.49 CPU s these are **1.93x / 0.80x CPU**. It includes 79 public row declarations and all their generated private helpers; its 6.0 MB export contains 2,088 declarations. This is a whole owner result.

### Fresh Lean kernel replay

The pinned leanchecker --from-export parses the same exact sample export and replays it into a fresh kernel environment. It does not reuse project oleans.
'''
replays=load('lean-replay-results.json') or []
s+='\n| Exact H1 sample | Lean replay s / GiB | Verdict | con-ron / replay | NanoDa / replay |\n|---|---:|---|---:|---:|\n'
for d in replays:
 orig=load('measurements/'+d['sample']+'/result.json')
 s+=f'| {d["sample"]} | {val(d)} | {verdict(d)} | {orig["conron"]["wall_s"]/d["wall_s"]:.2f}x | {orig["nanoda"]["wall_s"]/d["wall_s"]:.2f}x |\n'
s+='''\nReplay of the two large packed rows takes about eight seconds, matching source-module time after its import floor. The complete 79-row Constructorrows0029 owner additionally replays in **132.75 s / 0.432 GiB**, ACCEPT, versus 166.50 s for source elaboration/build. Its replay CPU time is 132.64 s; source time includes repeated elaboration and import costs. This gives a measured source-to-replay factor of about 0.80 on a complete owner. The H1 production forecast amortizes imports over bundled owners: its 79.64 CPU-hour constructor stage has only 1,161 owners, so subtracting even five seconds of imports per owner removes only 1.61 hours. This is substantial kernel computation, not 80 hours of repeated import overhead.

### Export, reader and declaration-shape diagnosis

- Stock export of original raw/empty-prefix modules timed out at 240 s on the common **12,582,912-bit denseClass literal**. The inspected serializer calls Nat.repr, a digit-at-a-time decimal conversion.
- The balanced serializer is byte-identical to stock on five probes, and its native executable is byte-identical on the complete original raw and empty-prefix exports: exporter-validation.json, exporter-validation-v2.json, exporter-native-validation.json. Native raw / empty-prefix exports take 7.06 / 26.00 s. The final clean assembly run also uses the reproducibly rebuilt native exporter successfully (release-test-top-final).
- A minimal example has one such Nat literal and the reflexive theorem **huge = huge**. Lean accepts in 6.24 s; stock export times out at 120.02 s; native balanced export takes 2.01 s. con-ron and NanoDa ACCEPT in 15.08 / 15.47 s. Con-ron's check phase is effectively zero: the cost is decimal input parsing. Reproduction: literal_probe.py and scratch/lib/RELFEAS/Literal.lean.
- 64 **actual** B1 G0000.p0–p63 data values, with all their centre lanes checked, take Lean 33.57 s, native export 7.84 s, con-ron 18.18 s, NanoDa 28.04 s. Con-ron parsing alone takes 14.914 s.
- A data-only export of those same 64 constants, with no numerical checker theorem, ACCEPTS in 13.06 / 12.76 s. This isolates reader cost. At that throughput 74,820 full-release spatial literals alone cost about **4.2 / 4.1 hours** to read, before other data and proof computation; the full-catalog runs reveal additional scaling costs.
- Nat/Int multiplication on small literals, Nat.rec at 10,000, a 1,000-element list, 100,000-bit powers, AND through 65,536 bits, and nested powers all pass both checkers. These are controls, not evidence that every scaling regime is cheap.
- A left-shift-only minimal export initially DECLINES in con-ron for an incomplete primitive pin environment. Exporting Nat.div/Nat.mod first fixes it; the canonical Comparator primitive-root export also passes. This is distinct from a false theorem. The release runner always exports the primitive roots; it never uses --trusted or --no-pins.
- Direct Eq.refl expected did not improve a real raw check: con-ron 165.83 s versus 165.21 s, while Lean elaboration worsened to 238.77 s versus 39.21 s. A direct-reflexivity P0106 build timed out at 300 s. Keep the current decide +kernel style unless a separate measurement supports a change.

### Minimal kernel-memory failure and a statement-preserving repair

The standalone **RELFEAS.MulOrderOOM** example uses only Init:

    def large : Nat := 2^2097152 - 1
    def expected : Nat := (Nat.shiftLeft 97632666219444 2097152) - 97632666219444
    theorem small_first : 97632666219444 * large = expected := by decide +kernel
    theorem large_first : large * 97632666219444 = expected := by decide +kernel

Lean checks both in 0.30 s / 0.287 GiB. The export is 388,053 bytes and its largest Nat literal has only 14 decimal digits: the large integer is represented by the short power expression (minimal-shape.json). This separates kernel normalization from the earlier reader bottleneck.

| Proof/export root | con-ron s / GiB | con-ron outcome | NanoDa s / GiB | NanoDa outcome |
|---|---:|---|---:|---|
| small_first, direct computation | 9.55 / 4.052 | RSS_CAP at 4 GiB; no acceptance | 0.10 / 0.002 | ACCEPT |
| large_first, direct computation | 2.92 / 0.043 | ACCEPT | 0.10 / 0.002 | ACCEPT |
| Same small-first statement, explicit commutation | 4.62 / 0.043 | ACCEPT | 0.10 / 0.001 | ACCEPT |

The repaired declaration **RELFEAS.MulOrderOOMReformulated.checked** keeps the original small-first equality:

    theorem checked : 97632666219444 * large = expected :=
      Eq.trans (Nat.mul_comm _ _) large_first

Its Lean build takes 0.20 s / 0.272 GiB; all these theorem audits report no axioms. Checker progress leaves exactly small_first._proof_1 and small_first unfinished after the other 153 checks, placing the cap in numerical theorem checking. The failed export and successful reformulation have the same mathematical target, with explicit equality transport replacing conversion of the expensive product. A smaller 786,432-bit control shows the same asymmetry without hitting its cap: 2.21 s / 1.688 GiB versus 0.61 s / 0.043 GiB. Reproduction drivers are mul_order_oom.py and mul_reformulate_oom.py; all files remain under this report.

This directly identifies a **large-Nat multiplication operand-order / normalization hazard**. It does not establish that every Nat.rec or bitwise operation is intrinsically slow. In particular, the original full B1 row runs did not reach a reported kernel check, so this is a separate isolated hazard, corroborated on real data by the lane evidence below.

### Converted 64-plane sample: multiplication versus shifts

The same actual 64 plane values were encoded using balanced 8,192-bit leaves. No generator was edited.
The checker is unchanged: all 64 centre lanes equal zero. The add/multiply and add/shift encodings reconstruct the same Nat values; exact equalities to **every original p0–p63** were separately checked.

| Representation | Lean s / GiB | Stock export s / GiB | con-ron s / GiB | NanoDa s / GiB |
|---|---:|---:|---:|---:|
'''
for name in ['PlaneLiteral','PlaneMacro2','PlaneShift']:
 d=load('measurements/'+name+'/result.json')
 if d:s+=f'| {name} | {val(d.get("lean"))} | {val(d.get("stock_export",d.get("export")))} {(d.get("stock_export",d.get("export")) or {}).get("limit") or "complete"} | {val(d.get("conron"))} {verdict(d.get("conron"))} | {val(d.get("nanoda"))} {verdict(d.get("nanoda"))} |\n'
s+='''\nThe shift sample deliberately drops an unused Mathlib-backed import; its source-build time/memory comparison is therefore not controlled for that import. The checker exports contain the same relevant arithmetic and data. The multiplication macro has the same heavy import as the literal baseline. Explicit source syntax for thousands of limb operations was also tried and exceeded a 300 s elaboration cap; constructing the typed Expr directly avoids that overhead.

**Use low + Nat.shiftLeft high cutBits**, not low + 2^cutBits * high.
With shifts, con-ron's parse / install / check phases are 0.165 / 0.300 / 3.300 s.
With multiplication, con-ron parses in under a second but times out at 300 s / 6.85 GiB in normalization.
On the separate equivalence export it finished p0 through p10 before the 300 s cap: about 16–27 s per reconstructed plane.
This localizes the slowdown to normalization of large products in the encoded Nat expression, rather than JSON, a giant list, or an invalid result.
Both encodings pass Lean; NanoDa accepts both sample computations and all 64 equivalences.

The successful shift equivalence run uses the primitive pins and ACCEPTS in **20.21 s con-ron / 20.71 s NanoDa**.
The generic arithmetic model is proved in scratch/lib/RELFEAS/ShiftEncoding.lean:
combine_eq n cut states (n & (2^cut-1)) + ((n >> cut) << cut) = n;
rebuild_eq fuel n states that recursive splitting/reconstruction preserves n.
Both print [propext, Classical.choice, Quot.sound]. The 64 concrete equivalence proofs print only permitted axioms.
The low-RSS optional export attempt for the generic model itself was capped at 0.5 GiB; it is not represented as independent acceptance.

A larger-leaf follow-up uses **65,536-bit leaves**, the same 64 real planes and the same centre-lane checker. Both use the thin import set, so this comparison controls the imports:

| Leaf size | Native export s / GiB | Export MB | con-ron s / GiB | NanoDa s / GiB | Module olean MB |
|---|---:|---:|---:|---:|---:|
| 8,192 bits | 4.52 / 1.590 | 35.04 | 3.83 / 0.332 ACCEPT | 17.32 / 0.221 ACCEPT | 29.24 |
| 65,536 bits | 3.82 / 1.586 | 31.60 | 4.02 / 0.206 ACCEPT | 15.07 / 0.135 ACCEPT | 26.11 |

The literal module olean is 12.94 MB and its export 31.49 MB. Chunking increases olean size about twofold; it accelerates numerical input parsing rather than compressing the payload. The 8,192-bit native export is byte-identical to its accepted stock export. At 65,536 bits stock decimal export exceeds 120 s; the fast serializer is essential. All **64 exact original-value equalities** for the 65,536-bit variant ACCEPT: con-ron 19.70 s / 0.085 GiB, NanoDa 18.59 s / 0.031 GiB, and Lean 6.34 s. General combine/rebuild preservation is also Lean-checked with this bound. The initial tuning driver hit a configuration-variable error after its successful equivalence build/export; a checker-only resume checked the same hashed file (ShiftEquiv64K/result.json). No failure was turned into an acceptance.

Prefer a **65,536-bit source pilot** with the fast serializer for its smaller footprint; 8,192 bits retains the additional measured Comparator acceptance. Neither sample checks a complete converted planeBatch: the changed sample checks the centre-lane conjunct only, with all data equivalences verified. Full original consumers still need fresh source builds and checks.

A complete converted three-row export was attempted with the same original proof/type declarations, rewriting large Nat literal subexpressions in certificate definition values to shift expressions. This prototype is **not byte-identical** to the original environment. It is not the serializer used by the strict release runner.\n\nThe first full-catalog prototype matched only definition values that were literal expressions. Real declarations wrap literals in OfNat.ofNat applications. Its histogram retained all 14,962 spatial literals of 400,000–499,999 decimal digits plus denseClass at 3,787,833 digits; both readers timed out at 900 s. It is an **ineffective shallow-rewrite control**, not a test of the shift proposal. Its redundant 7.4 GB export was removed after preserving the hash, histogram and capped-run receipts. Corrected V2 walks nested expressions and is measured separately.
'''
d=load('measurements/h3-row-group-shift-v2/result.json')
if d:
 s+='\n| Converted full row group | Export | con-ron | NanoDa |\n|---|---:|---:|---:|\n'
 s+=f'| nested shift rewrite V2 | {val(d.get("export"))} {verdict(d.get("export"))} | NOT RUN: export failed | NOT RUN: export failed |\n'
else:s+='\nCorrected V2 full converted group: no complete export or checker acceptance was obtained.\n'
s+='''\nThe V2 exporter hit its **2,400-second / 20 GiB** limit, with sampled peak 9.154 GiB, before completing the environment. Its partial histogram contains 531,397 2,000–2,999-digit leaves and maximum 2,467 digits, confirming the nested rewrite operated on the emitted prefix. This is an expensive post-processing prototype, not a validated complete-case source encoding. No independent checker was run on the incomplete file. The successful small-source encoding controls cannot be extrapolated to a complete new release without the fresh consumer pilot.

### Comparator measurements and the serial kernel gate

The same primitive-complete sample export was used as both challenge and solution. This tests mechanics only.
The sample Comparator experiments enable **its built-in Lean kernel only** to isolate that mandatory cost;
the release-runner tests below enable all three required kernels.

| 64-plane representation | Comparator wall / GiB | Outcome |
|---|---:|---|
'''
for name in ['ComparatorPlane64','ComparatorShift64']:
 d=load('measurements/'+name+'/result.json')
 if d:s+=f'| {name} | {val(d.get("comparator"))} | {verdict(d.get("comparator"))} |\n'
s+='''\nThe old literal sample reaches the 600 s cap with no kernel-status message; the shifted sample ACCEPTS in 57.19 s.
The raw unchunked format is therefore a serious problem for Comparator as well as export.
Do not extrapolate the self-comparison time literally: a real frozen mathematical challenge does not contain the certificate data, whereas this test parses the data on both sides.

More decisively, inspect the pinned toolchain:
[LeanChecker.lean](/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/src/lean/LeanChecker.lean:72) calls kernelEnv.replay;
[Lean/Replay.lean](/home/ubuntu/.elan/toolchains/leanprover--lean4---v4.35.0-rc2/src/lean/Lean/Replay.lean:176) loops declarations sequentially through addDeclCore.
There is no export-replay job count or parallel task in this path. Comparator's num_threads setting belongs to external NanoDa, not this replay.
Thus module sharding during the original clean build does not parallelize the mandatory monolithic fresh Lean replay.

## 2. Full-release extrapolation

Initial planning forecasts (preserved in measurement-snapshot.md) from the read-only [H3 lane report](/home/ubuntu/aklt/reports/CERT_H3/report.md) and [H1 lane report](/home/ubuntu/aklt/reports/CERT_H1/report.md): H3 5,035 modules / 19.8 Lean CPU-h; H1 7,964 owners / 7,962 patterns / 12,173 blocks / 115.35 CPU-h.
H1 stage CPU-h: constructors 79.64, Gram 8.51, local parameters 15.30.
The ordinary proof-tree baseline supplied in the brief is about 82,000 declarations / two minutes for con-ron.
The read-only [FIX_STAR report](/home/ubuntu/aklt/reports/FIX_STAR/report.md) resolves the original Q037/Q038 conversion failures in commit 26a4d3c, already included in this study's 973919f pin. Round 2 additionally repairs **_private.AKLT.W.Q017.Main.0.AKLT.W.Q017.starCasimir_vacuum**. Q017's repaired source is absent at the study pin, but its SHA256 matches newer main at 63d176a (proof-repair-provenance.json). Q037/Q038 source hashes match this worktree. These are existing lane results, not new measurements here: con-ron/NanoDa accept repaired Q017 in 24 / 5.17 s, Q037 in 37 / 2.22 s, Q038 in 23 / 5.25 s; con-ron peak 0.56 / 2.50 / 0.56 GiB.
The repair proves small index/input equalities first and lifts them through the concrete matrix operator using congrArg/congrArg₂. It avoids definitional conversion through 3,125 configurations. Carry those repairs into the final source pin; do not treat the brief's original two failures as still open on current main.
The unfinished headline, unmeasured final aggregation, and full-size reader/environment behavior still prohibit a finite guaranteed whole-release upper bound.
The following are planning ranges and explicit assumptions, not confidence intervals or claims of full acceptance.

The machine has only 32 physical cores. Dividing single-worker CPU measurements by all 64 logical threads assumes an unmeasured SMT speedup.
Use 24–32 effective workers as the optimistic full-machine planning range, and measure full-environment memory before increasing concurrency.

An explicit numerical model (source/kernel CPU-hour forecasts multiplied by measured or assumed CPU factors) is:

| Stage | Lean forecast CPU-h | con-ron CPU factor | NanoDa CPU factor |
|---|---:|---:|---:|
| H1 constructors | 79.64 | 1.9–2.5, whole owner and isolated rows | 0.7–1.3, whole owner and isolated rows |
| H1 Gram | 8.51 | 1.6–2.0, measured chunks | 0.9–1.6, measured chunks |
| H1 local parameters | 15.30 | 1–4, **unmeasured allowance** | 0.5–2, **unmeasured allowance** |
| H1 remaining stages | 11.90 | 1–4, **unmeasured allowance** | 0.5–2, **unmeasured allowance** |
| H3 numerical work | 19.80 | 1.5–3, heuristic weighted sample mix | 1–2, heuristic weighted sample mix |

The sums round outward to **220–400 con-ron CPU-h / 100–220 NanoDa CPU-h**, excluding the separate decimal-reader allowance. Stage factors for unmeasured H1 checks and the final assembly are assumptions, not measured bounds. With a giant original catalog, parsing is serial and may dominate; the 90-minute censor means even these planning totals may understate its cost.


| Checker / stage | Original monolithic environment | With shifted data | Memory / limiting factor |
|---|---|---|---|
| con-ron | About 220–400 numerical CPU-h, plus at least 4–6 h spatial-data parsing at sample throughput: roughly 11–23 h at 24–32 effective workers; the long full-catalog parse may worsen this. At 16 effective workers plan 18–31 h. | Reader cost falls sharply on the converted sample, but H1 computation remains. Conditional 7–18 h after representation fixes; no full-release validation or upper bound. | Unmeasured full base allowance 40–120 GiB, then worker-local reductions. A largest prefix uses 17.7 GiB; 16 such workers plus a 120 GiB base is about 403 GiB. 32 worst-case prefix workspaces exceed the machine. Mixed workloads may permit more. |
| NanoDa | About 100–220 numerical CPU-h plus roughly 4–6 h parsing: about 7–16 h at 24–32 effective workers. | Conditional 4–12 h, based on faster readers and observed H1/P0106 ratios; largest full-catalog/final aggregation behavior is not assumed. | Base allowance 30–100 GiB, plus working reductions. Completed worst prefix is 5.3 GiB, heavy H1 Gram 1.45 GiB. Full retained environment remains unmeasured. |
| Comparator's fresh Lean replay | Approximately 90–140 h of serial numerical replay is a credible planning range; unchunked decimal parsing can add much more. | The same order of numerical replay remains after fixing the reader. This cannot become a 12 h stage just by changing job counts. | One replay thread; reserve full installed environment plus the largest kernel reduction. It may fit 495 GiB while taking several days. |
| Strict end-to-end runner | Clean build + export + standalone con-ron/NanoDa + Comparator, which reruns both external kernels and Lean. | Still a multi-day procedure with the stock sequential Lean replay. | The script preserves the requested standard and records failure/caps. It does not substitute shards or skip a kernel. |

A clean parallel source build has an ideal 135 CPU-h / 24 workers = 5.6 h floor before ordinary proof/build overhead; budget roughly 6–10 h if memory and dependency scheduling allow. Formatting-only native export scales to about 1.7 h for five original B1-sized catalogs (5 × 1,236 s), plus H1/proof data: budget 2–6 h, with unmeasured full-export memory roughly 30–100 GiB. Both assume the final source pin includes the documented FIX_STAR repairs. These estimates require larger future resources than this study.\n\nThe replay planning range allows the complete-owner source-to-replay reduction: 0.80 times H1's 115 h is about 92 h before H3 and proof-tree replay. It subtracts import floors per **owner**, not per theorem: constructor import overhead is less than two hours of the roughly eighty-hour stage. The measured source/replay packed samples support similar computation cost. Changing H1 module sizes cannot remove that work. The final proof closure still needs a complete measured check; the known operator-conversion repairs are described above.

Five H3 spatial catalogs alone render about **35.8 GB of decimal digits** (74,820 literals of about 1.59 million bits), before endpoints, expressions, H1 or proofs. The study cannot retain a full-release monolithic export under its 30 GB disk cap. A future clean release needs room for regenerated sources, oleans and the export: provision and verify approximately 150–200 GiB rather than using this study's default 26 GiB output budget.

### Sharded scheme: precise evidence and limitation

For diagnostics, group 16–64 computational owner modules per export, request their exact public declarations, include each full dependency closure and canonical primitive roots, and check groups in parallel with explicit process RAM reservations.
Record one source/toolchain pin, root list, canonical declaration-content hashes and every overlapping definition/proof body. Root names or olean filenames are insufficient.
H3 groups currently repeat a complete case catalog: one export per row would repeat it 1,170 times.
Grouping 64 rows gives about four row-group exports per case, twenty case-catalog parses overall; grouping 16 gives about seventy-five.
Only a representation change removes the long per-group literal-reader cost.

With shifted data and 16–24 process reservations, a **diagnostic** certificate-shard sweep may plausibly take roughly 12–36 h for con-ron, 6–20 h for NanoDa, and 5–12 h for parallel Lean replay. These bands include duplicate closures but exclude unmeasured final-proof aggregation and do not constitute a release certificate.

Memory is reserved per process, because shard closures are duplicated:

| Checker | Initial full-machine reservation | Consequence / condition |
|---|---|---|
| con-ron | 16 processes × 24 GiB = 384 GiB; alternatively 24 × 16 GiB after group measurements | Largest completed prefix is 17.7 GiB, so it belongs in the 24 GiB class. Full row-group installed memory is unknown. |
| NanoDa | 24 × 16 GiB = 384 GiB | Single completed prefix uses 5.3 GiB; accumulation in a full row closure is unmeasured. |
| Lean shard replay | 16 × 24 GiB = 384 GiB, or 24 × 16 GiB for measured small groups | Give H2 an initial separate 36 GiB reservation; its fresh replay memory has not been measured here. |

These are **admission/cap plans**, not demonstrated full-group memory bounds. Reserve another 40–60 GiB for orchestration/OS; enforce a roughly 440 GiB aggregate limit on a future otherwise-idle machine. A capped group must be diagnosed and given a larger reservation with lower concurrency. Reducing the number of row roots does not shrink the current full case-catalog closure. The sharded time ranges above apply only after group caps pass; there is no finite unconditional acceptance bound.

For canonical overlap comparison, resolve export-local name/expression/universe IDs to qualified names and structural expression/level content. Hash declaration kind, level parameters, type, value/proof and safety; compare entire mutual inductive/constructor/recursor blocks. Preserve the exact source/toolchain pin and complete dependency inventory. A raw JSON hash or a declaration-name-only match cannot bind independently indexed exports.

Each accepted shard establishes its requested theorems and closure in the environment consumed.
A separately accepted **conditional assembly** together with accepted proofs of every explicit input proposition can mathematically establish the headline by external composition, provided all shared definitions and interfaces agree.
This is stronger than checking numerical shards alone. It still does not mean either binary accepted the actual headline's single exported dependency closure.
Today a shard containing the actual closed headline again contains all certificate proof bodies and is monolithic.
Replacing them by extra permitted axioms is not the stated three-axiom standard.

The installed Comparator accepts **one challenge export and one solution export**, not a shard manifest. Concatenation is invalid because name/expression indices are local.
A canonical merged export is monolithic again and its default Lean replay repeats all numerical proofs sequentially.
A formally justified import/composition protocol or parallel replay implementation would be an additional deliverable, not a flag already available in these binaries.

## 3. Recommendations, ranked by engineering cost

1. **Put the large operand first in computed Nat products, and transport the original statement explicitly.** On the standalone example above, direct small-first computation reaches 4 GiB without acceptance; the same statement proved using Nat.mul_comm and the large-first computation ACCEPTS at 0.043 GiB. The H3 lane's real multiplication and complete-row controls corroborate the improvement. For a packed checker, introduce an internal large-first variant; prove its weighted-list sum equals the old sum by list induction and Nat.mul_comm, lift that equality through the Boolean checker, and generate the old checked statement using an equality chain ending in decide +kernel on the new variant. Retain all bounds and the old public statement. The generic equivalence is still proof work for the lane; Fit.SwapSound is not yet proved.
2. **Use the native, balanced decimal serializer immediately.** Build it with release/build-fast-exporter.py in a new scratch directory and pass its executable to --exporter. It preserves all tested export bytes; it fixes the minimal literal export from >120 s to 2.01 s. It does not fix readers or serial replay by itself.
3. **Pilot balanced add/shift encoding for H3 data, then rebuild the attachment if its complete consumers pass.** The successful 64-plane prototypes are scratch/lib/RELFEAS/ShiftHex.lean and ShiftHex64K.lean; drivers shift_limbs.py, shift_64k_native.py and shift_64k_equiv_check.py. Retain the original hex syntax and values; change only the untrusted term elaborator so its emitted Nat expression has bounded leaves (pilot 65,536 bits; 8,192 bits is the Comparator-tested alternative). All 64 original data equalities pass Lean, con-ron and NanoDa; the converted field checks and Comparator pass. This establishes the small real-data improvement, not a full-release guarantee. Do not substitute multiplication by a large power: that measured form is much slower in con-ron.
4. **Resolve the sequential replay requirement before promising a short release.** With current binaries, either reserve a multi-day strict release window or develop/review a parallel export replayer using the same Lean kernel and a sound dependency/merge protocol. It must handle acyclicity, mutual inductive blocks, generated recursors, quotient post-checks, primitive definitions and exact common-environment binding. This is not achieved by launching today's Comparator over certificate shards.
5. **If the author accepts a different release procedure**, parallel module/kernel replays plus hash-bound conditional-assembly/shard composition and monolithic independent checks could avoid the serial replay. That is an author decision under the guide's “Any narrowing of verification is the author's decision,” not an automatic fallback. The delivered runner does not implement or claim that relaxation.
6. **Higher-cost proof-format work:** checkpoint and share H1 tensor-contraction computations using proved composition lemmas and literal intermediate results, so replay verifies each repeated subcomputation once. A pilot must measure the actual large constructor rows before undertaking a production rewrite. No such speedup is claimed here. Merely choosing fewer/larger modules, or changing decide to rfl, has no evidence of the required order-of-magnitude improvement.

### Concurrent lane evidence and next proof work

While this study ran, the read-only CERT_H3 lane completed all 5,035 original modules (19.455 CPU-h) and developed additional prototypes. Its independently checkable receipts are copied, with hashes, to cross-lane-evidence/; the source lane remains untouched. These are **attributed lane measurements**, not reruns by REL_FEAS. They do not replace the original sample table or change the current-production extrapolation.

| New H3 prototype | Lean build / GiB | Fresh Lean replay / GiB | con-ron / GiB | NanoDa / GiB |
|---|---:|---:|---:|---:|
| P0106 bitsets + sparse blocked endpoints | 17.92 / 2.470 | 15.29 / 1.819 | 50.64 / 3.545 ACCEPT | 22.32 / 1.388 ACCEPT |
| 20 complete real rows, uint32 storage, 8K-bit leaves | 0.81 / 0.598 | 6.54 / 0.412 | 16.99 / 0.445 ACCEPT | 26.16 / 0.230 ACCEPT |

Unlike this study's centre-lane encoding control, the twenty-row pilot includes cap domination, range/free/pin checks and endpoint extraction. It uses a changed checker and tighter coefficient ceilings, so its new numerical proofs **do not prove the existing production statements** without refinement lemmas.
Exact open obligations include Fit.ParitySound, Fit.SwapSound, Fit.GuardedSound, Fit.SplitSound, Fit.Ceiling32Sound, Fit.StrengtheningSound, Fit.RectangleSound, Fit.EndpointBlockSound and the routing/view refinement to Defs.
The lane has not delivered a complete production rerun or an end-to-end semantic bridge. Its new 8–11x whole-H3 CPU saving is a planning range, not an accepted complete-case speedup.

A particularly cheap next change is **large operand first in Nat.mul**. The lane's minimal real-data pair is
97632666219444 * Fit.Bits.p = expected versus Fit.Bits.p * 97632666219444 = expected.
The first exceeds 6 GiB after 16.4 s; the second ACCEPTS in 11.27 s / 0.12 GiB. Sources are Fit/MulLarge.lean and Fit/MulLargeSwap.lean; receipts are copied above. This isolates an operand-order normalization hazard independently of the full-catalog frontend timeout.
Prove the checker-preservation equality using Nat.mul_comm and list-fold congruence, then rewrite the soundness bridge; never drop no-carry/bound checks. Apply this to the executable guarded checker in a new staging copy, not a running production lane.

The H3 prototypes also natively compile the untrusted literal elaborator: the original real 64-plane data group loads in 2.13 s / 0.89 GiB. This removes source elaboration overhead while emitting kernel-visible terms. The delivered source-only release build does not claim that native-elaborator speedup; integrating native compilation facets would require a measured build extension.

[H1_FIT](/home/ubuntu/aklt/reports/H1_FIT/report.md) now identifies 41 unique local tensor specifications (15,040 cells) replacing 14,385,472 repeated local cells; sharing their already proved checks could remove much of the 15.30 h local stage. Compiled local identities improve a hard constructor row about 2x, but no full new constructor speedup is established. That supports shared local-table/transfer lemmas before speculative whole-operator packing. Even removing all H3 time does not remove the current H1 sequential replay bottleneck.

### Exact H3 lane instructions

After production has stopped, work in a new lane-owned staging copy and regenerate compacted source data from its pinned archive.
In CertData/H3/Kernel/Literal.lean keep decodeHexBalanced, the syntax, the validation of hex digits and the public elaborator name.
Replace only its final mkNatLit result by the following recursive **Expr construction** on the decoded Nat n, with B = 65536 for the smaller-footprint pilot or B = 8192 for the Comparator-tested variant (use the tested ShiftHex implementation, not a string containing thousands of overloaded arithmetic terms):

    bits := n.log2 + 1
    if bits <= B: emit mkNatLit n
    else:
      cut := B * max 1 (((bits + B-1) / B) / 2)
      low := n & (2^cut - 1)
      high := n >> cut
      emit Nat.add (encode low) (Nat.shiftLeft (encode high) (mkNatLit cut))

Use the same bounded recursion fuel 64 as the prototype. It covers these data sizes; the arithmetic preservation lemma is independent of any particular cut or fuel.
The split must make progress when B < bits <= 2*B; the max 1 is essential.
Emit Nat.add/Nat.shiftLeft applications directly with typed Nat literals.
No array-backed checker, untrusted proof, new mathematical axiom or native_decide is introduced.

Keep checker definitions, theorem statements, row/prefix sizes and generators unchanged for the first experiment.
Rebuild one real plane-data owner and its original row/prefix consumers from source, then the H3 attachment. Fingerprints must invalidate all affected .oleans; do not reuse old numeric receipts.
Run the independent checkers and Comparator on that fresh source-built sample before authorizing the full rerun.
Keep equivalence exports as validation artifacts: importing the old literal equalities into the final proof closure also retains the old literals.
H1's ordinary integer matrix coefficients are much smaller; keep its current source representation unless a separate measurement shows a benefit.

The full-catalog re-encoding experiment in this report modifies only copied/exported certificate data definitions. It is a prototype for the source change above, not a claim that its export is byte-identical or that the original source build used the new encoding.
Any definition actually compared in the frozen Challenge must retain the same representation on both sides, or be refrozen under author control.

## 4. Release runner and tested scope

The runner creates a new repository, fetches the exact commit, checks dependency Git pins and uses the prebuilt cache read-only.
It never builds Mathlib. It compiles the project/attachment source DAG with the project's flags and normal kernel checking, one Lean thread per process.
This produces library .oleans without native C/IR facets or Lake incremental traces; all active attached sources are checked.
Certificate libraries are separately registered in the isolated clone. Source-only attachments must include complete inventories and matching SHA256s.

The scan masks comments/strings, rejects forbidden constructs and records unlimited-heartbeat exceptions.
It explicitly registers the inherited AKLT.Cert.H2.Check computation; the receipt/scan records that exception rather than silently hiding it.
The actual headline theorem must pass #print axioms, direct comparison of its declared type with AKLT.Challenge.MainStatementV2, and an explicit-argument check (@theorem). Real mode rejects a changed --statement. This prevents expected-type elaboration from silently supplying implicit proof arguments.
The exported closure must contain a theorem at the requested name, only the permitted axioms, safe definitions and matching Lean metadata.
con-ron runs --verified --progress=1; NanoDa rejects nonstandard axioms.
The sandboxed Comparator runs Lean plus con-ron and NanoDa over the same hashed export and an independently supplied frozen challenge.
The guide's extra --paranoid checkers are not requested here.

--jobs, --checker-jobs, phase timeouts, per-process/total memory and disk budgets are parameters.
The current Comparator fixes its own NanoDa threads at four; the documented flag controls standalone NanoDa and both con-ron invocations.
Defaults reserve at most 56 GiB, with one Lean worker capped at 36 GiB to accommodate H2.Check's documented 29.1 GiB peak; invalid reservations fail before work. Receipts record all job, memory, disk and timeout settings. Every subprocess tree is RSS-monitored with an address-space backstop.
Failures, missing markers, timeouts, incomplete attachments and mismatched hashes produce FAILED receipts, never pass.
Only a real closed headline plus complete attachments/frozen challenge can produce RELEASE_PASS.
Stand-ins always produce STAND_IN_PASS with explicit self-comparison scope.

| Test | Result / evidence |
|---|---|
| Clean assembly implication AKLT.Blueprint.Top.mainV2_of_partsV2 | STAND_IN_PASS: release-test-top-delivered/receipt.json; assembly pipeline passed before the final real-mode type-guard addition. Clean source build, scan, audit, rebuilt fast exporter, both checkers and sandboxed three-kernel Comparator. con-ron 23.59 s, NanoDa 5.85 s, Comparator 59.19 s. Earlier stock-exporter run also passed. Stand-in execution is unchanged by the final real-mode guard; the final attachment run and positive/negative guard test validate that addition. |
| New opt-in certificate fixture, final runner | STAND_IN_PASS: release-test-guard-final/receipt.json; final runner SHA matches delivery; attachment inventory, source/artifact hashes and library registration. con-ron 6.05 s, NanoDa 0.10 s, three-kernel Comparator 6.35 s. |
| Tampered attachment hash | FAILED before build: release-test-bad-hash/receipt.json. |
| H2 clean stand-in attempt | FAILED at AKLT.Cert.H2.Check, 16 GiB cap after 81.15 s. Not counted as a passed clean build. The existing [CERT_H2 report](/home/ubuntu/aklt/reports/CERT_H2/report.md) records successful source build at 237 s / 29.1 GiB; the runner now defaults to 36 GiB for one Lean worker. |
| Scanner, strict type guard and syntax | Nested-comment/string masking assertions, Python compilation and bash -n pass. AuditGuard accepts an exactly typed closed fixture and rejects an implicit-Witness theorem even though ordinary expected-type elaboration can supply its instance. Test receipt matches the delivered runner SHA. |
| Full headline/final attachment | Not available; deliberately not simulated as an unconditional proof. |

The independently frozen challenge export, expected digest and provenance commit are explicit inputs. The author must supply/review that artifact; a solution self-comparison cannot replace the statement audit.
The attachment format and concrete commands are in release/README.md. Its full-release template explicitly raises disk/export/checker budgets and timeouts; it was not executed under this study's resource limits.

### Exported declarations and axiom audit

Original sample statement families:
Rows.checked : result = true, with result = planeBatch G T .B .north start count.
Prefix/Raw.checked : result = expected, with the complete exact expected record in the copied source.
Representatives.checked : representativeBatch G 0 64 = true.
H1 Gram: checkRows lRows (d*scale^2) g rowStart mChunk lChunk = true.
H1 packed: packedSectorRowCheck sectorNetwork outgoing width thresholdP thresholdQ row packedIndices savedRow = true.
Every exact qualified name is listed in its roots.txt/result.json and every complete statement in the copied source under scratch/lib; the large records are not abbreviated in the artifact.

The successful clean stand-in's exact type and audit are:

    AKLT.Blueprint.Top.mainV2_of_partsV2 :
      AKLT.Blueprint.Top.InputsStatementV2 →
      AKLT.Blueprint.Top.RecStatement →
      AKLT.Blueprint.Top.CutMOSStatement →
      AKLT.Blueprint.Top.MainWStatement →
      AKLT.Blueprint.Top.TorusKernelStatement →
      AKLT.Challenge.MainStatementV2
    'AKLT.Blueprint.Top.mainV2_of_partsV2' depends on axioms:
      [propext, Classical.choice, Quot.sound]

This is a proved assembly implication, with all inputs explicit. It is not a closed headline proof.
The opt-in fixture is CertData.H3.ReleaseSmoke.checked : (37 : Nat) + 5 = 42;
#print axioms reports that it does not depend on any axioms.

The new auxiliary closed statements are the MulOrder/explicit commutation examples, combine_eq and rebuild_eq above, the 64 exact ShiftEquiv.pN_same data equalities, and simple benchmark facts. No new AKLT mathematical leaf or unconditional headline is claimed.
Original H3/Gram checks generally print []; H1 packed checks and the generic encoding model print subsets of, or all of:
[propext, Classical.choice, Quot.sound].
All exact output is in lean.log/build logs; the new data equalities were also accepted by both independent checkers.
NanoDa's “Unable to print axioms” pretty-printer warning occurs with successful typechecking; acceptance requires exit zero and “no typechecker errors”.

## Resource accounting and remaining uncertainty

Production lanes remained read-only. Timed Lean-executable overlap reconstructs to at most four (lean-concurrency-audit.json).
Checker runs are capped; long runs reserve two 20 GiB processes and the converted stage 15 GiB, with small tools scheduled around them.
No claim of a continuously measured aggregate RSS trace is made; per-process peaks/overlaps and limits are retained.
Disk was kept below 30 GB across the worktree/report by removing the worktree's generated C/IR cache, incomplete exports and redundant byte-comparison copies (disk-cleanup.json).
Lean source and .olean files were retained. Final owned disk use is about 20.8 GB across this worktree and report. Existing production artifacts were copied, never writable-linked to producers.

The full-release forecasts do not validate 32/48-worker scaling, total installed-environment memory or final aggregation. The exact Q017/Q037/Q038 historical failures and their repaired-source pins are now identified above.
The exact unconditional final theorem name and frozen challenge remain author inputs.
The source-encoding change is demonstrated on actual data but still requires a clean production-lane rerun and source/statement freeze coordination.

## ORCH-SUMMARY
- Delivered strict release/run-release.sh, implementation, attachment schema and native fast serializer builder.
- Clean top-level assembly and opt-in certificate fixture pass all three kernels through the sandboxed Comparator.
- H1 sampled Gram/packed checks and H3 sampled raw/representative/prefix checks ACCEPT in con-ron and NanoDa.
'''
s+=f'- Original full-catalog row group: con-ron {verdict(longc)}, NanoDa {verdict(longn)}; see long-run receipts.\n'
s+='''- Minimal small-first Nat.mul hits 4 GiB; an explicit Nat.mul_comm proof of the same statement ACCEPTS at 43 MiB.\n- Stock huge Nat decimal export/parse is a measured bottleneck; minimal reflexive example and exact logs delivered.
- 8K-limb shift encoding of 64 planes passes both kernels, all data equalities and Comparator; 64K passes both kernels/equalities only.
- Full nested re-encoding export TIMEOUT at 40 min; no complete converted row-group checker acceptance.
- Mandatory monolithic Lean replay in the installed Comparator is sequential; plan roughly 100 hours of numerical replay, with a 90–140 h planning band.
- Shards can certify components/conditional assembly but do not satisfy the current single-export Comparator standard.
- Decide: multi-day strict release, reviewed parallel replayer, or an author-approved changed composition procedure.
- Pilot the exact H3 shift encoder and its complete consumers in a new source staging build; no generators or production worktrees were edited here.
- Final AKLT.Challenge.MainStatementV2 proof, complete source attachment, frozen challenge and final full-closure acceptance remain external gates.
- H2.Check exceeded the tested 16 GiB cap; documented 29.1 GiB success informs the new 36 GiB / one-worker default.
- No full release, full-machine memory bound or sub-12-hour end-to-end guarantee is claimed.
'''
(R/'report.md').write_text(s)
print('report updated',len(s),'bytes; original rows',verdict(longc),verdict(longn))
