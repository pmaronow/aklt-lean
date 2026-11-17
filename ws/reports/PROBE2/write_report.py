from pathlib import Path
import datetime
import json
import re

R = Path('/home/ubuntu/aklt/reports/PROBE2')
rows = [json.loads(s) for s in (R/'measurements.jsonl').read_text().splitlines()]
by = {r['id']: r for r in rows}
audit = json.loads((R/'audit.json').read_text())
groups = json.loads((R/'parallel_groups.json').read_text())
geometry = json.loads((R/'geometry_counts.json').read_text())

def rss(name):
    return by[name]['rss_kib']/1048576

def prof(name):
    s = (R/'logs'/f'{name}.log').read_text()
    m = re.search(r'^\ttype checking ([\d.]+)(ms|s)$', s, re.M)
    return float(m[1])/(1000 if m[2]=='ms' else 1)

def elapsed(r):
    parts = (r.get('time_wall') or str(r['wall_s'])).split(':')
    total = 0.0
    for p in parts:
        total = 60*total + float(p)
    return total

def effective_timeout(r):
    s = (R/'logs'/f"{r['id']}.log").read_text()
    m = re.search(r'INNER_WALL_SECONDS=(\d+)', s)
    return int(m[1]) if m else r['timeout_s']

def ax(r):
    if not r['axioms']:
        return 'N/A' if r['exit']==0 else 'not printed'
    s = ' '.join(r['axioms'])
    if 'does not depend on any axioms' in s:
        return '∅'
    names = re.search(r'depends on axioms: \[(.*?)\]',s)[1].split(', ')
    return ','.join({'propext':'P','Classical.choice':'C','Quot.sound':'Q'}.get(n,n) for n in names)

def command(r):
    c=r['command']
    flags=[]
    if '--profile' in c:flags.append('p')
    if 'leanchecker --fresh' in c:flags.append('c')
    if 'leanchecker-paranoid --fresh' in c:flags.append('cp')
    if not re.search(r' lean .* -o ',c) and not ('c' in flags or 'cp' in flags):flags.append('n')
    return f"K {r['name']} {r['limit_gib']} {effective_timeout(r)}" + (' '+','.join(flags) if flags else '')

def rank(r):
    n=r['name']
    if n=='Baseline':return 0
    if n.startswith(('BellmanGuard','FastBellmanGuard')):return 1
    if n.startswith(('Bellman9Guard','FastBellman9Guard')):return 2
    if n.startswith(('Packed1','Packed16','Packed128','FastPacked')) and n!='PackedLiteralSyntax':return 3
    if n=='H2Small':return 4
    if n in ['H1Gram','FastH1Gram','H1RowData','H1RowCheck']:return 5
    if n.startswith('PrefixLeaves'):return 6
    if n.startswith('Nat'):return 7
    if n.startswith('Int') and n!='IntRowsSyntax':return 8
    if n.startswith('List'):return 9
    if 'Literal' in n and n!='PackedLiteralSyntax':return 10
    if n.startswith('Parallel'):return 11
    return 12

m10row=(prof('FastBellmanGuard4096')-prof('FastBellmanGuard1024'))/3072
m9row=(prof('FastBellman9Guard4096')-prof('FastBellman9Guard1024'))/3072
packedstep=(prof('FastPacked4096')-prof('FastPacked1024'))/3072
packedmem=(by['FastPacked4096']['rss_kib']-by['FastPacked1024']['rss_kib'])/3072/1024
m10mem=(by['FastBellmanGuard4096']['rss_kib']-by['FastBellmanGuard1024']['rss_kib'])/3072/1024
m9mem=(by['FastBellman9Guard4096']['rss_kib']-by['FastBellman9Guard1024']['rss_kib'])/3072/1024
perproduct=prof('H1RowCheckFixed')/757966
fullproducts=2*60154555-2184033
decode_s_per_mb=(by['FastLiteral50MB']['wall_s']-by['FastLiteral10MB']['wall_s'])/40
nodecost=prof('PrefixLeaves12Geometry48')/139984
seq=groups[0]['wall_s']; concurrent=groups[1]['wall_s']
concurrent_rows=[r for r in rows if r['id'].endswith('Concurrent')]
success_audits=sum(bool(r['axioms']) and r['exit']==0 for r in rows)

text=f'''STATUS: COMPLETE

The small H2 route is a **go**. The H1 Gram/residual route is a **go for the positivity stage**, with improved data elaboration and row chunks; a full H1 schedule still depends on measuring its constructor. The packed stationary H3′ route at **m=10, R=70 is a conditional go**. Prefer it to m=9, R=80: the latter saves local certificate work but its exact prefix is much more expensive. A monolithic periodic replay and monolithic long-prefix reductions are **no-go** designs on this budget.

This is a completed timing study, including intentionally resource-censored measurements. It is not a completed AKLT certificate or its soundness proof. The generic guard checks do not implement the actual Bellman graph, and the H1 matrix is stored benchmark data. In particular, the proposed stationary certificates establish contraction for the modified type-dependent kernel described in COMPFEAS; they do not establish the paper's original fixed-coefficient numerical H3′ bound.

**Environment and method.** Measured 2026-11-16 UTC on Intel Xeon Platinum 8488C, 64 visible logical CPUs, Linux x86-64. Lean **4.35.0-rc2**, commit **11acb17ec6b07a8f9e9173e6845197929540936b**; Mathlib **065356127b1dc0016f66b7283ce0ce2c4055aa55**. The existing Mathlib build was imported; neither Mathlib nor dependencies were built or updated. The project configuration, manifest and toolchain were unchanged. All writes are in `AKLT/Probe2/` or this report directory. No sub-agents were launched.

Each measurement used a fresh process, `PATH="$HOME/.elan/bin:$PATH"`, `LEAN_NUM_THREADS=1`, `-DElab.async=false`, structural recursion and `decide +kernel`. The supplied probes set `maxHeartbeats=0` and `maxRecDepth=1000000`; Baseline is trivial. Every numerical proof was checked normally and successful `.olean` artifacts were retained beside their sources. There is no `#eval` timing substituted for a kernel proof. The source audit found no `native_decide`, `implemented_by`, `extern`, `unsafe`, axiom, sorry, or opaque declaration in any probe Lean file. Existing core-library runtime implementations are not additions to this checker.

`/usr/bin/time -v` encloses Lake. The wall timeout is **inside** `lake env`, so Lake survives to reap Lean and report child counters. `limit_exec.py` disables core dumps and applies `RLIMIT_AS`; table caps are GiB of **virtual address space**, not RSS. Exit 124 means timeout; exits 1/134 with allocation errors mean memory-censored computation. Neither establishes falsity of the theorem. All printed `sorryAx` belongs to rejected source-error invocations. A nonzero module is never counted as a certificate, even when it prints an axiom-free trivial theorem.

There are **{len(rows)} timed invocations**, **{audit['pass_count']} successful invocations**, and **{success_audits} successful theorem audits**. Every successful theorem audit is within `{{propext, Classical.choice, Quot.sound}}`. The largest single RSS was {rss('PrefixLeaves14Geometry48'):.2f} GiB. At most **{audit['max_simultaneous_timed_invocations']} timed Lean/checker invocations overlapped**. A conservative sum of each overlapping invocation's separately observed peak RSS is **{audit['overlap_rss_peak_upper_bound_gib']:.2f} GiB**, below 128 GiB with substantial headroom for Lake/timeout/Python launchers; this is an overlap upper bound, not a sampled aggregate peak. The six concurrent guard jobs sum to {sum(r['rss_kib'] for r in concurrent_rows)/1048576:.2f} GiB. Other users share the machine; measurements are single observations, without CPU affinity, generally with warm filesystem caches. Import baseline here is {elapsed(by['Baseline']):.2f} s / {rss('Baseline'):.2f} GiB, so use this study's baseline rather than subtracting PROBE1's smaller import footprint.

Two optional independent `leanchecker --fresh` attempts, on a guard and a bitwise microprobe importing Mathlib, timed out after 120 s. They are explicitly listed below. No successful independent whole-import-closure audit is claimed. The successful results here are normal Lean kernel checks and their printed axiom audits; a production Palomar build still needs its independent checking procedure.

Full commands, user/sys time, exact RSS in KiB, exit codes, source/output sizes and printed audits are in [measurements.jsonl](measurements.jsonl), with original GNU time outputs and complete diagnostics under [logs/](logs/). Provenance is in [source_changes.md](source_changes.md), [source_changes.json](source_changes.json) and [source_inventory.json](source_inventory.json). [audit.json](audit.json) records the resource and trust audit. Original files are retained in `/home/ubuntu/aklt/compfeas/probes/`.

**What changed to make the uncompiled probes usable.** The four guard files used root identifier `guard`, which Mathlib already defines. It was renamed to `guardMask`; the initial two failed guard runs and data-only diagnostic are retained. Baseline gained a trivial kernel theorem and axiom print. Other supplied files are unchanged. No numerical constant, matrix entry, factor entry, window enumeration, or arithmetic predicate was corrected to make a false check pass.

Large direct hexadecimal tokens and large overloaded Int lists make source elaboration a substantial bottleneck. New `Fast*` variants emit the **same ordinary literals/constructors** using untrusted term elaborators. `PackedLiteralSyntax` uses balanced decoding and emits an `Expr.lit` Nat; `IntRowsSyntax` emits ordinary List/Int constructors. These elaborators do not prove a proposition, install a kernel reduction rule, or trust a parse/decompression result as evidence. The kernel checks the emitted data against the checker. External Python comparison confirmed every packed digit sequence and every H1 matrix/factor entry matches the original. The syntax-helper development failures are also retained in the table and documented in the change log.

**Packed arithmetic and cache growth.** The real guard plane sizes are 1,590,480 bits (19,881 lanes, 80-bit fields) and 2,177,364 bits (25,921 lanes, 84-bit fields). After the name repair, ordinary BellmanGuard1/16 passed in {elapsed(by['BellmanGuard1Fixed']):.2f}/{elapsed(by['BellmanGuard16Fixed']):.2f} s; almost all time was literal elaboration. Ordinary Bellman9Guard1 passed in {elapsed(by['Bellman9Guard1']):.2f} s, while its 16-row raw-source attempt was stopped at 120 s. The Fast versions of **both** sizes and **both** counts passed in 4.6–5.3 s total. Once equivalent Fast checks passed, duplicate large raw-source loads were capped at 120 s; their censored durations are not completed checker runtimes. The raw-source timeout is not evidence of failed guarded arithmetic.

The earlier concern that bitwise operations might only be fast in compiled code was resolved empirically: normal `decide +kernel` guard, routing, and large bitwise checks complete quickly. The stdlib's `extern` attributes alone do not predict kernel behavior. Successful larger kernel reductions, rather than native timings, support the following rates. Profiling is Lean's cumulative **type-checking** time, not total wall time:

| Probe | Kernel type checking | Total wall s | Peak RSS GiB |
|---|---:|---:|---:|
'''
for n in ['FastBellmanGuard1','FastBellmanGuard16','FastBellmanGuard128','FastBellmanGuard1024','FastBellmanGuard4096','FastBellman9Guard1','FastBellman9Guard16','FastBellman9Guard1024','FastBellman9Guard4096','FastPacked1','FastPacked16','FastPacked128','FastPacked1024','FastPacked4096']:
    text+=f"| {n} | {prof(n):.6g} s | {elapsed(by[n]):.2f} | {rss(n):.3f} |\n"
text+=f'''
Using the 1024→4096 increments gives **{1000*m10row:.3f} ms/guard row** for m=10 and **{1000*m9row:.3f} ms/guard row** for m=9. Each generic row has two weighted planes and one easy successful comparison; this is not the cost of an actual row with all special masks and boundary rules. The corresponding retained RSS slopes are about **{m10mem:.3f} / {m9mem:.3f} MiB per row**.

Packed1/16/128 at the supplied 200,000-bit plane size passed in {elapsed(by['Packed1']):.2f}/{elapsed(by['Packed16']):.2f}/{elapsed(by['Packed128']):.2f} s, at {rss('Packed1'):.3f}/{rss('Packed16'):.3f}/{rss('Packed128'):.3f} GiB. That small range is dominated by literal loading. The longer Fast runs resolve the slope: **{1000*packedstep:.3f} ms per packed step** and **{packedmem:.3f} MiB retained per step**, approximately linear through 4096. Structural tail recursion does not release earlier reduction data within one kernel check. A long periodic replay therefore needs independently checked checkpoints/chunks; it is not approved as one reduction. The probe is one fixed-point east-routing average, not a full memory-walk transition.

Six independent 1024-row guard modules took **{seq:.2f} s sequentially** and **{concurrent:.2f} s concurrently**, a {seq/concurrent:.2f}× speedup on this small build. All twelve invocations passed, with `propext` only. This supports scheduling six independent small modules; it does not establish scaling for large H1 blocks, multi-GB imports or weighted prefixes. See [parallel_groups.json](parallel_groups.json).

**H2.** The complete supplied small test passed twice: {elapsed(by['H2SmallEarly']):.2f} s / {rss('H2SmallEarly'):.2f} GiB and {elapsed(by['H2Small']):.2f} s / {rss('H2Small'):.2f} GiB, with P,C,Q. It generates all length-six bond trails in Lean, checks the count **916**, then every raw window inequality, including positive witness lookup and true revisit weight **1/5**. Its 2,628 weighted edges are not supplied as a trusted transition matrix. This confirms the proposed computational core. Connecting the Boolean fact to domination and the H2 hypothesis remains mathematical work. It proves the weaker contracting H2 option, not the paper's optional numerical rate 0.98075.

**H1.** The original overloaded list source timed out at 600 s before finishing elaboration; a later repeat was capped at 120 s. The same 131×131 matrix and triangular factor emitted as constructors passed in **{elapsed(by['FastH1Gram']):.2f} s / {rss('FastH1Gram'):.2f} GiB**, with P only. Splitting its data into named row definitions built [H1RowData](../../wt/PROBE2/AKLT/Probe2/H1RowData.lean) in **{elapsed(by['H1RowDataFixed']):.2f} s / {rss('H1RowDataFixed'):.2f} GiB**; its separate [residual check](../../wt/PROBE2/AKLT/Probe2/H1RowCheck.lean) passed in **{elapsed(by['H1RowCheckFixed']):.2f} s / {rss('H1RowCheckFixed'):.2f} GiB**, of which about {prof('H1RowCheckFixed'):.0f} s was kernel type checking. Data and checker oleans are {by['H1RowDataFixed']['olean_bytes']:,} and {by['H1RowCheckFixed']['olean_bytes']:,} B. Row definitions solve the source/compiler problem; this full-block theorem still retains about 24 GiB. Arithmetic row sharding is a separate, recommended change.

This checker forms the residual and verifies strict row diagonal dominance. It does not regenerate the matrix from an H1 pattern, establish symmetry from that constructor, prove shape/completeness, or supply the Gram/DD quadratic-form soundness theorem. Those obligations cannot be replaced by the stored matrix's acceptance.

**Prefixes.** The table's successful equalities certify 1,466 / 11,482 / 89,150 leaves at lengths 8 / 10 / 12. Length 12 required a 48 GiB address cap and passed at **{elapsed(by['PrefixLeaves12Geometry48']):.2f} s / {rss('PrefixLeaves12Geometry48'):.2f} GiB**. It failed at 16, 24 and 32 GiB caps. Length 14 failed at every tested cap, including **{elapsed(by['PrefixLeaves14Geometry48']):.2f} s / {rss('PrefixLeaves14Geometry48'):.2f} GiB** under the 48 GiB cap. These failures do not certify the proposed 688,590 count or refute it.

An external traversal of the exact supplied geometry counts 2,304 / 18,024 / 139,984 / 1,081,424 recursive calls and reproduces the four expected leaf counts; these are **untrusted counting inputs to extrapolation**, not extra Lean results. See [geometry_counts.json](geometry_counts.json). No weights, phase-state transitions, endpoint potential lookup, or comparison of final weighted row bounds are included in the Lean geometry probes.

**Literal-size experiment.** MB means 10^6 binary bytes here; source hex text is twice that size, plus a small header. Each module contains one Nat of exactly the stated binary width, and a kernel theorem forces its reduction modulo 65536. The repeated digit pattern is deliberately deterministic; the `.olean` stores the entire Nat, not a compressed description. This experiment measures literal representation, not validity of any AKLT witness.

| Binary payload | Plain `0x` outcome | Balanced elaborator wall / RSS | `.lean` bytes (balanced) | `.olean` bytes | Import + kernel use wall / RSS |
|---|---|---|---:|---:|---|
'''
for mb in [1,10,50]:
    plain=by[f'Literal{mb}MB']; fast=by[f'FastLiteral{mb}MB']; imp=by[f'ImportLiteral{mb}MB']
    text+=f"| {mb} MB | timeout {elapsed(plain):.2f} s | {elapsed(fast):.2f} s / {fast['rss_kib']/1048576:.2f} GiB | {fast['source_bytes']:,} | {fast['olean_bytes']:,} | {elapsed(imp):.2f} s / {imp['rss_kib']/1048576:.2f} GiB |\n"
text+=f'''
All six successful literal/import theorems are axiom-free. The 10/50 MB plain-token runs had 120 s adaptive limits; the 1 MB run had 600 s. These are censored times, not completed parse times. Installed `Init/Meta/Defs.lean` decodes a hex token by the growing recurrence `val := 16*val+d`, explaining why enormous individual tokens are a bad source representation. Four ~199 KB plane literals already cost minutes in the ordinary guard files. The balanced elaborator emits exactly the same literal using small leaves and balanced joins.

At 50 MB, profiling gives about 75.8 s of elaborator interpretation, 0.301 s parsing, 0.079 s kernel type checking and 0.041 s `.olean` serialization. The useful observed limit is therefore **at least 50 MB per emitted Nat/module**, not a maximum supported size. Direct-token loading is already a bottleneck below 1 MB; with balanced emission, source-to-literal elaboration dominates while 50 MB serialization/import remains practical. No 1.2 GB literal, multi-GB module, serializer size limit, or 4 GB format boundary was tested. Do not infer safety of such a module from the 50 MB success. The measured 10→50 MB slope is about {decode_s_per_mb:.2f} seconds per binary MB in this interpreted elaborator.

**EXTRAPOLATION — H3′ stationary m=10, R=70, five cases.** Assumptions: spatial lanes remain at the measured widths; a proved packing/no-carry/guard/routing implementation can check actual Bellman rows with small bounded numbers of whole-plane operations; regenerated automaton indices and exceptions are sound; potentials can be emitted as ordinary literals; independent chunks release reduction caches. None of those implementation/soundness lemmas is supplied by the generic probe.

There are 4×3,741×5 = **74,820 phase/window planes** and 226,140 weighted whole-plane terms. Scaling the generic two-term row rate by the term count gives only **{m10row*226140/2:.0f} s of generic arithmetic**. It is a model anchor, not a completed local certificate. Allowing 2–10× for actual routing, caps, guards and centre/target/boundary exceptions suggests minutes to tens of minutes of local kernel arithmetic, conditional on that implementation. Scalar checking of the 4.50 billion weighted products is not justified by this packed rate.

The uint32 payload is **1,189,997,136 B/case**. Widening every value to an 80-bit lane gives **2,974,992,840 B/case**, **14,874,964,200 B for five**, and about **29.75 GB of hex source** before headers/common masks. Corresponding literal olean payload is about 14.88 GB, based on the size experiment, not the compressed 2.60 GB input size. The current balanced decoder alone extrapolates to **{decode_s_per_mb*14874.9642/3600:.1f} CPU-hours** across five cases. This data-loading cost dominates the generic guard arithmetic. It can be improved by an untrusted exporter/elaborator; it cannot be omitted from a source-build forecast.

Use one plane per literal and **32–64 planes per data module** (about 6.4–12.7 MB binary), with shared masks and indexing definitions. At 64 planes this is about **1,170 data modules** across all five cases. Check **64–256 rows per kernel process/module** initially, importing only the necessary neighboring plane groups; their generic cache increment is about 0.09–0.34 GiB, before actual graph overhead. Do not repeat the whole certificate in each checker source. A per-case or final aggregator can retain many imported literals; only a 50 MB import was tested, so explicitly measure a multi-GB aggregate before committing to the final import graph. Hashes identify input artifacts but never replace their checked relation to the definitions.

The m=10 exact prefix has 708,097 reported nodes across five cases. Scaling from the successful B/north geometry gives about **{nodecost*708097/60:.0f} minutes geometry-only**, with additional 3,516,794 phase products and verified balanced endpoint lookup. A full 12-prefix monolith uses tens of GiB even before weights; split by a shallow, definition-generated frontier and check small subtrees in fresh modules. Prove that frontier enumeration and recombination exhaust the original tree. Supply and verify a compact endpoint table once; do not extract from a million-bit plane separately at every leaf.

With the present interpreted loader, grouped data/check modules, and an engineered weighted prefix, **10–30 CPU-hours** is a planning scenario for numerical checking of all five cases. It includes the roughly 6.4-hour loader anchor, process startup and substantial overhead beyond the generic rows; it is not a measured end-to-end runtime or a bound on proof-development time. Six-way execution can shorten independent parts, but I/O and final aggregation were not benchmarked at that scale. **Conditional go; prioritize this route.** Before exporting all data, prove the packing/guard soundness and time one complete actual Bellman row, then a real prefix chunk and its verified endpoint lookup.

**EXTRAPOLATION — m=9, R=80 alternative.** There are **22,560 planes**, 66,340 generic weighted terms, and 84-bit lanes. The corresponding two-term guard model gives **{m9row*66340/2:.0f} s**; local checking and data are smaller. The uint32 payload is **467,822,208 B/case**, widening to **1,228,033,296 B/case**, or **6,140,166,480 B** for five; hex source is about 12.28 GB. Current decoder cost extrapolates to **{decode_s_per_mb*6140.16648/3600:.1f} CPU-hours**. Grouping 32–64 planes means about 8.7–17.4 MB binary per data module, within the measured 50 MB range.

Its successful mathematical design requires **B prefix 18 and C prefix 16**, not the failing 14/14 design. COMPFEAS reports 161,516,061 prefix nodes and 801,223,835 phase products, some reaching 1,518 bits. At the length-12 geometry rate alone this is **{nodecost*161516061/3600:.0f} CPU-hours**, with longer histories likely adding cost. Length-14 B/north alone extrapolates to about **{prof('PrefixLeaves12Geometry48')*1081424/139984/60:.0f} minutes** and roughly **{rss('PrefixLeaves8Geometry16')+(rss('PrefixLeaves12Geometry48')-rss('PrefixLeaves8Geometry16'))*1081424/139984:.0f} GiB** under linear cache growth; its 48 GiB failure supports the need for sharding, not that precise projected peak. A partitioned weighted implementation could plausibly take **4–10 CPU-days**, conditional on balanced lookup and bounded chunks. That range is less reliable than the geometry anchor. **No-go as the preferred route under the present implementation; retain only if lower disk/data cost becomes decisive.** The mixed m=10-B/m=9-C option has 24,458,661 prefix nodes: approximately {nodecost*24458661/3600:.0f} CPU-hours geometry-only, so it also needs a measured prefix advantage to displace m=10 throughout.

**EXTRAPOLATION — H1 at 12,173 blocks.** The measured full residual performs **757,966** Int products. Its ~104 s kernel time is about **{perproduct*1e6:.0f} μs per product including traversal, sums and row checks**, not isolated multiplication latency. COMPFEAS counts **60,154,555 triangular** Gram products, plus 2,184,033 factor entries; the probe checks both halves, so the corresponding full-row count is **2×60,154,555−2,184,033 = {fullproducts:,}**, not 60 million. At the sample's effective rate this is about **{perproduct*fullproducts/3600:.1f} CPU-hours** for full Gram arithmetic, or an idealized **{perproduct*60154555/3600:.1f} hours** if a verified triangular checker avoids duplication. Small-block row/shape/DD overhead, including the 8,439 blocks needing no factor, makes straight per-product scaling optimistic.

One fresh process per block adds about **{elapsed(by['Baseline'])*12173/3600:.1f} CPU-hours** of this import baseline. Group small blocks, but keep separate kernel reductions and bounded row chunks for large blocks. A reasonable positivity-stage planning range is **5–20 CPU-hours**, assuming similar operand widths/density and streamed data; startup/data export can dominate if every tiny block is its own process. The largest reconstructed size 179, extrapolated cubically from 131, would take roughly {prof('H1RowCheckFixed')*(179/131)**3/60:.1f} minutes and potentially over 50 GiB in one reduction. That is unmeasured; use **8–16 row obligations per large-block chunk** as an initial target and tune measured peaks to ~8–12 GiB for parallel work. Row definitions alone do not achieve that cache target.

The sample does not time the definition-derived moment contraction, inversion, Pauli placement, sector transformation, or complete pattern coverage. COMPFEAS's sparse counts still include about 95 million positive tensor products and 1.596 billion Pauli placements; a favorable Gram check does not make those free. **Go for Gram/DD, no-go for a dense source-style constructor or a promised full-H1 runtime based on this probe.** Retain tens-to-hundreds of CPU-hours as an unvalidated sparse-constructor scenario until one real small/sample/largest constructor has been checked from patterns in Lean. Importing a claimed matrix would leave H1 unproved.

**EXTRAPOLATION — H2.** The small true-revisit test is already a completed finite check at ~18.5 s / 9.2 GiB. Keep it as one module initially, with the domination/enumeration soundness lemma separate; no numerical sharding is presently needed. Allow roughly a minute, rather than hours, for a normal numerical rebuild including minor wrapper overhead. This does not estimate mathematical proof development.

If the original extension-eight numerical rate is required, it was not run here. COMPFEAS reports 5,627,018 extension multiplications and 3,609,484 terminal leaves on 938 orbit rows. Scaling the small test's 12 s kernel time by 9,236,502/2,628 weighted/terminal operations gives ~12 CPU-hours before accounting for different geometry, deeper history and orbit lookup. A **10–50 CPU-hour** scenario is plausible with generated row chunks and proved symmetry/balanced lookup, but is weakly constrained and must not be advertised as a measured original-H2 result. **Go for small H2; original H2 is conditional and unnecessary unless its numerical target is required.**

**Calibration and representation.** Supplied and doubled Nat/Int loops all passed. Kernel timings below isolate computation better than total wall times near the import baseline; each loop contains several operations and cannot be read as an isolated GMP instruction rate.

| Family | Original iterations | Kernel s | Doubled kernel s |
|---|---:|---:|---:|
'''
for n,count in [('Nat64',10000),('Nat256',10000),('Nat4096',2000),('Nat16384',200),('Int64',10000),('Int4096',2000)]:
    text+=f"| {n} | {count:,} | {prof(n+'Profile'):.6g} | {prof(n+'DoubleProfile'):.6g} |\n"
text+=f'''
ListZip1000/4000 passed in {elapsed(by['ListZip1000']):.2f}/{elapsed(by['ListZip4000']):.2f} s, at {rss('ListZip1000'):.2f}/{rss('ListZip4000'):.2f} GiB. ListIndex1000 failed a 16 GiB address cap but passed at 24 GiB in **{elapsed(by['ListIndex1000']):.2f} s / {rss('ListIndex1000'):.2f} GiB**. ListIndex4000 failed even at the 24 GiB cap ({elapsed(by['ListIndex4000']):.2f} s / {rss('ListIndex4000'):.2f} GiB). Sequential row/plane traversal and proved balanced lookup are mandatory design choices here; repeatedly indexing a linear list is not a viable full-certificate representation.

**Complete measurement table.** Rows are grouped in the requested ranked order, with repetitions/diagnostics retained. `K NAME CAP SECONDS [flags]` denotes the following reproducible command template, from `/home/ubuntu/aklt/wt/PROBE2`; `p` adds `--profile`, `n` omits `-o`. For `c`, replace the Lean argument tail by the toolchain's `leanchecker --fresh AKLT.Probe2.NAME`. The table uses effective wall limits; historical exact outer/inner wrappers are in each `.time` file and JSONL command field. `PROBE2_IGNORE_INNER_LIMITS=1` disables the adaptive policy for standalone replay.

```sh
source /home/ubuntu/aklt/reports/PROBE2/K.sh
K FastPacked128 24 600 p
```

[K.sh](K.sh) expands every table command into `/usr/bin/time -v lake env timeout ... python3 limit_exec.py CAP lean -DElab.async=false ...`, sets PATH/LEAN_PATH/LEAN_NUM_THREADS, and disables the adaptive inner-limit policy so the table's effective limit is reproduced. The example above is directly runnable. Wall and RSS come from GNU time; RSS is displayed as GiB (KiB/1,048,576). Full integer KiB values are in the raw records. Axiom abbreviations: **∅** = prints no axioms, **P** = propext, **C** = Classical.choice, **Q** = Quot.sound. “not printed” is not an axiom-free result. N/A is a successful support/data module with no theorem audit. Failed historical source versions are documented in `source_changes.md`; replaying current corrected sources need not reproduce those errors.

| Measurement / full log | Command | Wall s | Max RSS GiB | Exit / outcome | Printed axioms |
|---|---|---:|---:|---|---|
'''
for r in sorted(rows,key=lambda r:(rank(r),r['timestamp'])):
    text+=f"| [{r['id']}](logs/{r['id']}.log) | `{command(r)}` | {elapsed(r):.2f} | {r['rss_kib']/1048576:.3f} | {r['exit']} / {r['outcome']} | {ax(r)} |\n"

(R/'report.md').write_text(text)
models=dict(m10_guard_s=m10row,m9_guard_s=m9row,packed_step_s=packedstep,
            packed_cache_mib_per_step=packedmem,m10_cache_mib_per_row=m10mem,
            m9_cache_mib_per_row=m9mem,loader_seconds_per_binary_mb=decode_s_per_mb,
            h1_s_per_full_product=perproduct,h1_full_products=fullproducts,
            prefix_geometry_s_per_node=nodecost)
(R/'models.json').write_text(json.dumps(models,indent=2)+'\n')
print(f'Wrote {len(text):,} characters, {len(rows)} measurement rows.')
