STATUS: COMPLETE

The small H2 route is a **go**. The H1 Gram/residual route is a **go for the positivity stage**, with improved data elaboration and row chunks; a full H1 schedule still depends on measuring its constructor. The packed stationary H3′ route at **m=10, R=70 is a conditional go**. Prefer it to m=9, R=80: the latter saves local certificate work but its exact prefix is much more expensive. A monolithic periodic replay and monolithic long-prefix reductions are **no-go** designs on this budget.

This is a completed timing study, including intentionally resource-censored measurements. It is not a completed AKLT certificate or its soundness proof. The generic guard checks do not implement the actual Bellman graph, and the H1 matrix is stored benchmark data. In particular, the proposed stationary certificates establish contraction for the modified type-dependent kernel described in COMPFEAS; they do not establish the paper's original fixed-coefficient numerical H3′ bound.

**Environment and method.** Measured 2026-11-16 UTC on Intel Xeon Platinum 8488C, 64 visible logical CPUs, Linux x86-64. Lean **4.35.0-rc2**, commit **11acb17ec6b07a8f9e9173e6845197929540936b**; Mathlib **065356127b1dc0016f66b7283ce0ce2c4055aa55**. The existing Mathlib build was imported; neither Mathlib nor dependencies were built or updated. The project configuration, manifest and toolchain were unchanged. All writes are in `AKLT/Probe2/` or this report directory. No sub-agents were launched.

Each measurement used a fresh process, `PATH="$HOME/.elan/bin:$PATH"`, `LEAN_NUM_THREADS=1`, `-DElab.async=false`, structural recursion and `decide +kernel`. The supplied probes set `maxHeartbeats=0` and `maxRecDepth=1000000`; Baseline is trivial. Every numerical proof was checked normally and successful `.olean` artifacts were retained beside their sources. There is no `#eval` timing substituted for a kernel proof. The source audit found no `native_decide`, `implemented_by`, `extern`, `unsafe`, axiom, sorry, or opaque declaration in any probe Lean file. Existing core-library runtime implementations are not additions to this checker.

`/usr/bin/time -v` encloses Lake. The wall timeout is **inside** `lake env`, so Lake survives to reap Lean and report child counters. `limit_exec.py` disables core dumps and applies `RLIMIT_AS`; table caps are GiB of **virtual address space**, not RSS. Exit 124 means timeout; exits 1/134 with allocation errors mean memory-censored computation. Neither establishes falsity of the theorem. All printed `sorryAx` belongs to rejected source-error invocations. A nonzero module is never counted as a certificate, even when it prints an axiom-free trivial theorem.

There are **113 timed invocations**, **87 successful invocations**, and **83 successful theorem audits**. Every successful theorem audit is within `{propext, Classical.choice, Quot.sound}`. The largest single RSS was 42.43 GiB. At most **7 timed Lean/checker invocations overlapped**. A conservative sum of each overlapping invocation's separately observed peak RSS is **100.29 GiB**, below 128 GiB with substantial headroom for Lake/timeout/Python launchers; this is an overlap upper bound, not a sampled aggregate peak. The six concurrent guard jobs sum to 48.23 GiB. Other users share the machine; measurements are single observations, without CPU affinity, generally with warm filesystem caches. Import baseline here is 3.39 s / 6.45 GiB, so use this study's baseline rather than subtracting PROBE1's smaller import footprint.

Two optional independent `leanchecker --fresh` attempts, on a guard and a bitwise microprobe importing Mathlib, timed out after 120 s. They are explicitly listed below. No successful independent whole-import-closure audit is claimed. The successful results here are normal Lean kernel checks and their printed axiom audits; a production Palomar build still needs its independent checking procedure.

Full commands, user/sys time, exact RSS in KiB, exit codes, source/output sizes and printed audits are in [measurements.jsonl](measurements.jsonl), with original GNU time outputs and complete diagnostics under [logs/](logs/). Provenance is in [source_changes.md](source_changes.md), [source_changes.json](source_changes.json) and [source_inventory.json](source_inventory.json). [audit.json](audit.json) records the resource and trust audit. Original files are retained in `/home/ubuntu/aklt/compfeas/probes/`.

**What changed to make the uncompiled probes usable.** The four guard files used root identifier `guard`, which Mathlib already defines. It was renamed to `guardMask`; the initial two failed guard runs and data-only diagnostic are retained. Baseline gained a trivial kernel theorem and axiom print. Other supplied files are unchanged. No numerical constant, matrix entry, factor entry, window enumeration, or arithmetic predicate was corrected to make a false check pass.

Large direct hexadecimal tokens and large overloaded Int lists make source elaboration a substantial bottleneck. New `Fast*` variants emit the **same ordinary literals/constructors** using untrusted term elaborators. `PackedLiteralSyntax` uses balanced decoding and emits an `Expr.lit` Nat; `IntRowsSyntax` emits ordinary List/Int constructors. These elaborators do not prove a proposition, install a kernel reduction rule, or trust a parse/decompression result as evidence. The kernel checks the emitted data against the checker. External Python comparison confirmed every packed digit sequence and every H1 matrix/factor entry matches the original. The syntax-helper development failures are also retained in the table and documented in the change log.

**Packed arithmetic and cache growth.** The real guard plane sizes are 1,590,480 bits (19,881 lanes, 80-bit fields) and 2,177,364 bits (25,921 lanes, 84-bit fields). After the name repair, ordinary BellmanGuard1/16 passed in 249.62/250.07 s; almost all time was literal elaboration. Ordinary Bellman9Guard1 passed in 461.68 s, while its 16-row raw-source attempt was stopped at 120 s. The Fast versions of **both** sizes and **both** counts passed in 4.6–5.3 s total. Once equivalent Fast checks passed, duplicate large raw-source loads were capped at 120 s; their censored durations are not completed checker runtimes. The raw-source timeout is not evidence of failed guarded arithmetic.

The earlier concern that bitwise operations might only be fast in compiled code was resolved empirically: normal `decide +kernel` guard, routing, and large bitwise checks complete quickly. The stdlib's `extern` attributes alone do not predict kernel behavior. Successful larger kernel reductions, rather than native timings, support the following rates. Profiling is Lean's cumulative **type-checking** time, not total wall time:

| Probe | Kernel type checking | Total wall s | Peak RSS GiB |
|---|---:|---:|---:|
| FastBellmanGuard1 | 0.00191 s | 4.75 | 6.771 |
| FastBellmanGuard16 | 0.0125 s | 4.63 | 6.792 |
| FastBellmanGuard128 | 0.0968 s | 4.81 | 6.926 |
| FastBellmanGuard1024 | 0.747 s | 5.38 | 8.092 |
| FastBellmanGuard4096 | 2.98 s | 7.75 | 12.089 |
| FastBellman9Guard1 | 0.00225 s | 5.10 | 6.775 |
| FastBellman9Guard16 | 0.0166 s | 5.24 | 6.803 |
| FastBellman9Guard1024 | 0.997 s | 6.26 | 8.587 |
| FastBellman9Guard4096 | 4.02 s | 9.28 | 14.050 |
| FastPacked1 | 0.00115 s | 3.88 | 6.766 |
| FastPacked16 | 0.00453 s | 3.79 | 6.770 |
| FastPacked128 | 0.0332 s | 3.86 | 6.806 |
| FastPacked1024 | 0.249 s | 4.11 | 7.176 |
| FastPacked4096 | 1.02 s | 4.95 | 8.426 |

Using the 1024→4096 increments gives **0.727 ms/guard row** for m=10 and **0.984 ms/guard row** for m=9. Each generic row has two weighted planes and one easy successful comparison; this is not the cost of an actual row with all special masks and boundary rules. The corresponding retained RSS slopes are about **1.332 / 1.821 MiB per row**.

Packed1/16/128 at the supplied 200,000-bit plane size passed in 12.38/12.45/12.49 s, at 6.463/6.468/6.512 GiB. That small range is dominated by literal loading. The longer Fast runs resolve the slope: **0.251 ms per packed step** and **0.417 MiB retained per step**, approximately linear through 4096. Structural tail recursion does not release earlier reduction data within one kernel check. A long periodic replay therefore needs independently checked checkpoints/chunks; it is not approved as one reduction. The probe is one fixed-point east-routing average, not a full memory-walk transition.

Six independent 1024-row guard modules took **34.27 s sequentially** and **5.80 s concurrently**, a 5.91× speedup on this small build. All twelve invocations passed, with `propext` only. This supports scheduling six independent small modules; it does not establish scaling for large H1 blocks, multi-GB imports or weighted prefixes. See [parallel_groups.json](parallel_groups.json).

**H2.** The complete supplied small test passed twice: 18.11 s / 9.18 GiB and 18.48 s / 9.18 GiB, with P,C,Q. It generates all length-six bond trails in Lean, checks the count **916**, then every raw window inequality, including positive witness lookup and true revisit weight **1/5**. Its 2,628 weighted edges are not supplied as a trusted transition matrix. This confirms the proposed computational core. Connecting the Boolean fact to domination and the H2 hypothesis remains mathematical work. It proves the weaker contracting H2 option, not the paper's optional numerical rate 0.98075.

**H1.** The original overloaded list source timed out at 600 s before finishing elaboration; a later repeat was capped at 120 s. The same 131×131 matrix and triangular factor emitted as constructors passed in **122.13 s / 24.36 GiB**, with P only. Splitting its data into named row definitions built [H1RowData](../../wt/PROBE2/AKLT/Probe2/H1RowData.lean) in **11.37 s / 7.43 GiB**; its separate [residual check](../../wt/PROBE2/AKLT/Probe2/H1RowCheck.lean) passed in **108.07 s / 24.16 GiB**, of which about 104 s was kernel type checking. Data and checker oleans are 44,594,216 and 97,048 B. Row definitions solve the source/compiler problem; this full-block theorem still retains about 24 GiB. Arithmetic row sharding is a separate, recommended change.

This checker forms the residual and verifies strict row diagonal dominance. It does not regenerate the matrix from an H1 pattern, establish symmetry from that constructor, prove shape/completeness, or supply the Gram/DD quadratic-form soundness theorem. Those obligations cannot be replaced by the stored matrix's acceptance.

**Prefixes.** The table's successful equalities certify 1,466 / 11,482 / 89,150 leaves at lengths 8 / 10 / 12. Length 12 required a 48 GiB address cap and passed at **206.40 s / 33.85 GiB**. It failed at 16, 24 and 32 GiB caps. Length 14 failed at every tested cap, including **214.21 s / 42.43 GiB** under the 48 GiB cap. These failures do not certify the proposed 688,590 count or refute it.

An external traversal of the exact supplied geometry counts 2,304 / 18,024 / 139,984 / 1,081,424 recursive calls and reproduces the four expected leaf counts; these are **untrusted counting inputs to extrapolation**, not extra Lean results. See [geometry_counts.json](geometry_counts.json). No weights, phase-state transitions, endpoint potential lookup, or comparison of final weighted row bounds are included in the Lean geometry probes.

**Literal-size experiment.** MB means 10^6 binary bytes here; source hex text is twice that size, plus a small header. Each module contains one Nat of exactly the stated binary width, and a kernel theorem forces its reduction modulo 65536. The repeated digit pattern is deliberately deterministic; the `.olean` stores the entire Nat, not a compressed description. This experiment measures literal representation, not validity of any AKLT witness.

| Binary payload | Plain `0x` outcome | Balanced elaborator wall / RSS | `.lean` bytes (balanced) | `.olean` bytes | Import + kernel use wall / RSS |
|---|---|---|---:|---:|---|
| 1 MB | timeout 600.58 s | 5.01 s / 6.78 GiB | 2,000,267 | 1,009,488 | 3.56 s / 6.77 GiB |
| 10 MB | timeout 120.62 s | 19.30 s / 7.01 GiB | 20,000,269 | 10,009,488 | 3.52 s / 6.80 GiB |
| 50 MB | timeout 120.61 s | 81.24 s / 7.91 GiB | 100,000,269 | 50,009,488 | 3.59 s / 6.94 GiB |

All six successful literal/import theorems are axiom-free. The 10/50 MB plain-token runs had 120 s adaptive limits; the 1 MB run had 600 s. These are censored times, not completed parse times. Installed `Init/Meta/Defs.lean` decodes a hex token by the growing recurrence `val := 16*val+d`, explaining why enormous individual tokens are a bad source representation. Four ~199 KB plane literals already cost minutes in the ordinary guard files. The balanced elaborator emits exactly the same literal using small leaves and balanced joins.

At 50 MB, profiling gives about 75.8 s of elaborator interpretation, 0.301 s parsing, 0.079 s kernel type checking and 0.041 s `.olean` serialization. The useful observed limit is therefore **at least 50 MB per emitted Nat/module**, not a maximum supported size. Direct-token loading is already a bottleneck below 1 MB; with balanced emission, source-to-literal elaboration dominates while 50 MB serialization/import remains practical. No 1.2 GB literal, multi-GB module, serializer size limit, or 4 GB format boundary was tested. Do not infer safety of such a module from the 50 MB success. The measured 10→50 MB slope is about 1.55 seconds per binary MB in this interpreted elaborator.

**EXTRAPOLATION — H3′ stationary m=10, R=70, five cases.** Assumptions: spatial lanes remain at the measured widths; a proved packing/no-carry/guard/routing implementation can check actual Bellman rows with small bounded numbers of whole-plane operations; regenerated automaton indices and exceptions are sound; potentials can be emitted as ordinary literals; independent chunks release reduction caches. None of those implementation/soundness lemmas is supplied by the generic probe.

There are 4×3,741×5 = **74,820 phase/window planes** and 226,140 weighted whole-plane terms. Scaling the generic two-term row rate by the term count gives only **82 s of generic arithmetic**. It is a model anchor, not a completed local certificate. Allowing 2–10× for actual routing, caps, guards and centre/target/boundary exceptions suggests minutes to tens of minutes of local kernel arithmetic, conditional on that implementation. Scalar checking of the 4.50 billion weighted products is not justified by this packed rate.

The uint32 payload is **1,189,997,136 B/case**. Widening every value to an 80-bit lane gives **2,974,992,840 B/case**, **14,874,964,200 B for five**, and about **29.75 GB of hex source** before headers/common masks. Corresponding literal olean payload is about 14.88 GB, based on the size experiment, not the compressed 2.60 GB input size. The current balanced decoder alone extrapolates to **6.4 CPU-hours** across five cases. This data-loading cost dominates the generic guard arithmetic. It can be improved by an untrusted exporter/elaborator; it cannot be omitted from a source-build forecast.

Use one plane per literal and **32–64 planes per data module** (about 6.4–12.7 MB binary), with shared masks and indexing definitions. At 64 planes this is about **1,170 data modules** across all five cases. Check **64–256 rows per kernel process/module** initially, importing only the necessary neighboring plane groups; their generic cache increment is about 0.09–0.34 GiB, before actual graph overhead. Do not repeat the whole certificate in each checker source. A per-case or final aggregator can retain many imported literals; only a 50 MB import was tested, so explicitly measure a multi-GB aggregate before committing to the final import graph. Hashes identify input artifacts but never replace their checked relation to the definitions.

The m=10 exact prefix has 708,097 reported nodes across five cases. Scaling from the successful B/north geometry gives about **17 minutes geometry-only**, with additional 3,516,794 phase products and verified balanced endpoint lookup. A full 12-prefix monolith uses tens of GiB even before weights; split by a shallow, definition-generated frontier and check small subtrees in fresh modules. Prove that frontier enumeration and recombination exhaust the original tree. Supply and verify a compact endpoint table once; do not extract from a million-bit plane separately at every leaf.

With the present interpreted loader, grouped data/check modules, and an engineered weighted prefix, **10–30 CPU-hours** is a planning scenario for numerical checking of all five cases. It includes the roughly 6.4-hour loader anchor, process startup and substantial overhead beyond the generic rows; it is not a measured end-to-end runtime or a bound on proof-development time. Six-way execution can shorten independent parts, but I/O and final aggregation were not benchmarked at that scale. **Conditional go; prioritize this route.** Before exporting all data, prove the packing/guard soundness and time one complete actual Bellman row, then a real prefix chunk and its verified endpoint lookup.

**EXTRAPOLATION — m=9, R=80 alternative.** There are **22,560 planes**, 66,340 generic weighted terms, and 84-bit lanes. The corresponding two-term guard model gives **33 s**; local checking and data are smaller. The uint32 payload is **467,822,208 B/case**, widening to **1,228,033,296 B/case**, or **6,140,166,480 B** for five; hex source is about 12.28 GB. Current decoder cost extrapolates to **2.6 CPU-hours**. Grouping 32–64 planes means about 8.7–17.4 MB binary per data module, within the measured 50 MB range.

Its successful mathematical design requires **B prefix 18 and C prefix 16**, not the failing 14/14 design. COMPFEAS reports 161,516,061 prefix nodes and 801,223,835 phase products, some reaching 1,518 bits. At the length-12 geometry rate alone this is **65 CPU-hours**, with longer histories likely adding cost. Length-14 B/north alone extrapolates to about **26 minutes** and roughly **216 GiB** under linear cache growth; its 48 GiB failure supports the need for sharding, not that precise projected peak. A partitioned weighted implementation could plausibly take **4–10 CPU-days**, conditional on balanced lookup and bounded chunks. That range is less reliable than the geometry anchor. **No-go as the preferred route under the present implementation; retain only if lower disk/data cost becomes decisive.** The mixed m=10-B/m=9-C option has 24,458,661 prefix nodes: approximately 10 CPU-hours geometry-only, so it also needs a measured prefix advantage to displace m=10 throughout.

**EXTRAPOLATION — H1 at 12,173 blocks.** The measured full residual performs **757,966** Int products. Its ~104 s kernel time is about **137 μs per product including traversal, sums and row checks**, not isolated multiplication latency. COMPFEAS counts **60,154,555 triangular** Gram products, plus 2,184,033 factor entries; the probe checks both halves, so the corresponding full-row count is **2×60,154,555−2,184,033 = 118,125,077**, not 60 million. At the sample's effective rate this is about **4.5 CPU-hours** for full Gram arithmetic, or an idealized **2.3 hours** if a verified triangular checker avoids duplication. Small-block row/shape/DD overhead, including the 8,439 blocks needing no factor, makes straight per-product scaling optimistic.

One fresh process per block adds about **11.5 CPU-hours** of this import baseline. Group small blocks, but keep separate kernel reductions and bounded row chunks for large blocks. A reasonable positivity-stage planning range is **5–20 CPU-hours**, assuming similar operand widths/density and streamed data; startup/data export can dominate if every tiny block is its own process. The largest reconstructed size 179, extrapolated cubically from 131, would take roughly 4.4 minutes and potentially over 50 GiB in one reduction. That is unmeasured; use **8–16 row obligations per large-block chunk** as an initial target and tune measured peaks to ~8–12 GiB for parallel work. Row definitions alone do not achieve that cache target.

The sample does not time the definition-derived moment contraction, inversion, Pauli placement, sector transformation, or complete pattern coverage. COMPFEAS's sparse counts still include about 95 million positive tensor products and 1.596 billion Pauli placements; a favorable Gram check does not make those free. **Go for Gram/DD, no-go for a dense source-style constructor or a promised full-H1 runtime based on this probe.** Retain tens-to-hundreds of CPU-hours as an unvalidated sparse-constructor scenario until one real small/sample/largest constructor has been checked from patterns in Lean. Importing a claimed matrix would leave H1 unproved.

**EXTRAPOLATION — H2.** The small true-revisit test is already a completed finite check at ~18.5 s / 9.2 GiB. Keep it as one module initially, with the domination/enumeration soundness lemma separate; no numerical sharding is presently needed. Allow roughly a minute, rather than hours, for a normal numerical rebuild including minor wrapper overhead. This does not estimate mathematical proof development.

If the original extension-eight numerical rate is required, it was not run here. COMPFEAS reports 5,627,018 extension multiplications and 3,609,484 terminal leaves on 938 orbit rows. Scaling the small test's 12 s kernel time by 9,236,502/2,628 weighted/terminal operations gives ~12 CPU-hours before accounting for different geometry, deeper history and orbit lookup. A **10–50 CPU-hour** scenario is plausible with generated row chunks and proved symmetry/balanced lookup, but is weakly constrained and must not be advertised as a measured original-H2 result. **Go for small H2; original H2 is conditional and unnecessary unless its numerical target is required.**

**Calibration and representation.** Supplied and doubled Nat/Int loops all passed. Kernel timings below isolate computation better than total wall times near the import baseline; each loop contains several operations and cannot be read as an isolated GMP instruction rate.

| Family | Original iterations | Kernel s | Doubled kernel s |
|---|---:|---:|---:|
| Nat64 | 10,000 | 0.713 | 1.76 |
| Nat256 | 10,000 | 0.736 | 1.7 |
| Nat4096 | 2,000 | 0.182 | 0.417 |
| Nat16384 | 200 | 0.0567 | 0.116 |
| Int64 | 10,000 | 2.61 | 5.49 |
| Int4096 | 2,000 | 0.401 | 0.935 |

ListZip1000/4000 passed in 3.54/3.89 s, at 6.47/6.54 GiB. ListIndex1000 failed a 16 GiB address cap but passed at 24 GiB in **21.83 s / 10.96 GiB**. ListIndex4000 failed even at the 24 GiB cap (40.19 s / 18.46 GiB). Sequential row/plane traversal and proved balanced lookup are mandatory design choices here; repeatedly indexing a linear list is not a viable full-certificate representation.

**Complete measurement table.** Rows are grouped in the requested ranked order, with repetitions/diagnostics retained. `K NAME CAP SECONDS [flags]` denotes the following reproducible command template, from `/home/ubuntu/aklt/wt/PROBE2`; `p` adds `--profile`, `n` omits `-o`. For `c`, replace the Lean argument tail by the toolchain's `leanchecker --fresh AKLT.Probe2.NAME`. The table uses effective wall limits; historical exact outer/inner wrappers are in each `.time` file and JSONL command field. `PROBE2_IGNORE_INNER_LIMITS=1` disables the adaptive policy for standalone replay.

```sh
source /home/ubuntu/aklt/reports/PROBE2/K.sh
K FastPacked128 24 600 p
```

[K.sh](K.sh) expands every table command into `/usr/bin/time -v lake env timeout ... python3 limit_exec.py CAP lean -DElab.async=false ...`, sets PATH/LEAN_PATH/LEAN_NUM_THREADS, and disables the adaptive inner-limit policy so the table's effective limit is reproduced. The example above is directly runnable. Wall and RSS come from GNU time; RSS is displayed as GiB (KiB/1,048,576). Full integer KiB values are in the raw records. Axiom abbreviations: **∅** = prints no axioms, **P** = propext, **C** = Classical.choice, **Q** = Quot.sound. “not printed” is not an axiom-free result. N/A is a successful support/data module with no theorem audit. Failed historical source versions are documented in `source_changes.md`; replaying current corrected sources need not reproduce those errors.

| Measurement / full log | Command | Wall s | Max RSS GiB | Exit / outcome | Printed axioms |
|---|---|---:|---:|---|---|
| [Baseline](logs/Baseline.log) | `K Baseline 24 600` | 3.39 | 6.450 | 0 / PASS | ∅ |
| [BaselineNoOlean](logs/BaselineNoOlean.log) | `K Baseline 16 30 n` | 3.30 | 6.442 | 0 / PASS | ∅ |
| [BellmanGuard1](logs/BellmanGuard1.log) | `K BellmanGuard1 24 600` | 187.91 | 6.460 | 1 / FAIL | P,sorryAx |
| [FastBellmanGuard1](logs/FastBellmanGuard1.log) | `K FastBellmanGuard1 24 300 p` | 4.75 | 6.771 | 0 / PASS | P |
| [FastBellmanGuard16](logs/FastBellmanGuard16.log) | `K FastBellmanGuard16 24 300 p` | 4.63 | 6.792 | 0 / PASS | P |
| [BellmanGuard16](logs/BellmanGuard16.log) | `K BellmanGuard16 24 600` | 187.16 | 6.460 | 1 / FAIL | P,sorryAx |
| [FastBellmanGuard16Check](logs/FastBellmanGuard16Check.log) | `K FastBellmanGuard16 16 120 c` | 120.55 | 6.528 | 124 / TIMEOUT | not printed |
| [FastBellmanGuard128](logs/FastBellmanGuard128.log) | `K FastBellmanGuard128 24 300 p` | 4.81 | 6.926 | 0 / PASS | P |
| [FastBellmanGuard1024](logs/FastBellmanGuard1024.log) | `K FastBellmanGuard1024 24 300 p` | 5.38 | 8.092 | 0 / PASS | P |
| [FastBellmanGuard4096](logs/FastBellmanGuard4096.log) | `K FastBellmanGuard4096 24 300 p` | 7.75 | 12.089 | 0 / PASS | P |
| [BellmanGuard1Fixed](logs/BellmanGuard1Fixed.log) | `K BellmanGuard1 16 600 p` | 249.62 | 6.466 | 0 / PASS | P |
| [BellmanGuard16Fixed](logs/BellmanGuard16Fixed.log) | `K BellmanGuard16 16 600 p` | 250.07 | 6.486 | 0 / PASS | P |
| [FastBellman9Guard1](logs/FastBellman9Guard1.log) | `K FastBellman9Guard1 24 300 p` | 5.10 | 6.775 | 0 / PASS | P |
| [FastBellman9Guard16](logs/FastBellman9Guard16.log) | `K FastBellman9Guard16 24 300 p` | 5.24 | 6.803 | 0 / PASS | P |
| [FastBellman9Guard128](logs/FastBellman9Guard128.log) | `K FastBellman9Guard128 24 300 p` | 5.35 | 6.997 | 0 / PASS | P |
| [FastBellman9Guard1024](logs/FastBellman9Guard1024.log) | `K FastBellman9Guard1024 24 300 p` | 6.26 | 8.587 | 0 / PASS | P |
| [FastBellman9Guard4096](logs/FastBellman9Guard4096.log) | `K FastBellman9Guard4096 24 300 p` | 9.28 | 14.050 | 0 / PASS | P |
| [Bellman9Guard1](logs/Bellman9Guard1.log) | `K Bellman9Guard1 24 600` | 461.68 | 6.470 | 0 / PASS | P |
| [Bellman9Guard16](logs/Bellman9Guard16.log) | `K Bellman9Guard16 24 120` | 120.59 | 6.462 | 124 / TIMEOUT | not printed |
| [FastPacked1](logs/FastPacked1.log) | `K FastPacked1 24 300 p` | 3.88 | 6.766 | 0 / PASS | P |
| [FastPacked16](logs/FastPacked16.log) | `K FastPacked16 24 300 p` | 3.79 | 6.770 | 0 / PASS | P |
| [FastPacked128](logs/FastPacked128.log) | `K FastPacked128 24 300 p` | 3.86 | 6.806 | 0 / PASS | P |
| [FastPacked1024](logs/FastPacked1024.log) | `K FastPacked1024 24 300 p` | 4.11 | 7.176 | 0 / PASS | P |
| [FastPacked4096](logs/FastPacked4096.log) | `K FastPacked4096 24 300 p` | 4.95 | 8.426 | 0 / PASS | P |
| [Packed1](logs/Packed1.log) | `K Packed1 24 600` | 12.38 | 6.463 | 0 / PASS | P |
| [Packed16](logs/Packed16.log) | `K Packed16 24 600` | 12.45 | 6.468 | 0 / PASS | P |
| [Packed128](logs/Packed128.log) | `K Packed128 24 600` | 12.49 | 6.512 | 0 / PASS | P |
| [H2SmallEarly](logs/H2SmallEarly.log) | `K H2Small 32 600 p` | 18.11 | 9.178 | 0 / PASS | P,C,Q |
| [H2Small](logs/H2Small.log) | `K H2Small 24 600` | 18.48 | 9.182 | 0 / PASS | P,C,Q |
| [FastH1Gram](logs/FastH1Gram.log) | `K FastH1Gram 32 600 p` | 122.13 | 24.363 | 0 / PASS | P |
| [H1RowDataRows](logs/H1RowDataRows.log) | `K H1RowData 16 300 p` | 4.93 | 6.774 | 1 / FAIL | not printed |
| [H1RowCheckRows](logs/H1RowCheckRows.log) | `K H1RowCheck 16 300 p` | 0.54 | 0.787 | 1 / FAIL | not printed |
| [H1RowDataFixed](logs/H1RowDataFixed.log) | `K H1RowData 16 120 p` | 11.37 | 7.431 | 0 / PASS | N/A |
| [H1RowCheckFixed](logs/H1RowCheckFixed.log) | `K H1RowCheck 32 300 p` | 108.07 | 24.162 | 0 / PASS | P |
| [H1GramEarly](logs/H1GramEarly.log) | `K H1Gram 32 600 p` | 600.56 | 6.521 | 124 / TIMEOUT | not printed |
| [H1Gram](logs/H1Gram.log) | `K H1Gram 24 120` | 120.62 | 6.487 | 124 / TIMEOUT | not printed |
| [PrefixLeaves8Geometry16](logs/PrefixLeaves8Geometry16.log) | `K PrefixLeaves8 16 180 p` | 5.77 | 6.792 | 0 / PASS | P,C,Q |
| [PrefixLeaves10Geometry16](logs/PrefixLeaves10Geometry16.log) | `K PrefixLeaves10 16 180 p` | 25.74 | 9.559 | 0 / PASS | P,C,Q |
| [PrefixLeaves12Geometry16](logs/PrefixLeaves12Geometry16.log) | `K PrefixLeaves12 16 180 p` | 26.26 | 10.455 | 134 / MEMORY LIMIT | not printed |
| [PrefixLeaves14Geometry16](logs/PrefixLeaves14Geometry16.log) | `K PrefixLeaves14 16 180 p` | 26.06 | 10.455 | 134 / MEMORY LIMIT | not printed |
| [PrefixLeaves8Early](logs/PrefixLeaves8Early.log) | `K PrefixLeaves8 32 600 p` | 5.85 | 6.792 | 0 / PASS | P,C,Q |
| [PrefixLeaves10Early](logs/PrefixLeaves10Early.log) | `K PrefixLeaves10 32 600 p` | 25.71 | 9.559 | 0 / PASS | P,C,Q |
| [PrefixLeaves12Geometry48](logs/PrefixLeaves12Geometry48.log) | `K PrefixLeaves12 48 600 p` | 206.40 | 33.846 | 0 / PASS | P,C,Q |
| [PrefixLeaves8](logs/PrefixLeaves8.log) | `K PrefixLeaves8 24 600` | 5.94 | 6.792 | 0 / PASS | P,C,Q |
| [PrefixLeaves12Early](logs/PrefixLeaves12Early.log) | `K PrefixLeaves12 32 600 p` | 118.90 | 26.444 | 1 / MEMORY LIMIT | not printed |
| [PrefixLeaves10](logs/PrefixLeaves10.log) | `K PrefixLeaves10 24 600` | 26.03 | 9.561 | 0 / PASS | P,C,Q |
| [PrefixLeaves12](logs/PrefixLeaves12.log) | `K PrefixLeaves12 24 600` | 75.02 | 18.460 | 134 / MEMORY LIMIT | not printed |
| [PrefixLeaves14Geometry48](logs/PrefixLeaves14Geometry48.log) | `K PrefixLeaves14 48 600 p` | 214.21 | 42.434 | 1 / MEMORY LIMIT | not printed |
| [PrefixLeaves14Early](logs/PrefixLeaves14Early.log) | `K PrefixLeaves14 32 600 p` | 121.26 | 26.446 | 134 / MEMORY LIMIT | not printed |
| [PrefixLeaves14](logs/PrefixLeaves14.log) | `K PrefixLeaves14 24 600` | 75.20 | 18.460 | 134 / MEMORY LIMIT | not printed |
| [Nat64Profile](logs/Nat64Profile.log) | `K Nat64 16 300 p` | 4.07 | 6.594 | 0 / PASS | ∅ |
| [Nat256Profile](logs/Nat256Profile.log) | `K Nat256 16 300 p` | 4.05 | 6.597 | 0 / PASS | ∅ |
| [Nat4096Profile](logs/Nat4096Profile.log) | `K Nat4096 16 300 p` | 3.50 | 6.487 | 0 / PASS | ∅ |
| [Nat16384Profile](logs/Nat16384Profile.log) | `K Nat16384 16 300 p` | 3.43 | 6.465 | 0 / PASS | ∅ |
| [Nat64DoubleProfile](logs/Nat64DoubleProfile.log) | `K Nat64Double 16 300 p` | 5.11 | 6.745 | 0 / PASS | ∅ |
| [Nat256DoubleProfile](logs/Nat256DoubleProfile.log) | `K Nat256Double 16 300 p` | 5.09 | 6.750 | 0 / PASS | ∅ |
| [Nat4096DoubleProfile](logs/Nat4096DoubleProfile.log) | `K Nat4096Double 16 300 p` | 3.86 | 6.523 | 0 / PASS | ∅ |
| [Nat16384DoubleProfile](logs/Nat16384DoubleProfile.log) | `K Nat16384Double 16 300 p` | 3.53 | 6.474 | 0 / PASS | ∅ |
| [Nat64](logs/Nat64.log) | `K Nat64 24 600` | 4.25 | 6.594 | 0 / PASS | ∅ |
| [Nat256](logs/Nat256.log) | `K Nat256 24 600` | 4.27 | 6.596 | 0 / PASS | ∅ |
| [Nat4096](logs/Nat4096.log) | `K Nat4096 24 600` | 3.66 | 6.486 | 0 / PASS | ∅ |
| [Nat16384](logs/Nat16384.log) | `K Nat16384 24 600` | 3.58 | 6.465 | 0 / PASS | ∅ |
| [Int64Profile](logs/Int64Profile.log) | `K Int64 16 300 p` | 6.00 | 6.910 | 0 / PASS | ∅ |
| [Int4096Profile](logs/Int4096Profile.log) | `K Int4096 16 300 p` | 3.80 | 6.549 | 0 / PASS | ∅ |
| [Int64DoubleProfile](logs/Int64DoubleProfile.log) | `K Int64Double 16 300 p` | 8.95 | 7.378 | 0 / PASS | ∅ |
| [Int4096DoubleProfile](logs/Int4096DoubleProfile.log) | `K Int4096Double 16 300 p` | 4.30 | 6.657 | 0 / PASS | ∅ |
| [Int64](logs/Int64.log) | `K Int64 24 600` | 6.11 | 6.909 | 0 / PASS | ∅ |
| [Int4096](logs/Int4096.log) | `K Int4096 24 600` | 3.89 | 6.551 | 0 / PASS | ∅ |
| [ListZip1000Profile](logs/ListZip1000Profile.log) | `K ListZip1000 16 300 p` | 3.44 | 6.470 | 0 / PASS | P |
| [ListIndex1000Profile](logs/ListIndex1000Profile.log) | `K ListIndex1000 16 300 p` | 15.04 | 10.471 | 1 / MEMORY LIMIT | not printed |
| [ListZip4000Profile](logs/ListZip4000Profile.log) | `K ListZip4000 16 300 p` | 3.84 | 6.537 | 0 / PASS | P |
| [ListIndex4000Profile](logs/ListIndex4000Profile.log) | `K ListIndex4000 16 300 p` | 15.15 | 10.467 | 1 / MEMORY LIMIT | not printed |
| [ListZip1000](logs/ListZip1000.log) | `K ListZip1000 24 600` | 3.54 | 6.468 | 0 / PASS | P |
| [ListIndex1000](logs/ListIndex1000.log) | `K ListIndex1000 24 600` | 21.83 | 10.962 | 0 / PASS | P |
| [ListZip4000](logs/ListZip4000.log) | `K ListZip4000 24 600` | 3.89 | 6.537 | 0 / PASS | P |
| [ListIndex4000](logs/ListIndex4000.log) | `K ListIndex4000 24 600` | 40.19 | 18.463 | 1 / MEMORY LIMIT | not printed |
| [FastLiteral1MB](logs/FastLiteral1MB.log) | `K FastLiteral1MB 24 600 p` | 5.01 | 6.779 | 0 / PASS | ∅ |
| [FastLiteral10MB](logs/FastLiteral10MB.log) | `K FastLiteral10MB 24 600 p` | 19.30 | 7.012 | 0 / PASS | ∅ |
| [FastLiteral50MB](logs/FastLiteral50MB.log) | `K FastLiteral50MB 24 600 p` | 81.24 | 7.908 | 0 / PASS | ∅ |
| [ImportLiteral1MB](logs/ImportLiteral1MB.log) | `K ImportLiteral1MB 16 120 p` | 3.56 | 6.766 | 0 / PASS | ∅ |
| [ImportLiteral10MB](logs/ImportLiteral10MB.log) | `K ImportLiteral10MB 16 120 p` | 3.52 | 6.800 | 0 / PASS | ∅ |
| [ImportLiteral50MB](logs/ImportLiteral50MB.log) | `K ImportLiteral50MB 16 120 p` | 3.59 | 6.938 | 0 / PASS | ∅ |
| [Literal1MB](logs/Literal1MB.log) | `K Literal1MB 24 600` | 600.58 | 6.453 | 124 / TIMEOUT | not printed |
| [Literal10MB](logs/Literal10MB.log) | `K Literal10MB 24 120` | 120.62 | 6.524 | 124 / TIMEOUT | not printed |
| [Literal50MB](logs/Literal50MB.log) | `K Literal50MB 24 120` | 120.61 | 6.817 | 124 / TIMEOUT | not printed |
| [Parallel1Sequential](logs/Parallel1Sequential.log) | `K Parallel1 16 120 p` | 5.69 | 8.092 | 0 / PASS | P |
| [Parallel2Sequential](logs/Parallel2Sequential.log) | `K Parallel2 16 120 p` | 5.68 | 8.093 | 0 / PASS | P |
| [Parallel3Sequential](logs/Parallel3Sequential.log) | `K Parallel3 16 120 p` | 5.64 | 8.092 | 0 / PASS | P |
| [Parallel4Sequential](logs/Parallel4Sequential.log) | `K Parallel4 16 120 p` | 5.69 | 8.091 | 0 / PASS | P |
| [Parallel5Sequential](logs/Parallel5Sequential.log) | `K Parallel5 16 120 p` | 5.72 | 8.093 | 0 / PASS | P |
| [Parallel6Sequential](logs/Parallel6Sequential.log) | `K Parallel6 16 120 p` | 5.60 | 8.093 | 0 / PASS | P |
| [Parallel6Concurrent](logs/Parallel6Concurrent.log) | `K Parallel6 16 120 p` | 5.73 | 8.038 | 0 / PASS | P |
| [Parallel5Concurrent](logs/Parallel5Concurrent.log) | `K Parallel5 16 120 p` | 5.75 | 8.041 | 0 / PASS | P |
| [Parallel3Concurrent](logs/Parallel3Concurrent.log) | `K Parallel3 16 120 p` | 5.75 | 8.036 | 0 / PASS | P |
| [Parallel1Concurrent](logs/Parallel1Concurrent.log) | `K Parallel1 16 120 p` | 5.75 | 8.037 | 0 / PASS | P |
| [Parallel2Concurrent](logs/Parallel2Concurrent.log) | `K Parallel2 16 120 p` | 5.75 | 8.038 | 0 / PASS | P |
| [Parallel4Concurrent](logs/Parallel4Concurrent.log) | `K Parallel4 16 120 p` | 5.75 | 8.040 | 0 / PASS | P |
| [KernelAnd64](logs/KernelAnd64.log) | `K KernelAnd64 16 120` | 3.30 | 6.451 | 0 / PASS | P |
| [KernelShift64](logs/KernelShift64.log) | `K KernelShift64 16 120` | 3.30 | 6.451 | 0 / PASS | ∅ |
| [KernelAnd256](logs/KernelAnd256.log) | `K KernelAnd256 16 120` | 3.32 | 6.451 | 0 / PASS | P |
| [KernelShift256](logs/KernelShift256.log) | `K KernelShift256 16 120` | 3.31 | 6.451 | 0 / PASS | ∅ |
| [KernelAnd4096](logs/KernelAnd4096.log) | `K KernelAnd4096 16 120` | 3.35 | 6.451 | 0 / PASS | P |
| [KernelShift4096](logs/KernelShift4096.log) | `K KernelShift4096 16 120` | 3.38 | 6.451 | 0 / PASS | ∅ |
| [KernelAnd16384](logs/KernelAnd16384.log) | `K KernelAnd16384 16 120` | 3.34 | 6.452 | 0 / PASS | P |
| [KernelShift16384](logs/KernelShift16384.log) | `K KernelShift16384 16 120` | 3.35 | 6.451 | 0 / PASS | ∅ |
| [PackedLiteralSyntax](logs/PackedLiteralSyntax.log) | `K PackedLiteralSyntax 16 60` | 1.18 | 1.496 | 1 / FAIL | not printed |
| [PackedLiteralSyntaxRevised](logs/PackedLiteralSyntaxRevised.log) | `K PackedLiteralSyntax 16 60` | 1.13 | 1.498 | 1 / FAIL | not printed |
| [PackedLiteralSyntaxFinal](logs/PackedLiteralSyntaxFinal.log) | `K PackedLiteralSyntax 16 60` | 1.13 | 1.508 | 0 / PASS | N/A |
| [BellmanData](logs/BellmanData.log) | `K BellmanData 24 600` | 187.13 | 6.458 | 1 / FAIL | ∅ |
| [KernelAnd16384Check](logs/KernelAnd16384Check.log) | `K KernelAnd16384 16 120 c` | 120.56 | 6.275 | 124 / TIMEOUT | not printed |
| [IntRowsSyntax](logs/IntRowsSyntax.log) | `K IntRowsSyntax 16 60` | 1.17 | 1.510 | 0 / PASS | N/A |
| [IntRowsSyntaxRows](logs/IntRowsSyntaxRows.log) | `K IntRowsSyntax 8 60` | 1.14 | 1.500 | 1 / FAIL | not printed |
| [IntRowsSyntaxLift](logs/IntRowsSyntaxLift.log) | `K IntRowsSyntax 8 60` | 1.18 | 1.511 | 0 / PASS | N/A |
