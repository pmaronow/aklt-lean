STATUS: PARTIAL (neither Level A nor Level B demonstrated; generic packing refinements and full-budget validation remain)

# H1_FIT — design, full numerical audits, and kernel pilots

The best executable redesign is **shared four-site half-ring tensors, sparse contractions in tensor-factor digit order, bounded two-row slabs, and a packed uniform-error Gram certificate**. All 12,173 archived blocks are reproduced exactly outside Lean, and all 3,734 non-DD blocks have new exact integer uniform-error witnesses. The entire largest 179-row sample block has kernel-checked half reconstruction and slab checks, accepted by Lean replay and NanoDa. These are finite arithmetic results, **not yet a proof of H1**: the generic digit/no-carry/network refinements remain open.

**Verdict: neither level is established.** Level A is out of reach of the measured implementation. A carefully batched full generator has a **2.375–4.639 CPU-hour planning range**, excluding independent replays and the rest of the repository. That straddles Level B; it is not a measured upper bound. This is a credible Level B development candidate, not a default-profile submission. The existing H3′ lane still costs about 20 CPU-hours, so this work cannot establish that the combined package fits.

All new Lean sources are under `/home/ubuntu/aklt/wt/H1_FIT/AKLT/Cert/H1Fit/`; experiments, logs, exact audit results and exports are under this report directory. CERT_H1, the manuscript, the data bundle and PalomarSubmission were read only. No sub-agents were used. The anatomy and initial candidate table were written during the first hour. Failed or superseded prototypes are archived here as `.lean.txt`, outside the submitted worktree, with a manifest in `archived-pilots.json`.

## Verifier contract actually used

I read `README.md`, `verification-profile.json`, `execution-profiles.json`, and `docs/launch-security-review.md` in the official PalomarSubmission checkout. The current README/security policy governs where the older launch review differs. Default resources are 16 CPU / 32 GiB; 19,800 seconds include setup, cache fetch, fresh full-repository build, export, mandatory Lean and NanoDa replays, and advisory con-ron. The 32 CPU / 64 GiB retry is conditional on validated failure. Every submitted Lean source must use `module` and have at most 10,000 physical lines; Challenge files also have the 1,000-line / 100 KiB limits. No verifier changes are proposed.

The local Comparator source fixes NanoDa at **four threads**, while a possibly serial Lean replay must still be budgeted. Our reproducible independent measurements use **one thread for each checker** to expose total work. They export full dependency closures of explicitly named pilot roots, plus the official primitive targets and permitted axioms; they do not export a completed Solution. Local capacity kills are not authenticated Palomar capacity declarations.

## Anatomy: what the 115 hours mean

`anatomy.json` preserves the producer forecast and a snapshot of 7,348 events / 5,885 latest successful modules. The **115.3546 CPU-hours are a producer forecast, not a completed full release measurement**. Times include import/elaboration and system CPU, not solely kernel reduction.

| Forecast stage | CPU hours | Share | Cause addressed by redesign |
|---|---:|---:|---|
| Constructor rows | 79.637 | 69.0% | Every row traverses the eight-site network and central insertions again |
| Local parameters | 15.304 | 13.3% | Repeated local moment/Pauli tables despite just 41 specifications |
| Gram rows | 8.513 | 7.4% | Scalar dot-product/residual loops; only 23-bit factors |
| Other stages | 11.901 | 10.3% | Literal elaboration, broad imports, layouts, coverage, assembly |

The snapshot has 890 constructor modules consuming 134,278 user seconds (median 37.285, maximum 981.93), and 1,468 Gram modules consuming 29,382 user seconds. `observed_by_kind` in `anatomy.json` gives every kind's module count, user/system CPU, median, maximum, and RSS. Broad semantic imports impose roughly 6.5 GiB even on trivial production leaves; observed snapshot maximum is 7.90 GiB, versus the brief's 9–11 GiB planning reservation. Narrow module-system computation leaves here import at roughly 0.4 GiB; semantic Mathlib proofs are around 0.8–1 GiB. Import closure is a real memory cause, separate from arithmetic intermediates.

| Entry/work statistic | Count |
|---|---:|
| Patterns / blocks | 7,962 / 12,173 |
| Matrix rows / full cells / lower-triangle cells | 144,554 / 4,742,248 / 2,443,401 |
| Factor lower-triangle entries | 2,184,033 |
| Scalar multiplications in the lower-triangle Gram check | 60,154,555 |
| Maximum matrix-entry / factor bit length | 56 / 23 |
| Direct-DD / factor blocks | 8,439 / 3,734 |
| Patterns containing a factor block | 2,432 |
| Maximum central block / exchange tensor dimension | 179 / 864 |

Factor blocks occur in **30.54% of patterns**. Only **276 blocks (2.27%)**, belonging to **240 patterns (3.01%)**, have dimension at least 64, but they contain **50.38% of matrix cells and 80.94% of Gram products**. The 52 blocks of dimension at least 100, in 52 patterns, contain 26.35% of cells and 56.62% of Gram products. Hard-tail information and entry-bit histograms are in `blocks.json` and `anatomy.json`. Big rational arithmetic is not the current hot loop: it already uses small integers and fixed denominators. Structural repetition, large retained kernel terms, and imports dominate.

Coverage is already pruned by `allowedCorners`, not a naive 2,048,000-completion loop. The current production representation has 500 axial frontiers / eight first-corner checks. Snapshot `coverage_frontier` events include distinct alternative implementations: 19 original/batched-leaf modules total 2,107.81 CPU seconds and 16 final Bridge modules total 2,825.53 seconds. These must not be added as if both were the final certificate. The forecast uses the final Bridge implementation. The 2,825-second coverage cost alone exceeds Level A. A faster raw-code/additive encoding is a future task, not a reduction delivered here.

## Constants and complete numerical search

`numeric-scan.jsonl` / `numeric-summary.json` cover all patterns in 388.6 seconds on one numerical thread. That first scan compares floating matrix reconstructions to the archive; the later **exact integer half audit**, described below, supplies exact matrix equality. Scalar tree-collapse calculations use exact Python fractions. Weighted-DD tests below are numerical searches, without claimed rational scaling witnesses.

| Common decrement of both H1 constants | Direct DD blocks | Positive diagonal scaling found | Fallback blocks after scalar + DD | Fallback full cells |
|---:|---:|---:|---:|---:|
| 0 | 8,439 | 9,350 | 2,964 | 3,900,872 |
| 0.0002 | 8,447 | 9,353 | 2,958 | 3,899,140 |
| 0.0005 | 8,451 | 9,370 | 2,955 | 3,898,891 |
| 0.001 | 8,475 | 9,400 | 2,950 | 3,898,218 |
| 0.005 | 8,639 | 9,566 | 2,838 | 3,882,666 |
| 0.01 | 8,803 | 9,786 | 2,739 | 3,864,441 |
| 0.05 | 9,710 | 10,675 | 2,152 | 3,751,160 |

At the original constants, **4,735 patterns** (1,553 straight, 3,182 turn) have exact scalar tree-collapse witnesses. This leaves 6,551 operator blocks; scalar plus direct DD leaves 1,722 patterns requiring nontrivial fallback. Even an inadmissible 0.05 decrement scarcely removes the hard cells. Schur/row-sum/Gershgorin variants therefore do not solve the hard tail.

The paper's actual H2 constraint was rebuilt in `h2-slack.json`: 916 memory-six windows, 115 orbit rows, 330 edges. Archived q is `1119948287353/1120437614225 = 0.9995632716486955`. Re-optimizing the Perron vector gives an approximate common-H1 decrement threshold **0.00042085154** for this automaton: 0.0004 contracts, 0.0005 fails. This is not a universal all-trail threshold; longer memory could change it and require new certificates.

For H3′, rho0 = 0.993015 gives margin 0.006985 in the infinite trail kernel. It is **not** an H1 decrement allowance. The final construction has rho = 0.9965075, B* about 2.1103469866646e12, and 1−theta about 1.6549411173e−15. The existential headline tolerates a tiny final gap, but q<1 and rho0<1 must still hold. A conservative continuity transport using the paper's `n*C*CV*q^n` majorant absorbs about **2.48e−14** common H1 decrement; this is a sufficient planning estimate with an unformalized coefficient-derivative bound, not maximal slack or a checked new H3′ witness. Practical weakening near 0.0004 requires re-searching H3′. `slack.json` / `experiments/slack.py` spell out the calculation. The selected design keeps both original H1 constants (.961 straight / .935 turn), so no slack or H2/H3′ re-search is needed for it.

## Candidate comparison after experiments

| Candidate | Measured or expected factor | What needs proof / numerical work | Risk / decision |
|---|---|---|---|
| Symbolic ladder/moment formulas once; no per-pattern operator construction | 19 compiled action families reduce hard row time roughly 2×; shared local cells 956× fewer. A fully direct multiplicity formula could do much more, but has no measured factor | Local moment and action refinement; ladder/recoupling entry theorem to avoid construction entirely. Direct SU(2) matrices still need generation | Local compilation alone misses both levels. No operator-free linked-pattern inequality found |
| Slack + scalar/Schur/row sums/Gershgorin | 4,735 scalar patterns; 9,350 weighted-DD blocks; decrement .0002 removes only six scalar+DD fallback blocks | Tree collapse, radius monotonicity, rational scaling; H2/H3′ re-search if constants change | Large matrices survive. Useful auxiliary route, not the fit |
| Extra geometric quotient / matrix sharing / full SU(2) reduction | D4 7,962→7,905 (<1%); matrices 12,173→8,580, or 5,569 after positive gcd. Exact factor duplicates reduce cubic work only 6.55%. SU(2) dimensions give about 11.5× fewer Gram products | Congruence/scale transport; highest-weight basis, completeness, direct reduced entries. Need actual rational matrices | Matrix sharing mostly removes easy work. SU(2) changes construction and is a major new proof project |
| Small integer / fixed dyadic / rigorous rounding | All 3,734 blocks admit the new uniform-error certificate; maximum factor 23 bits, precision 6. Packed eight-row hard pilot 0.82 CPU s | Generic convolution/no-carry, digit extraction and parallel interval tests, then `uniform_gram_posDef` | Strong Gram reduction; cannot fix constructors by itself |
| Shared local and half tensors, tensor-order sparse joins | 41 local types; half occurrences 199,258→7,797 keys→4,680 values. 8.38 MB shared words. Hard full operator finite-input replay 34.60 CPU s | Half composition, all-coefficient bounds, dilation, tensor/slab indexing, tree coverage and matrix decode | Best tested route. Planning constructor cost ~3,000 s, not 900 s |
| Uniform parameter family proved once | Scalar patterns reduce to 9 straight + 10 turn maximal radius triples, all 19 quadratics proved over [−1,1] | Connect scalar family to network H1; linked patterns need a uniform CP/order/SOS argument and a numerical search for it | Successful scalar family, no demonstrated family theorem covering linked hard patterns |
| Incomplete / low-rank Gram | Floating pivoted Cholesky needs ranks 142/179, 104/131, 144/179 on hard samples | Exact factor/residual recertification after rank truncation | Too little reduction to drive the redesign |

Full SU(2) character computations are exact: 38,405 multiplicity blocks, 1,350,510 cells, maximum dimension 59, and 5,240,823 Gram products if every block is factored. These are **dimension counts, not constructed/reproved reduced matrices** (`symmetry-and-rank.json`). Factor de-duplication gives 3,734→2,360 classes but cubic work only 347,916,746→325,122,191 (`gram-dedup.json`).

## Best method: exact evidence and mathematical certificate

A four-site open transfer operator has virtual dimension four and physical dimension at most 36. Check each distinct half/code once. Contract left and right halves only over nonzero virtual pairs. In tensor-factor digit order, full row/column indices `(iL*B+iR, jL*B+jR)` occupy packed digit `(iL*A+jL)*B²+iR*B+jR`. The right multiplicand stays small; logarithmic broadword dilation embeds the left operand. Two-left-row slabs bound retained intermediates. A balanced rectangle tree checks the selected central-sector entries against packed expected words, avoiding long-list random access and extracting short chunks before digit comparisons.

`half-audit.json` and `half-audit-blocks.jsonl` certify the numerical experiment's scope: **all 12,173 blocks, all 4,742,248 entries, zero imaginary part, exact equality to archived M**. Python/GMP constructs half words with unbounded integers; NumPy joins use exact int64 after checking an absolute-sum bound below 2^62. No floating arithmetic is used in this audit. It takes 66.55 seconds. This is independent computational evidence, not a Lean theorem.

`half-size.json` counts 7,797 half keys, 4,680 distinct values, 249,504 component slots but only 27,540 nonzero, 5,402 distinct absolute words, and **8,379,449 shared binary payload bytes**, versus 32,204,598 without word sharing. Largest word: 41,463 bits, split for export into 4,096-bit chunks. `coefficient-bounds.json` computes all-weight L1 coefficient envelopes: maximum half 27,987,000 (25 bits), maximum full threshold 198,470,610,542,848,000 (58 bits). Widths 32/64 suffice **after proving the generic envelope and no-carry lemmas**. Bounds concern all magnetic weights, not only saved central entries.

For Gram positivity, find integer L and positive g,d,S,delta with nonnegative epsilon such that

`|d*S²*M[i,j] − g*(L*Lᵀ)[i,j] − delta*1(i=j)| ≤ epsilon`, and `n*epsilon < delta`.

This implies strict diagonal dominance of `d*S²*M − g*L*Lᵀ`, then positive definiteness. `uniform_error_strictDD` and `uniform_gram_posDef` in namespace `AKLT.Cert.H1Fit` prove these mathematical implications. The new generator finds witnesses for **every one of the 3,734 factor blocks**, verifies every residual entry by exact Python integer products, maximum precision 6, maximum factor 23 bits, in 33.13 seconds (`uniform-gram-summary.json`, per-block work in `uniform-gram-profile.jsonl`). Floating eigensolvers/Cholesky propose factors only; exact residual verification determines acceptance.

A packed multiplication of the row-stack by a reversed factor row yields all row dot products. Parallel guard-bit tests check the uniform interval. Integer/factor/stack bounds and padding checks are present. The arithmetic refinement from these bit tests to the displayed mathematical inequality remains open. Eight-row packets eliminate repeated global checks and large closed-Boolean type conversions; independent replay confirms the improvement.

## Lean pilots and independent replay

All retained sources use `module`, finite heartbeat limits, structurally recursive Nat/Int/list/tree code, and the allowed kernel path. Exposed public definitions require `@[expose]` for reduction across modules. A few computation definitions use explicit inductive recursors and `noncomputable` because the code compiler cannot compile that recursion; Lean's kernel, not native code, checks them. No legacy H1 module can currently be imported by a new `module` file; the minimal existing Gram mathematical proof was ported locally to `GramTheory.lean` instead of editing the release tree.

Measurements are one-process user+system CPU / resident memory, including imports and elaboration unless explicitly called replay. They are not pure reduction microbenchmarks.

| Pilot | Lean source CPU s | Peak RSS GiB | Scope |
|---|---:|---:|---|
| P0010 sparse join | 0.25 | 0.404 | Whole easy central block, n=10 |
| P0100 sparse join | 0.39 | 0.476 | Whole easy central block, n=35 |
| P0711 sparse slabs, all 18 | 39.46 summed | 2.018 max | Whole hardest central block n=179, A=36/B=24 |
| P0711 half reconstruction | 16.05 summed | 0.55 max | All 14 required half/code operators |
| P0711 sparse schedule | 0.50 | 0.45 | 160 nonzero products equal compiled schedule |
| P0711 eight Gram rows | 0.82 | 0.712 | Matrix bounds, factor links/bounds and uniform error bits |
| P0049 eight Gram rows | 0.28 | 0.412 | n=25 representative smaller factor block |
| Shared local tables | about 32 summed | <0.8 | All 41 specifications |
| Scalar families | about 4 summed | <1 | All 19 universal quadratic inequalities |

P5420 (n=131) and P7237 (n=179) also pass representative two-row slabs. Gram samples n=25,66,91,131,179 pass rows 0/middle/last. Four-row slab pilots use up to 3.79 GiB; two rows are the delivery choice. These are representative easy/hard block samples, not all parity blocks of the selected patterns.

| Full root export | Bytes | Lean replay CPU s / GiB | NanoDa CPU s / GiB | con-ron |
|---|---:|---:|---:|---|
| `Pilot711.sparseFiniteInputs` | 8,471,523 | 34.60 / 1.738 | 104.23 / 1.242 | local capacity kill at 5.8 GiB after 40.38 s |
| `Gram0711Batch.checked` | 5,682,155 | 1.07 / 0.416 | 3.10 / 0.285 | local capacity kill at 5.8 GiB after 15.39 s |
| Earlier easy rectangle root | 5,359,729 | 0.62 / 0.125 | 0.32 / 0.025 | accepted, 8.45 CPU s / 0.130 GiB |
| Local tensor roots 32–39 | 5,436,124 | 10.86 / 0.419 | 8.62 / 0.216 | accepted, 34.01 CPU s / 0.671 GiB |
| Uniform-error mathematical soundness (full Mathlib closure) | 199,937,445 | 27.18 / 0.436 | 17.40 / 0.201 | accepted, 44.34 CPU s / 0.630 GiB |

Lean and NanoDa accept the complete pilot root closures. Large-case con-ron results are **inconclusive local capacity results**, not proof rejection, acceptance, or an authenticated Palomar exception. Its configured official cap is 30 minutes; these experiments use a tighter memory guard so the production lane has priority. Small factor-bound roots also pass all three checkers. The older unbatched Gram Boolean root cost 12.64 NanoDa CPU seconds versus 1.34 Lean; this shows the brief's historical 0.1–5× ratio cannot be assumed for a new checker. Current eight-row packets restore about 3× on this sample. Raw commands, full logs, SHA-256 and exact roots are in `replays/*/result.json`.

**Resource deviation:** the first unguarded whole-matrix Lean experiment peaked at 96,200,304 KiB (91.75 GiB) and failed Lean's maximum-numeral-size guard after 115.58 user + 44.00 system seconds. This exceeded the authorized 60 GB and is a limitation of this run. That approach was discarded. Every subsequent heavy pilot/checker uses a sampled 5.8 GiB process-tree RSS kill guard, Lean `-M5500`, core dumps disabled, and lowered scheduling priority. An address-space limit was unsuitable because Lean maps large precompiled libraries. Failed/over-cap sources are not among delivered Lean files.

## What is proved, and what is open

`declarations.json` lists **every exported theorem, exact source statement, path and line**; `axioms.txt` records `#print axioms` for each. The principal statements are:

* `bernstein_nonneg`: the three nonnegative quadratic Bernstein coefficients imply nonnegativity on [−1,1]. `scalarCheck_sound` connects its integer checker to that real quadratic. `ScalarFamilies` proves all 19 concrete instances. The network/tree-collapse bridge is still absent.
* `Local.tableCheck_sound`: accepted table lookup agrees with the explicitly calculated local table. `LocalTables00..05` prove all 41 closed table checks. The connection of this new encoding to the existing paper-level moments must still be wired.
* `natRowsMatch_sound`, `rectCheck_sound`, `rectTreeCheck_sound`, `tensorSlabCheck_sound`, `sparseSlabCheck_sound`: accepted checks imply their exact extracted-digit/rectangle specifications. They do not claim those digits are the paper's network entries.
* `Pilot711.sparseFiniteInputs`: `HalfCertificates ∧ compileProducts joinTerms = products ∧ SparseSlabCertificates`; includes all halves and all 18 two-row checks for block 0. This is not `H1Statement` or a positivity theorem.
* `factorBounds_of_link`, `packedFactorRow_of_link`, `gramBatchCheck_sound`: proved decomposition/transport of the smaller checks. The generated Gram packet theorem proves the Boolean packet accepts.
* `uniform_error_strictDD`: a radius epsilon < delta/n implies strict DD. `uniform_gram_posDef`: for symmetric integer M, arbitrary rectangular integer L and positive scales, that uniform residual bound implies positive definiteness over any RCLike field. It is a genuine mathematical soundness theorem, conditional on the displayed residual inequality, not on unproved packing hypotheses.

Representative axiom audit output:

```
'AKLT.Cert.H1Fit.uniform_error_strictDD' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1Fit.uniform_gram_posDef' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1Fit.scalarCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.Cert.H1Fit.rectTreeCheck_sound' depends on axioms: [propext, Quot.sound]
```

The exact closed open obligations are `AKLT.Cert.H1Fit.Obligations.BalancedDigits`, `.Dilation`, `.PackedDot`, `.PackedUniformError`, `.SparseScheduleRefinement`. These are **`def ... : Prop` only**, without proofs or axioms. Additional network refinement work is listed next. No theorem advertised as H1 assumes these unproved propositions, and no new H1 theorem is claimed.

## Full implementation and statement plan

1. Keep H1 constants and the headline theorem unchanged. Implement the all-operator route first; this can preserve `H1Statement`, `CertificateStatementV2` and `H1FiniteDataStatementV2` through a decoder/adapter that supplies their existing Gram/residual witnesses. Uniform error implies the current strict-DD criterion; no mathematical input weakening is needed.
2. Prove balanced digits, logarithmic dilation, no-carry convolution, factor-row reversal, extraction and parallel interval soundness. Prove coefficient envelopes from shared local tensors for **all** physical weights; assemble half composition and tensor-order/slab indexing. Prove rectangle leaves cover every required central entry, not merely that the supplied leaves match. Link decoded M/L and new metadata to `integerSectorMatrix` and the existing witness type.
3. Reuse the existing geometry, parity/basis, moment-polynomial, tensor-substitution, sector-linearity, rational-current, representative/mirror transport and enumeration mathematics. The affected production soundness leaves are `sectorPackingExpansion`, `sectorCoefficientBound`, `signedPacking`, `packingDecode`, `directRowsEntry`, `acceptedDecode`, `acceptedLookup`, `representativeWitnessLookup`; their new encoding refinements need real proofs. Keep `inputCovered`, `enumerationSoundness`, representative-code/lookup/classification transport; rebuild coverage with a narrow module closure and measure it. Production already has local consistency pruning.
4. Write a shared, content-addressed local/half/absolute-word catalogue generator, with checked index lookups and exact constructor witnesses. Generate sparse schedules once per compatible half pair/support family when possible; the current per-block schedule equality is a safe prototype. Shard by measured work/bytes, not by pattern count. Use two-left-row constructor slabs and eight-row Gram packets; group several small packets/theorems into modules to remove import floors while retaining <4–6 GiB. Generate direct-DD checks for the 8,439 easy blocks and packed uniform witnesses for the other 3,734.
5. Measure the full generator and all root closures before declaring Level B. Explicitly account for coverage, layouts, source elaboration, lookups, aggregation and export. Prove/check every literal table; a numerical audit is not a trusted input. Avoid duplicate full M tables by projecting Gram rows from rectangle words, or prove one shared encoding conversion.
6. If adding the scalar route, introduce a **new disjunctive finite input (V3)** or directly prove the paper's H1 from scalar/operator cases. A scalar norm proof does **not** supply the V2 per-pattern operator witness. Prove tree collapse and radius-family monotonicity, then exact coverage of its 4,735 patterns. The hard constructor work falls only about 5.4%, so do not delay the all-operator route for this optional optimization.
7. Update sec8/app-input-contracts' certificate-format description after proofs exist: shared halves plus uniform-error factors replace the old row construction/Bareiss-or-factor narrative. No mathematical thresholds change. No manuscript/Top files were edited here. Release must migrate **all** repository Lean files to `module`, split oversized sources, and validate the unchanged Challenge and Solution statements.
8. Run fresh entire-repository Palomar default-profile build/export/Lean/NanoDa/con-ron with H2 and redesigned H3′ included. A successful H1 pilot gives no conclusion about the rest of the package or authenticated con-ron capacity treatment.

## Budget extrapolation and remaining risk

`extrapolation.json` / `experiments/extrapolate.py` expose the assumptions rather than scaling only the hard pattern count. Exact global work: 8,297,235,999 product-weighted tensor cells versus 119,439,360 in the hard sample; 45,497 two-row slabs; 1,199,610 half-instance dimension-squared units; 93,614 factor rows, 48,570,903,040 packed Gram bit-work units, and 6,831,576 factor-guard cells.

Subtracting a 0.25-second per-module floor from the 18 hard sparse slabs gives about 2,429 seconds of full constructor arithmetic, plus ~356 seconds if 32 small slab checks share each future module and ~333 seconds for per-block sparse-schedule checks. This is a **model, not a verified upper bound**: current pilot modules are separate. Half dimension-squared scaling gives ~1,222 seconds; the two-point eight-row Gram calibration gives ~1,186 seconds plus packet/module floors. Timer noise, sparsity, different word sizes and accumulated proof environment can change all of these.

| Full H1 stage | Planning CPU seconds |
|---|---:|
| Shared local and half proofs | 1,000–2,200 |
| Constructor checks / schedules | 2,500–5,000 |
| Packed Gram | 1,000–2,500 |
| Direct DD and layout | 400–1,000 |
| Coverage | 2,850–4,000 |
| Data elaboration and assembly | 800–2,000 |
| **Total before replays** | **8,550–16,700 = 2.375–4.639 h** |

That is roughly **25–49×** below the 115.35-hour forecast. It is not the ~461× needed to reach 15 minutes, and it does not certify the ~38.5× reduction needed for Level B. Independent NanoDa remains about 3× Lean on the best hard packets; its four official threads may help wall time, but serial Lean replay adds another whole pass. The overall 19,800-second envelope still includes H3′, H2, proof tree and setup.

Literal payload is favorable: at 64-bit lanes the full M cells cost 37.94 MB, factor lower triangles at conservative 64 bits cost 17.47 MB, and shared half words 8.38 MB, about 63.8 MB before metadata. A duplicate standard M row encoding can add up to 37.94 MB. Decimal Lean source adds ~2.4× binary payload plus term overhead, so a **few hundred MB** is plausible; full export size is unmeasured and cannot be asserted ≤200 MB. Level B's 2 GB literal ceiling looks comfortable, subject to full generation/export. Maximum observed delivered leaf RSS is 3.79 GiB; the selected two-row method is ~2.02 GiB, but accumulation in a full Solution closure is unmeasured. Time, generic soundness and full export validation remain the blocking risks.

## Reproduction and delivered artifacts

Numerics run with `PYTHONDONTWRITEBYTECODE=1`, `PYTHONPATH=/home/ubuntu/aklt/reports/H1_FIT/vendor`, `OPENBLAS_NUM_THREADS=1`, `OMP_NUM_THREADS=1`. NumPy/SciPy/GMP support was installed only in this report directory. Original data/generators are never modified. Main scripts: `experiments/anatomy.py`, `scan.py`, `slack.py`, `bounds.py`, `verify_halves.py`, `half_size.py`, `gram.py`, `extrapolate.py`. Search and witness outputs are the JSON/JSONL files linked by name above.

Build and replay commands (from the H1_FIT worktree):

```
PYTHONDONTWRITEBYTECODE=1 python3 /home/ubuntu/aklt/reports/H1_FIT/experiments/build_candidate.py
PYTHONDONTWRITEBYTECODE=1 python3 /home/ubuntu/aklt/reports/H1_FIT/experiments/replay.py AKLT.Cert.H1Fit.Pilot711Sparse AKLT.Cert.H1Fit.Pilot711.sparseFiniteInputs --tag full-sparse-hard-block
PYTHONDONTWRITEBYTECODE=1 python3 /home/ubuntu/aklt/reports/H1_FIT/experiments/replay.py AKLT.Cert.H1Fit.Gram0711BatchCheck AKLT.Cert.H1Fit.Gram0711Batch.checked --tag packed-gram-batch
```

`build_candidate.py` builds only the delivered namespace in dependency order, using existing pinned dependency oleans. Direct Lean command uses `-j1 -M5500 -DautoImplicit=false -DrelaxedAutoImplicit=false`; no Mathlib build or `lake update`. Delete/move its report-only checkpoint to force another complete source pass. `run_pilots.py` records `/usr/bin/time` user/system/wall/RSS and the resident guard. `replay.py` uses the installed `leanexport`, `leanchecker --from-export`, NanoDa's permitted-axiom configuration, and `con-ron --verified --jobs=1`; exports/results bind measurements to exact SHA-256. The final **fresh source pass** compiled **145 modules / 425 explicit theorems** in **198.30 CPU seconds**, one process at a time, with **3.788 GiB** maximum RSS. Delivered source totals **7,112,459 bytes**, maximum **427 physical lines** per file. `build-validation.json` records every module, exact command options, source hashes and inventory; `axioms.txt` contains all 425 audits, with no axiom outside propext, Classical.choice and Quot.sound. No forbidden source construct was found. Dependencies were reused from their existing pinned oleans; this is not a fresh entire-repository Palomar build. Pilot timing tables retain their original measurement cohorts; later fresh-build CPU variation is visible in `pilots.jsonl`.

`final-replay-binding.json` records byte-for-byte re-export comparisons after this final source build, binding accepted replay measurements to the current source manifest. The mathematical soundness closure is approximately 200 MB of total JSON export, mostly imported theorem/type/proof declarations; it is not 200 MB of certificate literal payload. Full Solution export size remains open.

## ORCH-SUMMARY
- PARTIAL: neither Level A nor Level B is demonstrated; no new proved H1 statement.
- Complete anatomy and all-pattern crude-bound/slack search delivered.
- Shared-half exact audit matches all 12,173 blocks / 4,742,248 entries.
- All 3,734 factor blocks have exactly verified uniform-error witnesses.
- Shared half binary words: 8.38 MB; maximum coefficient envelopes fit 32/64-bit lanes.
- 145 source modules / 425 audited theorems rebuild in 198.30 CPU s; all files ≤427 lines.
- 41 local tables and 19 scalar quadratic families are kernel proved.
- Full hardest central block's halves and sparse slabs pass Lean replay and NanoDa.
- Hard full-input replay: 34.60 Lean / 104.23 NanoDa CPU seconds, <1.8 GiB.
- Eight-row hard Gram packet: 0.82 build / 1.07 Lean / 3.10 NanoDa CPU seconds.
- Mathematical uniform-Gram soundness passes all three checkers (full ~200 MB closure).
- Small con-ron pilots accepted; large packed pilots hit local 5.8 GiB capacity guard.
- Open: Obligations.BalancedDigits, Dilation, PackedDot, PackedUniformError, SparseScheduleRefinement.
- Open: coefficient bounds, network/half refinement, tensor/slab indexing, coverage and V2 adapter.
- Full H1 planning range 2.375–4.639 CPU-hours before replays; not a Level B guarantee.
- H3′ and full proof tree still need independent budget reduction/validation.
- One initial unguarded pilot exceeded 60 GB; discarded; subsequent work guarded.
- Decide whether to fund the packed Level B route or a deeper uniform/SU(2) construction redesign.
- All sources isolated in AKLT/Cert/H1Fit; production/data/manuscript/verifier untouched.
