STATUS: PARTIAL (phase-5 structured-potential search in progress)

## Phase 3

The source-only merge handoff and the complete five-case finite numeric run are delivered. No written mathematical leaf proof was added. The finite Top targets remain conditional on the 56 closed mathematical leaf Props, as required by the author's first-attempt rule.

### Merge set — ready first

[merge-set.txt](merge-set.txt) lists the exact handwritten source files to copy, and [leaves-open.json](leaves-open.json) lists only the 56 real closed-Prop proof obligations in the requested format. A small [source archive](phase3/merge-set-sources.tar.gz) and [file hashes](phase3/merge-set-hashes.json) preserve the handoff. No generated graph literal, potential block, numeric check or case aggregation is included in the merge set.

Build the handwritten root with `lake build CertData.H3.Core`, or the optional library with `lake build CertData`. `CertData.lean` imports only that handwritten root. The optional library's glob selects this root rather than all generated descendants. Generated modules attach later under `CertData/H3/`; their explicit final root is `CertData.H3.Bridge.All`. The twelve small kernel modules were moved under `CertData/H3/Kernel`; the old public `AKLT.Cert.H3` declaration names are preserved for compatibility with previously proved helpers. There are **zero new Lean source files in the ordinary AKLT library**, and its default target/glob is unchanged.

A clean source closure from main `568d1244a898e01b1c3d365c7ab50392ee67d2c6` plus the merge set compiled **50 modules in 86.31 seconds**, at three processes, without generated H3 data/checks. All 56 closed Props type-checked. The separate writer audit checked all **28 exported handwritten theorems**, with only the permitted axioms. Evidence: [clean receipt](phase3/clean-merge-receipt.json), [writer axiom audit](phase3/writer-axioms.json), [merge policy audit](phase3/merge-policy-audit.json). Mathlib was prebuilt; every project dependency in this clean closure was compiled from main source.

The worktree itself was not merged, and no statement source was copied into it. Its older/missing statement files are recorded in [statement-main-check.json](phase3/statement-main-check.json). Main's seven relevant final statement sources match the accepted pilot's source text byte-for-byte; the final latest-main comparison is [here](phase3/final-main-comparison.json). Thus the merge set uses the actual final V2 layer on main, rather than repairing local foreign files.

The data-dependent graph interface was factored through the handwritten `PackedGraph`, `RawReceipt`, `RepresentativeReceipt` and `FieldReceipt` definitions. Seven formerly concrete leaf statements now quantify their graph/storage/receipt arguments: `SpanDataLeaf`, `ClassDataLeaf`, `QuotientDataLeaf`, `UnmaskedDataLeaf`, `FieldJoinLeaf`, `RawShardJoinLeaf`, `RepresentativeJoinLeaf`. `DecodeDataLeaf` is unchanged. Their exact current declarations are in `CertData.H3.Bridge.Production`; all are closed Props. This statement revision removes generated imports, and is explicitly flagged in the writer handoff. The generic assembly theorems accept kernel-produced receipts, with the final generated composition attaching the actual five datasets.

### Complete finite production

The full run also rebuilt B1 so every case uses the same isolated module paths and graph-storage interface. The exact checker arithmetic and potential values are unchanged. The production command was:

```sh
H3_REPORT_DIR=/home/ubuntu/aklt/reports/CERT_H3/phase3   python3 AKLT/Cert/H3/production.py build --cases B1 B2 C1 C2 C3   --jobs 32 --ram-gb 270 --process-gib 48 --timeout 3600 --resume --compact-sources
```

**All 5,035 of 5,035 generated modules have a successful kernel-check exit and a retained olean.** All **2,741 exported check/assembly theorems** in the production manifest have matching axiom receipts, with no disallowed axiom and no missing print. The final `CertData.H3.Bridge.All.stationary_from_leaves` is now kernel checked; it concludes `AKLT.Blueprint.Top.StationaryCheckStatementV2` from `AutomatonBridgeLeaves ∧ ProductionCaseLeaves`. It remains conditional on those mathematical leaves.

| Case | Modules | CPU hours | Prefix tails | Closed paths | Ceiling |
|---|---:|---:|---:|---:|---:|
| B1 | 968 | 3.351 | 89,150 | 937 | 351207554 |
| B2 | 968 | 4.346 | 103,257 | 922 | 290599163 |
| C1 | 968 | 3.978 | 66,947 | 715 | 527872005 |
| C2 | 968 | 3.317 | 99,168 | 1,036 | 380754375 |
| C3 | 968 | 3.939 | 92,748 | 861 | 273048088 |

Shared modules: 195. Total successful-module CPU: **19.455 hours**. Peak process RSS: **20.10 GB**; maximum sampled aggregate RSS across the runs: **209.53 GB**. The final resumed scheduler completed in **2752.81 seconds (45.88 minutes)**. The sampled elapsed spans of all production attempts total **70.17 minutes**, including the rejected/import and stopped/scheduling attempts. The 32-process ceiling is subject to the 270 GB reservation limit; no 32-process concurrency or speedup is assumed when memory reservations prevent it. Other proof writers were active. Exact per-module elapsed/CPU times, commands, hashes and statuses are in the receipts below. The receipt also records elapsed sample spans for every attempted/resumed run.

Each case contains all 14,964 spatial planes and endpoint rectangles, all 234 real packed row shards, all 256 depth-eight weighted prefix shards and its early-hit check, count/ceiling summary and case assembly. The shared automaton covers all 4^10 raw codes, all 3,741 representatives and unmasked fields, exact supplied-table equality, and all edge counts. The exact coefficient table is checked against Defs. No native computation supplies a proof; all finite proofs use `decide +kernel`, and the other new proofs are assembly glue.

One first packaging attempt stopped when Lean rejected an old module import left after a long catalog import list. All five affected catalog imports were corrected and audited, then the run resumed from already checked modules. The memory-aware scheduler was also stopped and corrected to drain capacity for a higher-priority catalog instead of indefinitely backfilling smaller data jobs. The corrected run resumed checked modules immediately; no numeric result or mathematical statement was changed to bypass either issue. The append-only measurements ledger retains both the failed attempt and all final successful receipts.

### Receipts and storage

- [production-receipt.json](phase3/production-receipt.json): exact module totals, CPU/RSS/storage and no-failure summary.
- [production-modules.json](phase3/production-modules.json): each exit status, command, source/olean SHA-256, elapsed/CPU/RSS and axiom output.
- [production-axioms.json](phase3/production-axioms.json): every generated theorem's axiom list.
- [production-inputs.json](phase3/production-inputs.json): all six actual data-input hashes, rechecked against the generator manifest.
- [build_runs.jsonl](phase3/build_runs.jsonl), [measurements.jsonl](phase3/measurements.jsonl), [memory_samples.jsonl](phase3/memory_samples.jsonl): append-only runtime evidence.
- [compacted_sources.json](phase3/compacted_sources.json): source/olean/archive hashes recorded before each completed-case literal source deletion.

Compaction removed **2,340 plane/endpoint literal source files** only after each complete case assembly succeeded. **Every check olean is kept**, together with every other production olean needed to import the final assembly: 31.57 GB in total. Owned worktree plus scratch storage is 31.90 GB, below 60 GB. Root free space at verification is 434.80 GiB, above the enforced 100 GiB threshold. No data archive, checker source, assembly source or proof source was compacted.

To verify the delivered finite work again without regenerating literals:

```sh
H3_REPORT_DIR=/home/ubuntu/aklt/reports/CERT_H3/phase3   python3 AKLT/Cert/H3/production_receipts.py
```

The phase-1 and accepted phase-2 design, numerical forms, proof-body preservation audit and earlier timing evidence remain available through [accepted phase-2 report](phase3/accepted-phase2-report.md), [original phase 1](phase1/report.md), [module relocation](phase3/module-relocation.json), and [retained proof audit](phase2/retained_proof_audit.json). The current path and statement authority is the phase-3 merge set and leaves-open handoff. The twelve relocated kernel declaration namespaces are a deliberate compatibility exception; no new written leaf proof was made during their relocation.

Remaining work is mathematical: assign first attempts for the 56 closed Props to other cheaper models, then inhabit the assembly premises. There is no remaining finite numeric case to run. H1 is outside this lane and is not claimed.

## phase 4 — fit

**Verdict: only a partial fit through engineering, roughly an 8–11× reduction in total Lean build CPU as a planning range. H3′ does not yet meet the proposed share.** The two new real-data micro-pilots pass the stock exporter, fresh Lean replay, con-ron and NanoDa within 6 GiB. The archived potentials still imply about **14.33 GB of decimal literal payload** with compact uint32 packing, before expression metadata. Reaching 300 MB needs another **47.8×** reduction in that payload. A new structured potential, or a substantial change in the available verification budget, is needed; the larger approved profile does not remove this serialization problem.

This phase is a completed design and micro-pilot study. It does not rebuild production, modify main, or prove new mathematical leaves. The accepted phase-3 production, merge set and 56 leaves remain unchanged. Their source hashes were rechecked in [prior-merge-set-unchanged.json](phase4/prior-merge-set-unchanged.json). The previous report, including its original summary, is preserved [here](phase4/report-before-fit.md).

### Verifier contract and experimental boundary

I read the four requested files in the read-only official PalomarSubmission checkout, and its checker revision pin. The checkout commit, document hashes and executable hashes are recorded in [verifier-pin.json](phase4/verifier-pin.json). The con-ron used for the final pilots is **4.36.0-rc1**, SHA-256 `4e5616d94374cae37324dad2594f6230c2bb2297240249fc78ff508f3bc5acef`, matching the official override for this Lean toolchain. Lean, leanexport, leanchecker and NanoDa remain 4.35.0-rc2.

The relevant constraints are one 19,800-second allowance for preparation, fresh project builds, export/comparison, required Lean and NanoDa acceptance, and the advisory con-ron attempt; 350-minute job timeout; default 16 CPU/32 GiB; 95%/98% host memory thresholds; at least 20 GiB free workspace. The 32 CPU/64 GiB retry requires authenticated, validated resource evidence. Our locally killed controls do not authorize that retry. Con-ron has a 30-minute cap inside the allowance; its recognized capacity decline is not an acceptance. Concatenating shard receipts does not replace the Comparator's full Solution export.

Every submitted `.lean` file, including unused experiments and generated files, needs a `module` header and at most 10,000 physical lines. Challenge files also have the 1,000-line/100 KiB limit. The old production modules are not ported by this study. Lean actually rejected importing an old non-module checker into a new module, so this requires a real module/visibility port, not just a header insertion. All **70** Lean sources currently under `Fit/` have headers and satisfy the line limit; [source-audit.json](phase4/source-audit.json) records their hashes and a clean forbidden-token scan. They are not attached to the ordinary AKLT target.

Only `Fit/` and the report directory were changed. Old import controls were run on stdin, using existing built production dependencies; no Mathlib build or package update occurred. Numerical searches use Python/NumPy under `Fit/`; their results are never proofs. Lean measurements use fresh processes and `decide +kernel`. New mathematical obligations are only closed Prop definitions. The study's fresh processes were bounded, with build pools of at most three workers and separately bounded replays, scheduled within the eight-process/60 GB study limit; no production scheduler was launched. The final storage receipt is [disk-receipt.json](phase4/disk-receipt.json), below the 60 GB ownership limit and above 100 GiB free on `/`.

### Where the 19.455 CPU-hours went

These are successful-module process CPU totals from the accepted receipts, not 19.455 hours of isolated kernel reduction. In particular, reading literals and loading imported environments dominate several stages. Full details by every stage are in [stage-costs.json](phase4/stage-costs.json).

| Stage | Modules | CPU hours | Peak RSS, GiB | Oleans, GB | Main cause |
|---|---:|---:|---:|---:|---|
| Spatial plane data | 1,170 | 10.887 | 6.880 | 14.991 | Interpreted hexadecimal elaboration, plus the large common import |
| Endpoint data | 1,170 | 2.043 | 6.788 | 0.583 | Same common import, then redundant projected literal data |
| Bellman/auxiliary row checks | 1,170 | 2.227 | 12.264 | 0.015 | Imports of an entire case, routing/masks, products and guard checks |
| Weighted prefixes | 1,280 | 3.516 | 15.580 | 0.024 | Replayed stems, list geometry, exact phase products, endpoint lookup |
| Raw automaton coverage | 64 | 0.362 | 9.983 | 0.001 | Length-ten bond-trail traversal and invalid-span checks |
| Representatives and fields | 118 | 0.143 | 6.892 | 0.001 | Mostly process/import cost; some replay and field decoding |
| Plane catalogs | 5 | 0.075 | 14.102 | 15.163 | Entire-case indexes and duplicated serialized compilation material |
| Endpoint catalogs | 5 | 0.069 | 7.777 | 0.758 | Entire-case index/compilation material |
| All other bindings/assemblies | 53 | 0.133 | 18.721 | 0.040 | Imports, finite joins and final all-case environment |
| Total | 5,035 | 19.455 | 18.721 | 31.573 | |

The last stage count includes the remaining manifest jobs; byte totals are rounded. The recorded peak 20.10 GB is 18.72 GiB. Literal/index duplication in old non-module oleans is a storage/import cost; the exporter can share identical literal expressions, so it is not automatically a second copy of every literal in the final export.

Fresh controls on the same twenty real B1 keys separate the costs more directly:

| Control | Total CPU seconds | Profiled reduction/type-check seconds | RSS, GiB |
|---|---:|---:|---:|
| Old Model import and trivial computation | 5.58 | negligible | 6.472 |
| Old graph and full B1 Tables import | 6.30 | negligible | 7.866 |
| Old local Bellman checks, 20 rows | 6.76 | 0.474 | 8.060 |
| Old full plane checks, 20 rows | 7.14 | 0.761 | 8.210 |
| New compact, chunked full checks, 20 rows | 0.78 | 0.536 | 0.598 |

The old controls' exact commands/sources are in `Old*.json` and `Old*-legacy-control.txt` under `phase4/`; [legacy_costs.py](../../wt/CERT_H3/Fit/legacy_costs.py) reproduces them. The new row checker includes caps, free rows, centre/target values and the endpoint rectangle, so the last comparison is not based on omitting those checks. These controls are not a measurement of the entire clean repository. Using a 3.5–5.6 second historical/current import envelope on 5,035 processes suggests roughly **4.9–7.8 CPU-hours** of repeated startup/import work; that is an attribution range, not subtraction of a universally constant baseline.

There are **74,820 planes × 19,881 sites = 1,487,496,420 values** across five cases. The current 80-bit lane representation occupies 14.875 GB of mathematical binary payload, about 29.75 GB of hex source characters or 35.82 GB of decimal export characters. The separately stored 625-site endpoint rectangles add 0.468 GB binary / about 1.126 GB decimal, before names and indexes. Most entries have many unused lane bits: archived values are below 2^26. Caps, coefficients and expected prefix sums are tiny compared with the planes. Graph pages/dense class data are only a few MB, but their single giant Nat literal is a separate serial conversion hazard. See [literal-volume.json](phase4/literal-volume.json).

Per row the old code regenerates four pulls, masks, several response masks, scalar products, every term's range checks, and the U≤Z/free/terminal/rectangle checks. Some are shared during one reduction, but each new module imports and starts its caches again. Per prefix module it replays all its depth-eight code slots, including invalid slots; surviving stems repeat the first eight transitions and then enumerate the suffix. Each prefix imports the whole case endpoint catalog even if it has no surviving stem. The new pilots remove this large dependency, rather than interpreting an empty shard as zero-cost data loading.

### Two measured routes

All figures below are wall seconds / sampled RSS GiB. Checkers use two workers. They include parse/install overhead, so their ratios to a subsecond row reduction are not pure arithmetic multipliers. Exact process CPU, command lines, exit statuses, axiom prints, export hashes, safety scans and largest literals are in [micro-summary.json](phase4/micro-summary.json). All three rows below have successful normal builds, **stock** exports, fresh Lean replay, con-ron and NanoDa acceptance.

| Pilot | Lean build | Kernel/type-check part | Stock export | Fresh Lean replay | con-ron | NanoDa | Export MB |
|---|---|---:|---|---|---|---|---:|
| Real B1 P0106, bitsets + blocked sparse endpoints | 17.92 / 2.470 | 16.9 s | 1.72 / 1.596 | 15.29 / 1.819 | 50.64 / 3.545 | 22.32 / 1.388 | 1.601 |
| 20 full real rows, 32-bit storage, 8192-bit literal leaves | 0.81 / 0.598 | 0.536 s | 16.49 / 1.604 | 6.54 / 0.412 | 16.99 / 0.445 | 26.16 / 0.230 | 16.587 |
| Same rows, 1024-bit literal leaves | 1.71 / 0.659 | 1.34 s | 10.55 / 1.624 | 8.14 / 0.471 | 22.10 / 0.623 | 26.23 / 0.298 | 29.133 |

`#print axioms` for `Fit.PrefixBlocked.checked`, `Fit.FullRows32Expr.checked` and `Fit.FullRows32Small.checked` prints `[propext]`. All exported definitions in these exports are safe. The included primitive roots permit only the three allowed axioms. NanoDa's pretty-printer message “Unable to print axioms” accompanies “no typechecker errors” and exit zero; it is not counted as a rejection or ignored type error. This is an isolated micro-pilot, not an authenticated Palomar run of the full Solution.

**Rows and literal loading.** [Rows.lean](../../wt/CERT_H3/Fit/Rows.lean) is an Init-only executable checker. Store uint32 lanes. Mask even and odd slots to obtain two interleaved 64-bit guarded planes, instead of expanding every field to 80 bits. Coefficients are `ceil(C48/2^16)`, so a 32-bit-scale inequality implies the required 48-bit-scale inequality. All no-carry and lane bounds remain Boolean checks. A native exhaustive B1 test passed **297,499,284** spatial inequalities at this stronger scale, and all **14,964** free-cap inequalities passed; this is numerical evidence for the encoding, not a kernel proof of a new complete case. Other four cases were not rerun at the new scale.

The twenty keys cover all four phases, low/high class indices and all three step kinds; their 69 actual source/target planes come from the archived B1 potential. `fullPlane32` includes centre/target pins, known initial-bond routing, boundary caps, cap domination, positivity/range, free rows and the real 25×25 endpoint extraction. Representation/routing soundness to Defs remains open. The potential values and prefix ceiling themselves are unchanged.

The real original 64-plane source group, loaded through the native-compiled balanced elaborator, takes **2.13 seconds / 0.89 GiB**, versus roughly 30 seconds previously. A direct enormous `0x` token timed out at 120 seconds: standard numeral syntax is not the fast loader. Native compilation is solely untrusted parsing of source data into ordinary kernel-visible terms. It does not run a checker or create a proof.

The final [Literal.lean](../../wt/CERT_H3/Fit/Literal.lean) emits balanced `Nat.add`/`Nat.shiftLeft` expressions whose numeric leaves are at most 8192 or 1024 bits. The kernel checks the resulting expressions. Constructing the expression natively restored the 69-plane data build to **2.43 seconds**, compared with **8.67 seconds** for elaborating explicitly written chunk arithmetic. The 8192-bit final export scan confirms its maximum Nat literal is exactly 8192 bits. The 1024-bit variant saves stock serialization time but makes the export 1.76× larger and the row reduction about 2.5× slower; it is not an unconditional improvement.

**Prefix.** [Prefix.lean](../../wt/CERT_H3/Fit/Prefix.lean) uses a 625-position rectangle, a bond bitset and once/twice departure bitsets. Position index is `(x+13)*25+(y+12)`; the centre is 337, B target 362 and initial position 312. Bond IDs use two forward orientations; reverse moves refer to the same bit. Raw memory remains twenty bits. The checker replays exactly the same depth-eight stem codes, preserves first-direction/first-hit rules, and computes exact phase and short-hit integers. A balanced table of blocks of at most 64 entries stores only endpoint keys actually needed by that shard; each value packs four uint32 values. The largest B1 shard's result is exactly the accepted production result: **7,459 nodes, 4,822 tails, 7 short hits and 77 surviving stems**. The generator asserts equality of every result field against the accepted manifest.

The previous same-shard Lean measurement was 93 seconds / 15.35 GiB. The new 17.92 seconds / 2.47 GiB gives about **5.2× total-time** and **6.2× RSS** improvement. Its endpoint dependency export falls from about 248 MB to 1.60 MB for this shard. Across complete cases, this is not a claim that 1.60 MB suffices for all endpoints: counting all required sparse entries forecasts about 20–25 MB of endpoint literal digits, plus tree/definition metadata, across five cases. A unified chunk store could make the prefix's value function and the row's packed view refer to the same data, eliminating this duplicated endpoint witness and its extraction checks. That canonical-view implementation and its refinement proof are not delivered as production here.

### Replay hazards found by measurement

1. **Multiplication order matters.** con-ron exceeded the 6 GiB cap in 16.4 seconds on the real `coefficient * plane` primitive control. `plane * coefficient` passed in 11.27 seconds / 0.12 GiB. A 20-row compact check with the old operand order timed out at 240 seconds; the swapped checker passed in 21.55 seconds. The final full checker passed in 16.99 seconds. Do not assume Nat multiplication's mathematical commutativity implies equal replay cost. `SwapSound` is an open Prop, not a proof written here.
2. **One giant literal breaks the serialization path.** Two widening identity controls had 38.8/86.9-second stock exports; con-ron timed out at 300 seconds or hit 6 GiB, although NanoDa accepted. Unchunked real row exports also timed out during fresh Lean replay after 120 seconds, at about 0.11 GiB. Their low RSS and the chunked controls identify decimal parsing as a serial bottleneck. The final chunked versions pass fresh replay in 6.54/8.14 seconds. Only the final chunked pilots support a stock-tool claim; earlier `-fast` receipts used the separately identified REL_FEAS serializer.
3. **Large modulo and widening are poor substitutes for direct views.** A million-bit modulo control timed out at 45 seconds in con-ron; an equivalent masked control passed. Replacing dense masks by sparse subtraction did not fix the old multiplication order. Broadword widening is successful in Lean and NanoDa but is not the selected replay route.
4. **Auxiliary work cannot be omitted from the forecast.** The local-only compact row sample takes NanoDa 5.74 seconds, while the full sample takes 26.16 seconds. The extra work includes cap domination, free/range/pin checks and rectangular endpoint extraction. I have not isolated a single dominant auxiliary operation, and do not use the local-only number as the full-row replay forecast.

### Reduction options, including numerical searches

Factors apply to the stated component; overlapping factors must not be multiplied blindly. “Estimate” means no complete-case measurement supports it yet.

| Option | Expected saving | Proof/search needed | Risk / evidence |
|---|---|---|---|
| Init-only Boolean kernels; statement bridge in separate modules | 4–10× process/import component; remove 6.5 GiB baseline | Port module visibility and connect checker to existing closed semantic leaves | Demonstrated at <0.6 GiB for full checks; whole library still needs its port |
| Native balanced data elaborator | About 15× plane-loading time | No trusted parsing lemma: emitted Nat expressions are checked | Demonstrated on the real original 64-plane group |
| Private meta imports; hide witnesses behind public case theorems | About 0.3 GiB/check process; lower startup | Correct public/exposed interfaces, existential case assembly | Demonstrated private check baseline; full export still contains witnesses |
| `noncomputable def` for certificate data/views | Avoid unnecessary runtime IR and duplicate catalog compilation material | No mathematical change | Small CPU improvement, large IR saving; does not remove mathematical literal payload |
| Local/grouped indexes; no monolithic repeated catalogs | Remove unnecessary case loading; possible ~2× olean/IR storage saving | Lookup coverage/refinement | Old catalogs alone are ~15.9 GB; final replay cannot hide required data |
| 32-bit storage, even/odd 64-bit guard views, 32-bit ceilings | 2.5× literal payload; comparable row arithmetic | Parity, ceiling strengthening, packing/routing soundness | Full micro passed all kernels; only B1 new-scale exhaustive native test |
| Phase-specific/adaptive widths, 26–28-bit storage | Further ~1.1–1.5× payload, estimate | Cross-width routing and new no-carry bounds; test all cases | 26-bit coefficient rounding passed the 127-state sample; 24-bit did not |
| Chunked literals, balanced native Expr construction | Removes giant-literal parse/render failures | No trust in the encoder; ordinary kernel expressions | 8K/1K pilots pass stock tools; per-literal metadata/assembly tradeoff measured |
| Put large operand first in multiplication | >11× censored row replay comparison; prevents a measured OOM | Small closed commutation/equivalence obligation | Demonstrated; not a volume saving |
| Check plane bounds once; derive routed-term bounds | About 1.1–1.3× row arithmetic in the pilot | Mask/pull bound preservation, global no-carry proof | Local full vs fast 0.396/0.339 s; do not drop bounds without proof |
| Share four-phase routing, free rows and masks | 1.2–2× row stage, estimate | Algebraic shared-view refinements | Not implemented/measured as a complete combined-phase checker |
| Larger data/row batches with several bounded reductions per module | 2–4× startup count, not arithmetic | Generalized interval joins and coverage | Tune ≤6 GiB; a long single reduction still retains caches |
| Work-based prefix frontier intervals, including replay work | Fewer empty/light modules at same maximum work | Existing interval coverage plus new replay refinement | Scheduling is untrusted; count all invalid code slots and early hits |
| Bitset geometry and blocked sparse endpoint tables | About 5× prefix CPU, 6× RSS; >40× endpoint literal reduction forecast | Position/bond encoding, step/refinement, sorting and frontier joins | Actual largest B1 shard passes three replays; semantic leaves open |
| A single canonical chunk store for C.value and packed rows | Remove endpoint data duplication and projection verification | Generic chunk lookup/reassembly and Defs view | High-priority engineering next step, not implemented end to end here |
| Bitset raw automaton; larger representative/field batches | 2–5× raw arithmetic and far fewer small processes, estimate | Raw walk/reflection/quotient refinement, same supplied table binding | Shared graph stage is only ~0.5 h of the old total; cannot solve volume |
| Smaller Nat chunks or spatial tiles used directly in checks | Faster stock conversion; may improve bounded arithmetic | Tile halos, boundary/known-site coverage | 1K literals worsen row CPU and NDJSON size; spatial tiling not measured |
| Delta/block-base/adaptive literal compression | Perhaps 1.5–3.5× payload, estimate | Verified reconstruction or define C directly by reconstructed terms | B1 lossless horizontal-delta zlib is 366 MB/case; still far above the total share |
| General LZ/Huffman/gzip decoder inside the kernel | Potential file saving | Verified decoder plus decoded-view refinement | Must expand ~1.49 billion values; likely trades bytes for prohibitive reductions. Native decompression cannot supply a proof |
| Outward-rounded fixed-denominator prefix weights | 2–5× arithmetic part, perhaps 1.1–2× whole prefix, estimate | Interval arithmetic and weighted traversal upper-bound soundness | Native B1 48/64/80-bit tests preserve the frozen ceiling; no Lean timing yet |
| Shorter prefix or smaller memory | Potential 3–10× prefix / fewer states | A lifted supersolution and a bound for the actual fixed length-12 Defs expression | Not a drop-in substitution: supplied memory ten and exact prefix twelve remain fixed |
| Smaller explicit spatial box with an analytic outer barrier | Roughly square of radius ratio for table size | New outer supersolution, interface shell and boundary proofs; re-search | Archived R50 B/north gives ~0.620 rather than 0.351: simple radius reduction fails |
| Coarser grid/interpolation of current potentials | Nominal 4–16× data | Re-search/repair a supersolution; rounding-error bounds | Direct stride-2/4 interpolation fails millions of sampled inequalities |
| Stronger value quantization | Save low value bits | Re-search and full row/prefix checks | Rounding to multiples of 4 or 16 fails many rows; even a passing row quantization can lose the 1e-9 prefix ceiling |
| Exact spatial/state symmetry | About 2× B/west case; only **1.110×** all-case data | Quotient automorphism, isometry, min-supersolution closure, folded lookup | A concrete B2 candidate is numerically successful below |
| Merge/dominates phases or use a coarser auxiliary automaton | Perhaps 1.3–4× data, estimate | New invariant cone/dominance and lifted Bellman operator; new search | Most archived C/D planes are distinct; merging can increase the very tight prefix bound |
| Low-rank/separable potential plus certified correction | Potentially 20–100× data | New integer search, correction margin, nonnegative basis/shift bounds | Promising scale, no valid complete candidate; signed SVD is not a certificate |
| Piecewise analytic/Bernstein/exponential barrier with a small inner patch | Potentially >50× data and far fewer inequalities | New search and coefficientwise sufficient positivity theorem | Best mathematical direction for the volume target; substantial new proof work |
| Define C by iterations/resolvent of a small operator instead of literals | Eliminate stored planes | Monotonicity plus enough verified iterations and the fixed prefix bound | Naive replay multiplies plane work by hundreds; compression alone does not make this cheap |

The archived B1 survey has **14,962 distinct planes out of 14,964** and no value equal to its outer cap. Only one A/B pair and one C/D pair are identical. Thus simple whole-plane deduplication, deleting cap-valued outer regions, or identifying phases does not save an order of magnitude. The B1 gzip-equivalent native compression was 498 MB; horizontal delta compression was 366 MB. These are file-compression measurements, not lower bounds on all possible encodings. See [B1-survey.json](phase4/B1-survey.json).

Additional numerical outcomes, all outside Lean:

- [row-search-all.json](phase4/row-search-all.json), [free-caps32.json](phase4/free-caps32.json): all B1 spatial/free-cap inequalities pass 32-bit coefficient ceilings. [row-search-initial.json](phase4/row-search-initial.json): 24-bit ceilings fail 47,098 of 10,099,548 sampled inequalities. The later 26/28/30/32-bit sample passes. Rounding values upward to a grid of 4 fails 83,917 sample inequalities even at 32-bit coefficient precision; a grid of 16 fails 3,361,057.
- [geometry-search.json](phase4/geometry-search.json): preserving the inner 25×25 region but interpolating the exterior from stride 2/4 grids fails 3,596,610 / 3,241,322 of the 10,099,548 sample inequalities. This was integer upward-rounded interpolation, not an unsafe floating check.
- [low-rank-survey.json](phase4/low-rank-survey.json): signed rank-64 fits on 128 states × 1296 sites have maximum value errors about 14.90, 10.26, 3.72 and 3.82 units in A/B/C/D. Rank 32 errors are much larger. This is a small approximation diagnostic, not positivity, residual domination or validation at unsampled points. A low-rank route needs a new supersolution search and a certified correction, not truncation of the SVD.
- [prefix-search.json](phase4/prefix-search.json): reference length-10/11 B1 expressions evaluate to 0.351048868 / 0.351175592, versus length-12 0.351207553504119. These smaller numbers do **not** prove the target: the fixed statement asks for the length-12 expression, and domination is not available at those earlier starts. The supplied memory-nine archive similarly needs longer prefixes and radius 80; it cannot simply replace the fixed statement's data.
- [dyadic-search.json](phase4/dyadic-search.json): outward rounding each phase update to a fixed 48-, 64- or 80-bit fractional denominator still passes B1's length-12 ceiling. Increases over the exact reference are `1.46467e-10`, `2.25089e-15`, `3.06015e-20`. This search keeps short hits exact, so it isolates fixed-width surviving weights. A Lean version and its upper-bound proof remain open; other cases were not tested.
- [symmetry-search.json](phase4/symmetry-search.json): y-reflection induces an involution on all 3,741 quotient classes, with raw-code and graph equivariance checked natively. For B/west, take the pointwise minimum of the archived potential and its reflected state/spatial potential, including caps. 2,630,956 values decrease by one. Its exact-prefix bound is **0.290598941482699**, below the original 0.290599162822789 and frozen ceiling. Store 71 of 141 y-columns. The positive-operator min closure and isometry are open mathematical obligations. This supplies a concrete cheaper candidate with only a 9.9% reduction in all-case data.

### A production plan consistent with these results

The first engineering pass would keep the current potential values and the actual V2 statements. Port computation to `module`, Init-only kernels; use private meta imports and the native chunk-expression elaborator; put coefficients on the right of huge products; use compact guarded views; and share a canonical chunk store between the finite row data and C.value. The separate opt-in `CertData` library remains the right build attachment. Default AKLT builds should import only generic statements/assemblies. Public per-case theorems should existentially hide data from ordinary downstream elaboration; independent full export must still include it.

Group about 256 planes/rows per data/check module and choose prefix intervals by a measured work limit including stem replay and invalid slots, aiming initially at no more than 5,000 visits per reduction. This suggests roughly **900–1,400 numeric/support modules**, rather than 5,035, after consolidating small graph checks and removing endpoint duplication. This is a scheduling design, not a generated manifest or a demonstrated 6 GiB bound for every proposed batch. The exporter must enforce physical line counts; 256 one-line data declarations and balanced expressions readily fit the cap. All unused old non-module generated files must be excluded from a submission, not merely left unimported.

For the 8192-bit design, direct extrapolation of measured data loading, full row reduction and the large prefix gives a provisional **1.7–2.5 CPU-hours for one complete Lean build**, including startup/loading; about **1.1–1.4 CPU-hours of numerical reductions** within that range. Other cases, fixed-data semantic proof compilation, final aggregation and a clean full build are unmeasured. This is the basis for the 8–11× estimate, not an achieved complete-case fit. Building and fresh Lean replay both consume the verifier budget. The 1024-bit variant increases Lean CPU, despite faster serialization. The native dyadic experiment could trim prefix arithmetic further, but is not included as a measured Lean saving.

The literal obstruction is more decisive than this uncertain CPU estimate:

- Compact uint32 planes retain **5.950 GB binary / about 14.33 GB decimal digits**. Chunking preserves almost all digit volume; small chunks add substantial NDJSON expression metadata. The 300 MB digit target requires a further 47.8× reduction, not another modest batching change.
- Scaling the actual stock export CPU by input planes gives roughly **4.9 hours** for the 8K representation or **3.2 hours** for 1K, from plane data alone. Shared primitive metadata makes such extrapolations approximate; it cannot turn them into a few minutes. These serial costs do not halve on the larger CPU profile.
- The full row NanoDa sample is much slower than its Lean reduction; multiplying only Lean's kernel number by an optimistic generic 2× would be unjustified. Literal parsing can be shared in a monolithic export, but a final installed environment and all auxiliary checks still need measurement.
- An installed 5.95 GB mathematical literal payload alone exceeds a 6 GiB process share once environment and reduction storage are added. H3 may fit a larger process inside a 32 GiB host by itself; coexistence with the proof library and H1 is not demonstrated. Module privacy helps builds, not the required full export/replay.
- Current `Automaton10Data` also contains a giant fixed Nat. A production release needs its meaning-preserving chunk representation in the statement/Challenge surface, or a verified toolchain serialization/parser improvement. Merely chunking Solution data leaves the protected Challenge export hazard. This study does not edit that layer or assume approval for an upstream tool change.

There is therefore **no validated wall-time plan for the whole submission at either 16×32 or 32×64**. Even an H3-only ideal 4–8-way build would spend roughly 15–40 minutes on a two-hour CPU build before setup/cache/other proofs; then the measured stock serialization scale consumes 3–5 hours. The full replay, H1 and the remaining repository do not fit in the leftover allowance. This is not a formal impossibility result for H3′; it rules out declaring the present archived-potential route budget-ready based on the micro-pilots.

The next research task should seek a potential represented by a small nonnegative spatial basis, a certified analytic outer region plus a small inner patch, or another certificate whose **row residual is certified in that representation**. Simply storing low-rank factors and reconstructing all 1.49 billion cells can replace byte cost with too many large multiplications. Keep memory ten, the supplied quotient, radius-70 extension, value scale 65536, the five exact ceilings and the fixed length-12 bound. Validate candidate values with the existing integer checker and exact prefix programs before investing in Lean. A useful go/no-go gate is all five native cases passing with ≤125 MB of binary coefficient/basis data (about 300 MB decimal payload), plus a residual checker whose measured all-case projection is comfortably below one CPU-hour. The B2 symmetry and dyadic prefix variants are safe small follow-on directions once their leaves receive first attempts; they do not close the volume gap.

### Writer handoff and remaining proofs

No written mathematical leaf proof was added. `Fit.Obligations` compiles; it and the generic kernels contain new exact closed Prop statements for guarded comparison, parity projection, 32→48-bit strengthening, rectangle extraction, endpoint block lookup and multiplication-order equivalence. The list is [fit-leaves.json](phase4/fit-leaves.json). `MinSupersolutionSound` is included for the B2 candidate. These low-level Props are not a complete replacement for the accepted 56-leaf Defs bridge. A selected production redesign still needs precise chunk/C.value refinement, bitset/list-coordinate/edge refinement, short-hit sorting, frontier coverage and endpoint binding or canonical-view soundness. Their first proof attempts belong to other cheaper models. No theorem here silently assumes those refinements or claims the new Fit checker proves a Top target.

Sources and reproduction commands are in [Fit/README.md](../../wt/CERT_H3/Fit/README.md). The final artifacts include generic checkers, native elaborator source, real selected data and checks, search programs, input hashes, per-tool receipts, axiom prints and bounded negative controls. The official verifier checkout and all phase-3 source files were kept unchanged.

## phase 5 — structured potential

Author-directed search in progress. The finite input is now allowed to change, provided it bounds the same true-trail kernel and gives contraction below one. Comparator NanoDa (four threads) and Lean replay run serially; the goal is minutes of replay and a few hundred MB. The phase-4 frozen-parameter restrictions no longer apply to this search.

MATH_FIT’s H3 section was read first. Its tilted-exponential obstacle/minimum family is excluded here. This lane starts with nonnegative tensor-product piecewise-linear/Bernstein bases, using a refined source-cell partition so that translated residuals are certified by a small set of Bernstein coefficients, followed by LP feasibility and exact/rounded finite checks. No new written leaf proofs will be attempted.

Experiments and intermediate outcomes will be appended as they finish. The accepted production is read-only.

### Intermediate result — tensor hats, memory six

The first hat LP uses 124 minimized states, 225 tensor-product coefficients per phase and 1089 translated-knot check points. Its phase-D LP on coarse vertices solved optimally (27,900 variables, 27,652 rows, 139,926 nonzeros; 462.35 seconds including crossover), but the required refined residual check fails at state 74, position (3,1), with residual −0.0149107. There are 147 violating spatial points. Adding their constraints hit the configured solver time limit. This is not a supersolution or a contraction bound; coarse-vertex feasibility is insufficient. The failure is in the piecewise-linear representation at a near-inner-grid transition, and motivates the smoother inverse-polynomial family now being implemented. See `phase5/hat_m6_B1_R64_i2.json` and its log.

### Intermediate result — piecewise rational/Bernstein family

A nonnegative tensor basis now gives a feasible memory-ten B/north candidate with exact inner radius eight. Each coordinate has seventeen singleton sites and four inverse-polynomial intervals on either side: distances 1–4, 5–12, 13–28 and 29–infinity. On each interval the profile is normalized `(16+L)/(16+s)`. A separate state coefficient is attached to every tensor feature. Finite intervals use Bernstein residual coefficients after multiplying by positive denominators; the infinite interval uses monomial coefficients. This differs from MATH_FIT’s minimum of tilted exponentials.

The candidate has 625 coefficients and 3025 coefficient inequalities per state/phase. The floating coefficient residual is at least about 9.995e-7. Native true-prefix evaluation gives B/N **0.35059223430708336** at length twelve, below the archived ceiling 0.351207554; length fourteen gives 0.34952659626822424. The other four cases, independent shift/residual validation, integer rounding and Lean micro-pilots are pending. No contraction or soundness theorem is claimed at this stage. See `phase5/seg_m10_B1_R8_c16_p1_n4.json` and `-prefixL12.json`.

Smaller patches/offsets show the obstruction: unsegmented offsets 4/8 and segmented offset 8 drive phase-A corner constraints unstable, while the feasible radius-four offset-12/16 candidates give B/N 0.953/0.597. Thus both stability and boundary feedback matter.

### Intermediate result — all cases pass exact native checks

All 226,180,860 coefficient rows pass after rounding upward to a 2^-22 grid (24-bit coefficient fields). The minimum exact residuals remain between 5.35e-7 and 5.66e-7. An independent Fraction calculation confirms the common convex shift identities at finite-interval interior points and 259 points of the infinite interval. This is native numerical validation, not a kernel or soundness proof.

The exact production-reference prefix DFS evaluates the rounded coefficients directly, with no materialized endpoint table. It gives B/N = 0.350592596877, B/W = 0.288096092443, C/N = 0.527561179045, C/W = 0.380169227919, C/S = 0.270116964514. The resulting two contractions are 0.989281286198 and 0.981539476232, both below 99/100. Receipts are in `phase5/*-exact-rows.json`, `*-exact-prefixL12.json`, and `exact-contraction.json`. The coefficient count is 46,762,500 (140.29 MB at 24 bits, about 337.85 MB decimal literal payload).

Further reductions tried: one/two exterior intervals at radius eight give B/N .40732/.37349; memory nine with four intervals gives .41576. These do not meet the original B/N ceiling. Larger-patch/fewer-interval trials are running; the accepted m10/R8/four-interval candidate is retained unchanged.

### Intermediate result — simpler profile and kernel pilot

The radius-ten/offset-24, single-exterior-interval model passes **all 62,773,980 exact native coefficient rows** after 2^-22 upward rounding. There are 529 coefficients / 841 coefficient rows per state/phase. The minimum residual is above 6.04e-7. Exact prefix gives B contraction 0.972423545370 and C contraction 0.968162872732. Coefficients occupy 118.74 MB binary / approximately 286 MB decimal digits. Compared with the first structured candidate this is 3.60x fewer coefficient rows and 15.36% less data.

A real Lean pilot on 64 states spread through all 3741 classes, all four phases, and all 839 nonpinned spatial coefficient rows per plane passes by `decide +kernel`: 214,784 row inequalities. Kernel type checking is 3.97 s; fresh build 13.26 s, peak 2.14 GiB. Stock full export is 6.86 MB. Independent acceptance: con-ron verified 14.47 s / 1.55 GiB; NanoDa four threads 3.32 s / .59 GiB; fresh Lean replay 4.72 s / 1.04 GiB. Every theorem prints only propext. This pilot uses direct spatial expansion/routing, avoiding arbitrary state gathers; the first state-gather approach was slower. Full-size projections and further precision reduction are still under study.

### Intermediate result — 16-bit coefficients and a smaller prefix certificate

Exact integer Gauss–Seidel repair at value scale 2^14 and coefficient scale 2^24 produces five valid 16-bit data sets. Every one of the 62,773,980 coefficient rows passes the independent uint128 validator. Their exact reference-prefix contractions are **.9892403802344695 / .9812143000020402**, below 99/100. Payload: 39,579,780 coefficients, **79,159,560 binary bytes**, about **190.6 MB decimal digits**. The coarse-grid LP with uniform slack .0002 was also tested: B/N rises to .38162 and is discarded; integer repair spends the slack only where needed.

The 16-bit / dynamically widened 64-bit spatial pilot checks the same 214,784 inequalities in 3.19 kernel seconds (earlier run), fresh build 7.74 s / 1.80 GiB. Stock export, con-ron, NanoDa and fresh Lean replay all accept. Direct structured endpoints with 64-bit outward phase rounding also pass the real 7,459-node prefix shard: 19.5 kernel seconds / 3.49 GiB build peak, 108.8 s / 5.41 GiB con-ron, 29.63 s NanoDa, 23.41 s fresh Lean. Its large per-shard data is shared with Bellman checks in a production canonical layout; it is not an additional endpoint payload.

An exact bitset automaton pilot checks 5,063 raw memory-ten windows, including kinds, arrivals and four batched successor classes, in 16.4 kernel seconds. All three replays accept. Invalid-word table values no longer need to be frozen in the proposed existential quotient statement. Representative coverage remains a finite check/refinement requirement.

A further **positive transient-prefix quotient** has been generated and evaluated natively. Before time ten, backward minimization of raw-prefix contexts preserves allowed directions, kinds and their next classes; class counts are 1,4,12,36,108,316,716,1372,2245,3156. Thereafter it uses the existing 3741-state quotient. Response weights retain only the centre as dead, and the initial bond is permanently forbidden. These relaxations have open domination leaves. All five forward bounds exceed the exact prefix by only about 1e-15. A 24-bit suffix-value certificate with 32-bit upper coefficients gives B/N .3504020791, B/W .2884389110, C/N .5270723689, C/W .3798507200, C/S .2705365607; both contractions remain below .99. It has 142,417 nonterminal contexts and 141,421 endpoint contexts over all cases, replacing 708,097 full DFS visits and their accumulated phase arithmetic.

Exact short hits are now enumerated independently with a Manhattan-distance prune. Across all cases it visits only **46,589** nodes and reproduces all **4,471** short hits and their exact original numerator. A real 2,743-node short shard passes Lean in 5.03 s / 1.37 GiB; independent replays are running. A 512-context suffix-row prototype passes Lean; dense pointer-checked rows and endpoint bindings are being piloted to remove repeated dictionary searches.

The mathematical specification and the coefficientwise-to-global assembly compile in `Fit/Structured/Specification.lean`. Canonical AKLT Defs are still legacy, non-`module` sources and cannot be imported from these submission-compatible modules; the unchanged Defs adapter and new proposed finite Top statement will be supplied as an explicit port/bridge handoff. No mathematical leaf proof was written.

## ORCH-SUMMARY
- Phase 5 numerical success: inverse-polynomial single-profile family, m10/R10/c24.
- Repaired 16-bit data: 79.16 MB binary / 190.6 MB decimal literals, contractions below .99.
- All 62,773,980 native integer coefficient rows pass; five exact reference prefixes pass.
- Real spatial/automaton/direct-prefix pilots accepted by Lean, NanoDa and con-ron.
- Transient tail-DAG and pruned short hits reduce prefix work substantially; final pilots running.
- Compiled analytic closed Props and assembly exist; no written leaf proofs.
- Canonical Defs require the upstream module port before direct bridge compilation.
- Final leaves, finite replacement statement and budget projection pending.
- Production/main untouched.
