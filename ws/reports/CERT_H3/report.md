STATUS: PARTIAL (the general full-plane packed-to-Defs bridge and complete certificate coverage remain open)

The design, exporter, and a working numerical prototype are delivered. `AKLT.Cert.H3.prototype : PrototypeStatement` is proved without assumptions. It combines a memory-10 quotient shard checked against the actual Defs, all three quotient edge counts, 64 sampled Defs Bellman component rows, 64 full packed phase/window planes, their full-plane cap inequalities, and one exact weighted prefix shard with verified endpoints and its short closed contribution. The full-plane packed expressions have a proved no-carry/guard theorem; their general equality with the Defs spatial operator is an **open Prop**, `AKLT.Cert.H3.RowTermsAgreement`. Thus the 64 full planes are not claimed to be 64 complete Defs plane-row proofs. Neither full target statement is claimed proved.

All source changes are under `/home/ubuntu/aklt/wt/CERT_H3/AKLT/Cert/H3/`. Reports and manifests are here. No sub-agents were used. No existing Defs, generic library, project configuration, package, or Mathlib source was changed. Lean is 4.35.0-rc2, commit `11acb17ec6b07a8f9e9173e6845197929540936b`; project base commit is `0959dfc2d693b843c431fa1bf2d2b227eafdc3c1`. The existing Mathlib 065356127b build and project dependency oleans were read through scratch import symlinks. Mathlib and packages were neither updated nor built.

**Files.** Paths below are relative to the worktree unless linked to this report directory.

| File | Purpose |
|---|---|
| `AKLT/Cert/H3/Main.lean` | Exact `PrototypeStatement` and its unconditional theorem `prototype`. |
| `Common.lean`, `Literal.lean` in that directory | Coding, coordinates, balanced sparse lookup, Defs component-row statement, balanced literal elaborator. |
| `Automaton.lean` | Decidable raw-window/admissibility checks, `CorrectAt`, proved Boolean soundness. |
| `Packed.lean`, `Rows.lean` | General checked packed sum, masks, cap-filled routing, actual case/window/phase term construction. |
| `View.lean`, `Grid.lean` | Proved coordinate membership view and inverse indexing. |
| `Prefix.lean`, `PrefixView.lean` | Defs prefix shard, integer dot-product identity, proved dead-neighbour/phase views and structural short sorting. |
| `Soundness.lean`, `Obligations.lean` | Ceiling/scaled-row soundness, target assembly proofs, closed open Props for writers. |
| `Data/Automaton.lean` | Dense proposed raw projection, quotient representatives, successors, kinds. |
| `Data/BNPrototype.lean` | 228 real B/north planes, real caps, sparse partial `StationaryData`. |
| `Data/PrefixBN.lean` | Exact phase numerators, endpoint table, survival mask, expected integer sum and short fraction. |
| `Check/AutomatonShard.lean`, `Check/Counts.lean` | Raw quotient shard and complete edge/square counts. |
| `Check/Coefficients.lean` | All 12 diagonal and 60 admissible response ceiling cases checked against Defs. |
| `Check/PackedRows64.lean`, `Check/SemanticRows64.lean`, `Check/Attachments64.lean` | Packed full planes; actual Defs sampled rows; caps/free/terminal checks. |
| `Check/PrefixShard.lean`, `Check/Baseline.lean`, `Audit.lean` | Complete prefix shard, import baseline, every exported theorem's statement and axiom audit. |
| `export.py`, `generate_prefix.py`, `run_checks.py` | Streaming archive exporter, reproducible shard generator, timed fresh Lean processes and resource guards. |

The canonical writer manifest is [leaves.json](leaves.json). It enumerates individual planned modules, not just glob names, and distinguishes proved results, open Props, missing implementations, and planned checks. Other artifacts are [export_manifest.json](export_manifest.json), [prefix_manifest.json](prefix_manifest.json), [frontiers.json](frontiers.json), [exported_declarations.json](exported_declarations.json), [measurements.jsonl](measurements.jsonl), and logs under [logs/](logs/). Planned modules in `leaves.json` are not represented as existing files.

**Exact data representation.** Absolute direction codes are E=0, N=1, W=2, S=3; phases A,B,C,D have codes 0,1,2,3. A length-m direction word has code `Σ directionCode(w i)*4^(m-1-i)`. `decodeWord` extracts those digits. No direction or physical position is rotated by the quotient. `WordCodecLaw` is the outstanding general inverse/completeness theorem; the prototype checks concrete words directly against Defs.

For a site `(x,y)` in `[-70,70]^2`, the lane index is `(x+70)*141+(y+70)`. Hence x is the slow coordinate, exactly as in the archive/C checker. `gridSite s = (s/141-70,s%141-70)`. `grid_index_law` proves both inverses and all bounds, with no enumeration of the 19,881 sites. `mem_square_iff` proves membership is exactly the four coordinate inequalities. `extended_view` identifies the coordinate test/cap lookup with `StationaryData.extended`.

Each spatial plane is a **single ordinary Nat literal**, with lane s in bits `[80*s,80*s+80)`, least significant lane first. The exporter writes `def pKEY : Nat := h3_hex% "..."`; `KEY = phaseCode*3741+class`. The literal holds all 19,881 uint32 values widened to 80-bit lanes, without rounding. One plane is 198,810 binary bytes. Caps are packed as 32-bit fields in the same key order. The integer scales are V=65,536 and D=281,474,976,710,656; these are independent. No value is a floating-point approximation at checking time.

`h3_hex%` is an untrusted elaborator adapted from the supplied balanced-loader experiment. It validates the alphabet, performs balanced decoding, and emits `Expr.lit`/`mkNatLit`, an ordinary kernel natural literal. It introduces no reduction rule or proof. Its UTF-8 array is an elaboration implementation detail, not a kernel certificate array. All certificate lookup/checker collections use lists or balanced trees. The generated data module holds a balanced `PlaneTree` of key/literal leaves. Production groups at most 64 planes per module, giving 234 modules per case and 1,170 for five cases. The prototype deliberately uses a larger single module, 228 planes/45.33 MB binary, to contain every selected source, successor, and prefix endpoint.

The proposed automaton uses four further literals: 12-bit raw class at every code in `[0,4^10)` (3741 marks invalid), 20-bit representative codes, 12-bit successor-plus-one fields at `4*class+direction` (zero means disallowed), and 2-bit kind fields. The Lean `MemoryQuotient 10 3741` is constructed from these fields. Its totalizations use modulo 3741 and a default successor; correctness must be proved for every actual raw window, not inferred from these totalizations. The archive's 60,092-word coverage/count and all class representatives remain to be checked globally. SHA-256 is provenance only: the selected gzip hash is `3bdc2f5cfe54b15548ccf4b40384ab9585938385bb7860cf94ad1706239293a2`.

**Packed Bellman rows.** `rowTerms` reads the selected quotient's allowed directions, successor, kind, and arrival; it does not read a supplied Bellman matrix. For each allowed direction it builds same-phase ordinary terms, permissible known-site terms, and the appropriate A→C turn or B→D straight response terms. Revisit rows have no phase change. Diagonal constants are `qs=97632666219444`, `qt=100347585280092`, `q3=93824992236886`, and `q5=56294995342132`. `Check.Coefficients` verifies the diagonal values and the 60 response values against `coefficientCeiling`, the exact dyadic h, and beta-prime; no rational 6/5 replaces h.

All masks select complete 80-bit fields. `allMask = 2^(80*19881)-1`; `oneMask s=(2^80-1) << (80*s)`. First/last rows are contiguous blocks. First-column mask is `repeatLane (80*141) 141 (2^80-1)`, and the last column is its shift by 80*140. Ordinary masks delete centre, target, start u, and a=u+d₀. The five response masks partition sources by which, if any, of the four neighbours is the centre. Their intersection with the ordinary mask removes known and terminal sources. These are formulas shared between rows, not independent trusted masks in each exported row.

`pull P Z d` reads P at x+d. E shifts right by 80*141 and fills the last x-row with Z; W shifts left by 80*141 and fills the first x-row. N shifts right by 80, excludes the last y-column, and fills it with Z. S shifts left by 80, excludes/fills the first y-column. Every shifted result is masked to prevent wrapping. `PullLaw` states this exactly on the infinite lattice; it remains open for these closed-form masks, with the generic lane/grid routing library available for its proof.

At u or a, the initial bond is forbidden in both directions forever, memory-detected revisit departures are killed, and the remaining departures have only diagonal q5 terms. No rule-release time is used. Centre and target source rows are deleted. Ordinary arrivals at the centre contribute zero through the independently checked zero centre value, which must be included when proving equivalence with Defs' explicitly deleted incoming centre coefficient. Target values are 0,0,V,V. Outside-square successors use their exact corresponding phase/class caps. Every stored lane needs U≤Z, including interior lanes, and every free row needs its own scaled inequality and positive caps; C,D caps must be at least V.

The generic arithmetic theorem is already proved. For `ts : List (Nat × Nat)`, `weighted ts = Σ c*P` and `component b s ts = Σ c*lane P b s`. `weighted_pack` proves the pack polynomial identity. `packedRowCheck g n k D U ts` checks U and **each constructed term input** with `capCheck`, checks `Σc*2^k < 2^g` and `D*2^k < 2^g`, then checks the guard subtraction for `weighted ts ≤ D*U`. `packedRowCheck_sound` proves every component inequality. Here g=79, n=19881, k=26. Thus no-carry bounds are checked, not assumed from a C maximum; neither sums nor subtractions can borrow/carry between lanes. The actual sums have ample room below bit 79.

The remaining general step is `RowTermsAgreement`: assuming a correct quotient, one of the five actual cases, fitting planes, small caps and zero centres, every nonterminal lane's `component` equals the actual Defs ceiling-weighted spatial sum. `PassesAssembly` then combines it with `GridIndexLaw`, caps, terminals, and free rows to obtain exactly `StationaryData.Passes`. Both are closed Props, not premises attached to an unconditional full-certificate theorem. `coefficientCeiling_bound` and `scaled_row_real` are proved: the integer inequality bounds the exact rational coefficients after division by D,V, using `AKLT.Gen.Bellman.scaled_row_sound`. The already proved generic Bellman local/global library can subsequently provide the infinite-lattice supersolution argument; that analytic argument is outside these two finite target statements.

**Automaton check and coverage.** `CorrectAt Q w` is exactly the per-word portion of `MemoryQuotient.Correct`, together with raw validity: all four absolute labels have the right admissibility, kind, projected successor, and nonrevisit arrival. `rawRowCheck_sound` is proved. `quotient_assembly` proves that valid/projecting representatives and `CorrectAt` for every raw word give the Defs quotient contract. Production must regenerate raw words by a structurally recursive used-unoriented-bond DFS, prove it enumerates each `RawWindow` once, count 60,092, and partition its checked rows into fresh modules. A provided text list, dense class map, or minimizer output cannot supply coverage by itself.

The working shard checks **32 distinct length-ten raw words**: representatives of classes 0–15 and a different last-listed preimage of each of those classes. It verifies representative projection and the entire `CorrectAt` contract for both words. Separately, all 3,741 quotient states' labelled edge counts are kernel checked: 2,516 straight, 5,032 turn, 1,872 revisit. This checks the supplied quotient's counts, not the unproved global correctness of its partition.

**Weighted exact prefixes and endpoints.** The production step denominator is K=12139925673538045870080000 (84 bits), distinct from the 48-bit ceiling scale. The inner prefix accumulator is integral. A node carries its absolute position/incoming direction, used undirected bonds, departure counts, last-ten code, four integer phase numerators at scale K^n, and the true first-visit score data for the short contribution. On a revisit multiply all phases by K/5. On a fresh turn update `(A,B,C,D)` to `(A*nt, B*n3, C*n3+A*r, D*n3)`; on a fresh straight use `(A*ns, B*ns, C*ns, D*n3+B*r)`. The coefficient r uses the actual dead neighbours, including two previous departures, and the exact h. These are exact coefficient numerators, never ceilings.

A target hit is processed before the depth-12 survival branch, is counted only in the short contribution, and has no children. Centre hits and used bonds are rejected. The short score uses `(x-1)/(x*kappa)`, infinity at zero reward, and the path-index tie break. `liveOther_view`, `witnessKappa_view`, and `prefixPhases_view` are proved semantic equalities to Defs. A structural fuel-based merge and sort are proved equal to the Defs merge/sort, so `closedContribution_view` preserves the prescribed ordering exactly. `PrefixDenominatorLaw` and `IntegerPhaseUpdateLaw` are the open general proofs needed to update numerators once per tree edge in an optimized replay. The prototype instead verifies a finite phase table against the rational Defs fold; its numeric sum is integral, but this semantic replay still incurs rational-fold cost.

Split production at a **definition-generated depth-eight frontier** and finish at depth twelve in independent modules. The untrusted scheduling traversal counts 1,466 / 1,703 / 1,095 / 1,631 / 1,525 surviving depth-eight stems for B/N, B/W, C/N, C/W, C/S: **7,420 modules**. Counts and codes are in `frontiers.json` and are scheduling hints only. Prove `GeneralPrefixFrontierLaw`, zero contribution from rejected stems, and first-hit short enumeration `ShortCodecLaw`; sum early hits through depth eight separately. At depth ten there are 58,090 valid stems, so one process per such stem wastes substantial startup time. The coded closed Props include the general depth and the prototype's depth-ten specialization.

An endpoint index is keyed by `(phase,class,site)`, stored in a balanced tree with uniqueness/range checks. For each distinct requested key, verify equality with the full plane's extracted lane once in the data-group checker; check the exact class and coordinate of every accepted leaf, then use the small table inside the weighted DFS. Endpoint equalities, sortedness/coverage, and shard recombination must be proved. Hashes or a value from the external Python evaluator do not replace them.

The real prototype stem is N,E,N,W,S,W,S,E,S,E. It includes true revisits and returns to the permanent known sites. It enumerates all 16 two-step suffixes. Surviving suffix codes are 0,3,12,14,15; suffix 1 hits the B target exactly at time twelve. `first_direction_checked`, `stem_checked`, and `words_injective` certify the family. `classification_checked` identifies every surviving candidate with `SurvivingPrefix`; `closed_classification` identifies the sole closed candidate. `endpoints_checked` verifies class, actual endpoint and all four plane values, and `endpoint_table_verified` gives exactly the `StationaryData.extended` equality. `phases_checked` proves each accepted numerator equals the true Defs phase weight times K^12. Numerator fields require 984 bits here. `integer_table_sum` then proves the single division of the integer dot-product sum; `tail_from_defs` identifies it with the Defs shard. `closed_checked` verifies the short term, and `complete_shard` combines them.

The exact short term is `8137373651801805136926263155227416318983831 / 992516354663529468664578524470487342383104000000`. The tail is `expectedNumerator/(K^12*65536)`, with the full numerator in `prefix_manifest.json` and the Lean data. Their reduced sum, calculated from these certified fractions, is `374958646435372441102583043063107790221679400313237521 / 21040453765400756381650107971314133493858490577741414400000`. It is one shard, not any entire nine-decimal case bound.

**Measured kernel builds.** All successful numerical facts use ordinary `decide +kernel`; no native decision procedure, trust-me axiom, effectful Lean evaluation, skipped type checking, or custom kernel reduction rule is used. GNU time wraps each fresh Lean process, with `LEAN_NUM_THREADS=1`, `-DElab.async=false`, timeouts and a 48-GiB address-space cap. At most three Lean processes were used concurrently. Data/check files alone set unlimited heartbeats and increased recursion depth. The generic sources use normal options. RSS includes imported dependencies.

| Module suffix | Checked work | Wall s | Peak RSS GiB | Olean bytes |
|---|---|---:|---:|---:|
| `Check.Baseline` | Imports and literal-use baseline | 3.26 | 6.792 | 5784 |
| `Data.Automaton` | Proposed automaton data | 5.69 | 6.815 | 1669032 |
| `Data.BNPrototype` | 228 real widened planes/caps | 72.18 | 7.128 | 46482040 |
| `Check.AutomatonShard` | 32 actual raw-word quotient rows | 8.82 | 7.629 | 37792 |
| `Check.Counts` | All quotient edge counts and square card | 11.06 | 8.185 | 28448 |
| `Check.Coefficients` | 12 diagonal / 60 response ceilings | 3.59 | 6.531 | 20968 |
| `Check.PackedRows64` | 64 full routed packed plane rows | 4.39 | 7.546 | 51032 |
| `Check.Attachments64` | 64 full caps plus free/terminal attachments | 4.45 | 7.121 | 141896 |
| `Check.SemanticRows64` | 64 actual Defs component rows | 4.88 | 7.073 | 105488 |
| `Check.PrefixShard` | Real weighted prefix / verified endpoint shard | 13.58 | 7.312 | 90592 |
| `Main` | Assembled unconditional prototype | 3.24 | 6.794 | 25808 |
| `Audit` | All exported statements and axiom audits | 3.19 | 6.793 | 1640 |

The profiled packed check spends 0.865 s in type checking for 64 real routed planes: about **13.5 ms/plane**, substantially more than the generic two-term guard's 0.7 ms. The profiled raw automaton shard spends 4.90 s in type checking for 32 words. The initial profiled weighted prefix shard spends 7.56 s in total type checking for five surviving leaves plus its closed branch, classification, and endpoint proofs. The extra explicit first-direction/closed-classification facts were added in the final normal build; use the table's final normal build time for its delivered source. Profiling is not an isolated timing of the integer dot product.

An initial direct Defs component-row reduction, before `extended_view`, failed at 149.74 s / 42.24 GiB RSS under the 48-GiB address cap. Its problem was repeated finite-set membership evaluation. The delivered coordinate-view version passes. Initial attempts to compute the short contribution through well-founded List merge/sort reductions did not reduce; the delivered structural functions have equality proofs and pass. Development invocations with source errors/failed goals are not certificates; their diagnostic axiom output is not counted. `measurements.jsonl` retains invocation records, and the successful final `Audit` output is authoritative for delivered declarations. Some early log basenames were reused before the runner began using fully qualified module names.

**Exporter and reproduction.** `export.py` uses only the Python standard library, validates the exact nine-int64 header `(10,12,70,3741,19881,targetX,targetY,16,d0)`, reads four cap arrays followed by four phase-major/class-major spatial arrays, handles little-endian uint32 data, requires EOF, and lets gzip validate its CRC. It emits exact widened planes and a balanced lookup tree, without trusting input floating-point data. It reads the gzip in one pass and emits individual ordinary literals. `--all` groups a complete chosen case by 64 planes; default mode reproduces the selected prototype, including all successor/endpoint windows. Production group functions are partial; `CaseDataAssembly` must combine them into one total case table and reject absent entries before claiming complete coverage.

```
cd /home/ubuntu/aklt/wt/CERT_H3
export PATH="$HOME/.elan/bin:$PATH"
python3 AKLT/Cert/H3/export.py
python3 AKLT/Cert/H3/generate_prefix.py
python3 AKLT/Cert/H3/run_checks.py \
  AKLT.Cert.H3.Literal AKLT.Cert.H3.Common AKLT.Cert.H3.Automaton \
  AKLT.Cert.H3.Packed AKLT.Cert.H3.Rows AKLT.Cert.H3.View \
  AKLT.Cert.H3.Prefix AKLT.Cert.H3.PrefixView AKLT.Cert.H3.Soundness \
  AKLT.Cert.H3.Data.Automaton AKLT.Cert.H3.Data.BNPrototype AKLT.Cert.H3.Data.PrefixBN \
  AKLT.Cert.H3.Check.AutomatonShard AKLT.Cert.H3.Check.Counts \
  AKLT.Cert.H3.Check.Coefficients AKLT.Cert.H3.Check.PackedRows64 \
  AKLT.Cert.H3.Check.SemanticRows64 AKLT.Cert.H3.Check.Attachments64 \
  AKLT.Cert.H3.Check.PrefixShard AKLT.Cert.H3.Check.Baseline \
  AKLT.Cert.H3.Obligations AKLT.Cert.H3.Grid AKLT.Cert.H3.Main AKLT.Cert.H3.Audit
```

The runner uses `lake env` only for environment setup, prepends one scratch import root combining read-only prebuilt dependencies with this worktree's own oleans, and invokes `lean -o` for each source. Full inner commands, user/system/wall times, RSS, exits and sizes are in `measurements.jsonl`. `--profile` adds Lean's profiler. There is no `lake update`, `lake build -j`, or Mathlib build. A complete case can be exported with, for example, `python3 AKLT/Cert/H3/export.py --all --case stationary_C_m10_R70_d3_coarse --group 64`. This large export has not been run.

**Production schedule and resources.** The fully expanded `leaves.json` schedules 1,170 plane data modules; 1,170 row/attachment/endpoint-slice check modules; 939 raw automaton shards of at most 64 words; 59 representative shards; 7,420 depth-eight prefix modules; five early-short modules; five case assemblies and two final assemblies. Add the common proof/implementation modules. Source-plane groups use the archive key order; row groups import only the source/successor groups they actually need. Random quotient routing can require many such groups, so cap each check's imports and measure this before the full export. The prototype's 46-MB data import does not establish the cost of a multi-GB final aggregate.

Build in this order: (1) codec, raw-regenerator completeness/count, `PullLaw`, `RowTermsAgreement`, and `PassesAssembly`; (2) one production 64-plane group and a complete semantic plane-row proof; (3) full automaton shards and representative/edge assembly; (4) one complete case's grouped data, caps/free/local/terminal/endpoint checks; (5) proved frontier partition and integer phase update, then one depth-eight weighted shard; (6) all five cases' prefix and early-short modules; (7) integer sum/ceiling comparisons, case assembly and both Top targets. Build shared data before parallel consumers. The target-assembly lemmas visibly require the actual remaining finite premises; neither hides an unproved fact in an unconditional theorem.

| Work | Planning CPU-hours | Basis/limitation |
|---|---:|---|
| Widened data loading/build | 8–10 | 14.875 GB literals; roughly 1.55 s/MB plus 1,170 fresh-process/import costs. |
| Raw/representative automaton checks | 4–6 | Measured 4.90 s/32 raw words plus about 1,000 process starts; requires a proved pruned regenerator, not testing every arbitrary word naively. |
| Packed local rows, free/cap/terminal/endpoint slices | 3–6 | Actual 64-plane and attachment timings; larger import graph remains unmeasured. |
| Conservative exact-prefix table replay | 160–240 | Current direct Defs phase verification, geometry, sorting, endpoint provenance and process overhead; not the geometry-only probe forecast. |
| Final sums/aggregation and margin | 2–4 | Multi-GB aggregation is a required resource test. |
| **Baseline production envelope** | **180–270** | Numerical build only, conditional on closing soundness/coverage and implementing planned modules. |

The prefix figure deliberately extrapolates conservatively: 7.56 s divided by five leaves and multiplied by 451,270 leaves is already about 190 CPU-hours, before adjusting for shared generic proofs and different branch mixes. It is not a confidence interval. A proved incremental integer DFS could remove most repeated rational/geometry work and plausibly reach a 20–40 CPU-hour overall scenario, but **that optimized scenario is not measured or approved by this prototype**. Do not pass the old 10–30 CPU-hour geometry-based estimate to writers as an achieved budget.

Use a memory-token scheduler with aggregate RSS below 140 GB and a hard campaign limit of 160 GB. Start six modest jobs; increase toward twelve only after the chosen production shard's RSS fits that allocation. Oversized prefix/data-aggregate jobs run with fewer peers. A 180–270 CPU-hour replay is roughly 20–45 wall-hours at six to twelve useful workers, with I/O/serial assembly uncertainty; no such full build has been performed.

All 74,820 widened planes occupy 14,874,964,200 binary bytes. Hex sources are about 29.75 GB; spatial literal oleans about 14.88 GB. Allow under 1 GB for phase/endpoint tables and their source/olean pairs, plus 2–5 GB for common/check artifacts and logs: **reserve 48–52 GB**, below the 60-GB worktree+scratch limit. Do not keep decompressed uint32 copies. The exporter checks the workspace/scratch total and reserves its next source write before writing. Exporter and runner abort below **100 GiB** available on `/`, a conservative interpretation of the requested 100-GB floor. The current worktree is about 275 MB, scratch holds import symlinks only, and `/` had about 180 GB free at the final resource check. No production dataset was exported. Aggregate import memory/serializer behavior is still a gate before committing the 45-GB data build.

**Open items and handoff.** The eleven closed open Props are `WordCodecLaw`, `AutomatonRegeneration`, `PullLaw`, `RowTermsAgreement`, `PassesAssembly`, `GeneralPrefixFrontierLaw`, `PrefixFrontierLaw`, `PrefixStemPruningLaw`, `ShortCodecLaw`, `PrefixDenominatorLaw`, and `IntegerPhaseUpdateLaw`, all under `AKLT.Cert.H3`. `GridIndexLaw` is closed by `grid_index_law`. Missing implementation names reserved in the manifest are `FiniteRawRegenerator`, `CaseDataAssembly`, `EndpointIndex`, and `FrontierReplay`. Complete raw coverage, other four cases, all other spatial rows/endpoints, full exact prefixes, and the five nine-decimal ceilings remain planned checks. The partial data object's default zero entries are not a complete candidate certificate. The prefix prototype uses exact integer table summation with rational Defs replay for its semantic table proof, rather than a proved incremental integer DFS. The general guarded arithmetic is proved; general routed geometry/Defs agreement is not.

**Exported statements and axiom output.** The following is the complete successful `Audit.lean` output: it gives every exported theorem's statement and its actual `#print axioms` result. Only `propext`, `Classical.choice`, and `Quot.sound` occur. `PrototypeStatement` is defined explicitly in `Main.lean` and its seven components are described above. The two `*_target_of_checks` declarations are assembly implications with their premises printed, not proofs that those premises hold. Open Props have no proof declarations.

```
AKLT.Cert.H3.rawRowCheck_sound {m q code : ℕ} {Q : AKLT.Defs.MemoryQuotient m q}
  (h : AKLT.Cert.H3.rawRowCheck Q code = true) : AKLT.Cert.H3.CorrectAt Q (AKLT.Cert.H3.decodeWord m code)
'AKLT.Cert.H3.rawRowCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.Attachments64.checked : (List.range 64).all AKLT.Cert.H3.Check.Attachments64.attachments = true
'AKLT.Cert.H3.Check.Attachments64.checked' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.Attachments64.terminal_caps (i : Fin 16) :
  65536 ≤ AKLT.Cert.H3.Data.BNPrototype.cap AKLT.Defs.Phase.C ⟨↑i, ⋯⟩ ∧
    65536 ≤ AKLT.Cert.H3.Data.BNPrototype.cap AKLT.Defs.Phase.D ⟨↑i, ⋯⟩
'AKLT.Cert.H3.Check.Attachments64.terminal_caps' depends on axioms: [propext, Quot.sound]
AKLT.Cert.H3.Check.Attachments64.finite_rows (i : ℕ) (hi : i < 64) :
  have φ := AKLT.Cert.H3.Check.PackedRows64.phase (i % 4);
  have a := AKLT.Cert.H3.Check.PackedRows64.state i;
  have U := AKLT.Cert.H3.Data.BNPrototype.plane φ a;
  have Z := AKLT.Cert.H3.Data.BNPrototype.cap φ a;
  (0 < Z ∧ Z < 2 ^ 26) ∧
    AKLT.Gen.Packed.lane U 80 (AKLT.Cert.H3.siteIndex AKLT.Defs.kernelCentre) = 0 ∧
      (AKLT.Gen.Packed.lane U 80 (AKLT.Cert.H3.siteIndex (AKLT.Defs.kernelTarget AKLT.Defs.PairType.B)) =
          if φ = AKLT.Defs.Phase.C ∨ φ = AKLT.Defs.Phase.D then 65536 else 0) ∧
        ∑ d,
            ∑ ψ,
              AKLT.Defs.coefficientCeiling (AKLT.Defs.freeCoefficient AKLT.Cert.H3.Data.quotient φ a d ψ) *
                AKLT.Cert.H3.Data.BNPrototype.cap ψ (AKLT.Cert.H3.Data.quotient.successor a d) ≤
          AKLT.Defs.certificateCoefficientScale * Z
'AKLT.Cert.H3.Check.Attachments64.finite_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.Attachments64.cap_rows (i : ℕ) (hi : i < 64) (s : ℕ) :
  s < 19881 →
    AKLT.Gen.Packed.lane
        (AKLT.Cert.H3.Data.BNPrototype.plane (AKLT.Cert.H3.Check.PackedRows64.phase (i % 4))
          (AKLT.Cert.H3.Check.PackedRows64.state i))
        80 s ≤
      AKLT.Cert.H3.Data.BNPrototype.cap (AKLT.Cert.H3.Check.PackedRows64.phase (i % 4))
        (AKLT.Cert.H3.Check.PackedRows64.state i)
'AKLT.Cert.H3.Check.Attachments64.cap_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.AutomatonShard.checked (i : Fin 16) :
  AKLT.Cert.H3.CorrectAt AKLT.Cert.H3.Data.quotient
      (AKLT.Cert.H3.Data.quotient.representative (AKLT.Cert.H3.Check.AutomatonShard.state i)) ∧
    AKLT.Cert.H3.Data.quotient.project
          (AKLT.Cert.H3.Data.quotient.representative (AKLT.Cert.H3.Check.AutomatonShard.state i)) =
        AKLT.Cert.H3.Check.AutomatonShard.state i ∧
      AKLT.Cert.H3.CorrectAt AKLT.Cert.H3.Data.quotient (AKLT.Cert.H3.Check.AutomatonShard.other i) ∧
        AKLT.Cert.H3.Data.quotient.project (AKLT.Cert.H3.Check.AutomatonShard.other i) =
          AKLT.Cert.H3.Check.AutomatonShard.state i
'AKLT.Cert.H3.Check.AutomatonShard.checked' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.Baseline.checked : 0 = 0
'AKLT.Cert.H3.Check.Baseline.checked' does not depend on any axioms
AKLT.Cert.H3.Check.Coefficients.diagonal_checked (φ : AKLT.Defs.Phase) (k : AKLT.Defs.StepKind) :
  AKLT.Cert.H3.diagonal φ k = AKLT.Defs.coefficientCeiling (AKLT.Defs.phaseDiagonal φ k)
'AKLT.Cert.H3.Check.Coefficients.diagonal_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.Coefficients.response_checked (a d : Fin 4) :
  AKLT.Cert.H3.direction ↑d ≠ (AKLT.Cert.H3.direction ↑a).reverse →
    ∀ (j : Fin 5),
      have x := if ↑j < 4 then -(AKLT.Cert.H3.direction ↑j).step else (10, 10);
      AKLT.Cert.H3.response ↑a ↑d ↑j =
        AKLT.Defs.coefficientCeiling
          (AKLT.Defs.passageFactor (decide (AKLT.Cert.H3.direction ↑d = AKLT.Cert.H3.direction ↑a)) *
              AKLT.Defs.relaxedReward x (AKLT.Cert.H3.direction ↑a) (AKLT.Cert.H3.direction ↑d)
                {AKLT.Defs.kernelCentre} /
            3)
'AKLT.Cert.H3.Check.Coefficients.response_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.Counts.square_card : (AKLT.Defs.square (0, 0) AKLT.Defs.certificateRadius).card = 19881
'AKLT.Cert.H3.Check.Counts.square_card' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.Counts.edge_counts :
  AKLT.Defs.quotientEdgeCount AKLT.Cert.H3.Data.quotient AKLT.Defs.StepKind.straight = 2516 ∧
    AKLT.Defs.quotientEdgeCount AKLT.Cert.H3.Data.quotient AKLT.Defs.StepKind.turn = 5032 ∧
      AKLT.Defs.quotientEdgeCount AKLT.Cert.H3.Data.quotient AKLT.Defs.StepKind.revisit = 1872
'AKLT.Cert.H3.Check.Counts.edge_counts' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.PackedRows64.checked : AKLT.Cert.H3.Check.PackedRows64.shardCheck = true
'AKLT.Cert.H3.Check.PackedRows64.checked' depends on axioms: [propext]
AKLT.Cert.H3.Check.PackedRows64.component_rows (i : ℕ) (hi : i < 64) (s : ℕ) :
  s < 19881 →
    AKLT.Cert.H3.component 80 s
        (AKLT.Cert.H3.rowTerms AKLT.Cert.H3.Data.quotient AKLT.Cert.H3.Data.BNPrototype.plane
          AKLT.Cert.H3.Data.BNPrototype.cap AKLT.Defs.PairType.B AKLT.Defs.Compass.north
          (AKLT.Cert.H3.Check.PackedRows64.phase (i % 4)) (AKLT.Cert.H3.Check.PackedRows64.state i)) ≤
      AKLT.Cert.H3.coefficientScale *
        AKLT.Gen.Packed.lane
          (AKLT.Cert.H3.Data.BNPrototype.plane (AKLT.Cert.H3.Check.PackedRows64.phase (i % 4))
            (AKLT.Cert.H3.Check.PackedRows64.state i))
          80 s
'AKLT.Cert.H3.Check.PackedRows64.component_rows' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.PrefixShard.stem_checked (e : Fin 16) :
  AKLT.Defs.takeWord (AKLT.Cert.H3.Data.PrefixBN.word e) 10 =
    AKLT.Cert.H3.decodeWord 10 AKLT.Cert.H3.Data.PrefixBN.stemCode
'AKLT.Cert.H3.Check.PrefixShard.stem_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.PrefixShard.words_injective : Function.Injective AKLT.Cert.H3.Data.PrefixBN.word
'AKLT.Cert.H3.Check.PrefixShard.words_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.PrefixShard.first_direction_checked :
  (∀ (e : Fin 4), AKLT.Defs.FirstDirection (AKLT.Cert.H3.Data.PrefixBN.word11 e) AKLT.Defs.Compass.north) ∧
    ∀ (e : Fin 16), AKLT.Defs.FirstDirection (AKLT.Cert.H3.Data.PrefixBN.word e) AKLT.Defs.Compass.north
'AKLT.Cert.H3.Check.PrefixShard.first_direction_checked' depends on axioms: [propext, Quot.sound]
AKLT.Cert.H3.Check.PrefixShard.closed_classification :
  (∀ (e : Fin 4), ¬AKLT.Defs.ClosedTrail AKLT.Defs.PairType.B (AKLT.Cert.H3.Data.PrefixBN.word11 e)) ∧
    ∀ (e : Fin 16), AKLT.Defs.ClosedTrail AKLT.Defs.PairType.B (AKLT.Cert.H3.Data.PrefixBN.word e) ↔ ↑e = 1
'AKLT.Cert.H3.Check.PrefixShard.closed_classification' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.PrefixShard.classification_checked (e : Fin 16) :
  AKLT.Cert.H3.Data.PrefixBN.survives e = true ↔
    AKLT.Defs.SurvivingPrefix AKLT.Defs.PairType.B AKLT.Defs.Compass.north (AKLT.Cert.H3.Data.PrefixBN.word e)
'AKLT.Cert.H3.Check.PrefixShard.classification_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.PrefixShard.endpoints_checked (e : Fin 16) :
  AKLT.Cert.H3.Data.PrefixBN.survives e = true →
    AKLT.Cert.H3.Data.quotient.project (AKLT.Defs.lastWindowWord 10 (AKLT.Cert.H3.Data.PrefixBN.word e)) =
        AKLT.Cert.H3.Data.PrefixBN.endpointClass e ∧
      AKLT.Defs.wordVertex AKLT.Defs.kernelStart (AKLT.Cert.H3.Data.PrefixBN.word e) 12 =
          AKLT.Cert.H3.gridSite (AKLT.Cert.H3.Data.PrefixBN.endpointSite e) ∧
        ∀ (φ : AKLT.Defs.Phase),
          AKLT.Cert.H3.Data.PrefixBN.endpointValue e φ =
            AKLT.Cert.H3.valueAt AKLT.Cert.H3.Data.BNPrototype.plane AKLT.Cert.H3.Data.BNPrototype.cap φ
              (AKLT.Cert.H3.Data.PrefixBN.endpointClass e)
              (AKLT.Cert.H3.gridSite (AKLT.Cert.H3.Data.PrefixBN.endpointSite e))
'AKLT.Cert.H3.Check.PrefixShard.endpoints_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.PrefixShard.endpoint_table_verified (e : Fin 16) (h : AKLT.Cert.H3.Data.PrefixBN.survives e = true)
  (φ : AKLT.Defs.Phase) :
  AKLT.Cert.H3.Data.PrefixBN.endpointValue e φ =
    AKLT.Cert.H3.Data.BNPrototype.certificate.extended φ
      (AKLT.Cert.H3.Data.quotient.project (AKLT.Defs.lastWindowWord 10 (AKLT.Cert.H3.Data.PrefixBN.word e)))
      (AKLT.Defs.wordVertex AKLT.Defs.kernelStart (AKLT.Cert.H3.Data.PrefixBN.word e) 12)
'AKLT.Cert.H3.Check.PrefixShard.endpoint_table_verified' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.PrefixShard.phases_checked (e : Fin 16) :
  AKLT.Cert.H3.Data.PrefixBN.survives e = true →
    ∀ (φ : AKLT.Defs.Phase),
      AKLT.Defs.prefixPhases (AKLT.Cert.H3.Data.PrefixBN.word e) φ =
        ↑(AKLT.Cert.H3.Data.PrefixBN.phaseNumerator e φ) / ↑(AKLT.Cert.H3.Data.PrefixBN.stepDenominator ^ 12)
'AKLT.Cert.H3.Check.PrefixShard.phases_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.PrefixShard.numerator_checked :
  AKLT.Cert.H3.Data.PrefixBN.shardNumerator = AKLT.Cert.H3.Data.PrefixBN.expectedNumerator
'AKLT.Cert.H3.Check.PrefixShard.numerator_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.PrefixShard.tail_from_defs :
  AKLT.Cert.H3.prefixShard AKLT.Cert.H3.Data.quotient AKLT.Cert.H3.Data.BNPrototype.certificate AKLT.Defs.PairType.B
      AKLT.Defs.Compass.north AKLT.Cert.H3.Data.PrefixBN.word =
    ↑AKLT.Cert.H3.Data.PrefixBN.expectedNumerator / ↑(AKLT.Cert.H3.Data.PrefixBN.stepDenominator ^ 12 * 65536)
'AKLT.Cert.H3.Check.PrefixShard.tail_from_defs' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.PrefixShard.closed_checked :
  AKLT.Cert.H3.Check.PrefixShard.closedPart =
    ↑AKLT.Cert.H3.Data.PrefixBN.shortNumerator / ↑AKLT.Cert.H3.Data.PrefixBN.shortDenominator
'AKLT.Cert.H3.Check.PrefixShard.closed_checked' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.PrefixShard.complete_shard :
  AKLT.Cert.H3.Check.PrefixShard.closedPart +
      AKLT.Cert.H3.prefixShard AKLT.Cert.H3.Data.quotient AKLT.Cert.H3.Data.BNPrototype.certificate AKLT.Defs.PairType.B
        AKLT.Defs.Compass.north AKLT.Cert.H3.Data.PrefixBN.word =
    ↑AKLT.Cert.H3.Data.PrefixBN.shortNumerator / ↑AKLT.Cert.H3.Data.PrefixBN.shortDenominator +
      ↑AKLT.Cert.H3.Data.PrefixBN.expectedNumerator / ↑(AKLT.Cert.H3.Data.PrefixBN.stepDenominator ^ 12 * 65536)
'AKLT.Cert.H3.Check.PrefixShard.complete_shard' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.SemanticRows64.checked_view (i : Fin 64) :
  AKLT.Cert.H3.viewRow AKLT.Cert.H3.Data.quotient AKLT.Cert.H3.Data.BNPrototype.plane AKLT.Cert.H3.Data.BNPrototype.cap
    AKLT.Defs.PairType.B AKLT.Defs.Compass.north (AKLT.Cert.H3.Check.SemanticRows64.phase (↑i % 4))
    (AKLT.Cert.H3.Check.SemanticRows64.state i) (AKLT.Cert.H3.Check.SemanticRows64.sampleSite (↑i / 4 % 8))
'AKLT.Cert.H3.Check.SemanticRows64.checked_view' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.Check.SemanticRows64.checked (i : Fin 64) :
  AKLT.Cert.H3.DefRow AKLT.Cert.H3.Data.quotient AKLT.Cert.H3.Data.BNPrototype.certificate AKLT.Defs.PairType.B
    AKLT.Defs.Compass.north (AKLT.Cert.H3.Check.SemanticRows64.phase (↑i % 4))
    (AKLT.Cert.H3.Check.SemanticRows64.state i) (AKLT.Cert.H3.Check.SemanticRows64.sampleSite (↑i / 4 % 8))
'AKLT.Cert.H3.Check.SemanticRows64.checked' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.grid_index_law : AKLT.Cert.H3.GridIndexLaw
'AKLT.Cert.H3.grid_index_law' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.prototype : AKLT.Cert.H3.PrototypeStatement
'AKLT.Cert.H3.prototype' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.automaton_target_of_checks (hcard : Fintype.card (AKLT.Defs.MemoryWindow 10) = 60092)
  (hQ : AKLT.Cert.H3.Data.quotient.Correct)
  (hs : AKLT.Defs.quotientEdgeCount AKLT.Cert.H3.Data.quotient AKLT.Defs.StepKind.straight = 2516)
  (ht : AKLT.Defs.quotientEdgeCount AKLT.Cert.H3.Data.quotient AKLT.Defs.StepKind.turn = 5032)
  (hr : AKLT.Defs.quotientEdgeCount AKLT.Cert.H3.Data.quotient AKLT.Defs.StepKind.revisit = 1872) :
  AKLT.Blueprint.Top.Automaton10Statement
'AKLT.Cert.H3.automaton_target_of_checks' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.stationary_target_of_checks (hcard : (AKLT.Defs.square (0, 0) AKLT.Defs.certificateRadius).card = 19881)
  (Q : AKLT.Defs.MemoryQuotient 10 3741) (hQ : Q.Correct)
  (C : AKLT.Defs.PairType × AKLT.Defs.Compass → AKLT.Defs.StationaryData 3741)
  (checks :
    ∀ k ∈ AKLT.Defs.stationaryCases,
      (C k).Passes Q k.1 k.2 ∧
        10 ^ 9 * AKLT.Defs.stationaryPrefixBound Q k.1 k.2 (C k) ≤ ↑(AKLT.Defs.stationaryPrefixCeiling k.1 k.2)) :
  AKLT.Blueprint.Top.StationaryCheckStatement
'AKLT.Cert.H3.stationary_target_of_checks' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.weighted_pack (b n : ℕ) (ts : List AKLT.Cert.H3.PackedTerm) (h : ∀ e ∈ ts, AKLT.Gen.Packed.Fits e.2 b n) :
  AKLT.Cert.H3.weighted ts = AKLT.Gen.Packed.packFn b n fun s => AKLT.Cert.H3.component b s ts
'AKLT.Cert.H3.weighted_pack' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.component_le (b s k : ℕ) (ts : List AKLT.Cert.H3.PackedTerm)
  (h : ∀ e ∈ ts, AKLT.Gen.Packed.lane e.2 b s ≤ 2 ^ k) :
  AKLT.Cert.H3.component b s ts ≤ AKLT.Cert.H3.coefficientSum ts * 2 ^ k
'AKLT.Cert.H3.component_le' depends on axioms: [propext]
AKLT.Cert.H3.packedRowCheck_sound {g n k D U : ℕ} {ts : List AKLT.Cert.H3.PackedTerm}
  (h : AKLT.Cert.H3.packedRowCheck g n k D U ts = true) (s : ℕ) :
  s < n → AKLT.Cert.H3.component (g + 1) s ts ≤ D * AKLT.Gen.Packed.lane U (g + 1) s
'AKLT.Cert.H3.packedRowCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.integer_table_sum.{u_1} {I : Type u_1} [Fintype I] (valid : I → Bool) (p v : I → AKLT.Defs.Phase → ℕ)
  (D V : ℕ) :
  (∑ i, if valid i = true then ∑ φ, ↑(p i φ) / ↑D * (↑(v i φ) / ↑V) else 0) =
    ↑(∑ i, if valid i = true then ∑ φ, p i φ * v i φ else 0) / (↑D * ↑V)
'AKLT.Cert.H3.integer_table_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.mergeFuel_eq.{u_1} {α : Type u_1} (le : α → α → Bool) (f : ℕ) (xs ys : List α)
  (h : xs.length + ys.length ≤ f) : AKLT.Cert.H3.mergeFuel le f xs ys = xs.merge ys le
'AKLT.Cert.H3.mergeFuel_eq' depends on axioms: [propext, Quot.sound]
AKLT.Cert.H3.mergeFuel_full.{u_1} {α : Type u_1} (le : α → α → Bool) (xs ys : List α) :
  AKLT.Cert.H3.mergeFuel le (xs.length + ys.length) xs ys = xs.merge ys le
'AKLT.Cert.H3.mergeFuel_full' depends on axioms: [propext, Quot.sound]
AKLT.Cert.H3.mergeSortFuel_eq.{u_1} {α : Type u_1} (le : α → α → Bool) (fuel : ℕ) (xs : List α) (h : xs.length ≤ fuel) :
  AKLT.Cert.H3.mergeSortFuel le fuel xs = xs.mergeSort le
'AKLT.Cert.H3.mergeSortFuel_eq' depends on axioms: [propext, Quot.sound]
AKLT.Cert.H3.liveOther_view {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i : Fin n) :
  AKLT.Defs.liveOtherNeighbours w i = AKLT.Cert.H3.liveOtherView w i
'AKLT.Cert.H3.liveOther_view' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.witnessKappa_view {n : ℕ} (w : AKLT.Defs.DirectionWord n) (i : Fin n) :
  AKLT.Defs.witnessKappa w i = AKLT.Cert.H3.kappaView w i
'AKLT.Cert.H3.witnessKappa_view' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.prefixPhases_view {n : ℕ} (w : AKLT.Defs.DirectionWord n) :
  AKLT.Defs.prefixPhases w = AKLT.Cert.H3.prefixPhasesView w
'AKLT.Cert.H3.prefixPhases_view' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.closedContribution_view {n : ℕ} (w : AKLT.Defs.DirectionWord n) :
  AKLT.Defs.closedContribution w = AKLT.Cert.H3.closedView w
'AKLT.Cert.H3.closedContribution_view' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.localRowCheck_sound {m q : ℕ} {Q : AKLT.Defs.MemoryQuotient m q} {plane cap : AKLT.Defs.Phase → Fin q → ℕ}
  {X : AKLT.Defs.PairType} {d₀ : AKLT.Defs.Compass} {φ : AKLT.Defs.Phase} {a : Fin q}
  (h : AKLT.Cert.H3.localRowCheck Q plane cap X d₀ φ a = true) (s : ℕ) :
  s < 19881 →
    AKLT.Cert.H3.component 80 s (AKLT.Cert.H3.rowTerms Q plane cap X d₀ φ a) ≤
      AKLT.Cert.H3.coefficientScale * AKLT.Gen.Packed.lane (plane φ a) 80 s
'AKLT.Cert.H3.localRowCheck_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.quotient_assembly (m q : ℕ) (Q : AKLT.Defs.MemoryQuotient m q)
  (representatives : ∀ (a : Fin q), AKLT.Defs.RawWindow (Q.representative a) ∧ Q.project (Q.representative a) = a)
  (rows : ∀ (w : AKLT.Defs.DirectionWord m), AKLT.Defs.RawWindow w → AKLT.Cert.H3.CorrectAt Q w) : Q.Correct
'AKLT.Cert.H3.quotient_assembly' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.coefficientCeiling_bound (t : ℚ) :
  t ≤ ↑(AKLT.Defs.coefficientCeiling t) / ↑AKLT.Defs.certificateCoefficientScale
'AKLT.Cert.H3.coefficientCeiling_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.scaled_row_real.{u_1} {E : Type u_1} (edges : Finset E) (t : E → ℚ) (v : E → ℕ) (u : ℕ)
  (h : ∑ e ∈ edges, AKLT.Defs.coefficientCeiling (t e) * v e ≤ AKLT.Defs.certificateCoefficientScale * u) :
  ∑ e ∈ edges, ↑(t e) * (↑(v e) / ↑AKLT.Defs.certificateValueScale) ≤ ↑u / ↑AKLT.Defs.certificateValueScale
'AKLT.Cert.H3.scaled_row_real' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.mem_square_iff (x : AKLT.Defs.Plane) :
  x ∈ AKLT.Defs.square (0, 0) AKLT.Defs.certificateRadius ↔ AKLT.Cert.H3.inBox x
'AKLT.Cert.H3.mem_square_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.extended_view {q : ℕ} (plane cap : AKLT.Defs.Phase → Fin q → ℕ) (φ : AKLT.Defs.Phase) (a : Fin q)
  (x : AKLT.Defs.Plane) : (AKLT.Cert.H3.dataOf plane cap).extended φ a x = AKLT.Cert.H3.valueAt plane cap φ a x
'AKLT.Cert.H3.extended_view' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.Cert.H3.viewRow_iff {m q : ℕ} (Q : AKLT.Defs.MemoryQuotient m q) (plane cap : AKLT.Defs.Phase → Fin q → ℕ)
  (X : AKLT.Defs.PairType) (d₀ : AKLT.Defs.Compass) (φ : AKLT.Defs.Phase) (a : Fin q) (x : AKLT.Defs.Plane) :
  AKLT.Cert.H3.viewRow Q plane cap X d₀ φ a x ↔ AKLT.Cert.H3.DefRow Q (AKLT.Cert.H3.dataOf plane cap) X d₀ φ a x
'AKLT.Cert.H3.viewRow_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**ORCH-SUMMARY**
- Delivered: real-data exporter, design, 228 B/N planes, guarded arithmetic proof and actual routed 64-plane acceptance.
- Delivered: 32 distinct memory-10 raw quotient rows; all 2,516/5,032/1,872 edge counts and 19,881-site count.
- Delivered: 64 actual Defs component rows, full-plane cap bounds, free/terminal attachments for 16 windows/all phases.
- Delivered: one genuine prefix shard, five surviving leaves and one time-12 hit; exact phases, endpoints and short ordering.
- `AKLT.Cert.H3.prototype` is unconditional; every exported theorem is audited against the three allowed axioms.
- PARTIAL: full-plane `RowTermsAgreement` and `PassesAssembly` are open; packed plane rows are not full Defs plane proofs.
- Open: `WordCodecLaw`, `AutomatonRegeneration`, `PullLaw`.
- Open: `GeneralPrefixFrontierLaw`, `PrefixFrontierLaw`, `PrefixStemPruningLaw`, `ShortCodecLaw`.
- Open: `PrefixDenominatorLaw`, `IntegerPhaseUpdateLaw`; `GridIndexLaw` is proved.
- Missing implementations: `FiniteRawRegenerator`, `CaseDataAssembly`, `EndpointIndex`, `FrontierReplay`.
- Complete automaton/raw count, all five full certificates/prefixes and both Top targets remain unproved.
- Prototype data are partial; missing planes default to zero. Only B/N was exported and checked.
- Prefix semantic table validation replays rational Defs; the optimized integer DFS is a plan, not an implementation.
- Writer manifest: `leaves.json`, with explicit pending modules and untrusted scheduling seeds.
- Production baseline: 180–270 CPU-hours / 48–52 GB; optimized 20–40 CPU-hours requires a new weighted-shard measurement.
- No sub-agents; at most three Lean processes; no package/project/foreign-source edits; resource floors respected.
- Decide ownership of the open geometry/codec/replay proofs and require a complete semantic plane-row proof before bulk export.
- Require measured production prefix shards and multi-GB aggregation before approving the final schedule.
