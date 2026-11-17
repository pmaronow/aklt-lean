STATUS: COMPLETE

# ARCH_PKG — the two-premise Palomar architecture

Architecture scope: the requested reduction, independent statement, package skeleton,
fidelity note and exact port inventory are delivered. This is **not** a populated,
ported, clean-built or mechanically accepted submission. No source port was performed.
The author-requested premise decision is preserved: the advertised theorem is conditional
on H1 and H3, and no extra mathematical hypothesis has been added.

Worktree: `/home/ubuntu/aklt/wt/ARCH_PKG`; starting commit `63d176add85a0eae6c862c54849a495434b7d438`.
Only `AKLT/Final/Inputs.lean` and files under `palomar/` were added in the worktree.
No sub-agents were used. Lean/checker work stayed within the six-process allowance;
header confirmation used two workers and proof replays ran sequentially.

## The proved reduction

[Inputs.lean](/home/ubuntu/aklt/wt/ARCH_PKG/AKLT/Final/Inputs.lean) contains **one** new theorem:

```lean
AKLT.Final.main_of_inputs :
  AKLT.Blueprint.Top.H1Statement →
  AKLT.Blueprint.Top.H3Statement →
  AKLT.Challenge.MainStatementV2
```

It assembles the existing Mom, Q, Win, Gap and repaired Rec leaves, discharges H2 with
`AKLT.Cert.H2.h2`, constructs the old **semantic** `Top.InputsStatement`, and applies
`AKLT.Blueprint.Top.mainV2_of_parts`. Its target is the all-parity `MainStatementV2`.
The proof does not import `Final.Skeleton` or `Final.Conditional`.

This uses exactly the analytic reduction already exposed by the existing assemblies.
`Top.mainV2_of_partsV2` itself immediately calls `mainV2_of_parts hInputs.1 ...`.
Consequently none of `H1FiniteDataStatementV2`, `CertificateStatement`,
`Automaton10StatementV2`, or `StationaryCheckStatementV2` is needed as a premise.
No finite-data conjunct was assumed or silently manufactured.

The only extra conjuncts required to construct `InputsStatement` are

```lean
AKLT.Defs.certifiedRate < (2499 / 2500 : ℚ)
(2499 / 2500 : ℚ) < 1
```

Both are proved in the theorem by `norm_num` (the first unfolds `certifiedRate`).
They are cheap rational arithmetic, not additional hypotheses. H2 has
`C_V = 10` and `q = 1119948287353 / 1120437614225`.

### Exact import and proof dependencies

[inputs-closure.tsv](/home/ubuntu/aklt/reports/ARCH_PKG/inventory/inputs-closure.tsv) lists every project source file,
physical line count, byte count, module-header flag and SHA-256:
**615 files / 90,501 physical lines / 7,190,677 bytes**, including Inputs itself.
[closures.json](/home/ubuntu/aklt/reports/ARCH_PKG/inventory/closures.json) gives the complete module graph.
Lean's own `--deps-json` confirmed all **11,380** headers in the Solution graph,
including external sources, meta imports and implicit Init imports.

There are **zero** imports from `AKLT/Cert/H1`, `AKLT/Cert/H3`, `CertData`,
`AKLT/W/H1C*`, `AKLT/W/H3C*`, `AKLT/W/H1M*` or `AKLT/W/H3M*`.
The proof export also has zero declaration hits in those layers.
`Blueprint.H3.Basic` and `Blueprint.H3.Positivity` remain; they are mathematical
contracts and positivity facts, not the excluded certificate or H3M layers.

The H2 sources retained are exactly `AKLT/Cert/H2/`'s `Check`, `Data`, `Finite`,
`Frames`, `Growth`, `Main`, `Mass`, `Trails` and `Words` modules.
The existing `AKLT/Defs/Automaton10Data.lean` is also a **source** dependency through
broad blueprint imports (1,631 lines / 3,282,597 bytes). Its presence does not add
an archive-check premise, and it is not the prohibited generated `CertData` layer.

The term directly names **244 canonical `AKLT.W.<KEY>.main` theorems**, plus
`AKLT.W.UNIQ_TOP.torusKernel` and `AKLT.Cert.H2.h2`.
The exact direct leaf list is [direct-leaves.txt](/home/ubuntu/aklt/reports/ARCH_PKG/inventory/direct-leaves.txt).
The full exported proof contains **260 canonical main/torusKernel leaf declarations**;
[reachable-leaves.txt](/home/ubuntu/aklt/reports/ARCH_PKG/inventory/reachable-leaves.txt) lists them all.
Its fifteen additional canonical leaves, used transitively by supplied leaf proofs,
are `REC001`, `REC002`, `REC003`, `REC039`, `REC041`, `REC043`, `REC046`, `REC050`,
`REC054`, `REC078`, `REC080`, `REC089`, `REC090`, `REC094`, and `REC096`
(all `AKLT.W.<KEY>.main`). Every reachable project theorem, including helpers and H2,
is listed in [reachable-project-theorems.txt](/home/ubuntu/aklt/reports/ARCH_PKG/inventory/reachable-project-theorems.txt).
This distinguishes source imports, direct theorem arguments, and actual exported proof
constants rather than treating every imported leaf as a used proof.

## Package layout and independent statement

The skeleton is [/home/ubuntu/aklt/wt/ARCH_PKG/palomar/](/home/ubuntu/aklt/wt/ARCH_PKG/palomar/README.md).

- `Challenge.lean`: **572 lines / 26,735 UTF-8 bytes**, one `module` header,
  Mathlib-only import, and one deliberate `sorry` in the selected theorem.
  It inlines the relevant definitions from eight statement-source files. All of
  PinModel and most of Domain/Geometry/Moment/Trails/Kernel are unnecessary and omitted;
  the obsolete parity-restricted `MainStatement` is omitted.
- `Solution.lean`: `module`, imports `AKLT.Final.Inputs`, defines the same three aliases,
  proves their equivalences and applies `main_of_inputs`. It never imports Challenge.
- `comparator.json`: selects only `AKLTPalomar.aklt_gap_of_inputs`, permits the three
  standard axioms and has no definition-hole exemptions.
- `Audit.lean`: axiom prints for all five new exported theorems and exact signature checks.
  `scripts/check_axioms.py` checks that all expected prints are present and allowed.
- `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`: self-contained Lake configuration,
  with `AKLT` library ownership of `AKLT.+`, and the pinned original dependency manifest.
- `formalization.yaml`, `README.md`: precise conditional mathematical coverage and companion
  artifact boundary; authors, maintainers, release license and public provenance remain
  clearly marked TODO. No author identity or licensing decision was invented.
- `FIDELITY.md`: the detailed mathematical correspondence requested for independent review.
- `scripts/make_challenge.py`, `statement-sources.json`: reproducible source fragment selection
  and original hashes. `scripts/inventory.py` regenerates the exact source lists without porting.
- `scripts/verify_sources.py`, `scripts/verify.sh`, leaf lists and `verification/`: future
  source/build/audit/Comparator commands and labelled local diagnostic receipts.

The three explicit interface theorems, all proved by `Iff.rfl`, are

```lean
AKLTPalomar.h1_iff : AKLTPalomar.H1 ↔ AKLT.Blueprint.Top.H1Statement
AKLTPalomar.h3_iff : AKLTPalomar.H3 ↔ AKLT.Blueprint.Top.H3Statement
AKLTPalomar.main_iff : AKLTPalomar.Main ↔ AKLT.Challenge.MainStatementV2
AKLTPalomar.aklt_gap_of_inputs : AKLTPalomar.H1 → AKLTPalomar.H3 → AKLTPalomar.Main
```

As in the model package, the inlined definitions use the original fully qualified names
in the independent Challenge environment. The Solution environment obtains those names
from the tree; the theorem-level equivalences make the semantic identifications explicit.
They do **not** waive Comparator's recursive declaration comparison.

The Challenge uses the model's eight auxiliary-proof-cache resets at original file
boundaries and `backward.proofsInPublic` to preserve generated helper names. These only
control names/visibility, not proof rules, kernel checks, or IO. The otherwise unnecessary
`trailWeight` is retained because it owns a numeral-proof helper shared by `trailBaseWeight`.
The Prop-valued instance `AKLT.Challenge.size_neZero` is explicitly `@[expose]`; the same
attribute must be supplied in its eventual tree port. An `@[expose] public section` alone
does not expose Prop-valued instances. No original statement or proof body was changed.

## Fidelity and mathematical coverage

[FIDELITY.md](/home/ubuntu/aklt/wt/ARCH_PKG/palomar/FIDELITY.md) gives a clause-by-clause table for each premise
and the headline, including indexing, exact constants, retained slot factors, tip
exceptions, finite laws, true revisits, all-cutoff quantification and both orderings.
Its principal references are:

| Surface | Exact paper location |
| --- | --- |
| H1 | `sec6-walks.tex:531–541`, `h:H1`; fixed theorem `sec8-inputs.tex:158–168`, `t:H1` |
| H1 pattern and laws | `sec6-walks.tex:488–519`, `d:pattern`; `sec2-moments.tex:8–29`, `d:moment` |
| H3 | `sec7-recursion.tex:598–612`, `h:H3` (displayed inequality 602–607) |
| H3 kernel/order | `sec7-recursion.tex:520–556`, `d:kernel`; `575–591`, `d:kernel-order` |
| Fixed input constants and certificate route | `sec8-inputs.tex:280–296`, `t:inputs` |
| Headline | `sec1-result.tex:39–45`, `t:main`; model `16–37`, `d:model` |
| Polynomial normalization | `sec3-quantum-frames.tex:14–23`, `d:poly`, and tensor identification 74–76 |

The headline proposition itself agrees with the paper: nonvanishing and exact kernel
at **every** pair of periods ≥ 3, then one eventual uniform positive gap with every parity.
H1 agrees at the two fixed thresholds; its four elementary threshold conjuncts are true
rational comparisons. Redundant removed/tip kept data and zero-weight spin labels change
only the indexing. H3 is exactly the displayed **every finite cutoff** assertion, not a
single finite prefix; h_C is the prescribed dyadic, not 6/5.

The proved implication is weaker than the paper's unconditional headline precisely
because H1 and H3 remain explicit antecedents. These semantic premises have universal
quantifiers; they are the consequences of finite computations, not themselves finite
Boolean certificate tests. The package certifies the analytic/algebraic reduction and H2.
The companion artifact supplies the separate H1/H3 verification routes under
`AKLT/Cert/H1`, `AKLT/Cert/H3`, `CertData`, H1C/H3C and H1M/H3M. Those computations were not
rerun here. Public immutable source/artifact identifiers and receipts must be filled
before release. [manuscript-sources.json](/home/ubuntu/aklt/reports/ARCH_PKG/manuscript-sources.json) fingerprints the
source text used for this note.

## Exact port list — no port performed

[palomar/port-list.tsv](/home/ubuntu/aklt/wt/ARCH_PKG/palomar/port-list.tsv) is the exact **local** Solution source
closure: **616 files / 90,537 physical lines / 7,192,086 bytes**. It lists module, origin,
release-relative path, original line/byte counts, header status and pre-port SHA-256.
It consists of the 615 original-tree files plus the module-system `Solution.lean`.
**615 lack `module`; none is over 10,000 lines.** The largest is Automaton10Data at 1,631.
The new Inputs is deliberately legacy-compatible today and is included among the 615 to port.

A populated release additionally contains Challenge and Audit: **618 Lean files**.
It should be a separate release root containing exactly the selected sources and this
skeleton. Submitting the entire current parent repository, even with `project_path=palomar`,
would expose every other unported Lean file to the repository-wide scan.

The **10,764 external dependency sources / 2,981,508 lines / 124,941,787 bytes** are listed
in [dependency-closure.tsv](/home/ubuntu/aklt/reports/ARCH_PKG/inventory/dependency-closure.tsv), with exact module paths
and hashes. They are resolved from the pinned Mathlib dependency graph and toolchain;
they are not sources to copy or port. Two trusted Std sources exceed 10,000 lines:
`Std/Data/DTreeMap/Internal/Lemmas.lean` and `Std/Data/Internal/List/Associative.lean`.
The per-submitted-repository source cap does not apply to these external toolchain files.
All external source headers are already modules.

The existing procedure is
`/home/ubuntu/aklt/reports/PAL_FIT/tools/port_modules.py`. It makes imports public and
ordinary declarations public/exposed while preserving explicit private declarations and
proof bodies with Lean's documented compatibility options. Run it only on the separate
materialized release copy; then additionally expose `AKLT.Challenge.size_neZero`, rebuild
and compare the resulting reachable helpers. No port or post-port success is asserted here.

A source token audit of the **616-file local closure** found no proof holes, forbidden
axioms, native proofs or unsafe declarations. Its sole listed exception is the existing
`set_option maxHeartbeats 0` at `AKLT/Cert/H2/Check.lean:5`, in the H2 certificate module
named by this brief. No new unlimited-heartbeat option was added. Among the four delivered
Lean files the only proof hole is the explicitly required Challenge placeholder.
See `closure-token-audit.json` and `delivered-source-audit.json`.

## Build, axiom and Comparator diagnostics

`PATH=$HOME/.elan/bin:$PATH lake build AKLT.Final.Inputs` **passes**.
The final run took **11.56 s**, peak process RSS **6.686 GiB**. It built Inputs with existing
pinned dependency/project artifacts; the other Lake jobs were cached/replayed.
It did not build Mathlib, fetch caches, or constitute a clean project build.
Full output: [inputs-build.log](/home/ubuntu/aklt/reports/ARCH_PKG/inputs-build.log).

The final canonical Challenge compiles directly with only pinned dependency paths,
under a verifier-generated random module alias, with candidate project objects removed
from `LEAN_PATH`. Its bytes match the delivered Challenge. The one expected warning is
the deliberately required theorem placeholder. `canonical-challenge.json` records the
alias, trusted paths and hash.

The delivered module-system Solution **cannot yet import the unported tree**:

```text
palomar/Solution.lean:1:0: error: cannot import non-`module` AKLT.Final.Inputs from `module`
```

This failed in 1.40 s; see `solution-module-build.log`. To run the proof and axiom checks
today, a separate diagnostic Solution copy removed only the `module` line, `public` from
its import, and the `@[expose] public section` command. No definition, theorem statement
or proof body changed. The same interface-only adaptation was applied to the audit.
Both compile; the audit runs with `-DwarningAsError=true`. The two source hashes and exact
transform are in `compatibility-copy.json`. This is not a source port or a successful
build of the final module-system Solution.

Exact axiom output for **every newly exported theorem**:

```text
'AKLT.Final.main_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLTPalomar.h1_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLTPalomar.h3_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLTPalomar.main_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLTPalomar.aklt_gap_of_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
```

`scripts/check_axioms.py` also passes on this transcript.
The full Solution export has **65,738 declarations**, exactly the same three axioms,
and **671,960,957 bytes**; its SHA-256 is
`63f03cc6a8040a757fe5fa26604fc39282c1028dc5d5d2d77f252fd395295556`.
`export-inventory.json` records this independently of the axiom-print transcript.

The read-only model's `scripts/verify_comparator.py` was actually invoked with this
package and the supplied verifier path. It stops at **“Wrong PalomarSubmission revision”**:
the model hard-codes `d4e41c1d5b0d114c4859e6e5831dc6d3ad1d0d44`, whereas the requested
read-only verifier is `14aa8d6b3c2f14a8540605e37144560b9a00e7e7`. Its source script also
hard-codes that package's twelve theorem names. Neither checkout was modified.
The failure receipt is under `model-run/slowequilibration-comparator-s8cfijy5/result.json`.

A direct Comparator-style run was therefore also performed using the supplied verifier's
export target/configuration helpers and the selected toolchain's real `lake comparator`,
with the canonical modern Challenge and compatibility Solution exports. It reaches the
recursive comparison and stops at:

```text
error: Const does not match between challenge and target 'AKLT.Defs.Compass.step'
```

The exact inspected difference is the matcher used in the otherwise identical body:

```text
modern Challenge: AKLT.Defs.Compass.step.match_1
legacy Solution:  AKLT.Defs.instReprCompass.repr.match_1
```

Legacy Lean exposes the `deriving Repr` helper, allowing the subsequent direction match
to reuse its matcher. Module-system Lean makes that helper non-exposed and creates the
public direction matcher. This is an actual module-system elaboration difference, not a
mathematical mismatch or an extra hypothesis. The source port and its regenerated proof
objects must be compared again; this run does **not** establish post-port Comparator
acceptance. Earlier numeric-proof-cache and private `size_neZero` helper mismatches were
resolved in the delivered Challenge by the explicit conventions described above.

No kernel phase of that failed Comparator run was reached. Separately, direct full-export
kernel diagnostics were run, one checker at a time, under a **31 GiB virtual-address limit**:

| Local stage | Exit | Wall seconds | Peak process RSS, GiB |
| --- | ---: | ---: | ---: |
| Compatibility Solution compile | 0 | 4.073 | 6.662 |
| Strict compatibility Audit | 0 | 3.973 | 6.653 |
| Canonical Mathlib-only Challenge | 0 | 4.028 | 3.672 |
| Canonical Challenge export | 0 | 8.975 | 6.362 |
| Full Solution export | 0 | 42.707 | 7.063 |
| Comparator on those exports | 1 | 22.786 | 1.138 |
| Lean kernel, full Solution export | 0 | 239.193 | 23.117 |
| Bundled rc2 con-ron, full export | 134 | 236.609 | 27.703 |
| NanoDa, correctly configured full export | 0 | 290.317 | 18.849 |

Lean's kernel accepted the full Solution export. NanoDa exited 0; its exact output is `solution-nanoda-configured.log` and `solution-nanoda-configured.stderr`. It checked 65,738 declarations with no typechecker errors; its sole nonfatal pretty-printer diagnostic was “Unable to print axioms”.
Bundled rc2 con-ron aborted with `memory allocation of 1280 bytes failed` under that local
address-space cap (exit 134 / SIGABRT). This is a failed local capacity diagnostic, not an
ill-typed-proof verdict, an authenticated production OOM, or a production inconclusive
classification. This standalone con-ron is the rc2 bundled checker, not the verifier's
separately authenticated production checker update.
An initial NanoDa harness call mistakenly supplied NDJSON where NanoDa requires a JSON
configuration; that exited 101 before replay. The configured run is the relevant result;
its configuration enables nat/string extensions, four threads and hard errors for any
unpermitted axiom. Every raw attempt is retained in `local-stages.json`.

[local-stages.json](/home/ubuntu/aklt/reports/ARCH_PKG/local-stages.json) records exact executable argv, paths, exits,
times and logs. `run_local.py`, `recompare.py`, `replay.py`, and `nanoda.py` reproduce the
diagnostic commands in this report directory. `toolchain.json` records binary digests.
The simple user-namespace bubblewrap probe passes here; no full production sandbox/cgroup
or clean-build claim follows from it.

The skeleton's source/config check also ran. Its three present Lean modules satisfy the
source-header/length rules, and its Comparator configuration is accepted by the official
parser. The check intentionally fails with **617** unfinished-release items: 615 source
paths have not been materialized, metadata contains TODOs, and a release root license is
missing. It does not mistake the three-file skeleton for the complete release.

## Production envelope and remaining work

The requested read-only verifier's README, `verification-profile.json`,
`execution-profiles.json` and `docs/launch-security-review.md` were read. Current README
and profile data take precedence over superseded launch-review history.

- Default profile: `palomar-namespace-16x32-v1`, 16 CPU / 32 GiB. Approved 32 CPU / 64 GiB
  retry has the same time budget and requires validated production OOM/timeout evidence.
- One **19,800 s** budget (350-minute job timeout) includes setup, pinned Mathlib cache,
  fresh-source build, Comparator and replay. Memory pressure/ceiling are 95%/98%, with
  at least 20 GiB free workspace.
- Lean **and NanoDa** must accept the full Solution export in production. con-ron is
  attempted with a 30-minute cap inside the same budget; only an authenticated capacity
  limit can justify its documented inconclusive outcome.
- The present replays are local, cached-source diagnostics without the production cgroup
  and are separate from statement comparison. No end-to-end budget or clean-build fit was
  established. The retained `AKLT.Cert.H2.Check` must be measured in the materialized,
  ported package; prior PAL_FIT virtual-address failures and this con-ron cap failure do
  not authorize the larger production tier.

No task-scoped mathematical proof obligation remains open. Release work is explicit:
materialize and port the 615 named tree sources, preserve/compare statement helpers,
rebuild `Solution`/`Audit`, complete metadata/license/immutable companion links, then run
protected statement comparison and clean production verification, including the proper
con-ron attempt. The independent reviewer still needs to evaluate `FIDELITY.md`.

## ORCH-SUMMARY
- Delivered `AKLT.Final.main_of_inputs : H1Statement → H3Statement → MainStatementV2`.
- Exactly two semantic premises; H2 is `AKLT.Cert.H2.h2`; both rate inequalities are proved.
- Inputs builds; all five exported theorem axiom sets are exactly the standard three.
- No H1/H3 Cert, CertData, H1C/H3C, or H1M/H3M imports or exported proof constants.
- Inputs project closure: 615 files / 90,501 lines; all 615 need module conversion.
- Solution local closure: 616 files / 90,537 lines; none exceeds 10,000 lines.
- Exact source lists, line counts, hashes, imports and direct/transitive leaves are supplied.
- Direct proof inputs: 244 canonical mains + torusKernel + H2.h2; 260 canonical leaves in export.
- `palomar/` contains the independent Challenge, Solution, Audit, Lake pins and metadata skeleton.
- Challenge is 572 lines / 26,735 bytes, Mathlib-only, with exactly the requested placeholder.
- Explicit `h1_iff`, `h3_iff`, `main_iff`; no Comparator definition exemptions.
- `FIDELITY.md` maps both premises and headline to exact paper labels/lines clause by clause.
- Companion finite checks are excluded, not rerun; public immutable artifact references remain TODO.
- No port performed. Final module Solution fails on legacy Inputs import, as documented.
- Compatibility Solution/Audit compile; canonical Challenge compiles; Lean full-export replay passes.
- Direct Comparator finds the modern/legacy `Compass.step` matcher identity difference.
- Expose `AKLT.Challenge.size_neZero` during port; preserve and recompare generated helpers.
- Bundled con-ron hit local 31 GiB address-space limit; production classification remains open.
- Configured NanoDa exit 0; raw receipts distinguish the corrected invocation.
- Fresh build, protected Comparator, production resource fit and production con-ron remain open.
- Author/maintainer/license metadata and independent fidelity review remain release decisions.
