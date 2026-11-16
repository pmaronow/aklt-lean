STATUS: NOT READY (1 blocking)

The installed **v4 integrator closes the audited MERGE overwrite race**. Candidate merges and builds use fresh disposable checkouts; the operator's MERGE checkout keeps its bytes and HEAD. Publication requires a matching private validation commit/base and uses compare-and-swap. The original interleaving regressions and independent late-write variants pass.

The deployment is nevertheless **not ready**: unmodified current `main` cannot initialize or integrate even a correct tiny writer because an existing library module violates the installed resource policy. This is separate from the repaired race and root-module issue. No production changes were made.

**Blocking 1 — Current main fails the mandatory validator before ordinary integration.**

Snapshot: `0959dfc2d693b843c431fa1bf2d2b227eafdc3c1` (`main`, benchmark relocation commit). [AKLT/Gen/Packed/Example.lean:2](/home/ubuntu/aklt/repo/AKLT/Gen/Packed/Example.lean:2) sets `maxRecDepth 100000`; the installed [certificate-modules.txt](/home/ubuntu/aklt/state/certificate-modules.txt) has no entries. The ordinary limit is 10000. `build_modules` scans the complete inventoried dependency order, so this unchanged base module blocks every candidate and its rejected-attempt archive.

A disposable clone retained all current source files, the actual Lake configuration and the exact installed certificate policy. The installed wrappers produced:

```text
aklt-freeze                         exit 0
aklt-init                           exit 1
aklt-integrator --once (TINYGOOD)    exit 1
aklt-integrator --once (TINYBAD)     exit 1
aklt: AKLT/Gen/Packed/Example.lean: maxRecDepth 100000 requires certificate allow-list
```

`TINYGOOD` contains `import AKLT` and `theorem tiny_good : True := True.intro`. `TINYBAD` replaces the conclusion with `False`, retaining `True.intro`; it passes the lexical gate but must fail Lean. Initialization failed before any `validated` ref existed. To exercise integration separately, the harness then **seeded a diagnostic ref at main without claiming validation**. Both tasks remain `finished`; `validated` and `main` remain at the original commit. The bad theorem never reaches its Lean verdict because the same base gate blocks first. Thus the requested successful unmodified-main end-to-end run is **not established**, and the bad task is not counted as a successful rejection.

[Test script](/home/ubuntu/aklt/scratch/V-ORCH-4/end_to_end.py), [commands and states](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/end-to-end.json), [log](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/end-to-end.log). Bring the library module and certificate/resource policy into agreement, then repeat initialization and correct/incorrect writer integration. An exception, if appropriate, must name the exact audited certificate module; broad gate relaxation is unnecessary.

A separate optional control added only `AKLT/Gen/Packed/Example.lean` to a disposable allow-list. It reached real library compilation (54 successful explicit module build logs, plus the root compilation) before the auditor stopped it with SIGINT. It did not complete initialization or integration and supplies **no readiness or proposed-fix validation claim**. Its private checkout was then removed. [Control record](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/main-policy-control.json).

**Verified race, publication and layout behavior.**

| Check | Result and evidence |
| --- | --- |
| Original ignored write immediately before actual Git merge | **Pass.** Exactly one write is injected after the operation journal/clean check. Exact binary bytes survive; `validated` stays fixed. The nonignored and Git-flag controls pass too. All three original test methods are verbatim; only the scheduler recognizes the new private merge path. [Tests](/home/ubuntu/aklt/scratch/V-ORCH-4/races/test_races.py), [race record](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/ignored-arrival-race.json), [log](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/races.log). The flag control adds `--no-overwrite-ignore` and is explicitly a modified-call control. |
| Arrival after the last scan, at actual ref update | **Pass.** Real publication proceeds while preserving operator HEAD and ignored bytes. The validated tree contains the writer bytes at the same relative path; the private checkout is removed. [Builder record](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/after-final-scan.json). |
| Independent late-write variants | **Pass.** Binary collision, newline filename, symlink, directory/file prefix collision, tracked edit and staged edit, all injected at actual ref update. Operator data survives, task is integrated, and the published commit equals a successful real `fast` result and publication receipt. [Tests](/home/ubuntu/aklt/scratch/V-ORCH-4/independent/test_independent.py), [binary record](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/independent-late-binary.json), [staged record](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/independent-late-staged.json). |
| Only validated disposable commits can publish | **Pass.** No live lease, no validation, wrong receipt commit/base, changed private HEAD and expired lease all refuse. A concurrent author advance injected at the actual Git CAS remains intact. [Resume4 tests](/home/ubuntu/aklt/scratch/V-ORCH-4/builder/test_resume4.py), [independent CAS record](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/independent-cas-race.json). |
| Failure and recovery paths | **Pass.** Private archive interruption disposes the checkout without touching operator MERGE; crash after actual CAS recovers after disposal; abandoned checkouts are preserved and never reused. Legacy recovery backs up ordinary/ignored bytes and requires manual reconciliation. [Builder log](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/builder.log), [focused recovery evidence](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/ignored-recovery.json). |
| Root module and both globs variants | **Pass.** Root-importing writers and root declarations survive fast integration and real leanexport → con-ron `--verified --jobs=1` → NanoDa validation with both `["AKLT.+"]` and `["AKLT", "AKLT.+"]`. [Builder tests](/home/ubuntu/aklt/scratch/V-ORCH-4/builder/test_resume4.py), [focused log](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/focused.log). |
| Actual current Lake configuration and out-of-library bench | **Pass on isolated layout control.** Uses the current lakefile verbatim, a root declaration, and a deliberately invalid/effectful `bench/Invalid.lean`. A correct root-importing theorem integrates; the incorrect theorem is rejected and archived as inert JSON, absent from the validated Lean tree. Full independent validation succeeds and includes the root declaration. [Record](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/independent-current-layout.json). This reduced fixture establishes layout support; it does not establish that current main's entire library passes. |
| Current-main inventory | **Pass.** Includes root `AKLT` and 95 submodules; excludes all 71 Lean benchmark files. [Inventory and gate scan](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/end-to-end.json). |

**Passed suites and provenance.**

Installed modules are imported directly from `/home/ubuntu/aklt/tools/v4`; public-command cases execute `/home/ubuntu/aklt/bin/` wrappers. Git, Lean and independent kernels are real. Agent/driver/tmux launch seams are mocked; none are launched.

| Suite | Result | Evidence |
| --- | --- | --- |
| Complete maintained V-ORCH-2 suite | 69 passed; 0 failures/errors/skips; 313.514 s | [Log](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/maintained.log), [JSON](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/maintained/suite-result.json) |
| Complete V-ORCH-3 focused suite | 16 passed; 0 failures/errors/skips; 164.645 s | [Log](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/focused.log), [JSON](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/focused/suite-result.json) |
| Complete V-ORCH-3 race/framing suite | 4 passed; 0 failures/errors/skips; 57.035 s | [Log](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/races.log) |
| Supplemental installed public-budget matrix | 1 passed | [Log](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/extra.log) |
| Resume4 builder regressions | 7 passed; 0 failures/errors/skips; 97.032 s | [Log](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/builder.log) |
| Auditor-authored independent cases | 8 passed; 0 failures/errors/skips; 96.108 s | [Log](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/independent.log) |
| Historical original-assertion replay | 35/43 passed; 3 failures, 5 errors; no skips; 236.303 s | [Log](/home/ubuntu/aklt/scratch/V-ORCH-4/original/evidence/replay.log) |

The historical replay retains eight known interface/policy incompatibilities: nineteen rather than twenty dispatcher entry points; immediate reopening after quota reset; the old module-build spelling in certificate inspection and timeout injection; the removed subprocess retry seam; the disabled unsafe `--driver` route; Python `runpy` parsing the Bash manual gate; and a persistent `wt/MERGE` build checkout. These are the same eight reported by PORT1 resume4. The maintained replacements all pass. None of the historical failures/errors are counted as passing. [Exact result list](/home/ubuntu/aklt/scratch/V-ORCH-4/original/evidence/suite-result.json).

The **105 passing maintained/additional cases** include all V-ORCH-2/3 test names with no removed or skipped cases. Coverage includes lexical/effect/resource gates, exact certificate exemptions and cache integrity, ownership/frozen hashes/modes, theorem kind/type/axioms, timeout attribution and culprit removal, ladder/retry inheritance and restrictions, both quota windows/resets/freshness/reserve/pauses, durable reservations and caps, dirty-checkout preservation, publication/recovery, checker failure propagation, composition, wrappers/status/digest, and cleaner/disk checks.

Private, Unicode, quoted and auxiliary exports still pass. The stress fixture inventories **5293 names** from **5286 generated theorems**: **2,204,485 argv bytes > 2,097,152 ARG_MAX**, an actual unchunked `E2BIG`, and **23 real export/checker chunks**. [Stress record](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/arg-max-export.json).

Harness sources are copied from the builder's v4 adaptations and compared with V-ORCH-3. Changes cover the explicit module targets, fresh validated snapshots for inventory, private receipt/disposal assertions, manual legacy recovery, and widened merge scheduler. Six original ignored/private/Unicode/interleaving test methods remain verbatim. Tiny baseline fixtures remain pinned to historical bootstrap `6ef9d9c2d9587a4522a2e942cc98ef58dcfe0921`; current layout/main are separately tested above. [Exact diff](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/suite-adaptations.diff), [provenance](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/provenance.json).

The first historical replay omitted the pre-created `original/test-runs` directory required by its earliest fixtures. Its setup failures are retained in [the initial log](/home/ubuntu/aklt/scratch/V-ORCH-4/original/evidence/initial-missing-fixture-dir.log); the full replay was restarted after creating that directory, without changing its assertions.

An initial independent fixture placed a newline in the writer's staged filename. The scope gate rejected its Git-quoted path, so five cases reached a safe archive instead of the intended successful writer publication. The corrected fixture uses a supported writer path and tests a newline separately in arriving operator data. No tool or preservation assertion was relaxed. [Retained initial log](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/independent-initial.log), [correction diff](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/independent-fixture-correction.diff).

Reproduction from `/home/ubuntu/aklt/scratch/V-ORCH-4` (all runners foreground):

```sh
export PYTHONDONTWRITEBYTECODE=1 GIT_OPTIONAL_LOCKS=0
export TMPDIR=/home/ubuntu/aklt/scratch/V-ORCH-4/tmp
python3 -B -u run_suite.py tests evidence/maintained
PYTHONPATH=tests python3 -B -u run_suite.py focused evidence/focused
PYTHONPATH=tests python3 -B -u run_suite.py races evidence/races
PYTHONPATH=tests:supplemental python3 -B -u -m unittest test_extra -v
PYTHONPATH=tests python3 -B -u run_suite.py builder evidence/builder
PYTHONPATH=tests python3 -B -u run_suite.py independent evidence/independent
python3 -B -u run_suite.py original/tests original/evidence
# These clone-creation scripts require a fresh destination, as used in this audit:
python3 -B -u end_to_end.py
python3 -B -u main_policy_control.py
python3 -B verify.py
```

**Preservation, resources and limits.**

All **119 protected records** match their captured hashes/modes/links, including installed sources/wrappers, configuration, original credit baseline, frozen manifest, certificate policy and prior audit inputs. All four installation receipts match their source files. Final verification finds **332 valid shared-package links**, no remaining disposable `.lake/build` trees, and about **0.659 GB** of V-ORCH-4 disk use, below 10 GB; free disk is about **180.9 GB**. [Verification record](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/verification.json), [verification log](/home/ubuntu/aklt/scratch/V-ORCH-4/evidence/verification.log). The initial resource verifier mistook an intentional nested fake-cache test directory for a real package cache; the final verifier checks actual worktree roots.

All audit writes are under the two V-ORCH-4 roots, including temporary files. Shared packages are symlinked read-only; disposable builds are private. At most four Lean-using runners overlapped, and each campaign serializes every Lean child through its installed admission lock: at most four audit Lean processes. Per-runner visible `/proc` samples observe at most one Lean process; these are not a global host count. No daemon, agent, sub-agent or tmux session was started. Full independent checkers were exercised on the tiny/layout/name fixtures, not the entire production corpus or a four-hour certificate.

ORCH-SUMMARY
- Installed dispatcher and sources: v4.
- Original MERGE ignored-write overwrite race: closed in tested interleavings.
- Disposable commit/validation matching and CAS protections: pass.
- Late binary/symlink/directory/tracked/staged/newline variants: pass.
- Root module, both globs and bench exclusion: pass on layout controls.
- Maintained/additional suites: 105 passed, no skips.
- Historical replay: 35/43 pass; 8 obsolete interface/policy expectations reported separately.
- Current-main dry run: blocked before ordinary task validation.
- Blocking count: 1, Packed Example resource option versus empty allow-list.
- Disk: 0.659 GB; at most 4 audit Lean processes; private builds removed.
- Production edits/ref updates, daemons, agents, tmux: none by this audit.
