STATUS: NOT READY (2 blocking)

Re-audited the installed **v3** tools and dispatcher on 2026-11-16. The original ignored-file collision is fixed when the file exists at admission, and private/Unicode/quoted/auxiliary declaration export passes real independent validation, including an inventory exceeding the host's ARG_MAX. The manual `aklt-gate` delegates to `aklt-budget-check` and passes the previously failing decisions. However, an ignored write arriving between admission and merge still loses bytes, and the current campaign Lake configuration prevents ordinary integration. No production fixes were applied.

The maintained V-ORCH-2 suite passes **69/69**, with its supplemental public-command test also passing. The additional tests expose the two blockers below. There are no other observed regressions on the original bootstrap fixture; this does not establish readiness of the current campaign configuration.

| Requested check | Result | Evidence |
| --- | --- | --- |
| Existing ignored MERGE files, regardless of extension | **Fixed for files present at admission; concurrent-write bypass remains** | Original regression retained verbatim: exact binary bytes preserved, task remains `finished`, `validated` unchanged. [Original collision result](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/ignored-merge-loss.json). |
| Other extensions and nested ignore rules | **Pass** | Ten extension/no-extension collisions; nested `.gitignore`, `.git/info/exclude`, and configured `core.excludesFile` rules; newline/tab/Unicode/hidden/option-like filenames; directory/file prefix collision; ignored symlink; root/outside-AKLT files; eleven Lake exemption near misses. [Tests](/home/ubuntu/aklt/scratch/V-ORCH-3/focused/test_focused.py:48), [extension results](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/extension-collisions.json), [nested exclude results](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/nested-info-exclude.json), [near misses](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/ignored-near-misses.json). |
| Alternative mutation/recovery paths | **Pass for existing dirt** | Direct reset/combine/archive/begin-operation calls and actual `aklt-integrator --once` refuse. Interrupted recovery backs up exact nested ignored bytes and archive bytes, refuses unrelated data, and succeeds after operator reconciliation. Genuine Lake output exemptions still permit real integration. [Public command](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/public-ignored-admission.json), [recovery receipt](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/ignored-recovery.json). |
| Private, Unicode, `«…»`, numeric-string and auxiliary names | **Fixed; pass** | Original two regressions retained verbatim. Additional real fixture exports 78 names: private numeric components, private inductive declarations, recursors, constructors/projections, match helpers, equation lemmas, Unicode, quoted dots/spaces/tabs/newlines/U+2028, `«123»`, `«--help»`, and `«--format=json»`. Con-ron accepts 116 declarations including dependencies; NanoDa succeeds. [Names and receipt](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/auxiliary-export.json). |
| Very many names exceeding actual ARG_MAX | **Pass without mocking chunking** | 5,286 distinct generated theorems; 5,293 inventoried names; **2,204,485 argv bytes including pointers > 2,097,152 ARG_MAX**. The unchunked argv produces actual `E2BIG`. Full validation naturally makes **23 real exports**; every con-ron `--verified --jobs=1` and NanoDa invocation succeeds; requested counts sum to the complete inventory. [Record](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/arg-max-export.json). |
| Name framing and argument rejection | **Pass** | A quoted declaration containing a newline, tab, quotes and `AKLT_NAME` text remains one name; no forged inventory entry appears. `AKLT_AUDIT_OK` inside another name cannot forge a receipt. Full export succeeds. UTF-8/environment/pointer budgeting and empty/NUL/option-like/oversized argument rejection also pass. [Framing evidence](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/name-framing.json), [tests](/home/ubuntu/aklt/scratch/V-ORCH-3/focused/test_focused.py:290). |
| Manual launch gate | **Fixed; pass** | Executes the installed shell wrapper, not a Python emulation. The six V-ORCH-2 bypasses now reject: future event, spend hold, newest missing limits, reset hold, manual pause, newest event beyond sixty file mtimes. Default and explicit N=0/1/4 decisions, invalid N and exit-status propagation match budget-check. [Reserve matrix](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/manual-gate-reserves.json), [retained suite](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/complete-suite.log). |

**Blocking 1 — An ignored MERGE write arriving after the final cleanliness check is overwritten.**

Location: [aklt_integrate.py:156](/home/ubuntu/aklt/tools/v3/aklt_integrate.py:156), particularly the real merge call at line 158. The new enumeration in `Context.clean_head` is correct for existing files, but its check and the destructive Git operation are separate.

`MergeInterleaving.test_ignored_note_arriving_before_merge_is_preserved` stages an allowed writer file at `AKLT/W/ARRIVAL/operator.bin`, ignored through the disposable repository's `.git/info/exclude`. MERGE initially is clean. The test schedules one operator write **after `begin_operation` has checked cleanliness and saved its journal, immediately before the actual Git merge**. Only this timing is injected; the installed controller, Git merge, Lean builds, audits and publication all execute normally. No concurrent process is needed to make the interleaving deterministic.

The operator bytes `operator arriving edit\x00\xff\n` become `writer replacement\n`. Integration returns without an error, the task becomes `integrated`, and `validated` advances. The journal knows the destination path but does not back up these arriving bytes. This is a narrower remaining bypass than the original pre-existing-file defect: it requires an operator or another process to write MERGE during integration.

[Test](/home/ubuntu/aklt/scratch/V-ORCH-3/races/test_races.py:53), [byte/ref/state evidence](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/ignored-arrival-race.json), [complete log](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/races.log). It reproduced twice. The matched nonignored-write control preserves bytes and holds `validated`. A separate mitigation probe adding `--no-overwrite-ignore` to the real merge also **fails** on installed Git 2.43.0 with this `--no-ff` merge; that probe is explicitly not an unmodified installed-tool test. [Nonignored control](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/arrival-control-nonignored.json), [flag-only probe](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/arrival-control-git-guard.json).

Required correction: protect the mutation itself against late operator writes, or perform candidate merges in an isolated disposable checkout while preserving the operator's checkout. Retain this interleaving regression. Another earlier cleanliness scan, or the tested Git flag alone, does not close it.

**Blocking 2 — The current Lake globs omit the root module required by the validator.**

Locations: [lakefile.toml:12](/home/ubuntu/aklt/repo/lakefile.toml:12), [aklt_validate.py:22](/home/ubuntu/aklt/tools/v3/aklt_validate.py:22), [aklt_validate.py:129](/home/ubuntu/aklt/tools/v3/aklt_validate.py:129). This is a **current deployment/configuration incompatibility**, not a change introduced by the v3 name/ignored-file fixes.

Live main acquired `globs = ["AKLT.+"]` in commit `3166ac0` at 05:45 UTC, after the earlier audit/builder runs. The inventory includes `AKLT.lean`, but `lake build AKLT` resolves the library target, whose new globs build submodules without the root `AKLT.olean`. The audit then imports `AKLT` and fails with:

```text
error: object file '…/wt/MERGE/.lake/build/lib/lean/AKLT.olean' of module AKLT does not exist
```

The initial full replay against the live bootstrap yielded **13 errors in 69 maintained cases**. A separate tiny reproduction changes only the original fixture's Lake configuration to the current globs, then tries an ordinary valid theorem. It reproduces the missing-root failure, leaves the task `finished`, and does not advance `validated`. This blocks ordinary integration; a fresh full-validation checkout has the same build/import mismatch. [Reproduction test](/home/ubuntu/aklt/scratch/V-ORCH-3/focused/test_focused.py:345), [result](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/current-globs-regression.json), [initial full replay](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/live-bootstrap-suite.log).

Positive control: changing only the disposable Lake globs to `["AKLT", "AKLT.+"]` restores both real integration and full leanexport/con-ron/NanoDa validation. [Control test](/home/ubuntu/aklt/scratch/V-ORCH-3/focused/test_focused.py:332), [receipt](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/root-glob-control.json). Include the root in the deployed library globs or make the controller explicitly build every inventoried module using an unambiguous module target.

**Complete suite, adaptations and reproduction.**

Tests import `/home/ubuntu/aklt/tools/v3` directly; public-command tests execute installed wrappers. Implementation files were not copied or patched. Agent, driver and tmux launch seams remain mocked. Lean, Git and independent validators are real, except the explicitly labelled Git-flag mitigation probe.

To reproduce the V-ORCH-2 baseline deterministically, disposable clones are pinned to its original bootstrap commit `6ef9d9c2d9587a4522a2e942cc98ef58dcfe0921` before the tiny fixture is constructed. The current-globs failure is separately preserved and tested above. Other harness changes are v2→v3 imports and replacing the retired Python gate's `runpy` seam with execution of the real shell wrapper. **No maintained assertions were weakened or skipped**, and the original ignored/private/Unicode regression methods are verbatim. [Exact diff](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/suite-adaptations.diff), [provenance](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/provenance.json), [fixture rationale](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/fixture-pin.json).

Run from `/home/ubuntu/aklt/scratch/V-ORCH-3`:

```sh
export PYTHONDONTWRITEBYTECODE=1 GIT_OPTIONAL_LOCKS=0
export TMPDIR=/home/ubuntu/aklt/scratch/V-ORCH-3/tmp
python3 -B -u run_suite.py tests evidence > evidence/complete-suite.log 2>&1
PYTHONPATH=tests:supplemental python3 -B -u -m unittest test_extra -v > evidence/extra.log 2>&1
PYTHONPATH=tests python3 -B -u run_suite.py focused evidence/focused > evidence/focused.log 2>&1
PYTHONPATH=tests python3 -B -u run_suite.py races evidence/races > evidence/races.log 2>&1
python3 -B -u run_suite.py original/tests original/evidence > original/evidence/replay.log 2>&1
python3 -B verify_audit.py > evidence/verification.log 2>&1
```

| Run | Outcome | Evidence |
| --- | --- | --- |
| Entire maintained V-ORCH-2 suite | **69 passed**, 0 failures/errors/skips; 274.790 s | [Log](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/complete-suite.log), [JSON](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/suite-result.json) |
| Supplemental real public-budget matrix | **1 passed**, including nine fixtures across both commands | [Log](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/extra.log) |
| New focused cases | **15 passed, 1 failed**, 0 errors/skips; failure is Blocking 2; 144.541 s | [Log](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/focused.log), [JSON](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/focused/suite-result.json) |
| Race/name-framing cases, including flag-only probe | **2 passed, 2 failed**, 0 errors/skips; both failures demonstrate Blocking 1, one with the mitigation flag; 40.046 s | [Log](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/races.log), [JSON](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/races/suite-result.json) |
| Historical original-assertion replay | **38/43 passed; 2 failed, 3 errored**, 0 skips; 219.623 s | [Log](/home/ubuntu/aklt/scratch/V-ORCH-3/original/evidence/replay.log), [JSON](/home/ubuntu/aklt/scratch/V-ORCH-3/original/evidence/suite-result.json) |
| Integrity, provenance, syntax/static review and resource verification | **Passed** | [Log](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/verification.log) |

The historical replay retains the five incompatibilities already documented in PORT1 resume3: nineteen-command count, immediate reopening after quota reset, removed subprocess retry seam, unsafe `--driver` expected to reach delegation, and Python `runpy` attempting to parse the retired shell gate. Those results are not counted as passing. Initial live-bootstrap logs and fixture-development failures are retained separately; the invalid first large-name fixture used the reserved `λ` token in an unquoted identifier and was corrected to `ε` before the final run.

The **70/70 passed maintained cases** cover lexical/effect/resource-option gates and exact certificate exemptions; frozen hashes, ownership, file modes and clean checkouts; certificate cache reuse/corruption; exact theorem type/kind/axioms and deferred infrastructure failures; the two-attempt ladder, inheritance and first-line reports; retry/session/effort/root restrictions and no agent kills; both quota windows, Decimal credits, freshness, reserve, resets and pauses; caps, leaf ownership and durable reservations; dirty-main/dirty-MERGE preservation and recovery; validation-before-publication and journal recovery; timeout attribution, culprit removal and duplicate batches; exporter/checker failure propagation; composition/fixed-point/generated terms; all twenty dispatcher help entry points, status/digest, read-only writer sandbox, cleaner and disk bounds. Every individual case is listed in the complete log.

**Preservation, resources and limits.**

The installed v1/v2/v3 receipts match their files. All **79 protected pre/post records** match, including supported wrappers/dispatcher/gate, tool sources, original credit baseline, frozen manifest, configuration and historical audit sources. Gate SHA-256 remains `23d218f12f4e7625fce58a648466b8edada9fcdd5c2fdfa61452c53969dfa107`. The live campaign was active independently: its refs/Git metadata/quota cache changed, and the unrelated manual `bin/merge-validate.sh` was externally edited at 05:48 UTC. That script was not executed by this audit. These changes are recorded explicitly rather than asserting the live repository remained immutable. [Integrity record](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/immutability.json), [static review](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/static-review.json).

All audit writes and temporary files are under the two authorized V-ORCH-3 roots. At most three audit runners overlapped, each with sequential compiler/checker calls and a per-fixture Lean lock: at most **three audit Lean processes**, below four. Each runner observed at most one Lean process in its visible process namespace; those samples are not a global process measurement. No daemon, model agent, sub-agent or tmux session was started. Cleanup verifies **479** package symlinks and no remaining disposable `.lake/build` trees. Scratch use is approximately **277 MB**, below 10 GB; free space was approximately **188 GB**. [Resource record](/home/ubuntu/aklt/scratch/V-ORCH-3/evidence/final-resources.json).

Validation exercised real small modules and a 5,286-theorem stress fixture, not the entire evolving production certificate corpus or a four-hour certificate. No live campaign reset was acknowledged, baseline rebased, or production file/ref changed by this audit.
