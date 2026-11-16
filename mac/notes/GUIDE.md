# A guide for Lean formalization campaigns

This is the default procedure as of 2026-10-27. It replaces the guide of 2026-10-20
(`Result Archive/Lean_formalization_guide_2026-10-20/`). That guide predates three changes: the Luna-first proof
ladder, Opus as the third rung, and the ban on redundant agents. Where the two differ, this one governs.

It draws on three campaigns, each run on AWS by a Claude Code orchestrator:

| Campaign | Dates | Result |
|---|---|---|
| SK Glauber upper bound | 2026-10-19/20 | The c < 1/4 bound was proved in Lean. The Palomar package passed the clean build, the Audit and the three-kernel Comparator |
| Spherical SK dynamics | 2026-10-20 to 10-26 (3 sessions) | All 21 Challenge Props were certified, on a blueprint of 1,146 leaves. The Ramírez–Rider–Virág edge limit remains an explicit premise inside the Airy Props |
| Superfluid stiffness / NCRI | 2026-10-25 to 10-27 (3 sessions) | All four headline theorems were certified unconditionally (51,967 declarations) |

Detailed records:
- **Glauber:** `REPRODUCE.md` in `Result Archive/SK_two_sided_hexagon_2026-10-19/`.
- **Spherical:** `~/sq-lean/NEXT.md` and `~/sq-lean/RESUME.md` on the Mac.
- **Superfluid:** `~/sf-full/RESUME.md` and `~/sf-full/NEXT.md` on the Mac, with tools in `~/sf-full/tools` and briefs in
  `~/sf-full/briefs`.

## 1. The shape of a campaign

1. **Map the gap.** Write down the exact target, what is already proved, what is missing, and where reusable code
   might exist.
2. **Referee the paper proof.** Two independent Sol referees check it before anything is formalized. The paper is then
   frozen until the Lean is done.
3. **Search donors and literature (§4), and audit the hypotheses** that the paper takes from the literature.
4. **Blueprint.** A Sol architect states every step as a closed Lean proposition and proves the assembly.
5. **Truth sweep.** Check every open leaf for truth before the first writer wave.
6. **Writer waves.** Writers climb the proof ladder (§5), and their work is integrated continuously.
7. **Consolidate and close.** Merge the partial results into canonical jobs, compose the frontier into an exact list of
   open nodes, and finish them.
8. **Release.** Audit the statement, run the cheap checks, then run one clean three-kernel verification.
9. **Wrap up and back up** at the end of every session.

## 2. Before the run

**Ask for every approval at once:**
- the instance type and size, given the account's vCPU quota;
- Codex sandbox network access (`[sandbox_workspace_write] network_access = true`), which Lean Beam needs.
  Without it, the Glauber writers went 3.5 h without Beam;
- headless agents skipping permission prompts, and sudo, on the workstation only;
- the repository and push policy: private repositories, with validated milestones pushed;
- the hypothesis policy:
  - refereed published theorems may become explicit, named hypotheses, stated as transparent Props and never as
    axioms;
  - ask before any analytic foundation becomes a hypothesis;
  - the goal is an empty hypothesis list;
- the Codex quota floor for the session, and what to do on a Codex reset or on exhaustion;
- the point on the Claude session limit at which Opus launches stop.

Any narrowing of verification is the author's decision.

**AWS.**
- Use region us-east-2 and profile `agent-toolkit` (`aws login --profile agent-toolkit`). The login lasts 12 h.
  Check it before leaving a run unattended and before wrap-up; it expired at wrap-up twice.
- Codex agents get no AWS tooling: no MCP server, no skills, no credentials.
- **Memory is the limit, not CPU.**
  - Plan 2–3 GB per Lean writer, with spikes to 7–8 GB during exports.
  - 128 GB holds 25–30 writers; 64 GB with 25 writers swapped heavily.
  - The superfluid campaign ran up to about 90 agents on an r7i.16xlarge, later an r6i.16xlarge (64 vCPU, 512 GB).
    That is the account's whole 64-vCPU quota, so only one such machine can run at a time.
  - r7i capacity in us-east-2b is sometimes missing; r6i works.
- **Disk:** gp3 and encrypted, at least 600 GB. Large waves need 1.5 TB at 16k IOPS and 1000 MB/s, because each
  worktree copies a ~7 GB build unless builds are linked. AWS allows one volume modification per 6 h.
- **Access:** require IMDSv2, open SSH only to the Mac's IP, and add a swapfile.
- **IP address:** the public IP changes at every start, so update `~/.ssh/config` and the campaign's IP file.

**Provisioning** (script: `~/sf-full/tools/provision.sh`):
- Install Lean at the pinned version via elan, the Mathlib cache, Codex CLI, Claude Code, Lean Beam, leanexport,
  con-ron, NanoDa and the Palomar Comparator.
- On Ubuntu 24.04, enable unprivileged user namespaces; both the Codex sandbox and Palomar's verifier need them.
- Run a baseline build and a full validation before any agent starts.

**Accounts and credentials.**
- GitHub credentials stay on the Mac, and only the Mac pushes.
- Before computing a budget, check which Codex account each machine is logged into (`~/.codex/auth.json`). The Mac and
  the workstation have been on different accounts.
- Quota readings come from `rate_limits` in the `~/.codex/sessions` rollout files.

## 3. Roles

| Agent | Use for |
|---|---|
| Orchestrator (Claude Code, Opus, on the Mac) | Writes briefs, launches agents, reads every report, decides, handles integration exceptions, commits, keeps the log |
| Luna (Codex GPT-6-Luna) | The first attempt on every proof leaf; the quota watcher; cheap bulk checks |
| Sol (Codex GPT-6.1-Sol) | The second attempt (max effort) on leaves Luna fails. Also all statements, blueprints, splits, consolidation, truth sweeps, audits, referees, compositions and releases |
| Opus (Claude Code subagents) | The third attempt on leaves Sol fails; one or two at a time on creative architecture obstacles |
| Terra (Codex GPT-6.1-Terra) | Not a regular rung; at most a second opinion from a different model after Sol fails |
| Sonnet | A health-check cron job and bookkeeping |

Prices per token, relative to Sol: Luna 5%, Terra 50%.

## 4. Planning, before any writer starts

**Donor search and literature review** come at the start.
- **Sources:** your own repositories (aging-palomar, spherical-dynamics-lean, fluctuations-palomar-temp, …), OpenAI's
  math repository (HardSphere), Mathlib, other formalizations and the web.
- **Vendoring:** vendor what you reuse at the same pin, with its licence and a record of where it came from.
- **Repeat** the search whenever a new plan appears: a new blueprint, a split, a change of approach, a stuck node.
  Each new plan creates narrower targets that a broader search could not look for.
- **Hand results over:** pass what the search finds to the writers as data.

**Audit the hypotheses early.** Dedicated search and referee agents re-examine every input taken from the literature.
On spherical, donor proofs eliminated GOE rigidity and the Landon–Sosoe counts, leaving a single hypothesis.

**Blueprint.**
- A Sol architect at max effort writes it; Opus comes in only for creative obstacles.
- Every step is a closed `…Statement : Prop` with a proved assembly, so all leaves can run in parallel.
- Keep nodes to about 400 lines, or 1–2 h of agent work. Split hard nodes a second time inside the first blueprint;
  that was the biggest single speedup.
- Before a later architect's wave, check its dictionaries against earlier ones, so that no lemma is proved twice
  (the DEDUP rounds).
- Launch no writers before the blueprint exists. In the Glauber campaign that wasted a whole wave.

**Freeze the statement layer.** Validation checks the hashes of the frozen statement files. Corrections become new
`…V2`/`…V3` nodes, and frozen files are never edited. An architect who kept refining statements after writers had
started broke proofs that were already integrated.

**Truth sweep before each writer wave.** Sol agents at max effort take about 10 leaves each and write their verdicts to
JSONL as they go. On spherical, 44 agents swept 427 leaves in about 40 min and found 136 leaves missing premises and 9
false leaves.

**Lint for Lean traps:**
- `ContDiff ℝ ⊤` means real-analytic in current Mathlib; use `∞`. Fixing this exposed about 22 vacuous "proofs".
- `Encodable.decode` may repeat indices; use `decode₂`.
- `NormedSpace.exp` applied to a raw lambda is the pointwise exponential.
- Integrals appear without `Integrable` hypotheses.
- Section typeclass arguments (e.g. `CompleteSpace`) silently drop out of statements that do not use them.
- Statements about `AEEqFun` can depend on the chosen representative; one such node was undecidable.
- Labelled vs. symmetric domains, connectedness, and empty cases.

**Interface audit before the closing compositions.** Check that the packages actually compose into the Challenge
statements, and add adapter nodes for the mismatches. On superfluid there were 56 groups of mismatches and 68 adapter
nodes.

**Challenge files** import only Mathlib and stay short (Palomar prefers 300 lines or fewer). They read as ordinary
mathematics, and a Sol fidelity referee checks them.

## 5. The proof ladder

Each leaf has one agent at a time, climbing:

1. **Luna**, at xhigh effort, or max on hard leaves. A paired test on 12 leaves:
   - easy leaves: 6/6, at 0.08–0.20× Sol's cost;
   - hard leaves: mostly fast partials. One was proved at 0.42× Sol's cost, and failures cost 0.02–0.06×.
2. **Sol at max effort** on the same leaf, in a worktree where Luna's attempt is visible. Starting from a partial, Sol
   proved 3 of 4 hard leaves, using 0.7–0.9× the tokens of Sol from scratch.
3. **Opus** on leaves Sol fails.
   - Opus agents are Claude Code subagents on the Mac that work on the workstation over SSH.
   - Each works in a worktree made from `validated`, which contains the earlier attempts.
   - Its wrapper brief lists those attempts and Sol's last verdict (`~/sf-full/briefs/S3/OPUS-wrapper.md`,
     `~/sf-full/tools/s3/opus-prompt.sh`).
   - Launch one per Sol failure, with no fixed cap, and stagger large bursts.
   - Stop launching at 60% of the Claude session limit. That meter cannot be read inside the session, so ask the
     author for `/usage`.
   - On superfluid there were 11 attempts: 9 proved, 1 partial that closed by composition, and 1 that found its node
     undecidable.
4. **Exhausted leaves** — failed at every rung — go to consolidation or a re-route.

Rules:
- **No redundancy.** Never put two agents on the same leaf or task at the same time. Spare capacity goes to other open
  work or stays idle.
- **Check every claimed proof.**
  - Run an exact-type check, `example : <leaf> := <thm>`, plus `#print axioms`; a successful build is not enough.
  - Detect proved nodes in Lean (`ProvedNodes.lean`), not with grep.
- **Partial results must be compiled.**
  - The leaf is proved from explicit, transparent residual nodes.
  - A Sol consolidation round (RESID) dedups the residuals across writers into canonical jobs, which go back on the
    ladder.
  - Never trigger launches from words in a final message: the word "partial" in an architect's report once launched 21
    duplicate writers.
- **False or under-premised leaves.** The writer reports a counterexample and a corrected `…V3` statement, and a fix
  architect re-routes the consumers.
- **Escalate early.** Escalate a critical-path leaf as soon as Sol reports PARTIAL.

**Briefs** (template: `~/sf-full/tools/s3/LEAF-template.md`):
- **Scope.** Read `AGENTS.md` first. Write only under the task's own namespace directories, and never edit existing
  files.
- **Soundness.**
  - Forbidden tokens: `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `opaque`.
  - Allowed axioms: `propext`, `Classical.choice`, `Quot.sound`.
- **Building.**
  - Build single modules, never the whole package.
  - Give conditional resource caps ("≤ 2 Lean processes while other agents run"). If an agent will be alone on the
    machine, say so.
- **Delivery.**
  - No subagents, and no stopping before the deliverable exists.
  - The report opens with a status line: PROVED, PROVED FROM DEPS, PARTIAL or FALSE.
- **Scratch.** Use unique scratch tags. A shared tag in one brief collided with the integrator's own validation run.

**Codex mechanics:**
- **Resuming.**
  - `codex_sol.py`, `codex_luna.py` and `codex_terra.py resume` keep the effort, search setting and writable roots
    (since 2026-10-26). Sessions recorded before then need `-e` passed explicitly.
  - On "Selected model is at capacity", resume the same session with a growing sleep and the same effort.
- **Changing constraints.** To change a running agent's constraints, stop it and resume it with an explicit orchestrator
  message. An agent whose files are edited mid-run reads that as tampering.
- **Service tier.** Never use Codex's Fast/priority tier.

## 6. Workstation operations

**Running and integrating**
- **Long jobs.** Run them in tmux on the workstation, never through long SSH calls from a Mac that may sleep. The Mac
  watches completion flags (`~/sf/flags/<KEY>.done`).
- **Worktrees.**
  - Each task gets one git worktree, linked to a shared prebuilt build (`sf-mkwt4`, about 1 s).
  - Never work in the main checkout: the integrator's hard reset wipes uncommitted edits.
- **Commits.** Codex agents cannot commit, because a worktree's git metadata lies outside their writable roots; the
  integrator commits for them.
- **Integrator daemon** (`sf-integrator4.py`).
  - It merges tasks as they finish, batching those that finish together and falling back to one at a time.
  - Culprit removal iterates until the batch validates, and the daemon then moves `validated`.
  - Architect deliveries are accepted in batches, with `validated` merged into each worktree first.
- **Validation tiers.**
  - Each batch runs `sf-validate-fast`: build, frozen hashes, forbidden-token scan, and an axiom audit of the changed
    modules.
  - The full `sf-validate` (export plus `con-ron --verified`) runs at milestones, before releases and at wrap-up. It is
    chunked through `export-chunks.sh` once the name list exceeds ARG_MAX.
  - Running the full validation on every batch took about 13 min per cycle.

**Budget and monitoring**
- **Launch queue** (`sf-queue5.py`; each task names its model).
  - `sf-budget` gates launches: remaining quota minus a reserve per running agent (about 0.25–0.4 points) minus a
    margin, compared with the session floor.
  - Never kill running agents to save quota.
- **Quota watcher.**
  - A deterministic rule decides, a Luna agent at medium effort cross-checks it, and disagreements are logged. A
    low-effort Luna watcher acting alone once raised a false pause.
  - A reset (the allowance rising more than 5 points above its minimum) or exhaustion (≤ 3%, or rate-limit errors) sets
    `WRAPUP_MODE` and `QUEUE_PAUSE`. Nothing is killed.
- **Cleaner daemon.** Run it from the start for worktree builds, excluding infrastructure worktrees such as MERGE and
  VENDOR.
- **Digest and health check.** A digest every 10 min (`sf-digest`) and a Sonnet health-check cron job.

**Hazards**
- **Integrator state.** Pause the integrator and wait until it is idle before editing `integrator-state.json`. Its
  in-memory copy overwrote edits, and 39 retries were silently skipped.
- **Restarting a killed integrator.** First run `git reset --hard validated`, then reconstruct the merged tasks from
  `git log validated`.
- **Running scripts.** Never overwrite a shell script that is running (bash reads scripts incrementally). Deploy under a
  new name.
- **Self-matching kills.** Never run `pkill -f` or `pgrep -f` inside an SSH command whose text contains the pattern; it
  kills its own shell. Use a bracket pattern like `[c]odex`, or kill by tmux session or PID.
- **Sandbox path checks.** Path checks inside the Codex sandbox see bwrap mount points that vanish outside it.
- **Final validation.** Before it, compare the working tree with HEAD. One integration path left committed files
  missing on disk.

## 7. Validation ladder

| Stage | Checks |
|---|---|
| Writers | Beam, module builds, exact-type check, `#print axioms` |
| Integration | combined build, clashing names, frozen hashes, token scan, axiom audit of new declarations |
| Milestones | export plus `con-ron --verified` on the whole validated head |
| Final theorem | transitive constant check; con-ron and NanoDa on its export; adversarial statement audit |
| Release | Palomar Comparator with three kernels, on a clean clone |

The statement audit unfolds every definition down to Mathlib and checks non-vacuity, with nonvacuity witnesses such as
`…_exists`.

Searching the text for `sorry` is not proof of soundness. Rely on axiom collection.

## 8. Release and packaging

**Decide first:**
- the claims and their Lean names;
- the repository, private until the author decides;
- the authors and maintainers;
- a frozen copy of the manuscript.

**Checks and verification:**
- Finish the statement audit and an independent package review before verifying.
- Run the cheap checks (Audit, the Comparator's quick comparison, source checks) on an incremental build. Then run one
  clean build, which takes about 1.5 h.
- **Split-Challenge stubs.** When definitions live in companion modules, Lean's auto-generated helper names
  (`_proof_n`) differ between a monolithic Challenge and the Solution. A Challenge entry module made of Mathlib-only
  companions plus verbatim stubs passes.

**Merging several developments:**
- rename namespaces that clash;
- keep one copy of duplicated modules;
- if auxLemma cache resets are needed in the Challenge, comment them.

**Published history:**
- one orphan content commit plus one records commit;
- the local history, with unscrubbed sources, stays on the workstation;
- a clean package repository holds only the releases and their Challenges (the model is spherical-dynamics-lean).

## 9. Budgets and wrap-up

**Budget.** The author sets each session's floor in quota terms; record it verbatim. Costs depend on the account's
plan, so record a baseline with `quota-log` at the start. Superfluid measurements (Yale account, allowance = 100
points):

| Work | Time | Cost |
|---|---|---|
| Sol writer on an architect's leaf | about 10 min | 0.1–0.3 points |
| Writers in general | per agent-hour | about 0.75 points |
| Max-effort architects | per agent-hour | about 1 point |
| About 90 agents running at once | per hour | about 30 points |

**Wrap-up triggers:** the author's floor, a Codex reset (allowance up), exhaustion, or a context reset when the state is
unclear.

**Wrap-up steps:**
1. Launch nothing new. Let running agents finish, then integrate them.
2. Run the full validation, and compare the working tree with HEAD.
3. Push from the Mac:
   - `validated`, as a dated branch;
   - an orphan `campaign-state-<date>` branch with the briefs, reports, logs, tools, queue and integrator state;
   - `wip/*` branches for unvalidated work.
4. Write the `NEXT.md` handoff: state, frontier counts and resume steps.
5. Stop the instance. Confirm it with `describe-instances` before writing "stopped" anywhere. A Mac crash once left an
   instance running after the log already said it was stopped.
6. Take an EBS snapshot.
   - Delete the volume or older snapshots only when the author says so, and only after the new snapshot completes.
   - The snapshot may become the only copy; ask before deleting it.

**Restore.** Create a gp3 volume from the snapshot in the same availability zone, attach it as `/dev/sda1`, and start
the instance.
- Lazy loading makes first reads slow, so parallelize first reads and deletes.
- Raise IOPS before a writer wave.

**Compaction.** EBS ignores TRIM, so a compact snapshot needs a file-level copy onto a fresh, smaller volume, with the
same partition GUIDs and filesystem UUIDs.

**Mac disk.** The Mac disk is small. Bulky archives stay on the workstation, on GitHub (private) or in snapshots, and
only small handoff files come to the Mac.

## 10. What went wrong

| Failure | Cost | Remedy |
|---|---|---|
| Writers launched before the blueprint | A wasted wave | Blueprint first |
| No sandbox network approval | 3.5 h without Beam | Ask up front |
| 64 GB for 25 writers | Heavy swapping | 128 GB or more |
| Statements changed after writers started | Broke integrated proofs | Freeze; issue V2 nodes |
| No truth sweep | Many stuck writers (136 under-premised and 9 false leaves) | Sweep before each wave |
| `ContDiff ⊤` | 22 vacuous proofs | Lint for Lean traps |
| Integrator state edited while it ran | 39 retries silently skipped | Pause until idle |
| A running script redeployed | A fake validation failure | Deploy under a new name |
| `pkill -f` over SSH | Killed its own session | Bracket patterns; kill by tmux session or PID |
| A shared scratch tag in a brief | A failed 15-task batch; the integrator dropped to one task at a time | Scratch paths per project |
| A launch daemon triggered by a keyword | 21 duplicate writers, about 2 points | Parse explicit status lines; consolidation rounds |
| A queue daemon crash on one malformed task | 18 min with nothing launched | Per-step try/except; the digest watches the daemons |
| Resume without the original effort | Reports finished at medium | Resume now keeps effort |
| 27 redundant writers | Projected over budget; killed | No redundancy |
| Late discoveries during release | Reruns of 1.5 h builds | Cheap checks first |
| "Stopped" written before the instance was stopped | An instance left running after a crash | Stop, verify, then write |
| 50 Opus agents launched at once | Hit the Claude session limit in 5 min; all their work lost | Stagger; stop at 60% |
| Full validation on every batch | 13 min per cycle | Fast per batch; full at milestones |
| Leaf waves held back "for budget" while capacity idled | Lost wall-clock time | Launch distinct open work when capacity is free |

## 11. Rules of thumb

- **Keep one running log** (`RESUME.md`): the author's instructions verbatim, every milestone commit with its counts,
  and every failure with its fix.
- **Trust receipts, not summaries.** Read every report, and run an exact-type check on every claim.
- **Commit every validated milestone,** and push only validated work.
- **Prefer small, fully proved lemmas** over large partial ones.
- **Prefer more parallel agents to bigger CPUs,** within the memory budget.
- **Leave spare capacity idle** when nothing distinct is open. Never fill it with duplicate attempts.
