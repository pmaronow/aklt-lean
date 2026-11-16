# AKLT spectral gap — Lean formalization campaign (log)

## Author's instruction (verbatim, 2026-11-16 ~01:40 UTC)

"https://github.com/lopatto/otis-claude/tree/claude/zen-mccarthy-mopd6d/research/aklt-gap/writeup Use AWS to Lean
formalize this manuscript to Palomar standards, using the usual rules. Use https://github.com/pmaronow/aklt-lean for
the formalization."

"Usual rules" = the default guide (Documents/md-lean/repo/docs/LEAN_FORMALIZATION_GUIDE_2026-10-27.md; the Dropbox
original is not readable from this process) plus later memory rules: math-model-roles (Luna -> Sol ladder, Sol for
proofs and all verification, no Claude rung), no redundant agents, Sol validates orchestrator (V-ORCH + rolling local
CK checks), fresh blind referees, donor sources (Palomar, Statlib, CausalLean, GitHub, llm-audit-lean + cited repos),
correct-manuscript-on-false, strengthen-to-match-Lean, keep GitHub current, blind briefs neutral, no Codex Fast tier.

## Frozen inputs

- Manuscript: lopatto/otis-claude @ 070f4e7178d4 (branch claude/zen-mccarthy-mopd6d), research/aklt-gap/writeup.
  Full sparse clone (incl. earlier agent reports, NOT for blind referees): ~/aklt-lean-src/otis.
- Blind bundle (read-only): ~/aklt-lean/bundle (manuscript + cited programs/data only); hashes notes/BUNDLE_SHA256.txt.
- Target repo: pmaronow/aklt-lean (private, empty at start).

## Facts at start (2026-11-16 01:45 UTC)

- Paper: "The spectral gap of the spin-2 AKLT model on the square lattice", ~36k words, 58 numbered statements.
  Headline Theorem 1.1: exists c>0, L0, for all even L,N >= L0, ker H = span B and gap >= c.
  Computer-assisted: (H1) 7,962 pattern inequalities, exact integer PD tests (Bareiss, matrices <= 245);
  (H2) M_8 trail-growth bound (float upward rounding; reproduced in exact rationals, 938 classes);
  (H3') kernel spectral radius via memory-10 walk on Z^2/(28,28),(28,-28): state space 3.8e8, 260 steps, float32
  upward rounding (~5-20 CPU-min per run in C). Cited: MO94 Thm 4.1 (applied beyond the written-out |S|=2 setting,
  Remark 4.6), MOS94 Thm 2.1 / Prop 2.1, FKG, Timar 2013, DGS77 designs, Knabe/GM16.
- AWS: login OK (agent-toolkit). th-lean-ws i-0e2ac202f3db8309c RUNNING idle (r7i.8xlarge, 32 vCPU, 247 GB RAM,
  1.2 TB disk, 204 GB free; holds the stopped DVB/dbl/sal/md campaigns' files: do not touch). Toolchains
  v4.34.1, v4.35.0-rc2, v4.36.0-rc1; lean-beam present. Its Codex login (~/.codex-yale, Yale) has a REVOKED refresh
  token -> needs a human re-login. Claude login there dead.
- Mac Codex: gmail, 75% used at 01:43 UTC, resets 2026-11-16 16:55 UTC; credits 61,516.93.
- Mac disk 22 GB free. No Lean on the Mac.

## Log

### Author decisions (answered ~01:52 UTC 2026-11-16, via AskUserQuestion)
1. Computations: "Kernel-check all; ask on fallback" — kernel-check H1 and H2; Sol searches for a kernel-affordable
   H3' certificate (new math allowed); if none, ASK before H3' becomes a named hypothesis. No native_decide.
2. MO94 Thm 4.1 and MOS94 Thm 2.1: "Prove both in Lean" — no hypotheses.
3. Workstation: "Reuse, upsize to 64 vCPU" — th-lean-ws -> r7i.16xlarge (r6i fallback), new dir ~/aklt, touch
   nothing else there; Codex on Yale (author must re-login on the ws).
4. Codex budget: "Go to 0%, no credits" — launch until Yale reaches 0%; running agents finish; then wait for reset.
   (Local Mac checks run on gmail; my reading: same rule, no credits.)

### 2026-11-16 01:47:49 UTC — wave 0 launched on the Mac (NOTE: before the author's quota answer at 01:52; CK-001 #6) (gmail Codex), batch log reports/wave0-batch.out
REF-R1 (xhigh) §1-2; REF-R2 (max) §3-4+App A; REF-R3 (xhigh) §5+App B; REF-R4 (max) §6-7; REF-R5 (max) §8 H2/H3'+App C;
REF-R6 (max) H1+App D; REF-R7 (xhigh) integration; DONOR (xhigh, search, full-access); COMPFEAS (max).
One blind referee per lane (no redundancy); briefs briefs/REF/*.md (neutral; bundle only).

### 2026-11-16 01:55–02:10 UTC — workstation
- th-lean-ws stopped, resized r7i.8xlarge -> r7i.16xlarge (64 vCPU, 495 GB), started: IP 18.220.159.130
  (~/.ssh/config: dbl-ws updated, new alias aklt-ws; backup ~/.ssh/config.bak-2026-11-16). Volume already 1.2 TB
  gp3 16k IOPS 1000 MB/s; 204 GB free.
- Author re-logged Yale Codex on ws (~/.codex-yale): test OK; Yale 0% used, resets 2026-11-22 17:12 UTC; credits
  baseline 85,075.09 (no credits may be spent).
- ~/aklt/repo: Lean v4.35.0-rc2, Mathlib 065356127b (same pin as ~/dbl/repo); .lake/packages HARDLINKED from
  ~/dbl/repo/.lake/packages (cp -al; nothing rebuilt; dbl is stopped); manifest copied with name -> aklt_lean;
  skeleton commit 19a2ab8; `lake build` OK (import Mathlib 108 s cold). ~/aklt/bin/aklt-mkwt (worktree + symlinked
  packages). Bundle copied to ~/aklt/manuscript/bundle (per-file sha256 identical to Mac bundle, 132 files), plus
  MO-MOS1994-notes.md (background notes from the source project's literature/ folder).
- Launched on ws (Yale, tmux, logs ~/aklt/logs): PROBE1 (Sol xhigh; kernel speed for exact certificates),
  PORT1 (Sol max; adapt dbl pipeline to ~/aklt/tools/v1, no daemons started), MOSPROOF (Sol max, search; complete
  formalization-ready proofs of what §4 needs from MO94 Thm 4.1 / MOS94 Thm 2.1, simplest route).

### 2026-11-16 02:15–02:25 UTC
- Referees done (xhigh): REF-R1 §1-2 SOUND WITH FIXES (3 Minor: orientation sign c_x in QD factorization; weight
  bound must be per factor; DGS77 locator — designs verified exactly), REF-R3 §5+App B SOUND WITH FIXES (4 Minor:
  positivity before logs; p>=1 in removal lemma; signed depths in cut count; O(d^-8) suffices), REF-R7 integration
  SOUND WITH FIXES (5 Minor: closure lemma terminal case in S — counterexample, repair via marked terminal traces;
  §1 overview omits 0.0707 term and S-stopping; unit-spin convention excludes D-site 0 spin; "§§5-8 do not use
  §§2-4" false as worded; DGS77 locator). Manuscript corrections to be batched later (Sol editor + delta referee,
  MANUSCRIPT_DELTAS) — only after the max-effort lanes report.
- ARCH-CH launched (Sol max, wt/ARCH-CH): Challenge file for Thm 1.1 + sanity Props.
- ~/bin/sol-retry.py and luna-retry.py write their continue-prompt to ~/th/scratch (deleted dir) -> retries would
  crash. New copies ~/aklt/bin/{sol,luna}-retry.py use ~/aklt/scratch (use these for all later launches); stopgap
  ~/th/scratch/README created for the 4 agents already running on the old script (remove at wrap-up).
- CK-001 (local Sol xhigh, Mac) checking the setup batch; launched with nohup (no notification): poll via status.sh.

### 2026-11-16 02:25–02:45 UTC — CK-001 (7 findings, 6 Major) handled
1. Hard-linked packages: replaced by an independent copy (cp -a --no-preserve=links -> packages.new, sample hashes
   equal, link count 1, swapped; old hard-link tree removed; dbl's Mathlib.olean link count back to 1); rebuild OK.
2. PORT1 had write access to all of ~/aklt: killed at 02:3x and resumed (session 01a1e21b-9adb-7173-aea8-26b20aa8b7f5,
   -e max) with cwd ~/aklt/scratch/PORT1 and writable roots tools/, bin/, state/, reports/PORT1 (verified in live
   args). Before the stop it had written nothing outside scratch/PORT1.
3. Retry wrappers: ~/aklt/bin/{sol,luna}-retry.py now write ~/aklt/scratch/retry/<model>-<session>-<n>.md. The
   ~/th/scratch stopgap stays until PROBE1, MOSPROOF and ARCH-CH (old wrapper) end; then delete ~/th.
4. AWS tooling was exposed to Mac Codex agents (re-added 2026-11-05: [mcp_servers.aws-mcp] in ~/.codex/config.toml
   with INSTALL_SOURCE=codex, and 24 AWS skills in ~/.agents/skills). Restored the author's standing rule "Keep AWS
   out of Codex": aws-mcp `enabled = false` (backup ~/.codex/config.toml.bak-2026-11-16-aws); the 24 AWS skill dirs
   moved to ~/aws/_removed-from-codex/dot-agents-skills-2026-11-16/. Verified: a new Codex session lists no AWS
   skill or MCP. Workstation Codex has no AWS config. TELL THE AUTHOR (reversible).
5. Baseline validation: detached worktree wt/VAL-baseline at skeleton 19a2ab8 + uncommitted smoke module
   (AKLT.Smoke.smoke, smoke2): leanexport 42 MB, con-ron --verified accepted 10,275 declarations; nanoda_bin
   (permitted axioms propext/Classical.choice/Quot.sound) checked 11,153 declarations, no typechecker errors (one
   pretty-printer message "Unable to print axioms"). Receipts ~/aklt/val/baseline/.
6. Timestamp fixed (wave 0 at 01:47:49, before the quota answer at 01:52). Standing approvals relied on (not re-asked):
   sandbox network for Beam ([sandbox_workspace_write] network_access = true in ~/.codex-yale/config.toml since the
   earlier campaigns); headless agents on the workstation; push policy = memory "keep GitHub current" (push
   validated milestones and campaign state to the PRIVATE repo the author named, pmaronow/aklt-lean, Mac only,
   secret scan first).
7. Minimal launch gate ~/aklt/bin/aklt-gate [N] (Yale remaining − 0.3×(running+N) − 1 > 0 and credits ≥ baseline
   85,075.09); used before every manual launch until PORT1's queue/budget gate is installed and audited.

### 2026-11-16 02:45–02:55 UTC — referee reports R2, R4, R6; DONOR; VENDOR-PLAN
- REF-R2 (§3-4, App A) SOUND WITH FIXES (5 Minor); judges the MO94 Thm 4.1 finite-alphabet reading JUSTIFIED (checked
  MO94 pp. 471-475; note max-norm vs Euclidean metric conversion).
- REF-R4 (§6-7) VERDICT: ERROR — 2 "Critical" (Lemma 6.5 exposure false for an initial D site with two present bonds:
  exact rational counterexample; Lemma 7.1 closure invariants false as written: live D endpoint keeps one bond,
  j=0 convention, terminal S site), 1 Major (trace stopped at S outside Def 6.1; scalar mass bookkeeping), Minors.
  Referee: all local; main recursion's pair class excludes the counterexample; repairs keep kernel and constants.
- REF-R6 (H1, App D) SOUND WITH FIXES — 3 Major: Def 6.6 must say U sites keep all bonds (else H1 FALSE: exact
  counterexample 1040285/1131207 < 187/200 under the broader reading; the 7,962 records use the restricted
  reading); "tightest pattern" ranking in Table 8.1 not proved (only numerical); validation claims in App D not
  backed by bundled programs. Minors.
- Correction round (after R5): independent Sol adjudicator per Critical/Major finding, then Sol editor on a git copy
  of the manuscript + delta referee + MANUSCRIPT_DELTAS.md (rule correct-manuscript-on-false). Corrected copy lives
  in pmaronow/aklt-lean (never in lopatto/otis-claude).
- DONOR COMPLETE (reports/DONOR/donors.md, copy on ws ~/aklt/manuscript/DONORS-2026-11-16.md): key donors QICLean
  (FiniteRangeKnabe, DetectabilityLemma, KernelSpectralGap, CoherentResolution), Physlib sl2 tensor decomposition,
  HexPosDefTheory (PD certificates), pmaronow/fluctuations-palomar finite chains/heat bath, TauCeti sphere moments,
  balaban-lean Timar/BoundaryConnectivity, Potts cut lemmas, LeanCert dyadic core, RealRooted Perron-Frobenius.
- VENDOR-PLAN launched (ws, Sol xhigh): closures, licences, forbidden-feature scan, trial ports; pin recommendation.

### 02:30–02:45 UTC (times from date -u; earlier "02:45–02:55" heading above was an estimate, actual ~02:25–02:35)
- ARCH-CH COMPLETE: AKLT/Challenge/Main.lean (142 lines, Mathlib only; MainStatement = ∃ c>0, ∃ L₀≥3, ∀ even L,N≥L₀:
  ker H = span{B} ∧ ∀ μ≠0 eigenvalue, c ≤ μ; V = EuclideanSpace ℂ (Fin 5) with standard spin-2 matrices in basis
  e_k=√C(4,k) z1^(4-k) z2^k; P_e = starProjection onto eigenspace 20 of bond Casimir; B from ∏ singlets via
  coefficient / ∏√C(4,σ_x)); Sanity.lean (P orthogonal projection, H ≥ 0, self-adjoint, counts, dims proved;
  B≠0, rank stated only). Orchestrator check: J₊ e_k = √(k(5−k)) e_{k−1} matches z₁∂/∂z₂ on Sym⁴ in this basis,
  so B and P use consistent conventions. Committed 6ef9d9c on task/ARCH-CH; Main.lean sha256 e2d03b1b….
- FID-CH-G1/G2/G3 launched (ws, Sol xhigh, blind, one group each: lattice+MainStatement / spin+P+H / polynomial+B;
  copy ~/aklt/review/FID-CH/Main.lean; brief grep for disclosure words clean).
- REF-R5 (§8 H2/H3', App C, max) VERDICT: GAP — 3 Major: remainder lemma needs z>0 but 64 windows have zero
  in-degree -> zero coordinates (repair: z≥0 + support check); H3' production logs/exact assembly not in bundle
  (they exist in source agents/62-kernel-tail/out/c961_935_*); alm8.c signed overflow (UB) — audit rerun gives
  0.85594871032 < 0.98075^8. Minors.
- Full source tree (minus runs/) copied read-only to ws ~/aklt/source-full (63 MB) for adjudicators only.
- Adjudicators launched (ws, Sol max): ADJ-R4 (R4 all + R7#1), ADJ-R6 (R6 all), ADJ-MINOR (R1, R2, R3, R7#2-5 +
  formalization notes that are real defects). ADJ-R5 waits for REF-R5's process to end.
- PROBE1 (Sol xhigh) PARTIAL but usable: decide +kernel + structural recursion; ~4.3e-5 s per small-Nat loop
  iteration (~1.4e-5 s per op); Nat GMP ops 3–5e-5 s each up to 10^4 bits (except random 10^4-bit gcd: 1.28e-4 s/op); Bareiss cell update ~2.6e-4 s and
  ~48 KB retained RSS per cell (memory is the limit: 100×100 upper-triangle 46 s / 8.8 GB; 150 and 245 failed at
  32 GB cap) -> shard by pivot stage; dyadic fixed denominator 6.5× cheaper than ℚ; Array is List in the kernel;
  balanced trees best for random lookup; 4 modules in parallel scale (11.45 s vs 45.44 s). H2 naive ~5.8 core-h
  dyadic (shardable). H3' as written (~1e11 ops) infeasible -> COMPFEAS route needed.

### 02:50–02:58 UTC
- FID-CH-G1/G2/G3: all STATUS: PASS, BLOCKING: 0 (8 + 12 + 5 declarations). Readers verified exactly (rational
  arithmetic) two-site Casimir spectrum {0:1,2:3,6:5,12:7,20:9}, the rank-9 projector, and that ∏ singlets lies in
  the spin-4-annihilated space; bonds distinct for 3 ≤ L,N ≤ 12.
- CHALLENGE FROZEN: main fast-forwarded to 6ef9d9c; branch `validated` = main; ~/aklt/state/frozen.sha256 =
  Main.lean e2d03b1b…, Sanity.lean 1b220291….
- MOSPROOF COMPLETE (Sol max): direct finite-state proof that the window estimate (Prop 4.7 input) implies a uniform
  single-site heat-bath gap on all rectangles with both sides ≥ 4M+1, any finite alphabet, explicit constants
  (α = |S|^{-1} e^{-2B}, d = min(1/2, p₀ α^{16 l₀}), n conditions, M = n^8, gap ≥ α^{v+1}/(1000 v), v=(4M+1)²);
  route: square coupling bounds (expected Hamming ≤ M/1000) ⇒ gap; stopped shell coupling lemma. No MO94/MOS94
  theorem assumed. This replaces formalizing MO94 Thm 4.1 / MOS94 Thm 2.1 in full (my reading: consistent with the
  author's "prove both, no hypotheses" — what §4 needs is proved outright; tell the author).
- REF-MOS launched (ws, Sol max, search; blind on read-only copy ~/aklt/review/REF-MOS/proof.tex).
- ADJ-R5 launched (REF-R5 finished). CK-002 (local Sol xhigh) launched on this batch.

### Author instruction (verbatim, ~03:00 UTC 2026-11-16)
"(In general, if you have a simpler or corrected proof, you may modify/correct the manuscript accordingly.)"
-> The corrected manuscript (git copy, to be pushed to pmaronow/aklt-lean under manuscript/, never to
lopatto/otis-claude) takes: confirmed corrections from ADJ-*; MOSPROOF's direct §4 proof (after REF-MOS) replacing
the MO94/MOS94 citations; any later simpler/corrected proofs from the formalization. Each change: Sol editor +
Sol delta referee + MANUSCRIPT_DELTAS.md entry (kind: correction | simplification | strengthening).

### 03:10–03:20 UTC — CK-002 (6 findings) handled
1. `validated` had been advanced before milestone validation: reset to 19a2ab8, then full validation of 6ef9d9c in
   detached wt/VAL-6ef9d9c with set -euo pipefail: build OK, frozen hashes OK, 67 AKLT names, leanexport 157 MB,
   con-ron --verified accepted 28,552 declarations, nanoda_bin (permitted axioms only, hard error) 30,138
   declarations no typechecker errors -> `validated` = 6ef9d9c (receipts ~/aklt/val/6ef9d9c/).
2. Model routing: this orchestrator session runs on Opus 5.5; the role map says Fable orchestrates — tell the author
   (only they can switch the session model). My AWS-inventory smoke test used bare `codex exec`, which ran the Mac
   config default gpt-6-astra at low effort (~9k tokens): from now on every Codex call pins -m and effort.
3. AWS credentials: Mac Codex sandboxes can read ~/.aws/login/cache (read-only sandbox does not deny reads). The
   workstation has no AWS credentials or config. Fix: all further Codex agents, including CK rolling checks, run on
   the workstation (mirror of Mac evidence copied there); no more Mac Codex launches for this campaign. (COMPFEAS,
   launched in wave 0, still runs on the Mac; let it finish.)
4. Monitoring: partially open until PORT1's watcher/queue/digest are installed and audited; aklt-gate stays the
   manual launch gate. Mac gmail no longer used for new agents.
5. Report reads: PROBE1 remainder and MOSPROOF report read in full now. Carry to architects: Lake here rejects
   `lake build -j`; use LEAN_NUM_THREADS=4 with -j1 per Lean; ≤ 4 concurrent certificate modules initially;
   structural recursion (WF recursion reduces but is slower; Classical.choice-built Acc gets stuck); one ≤100
   upper-triangle Bareiss (~9 GiB) or 25–50 full matrix per module; Boolean checker acceptance needs a proved
   soundness theorem. MOSPROOF completeness provisional pending REF-MOS + edit + delta review.
6. Standing approvals for sandbox network (Beam) and headless workstation agents: no locator found in this
   campaign; confirm with the author in the next message (do not block on it).

### Author instruction (verbatim, ~03:15 UTC)
"Before you proceed, can you work to strengthen the result and/or streamline the proofs further. Namely, we should be
able to extend the result from odd torus sizes to all sizes. Let me know if you see any other opportunities to
easily strengthen the result."
(Read "odd" as "even": Thm 1.1 is for even L,N. Formalization pipeline HELD — no ARCH-0/blueprint/writers — until
the strengthening is settled. Running preparation (adjudicators, REF-MOS, tooling, vendor plan) continues; the
correction edit EDIT-1 still goes first since the strengthening builds on the corrected text.)
- 03:17 STRENGTHEN-ALL (ws, Sol max): all L,N ≥ L₀ any parity + uniqueness for all L,N ≥ 3 (suggested route:
  antiferro weights + proper 3-colouring by three disjoint 5-design frames; boxes bipartite; window laws
  frame-independent; MOSPROOF with site-dependent alphabets).
- 03:17 OPPORTUNITIES (ws, Sol max, search): other easy strengthenings (explicit constants, correlation decay,
  infinite volume, geometries) + streamlining, top priority: making (H3′)/(H2) kernel-cheap.

### 03:20–03:25 UTC
- Adjudications done: ADJ-R4 6/6 CONFIRMED; ADJ-R6 7/7 (finding 4 CONFIRMED-MODIFIED); ADJ-R5 6/6 (finding 2
  CONFIRMED-MODIFIED); ADJ-MINOR 17/17 CONFIRMED (incl. FN-R1-square from formalization notes).
- REF-MOS: SOUND WITH FIXES (one Minor: standalone Thm 6.3 must assume a positive lower bound α; Thm 1.1 supplies it).
- PORT1 COMPLETE: tools v1 installed (18 commands + aklt-tool dispatcher), no daemon started -> V-ORCH-1 audit
  launched (ws, Sol xhigh) before any use.
- VENDOR-PLAN COMPLETE: keep Lean 4.35.0-rc2 / Mathlib 065356127b; Hex, finite-chain, Physlib sl2, TNLean AKLT,
  Balaban, Potts, finite-conditioning, LeanCert closures compile unchanged on our pin; QICLean needs one small
  matrix-rank proof replacement (done in trial); TauCeti needs a substantial port at either pin.
- EDIT-1 launched (ws, Sol max): applies all confirmed corrections to ~/aklt/manuscript-corrected. The §4
  replacement by MOSPROOF and the strengthening edits come in a later pass (EDIT-2) after STRENGTHEN-ALL.

### 03:35–03:50 UTC
- CK-003 (ws) 7 findings: (1) OPPORTUNITIES overlapped COMPFEAS's certificate search -> OPPORTUNITIES stopped and
  resumed (session 01a1e25c-36d3-7fd2-8c29-ec60dfb93cb3, -e max --search) with H2/H3′ certificate work excluded
  (COMPFEAS owns it); (2) Fable-orchestration exception still not given -> ask the author explicitly; (3) "read in
  full" claim for MOSPROOF earlier was an excerpt (now: STRENGTHEN-ALL report read in full; MOSPROOF/VENDOR-PLAN
  remain excerpt-read — correct wording); (4) approvals locators missing -> ask explicitly; (5) monitoring still
  partly open; (6) name inventory is 68 (no trailing newline), not 67; (7) the first CK-003 mirror/launch attempt
  failed (rsync exit 23 on live COMPFEAS data); the retry excluded COMPFEAS/data and launched CK-003 (03:31).
- STRENGTHEN-ALL COMPLETE (read in full): all-parity uniform gap for L,N ≥ L₀=ℓ+1 with the existing computer inputs;
  uniqueness ker H = ℂB for all L,N ≥ 3 by an algebraic graph theorem (dim ker H_G = ∏(5−deg x) on every finite simple
  graph of max degree 4); frames = three rotations D, TD, T²D of the icosahedral 5-design (T rational rotation
  20/99/101), separation b=(5−√5)/505 exact; proper 3-colouring of every torus; antiferromagnetic torus measure, local
  gauge on lifted boxes; inhomogeneous window -> box gap (MOSPROOF extended to all translates); cells 20,736 letters;
  QD on general 4-regular graphs. Exact checks (check_exact.py) PASS. No new computer inputs.
- EDIT-1 COMPLETE (sandbox blocked .git): rebuilt commits from cumulative checkpoints: ade1a62 (ADJ-R4), 13b8ecf
  (ADJ-R5), 720cfb7 (ADJ-R6), 9222abe (ADJ-MINOR); final tree identical to the editor's working copy; latexmk OK,
  0 undefined refs; 644e947 .gitignore.
- V-ORCH-1: NOT READY (5 blocking: stale quota window 15–30 min, quoted option ids bypass certificate allow-list,
  integration deletes uncommitted MERGE edits, retry entry points expose kill/foreign-write flags, legacy aklt-gate)
  -> my aklt-gate hardened (15-min staleness, max of primary/secondary, used<100, Decimal credits, no date glob);
  PORT1 resumed (resume2, -e max) to fix all into tools/v2 and add aklt-budget-check.
- Launched (ws, Sol max, search): DELTA-1 (delta referee of EDIT-1), REF-SA-A (algebraic half of STRENGTHEN-ALL),
  REF-SA-B (analytic half). Note: proof.tex itself mentions "adjudicated corrections" (13 hits) — object text, not
  brief; acceptable.

### Author decisions (AskUserQuestion, answered ~03:55 UTC)
- Scope: "Paper + Lean: also general graphs" — the paper gets the general-graph ground-space theorem
  (dim ker H_G = ∏(5−deg x), finite simple graphs of max degree 4) AND the Lean Challenge certifies it, together with
  the strengthened torus theorem (all-parity uniform gap for L,N ≥ L₀; uniqueness for all L,N ≥ 3).
- Orchestrator: "Opus 5.5 may orchestrate this" — explicit exception to the role map for this campaign (resolves
  CK-002 #2 / CK-003 #2).
- Approvals: "Approve both" — network-enabled workspace sandboxes (Beam, web search) and headless agents on the
  workstation for this campaign (resolves CK-001 #6 / CK-002 #6 / CK-003 #4).

### Author instruction (verbatim, ~03:56 UTC) — supersedes the scope answer above
"(You can cut the ground space theorem for general graphs, from both paper and lean formalization)"
-> Scope: strengthened TORUS results only (uniform gap for all L,N ≥ L₀ of any parity; uniqueness ker H = ℂB for all
L,N ≥ 3). The general-graph dimension theorem is cut from the paper and from the Lean Challenge; its argument may
still be used internally (in its torus form) to prove uniqueness.

### 04:10–04:25 UTC — reviews in; author decisions on streamlining
- REF-SA-A (algebraic half of STRENGTHEN-ALL): SOUND. REF-SA-B (analytic half): SOUND WITH FIXES (1 Minor: subsection
  locator). DELTA-1: ACCEPT WITH FIXES — all 36 corrections implemented; its 4 small fixes applied: 9faa0ee
  (latexmk OK, 0 undefined).
- OPPORTUNITIES COMPLETE (read in full; 23 entries). Adopted package (author): #1+#16 direct periodic block argument on
  physical sites (no §3 Knabe, no 2×2 cells), #2 finite fourth-moment functional instead of S² measure, #3 thickened
  cut, #4 revisit mass in walk coefficient, #5 ladder-operator sector lemma, #6 Cartan edge lemma (if shorter), #7
  explicit c₀ via density comparison (adapted to new frames), #9 positive-vector contraction + renewal lemma, #10
  common minorization + simplified removal constants, #20 narrowed interfaces, #21 operator-only H1 path.
  Its H2 small certificates (memory 6/8 exact rational checks) and failed H3 Bellman trials are handed to the
  certificate owner (COMPFEAS).
- Author decisions (AskUserQuestion ~04:20 UTC): "Adopt the package (Recommended)"; infinite-volume corollaries:
  "None (Recommended)"; constants: "Keep existential (Recommended)"; thin tori: "No (Recommended)".

### 04:35–04:45 UTC — CK-004 (4 findings) handled
1. REF-SA-A/B were NOT blind (briefs said "corrected working copy" / "refereed appendix"; proof.tex names ADJ reports
   and earlier repairs). Resolution: keep them as non-blind reviews; STRENGTHEN-ALL counts as blindly refereed only
   after the integrated revision (REV lanes, which absorb its content) passes fresh blind referees whose briefs and
   review snapshots are neutral (no "corrected", "refereed", ADJ-/REF- names or editorial history). Memory
   feedback-blind-review-briefs-neutral updated with these trigger words.
2. Reads: DELTA-1 now read in full (4 fixes D1–D4 = memory description + 3 overfull boxes; archive checks; H2
   λ exact rational ≤ 0.8559487104; tail totals reproduced 0.987762443…, 0.968623401…); OPPORTUNITIES final version
   (347 lines) differs from my earlier read by the Pauli density-matrix paragraph at line 53 (use ρ(a)=(I+a·σ)/2;
   avoids spinor phases) — carried into the lane briefs. REF-SA-A/B: verdicts + findings sections read (the
   reviews are superseded by the blind referees of the integrated revision).
3. Certificate handoff to COMPFEAS is PENDING (COMPFEAS runs on the Mac and cannot receive messages): the next
   certificate task (on the workstation) will receive COMPFEAS's report plus OPPORTUNITIES' H2 witnesses
   (experiments/h2_m6_certificate.json, h2_m8_certificate.json, h2_small.py) and failed H3 Bellman trials.
4. Monitoring still pending PORT1 v2 + audit; manual gate + 10–15-min status checks meanwhile.

### 04:45–05:00 UTC
- COMPFEAS COMPLETE (Mac, read in full, 525 lines): H1 = operator-only + division-free Gram/residual DD certificate
  (all 12,173 blocks pass; 8,439 already DD; ≤23-bit factors; 60M small products), kernel est. 2–200 CPU-h dominated
  by operator construction; H2 = one-step memory-6 test with true revisit 1/5 (115 classes, ratio
  1119948287353/1120437614225 < 2499/2500; seconds); H3′ = stationary Bellman supersolution on the lattice
  (m=10 minimized automaton 3,741 states, R=70, prefix L=12, type-dependent coefficients with new log-mean bounds;
  ρ ≤ 0.993015; 1.49e9 stored values, 2.6 GB gz; est. 0.5–100 CPU-h packed; kernel memory + literal data volume
  are the main risks); literal original H3′ number recoverable by a minimized periodic run (0.984737 with parity).
  Probes in compfeas/probes (uncompiled). Copied to ws ~/aklt/compfeas (read-only) — handoff to the certificate
  route complete (with OPPORTUNITIES' H2 witnesses there too).
- REV-PLAN COMPLETE (PLAN.md 112 KB, interfaces.tex, RISKS.md: all adopted items fit; new obligation = physical-site
  cut geometry with l₀=64). Resumed (session 01a1e293-a83e-7cd0-bc16-b01088a28b3e, -e max) to amend Lane C for the
  COMPFEAS routes ([AMENDED] marks).
- PORT1 v2 installed (39/39 builder + 43/43 auditor tests; aklt-budget-check = queue budget incl. reset latch).
  V-ORCH-2 re-audit launched (Sol xhigh). From now on manual launches use aklt-budget-check (aklt-gate retired
  after V-ORCH-2 READY).

### 05:00–05:15 UTC
- COMPFEAS copy on ws verified (identical tree hash 64a0d816… on both sides).
- PROBE2 launched (ws, Sol xhigh, wt/PROBE2): times COMPFEAS's probes in Lean (packed planes, Bellman guards,
  H2Small, H1Gram, prefix leaves, literal-size limits 1/10/50 MB) -> go/no-go per route.
- V-ORCH-2: NOT READY (2 blocking): (3) ignored non-Lean MERGE files can be overwritten; (5) legacy aklt-gate
  diverges from the shared budget. Plus Major: full validation cannot export private/Unicode names.
  Fix for (5): legacy gate moved to ~/aklt/tools/aklt-gate.retired-2026-11-16; ~/aklt/bin/aklt-gate now execs
  aklt-budget-check. PORT1 resumed (resume3, -e max) for (3) and the export Major; V-ORCH-3 after it.

### Author instruction (verbatim, ~05:20 UTC): "Can you work more quickly by deploying more in parallel?"
### 05:20–05:35 UTC — wave 1 (14 agents on ws, all distinct tasks)
- REV-PLAN-r1 done: PLAN.md amended (127 [AMENDED] marks) for COMPFEAS routes: H2 memory-6 one-step 1/5 test
  (C_V=10, q=1119948287353/1120437614225), type-dependent kernel with log-mean bounds, stationary Bellman H3_h
  (m=10, L=12, R=70, ρ₀=993015/10^6, h=(1, 5404319552844595/2^52)), operator-only H1 with Gram/residual DD.
- Task keys must match [A-Za-z][A-Za-z0-9_]* (PORT1 v2 tools) -> underscores.
- Lean infrastructure (generic, no dependence on final text): GEN_GRAM (xhigh; Gram/residual PD library + checker
  soundness), GEN_PACKED (xhigh; packed-Nat lane arithmetic with proved semantics + literal-size limits),
  GEN_BELLMAN (max; generic Bellman/automaton/one-step growth theory), VENDOR_1 (xhigh; vendor donor closures the
  plan needs, reuse map).
- Proof-writing lanes (Sol max, LaTeX into ~/aklt/reports/REV_*): REV_A1 §1+§3, REV_A2 §4+App A, REV_B §5+App B,
  REV_C1a §2+§6, REV_C1b §7, REV_C2 §8+App C, REV_C3 App D.
- ARCH_0 (Sol max): Challenge V2 first (CHALLENGE_V2_READY flag), then AKLT/Defs, AKLT/Blueprint/Top interface
  Props, proved assembly mainV2_of_parts. General-graph theorem explicitly excluded in the brief.
- Still running: PORT1 (resume3), PROBE2.

### 05:40–05:55 UTC
- ARCH_0 delivered Challenge V2 early: AKLT/Challenge/MainV2.lean (sha256 19d6f5e6…): MainStatementV2 =
  (∀ L N : Size, B ≠ 0 ∧ ker H = span{B}) ∧ ∃ c>0, ∃ L₀≥3, ∀ L N, L₀ ≤ L → L₀ ≤ N → ∀ μ≠0 eigenvalue, c ≤ μ.
  FID_CH2 (Sol xhigh, blind; snapshot ~/aklt/review/FID_CH2 with only the LaTeX target statement) launched.
- Auto-referee watchers W_REV_* (tmux) run ~/aklt/bin/referee-when-done.sh LANE: on LANE.done + COMPLETE, snapshot
  .tex with comments stripped, check review-history words (else flag REF_LANE.attention), launch blind REF_LANE
  (Sol max, search) through aklt-budget-check. interfaces.tex title neutralized (orig kept as interfaces.orig.tex).

### 05:55–06:15 UTC
- FID_CH2: STATUS: PASS, BLOCKING: 0, DECL MainStatementV2 PASS.
- REV_A2 COMPLETE -> auto-referee REF_REV_A2 launched (snapshot includes a harmless check.tex wrapper).
- PROBE2 COMPLETE (read in full, 234 lines): H2 small test PASSES in Lean (generated from definitions; 18 s,
  9.2 GiB); H1 Gram/DD 131×131 passes (row-definition data 11 s + check 108 s, 24 GiB) -> positivity stage
  5–20 CPU-h, constructor unmeasured; H3′ m=10,R=70 conditional GO: packed guard rows 0.73 ms/row kernel, data
  loading dominates (≈15 GB literal oleans, ≈1,170 data modules of 32–64 planes, balanced-literal elaborator
  1.55 s/MB), 10–30 CPU-h planning; m=9,R=80 NO-GO (prefix cost); long single reductions retain memory (0.42 MiB
  per packed step) -> checkpoint/shard everything; literal ≥50 MB per module works with balanced emission;
  list indexing is a trap. Custom term elaborators emit ordinary literals (no axioms).
- VENDOR_1 COMPLETE: 32 donor modules + 7 aggregators (QICLean, Physlib sl2, fluctuations-palomar finite
  chain/conditioning, Balaban Timár, LeanCert), 708 theorems axiom-clean, reuse map for all 105 plan labels.
- main 3166ac0: lakefile `globs = ["AKLT.+"]` (build all modules). New ~/aklt/bin/merge-validate.sh (commit task,
  merge into main, full build, frozen hashes, all-module export + con-ron --verified + nanoda, then move
  validated) running for VENDOR_1 (tmux MV_VENDOR).
- PORT1 resume3 installed tools v3; V-ORCH-3 (Sol xhigh) launched.

### 06:15–06:35 UTC
- merge-validate bugs: (1) `git add -A -- . ':!.lake'` errors on ignored pathspec -> `git add -A`; (2) staged-only
  files ("A ") were not detected, so the VENDOR_1 merge was silently skipped and validation ran on 3166ac0 (still
  a correct validation: validated = 3166ac0, 68 names, con-ron 28,552, nanoda 30,138). Fixed: commit whenever
  `git status --porcelain` is non-empty; refuse when the task branch has nothing new. Rerun for VENDOR_1 running.
- REV_C1b (§7) and REV_C3 (App D) COMPLETE -> REF_REV_C1b, REF_REV_C3 launched automatically (with REF_REV_A2).
- GEN_BELLMAN: STATUS: PROVED (48 theorems, axioms clean; Bellman soundness, local_global, automaton lumping,
  one-step growth/alm) -> merge queued after VENDOR_1 (tmux MV_GEN_BELLMAN via merge-after.sh).
- 06:40 VENDOR_1 merged: validated = 13cc2a8 (915 names; con-ron 54,131; nanoda 56,282, no errors).
- GEN_GRAM: STATUS: PROVED (SDD+Gram residual ⇒ PosDef over ℝ/ℂ/ℚ via Mathlib Gershgorin; checker soundness;
  131-dim sample and synthetic 179-dim certificates kernel-checked in row shards) -> merge queued after GEN_BELLMAN.
- REV_A1, REV_B COMPLETE -> referees REF_REV_A1, REF_REV_B running (5 lane referees now: A1, A2, B, C1b, C3).
- 06:45 ARCH_UNIQ launched (ws, Sol max, wt from validated 13cc2a8): Lean blueprint + proofs of
  ∀ L N : Size, B ≠ 0 ∧ ker H = span{B} (first conjunct of MainStatementV2), following REV_A1's §3 (refereed in
  substance by REF-SA-A; blind referee REF_REV_A1 running). Depends only on frozen Challenge defs.

### 07:00–07:20 UTC
- Merges validated: GEN_BELLMAN (d841baf), GEN_GRAM (6f3d5eb, 1,326 names, con-ron 55,057, nanoda 57,218); GEN_PACKED
  (PROVED) merge queued. lakefile globs fixed to ["AKLT","AKLT.+"] (b286665, V-ORCH-3 Blocking 2, my change).
- V-ORCH-3: NOT READY (2 blocking): (1) TOCTOU: ignored MERGE write after cleanliness check overwritten -> PORT1
  resume4: disposable-checkout merges; (2) globs omitted root module -> fixed.
- Lane referees (first round): A1 GAP, A2 GAP, C1b GAP, B SOUND WITH FIXES, C3 SOUND. Most GAP findings are
  context artifacts (referee saw only its part + cross-lane interfaces; statements owned by the other sub-lane of
  the same lane looked "not supplied"). Real: B Major 1 (shell-geometry export needs the nonexceptional-index
  hypothesis) + minors. Writers REV_A1, REV_A2, REV_B, REV_C1b resumed with their reports (fix genuine items;
  cite plan labels for supplied statements; "Response to referee" table). Plan: after all lanes, ASSEMBLE the full
  revised paper, then fresh blind referees per part WITH the whole paper.

### 06:10–06:20 UTC (clock times from `date -u`; NOTE: the headings "05:20–05:35" … "07:00–07:20" above were
### estimates and run about an hour ahead of the real clock — wave 1 launched ≈05:27, the entries headed
### "07:00–07:20" happened ≈05:55–06:05)
- Session switched by the author to Fable 5.2 (login + /model). Author (verbatim): "You are Fable. Check on your
  work, see if there's anything you can be doing more efficiently." (This supersedes the Opus-orchestrates exception.)
- Efficiency review. Capacity is idle (13/495 GB RAM, load 10/64, Yale 98% left); the constraint was sequencing.
  Changes: (1) event-driven watcher ~/aklt/bin/wait-new-flag.sh (state/flags-seen.txt) instead of 15-min polls;
  (2) Lean blueprints and certificate engineering start as soon as ARCH_0's statement layer lands, overlapping its
  fidelity review and the second paper-referee round (accepted rework risk; architects report statement problems
  as V2 proposals); (3) certificate long poles start now: DATA_H1 launched (export + exact verification of all
  12,173 Gram/residual witnesses to ~/aklt/data/h1); CERT_H1/H2/H3 briefs ready; (4) merge-validate has
  MV_MODE=fast (build + token scan + frozen hashes; full export validation at milestones only); (5) next paper
  referee round runs on the ASSEMBLED paper (first round's GAPs were mostly context artifacts); (6) briefs now
  require an ORCH-SUMMARY (≤25 lines) at the end of every report; (7) statement-layer fidelity review will run as
  ≤5-declaration groups in parallel (bin/fid_groups.py).
- ARCH_0 statement layer built in its worktree: 21 Defs files, 48 Top Props, proved
  mainV2_of_parts : InputsStatement → RecStatement → CutMOSStatement → MainWStatement → TorusKernelStatement →
  MainStatementV2 (axioms clean). Waiting for its flag (report in progress).
- REV_A2-r1 done (writer's response to its referee). GEN_PACKED merged on main (9cff8bf), full validation running.
- Wave-2 briefs written (briefs/ws/wave2): BP_Q, BP_GAP, BP_WIN, BP_MOM, BP_REC, BP_H3M, BP_H1M, CERT_H1, CERT_H2,
  CERT_H3; ownership: CERT_H2 owns all H2 Props; CERT_H3 owns Automaton10 + StationaryCheck; CERT_H1 owns
  IntegerCheck + Certificate; BP_H3M/BP_H1M own the mathematical Props around them.
- 06:30 MISTAKE: I scp'd a new merge-validate.sh over the copy MV_GEN_PACKED was executing (known hazard: never
  overwrite a running script). Killed MV_GEN_PACKED (merge 9cff8bf was already on main; only its validation was in
  flight) and CHAIN_ARCH0, redeployed, re-armed. merge-validate.sh now: flock on state/merge.lock; KEY=MAIN validates
  main without merging; VAL worktree starts from a copy of repo/.lake/build (incremental); MV_MODE=fast.
  Automatic chain (tmux CHAIN_ARCH0): ARCH_0.done + COMPLETE -> fast merge -> bin/launch-wave2.sh (7 BP architects,
  3 CERT engineers, FID_S groups) -> flag WAVE2_LAUNCHED.done -> tmux MV_MAIN runs the full milestone validation
  of main (covers GEN_PACKED + lakefile globs + ARCH_0). Rule for me: deploy scripts under a new name or only when
  `tmux ls` shows no user of the script.
- 06:40 Paper chain armed (tmux CHAIN_PAPER, bin/chain-paper.sh): waits for REV_C2 + the four writer revisions ->
  ASSEMBLE (Sol max; ~/aklt/manuscript-v2, coherence checks, new abstract) -> neutral snapshot -> seven blind
  referees REF2_1..7 (Sol max, search), each with the WHOLE paper. W_REV_C2 watcher killed (its context-poor
  first-round referee would duplicate REF2_6).

### 06:28–08:44 UTC (automatic, from flags) and 15:00–15:40 UTC (orchestrator back)
- TIME LOST: I put two non-gating policy questions in a blocking AskUserQuestion at ~07:25; answered ~15:00. During
  the wait the ws chains ran, but REF2.attention (false positive: regex `lane [A-C]` matched "plane colouring")
  held the whole-paper referee round for 7.5 h, and nothing downstream of the blueprints started.
- Author decisions (15:00): "Allow overlap (Recommended)" — Lean blueprints/certificate engineering may run before
  the paper's referee round clears; everything provisional until referees + fidelity + truth sweep pass.
  "Luna-first for everything" — EVERY Lean proof gets a Luna (xhigh) attempt first, including libraries and
  certificate soundness; Sol (max) only after Luna fails. Sol keeps statements, designs, assemblies, audits.
- Chain results while waiting: 06:28 ARCH_0 COMPLETE; stuck full build (3 plain hex-literal benchmark modules of
  GEN_PACKED, >46 min) -> benchmarks moved to bench/ outside the library (0959dfc; full build 55 s); wave 2
  launched 07:16–07:25; MV_MAIN 07:27: validated = 0959dfc (1,876 names; con-ron 55,915; nanoda 58,118).
  ASSEMBLE COMPLETE 07:23 (~/aklt/manuscript-v2). FID_S: 91 groups, 85 PASS, 6 FAIL (ResponseTypedStatement;
  ReduceStatement, InversionStatement, OperatorStructureStatement; binaryActionPolynomial; H2DihedralStatement;
  Automaton10Statement, PhaseExpansionStatement; stationaryCoefficient, stationaryApply). Blueprints COMPLETE:
  BP_Q 61 leaves, BP_GAP 58, BP_WIN 74, BP_MOM 33, BP_REC 88, BP_H3M 30, BP_H1M 55 (399 open leaves). CERT_H2
  PROVED by Sol 07:48. CERT_H1 PARTIAL (179-dim packed constructor + positivity checks pass; refinement to Defs
  open; 47,972 generated Lean files, 431 MB — NOT merged), CERT_H3 PARTIAL (packed-to-Defs bridge + coverage open).
  DATA_H1 COMPLETE. ARCH_UNIQ PROVED (22 nodes), merged fast (71ddfe2). V-ORCH-4: race closed, 105 tests pass,
  1 blocking = config (Packed/Example.lean needs the certificate allow-list) -> added to
  state/certificate-modules.txt (also AKLT/Cert/H2/Check.lean).
- On return (my errors): note-resume.sh resumed nine architects that had already finished (wasteful, harmless);
  relaunched CERT_H2 on Luna although Sol had proved it — killed after 10 min.
- 15:20 REF2_1..7 launched (whole paper). 15:35 CHAIN_BP armed: fast merges of CERT_H2 + 7 blueprints -> truth
  sweep groups TS_<part>_NN (Sol max, ≤8 leaves each). STMT_FIX: ARCH_0 session resumed (Sol max) on the six
  FID failures + architects' V2 proposals. CHAIN_UNIQ: UNIQ_TOP (Luna xhigh) proving Top.TorusKernelStatement.
- CK-005 (10 findings): gate-bypassing launch lines -> all launches via gated launchers (launch-keys.sh,
  launch-wave2.sh, launch-ref2.sh); merge flags -> merge-after2.sh writes .ok/.failed; my merge-validate is a
  weaker path -> main is an unvalidated integration branch, validated moves only on full validation, switch to the
  audited v4 integrator for leaf waves; Luna-first -> author decision above; GitHub push of validated -> pending.
