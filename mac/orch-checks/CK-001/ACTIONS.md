# CK-001 — setup batch (2026-11-16 01:40–02:15 UTC)

1. Froze the manuscript: sparse clone of lopatto/otis-claude branch claude/zen-mccarthy-mopd6d at 070f4e7 into
   ~/aklt-lean-src/otis (moved out of ~/aklt-lean so blind agents do not stumble on earlier agent reports).
   Claim: notes/FROZEN_COMMIT.txt = 070f4e7178d4ad996b71eb5fe286e7191725975c.
2. Built the blind bundle ~/aklt-lean/bundle (read-only): manuscript/*.tex + main.pdf; programs cited by the paper
   (agents/70-local-bounds code+out, 57-vector-channel code, 62-kernel-tail code, alm8.c, data pext7962.json and
   59-swm-certificate/out); compiled binaries removed; no REPORT/NOTES/LOG files. Claim: notes/BUNDLE_SHA256.txt
   lists 132 files; bundle/README.md maps original paths.
3. Wave 0 on the Mac (gmail Codex), batch reports/wave0-batch.out, file briefs/wave0.json: seven referees
   REF-R1..R7 (one per distinct lane; R1,R3,R7 xhigh, others max), DONOR (xhigh, search, full-access: needs gh for
   private repos and cloning), COMPFEAS (max). Claim: briefs are neutral (no earlier findings disclosed) and
   referees are told to read only the bundle.
4. Asked the author four up-front questions; answers logged verbatim-in-substance in RESUME.md.
5. Resized th-lean-ws (i-0e2ac202f3db8309c) to r7i.16xlarge after confirming it idle (no tmux, load 0); new IP
   18.220.159.130 in ~/.ssh/config (dbl-ws + new aklt-ws). Author approved ("Reuse, upsize to 64 vCPU").
6. ~/aklt on ws: repo skeleton (Lean v4.35.0-rc2, Mathlib 065356127b), packages hard-linked from ~/dbl/repo
   (cp -al) — risk: shared inodes with the stopped dbl campaign (see ws-mirror/repo-state.txt, link count 2).
   Bundle copied to ws (per-file sha256 identical).
7. ws agents (Yale): PROBE1 (Sol xhigh, worktree wt/PROBE1), PORT1 (Sol max, -C ~/aklt --write: can write all of
   ~/aklt), MOSPROOF (Sol max, search). Briefs in ws-mirror/briefs.
