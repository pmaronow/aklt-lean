Orchestrator message — change of target by the author, and the next phase for you.

AUTHOR'S DIRECTION (verbatim): "I'm not worried about the CPU/memory limit -- we are not actually submitting to
Palomar. This is designed to be a complete Lean formalization. I just want the challenge files, etc. to meet
Palomar standards." and: "Use American english throughout."

So the release is now the COMPLETE formalization: `Challenge.lean` states the paper's main theorem
UNCONDITIONALLY and `Solution.lean` proves it, using the certificate libraries. Resource limits of the external
verifier no longer constrain anything (still record measurements). The file-level standards stay: every `.lean`
file in the repository uses the module system and has at most 10,000 lines; Challenge imports Mathlib only and is
at most 1,000 lines / 100 KiB with the single conventional placeholder; `comparator.json`, `Audit.lean`,
`formalization.yaml`, README, verification scripts and records as in the model package; only the axioms propext,
Classical.choice, Quot.sound; no `native_decide`, `unsafe`, `implemented_by`, `extern`, new `opaque`.

What exists: your two-input release at `/home/ubuntu/aklt/wt/PAL_FIT/_pkg` (618 files ported). The complete
legacy tree is `/home/ubuntu/aklt/repo` at `main` (commit 8f59d33): it additionally has the certificate
checkers and soundness layers (`AKLT/Cert/H1/**`, `AKLT/Cert/H3/**`, hand-written `CertData/**`), the leaves that
derive the analytic inputs from the certificates (`AKLT/W/H1M*`, `H3M*`, `H1C*`, `H3C*`), `AKLT/Final/Conditional.lean`,
and the closing modules `CertData/H1/Close/*`, `CertData/H3/Close/*`, `CertData/Close/All.lean` with the
hypothesis-free `CertData.Close.main : AKLT.Challenge.MainStatementV2` (and `h1`, `h2`, `h3`). The generated
certificate modules (H1: 7,964; H3: 5,032) were compiled against the LEGACY sources and live outside git
(`/home/ubuntu/aklt/wt/CLOSE_H3`); they will be regenerated as module-system files and rebuilt by two other
agents AFTER your phase, against your ported hand-written kernels.

YOUR PHASE:
1. Extend the release root (same directory, new commits) to the complete hand-written tree: every hand-written
   Lean file in the import closure of `CertData.Close.All`, plus everything already there. Port all of it to the
   module system with the same rules as before (no change of meaning of any statement or definition; proof
   bodies changed only where visibility requires, each recorded in `PORT-CHANGES.md`; theorem names kept).
   Definitions that generated certificate modules evaluate in the kernel (checker functions, packed arithmetic,
   literals' consumers) must be exposed so that `decide +kernel`-style checks across module boundaries still
   reduce; say which declarations you exposed for that reason.
2. Lake layout for a complete formalization: library for the hand-written development; certificate libraries
   whose generated modules are NOT tracked in git (they are produced by generator scripts or fetched from release
   archives into the tree before building); targets `Challenge`, `Solution`, `Audit`. Everything hand-written that
   does not import a generated module must build now from a fresh `.lake/build`. For each hand-written module that
   imports generated modules (assemblies, closing modules, Solution), port it and state exactly which generated
   modules it needs.
3. INTERFACE NOTE for the regeneration agents: `REGEN-INTERFACE.md` listing, for H1 and for H3 separately, the
   hand-written modules that generated modules import (old and new module names if any changed), every
   declaration name the generated modules reference, the header each generated file must now have (`module`,
   `public import …`, visibility attributes needed on generated definitions and theorems so that downstream
   hand-written assemblies see them), and a tiny hand-made sample generated module for each family that compiles
   against your ported kernels and is consumed correctly by the next hand-written layer.
4. New `Challenge.lean`: the unconditional theorem (the present headline statement only — drop the two premise
   definitions; keep the file readable as mathematics, with correct references to the paper:
   the model, Hamiltonian and VBS product are `d:model` in `sec1-result.tex`; the polynomial normalization is
   `d:poly` in `sec3-quantum-frames.tex` — an independent review found the old comments cite labels `e:H`,
   `e:Vinner`, `e:B`, `s:poly` that do not exist; fix them). `Solution.lean`: proves it from
   `CertData.Close.main` through `main_iff`. Keep the two-input reduction as an ordinary library theorem
   (`AKLT.Final.main_of_inputs`); the predicate now named `ClosedTrail` describes a first-hit path — add a
   one-line doc comment saying so wherever it is defined (do not rename).
5. AMERICAN ENGLISH in all prose you ship: comments, doc strings, README, `formalization.yaml`, notes
   (neighbor, color, center, fiber, labeled, -ize; serial comma). Do not rename Lean identifiers for spelling;
   list any identifier containing a British spelling so the orchestrator can decide. Paper labels cited in
   comments keep their exact spelling (e.g. `l:colour`).
6. Verify what can be verified before the certificates are rebuilt: source/header checks with the official
   verifier's scripts over the whole tree; fresh build of all hand-written modules that need no generated module;
   strict Audit of what exists; the Comparator on the two-input theorem as a regression of your earlier result.
Report: append a section "complete release — hand-written port" to `/home/ubuntu/aklt/reports/PAL_FIT/report.md`
(first line `STATUS: FULL PORT COMPLETE | FULL PORT PARTIAL (reason)`), with file counts, the list of proof-body
changes, exposed declarations, what builds, the package commit hash, and an ORCH-SUMMARY (≤ 20 lines). You may
use up to 48 Lean processes and 300 GB RAM.
