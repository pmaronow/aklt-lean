# EDIT_5: reviewer replacements from EDIT4_DELTA applied

All prescribed replacements and the one deletion in findings 1–5 were applied verbatim to `/home/ubuntu/aklt/manuscript-v2`, on top of the existing uncommitted edits. Nothing was committed.

- Script: `/home/ubuntu/aklt/reports/EDIT_5/edit5.py`. It matches each target literally, letting a whitespace run match any whitespace run. It asserts that every target occurs exactly once before writing anything, and asserts this again before each replacement.
- Matched old text, new text and line numbers: `/home/ubuntu/aklt/reports/EDIT_5/edits.json`.
- Pre-edit copies: `/home/ubuntu/aklt/reports/EDIT_5/pre-edit/`.
- Diff of this edit only: `/home/ubuntu/aklt/reports/EDIT_5/edit5.diff`.

All 11 targets were found exactly once, so no target is missing. Lines were not re-wrapped: the replacement text keeps the reviewer's line breaks, and some joined lines run long.

**Not applied, because the report marks them optional:**
- Answer A's alternative sentence, "An external exact-integer calculation also verifies…". It applies only if the redundant check is kept, and the minimal deletion of finding 2 was applied instead.
- Answer B's replacement at `app-input-contracts.tex:1093`, "The five witnesses are the arrays \(Z,U\) stored in the files". The report offers it "if an additional general transcription sentence is wanted" and says no further change is warranted.

Neither answer prescribes any other replacement that the statements need in order to be true.

## Finding 1 (sec8-inputs.tex, six locations)

**(a) Line 9.**

Old:
```tex
The certificates consist of the finite
integer equalities, inequalities, and divisibility tests specified
below and in Appendix C, with positive rational denominators cleared.
```
New:
```tex
The finite tests specified below and in Appendix C use integer
equalities, inequalities, and divisibility tests, with positive
rational denominators cleared.
```

**(b) Line 36 before the edit.** This is the paragraph between the formalization paragraph and `\subsection*{The finite local verification}`.

Old:
```tex
For the local input we use the archived representation and inversion
choices, and the division-free Gram/residual format wherever its
witness is available. For a block without a supplied nonzero Gram
factor which is not directly diagonally dominant, we use the
Bareiss fallback permitted by Lemma~\ref{l:integercheck}. The local
certificate consists of the coverage, reconstruction, and positivity
checks on these data specified below.
```
New:
```tex
The local verification described below uses the archived
representation and inversion choices, the two supplied nonzero
Gram factors, and the Bareiss fallback permitted by
Lemma~\ref{l:integercheck}. The Lean certificate uses the same
patterns, choices, and reconstructed matrices, with zero Gram
factors for the \(8439\) directly dominant blocks and nonzero
Gram factors for all \(3734\) remaining blocks. It therefore
proves the same local input without running the numerical
Bareiss fallback.
```

**(c) Now line 145.**

Old: `These are the only two nonzero factors used.`

New: `These are the only two nonzero factors supplied in the original archive.`

**(d) Now line 185, in the proof of Theorem t:H1.**

Old:
```tex
The finite assertions specified above constitute
the local certificate, verified by the Lean kernel.
```
New:
```tex
The finite assertions specified above constitute the archived local
verification. The accompanying Lean certificate proves the same
local input by the reconstructed-matrix Gram/residual checks
described at the beginning of this section.
```

**(e) Now line 337, under Certification scope.**

Old:
```tex
The H1 calculation uses
the frozen representation and inversion records. Its residual
tests require all rows, and its fallback requires every division
exact and every pivot positive. The fallback discharges exactly
the blocks without supplied nonzero Gram factors, using the fixed
representation and inversion records.
```
New:
```tex
The archived H1 calculation uses the frozen representation and
inversion records. Its residual tests require all rows, and its
fallback requires every division exact and every pivot positive.
The fallback discharges exactly the blocks without supplied
nonzero Gram factors, using the fixed representation and inversion
records. The Lean certificate uses Gram/residual witnesses for all
blocks and checks their mathematical reconstruction and coverage.
```

**(f) Now line 358.**

Old:
```tex
Each certificate is a proof of the
specified finite assertions, checked by the Lean kernel as described
at the beginning of this section.
```
New:
```tex
Each Lean certificate proves its computational input from the
finite integer assertions used in that certificate, with the (H1)
witness format described at the beginning of this section.
```

## Finding 2 (sec8-inputs.tex, line 169 before the edit; deletion)

The minimal correction was applied. Deleted, together with the space before it:
```tex
As an additional finite check,
all \(3734\) blocks failing the direct dominance test, including
the two with supplied nonzero factors, pass this fallback too.
```
The paragraph now ends "No stored pivot or floating eigenvalue replaces any requirement."

## Finding 3 (sec8-inputs.tex, line 22)

Old:
```tex
The certificate for (H1)
covers all \(7962\) local patterns and their \(12173\) sector
blocks; its kernel check took about \(139\) CPU-hours. The
certificate for (H3\(_h\)) consists of \(5035\) generated modules;
its kernel check took about \(19.5\) CPU-hours. The kernel check
for (H2) took seconds.
```
New:
```tex
The certificate for (H1) covers all \(7962\) local patterns and
their \(12173\) sector blocks; successful Lean builds of its
numerical certificate library used about \(139\) CPU-hours.
The production manifest for (H3\(_h\)) contains \(5032\) generated
modules and three hand-written bridge modules; successful Lean
builds of these modules used about \(19.5\) CPU-hours. The
exhaustive kernel computation for (H2) took about four minutes.
```

## Finding 4 (sec8-inputs.tex, line 28)

Old:
```tex
Everything in the formalization except the
certificates for (H1) and (H3\(_h\)), in particular the derivation
of Theorem~\ref{t:main} from the three inputs, has also been checked
by two independent implementations of the Lean kernel.
```
New:
```tex
At commit~\texttt{63d176a}, the part of the formalization independent
of the (H1) and (H3\(_h\)) certificate proofs, including the
conditional derivation of Theorem~\ref{t:main} and the (H2) proof,
was also checked by con-ron and NanoDa, two independent
implementations of the Lean kernel. These rechecks exclude the
(H1) and (H3\(_h\)) certificate proofs and the subsequent closing
and packaging modules.
```

## Finding 5 (two locations)

**(a) app-input-contracts.tex, line 16.**

Old:
```tex
These finite assertions are verified by proofs
checked by the Lean kernel, as described at the beginning of
Section~\ref{s:inputs}.
```
New:
```tex
In Lean, the archived (H2) integer vector is expanded to all
\(916\) raw windows and checked directly, and the archived
(H3\(_h\)) automaton and stationary arrays are checked through
their literal encodings. The resulting proofs are checked by the
Lean kernel, as described at the beginning of Section~\ref{s:inputs}.
```

**(b) sec8-inputs.tex, line 21.**

Old:
```tex
The certificates are checked inside the
Lean kernel, not by external programs.
```
New:
```tex
The certificate proofs are checked by the Lean kernel; external
programs generate and encode witness data.
```

## Collision check (step 4)

I searched `sec8-inputs.tex`, `app-input-contracts.tex`, `sec1-result.tex` and `main.tex` for: 5035, 5032, seconds, minutes, two nonzero, nonzero (Gram) factor, 3734, 3732, 8439, independent, everything, external, kernel check, CPU-hour, local certificate, Bareiss, fallback, verified by, Lean kernel, consist of, con-ron and NanoDa. Some of these searches also ran over all `.tex` files.

**Removed phrases with no remaining occurrence:**
- **"5035":** no occurrence remains. The only match is the digit string inside 4503599627370496, at `app-input-contracts.tex:1190,1220` and `sec7-recursion.tex:578`, which is not a module count.
- **"seconds" for (H2):** none remain.
- **"kernel check", "local certificate", "only two nonzero factors used", "Everything in the formalization", "certificates consist":** none remain.
- **"two independent implementations", "CPU-hours":** these occur only in the new text, at lines 24, 27 and 31.

**Remaining occurrences and whether each is still true:**
- **sec8:17** "…has been formalized in Lean~4 … and checked by the Lean kernel." Still true; the report's table says so.
- **sec8:51** "The two supplied nonzero factors are h1_chol_5420_131.json and h1_chol_7697_131.json." Still true. These are the two factors supplied in the archive, and this subsection now explicitly describes the archived verification.
- **sec8:121–128** "8439 satisfy the direct integer inequalities … Gram/residual certificate with L=0 … The two archived nonzero factors match…". Still true. It agrees with the new statement that Lean uses zero Gram factors for the 8439 directly dominant blocks.
- **sec8:147** "For each of the remaining \(3732\) blocks use the following exact fallback." Still true for the archived route (8439 + 2 + 3732 = 12173). It does not contradict the new line 42 (Lean uses nonzero Gram factors for all 3734), because the new paragraph separates the two routes.
- **sec8:239–243** (proof of t:H1) "For either supplied nonzero factor…". Still true inside the archived argument.
- **sec8:294–297** (Theorem t:inputs) "(H1) holds by the operator-only certificates of Appendix D, using the supplied Gram/residual checks and its Bareiss fallback." True as a statement of the archived route: the report's answer A records that the fallback passes on all blocks. However, the word "certificates" here means the archived Bareiss route, not the Lean certificate, which runs no fallback. The report does not list this line and prescribes no change, so it was left alone. The author may want to look at it.
- **sec8:313–316** (proof of t:inputs) "The direct Gram checks, the two supplied nonzero factors and the fallback cover every supported sector as established above." Still true for the archived route; the same remark as for sec8:294–297 applies.
- **app-input-contracts:1176–1180** "…constitute the stationary certificates. Their proofs are checked by the Lean kernel." Still true; the report's table says no replacement is needed.
- **sec1-result.tex:10–13** "Theorem~\ref{t:main}, including the finite certificate checks for these inputs, has been formalized in Lean~4 and checked by the Lean kernel." Still true per the report's table. The file is unchanged by this edit.
- **main.tex:51–52** (abstract) "The theorem, including these finite checks, has been formalized in Lean~4 and checked by the Lean kernel." Still true per the report's table. The file is unchanged by this edit.

**Style words:** none of the inserted text contains "whereas" or "harmless" (checked by script over all 11 new strings). Two older occurrences of "whereas" are in `app-input-contracts.tex`, at line 97 ("its weight is \(1/5\), whereas the window") and line 928 ("five, whereas only three avoid \(c\)"). This edit did not insert them and they were left untouched. They are on the author's banned-word list, if that is wanted later.

## Compile (step 5)

`latexmk -pdf -interaction=nonstopmode main.tex` exited 0 after two pdflatex passes; the log is `/home/ubuntu/aklt/reports/EDIT_5/latexmk-output.log`.
- The final `main.log` has no LaTeX errors, no undefined references or citations, no multiply defined labels and no overfull boxes.
- One underfull `\vbox` remains in the output routine; it was also present before this edit.
- `main.pdf` has 83 pages, up from 82 before this edit.

## git -C /home/ubuntu/aklt/manuscript-v2 diff --stat

The stat is against HEAD `cd53b3ce30fb8ad15889224a1d2ea309e3fbbd6e` and includes the earlier uncommitted edits.
```
 app-input-contracts.tex |  38 ++++++++++++---------
 main.pdf                | Bin 775760 -> 777858 bytes
 main.tex                |   3 +-
 sec1-result.tex         |   7 ++--
 sec7-recursion.tex      |  20 ++++++-----
 sec8-inputs.tex         |  88 ++++++++++++++++++++++++++++++------------------
 6 files changed, 98 insertions(+), 58 deletions(-)
```
This edit changed only `sec8-inputs.tex` and `app-input-contracts.tex`, plus the rebuilt `main.pdf` and auxiliary files. `main.tex` and `sec1-result.tex` are byte-identical to the copies in `pre-edit/`. The script never writes `sec7-recursion.tex`, and its last modification predates this edit.
