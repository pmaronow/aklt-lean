# EDIT_4: verification-status wording and removal of pending markers

All edits were made in place in /home/ubuntu/aklt/manuscript-v2 on top of the earlier uncommitted edits, by the literal-replacement script /home/ubuntu/aklt/reports/EDIT_4/edit4.py. Each target was asserted to occur exactly once. Pre-edit copies of the four touched files, the pre-edit main.pdf, and the pre-edit working-tree diff are in /home/ubuntu/aklt/reports/EDIT_4/pre-edit/. Nothing was committed. No mathematics, constant, or numbered statement was changed. sec7-recursion.tex was not touched.

## Locations changed (old line numbers are from the pre-edit working tree, new ones from the edited file)

### main.tex
1. Line 23 (deleted). The macro definition, which nothing uses any more:
   OLD: `\newcommand{\certpending}[1]{\textbf{[certificate check pending]}}`
   NEW: (line removed)
2. Abstract, lines 52-54 → new 51-52:
   OLD: `prefix sums. The accompanying formalization uses the Lean kernel` / `to verify the finite certificate checks; pending checks are marked` / `explicitly.`
   NEW: `prefix sums. The theorem, including these finite checks, has been` / `formalized in Lean~4 and checked by the Lean kernel.`

### sec1-result.tex
3. Lines 10-12 → new 10-14:
   OLD: `inequalities and finite prefix sums. The accompanying formalization` / `uses the Lean kernel to verify the finite certificate checks; pending` / `checks are marked explicitly. The polynomial realization of the spin space,`
   NEW: `inequalities and finite prefix sums. Theorem~\ref{t:main}, including` / `the finite certificate checks for these inputs, has been formalized` / `in Lean~4 and checked by the Lean kernel. Section~\ref{s:inputs}` / `describes the accompanying Lean formalization. % CHECK: add repository reference` / `The polynomial realization of the spin space,`

### sec8-inputs.tex
4. Line 2 (label added so the introduction and the appendix can refer to the section; it renders as Section 8):
   OLD: `\section{Exact computational inputs}`
   NEW: `\section{Exact computational inputs}\label{s:inputs}`
5. Lines 12-15 → new 12-30. The marker legend was removed, and the one paragraph with all the quantitative facts was added here, where the inputs are introduced:
   OLD: `The accompanying formalization uses proofs checked by the Lean` / `kernel to verify these assertions. Each check whose kernel proof is` / `pending is marked \textbf{[certificate check pending]}. The soundness` / `arguments prove deterministic implications from these finite assertions.`
   NEW:
   ```
   The soundness arguments prove deterministic implications from these
   finite assertions.

   Theorem~\ref{t:main}, including the three inputs (H1), (H2), and
   (H3\(_h\)) and their certificates, has been formalized in Lean~4
   (version 4.35.0-rc2, with Mathlib) and checked by the Lean kernel.
   The accompanying Lean formalization % CHECK: add repository reference
   uses only the standard axioms \texttt{propext},
   \texttt{Classical.choice}, and \texttt{Quot.sound}, and it does not
   use \texttt{native\_decide}. The certificates are checked inside the
   Lean kernel, not by external programs. The certificate for (H1)
   covers all \(7962\) local patterns and their \(12173\) sector
   blocks; its kernel check took about \(139\) CPU-hours. The
   certificate for (H3\(_h\)) consists of \(5035\) generated modules;
   its kernel check took about \(19.5\) CPU-hours. The kernel check
   for (H2) took seconds. Everything in the formalization except the
   certificates for (H1) and (H3\(_h\)), in particular the derivation
   of Theorem~\ref{t:main} from the three inputs, has also been checked
   by two independent implementations of the Lean kernel.
   ```
   (The paper's own name for the third input, (H3\(_h\)), is used for (H3′). The counts are written \(7962\) and \(12173\), without commas, as elsewhere in the paper.)
6. Six marker lines deleted, each a line by itself: old 56 `\certpending{h1-pattern-enumeration}`, old 69 `\certpending{h1-pattern-coverage}`, old 101 `\certpending{h1-sector-reconstruction}`, old 108 `\certpending{h1-direct-dominance}`, old 129 `\certpending{h1-gram-residual}`, and old 156 `\certpending{h1-bareiss}`.
7. Proof of Theorem t:H1, lines 173-174 → new 182:
   OLD: `the local certificate, verified by the Lean kernel in the accompanying` / `formalization, with pending checks marked at their specifications.`
   NEW: `the local certificate, verified by the Lean kernel.`
8. "Certification scope", lines 344-347 → new 352-355:
   OLD: `specified finite assertions checked by the Lean kernel in the` / `accompanying formalization. The placeholders identify the pending` / `kernel checks. None of these arguments assumes a physical window` / `estimate, a frame finite-energy bound, or a spectral-gap conclusion.`
   NEW: `specified finite assertions, checked by the Lean kernel as described` / `at the beginning of this section. None of these arguments assumes` / `a physical window estimate, a frame finite-energy bound, or a` / `spectral-gap conclusion.`

### app-input-contracts.tex
9. Lines 16-18 → new 16-18:
   OLD: `of those checks. The accompanying formalization verifies these finite` / `assertions by proofs checked by the Lean kernel; pending checks are` / `marked at their full arithmetic specifications. An executable's exit`
   NEW: `of those checks. These finite assertions are verified by proofs` / `checked by the Lean kernel, as described at the beginning of` / `Section~\ref{s:inputs}. An executable's exit`
10. Lines 241-244 → new 241-242. The earlier pass had split this sentence only to attach two markers; it is restored to the committed wording, and this hunk no longer differs from HEAD:
   OLD: `without repetition, and their integer values are positive.` / `\certpending{h2-vector-indexing}` / `Every regenerated row satisfies the displayed integer inequality.` / `\certpending{h2-row-inequalities}`
   NEW: `without repetition; their integer values are positive; and every` / `regenerated row satisfies the displayed integer inequality.`
11. Six marker lines deleted, each a line by itself: old 260 `\certpending{h2-vector-extrema}`, old 271 `\certpending{h2-maximizing-row}`, old 408 `\certpending{h3-window-enumeration}`, old 415 `\certpending{h3-quotient-indexing}`, old 427 `\certpending{h3-quotient-transitions}`, and old 773 `\certpending{h3-transition-ceilings}`.
12. Lines 976-977 → new 968 (restores the committed line):
   OLD: `check with the displayed constants. \certpending{h3-prefix-denominator}` / `Multiplying phase weights by`
   NEW: `check with the displayed constants. Multiplying phase weights by`
13. Old line 1123 deleted: `\certpending{h3-array-indexing}`
14. Lines 1129-1134 → new 1119-1122. The split is undone, and the earlier pass's spelling "center" is kept:
   OLD: `bounds. \certpending{h3-free-rows}` / `For each of the \(4\cdot3741\cdot19881\) stored` / `phase/class/site indices, require \(0\le U\le Z\) and the specified` / `center and target equalities. \certpending{h3-caps-and-terminals}` / `Require the nonterminal stationary row inequality when appropriate.` / `The coefficients are regenerated`
   NEW: `bounds. For each of the \(4\cdot3741\cdot19881\) stored` / `phase/class/site indices, require \(0\le U\le Z\), the specified` / `center and target equalities, and the nonterminal stationary row` / `inequality when appropriate. The coefficients are regenerated`
15. Two marker lines deleted: old 1156 `\certpending{h3-local-rows}` and old 1172 `\certpending{h3-prefix-enumeration}`.
16. Lines 1185-1189 → new 1171-1173 (restores the committed wording):
   OLD: `rounding convention. \certpending{h3-prefix-values}` / `A compact lookup is accepted only with the` / `entry-by-entry identity with the full potential described after` / `Definition~\ref{d:prefix-bound}.` / `\certpending{h3-prefix-lookup}`
   NEW: `rounding convention. A compact lookup is accepted only with the` / `entry-by-entry identity with the full potential described after` / `Definition~\ref{d:prefix-bound}.`
17. Lines 1194-1195 → new 1178:
   OLD: `the Lean kernel in the accompanying formalization, with pending` / `checks marked above.`
   NEW: `the Lean kernel.`

In total, all 22 `\certpending{}` uses were removed, along with the macro definition and the marker legend. The quantitative facts (toolchain version, axioms, no native_decide, pattern, block and module counts, CPU-hours, and the scope of the independent-kernel recheck) appear only in sec8-inputs.tex, new lines 15-30. The introduction, the proof of t:H1, "Certification scope", and Appendix C refer to that paragraph. The abstract has one plain sentence. `% CHECK: add repository reference` is at sec1-result.tex:13 and sec8-inputs.tex:18, and a space precedes each `%`, so no words run together.

## grep after the edit

```
$ grep -rn "certpending\|pending\|provisional\|outstanding" /home/ubuntu/aklt/manuscript-v2/*.tex
/home/ubuntu/aklt/manuscript-v2/app-local-operator.tex:91:with no present internal bond gives a positive factor depending
/home/ubuntu/aklt/manuscript-v2/sec5-window.tex:699:\(p_0\in(0,1]\) and integer \(M_\star\ge1\) depending only on
/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:142:There is no residual factor depending on \(n\).
/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:196:depending only on its own slots, by Lemma~\ref{l:leaf}. It is
```
- app-local-operator.tex:91 matches only because "depending" contains "pending"; it is mathematical prose, not status wording.
- sec5-window.tex:699 is the same substring match ("depending only on").
- sec6-walks.tex:142 is the same substring match ("factor depending on n").
- sec8-inputs.tex:196 is the same substring match, in the proof of t:H1 ("depending only on its own slots").

## Compile

`cd /home/ubuntu/aklt/manuscript-v2 && latexmk -pdf -interaction=nonstopmode main.tex` exited 0 after two pdflatex passes. The full output is in /home/ubuntu/aklt/reports/EDIT_4/latexmk-output.log.
- main.pdf has 82 pages (83 before this pass).
- main.log has no undefined references, no undefined citations, no multiply defined labels, no LaTeX errors, and no overfull boxes. Its only warning is the one underfull \vbox (badness 10000) during \output, which was already there before this pass.
- The new label resolves: `\newlabel{s:inputs}{{8}{50}{}{}{}}`. The rendered text reads "Section 8" in the introduction and in Appendix C, and "Theorem 1.2" in Section 8.

## git diff --stat (against HEAD, including the earlier uncommitted edits)

```
 app-input-contracts.tex |  36 ++++++++++++++++++-------------
 main.pdf                | Bin 775760 -> 777558 bytes
 main.tex                |   3 ++-
 sec1-result.tex         |   7 ++++--
 sec7-recursion.tex      |  20 +++++++++++-------
 sec8-inputs.tex         |  55 +++++++++++++++++++++++++++++++-----------------
 6 files changed, 76 insertions(+), 45 deletions(-)
```
`git diff --check` passes.

## Points for the author (not changed)

- sec8-inputs.tex:163-165: "As an additional finite check, all \(3734\) blocks failing the direct dominance test, including the two with supplied nonzero factors, pass this fallback too." The committed text called this "additional native evidence". It is a redundant claim outside the certificate, which uses the Gram witness for those two blocks. The facts supplied for this edit do not say whether Lean checks it. It now sits next to the statement that the certificates are not checked by external programs. If Lean does not check it, it could be cut or reworded.
- Appendix C and Section 8 still describe the finite assertions as checks of named archived files (for example h2_exact_m6k1_r5.json and stationary_*_coarse.bin.gz). The new wording says these assertions are verified by proofs checked by the Lean kernel. This is accurate only if the Lean certificates encode those archived witnesses. If the formalization uses regenerated data instead, the file references may need a sentence.
