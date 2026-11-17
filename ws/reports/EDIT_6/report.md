# EDIT_6: formal verification confined to one paragraph in Section 1

Repository /home/ubuntu/aklt/manuscript-v2, on top of HEAD d4d3848. Nothing committed.
Script: /home/ubuntu/aklt/reports/EDIT_6/edit6.py (literal replacements, each asserted to occur exactly once).
Pre-edit copies: /home/ubuntu/aklt/reports/EDIT_6/pre-edit/. Diff of this edit: /home/ubuntu/aklt/reports/EDIT_6/edit6.diff.
Method: sec8-inputs.tex was rebuilt from cd53b3c (every hunk there is kind (b) apart from one terminology repair). app-input-contracts.tex was kept at HEAD, and its two kind-(b) hunks were reverted.
Line numbers marked "now" refer to the edited files. In app-input-contracts.tex, "now" = HEAD - 3 after the first hunk.

## (i) Classification of the hunks of `git diff cd53b3c HEAD`

### sec8-inputs.tex: restored to cd53b3c (all kind (b))
1. HEAD l.2 `\section{Exact computational inputs}\label{s:inputs}` -> `\section{Exact computational inputs}`. After this edit nothing references s:inputs, so the label was removed.
2. HEAD l.9-13 "The finite tests specified below and in Appendix C use integer equalities, inequalities, and divisibility tests, ... The soundness arguments prove deterministic implications from these finite assertions." -> cd53b3c "All numerical checks below are finite integer inequalities, with positive rational denominators cleared." The following cd53b3c Lean sentence was removed (see (ii)).
3. HEAD l.15-34, the formalization paragraph (Lean 4.35.0-rc2, axioms, native_decide, 7962/12173, 139 and 19.5 CPU-hours, 5032+3 modules, four minutes, commit 63d176a, con-ron, NanoDa): deleted. cd53b3c had no counterpart.
4. HEAD l.36-44 "The local verification described below uses ... The Lean certificate uses the same patterns ... without running the numerical Bareiss fallback." -> cd53b3c "For the local input we use the archived representation and inversion choices, and the division-free Gram/residual format wherever its witness is available. ... Thus the complete local input is specified by the supplied data."
5. HEAD l.145 "These are the only two nonzero factors supplied in the original archive." -> "These are the only two nonzero factors used." (now l.118)
6. HEAD l.169 (sentence deleted at HEAD) -> restored "As additional native evidence, all \(3734\) blocks failing the direct dominance test, including the two with supplied nonzero factors, pass this fallback too." (now l.142-144)
7. HEAD l.185-188 (proof of t:H1) "The finite assertions specified above constitute the archived local verification. The accompanying Lean certificate proves ..." -> "The finite counts and inequalities specified above are the numerical local assertions; their verification uses only the archived pattern, choice and factor data." (now l.160-162)
8. HEAD l.337-343 (Certification scope) "The archived H1 calculation uses ... The Lean certificate uses Gram/residual witnesses for all blocks ..." -> "The H1 calculation uses the frozen representation and inversion records. ... using the fixed representation and inversion records."
9. HEAD l.357-362 (last paragraph) "...file hashes, and native exit codes ... Each Lean certificate proves its computational input ... finite-energy bound, or a spectral-gap conclusion." -> cd53b3c "...file hashes and native exit codes do not replace the prescribed comparisons. The native exact reruns provide reproducibility evidence. None of these arguments assumes a physical window estimate, a frame finite-energy bound or a spectral-gap conclusion." The cd53b3c Lean sentences were removed (see (ii)).

### sec8-inputs.tex: kind (a), kept
- l.7 "The closed-trail input" -> "The kernel input". This hunk mixes kinds: its other parts are item 2 above. The change was made in EDIT_3 and is the terminology repair of REF2_5 Minor 2: kernel trails run from u to v and are not closed, and "closed trail" terminology for them is to be replaced. It contains no verification wording.

### app-input-contracts.tex: restored to cd53b3c (kind (b))
1. HEAD l.16-22 "In Lean, the archived (H2) integer vector is expanded to all \(916\) raw windows ... The resulting proofs are checked by the Lean kernel, as described at the beginning of Section~\ref{s:inputs}. An executable's exit code ..." -> cd53b3c "The finite checks themselves are stated with their full arithmetic contracts, for separate verification; an executable's exit code or a floating approximation is not an additional hypothesis of any soundness lemma." (now l.16-19)
2. HEAD l.1179-1180 "constitute the stationary certificates. Their proofs are checked by the Lean kernel." -> cd53b3c "are the numerical assertions to be verified separately." (now l.1176)

### app-input-contracts.tex: kind (a), kept exactly as at HEAD (now line numbers)
- l.94 "whereas" -> "while".
- l.328-330 l:automaton-quotient: "provided that the raw terminal indicator and terminal reward are pullbacks of their quotient counterparts" (REF2_6 Minor 3).
- l.460-464 l:phase-expansion statement: "Let \(w\in\mathcal T_n^X\) with \(n>12\), and let \(\sigma_w\) be the ordering of Definition~\ref{d:kernel-order}: ..." (REF2_6 Minor 2).
- l.507-509 proof of l:phase-expansion: "Since \(n>12\), this is the ordering ...", and the sentence about other trails deleted (REF2_6 Minor 2).
- l.834-835 d:prefix-bound: "over trails in \(\mathcal T_n^X\)" (REF2_5 Minor 2).
- l.925 "whereas" -> "while".
- l.987 l:prefix-domination: "all kernel trails" (REF2_5 Minor 2).

### Kind-(a) hunks in the other files, untouched and kept as at HEAD
app-finite.tex l.206, sec5-window.tex l.75, 421, 509, and sec7-recursion.tex l.506: the five remaining "whereas" -> "while" (seven in all, with the two above). sec7-recursion.tex l.80-84 l:closure (REF2_5 Minor 1) and l.582-588 d:kernel-order (REF2_5 Minor 2). main.tex: only the abstract sentence differs from cd53b3c, and it is unchanged.

## (ii) cd53b3c Lean claims removed, and the hunk not classified

Removed from the restored cd53b3c text of sec8-inputs.tex, each by deleting only the claim:
1. First paragraph (cd53b3c l.11-12): deleted the sentence "Their separate Lean verification is not used as a mathematical assumption in the soundness arguments."
2. Last paragraph (cd53b3c l.333-336): "The native exact reruns provide reproducibility evidence; separate Lean verification must check the same finite assertions against their mathematical definitions. No completed Lean verification is claimed here. None of these ..." became "The native exact reruns provide reproducibility evidence. None of these ...". The clause after the semicolon and the sentence "No completed Lean verification is claimed here." were deleted.

Not classified, left as at HEAD:
- app-input-contracts.tex now l.1120 (HEAD l.1123): "centre and target equalities" -> "center and target equalities". This is a spelling change. EDIT_3 made it while splitting the sentence for a pending marker, and EDIT_4 rejoined the sentence but kept "center". It is neither a referee repair nor verification wording. The paper otherwise spells "centre" (about 20 times) and "neighbour". The kept kind-(a) hunk in sec7-recursion.tex l.80-84 also uses "neighbors" and "center". These are the only American spellings of the two words in the paper.

Points for the author (nothing changed):
- Restored cd53b3c wording that refers to verification but does not name Lean was kept, as the rule requires: app C l.17 "for separate verification", app C l.1176 "to be verified separately", sec8 l.142 "As additional native evidence, ...", and sec8 l.330-332 "native exit codes", "The native exact reruns provide reproducibility evidence".
- The restored sec8 l.9-10 says "All numerical checks below are finite integer inequalities". The checks also include equalities (for example the center and target equalities) and the Bareiss divisibility tests, which the HEAD wording listed.
- The restored last paragraph of sec8 has no serial commas ("file hashes and native exit codes", "finite-energy bound or a spectral-gap conclusion"), because the restore copies cd53b3c exactly. HEAD had added them.
- In sec1, cd53b3c's sentence "All computations are checked in exact arithmetic." was not restored at l.10. As instructed, the HEAD sentences there were replaced by the new paragraph, which sits in a later subsection.

## (iii) The new Section 1 paragraph

The paper does not use \paragraph. Its run-in headings are \emph{Title.} on a line of their own (sec5-window.tex l.441, 514, 531, 574, 641), and the new paragraph follows that convention. It is the last paragraph of Subsection 1.1 "Structure of the proof" (sec1-result.tex l.117-124). It follows the paragraph that ends with the gap implication, "the computational certificate arguments are proved in Appendices~B--D", and the sentence about scale choices, and it comes just before \subsection{Conventions}. The inputs are first named as (H1), (H2), and (H3\(_h\)) in the proof of Theorem~\ref{t:main} (l.49-57), which precedes this subsection. The main theorem's label is t:main, and the PDF shows "Theorem 1.2".

    \emph{Formal verification.}
    Theorem~\ref{t:main} has been formalized in Lean~4 and checked by the
    Lean kernel. The formalization has two parts. The first derives
    Theorem~\ref{t:main} from (H1) and (H3\(_h\)) and proves (H2); it is
    self-contained and is checked in minutes. The second checks the
    finite inputs (H1) and (H3\(_h\)) in the Lean kernel, which takes
    about \(139\) and \(19.5\) CPU-hours. Both parts are available with
    this paper. % CHECK: add repository reference

The old sentences at l.10-13 were removed. l.10 now ends "...inequalities and finite prefix sums." and l.11 continues "The polynomial realization of the spin space,".

main.tex: the abstract sentence (l.51-52) is unchanged. \certpending occurs in no .tex file at HEAD or now, and cd53b3c's main.tex does not contain it (checked with git show cd53b3c:main.tex | grep certpending, which finds nothing).

## (iv) grep -n -i "lean\|kernel\|formaliz\|con-ron\|nanoda\|CPU-hour\|archived local\|Lean certificate" *.tex

Formal verification (the two expected places only):
- main.tex:52 "formalized in Lean~4 and checked by the Lean kernel.": the abstract sentence (unchanged).
- sec1-result.tex:118, 119, 122, 123: the new paragraph.

Mathematical "kernel" (response kernel M, operator kernels, probability kernels, labels d:kernel, d:kernel-order, l:kernel-reflection, p:toruskernel):
- app-finite.tex:139 "composition of such kernels": coupling/probability kernels.
- app-input-contracts.tex:8, 9, 443, 461, 508, 522, 535, 883, 905, 1028, 1195: \ref{d:kernel}, \ref{d:kernel-order}, \label{l:kernel-reflection}, and \ref{l:kernel-reflection}.
- app-input-contracts.tex:834 "kernel sum over trails", 987 "kernel trails", 1032 "kernel contributions", 1067 (\ref{d:kernel}), 1189 "type-dependent kernel": response kernel.
- main.tex:48 "positive-vector bound for a response kernel": response kernel.
- sec1-result.tex:47 "kernel assertions" and 73 "The kernel of each edge projection": operator kernels (ker H, ker P_e). sec1-result.tex:47 also contains \ref{p:toruskernel}. sec1-result.tex:54 "type-dependent kernel": response kernel.
- sec3-quantum-frames.tex:4 "the edge kernel", 191 \label{p:toruskernel}, 218 "kernel equality", 685 \ref{p:toruskernel}: operator kernels.
- sec4-periodic-gap.tex:521, 538 \ref{p:toruskernel}, 532 "the kernel identity": operator kernel of H.
- sec7-recursion.tex:520, 575 (labels), 555 "type-dependent response kernel", 599, 600, 623, 708, 709, 737, 819, 841, 844, 848, 851, 857, 861, 868, 1015: the response kernel and kernel-live/kernel-dead sites.
- sec8-inputs.tex:7 "The kernel input": the (H3_h) kernel input. sec8-inputs.tex:278, 319, 320, 322: response kernel and \ref{d:kernel...}.

There are no hits for con-ron, NanoDa, "archived local", or "Lean certificate". A separate grep for s:inputs, certpending, whereas, and harmless over *.tex finds nothing.

## (v) Compile

latexmk -pdf -interaction=nonstopmode main.tex exited 0 after two pdflatex runs (log: /home/ubuntu/aklt/reports/EDIT_6/latexmk-output.log). main.log has no LaTeX errors (no "!" lines), no undefined references or citations, no multiply defined labels, and no overfull boxes. The one underfull \vbox in the output routine was there before. main.pdf has 82 pages: HEAD had 83, and cd53b3c had 82. git diff --check passes.

## (vi) Diff stats

git diff --stat cd53b3c
 app-finite.tex          |   2 +-
 app-input-contracts.tex |  28 ++++++++++++++++------------
 main.pdf                | Bin 775760 -> 776280 bytes
 main.tex                |   3 ++-
 sec1-result.tex         |  13 +++++++++++--
 sec5-window.tex         |   6 +++---
 sec7-recursion.tex      |  22 +++++++++++++---------
 sec8-inputs.tex         |   8 ++------
 8 files changed, 48 insertions(+), 34 deletions(-)

git diff --stat HEAD
 app-input-contracts.tex |  14 +++------
 main.pdf                | Bin 777882 -> 776280 bytes
 sec1-result.tex         |  14 ++++++---
 sec8-inputs.tex         |  82 ++++++++++++++++--------------------------------
 4 files changed, 42 insertions(+), 68 deletions(-)
