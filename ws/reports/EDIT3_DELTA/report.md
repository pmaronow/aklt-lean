VERDICT: FIXES NEEDED

1. **Unsupported claims of completed Lean verification.** Locations: [main.tex:50](/home/ubuntu/aklt/manuscript-v2/main.tex:50), [sec1-result.tex:10](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:10), [sec8-inputs.tex:12](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:12), [sec8-inputs.tex:172](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:172), [sec8-inputs.tex:343](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:343), [app-input-contracts.tex:16](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:16), and [app-input-contracts.tex:1193](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1193).

   The new text repeatedly says that the finite assertions are verified, or that their proofs are checked, by the Lean kernel in an accompanying formalization. The supplied repository contains no Lean project or certificate archive, and identifies no accessible formalization or archive. The edits supply none. In particular, the local reconstruction/positivity checks and the five stationary arrays and their evaluations remain unverified in the supplied material, exactly as REF2_6 reported. The nearby qualification about pending checks does not justify the affirmative claims of verification. The new legend also substitutes “kernel proof pending” for the requested status, “finite certificate verification pending”; these are different conditions.

   Proposed exact replacements:

   * Replace `main.tex:50–54` with:

     ```latex
     inputs reduce to exact matrix positivity tests, a
     finite-memory test, and stationary Bellman inequalities with finite
     prefix sums. The outstanding finite certificate checks are marked
     explicitly; no completed Lean verification is claimed.
     ```

   * Replace `sec1-result.tex:10–12` with:

     ```latex
     inequalities and finite prefix sums. The outstanding finite
     certificate checks are marked explicitly; no completed Lean
     verification is claimed. The polynomial realization of the spin space,
     ```

   * Replace `sec8-inputs.tex:12–15` with the following status convention. This convention and the statement markers in finding 2 must be applied together:

     ```latex
     The markers identify finite assertions whose exact verification
     remains outstanding. Statements bearing
     \textbf{[certificate check pending]} are provisional; the soundness
     arguments prove deterministic implications from these assertions.
     No completed Lean verification is claimed.
     ```

   * Replace `sec8-inputs.tex:172–174` with:

     ```latex
     arithmetic tests. The finite assertions specified above constitute
     the local certificate obligations. The checks marked at their
     specifications remain pending; the argument below proves the
     implication from their validity.
     ```

   * Replace `sec8-inputs.tex:343–346` with:

     ```latex
     the prescribed comparisons. The placeholders identify the finite
     assertions whose exact verification remains pending. No completed
     Lean verification is claimed. None of these arguments assumes a physical window
     ```

   * Replace `app-input-contracts.tex:16–18` with:

     ```latex
     of those checks. Exact verification of the marked finite assertions
     remains pending; no completed Lean verification is claimed.
     An executable's exit
     ```

   * Replace `app-input-contracts.tex:1193–1195` with:

     ```latex
     constitute the stationary certificate obligations. Exact verification
     of the checks marked above remains pending; no completed Lean
     verification is claimed.
     ```

2. **The principal claims depending on the missing certificates are unmarked, and several uses still describe them as proved.** Locations: [sec8-inputs.tex:158](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:158) (`t:H1`), [sec8-inputs.tex:280](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:280) (`t:inputs`), [app-input-contracts.tex:376](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:376) (`p:automaton10`, its particular supplied map), [app-input-contracts.tex:1083](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1083) (`p:stationary-check`), [sec1-result.tex:42](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:42) (the gap part of `t:main`), [main.tex:43](/home/ubuntu/aklt/manuscript-v2/main.tex:43), [sec1-result.tex:4](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:4), [sec7-recursion.tex:610](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:610), and [sec4-periodic-gap.tex:531](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:531).

   The 22 invocations are all attached to lower-level checks. None marks the actual local theorem, the stationary existence and prefix-bound proposition, the H1/H3 input assembly, or the resulting uniform-gap assertion. Their dependence is essential: generic certificate soundness does not supply passing witnesses. Independently reconstructing some quotient with the right counts also does not check the particular archived class map used to interpret the arrays. Conversely, the ground-state uniqueness assertion is independent of these checks and should remain unmarked.

   Proposed exact marker insertions, using the provisional-status convention in finding 1:

   | Insertion point in the current source | Exact inserted text |
   | --- | --- |
   | `sec8-inputs.tex`, immediately before `\end{theorem}` at line 168 | `\certpending{h1-inequalities}` |
   | `sec8-inputs.tex`, after “its Bareiss fallback.” at line 283 | `\certpending{h1-input}` |
   | `sec8-inputs.tex`, after “automaton quotient.” at line 295 | `\certpending{h3-input}` |
   | `app-input-contracts.tex`, after the supplied map's edge-count sentence at line 380 | `\certpending{h3-archived-quotient}` |
   | `app-input-contracts.tex`, immediately before `\end{proposition}` at line 1099 | `\certpending{stationary-supersolutions-and-prefix-bounds}` |
   | `sec1-result.tex`, after the spectral-gap sentence at line 44, before `\end{theorem}` | `\certpending{uniform-quantum-gap}` |

   Put a paragraph break after the already verified raw-window count at `app-input-contracts.tex:375`, so the quotient marker belongs to the following claims about the particular supplied map, rather than to that count.

   Make the following small qualifications at the other uses; these do not change any constant or uniqueness claim:

   * In the abstract, replace `main.tex:44–47` with:

     ```latex
     has a unique ground state for every pair of integers $L,N\ge3$ and,
     subject to the finite certificate checks marked pending below, a
     spectral gap bounded below by one positive constant for all integers
     $L,N\ge L_0$, for some fixed $L_0$, with either parity allowed for
     each period. \certpending{abstract-gap}
     The proof is computer-assisted. Its computational inputs
     ```

   * Replace `sec1-result.tex:5–7` with:

     ```latex
     state on every torus with integer periods \(L,N\ge3\) and,
     subject to the finite certificate checks marked pending below, a
     uniform positive spectral gap for all integers \(L,N\ge L_0\),
     with no parity restriction, for one fixed threshold \(L_0\).
     \certpending{introduction-gap} The computational inputs
     ```

   * Replace `sec7-recursion.tex:610–611` with:

     ```latex
     Passing the stationary lattice Bellman certificate checks implies
     this assertion, with no periodic spatial walk or remainder.
     ```

   * In the first proof of the main theorem, replace the text beginning “For the uniform gap,” at `sec1-result.tex:49–50` with:

     ```latex
     assertions for every \(L,N\ge3\). For the uniform gap, assume the
     finite certificate assertions marked pending in Section~8 and
     Appendix~C. Theorem~\ref{t:inputs} then supplies (H1), (H2) with
     ```

   * Replace the repeated introductory sentence at `sec4-periodic-gap.tex:531–535` with:

     ```latex
     We now prove the two conclusions of Theorem~\ref{t:main}, with
     the uniform-gap conclusion subject to the finite certificate
     assertions marked pending in Section~8 and Appendix~C.
     ```

     Replace the start of its uniform-gap argument at line 540 with:

     ```latex
     For the uniform positive gap, assume the finite certificate
     assertions marked pending in Section~8 and Appendix~C.
     Theorem~\ref{t:inputs} then gives (H1),
     ```

   These corrections retain the intended mathematical claims as visibly provisional where requested. They do not discharge the unresolved H1/H3 proofs. The conditional soundness lemmas, including `l:stationary-local-global`, `l:prefix-domination`, and the assembly with certified potentials, do not require pending markers merely because their hypotheses may later be instantiated with unverified data.

3. **Five markers report already verified finite arithmetic as pending.** Locations and exact corrections:

   | File:line | Exact text to delete |
   | --- | --- |
   | [sec8-inputs.tex:56](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:56) | `\certpending{h1-pattern-enumeration}` |
   | [app-input-contracts.tex:408](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:408) | `\certpending{h3-window-enumeration}` |
   | [app-input-contracts.tex:773](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:773) | `\certpending{h3-transition-ceilings}` |
   | [app-input-contracts.tex:976](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:976) | `\certpending{h3-prefix-denominator}` |
   | [app-input-contracts.tex:1172](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1172) | `\certpending{h3-prefix-enumeration}` |

   Leave the adjacent mathematical text unchanged. REF2_6 explicitly verified these counts, the four diagonal ceiling numerators, and the phase denominator; REF2_7 independently verified the local enumeration. I reproduced those checks, regenerated the memory-window and five prefix counts, and checked the ceiling formula on all possible response coefficients. No absent local operator choices or stationary arrays are needed for these assertions. The general ceiling formula is itself proved by the displayed integer inequalities. An unfinished Lean proof does not make an already performed exact certificate/arithmetic verification unperformed.

   This does **not** justify deleting the archive-specific tags. In particular, the four `h2-*` sites concern the contents of the named archived file, which has not been supplied. REF2_6's separate witness, whose 916 exact row checks I reran successfully, proves the mathematical H2 existence assertion and its constants; it does not establish byte-for-byte or record-for-record agreement with the missing archived file. Likewise, keep the local coverage/reconstruction/positivity tags, the particular quotient-map tags, and the full stationary-array and array-dependent prefix-value tags. The current markers conflate these distinct kinds of outstanding work through the Lean-only legend in finding 1.

4. **A generic optional lookup acceptance rule is marked as an unverified assertion.** Location: [app-input-contracts.tex:1186](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1186).

   “A compact lookup is accepted only with the entry-by-entry identity” states a condition for accepting an optional representation. It does not assert that any particular lookup passes, or even that one is used. The identity's sufficiency is already explained at lines 984–993. Evaluating the full arrays directly requires no compact-lookup certificate. Thus this marker labels a sound conditional rule as pending. If a particular compact table is actually used, its identity assertion must instead name that table and carry the marker there.

   Proposed exact replacement for lines 1186–1189:

   ```latex
   A compact lookup is accepted only with the
   entry-by-entry identity with the full potential described after
   Definition~\ref{d:prefix-bound}.
   ```

Minor-item coverage and mathematical checks

- **REF2_6 Minor 2: fully repaired.** The phase-expansion statement now requires `w` in the actual kernel trail class, `n>12`, and increasing path order within each type. Its proof uses that same order. Its only application to a full kernel contribution, at `app-input-contracts.tex:1015`, has total length greater than twelve. Short hits still use the rational-key ordering at lines 912–921. The length-twelve phase vectors in the prefix definition are prefixes of longer trails, not substitutes for short-hit kernel values. I reproduced the length-ten counterexample and its exact positive discrepancy, and checked phase multiplication against the prescribed long order on 100 completed trails, 87 containing revisits. The general product proof supplies the all-trail identity.
- **REF2_6 Minor 3: fully repaired.** The stopped quotient statement now explicitly requires pullback terminal indicators and rewards. The actual terminal set depends on position (`c,v`), and the reward depends on position and phase, so all its stationary uses satisfy the added hypothesis. The EN/WN zero-step counterexample is excluded.
- **REF2_7: no Minor items.** Its numbered entries are successful checks. No repair from that report is outstanding.
- The additional closure and ordering edits attributed by EDIT_3 to REF2_5 also pass: at a U departure, removal of the live site leaves each non-arrival D endpoint with at most one present bond; response pairs used at `sec7-recursion.tex:792–806` are exactly among those neighbors in that pre-step removal domain. The ordering definition now covers both canonical kernel trail classes, including distinct-endpoint short trails. Its zero-reward and tie rules are unchanged.
- I searched all thirteen TeX sources for the changed labels, orderings, trail terminology, certificate/status claims, and uses of the thresholds, coefficients, vector and contraction constant. The repaired mathematical statements fit all their uses. The diff changes no numerical constant. The remaining problems are certificate status and marker coverage, not a newly detected counterexample to the local inequalities or gap conclusion.

Verification and limits

- The local enumeration rerun returned 106101 consistent assignments, 184914 marked assignments, 123339 with mark N/E, and 7962 effective keys. This does not check equality with the absent pattern/choice files or positivity of their reconstructed matrices.
- Independent window recursion returned `4,12,36,108,316,916,2628,7500,21268,60092`. Independent prefix recursion returned the paper's five node/prefix/hit triples. The exact short-part ceilings `ceil(10^9 S)` were `156464182,83739991,387445747,177032327,84238191`, matching REF2_6. These do not verify the array-dependent tails or the five J ceilings.
- Exact rational checks passed for all ten distinct possible phase-edge coefficient values, the displayed `2^48` diagonal ceilings, the common denominator Delta, `8439+2+3732=12173`, the 297469356 nonterminal rows per stationary file, and the two final row-sum comparisons. The distinction between these arithmetic checks and acceptance of the missing arrays is essential.
- The 22 macro arguments are distinct. The current PDF contains 23 rendered pending phrases, comprising the 22 invocations and the explanatory legend. The macro itself renders correctly.
- **Compilation passed.** I copied the working-tree sources to [build-copy](/home/ubuntu/aklt/reports/EDIT3_DELTA/build-copy), excluding Git metadata and old build products, and ran exactly `latexmk -pdf -interaction=nonstopmode main.tex` there. It exited 0 after three pdflatex passes and produced an 83-page [main.pdf](/home/ubuntu/aklt/reports/EDIT3_DELTA/build-copy/main.pdf). The final [main.log](/home/ubuntu/aklt/reports/EDIT3_DELTA/build-copy/main.log) has no undefined references or citations, errors, or multiply defined labels; it has one harmless underfull vertical box. The complete command output is [latexmk-output.log](/home/ubuntu/aklt/reports/EDIT3_DELTA/build-copy/latexmk-output.log). A source check also found 137 distinct labels, 354 resolved reference occurrences, and two resolved citation keys.
- `git diff --check` passed. SHA-256 comparisons of all 20 original top-level files, including the original PDF and build products, were identical before and after this review. No paper file was edited or built in place. The binary `main.pdf` diff was excluded from the editorial review as requested.

Hunks checked

All 30 source hunks from the ordinary `git diff` are listed below. Coordinates are the exact old/new hunk headers; links point into the current original working tree. “Pass” for a pending-data marker means its scope is appropriate, not that the missing data passed verification. Finding 2 additionally concerns unmarked uses and statements outside the changed lines.

| # | File and hunk coordinates | One-line verdict |
| --- | --- | --- |
| 1 | [app-input-contracts.tex:13](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:13), `-13,10 +13,11` | **Fix:** unsupported accompanying-formalization/Lean verification claim; finding 1. |
| 2 | [app-input-contracts.tex:238](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:238), `-237,8 +238,10` | **Pass:** separates and marks the missing named H2 file's indexing/positivity and row acceptance checks. |
| 3 | [app-input-contracts.tex:257](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:257), `-254,6 +257,7` | **Pass:** marks extrema assertions about that archived vector; independent H2 existence is a separate matter. |
| 4 | [app-input-contracts.tex:268](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:268), `-264,6 +268,7` | **Pass:** marks the missing archived vector's specified maximizing-row data; the displayed cancellation is correct. |
| 5 | [app-input-contracts.tex:330](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:330), `-325,7 +330,9` | **Pass:** fully repairs REF2_6 Minor 3; every actual terminal rule and reward descends. |
| 6 | [app-input-contracts.tex:405](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:405), `-398,12 +405,14` | **Fix:** archived-map indexing tag is warranted; independently verified window counts are overmarked; finding 3. |
| 7 | [app-input-contracts.tex:424](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:424), `-415,6 +424,7` | **Pass:** the particular archived map's direction, kind, successor and incoming-direction comparisons remain unverified. |
| 8 | [app-input-contracts.tex:465](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:465), `-455,9 +465,11` | **Pass:** fully repairs REF2_6 Minor 2's trail-domain, length and within-type ordering defects. |
| 9 | [app-input-contracts.tex:512](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:512), `-500,10 +512,9` | **Pass:** proof conclusion now has exactly the lemma's long-trail scope; prefix/suffix factorization is unaffected. |
| 10 | [app-input-contracts.tex:770](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:770), `-759,6 +770,7` | **Fix:** ceiling formula and numerical ceiling checks are established, not an outstanding witness acceptance; finding 3. |
| 11 | [app-input-contracts.tex:840](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:840), `-828,7 +840,8` | **Pass:** short sum now explicitly ranges over the correct distinct-endpoint kernel trails and keeps the prescribed short order. |
| 12 | [app-input-contracts.tex:973](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:973), `-960,7 +973,8` | **Fix:** Delta divisibility is already exactly verified; finding 3. |
| 13 | [app-input-contracts.tex:994](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:994), `-980,7 +994,7` | **Pass:** “kernel trails” matches the proof's actual trail class and all-length conditional bound. |
| 14 | [app-input-contracts.tex:1120](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1120), `-1106,15 +1120,18` | **Pass:** identifies the missing full arrays' literal indexing, free inequalities, caps and terminal values as pending. |
| 15 | [app-input-contracts.tex:1153](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1153), `-1136,6 +1153,7` | **Pass:** marks the unresolved local-row checks on the five arrays; the row count is correct. |
| 16 | [app-input-contracts.tex:1169](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1169), `-1151,6 +1169,7` | **Fix:** prefix enumeration counts are already verified and independent of the absent arrays; finding 3. |
| 17 | [app-input-contracts.tex:1182](/home/ubuntu/aklt/manuscript-v2/app-input-contracts.tex:1182), `-1163,13 +1182,17` | **Fix:** J-value tag is warranted, but optional lookup rule is overmarked and completed Lean verification is unsupported; findings 1 and 4. |
| 18 | [main.tex:20](/home/ubuntu/aklt/manuscript-v2/main.tex:20), `-20,6 +20,7` | **Pass:** macro definition is valid, visible, and has no mathematical effect; its argument records the source identifier. |
| 19 | [main.tex:49](/home/ubuntu/aklt/manuscript-v2/main.tex:49), `-48,7 +49,9` | **Fix:** abstract overstates verification and leaves its gap assertion unmarked; findings 1 and 2. |
| 20 | [sec1-result.tex:7](/home/ubuntu/aklt/manuscript-v2/sec1-result.tex:7), `-7,8 +7,9` | **Fix:** introductory verification/status claim needs the same correction and gap qualification; findings 1 and 2. |
| 21 | [sec7-recursion.tex:77](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:77), `-77,8 +77,11` | **Pass:** at a U departure, distinct non-arrival pairs in the pre-step removal domain meet the ordinary response-pair definition. |
| 22 | [sec7-recursion.tex:579](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:579), `-576,12 +579,13` | **Pass:** defines sigma on every actual kernel trail; short keys, zero rewards, ties and long ordering agree with every use. |
| 23 | [sec8-inputs.tex:4](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:4), `-4,19 +4,23` | **Fix:** kernel terminology and finite contracts are correct; verification claim and Lean-only status legend are not; finding 1. |
| 24 | [sec8-inputs.tex:53](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:53), `-49,6 +53,7` | **Fix:** local enumeration numbers are already independently verified; finding 3. |
| 25 | [sec8-inputs.tex:66](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:66), `-61,6 +66,7` | **Pass:** exact equality with the absent pattern/choice files remains an appropriate pending obligation. |
| 26 | [sec8-inputs.tex:98](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:98), `-92,12 +98,14` | **Pass:** sector reconstruction/count and the 8439 blocks' strict-dominance tests are unresolved and correctly tagged. |
| 27 | [sec8-inputs.tex:126](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:126), `-118,6 +126,7` | **Pass:** matching the two actual Gram factors and every residual row remains unverified. |
| 28 | [sec8-inputs.tex:150](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:150), `-141,9 +150,10` | **Pass:** tags the fallback acceptance assertions, including the redundant 3734-block claim; no divisor, pivot or scale changes. |
| 29 | [sec8-inputs.tex:169](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:169), `-159,9 +169,9` | **Fix:** declaring the local certificate Lean-verified is unsupported; deterministic reduction itself remains sound; finding 1. |
| 30 | [sec8-inputs.tex:339](/home/ubuntu/aklt/manuscript-v2/sec8-inputs.tex:339), `-329,10 +339,9` | **Fix:** replaces the truthful noncompletion disclaimer with an unsupported checked-proof claim; finding 1. |
