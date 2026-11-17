VERDICT: GAP

## Scope and conclusion

I read the complete LaTeX paper, checked Section 8 and Appendix C line by line, and checked their uses of results elsewhere against the stated hypotheses. I read no other pre-existing machine files. The computations below used one process and did not modify the inputs.

The deterministic implication from passing certificates to (H1), (H2), and (H3\(_h\)) is sound after the two statement clarifications below. I independently verified the H2 existence assertion, the enumerations, the displayed arithmetic, and the prefix enumeration and short sums. The unconditional H1 and H3 assertions remain unverified: their essential witness files are absent from the supplied paper directory, and the paper does not identify an accessible archive. This is the reason for GAP; it is not a counterexample to H1, H3, or the spectral-gap conclusion.

## Numbered findings

### 1. Critical — the unconditional local and stationary input assertions have unresolved certificate obligations

**Locations and labels:** [sec8-inputs.tex:148](/home/ubuntu/aklt/review/REF2/paper/sec8-inputs.tex:148), t:H1; [sec8-inputs.tex:270](/home/ubuntu/aklt/review/REF2/paper/sec8-inputs.tex:270), t:inputs; [app-input-contracts.tex:1069](/home/ubuntu/aklt/review/REF2/paper/app-input-contracts.tex:1069), p:stationary-check. See also sec8-inputs.tex:160–164, 310–336 and app-input-contracts.tex:1087–1172.

**Exact claims.** Theorem t:H1 asserts both pointwise local inequalities unconditionally. Proposition p:stationary-check asserts the existence of five full integer supersolutions and the five stated upper bounds on \(J\). Theorem t:inputs consequently asserts (H1) and (H3\(_h\)) unconditionally.

**Unresolved step.** The proofs specify what a checker must verify, but the submitted material contains neither the essential local representation/inversion records nor the stationary arrays. The input directory contains only the thirteen TeX files and main.pdf; the PDF has no embedded files. No archive URL, persistent identifier, or bibliography entry identifies the referenced archive. In particular, the following checks cannot be completed from the submitted material:

- The regenerated local matrices using the choices in certificates_covered_operator_only.jsonl, their sector counts and dimensions, and their positive pivots or residual rows. The two Gram factors are also absent; they could be dispensed with if all relevant fallback computations were actually supplied and verified.
- The particular class map in windows_m10_min.txt that fixes the interpretation of the stored stationary array indices.
- Every free, cap, terminal and local inequality for the five stationary files, and their array-dependent prefix evaluations. Each file entails 297,469,356 nonterminal component inequalities, in addition to the other checks.

The local enumeration counts and the counts of prefix branches do not establish these assertions. Nor do the displayed five \(J\) ceilings establish themselves. The soundness lemmas prove implications from passing tests, rather than existence of passing data. The paper itself calls these numerical assertions “to be verified separately” at app-input-contracts.tex:1172.

**Repair.** Supply an identified archive containing the necessary literal data and complete the prescribed exact checks. A completed Lean development is not required for an ordinary computer-assisted proof, but the exact numerical assertions must be substantiated. Until then, an honest assembly statement is:

~~~latex
\begin{theorem}[Conditional input assembly]\label{t:inputs}
Assume that all finite local coverage, reconstruction and positivity
assertions specified in this section hold, and assume
Proposition~\ref{p:stationary-check}.
Then (H1) holds at
\(c_{\rm s}=961/1000,\ c_{\rm t}=187/200\);
(H2) holds with
\[
 q=\frac{1119948287353}{1120437614225},\qquad C_V=10;
\]
and (H3\(_h\)) holds for the coefficients and orderings of
Definitions~\ref{d:kernel}--\ref{d:kernel-order}.
\end{theorem}
~~~

The same local-test qualification must then be attached to t:H1, and the stationary existence assertion must be explicitly treated as an input until discharged. This interim repair yields a conditional main gap theorem, not the presently claimed unconditional one. H2 need not remain an assumption: the independent exact witness supplied with this report proves its numerical existence claim.

### 2. Minor — the phase-expansion statement needs the exact within-type order and a long-trail qualification

**Locations and labels:** [app-input-contracts.tex:457](/home/ubuntu/aklt/review/REF2/paper/app-input-contracts.tex:457), l:phase-expansion, especially lines 458–466 and 503–506; [sec7-recursion.tex:572](/home/ubuntu/aklt/review/REF2/paper/sec7-recursion.tex:572), d:kernel-order.

**Exact claim.** The lemma identifies its phase sum with a trail's contribution to \(M_1h\), using \(\sigma_w\), under the wording “straight first visits before turning first visits.”

**Issue.** The phase products implement increasing path index within each type. Merely putting straight visits before turns does not impose that condition. Moreover, \(\sigma_w\) already denotes the rational-key ordering for lengths at most twelve. The proof correctly distinguishes this at lines 503–506, but the statement should make the distinction explicit.

Here is an exact diagnostic for the literal type-order-only reading. In row C take the length-ten trail
\[
\begin{split}
(-1,0),(-1,-1),(0,-1),(0,-2),(1,-2),(1,-1),\\
(2,-1),(2,0),(1,0),(1,1),(0,1).
\end{split}
\]
It avoids \(c\), first hits \(v\) at its last vertex, has distinct bonds and vertices, and all ten departures are turns. Thus the type-order condition alone is vacuous. Set
\[
x=x_{\rm t},\quad
K=b_{\rm t}+(a_{\rm t}+b_{\rm t})h_C,\quad
P=b'_{\rm t}h_C,\quad O=b'_{\rm t}.
\]
The rewards at departure indices 2 and 8 are \(P\) and \(O\); the other eight rewards are \(K\). Since \(K>P>O>0\), the prescribed short order is
\[
0,1,3,4,5,6,7,9,2,8.
\]
The phase sum instead uses path order. The phase sum minus the prescribed short contribution is exactly
\[
3^{-10}\bigl[(K-P)(x^9-x^3)+(K-O)(x^{10}-x^9)\bigr]>0.
\]
Consequently the phase identity must not be stated as an identity for the short-trail \(M_1h\) contribution on the basis of the type-order condition alone.

**Repair.** The only application to full trail contributions, at app-input-contracts.tex:1000–1001, concerns lengths greater than twelve and is valid. Replace the opening of the lemma by:

~~~latex
Let \(w\in\mathcal T_n^X\) with \(n>12\), and let \(\sigma_w\)
be the ordering of Definition~\ref{d:kernel-order}: straight first
departures in increasing path order, followed by turning first
departures in increasing path order.
Then its \(h\)-weighted contribution to \(M_1\) equals ...
~~~

Alternatively, define a separate \(\sigma_w^{\rm sf}\) for the phase identity at arbitrary lengths, and assert equality with the kernel contribution only when \(\sigma_w=\sigma_w^{\rm sf}\). The existing instruction to recompute short hits with their rational-key order is correct.

### 3. Minor — stopped quotient intertwining needs its terminal-data hypothesis in the statement

**Location and label:** [app-input-contracts.tex:315](/home/ubuntu/aklt/review/REF2/paper/app-input-contracts.tex:315), l:automaton-quotient, especially lines 326–328 and 358–363.

**Exact claim.** The lemma says the intertwining also holds for each finite stopped continuation sum. Its proof adds that the stopping rule and terminal reward must factor through the quotient state.

**Issue.** That condition is necessary and should be stated, rather than introduced only in the proof. For example, for \(m=2\), quotient windows by their last direction. This quotient satisfies the displayed transition hypotheses. The raw windows \((\mathrm E,\mathrm N)\) and \((\mathrm W,\mathrm N)\) have the same image, but a zero-step terminal reward supported only on the first window cannot descend to the quotient.

**Repair:** append the following sentence to the lemma statement:

~~~latex
The assertion for stopped sums assumes that the raw terminal
indicator and terminal reward are pullbacks of their quotient
counterparts.
~~~

All actual uses satisfy this condition: the terminal positions are \(c,v\), and the target reward depends only on the phase. Thus this is a statement repair, not a defect in the stationary application.

## Statement table

“Pass” evaluates the stated deterministic implication under its explicit hypotheses. It does not certify missing numerical witnesses. All Appendix C labels below are in app-input-contracts.tex.

| Label | Content | Verdict | Dependencies |
|---|---|---|---|
| Section 8, unlabelled finite local contract | Exhaustive patterns, effective records, matrix reconstruction, Gram/Bareiss tests | Enumeration independently verified; matrix assertions unresolved | d:pattern; l:leaf; l:moments; l:Iw; l:integercheck; l:gram-residual |
| t:H1 | Pointwise local inequalities at 961/1000 and 187/200 | GAP in numerical discharge; reduction is sound | Local coverage and matrix tests; l:Ostruct; l:sector; l:inversion; c:reduce |
| t:inputs | Assemble H1, H2 with \(C_V=10\), and H3\(_h\) | Conditional assembly passes; unconditional claim unresolved | t:H1; p:H2-test; l:alm; l:H2-CV; p:automaton10; p:stationary-check; l:stationary-assembly |
| d:memory-automaton | Bond-distinct windows, admitted directions, successor and kind | Pass; \(m\ge1\) ensures a final direction | Finite square-lattice directions; unoriented bonds |
| d:memorygrowth | Exact one-step matrix and true last-window weight sums | Pass | d:memory-automaton; d:weights |
| l:alm | True/window domination and positive-vector growth bound | Pass | Revisit weight \(1/5\le x_\tau/3\); finite positive vector |
| l:H2-dihedral | Dihedral invariance; 916 windows and 115 orbits | Pass; counts independently verified | d:memory-automaton; absolute direction relabeling |
| p:H2-test | Integer vector, exact extrema, exact maximum \(q_*\) | Pass independently, using the supplied referee witness | Regenerated windows and 916 exact row checks |
| l:H2-CV | \(W_r\le x_{\rm t}^r\) and \(C_V=10\) | Pass; rational comparisons independently verified | p:H2-test; l:alm; at most three directions |
| l:automaton-quotient | Labeled quotient and backward intertwining | Pass after terminal-data clarification in finding 3 | Same admissibility, kind, successor class, and required final direction |
| p:automaton10 | 60,092 windows, 3,741 states, stated edge counts | Quotient existence and counts independently verified; particular archived map unavailable | Raw enumeration; partition refinement; l:automaton-quotient |
| d:phaseweights | Four phases, diagonal and response weights, initial/terminal vectors | Pass | d:kernel; positive \(x_\tau,h\); l:log-mean-bounds |
| l:phase-expansion | Phase representation of the straight-first response sum | Pass with exact ordering/length clarification in finding 2 | d:phaseweights; d:kernel-order |
| d:stationary-walk | Stationary lattice operator, two known sites, centre and target stopping | Pass for a valid quotient | l:automaton-quotient; d:phaseweights; d:kernel |
| l:stationary-domination | Dominate each true suffix/history, preserving multiplicity | Pass | \(L\ge m+2=12\); fixed initial bond; at most two departures; \(b'_\tau\le b_\tau\) |
| l:Bellman-soundness | Supersolution bounds every finite stopped sum and its supremum | Pass | Finite branching; nonnegative coefficients and reward; zero terminal rows |
| d:stationary-certificate | Integer ceilings, free supersolution, caps and local rows | Pass as a finite contract | Exact rational coefficients; valid quotient; \(D_3,V>0\) |
| l:stationary-local-global | Extend stored potential to the whole plane and obtain a Bellman supersolution | Pass | d:stationary-certificate; stationary/free row domination; \(F\le z\) |
| d:prefix-bound | Exact short sum plus all surviving length-twelve phase prefixes | Pass; enumeration and denominator checks independently verified | Actual departure counts, dead-site rewards and short order; last-window quotient |
| l:prefix-domination | Bound every finite cutoff and all lengths by \(J\) | Pass for any passing certificate | Long-trail phase identity; stationary domination; local/global extension; Bellman induction |
| l:kernel-reflection | Equality of B/N and B/S true contributions | Pass | Reflection fixes B triple; preserves types, rewards, indices and shifts |
| p:stationary-check | Five integer supersolutions and five \(J\) ceilings | GAP: essential arrays and their full checks unavailable | Particular quotient indexing; d:stationary-certificate; d:prefix-bound |
| l:stationary-assembly | \(M_1h\le\rho_0h\), including every finite cutoff | Pass conditional on the five certificates and prefix ceilings | l:prefix-domination; l:kernel-reflection; exact final rational comparisons |

## Independent exact computations

The following checks were performed independently of the unavailable archive.

- **Local enumeration.** The Cartesian product has 2,048,000 assignments. Filtering gives 106,101 consistent assignments, 184,914 marked assignments, 123,339 with the mark N or E, and 7,962 effective reflection classes. The effective record retained the marked outgoing site, present internal bonds, and incident non-tip statuses. This verifies the stated cardinalities, not equality with the absent pattern file.
- **Memory windows and quotient.** The counts through memory ten are \(4,12,36,108,316,916,2628,7500,21268,60092\). Partition refinement retaining absolute direction labels and the required incoming direction gives 3,741 classes and 2,516 straight, 5,032 turning, and 1,872 revisit edges. This supplies a valid quotient independently; its arbitrary class numbering is not asserted to match the unavailable array indexing.
- **H2.** A 115-entry positive integer vector was recovered and pulled back to all 916 raw windows. Every row inequality was checked with integers. The minimum, maximum, their codes, the value at code 428, its row numerator, and the maximum ratio agree exactly with p:H2-test. In particular the maximum is \(1119948287353/1120437614225\), not an approximate eigenvalue. The checks \(999/1000<q_*<2499/2500\) and \(6(200/(187q_*))^6<10\) also pass.

The durable H2 artifacts are [referee_h2_witness.json](/home/ubuntu/aklt/reports/REF2_6/referee_h2_witness.json) and [verify_referee_h2.py](/home/ubuntu/aklt/reports/REF2_6/verify_referee_h2.py). Running the latter with Python 3 regenerates the windows and verifies all rows using integers and fractions. It reads only the referee-generated witness. No claim of byte-for-byte agreement with the unavailable archive is made.

The exact prefix recursion gives:

| Case | Nodes | Surviving length-12 prefixes | Short first hits | \(\lceil10^9 S_{X,d_0}\rceil\) |
|---|---:|---:|---:|---:|
| B/N | 139985 | 89150 | 937 | 156464182 |
| B/W | 161929 | 103257 | 922 | 83739991 |
| C/N | 105025 | 66947 | 715 | 387445747 |
| C/W | 155673 | 99168 | 1036 | 177032327 |
| C/S | 145485 | 92748 | 861 | 84238191 |

The three counts in every case agree with the paper. The short sums were evaluated as exact fractions with the prescribed rational-key ordering, not with the phase order. The last column is a new exact integer ceiling of the short part alone; it does not verify \(J\), which additionally depends on the missing potential entries.

I also checked that the displayed
\[
\Delta=12139925673538045870080000
\]
clears every possible actual phase-edge denominator, including all dead-neighbour choices. The four displayed \(2^{48}\)-ceiling numerators are correct. The spatial count \(19881=141^2\), nonterminal row count, and the two final assembly comparisons are correct. The B-row ceiling leaves the exact positive margin \(729/10^9\) below \(\rho_0h_B\). The C comparison follows from the displayed dyadic \(h_C>1199/1000\) and \(993015\cdot1199=1190624985\).

## Formalization notes and hypothesis audit

1. **Keep numerical obligations separate.** Define decidable local and stationary acceptance predicates. Prove the generic implication theorems, then instantiate them with actual literals and proved acceptance. The currently missing H1/H3 instantiations must not become axioms or be inferred from file counts. The separate Lean verification need not be assumed in the mathematical soundness lemmas.

2. **The H1 dependencies are used within their hypotheses.** Both thresholds lie strictly in \((0,1)\), as required in Appendix D. Groups, inversions and degree bounds are correctly enforced. The positive scale is \(15D_0q\), and the matrices are Hermitian-form matrices \(B_\epsilon^*PB_\epsilon\) in unnormalized integer bases. They are not coordinate matrices obtained by an orthonormal-basis substitution. Isolated discarded factors are common and strictly positive. The empty vector list and zero-dimensional sectors cause no exception.

3. **The local fallback is sound.** With a removed positive common factor \(a\), the trailing-matrix invariant is \(A^{(j)}=a^{j+1}B^{(j)}\); the preceding pivot has factor \(a^j\), including \(j=0\). Exact normalized divisions therefore imply exact original divisions and positive original pivots. Symmetry justifies storing only the upper triangle. No division is required after the last pivot.

4. **H2 uses a right positive vector with row trail masses.** Preserve the orientations \(A_{n+1}\le A_n\mathsf A_m\) and \(\mathsf A_mv\le qv\). A detected revisit is an earlier departure; a forgotten revisit is bounded above by a first-departure coefficient. The initial reversal is forbidden, but its virtual bond is not a used trail bond. The empty trail has weight one, so \(C_V\ge1\).

5. **H3 must retain absolute labels.** The H2 dihedral reduction cannot be substituted for the H3 quotient. Quotient edges retain each direction and each next-phase possibility separately; no class-size division or spatial wrapping is allowed. Mixed-incoming classes have only revisit edges, on which no response direction is required.

6. **The known-site rule is justified at every suffix time.** For \(j\ge L\ge12\), remembered departure indices begin at \(j-10\ge2\). Initial departures 0 and 1 are outside the memory. Detection at \(u\) or \(a\) would imply a third departure, impossible using the available distinct incident bonds. The fixed initial bond remains forbidden in both directions. A true outgoing neighbour is live, including on the final step. No periodicity or parity multiplier is used.

7. **Nonnegative series need an explicit representation.** Use finite-horizon path sums, then their monotone supremum or an equivalent nonnegative series. Bellman soundness requires no stochastic row normalization and no asymptotic remainder estimate. Terminal rows are zero even when the terminal reward is zero. The target and centre lie inside \(B_{70}\); the outside cap and free-row comparison establish the inequality at every outside state.

8. **Prefix bookkeeping is essential.** Include a hit at time twelve in the short sum by testing the hit before the length cutoff. Surviving prefixes avoid both \(c\) and \(v\); keep their multiplicities when quotient states coincide. Use preincrement departure counts to freeze each earlier reward. For longer trails, use straight-first weights on the prefix even though that prefix itself has length twelve. The actual full trail has length greater than twelve, which is why this ordering is appropriate.

9. **Arithmetic must be unbounded.** The 32-bit storage format does not bound row products or accumulators. H2 cross-products, rounded-coefficient times potential products, prefix denominators and Bareiss intermediates exceed machine-integer ranges. Use mathematical integers/naturals or checked sufficiently wide arithmetic. All denominators used in the proof are positive; zero rewards use a separate infinite-key case rather than division by zero.

10. **Assembly matches the downstream hypotheses.** The B reflection is applied to true trail sums, not to a presumed symmetry of the quotient or the potentials. C uses three independent first directions. The bounds hold uniformly for every finite cutoff and hence give precisely h:H3. The H2 constants and the coefficient/vector/order choices match t:rec, including \(a_{\rm t}=150000/10^6\).

## ORCH-SUMMARY

- Verdict: GAP in the unconditional computational inputs as submitted.
- Read the whole paper; audited Section 8 and Appendix C line by line.
- Essential H1 choices/matrix checks and five H3 potential arrays are absent.
- No accessible archive is identified; native-check claims cannot be inspected here.
- Deterministic local reduction, memory domination, stationary domination and Bellman soundness pass.
- Restrict the phase-to-kernel identity to the specified long-trail order.
- State the terminal-data factorization hypothesis for stopped quotient sums.
- Independently re-established H2, including all 916 exact rows and the precise \(q_*\).
- Reproduced local enumeration, memory-ten quotient counts, all five prefix counts and exact short sums.
- Verified coefficient ceilings, common denominator, \(C_V=10\), and final assembly arithmetic.
- H1/H3 remain conditional; no counterexample to their inequalities was established.
- Referee H2 witness and standalone exact verifier accompany this report.
