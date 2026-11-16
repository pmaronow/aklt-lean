STATUS: COMPLETE

Completed the assigned scope in [sec2-moments.tex](sec2-moments.tex) and
[sec6-walks.tex](sec6-walks.tex). All twenty statement blocks are verbatim
copies of the current PLAN.md inventory, in its order. Every lemma and
proposition has a complete proof; the tracing and ratio definitions also
have derivations of their asserted identities and admissibility facts.

| Label | Written? | Depends on |
|---|---|---|
| d:moment | Yes — definition | Finite elementary conventions |
| l:moments | Yes — statement and proof | d:moment |
| d:pinmodel | Yes — definition | d:moment |
| l:finitefacts | Yes — statement and proof | d:moment, l:moments, d:pinmodel |
| l:35 | Yes — statement and proof, including the full covering range | l:moments, l:finitefacts |
| l:exact | Yes — statement and proof | l:moments |
| h:P | Yes — response property definition | d:pinmodel |
| d:domain | Yes — definition and normalization facts | d:pinmodel, d:moment, l:finitefacts |
| d:trace | Yes — definition, admissibility induction and coefficient identity | d:domain |
| l:stepid | Yes — statement and proof for the two prescribed degree ranges | l:moments |
| p:pairwalk | Yes — statement and proof, with all insertion degree cases | d:trace, l:stepid, l:finitefacts |
| d:ratios | Yes — definition and derivation of all step ratios | d:trace, l:moments, l:finitefacts |
| l:response | Yes — statement and proof with exact rational bounds | d:ratios, l:35, l:finitefacts |
| l:exposure | Yes — statement and proof for every ordering, including the empty set | d:trace, l:response |
| d:pattern | Yes — full covered pattern definition and positivity justification | d:domain, l:finitefacts |
| h:H1 | Yes — pointwise computational contract and fixed thresholds | d:pattern |
| l:local | Yes — statement and proof, including missing slots and every allowed tip status | l:35, h:H1, d:ratios, l:finitefacts |
| d:weights | Yes — lattice weight definition and trace comparison | h:H1, d:trace |
| h:H2 | Yes — all-length open-trail computational contract | d:weights |
| l:onepoint | Yes — statement and proof of the common sum-of-maxima bound | h:H1, h:H2, l:local, l:response, d:trace, d:weights |

## Deviations

None. No planned statement, hypothesis, constant, or label was changed.
The uniform response proof uses a short elementary rational logarithm
enclosure, with explicit fractions and cross products, to establish the
prescribed uniform constants. This is a proof choice, with the same
statement and bounds.

The satisfaction of (H1) and (H2), the type-dependent response theorem,
and the recursion proving (P) belong to other assigned files. Here H1,
H2 and P have precisely their planned status as definitions of contracts;
the conditional conclusions explicitly assume their prescribed premises.

## Checks run

- **Source baseline:** manuscript-corrected HEAD is
  9faa0eee768bef27a483cf7469c65c3e9958a84e, as specified.
- **Statement/interface audit:** All 20 blocks match PLAN.md exactly and
  appear in order. All 13 exported blocks among them match interfaces.tex.
  There are no duplicate labels or unresolved references.
- **Exact algebra:** [exact_checks.py](exact_checks.py), with Python 3.12,
  SymPy 1.14.0 and fractions.Fraction, verifies the twelve unit letters,
  all 35 monomial moments through degree four, covariance under a
  nontrivial rational orthogonal matrix, the four U and two D step
  identities with symbolic vector entries, both squared-norm moments,
  the three-field sum-of-squares identity, and every displayed rational
  response comparison and cross product.
- **Exact expansion checks:** Eight small retained-network contractions
  compare unnormalized pair numerators with complete stopped-trail
  expansions. They include both start statuses, both target statuses,
  D revisits, boundary stops with unchanged pin factors, ratio one at
  every D departure, and degree checks for every evaluated polynomial.
  These are algebra checks, not computational certificates for H1/H2.
- **Compilation:** [compile-sections.tex](compile-sections.tex) copies the
  entire preamble of manuscript-corrected/main.tex and inputs the two
  sections at section numbers 2 and 6. The resulting
  [compile-sections.pdf](compile-sections.pdf) has 13 pages. The final
  pdflatex build has no errors, undefined references, multiply defined
  labels, overfull boxes or underfull boxes. See
  [latex-build.log](latex-build.log) and [compile-sections.log](compile-sections.log).
- **Undefined references to other lanes:** None.
- **Scope/resource audit:** Only files in REV_C1a and temporary dependency
  files under /tmp were written. No inputs were modified and no
  sub-agents were launched. Computations were single-threaded; at most
  two independent processes ran concurrently.

Exact-check output is retained in [exact-checks.log](exact-checks.log).
The dependency installation under /tmp is recorded in
[dependency-setup.log](dependency-setup.log). To rerun in this environment:

    PYTHONPATH=/tmp/rev-c1a-py OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 python3 exact_checks.py
    pdflatex -interaction=nonstopmode -halt-on-error compile-sections.tex
    pdflatex -interaction=nonstopmode -halt-on-error compile-sections.tex
