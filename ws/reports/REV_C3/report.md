STATUS: COMPLETE

| Label | Written? | Depends on |
|---|---|---|
| `l:Iw` | Yes, statement and proof | `d:pattern`, `l:moments`, `l:finitefacts` |
| `l:leaf` | Yes, statement and proof | `d:pattern`, `l:moments`, `l:35` |
| `d:reduction` | Yes, definition and explicit factor convention | `l:Iw`, `l:leaf` |
| `c:reduce` | Yes, statement and proof | `d:reduction`, `l:leaf`, `l:Iw`, `l:moments` |
| `d:Pauli` | Yes, definition and explicit Pauli matrices | Elementary polynomial and matrix algebra |
| `l:inversion` | Yes, statement and proof | `d:Pauli`, finite Hermitian spectral theorem |
| `l:Ostruct` | Yes, statement and proof | `c:reduce`, `d:Pauli`, `l:inversion`, `d:reduction` |
| `d:exchange` | Yes, definition, basis conventions and local ladder actions | `d:reduction`, `d:Pauli` |
| `l:sector` | Yes, statement and ladder proof | `d:exchange`, finite Hermitian spectral theorem |
| `l:gram-residual` | Yes, statement and proof over both real and complex scalars | Elementary quadratic-form inequalities |
| `l:integercheck` | Yes, statement, explicit reconstruction and proof; optional Bareiss proof | `d:reduction`, `l:Iw`, `c:reduce`, `l:moments`, `l:Ostruct`, `d:exchange`, `l:gram-residual` |
| `p:certificate` | Yes, statement and proof | `l:integercheck`, `l:gram-residual`, `l:Ostruct`, `d:exchange`, `l:sector`, `l:inversion`, `c:reduce` |

The section file is [app-local-operator.tex](app-local-operator.tex). It contains all twelve assigned statement environments, in the plan's order, and nine complete proofs. The three definitions have additional explanatory algebra. Every statement environment matches both the amended plan and `interfaces.tex` verbatim.

The reconstruction starts with the pattern's retained bonds, vector attachments, radii and site statuses. It gives each coefficient as a finite sum of products of the displayed moments through degree four, applies the supplied inversion and explicit Pauli matrices, and forms the integer-coordinate central-sector matrices. A universally valid denominator is

`D_0 = 15^(number of retained U spins) * 25^(number of retained D spins) * product(vector-radius denominators)`.

The form matrix identity is exactly `M_epsilon = 15 D_0 q B_epsilon^* O(Fhat_c^I) B_epsilon`. The basis remains unnormalized, and the proof uses congruence of Hermitian forms. Gram/residual soundness is the primary route; the leading-minor criterion, bordered-minor invariant and exact Bareiss divisions are proved only as the optional fallback.

## Deviations

None. No planned statement needed correction, weakening or an additional hypothesis. The explicit coefficient formula, safe denominator and generator calculation supply details within the prescribed statements.

## Checks run

1. `python3 checks.py` — passed. The script uses only the standard library, exact `Fraction` arithmetic and an explicit implementation of `Q(sqrt(5))`. It checks:
   - All twelve statements against both contract files, their order, nine proof environments, and the complete external-reference list.
   - All 121 coordinate monomials of degree at most four against the finite icosahedral sum, including the diluted moments, and both corner sum-of-squares identities.
   - Eight representative core networks, including the empty vector list, a tip, one-bond U/D corners in both representations, and two-bond U/D corners, against independent direct finite-law partition sums.
   - Coefficient-denominator integrality, real symmetry, spin commutators, U-pair support, D-pair exchange, and the exact positive scale in ten central exchange sectors of those examples.
   - Integer Gram/residual examples of sizes zero through six, including singular `L` and nonunit positive scales; exact Bareiss divisions and equality of pivots with leading determinants independently computed by rational elimination.
2. `pdflatex -interaction=nonstopmode -halt-on-error wrapper.tex` — passed twice. [wrapper.tex](wrapper.tex) uses the exact preamble and macros from `/home/ubuntu/aklt/manuscript-corrected/main.tex` and inputs the section as Appendix D. [wrapper.pdf](wrapper.pdf) has ten pages. There are no TeX errors, overfull or underfull boxes, or unresolved internal references.
3. The six expected undefined references in the standalone wrapper are `d:moment`, `d:pattern`, `h:H1`, `l:35`, `l:finitefacts`, and `l:moments`. All are plan labels belonging to the other Lane C files. All references in the section use plan labels.
4. Exact computations used a single Python process; all commands stayed within the four-core limit. No sub-agents, certificate searches, floating arithmetic in the mathematical checks, or input modifications were used.

The exact tests validate representative formulas and networks. Exhaustive pattern coverage and all numerical witness-row checks remain with `t:H1` and `t:inputs` in the separately assigned section files. All Appendix D implications are proved here without assuming a stored matrix or stored pivot list.

The principal proof sources were the amended Appendix D inventory and interfaces, the corrected manuscript's `app-local.tex`, OPPORTUNITIES entries 2, 5 and 21, and the H1 reconstruction and Gram/residual discussion and programs in `compfeas`. The source risk register's finite-degree, full-slot, support and certificate distinctions are preserved.
