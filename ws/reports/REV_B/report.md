STATUS: COMPLETE

Lane B is written in `sec5-window.tex` and `app-topology.tex`, in the contract's order. All nine assigned statements have complete proofs. Eight statements reproduce the contract verbatim up to whitespace; the clearance clause of `l:shellgeom` has the explicit scope clarification recorded below. The proof of the response premise (P) is not imported: this lane proves the specified implication from (P) to physical windows.

| Label | Written? | Depends on |
|---|---|---|
| `l:shellgeom` | Yes; clearance scope clarified below | `d:shells`; elementary square geometry |
| `l:cut` | Yes | `d:framemodel`, `d:pinmodel`, `l:threeframes`, `l:exact`, `l:finitefacts` |
| `l:removal` | Yes | `d:pinmodel`, `h:P`, `l:moments`, `l:finitefacts`, `l:35` |
| `d:thickcut` | Yes | `d:shells` |
| `l:cutgeom` | Yes | `d:thickcut`, `l:shellgeom`; the thickening sum is proved directly |
| `l:Xconn` | Yes | `l:cutgeom`, `l:boundaryconn`, `l:thicken` |
| `t:cutMOS` | Yes | `h:P`, `d:W`, `l:cut`, `l:removal`, `l:cutgeom`, `l:Xconn` |
| `l:boundaryconn` | Yes | Finite edge-set algebra over F₂ and the two stated star-connectivity hypotheses |
| `l:thicken` | Yes | Cross intersections, the distance Lipschitz inequality, and positive finite sums |

## Deviations

1. **`l:shellgeom`: make the nonexceptional index condition explicit in the parallel-side clause.** The contract's standalone sentence “Every side …” must use the preceding range `2 ≤ i ≤ i₁`, `i ∉ I₀`. Without that scope it is false. Take `l₀ = 64`, any integer `s ≥ 390`, `u = s⁴`, `a = 0`, `y = (2s − u, −u − 1)`, and `i = 2`. Then `k₂ = 2s`, the left shell side has first coordinate `−u`, and it meets `C_u(0)` at distance one from the left exterior half-plane. This is less than `s/3`. The corner `(−u,−u)` itself belongs to `D₂`, so `2 ∈ I₀`. The minimal correction used in the section is to begin that sentence **“For the same indices `2 ≤ i ≤ i₁` outside `I₀`, every side …”**. This is the quantifier already explicit in the baseline shell lemma and used in the plan's geometric argument. All other assertions, constants, labels, and the exported window conclusion are unchanged. The counterexample is also given immediately before the lemma in the LaTeX file. The matching correction to both read-only contract files is supplied, unapplied, in `interface-scope.patch`.

No other statement changes are needed. The geometry proof supplies the concrete admissible threshold `s₀ = 390`, which is stronger than the contract's existential threshold and does not alter its statement.

## Checks run

- Read the current contract, `interfaces.tex`, `RISKS.md`, the cited baseline cut and topology proofs at manuscript HEAD `9faa0eee768bef27a483cf7469c65c3e9958a84e`, the relevant strengthening/MOS proofs, and the adopted opportunities. Computational H1/H2/H3 witnesses are not dependencies of Lane B; only the quantified (P) interface is used. No inputs were modified and no sub-agents were launched.
- `python3 -u check_lane_b.py > checks.log 2>&1` passed, using one process and exact integer/rational arithmetic. It checks the nine statements against the contract, permitting only the recorded clearance clarification, and checks that all cross-lane citations are allowed.
- The same script exhaustively checks all 511 nonempty subsets of a `3×3` square. The 387 sets satisfying both topology hypotheses have nonempty star-connected exterior boundaries. Cross thickening is checked for all 388 star-connected subsets.
- Eight physical-geometry samples use actual admissible scales `u = 390⁴`, `390⁴ + 1`, `391⁴ − 1`, and `396⁴`. These include an exterior corner, sides outside the square before radial shifting, clearance at its endpoint, nonintegral fourth roots, and swapped axes. The script uses integer fourth roots for every shell/cap/exception test. It checks every shell index through `i₁` for the sampled exterior sites; for the chosen cuts it checks both connectivities, window containment and its neighbours, raw/thick depths, the per-level count, separation, and the thickening inequality at exact `ϑ = 1/2, 9/10`. Complement connectivity is checked by a finite padded-rectangle graph compressed into horizontal runs. All samples passed; detailed sizes and minima are in `checks.log`. These finite checks are supplemental to the uniform proofs.
- Exact rational checks confirm the removal lower bounds `41/50 > 1/2` and `14/25 > 1/2`, and seed logarithmic four-spin cost `4/5 ≤ 1`. The text retains the single seed and constants `1,4,2`; raw depth `max(t,16) − 2`; thick depth `13`; count `48`; thickening factor `5/θ`; and precisely the specified `E` and `p₀ = exp(−2E)`.
- `compile-wrapper.tex` uses the preamble, packages, macros, and theorem environments copied from the read-only baseline `main.tex`. Two successive runs of `pdflatex -interaction=nonstopmode -halt-on-error compile-wrapper.tex` succeeded after the referee revisions. `compile-wrapper.pdf` has 11 pages, with no LaTeX errors, overfull boxes, multiply defined labels, or unresolved internal references. The section and appendix are numbered §5 and Appendix B.

The standalone wrapper intentionally omits other lanes. Its only undefined labels are:

`d:W`, `d:framemodel`, `d:pinmodel`, `d:shells`, `h:P`, `l:35`, `l:exact`, `l:finitefacts`, `l:moments`, `l:threeframes`.

The uniform tail bound in the proof of `t:cutMOS` is analytic: with `c = −log θ > 0`, it uses `exp(cs/12) ≥ (cs/12)¹⁰/10!` to obtain an eventual bound for **every** larger scale. It is not inferred from the sampled scales.

## Response to referee

The referee's verdict is **SOUND WITH FIXES**. Its only numbered finding is R1 below: a genuine mismatch between the read-only export and the necessary hypothesis already used by the local proof. For completeness, FN1–FN8 record the eight formalization notes separately; the referee did not identify them as mathematical defects. The statement table and proof audit raised no further adverse findings.

| Id | Genuine? | Action taken (file:line) | Plan label and where supplied/proved |
|---|---|---|---|
| R1 (numbered finding 1) | yes | Spelled out the complete nonexceptional range in `sec5-window.tex:31`; made the scale threshold, index range, nonexceptionality, and intersection hypothesis explicit at its use in `sec5-window.tex:598`. Retained the counterexample at `sec5-window.tex:19`, now also specifying `l₀ = 64`. Supplied the matching, unapplied `interface-scope.patch:1` for both `PLAN.md` and `interfaces.tex`. | `l:shellgeom`, proved in `sec5-window.tex:40`; used only with `u ≥ M_g(64)`, `2 ≤ i ≤ i₁`, and `i ∉ I₀`. The contract inputs were not modified. |
| FN1 (original volume) | no | Added an explicit original-volume convention at `sec5-window.tex:5`; the restricted-leg factorization and original protected layer remain unchanged. | `d:pinmodel`, supplied by Lane C's `sec2-moments.tex` under the plan; applied with the original `G` throughout `l:cut` and `l:removal`. |
| FN2 (two ambient metrics) | no | Retained the explicit metric convention at `sec5-window.tex:10` and added the full nonexceptional quantifier at `sec5-window.tex:31`. Original response depths remain in the ambient ℓ¹ metric; square/corner geometry remains in ℓ∞. | Shared `d:moment`, `d:shells`, `h:P`; geometry proved in `l:shellgeom` and `l:cutgeom` in `sec5-window.tex`. |
| FN3 (removal cases) | no | Replaced indicator notation by literal cases `k = 0,1`, `k = 2,3`, and `k = 4` at `sec5-window.tex:259`. The quartic polynomial and its four endpoints are defined only in the last case, explicitly stated at `sec5-window.tex:273`. | `l:removal`, proved in `sec5-window.tex:247`, using exactly `l:moments` from Lane C's `sec2-moments.tex`. The statement and constants are unchanged. |
| FN4 (joint conditional law) | no | Gave the factorization and product normalization of the whole neighbour-set conditional law directly at `sec5-window.tex:289`. Only positive-probability fibres are used; no pin factors occur and each site has at most three surviving bonds. | Imported `l:finitefacts` and `l:35`, supplied/proved in Lane C's `sec2-moments.tex`; their positivity and at-most-three-factor hypotheses are checked before use in `l:removal`. |
| FN5 (degree budget) | no | Rechecked and retained the separate-degree explanation at `sec5-window.tex:352`: each inserted endpoint has lost its arrival bond and gains one observable occurrence. | `l:moments`, `l:exact`, and `l:finitefacts`, supplied by Lane C's `sec2-moments.tex`; no insertion exceeds separate degree four. |
| FN6 (finite parity sums) | no | Made the plaquette coefficients literal finite sums using an explicit endpoint cutoff `R`, including `Z′ = ∅`, at `app-topology.tex:39`. Gave finite vertical telescoping and the separate `j ≥ R` zero case at `app-topology.tex:75`. | `l:boundaryconn`, proved entirely in `app-topology.tex:18`; no other-lane topology result is used. |
| FN7 (nonempty cut and order) | no | Made the Appendix B location of both internal lemmas explicit at `sec5-window.tex:679`. Nonemptiness precedes the root choice and shortest-path order at `sec5-window.tex:685`. In `l:cutgeom` the weighted cross bound is proved directly, without using connectedness before it is established. | `l:boundaryconn` and `l:thicken`, assigned by the plan to `app-topology.tex` and proved there at lines 18 and 150. At the use, `U` is finite, nonempty and star-connected with star-connected complement; hence `X₀` is finite, nonempty and star-connected. These are exactly the successive hypotheses. |
| FN8 (real scales and integer sites) | no | Explicitly distinguished real `s,T` from integer lattice quantities at `sec5-window.tex:421`. Retained the real exponential estimate, positive `c = −log θ`, and integer ceiling threshold at `sec5-window.tex:712`. | `d:shells`, `l:cutgeom`, and `t:cutMOS`; all tail estimates hold for every integer `u ≥ M⋆`, including nonintegral fourth roots. |

The cross-lane citation audit still finds only the permitted ten imported labels listed above. The same-lane results in Appendix B are now named by their plan labels and explicitly located in that appendix. Their hypotheses are checked at each use; no missing external theorem is assumed.

After the revisions, `check_lane_b.py` passed again in one process, including all statement, topology, exact-depth, and weighted-cut checks. The two-file patch was applied successfully to temporary copies of the contract, and each resulting `l:shellgeom` export matched the revised local statement exactly up to whitespace. The original `REV-PLAN/PLAN.md` and `REV-PLAN/interfaces.tex` remained byte-for-byte unchanged. Applying that patch to those read-only inputs is the remaining integration step for their owner; all authorized Lane B changes are complete. The window theorem and its displayed `E,p₀` are unchanged.
