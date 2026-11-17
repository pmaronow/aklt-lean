STATUS: PASS
BLOCKING: 0

DECL: reducedDifferenceReal PASS

`AKLT.Defs.reducedDifferenceReal` (`AKLT/Defs/RealOperator.lean:58`) matches the difference polynomial in Definition `d:reduction`, `app-local-operator.tex:148–170`, specifically the formula at lines 156–158: \(\widehat F_c=\widehat Z_{\rm cur}-c\widehat Z_{\rm next}\). The appendix fixes a covered pattern and a real threshold \(0<c<1\) at `app-local-operator.tex:5–12`. The rational-threshold restriction appears only in the later integer certificate lemma (`app-local-operator.tex:582–585`), and is correctly absent from this definition's real parameter.

The defining expression uses `false` for current and `true` for next, in the correct order. Tracing `reducedPolynomialReal` through `reducedPolynomial` and `reducedIntegrand` (`AKLT/Defs/Operator.lean:91–109`) confirms that next changes the passage law to D and deletes precisely the unordered passage/outgoing bond. This is the convention in `sec6-walks.tex:513–516`. The passage spin is contracted together with the other retained spins, rather than first; finite distributivity gives exactly the paper's factors I and J (`app-local-operator.tex:24–63`, `app-local-operator.tex:625–634`).

The underlying leaf construction agrees with `app-local-operator.tex:148–170`: both representations drop isolated tips/corners and their common positive factors; bonded tips become single vectors of radius 3/5; reduced one-bond corners become singles of radius 1/2 (U) or 1/3 (D); unreduced one-bond corners and other bonded corners retain their spin, original status law, and both slots. These choices are implemented by `SingleReplacement`, `reducedSpinSites`, `reductionGroups`, and `replacementRadius` (`AKLT/Defs/Operator.lean:20–55`). In covered patterns each single has exactly one incident bond, so `leafNeighbour`'s default is unused. All internal variables appearing in the reduced integrand belong to the contracted site set, and removed sites contribute neither a variable nor a status moment.

`contractSpins` sums each monomial coefficient times the product of its site moments, retaining its external-vector exponents (`AKLT/Defs/Operator.lean:69–87`). Mathlib's `Finsupp.comapDomain Sum.inr` really restricts the exponent function to the external summand (`Mathlib/Data/Finsupp/Basic.lean:503–518`). The rational moment cases are precisely 1, 1/3, 1/5, 1/15, or zero, with positive-degree D moments scaled by 3/5 and constant moment one. These match `sec2-moments.tex:35–52` and `app-local-operator.tex:636–652`. Coveredness and the factor counts ensure separate spin degree at most four (`app-local-operator.tex:183–195`), so the moment function's behavior at higher degrees is irrelevant here.

Mathlib's `MvPolynomial` is the formal polynomial ring with finitely supported natural exponent vectors (`Mathlib/Algebra/MvPolynomial/Basic.lean:80–106`). `MvPolynomial.map` changes coefficients, not variables or exponents; `coeff_map` states this explicitly (`Mathlib/Algebra/MvPolynomial/Eval.lean:329–345,384–401`). `Rat.castHom ℝ` is the ordinary injective rational-to-real ring homomorphism (`Mathlib/Data/Rat/Cast/CharZero.lean:24–64`). Thus the rational reconstruction is embedded exactly, without rounding or loss of coefficients. `MvPolynomial.C c` is the constant polynomial c; multiplication by it scales every coefficient by the arbitrary real c. Subtraction is ordinary ring subtraction, as confirmed by `coeff_sub` (`Mathlib/Algebra/MvPolynomial/CommRing.lean:68–73`).

Consequently, for every assignment `u : Fin 20 → Vec3`, Mathlib's evaluation homomorphisms give

```text
evaluateRealPolynomial (reducedDifferenceReal π r c) u
  = evaluateReduced (reducedPolynomial π r false) u
      - c * evaluateReduced (reducedPolynomial π r true) u.
```

The relevant evaluation meanings are `eval`, `eval_map`, `eval₂_mul`, and `eval₂_sub` (`Mathlib/Algebra/MvPolynomial/Eval.lean:138–142,255–257,432–434`; `Mathlib/Algebra/MvPolynomial/CommRing.lean:159–164`). This establishes the intended difference on all real vector assignments, including the arbitrary replacement vectors permitted at `app-local-operator.tex:168–170`.

The `Fin 20 × Fin 3` indexing supplies twenty vector labels with three coordinates each. Active group leaders and retained corner second slots are distinct; all other labels are unused. Keeping these dummy variables gives the same polynomial as the paper's list of k remaining vectors, including a constant if that list is empty. It adds no realizability condition or restriction to unit vectors. Both representations are available. The consuming real interfaces supply `π.Covered` and `0 < c < 1` (`AKLT/Blueprint/Top/Operator.lean:156–167,183–197`), so defining the function on raw patterns and all real thresholds does not broaden the asserted paper results. There are no hidden finiteness hypotheses, natural-number subtractions, or variable denominators in the target definition. The rational constants used in reconstruction have nonzero denominators.

Non-blocking remarks: None affecting fidelity. The complete source file and its project-local import closure were read. An exact-arithmetic Python check passed all 242 ordered-coordinate-word/status moment comparisons through degree four and all 16 current/next passage polynomial identities across the eight neighbour-presence masks. No Lean processes were launched, and the inputs were not modified.
