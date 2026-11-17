STATUS: PARTIAL

The requested unconditional theorem `AKLT.W.REC004.main : AKLT.Blueprint.Rec.RemovedMeanIntervalsStatement` is **not proved and is not declared**. The delivered, compiled replacement is

```lean
theorem AKLT.W.REC004.main_from_residuals
    (h : AKLT.W.REC004.Residual_FibreExpansion) :
    AKLT.Blueprint.Rec.RemovedMeanIntervalsStatement
```

This attempt replaces the earlier three unproved numerical residuals with one exact finite-sum residual. Free-pair positivity, the required one-site mean estimates, the three-neighbour geometry, product-fibre pair factorization, averaging, and all final rational interval arithmetic are now proved. The residual connecting the lattice partition to those product fibres remains open.

Files, all under the assigned directory:

| File | Content |
| --- | --- |
| [Main.lean](/home/ubuntu/aklt/wt/LW_REC004/AKLT/W/REC004/Main.lean) | Unconditional free comparison and conditional assembly of the frozen target. |
| [Algebra.lean](/home/ubuntu/aklt/wt/LW_REC004/AKLT/W/REC004/Algebra.lean) | Cauchy–Schwarz, three-vector pair bounds, finite quotient intervals including zero mass. |
| [Local.lean](/home/ubuntu/aklt/wt/LW_REC004/AKLT/W/REC004/Local.lean) | Explicit icosahedron calculation, scalar/vector triple formulas, unit-field sum-of-squares bound, zero fields, depleted-site contraction. |
| [Free.lean](/home/ubuntu/aklt/wt/LW_REC004/AKLT/W/REC004/Free.lean) | Sign-pair monomial positivity, natural-coefficient polynomial positivity, actual lattice free-pair positivity. |
| [Geometry.lean](/home/ubuntu/aklt/wt/LW_REC004/AKLT/W/REC004/Geometry.lean) | Nonadjacency, absence of original legs, survival and degree at most three after removal. |
| [Conditioning.lean](/home/ubuntu/aklt/wt/LW_REC004/AKLT/W/REC004/Conditioning.lean) | Explicit three-spin product sums and their pair moments. |
| [FibreExpansion.lean](/home/ubuntu/aklt/wt/LW_REC004/AKLT/W/REC004/FibreExpansion.lean) | The single closed residual and the complete averaging reduction. |
| [Audit.lean](/home/ubuntu/aklt/wt/LW_REC004/AKLT/W/REC004/Audit.lean) | `#check` for all 73 exported declarations and `#print axioms` for every one of the 65 exported theorems/lemmas. |

No existing statement, definition, library, or other leaf was edited. No sub-agents were used. The earlier report remains at [report.luna.md](/home/ubuntu/aklt/reports/LW/REC004/report.luna.md).

The full exported API, including every elaborated statement and its axiom output, is recorded in [declarations.log](/home/ubuntu/aklt/reports/LW/REC004/declarations.log). Principal declarations, all in `AKLT.W.REC004`, are:

```lean
removedPairMean_free_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (y f g : Plane) :
  0 ≤ removedPairMean D τ false y f g

free_response_comparison {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (y o f g : Plane) :
  1 ≤ responseJ D τ false y f g ∧
    responseJ D τ false y f g ≤ responseI D τ false y o f g

triple_normalizer (a : Fin 3 → Vec3) :
  siteFunctional .U (localProduct a) = 1 + localP a / 3

triple_numerator (a : Fin 3 → Vec3) (i : Fin 3) :
  15 * siteFunctional .U (fun v => v i * localProduct a v) = localV a i

atom_mean_bound (s : Status) (hs : s = .U ∨ s = .D)
    (a : Fin 3 → SpinLetter) :
  1 / 2 ≤ siteFunctional s (localProduct (fun j => spinVector (a j))) ∧
    normSq (localMean s (fun j => spinVector (a j))) ≤ (3 / 5 : ℝ)^2

triple_dot_bounds {u v w : Vec3}
    (hu : normSq u ≤ 9 / 25) (hv : normSq v ≤ 9 / 25)
    (hw : normSq w ≤ 9 / 25) :
  -(27 / 50 : ℝ) ≤ dot u v + dot u w + dot v w ∧
    dot u v + dot u w + dot v w ≤ 27 / 25

fibre_pair_eq (s : Fin 3 → Status)
    (hs : ∀ j, s j = .U ∨ s j = .D)
    (a : Fin 3 → Fin 3 → SpinLetter) (p q : Fin 3) (hpq : p ≠ q) :
  (∑ t : Fin 3 → SpinLetter, (∏ j, fibreDensity s a j (t j)) *
    dot (spinVector (t p)) (spinVector (t q))) =
  fibreMass s a * dot (fibreMean s a p) (fibreMean s a q)

neighbours_nonadjacent (y f g : Plane)
    (hf : Adjacent y f) (hg : Adjacent y g) : ¬ Adjacent f g

no_leg_at_neighbour {G : Finset Plane} {D : Network G} {y f : Plane}
    (hy : D.AdmissibleStart y) (hf : f ∈ D.presentNeighbours y) :
  ∀ e ∈ originalLegs G, e.1 ≠ f

neighbour_removed_card {G : Finset Plane} {D : Network G} {y f : Plane}
    (hD : D.Auxiliary) (hf : f ∈ D.presentNeighbours y) :
  ((removeSite D y).presentNeighbours f).card ≤ 3
```

`removed_pair_bounds_from_fibres` assumes only `Residual_FibreExpansion` in addition to the target's ordinary departure/neighbour hypotheses. For either pin flag it proves the single-pair interval `[-9/25, 9/25]` and the three-pair sum interval `[-27/50, 27/25]`. `main_from_residuals` converts these to the four requested I/J bounds and uses the unconditional free comparison for the remaining conjunction.

The sole open residual is the following transparent closed definition in `FibreExpansion.lean`:

```lean
def Residual_FibreExpansion : Prop :=
  ∀ a : AKLT.Blueprint.Rec.Departure, a.D.status a.y = .U →
    ∀ f g : Plane, a.D.presentNeighbours a.y = {a.o, f, g} →
    a.o ≠ f → a.o ≠ g → f ≠ g → ∀ b : Bool,
      ∃ (N : ℕ) (C : Fin N → ℝ) (s : Fin 3 → Status)
        (fields : Fin N → Fin 3 → Fin 3 → SpinLetter),
        (∀ r, 0 ≤ C r) ∧ (∀ j, s j = .U ∨ s j = .D) ∧
        ∀ F : (Fin 3 → Vec3) → ℝ,
          (removeSite a.D a.y).partition a.τ b
            (fun v => F ![v f, v g, v a.o]) =
          ∑ r, C r * ∑ t : Fin 3 → SpinLetter,
            (∏ j, fibreDensity s (fields r) j (t j)) *
              F (fun j => spinVector (t j))
```

Here `fibreDensity s fields j t` is `spinWeight (s j) t` times three factors `1 + dot (spinVector t) (spinVector (fields j k))`. A zero letter supplies a missing factor. The remaining proof must enumerate configurations of the other active spins, allocate all incident bond factors to the three selected neighbours, and collect the nonnegative off-site factors in `C`. The geometry needed to justify absence of mutual bonds, absence of original pins, and at most three incident factors is already proved in `Geometry.lean`. The actual product allocation and configuration reindexing have not been formalized.

Scope and limitations:

- The residual contains an exact unnormalized sum identity; it assumes no numerical response or mean bound. It isolates the combinatorial conditioning bridge rather than renaming the original inequalities.
- The local mean theorem treats unit or zero support fields, which are precisely the fields needed at these unpinned neighbours. It does not claim the broader arbitrary-ball-field blueprint leaf.
- Free positivity is proved directly on the actual active-site subtype using natural-coefficient polynomials. Sign pairing proves monomial positivity in every degree, so that part requires neither a degree-four restriction nor reindexing into `FiniteSpinNetwork`.
- Zero outside factors contribute zero. The averaging theorem also handles a zero total mass directly through real division by zero. No cancellation on a zero-mass fibre is used.
- No arbitrary-function rotational covariance is asserted. The universal test function in the residual expresses finite product factorization only.
- No optimized coefficient or logarithmic-mean statements are part of the frozen target and none are claimed here.

Axiom audit:

```text
'AKLT.W.REC004.main_from_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC004.free_response_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC004.atom_mean_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC004.removedPairMean_free_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.REC004.removed_pair_bounds_from_fibres' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 65 exported theorems/lemmas were audited, and every dependency set is a subset of the permitted three axioms. The complete output is in `declarations.log` and [audit.log](/home/ubuntu/aklt/reports/LW/REC004/audit.log). A source scan of all eight delivered Lean files found no forbidden proof declarations or escape mechanisms.

Final validation:

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC004.Main` — succeeded without warnings; wall time **29.31 s**, including rebuilds of changed helpers. Main itself reported **3.9 s**. Output: [build.log](/home/ubuntu/aklt/reports/LW/REC004/build.log).
- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.REC004.Audit` — succeeded without warnings; wall time **9.13 s**. Audit output includes all statements and axiom checks.
- The exact unconditional-name check is not satisfied: `AKLT.W.REC004.main` remains absent. Successful compilation of the conditional reduction does not establish the leaf.

## ORCH-SUMMARY

- STATUS: PARTIAL; the exact requested `AKLT.W.REC004.main` is not declared.
- Delivered eight compiled files under `AKLT/W/REC004/`.
- `main_from_residuals : Residual_FibreExpansion → RemovedMeanIntervalsStatement`.
- Sole open residual: `AKLT.W.REC004.Residual_FibreExpansion`.
- Remaining work: explicit lattice configuration reindexing and allocation of factors into product fibres.
- Proved: support-field U/D mean bounds, exact triple formulas, fibre pair factorization and averaging.
- Proved: neighbour nonadjacency, no original legs, survival, and degree at most three after removal.
- Proved unconditionally: `removedPairMean_free_nonneg` and `free_response_comparison`.
- Free positivity uses direct active-site polynomial expansion and all-degree sign pairing.
- Local mean bounds cover support fields; the full arbitrary-ball-field leaf is not claimed.
- Zero masses are handled algebraically without cancellation.
- Main build: 29.31 s; audit build: 9.13 s; both succeeded without warnings.
- All 65 exported theorems/lemmas use only permitted axioms.
- No statement-layer edits, unproved axioms, forbidden mechanisms, or sub-agents.
- Orchestrator must finish the named residual before claiming REC004 proved.
