STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP046/AKLT/W/GAP046/Main.lean:12) proves the requested leaf.
- [TraceHelpers.lean](/home/ubuntu/aklt/wt/LW_GAP046/AKLT/W/GAP046/TraceHelpers.lean:1) contains the finite trace and endpoint lemmas.

## Exported declarations and statements

```lean
AKLT.W.GAP046.main : AKLT.Blueprint.Gap.TraceMarginalsStatement

traceLaw_probability {X} [Fintype X] (m : ℕ)
  (initial : Weight (X × X)) (K : Fin m → X × X → Weight (X × X))
  (hinitial : Probability initial) (hK : ∀ j ω, Probability (K j ω)) :
  Probability (traceLaw m initial K)

traceEndpoint {X} [Fintype X] [DecidableEq (X × X)] (m : ℕ)
  (initial : Weight (X × X)) (K : Fin m → X × X → Weight (X × X)) :
  Weight (X × X)

marginal_probability {A B} [Fintype A] [Fintype B] [DecidableEq B]
  (p : Weight A) (hp : Probability p) (r : A → B) :
  Probability (marginal p r)

traceEndpoint_probability {X} [Fintype X] [DecidableEq (X × X)] (m : ℕ)
  (initial : Weight (X × X)) (K : Fin m → X × X → Weight (X × X))
  (hp : Probability (traceLaw m initial K)) :
  Probability (traceEndpoint m initial K)

traceEndpoint_coupling {Ω} [Fintype Ω] [DecidableEq (Ω × Ω)] (m : ℕ)
  (initial : Weight (Ω × Ω)) (K : Fin m → Ω × Ω → Weight (Ω × Ω))
  (p q : Weight Ω) (hprob : Probability (traceLaw m initial K))
  (hmarg : (∀ x, ∑ y, traceEndpoint m initial K (x, y) = p x) ∧
           ∀ y, ∑ x, traceEndpoint m initial K (x, y) = q y) :
  ∃ c : Coupling p q, ∀ x y,
    c.mass x y = marginal (traceLaw m initial K) (fun t => t (Fin.last m)) (x, y)

independentPairProbability {Ω} [Fintype Ω] (p q : Weight Ω)
  (hp : Probability p) (hq : Probability q) :
  Probability (independentPairs p q)

surgeryTrace_endpoint_marginals (P : PlaneSpec) (a y : Plane)
  (u l h : ℕ) (p α : ℝ) (η ξ : Config P.Letter)
  (R : SurgeryKernels P a y u l h p α η ξ)
  [DecidableEq (PlaneConfig P (square a u) × PlaneConfig P (square a u))]
  (hμpos : PositiveProbability (P.law (square a u) η))
  (hνpos : PositiveProbability (P.law (square a u) ξ)) :
  (∀ σ, ∑ τ, traceEndpoint h
    (independentPairs (P.law (square a u) η) (P.law (square a u) ξ)) R.kernel (σ, τ) =
      P.law (square a u) η σ) ∧
  ∀ τ, ∑ σ, traceEndpoint h
    (independentPairs (P.law (square a u) η) (P.law (square a u) ξ)) R.kernel (σ, τ) =
      P.law (square a u) ξ τ

surgeryTrace_eq_traceLaw (P : PlaneSpec) (a y : Plane)
  (u l h : ℕ) (p α : ℝ) (η ξ : Config P.Letter)
  (R : SurgeryKernels P a y u l h p α η ξ) :
  surgeryTrace P a y u l h p α η ξ R =
    traceLaw h (independentPairs (P.law (square a u) η) (P.law (square a u) ξ)) R.kernel
```

The endpoint marginals are proved by induction on the number of rows. At each step, conditional-fibre mixing preserves both marginals; an exceptional skip row is the identity kernel. The product initial law supplies the two initial marginals, and the final coupling uses the endpoint distribution itself.

## Axioms

`#print axioms` was run on every exported theorem above (excluding `traceEndpoint`, which is a definition). Every theorem reports exactly:

```text
[propext, Classical.choice, Quot.sound]
```

## Build

- `lake build AKLT.W.GAP046.TraceHelpers` — passed (6.6 s for the helper module on its final build).
- `lake build AKLT.W.GAP046.Main` — passed (11.28 s on the full build; final cached rerun 5.69 s).
- The temporary axiom-check module compiled in 5.24 s and was removed.

The helper module emits only non-fatal deprecation and unused-tactic/simp-argument warnings. No frozen files were changed. No residual statements or open proof obligations remain.

## ORCH-SUMMARY

- Delivered `AKLT.W.GAP046.main` with the exact requested type.
- Added `AKLT/W/GAP046/TraceHelpers.lean` for finite trace normalization and endpoint marginal preservation.
- Build passed with `lake build AKLT.W.GAP046.Main`.
- Exported theorem axioms are limited to `propext`, `Classical.choice`, and `Quot.sound`.
- No open issues or orchestrator decisions remain.
