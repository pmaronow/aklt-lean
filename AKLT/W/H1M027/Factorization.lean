import AKLT.W.H1M027.Factors

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M027

theorem leaf_product (π : PatternData) (r : Representation)
    (hGeometry : PeripheralGeometry π r) (m : Fin 20 → UnitVector)
    (A : {x // x ∈ deletedLeafSites π r} → ℝ)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3)
    (hfactor : ∀ x n, normSq (n (leafNeighbour π x.1)) ≤ 1 →
      integratedLeafFactor π m x.1 n = A x *
        (if patternDegree π x.1 = 0 then 1 else
          1 + (replacementRadius π x.1 : ℝ) * dot (v x) (n (leafNeighbour π x.1))))
    (n : Plane → Vec3) (hn : ∀ x, normSq (n x) ≤ 1) :
    (∏ x ∈ deletedLeafSites π r, integratedLeafFactor π m x n) =
      (∏ x : {x // x ∈ deletedLeafSites π r}, A x) *
        ∏ x ∈ templateCorners ∪ templateTips, leafRemainder π r v n x := by
  classical
  calc
    _ = ∏ x : {x // x ∈ deletedLeafSites π r},
        A x * leafRemainder π r v n x.1 := by
      rw [← Finset.prod_coe_sort]
      apply Finset.prod_congr rfl
      intro x hx
      simpa [leafRemainder, x.property] using hfactor x n (hn _)
    _ = (∏ x : {x // x ∈ deletedLeafSites π r}, A x) *
        ∏ x : {x // x ∈ deletedLeafSites π r}, leafRemainder π r v n x.1 :=
      Finset.prod_mul_distrib
    _ = (∏ x : {x // x ∈ deletedLeafSites π r}, A x) *
        ∏ x ∈ deletedLeafSites π r, leafRemainder π r v n x := by
      rw [Finset.prod_coe_sort]
    _ = _ := by
      congr 1
      apply Finset.prod_subset
      · intro x hx
        exact (hGeometry x hx).1
      · intro x hx hd
        simp [leafRemainder, hd]

theorem retained_leaf_product (π : PatternData) (r : Representation)
    (hGeometry : PeripheralGeometry π r) (m : Fin 20 → UnitVector)
    (A : {x // x ∈ deletedLeafSites π r} → ℝ)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3)
    (hfactor : ∀ x n, normSq (n (leafNeighbour π x.1)) ≤ 1 →
      integratedLeafFactor π m x.1 n = A x *
        (if patternDegree π x.1 = 0 then 1 else
          1 + (replacementRadius π x.1 : ℝ) * dot (v x) (n (leafNeighbour π x.1))))
    (next : Bool) (n : Plane → Vec3) (hn : ∀ x, normSq (n x) ≤ 1) :
    retainedOriginalFactors π r next m n *
        (∏ x ∈ deletedLeafSites π r, integratedLeafFactor π m x n) =
      (∏ x : {x // x ∈ deletedLeafSites π r}, A x) *
        localEvaluation (reducedIntegrand π r next) n (assignedVectors π r m v) := by
  classical
  have hgroups :
      (∏ x ∈ templateCorners ∪ templateTips,
        (if x ∈ reducedSpinSites π r then coveredSiteField m x (n x) else 1) *
          leafRemainder π r v n x) =
      ∏ x ∈ reductionGroups π, groupFactor π r (assignedVectors π r m v) n x := by
    calc
      _ = ∏ x ∈ templateCorners ∪ templateTips,
          if 0 < patternDegree π x then
            groupFactor π r (assignedVectors π r m v) n x else 1 := by
        exact Finset.prod_congr rfl (fun x hx => peripheral_factor π r m v n hx)
      _ = _ := (Finset.prod_filter _ _).symm
  rw [leaf_product π r hGeometry m A v hfactor n hn,
    retainedOriginalFactors, retained_field_product, evaluate_reducedIntegrand,
    ← hgroups, Finset.prod_mul_distrib]
  ring

/-- The positive scalar and vector assignment are fixed before `next` is
chosen. Only the atom norm hypothesis is needed at the surviving spins. -/
theorem separated_factorization
    (hIco : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (π : PatternData) (r : Representation) (hGeometry : PeripheralGeometry π r)
    (m : Fin 20 → UnitVector)
    (A : {x // x ∈ deletedLeafSites π r} → ℝ)
    (v : {x // x ∈ deletedLeafSites π r} → Vec3)
    (hfactor : ∀ x n, normSq (n (leafNeighbour π x.1)) ≤ 1 →
      integratedLeafFactor π m x.1 n = A x *
        (if patternDegree π x.1 = 0 then 1 else
          1 + (replacementRadius π x.1 : ℝ) * dot (v x) (n (leafNeighbour π x.1))))
    (next : Bool) :
    separatedLeafFunctional π r next m =
      (∏ x : {x // x ∈ deletedLeafSites π r}, A x) *
        rawFunctional (reducedSpinSites π r) (nextStatus π next)
          (reducedIntegrand π r next) (assignedVectors π r m v) := by
  classical
  unfold separatedLeafFunctional rawFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_assoc, retained_leaf_product π r hGeometry m A v hfactor next
    (supportSpins (reducedSpinSites π r) n) (supportSpins_ball hIco _ n)]
  ring

end AKLT.W.H1M027
