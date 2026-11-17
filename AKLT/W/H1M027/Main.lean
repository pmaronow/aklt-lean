module
public import AKLT.W.H1M027.Factorization

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs

namespace AKLT.W.H1M027

open AKLT.Blueprint.H1

/-- The local content of the assignment step: every deleted leaf has a positive
normalizer and, in the one-bond case, a replacement vector in the unit ball.
The choice is made before either next value is considered. -/
theorem deletedLeafChoices
    (π : PatternData) (r : Representation) (m : Fin 20 → UnitVector)
    (hGeometry : PeripheralGeometry π r) (hRule : LeafRule π m) :
    ∃ A : {x // x ∈ deletedLeafSites π r} → ℝ,
    ∃ v : {x // x ∈ deletedLeafSites π r} → Vec3,
      (∀ x, 0 < A x) ∧
      (∀ x, normSq (v x) ≤ 1) ∧
      (∀ x n, normSq (n (leafNeighbour π x.1)) ≤ 1 →
        integratedLeafFactor π m x.1 n = A x *
        (if patternDegree π x.1 = 0 then 1 else
          1 + (replacementRadius π x.1 : ℝ) * dot (v x) (n (leafNeighbour π x.1)))) := by
  classical
  let D := {x // x ∈ deletedLeafSites π r}
  have hlocal : ∀ x : D, ∃ p : ℝ × Vec3,
      0 < p.1 ∧ normSq p.2 ≤ 1 ∧
      ∀ n, normSq (n (leafNeighbour π x.1)) ≤ 1 →
        integratedLeafFactor π m x.1 n = p.1 *
        (if patternDegree π x.1 = 0 then 1 else
          1 + (replacementRadius π x.1 : ℝ) * dot p.2 (n (leafNeighbour π x.1))) := by
    intro x
    have hx := hGeometry x.1 x.2
    have hactive : x.1 ∈ π.active := by
      exact (Finset.mem_sdiff.mp x.2).1
    have hnotX : π.statusAt x.1 ≠ .X := (Finset.mem_filter.mp hactive).2
    have hdeg := hx.2.1
    have hperiph := hx.1
    rcases Nat.eq_zero_or_pos (patternDegree π x.1) with hzero | hpos
    · refine ⟨(siteFunctional (π.statusAt x.1) (coveredSiteField m x.1), 0), ?_, ?_, ?_⟩
      · exact (hRule x.1 hperiph hnotX).1 hzero
      · simp [normSq, dot]
      · intro n _
        simp [integratedLeafFactor, hzero]
    · have hone : patternDegree π x.1 = 1 := by omega
      obtain ⟨A, hA, u, hu, hfactor⟩ :=
        (hRule x.1 hperiph hnotX).2 hone
      refine ⟨(A, u), hA, hu, ?_⟩
      intro n hn
      simpa [integratedLeafFactor, hone] using hfactor (n (leafNeighbour π x.1)) hn
  choose p hp using hlocal
  refine ⟨fun x => (p x).1, fun x => (p x).2, ?_, ?_, ?_⟩
  · intro x
    exact (hp x).1
  · intro x
    exact (hp x).2.1
  · intro x n hn
    exact (hp x).2.2 n hn

/-- A common positive product of local normalizers and a common ball-valued
assignment reconstruct the separated functional for both values of `next`. -/
theorem main : AKLT.Blueprint.H1.PeripheralAssignmentStatement := by
  classical
  intro hIco π _hπ r hGeometry m hRule
  obtain ⟨A, v, hA, hv, hfactor⟩ := deletedLeafChoices π r m hGeometry hRule
  refine ⟨∏ x : {x // x ∈ deletedLeafSites π r}, A x, ?_,
    assignedVectors π r m v, assignedVectors_ball π r m v hv, ?_⟩
  · apply Finset.prod_pos
    intro x hx
    exact hA x
  · exact separated_factorization hIco π r hGeometry m A v hfactor

#print axioms deletedLeafChoices
#print axioms main

end AKLT.W.H1M027
