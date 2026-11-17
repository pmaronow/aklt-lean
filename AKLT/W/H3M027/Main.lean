module
public import AKLT.Blueprint.H3.NodesKernel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.W.H3M027

private theorem pairShift_mem_lengthShifts {X : PairType} {n : ℕ}
    (w : DirectionWord n) (i : Fin n) (p : Finset Plane)
    (hp : p ∈ responsePairs w i) :
    pairShift X p ∈ AKLT.Blueprint.H3.lengthShifts X n := by
  classical
  unfold AKLT.Blueprint.H3.lengthShifts
  exact Finset.mem_biUnion.mpr ⟨w, Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
      Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩⟩

private theorem responseKappa_eq_zero_of_not_mem {X Y : PairType} {n s : ℕ}
    (w : DirectionWord n) (i : Fin n)
    (hs : s ∉ AKLT.Blueprint.H3.lengthShifts X n) :
    responseKappa X Y s w i = 0 := by
  classical
  unfold responseKappa
  apply Finset.sum_eq_zero
  intro p hp
  have hmem := pairShift_mem_lengthShifts (X := X) w i p hp
  have hne : pairShift X p ≠ s := by
    intro heq
    exact hs (heq ▸ hmem)
  simp [hne]

private theorem exposureSum_responseKappa_eq_zero {X Y : PairType} {n s : ℕ}
    (w : DirectionWord n)
    (hs : s ∉ AKLT.Blueprint.H3.lengthShifts X n) :
    exposureSum w (responseKappa X Y s w) (kernelOrdering w) = 0 := by
  have hz : ∀ i : Fin n, responseKappa X Y s w i = 0 := fun i =>
    responseKappa_eq_zero_of_not_mem w i hs
  induction kernelOrdering w with
  | nil => rfl
  | cons i rest ih => simp [exposureSum, hz i, ih]

private theorem kernelLengthCoefficient_eq_zero_of_not_mem
    (X Y : PairType) (n s : ℕ)
    (hs : s ∉ AKLT.Blueprint.H3.lengthShifts X n) :
    kernelLengthCoefficient X Y s n = 0 := by
  classical
  unfold kernelLengthCoefficient
  apply Finset.sum_eq_zero
  intro w hw
  by_cases hc : ClosedTrail X w
  · have hz := exposureSum_responseKappa_eq_zero (X := X) (Y := Y) (s := s) w hs
    simp [hc, hz]
  · simp [hc]

theorem main : AKLT.Blueprint.H3.LengthShiftSupportStatement := by
  intro X Y n s hs
  exact kernelLengthCoefficient_eq_zero_of_not_mem X Y n s hs

end AKLT.W.H3M027

#print axioms AKLT.W.H3M027.main
