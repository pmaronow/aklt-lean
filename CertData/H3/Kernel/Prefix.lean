import CertData.H3.Kernel.Automaton
import CertData.H3.Kernel.View

namespace AKLT.Cert.H3
open AKLT.Defs

instance trailDecidable {n : Nat} (w : DirectionWord n) : Decidable (IsTrail kernelStart kernelIncoming w) := by
  unfold IsTrail Function.Injective
  infer_instance
instance firstDecidable {n : Nat} (w : DirectionWord n) (d : Compass) : Decidable (FirstDirection w d) := by
  unfold FirstDirection
  infer_instance
instance survivingDecidable {n : Nat} (X : PairType) (d : Compass) (w : DirectionWord n) :
    Decidable (SurvivingPrefix X d w) := by unfold SurvivingPrefix; infer_instance
instance closedDecidable {n : Nat} (X : PairType) (w : DirectionWord n) : Decidable (ClosedTrail X w) := by
  unfold ClosedTrail
  infer_instance

/-- Subset of the Defs prefix sum indexed by a specified, injective frontier family. -/
noncomputable def prefixShard {I : Type*} [Fintype I] (Q : MemoryQuotient 10 3741) (C : StationaryData 3741)
    (X : PairType) (d₀ : Compass) (words : I → DirectionWord 12) : ℚ :=
  ∑ i : I, if SurvivingPrefix X d₀ (words i) then
    ∑ φ : Phase, prefixPhases (words i) φ *
      C.potential φ (Q.project (lastWindowWord 10 (words i))) (wordVertex kernelStart (words i) 12) else 0

/-- Integer dot products can be added before the single division. -/
theorem integer_table_sum {I : Type*} [Fintype I] (valid : I → Bool)
    (p v : I → Phase → Nat) (D V : Nat) :
    (∑ i : I, if valid i then ∑ φ : Phase, ((p i φ : ℚ) / D) * ((v i φ : ℚ) / V) else 0) =
      ((∑ i : I, if valid i then ∑ φ : Phase, p i φ * v i φ else 0 : Nat) : ℚ) / ((D : ℚ) * V) := by
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_mul]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro φ _
    exact div_mul_div_comm _ _ _ _
  · simp

#print axioms integer_table_sum
end AKLT.Cert.H3
