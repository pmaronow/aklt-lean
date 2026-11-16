import AKLT.W.H1M052.Expansion

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs AKLT.Blueprint.H1

namespace AKLT.W.H1M052

@[simp] theorem toEnd_sub {J : Finset (Fin 20)}
    (A B : Matrix (J → Fin 2) (J → Fin 2) ℂ) :
    toEnd (A - B) = toEnd A - toEnd B := Matrix.toEuclideanLin.map_sub A B

@[simp] theorem toEnd_smul {J : Finset (Fin 20)}
    (z : ℂ) (A : Matrix (J → Fin 2) (J → Fin 2) ℂ) :
    toEnd (z • A) = z • toEnd A := Matrix.toEuclideanLin.map_smul z A

def spinMass (π : PatternData) (r : Representation) (next : Bool)
    (a : reducedSpinSites π r → SpinLetter) : ℝ :=
  ∏ y : reducedSpinSites π r, spinWeight (nextStatus π next y.val) (a y)

def rawWeight (π : PatternData) (r : Representation) (next : Bool)
    (a : reducedSpinSites π r → SpinLetter) : ℝ :=
  spinMass π r next a * bondScalar π r next (supportSpins (reducedSpinSites π r) a)

def differenceWeight (π : PatternData) (r : Representation) (c : ℚ)
    (a : reducedSpinSites π r → SpinLetter) : ℂ :=
  (rawWeight π r false a : ℂ) - (c : ℂ) * (rawWeight π r true a : ℂ)

def rawAuxiliary (π : PatternData) (r : Representation) (I : Finset (Fin 20))
    (x : reductionGroups π) (h : groupIsPair π r x.val = true)
    (a : reducedSpinSites π r → SpinLetter) : Module.End ℂ (TensorSpace (reductionVectors π r)) :=
  toEnd (remainingTensor (leaderToken π r x) (secondToken π r x h)
    (summandMatrices π r I (supportSpins (reducedSpinSites π r) a)))

theorem rawPauli_tensor_sum (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (next : Bool) :
    rawPauliFunctional (reducedSpinSites π r) (nextStatus π next) (reductionVectors π r) I
        (reducedIntegrand π r next) =
      ∑ a : reducedSpinSites π r → SpinLetter,
        (rawWeight π r next a : ℂ) • tensorMatrix (reductionVectors π r)
          (summandMatrices π r I (supportSpins (reducedSpinSites π r) a)) := by
  unfold rawPauliFunctional
  apply Finset.sum_congr rfl
  intro a _
  rw [integrand_pauli_tensor, smul_smul]
  simp only [rawWeight, spinMass, Complex.ofReal_mul]
  rfl

theorem rawEnd_pair_sum (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true) (next : Bool) :
    toEnd (rawPauliFunctional (reducedSpinSites π r) (nextStatus π next) (reductionVectors π r) I
        (reducedIntegrand π r next)) =
      ∑ a : reducedSpinSites π r → SpinLetter,
        (rawWeight π r next a : ℂ) •
          (pairTerm (reductionVectors π r) (leaderToken π r x) (secondToken π r x h)
            (inversionSign I (groupLeader x.val))
            (supportSpins (reducedSpinSites π r) a x.val) * rawAuxiliary π r I x h a) := by
  rw [rawPauli_tensor_sum]
  simp only [toEnd, map_sum, map_smul]
  apply Finset.sum_congr rfl
  intro a _
  exact congrArg (fun T => (rawWeight π r next a : ℂ) • T)
    (summand_factor_pair π r I hI x h (supportSpins (reducedSpinSites π r) a))

theorem spinMass_zero_at_U (π : PatternData) (r : Representation)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true)
    (hU : π.statusAt x.val = .U) (next : Bool)
    (a : reducedSpinSites π r → SpinLetter)
    (ha : a ⟨x.val, pair_retained π r x h⟩ = none) : spinMass π r next a = 0 := by
  classical
  apply Finset.prod_eq_zero (i := ⟨x.val, pair_retained π r x h⟩) (Finset.mem_univ _)
  simp [nextStatus, pair_ne_origin π r x.val h, hU, ha, spinWeight]

theorem rawDifference_pairExpansion
    (hNorm : ∀ j : IcoLetter, normSq (icoVector j) = 1)
    (π : PatternData) (r : Representation) (I : Finset (Fin 20))
    (hI : GroupInversion π r I) (c : ℚ)
    (x : reductionGroups π) (h : groupIsPair π r x.val = true) :
    PairExpansion (reductionVectors π r) (leaderToken π r x) (secondToken π r x h)
      (toEnd (rawPauliFunctional (reducedSpinSites π r) (nextStatus π false)
          (reductionVectors π r) I (reducedIntegrand π r false) -
        (c : ℂ) • rawPauliFunctional (reducedSpinSites π r) (nextStatus π true)
          (reductionVectors π r) I (reducedIntegrand π r true)))
      (π.statusAt x.val = .U) := by
  classical
  have hsum :
      toEnd (rawPauliFunctional (reducedSpinSites π r) (nextStatus π false)
          (reductionVectors π r) I (reducedIntegrand π r false) -
        (c : ℂ) • rawPauliFunctional (reducedSpinSites π r) (nextStatus π true)
          (reductionVectors π r) I (reducedIntegrand π r true)) =
      ∑ a : reducedSpinSites π r → SpinLetter,
        differenceWeight π r c a •
          (pairTerm (reductionVectors π r) (leaderToken π r x) (secondToken π r x h)
            (inversionSign I (groupLeader x.val))
            (supportSpins (reducedSpinSites π r) a x.val) * rawAuxiliary π r I x h a) := by
    rw [toEnd_sub, toEnd_smul]
    rw [rawEnd_pair_sum π r I hI x h false, rawEnd_pair_sum π r I hI x h true]
    simp only [differenceWeight, Finset.smul_sum, smul_smul, ← Finset.sum_sub_distrib,
      sub_smul]
  rw [hsum]
  apply pairExpansion_of_sum _ _ _ _ (inversionSign_sq I (groupLeader x.val))
  · intro a
    have hspin : supportSpins (reducedSpinSites π r) a x.val =
        spinVector (a ⟨x.val, pair_retained π r x h⟩) := by
      simp [supportSpins, pair_retained π r x h]
    rw [hspin]
    refine ⟨spinVector_norm hNorm _, ?_⟩
    intro hU hw
    cases ha : a ⟨x.val, pair_retained π r x h⟩ with
    | none =>
      exfalso
      apply hw
      have hzero (next : Bool) := spinMass_zero_at_U π r x h hU next a ha
      simp [differenceWeight, rawWeight, hzero]
    | some j => exact hNorm j
  · intro a
    exact remainingTensor_commute _ _ _

end AKLT.W.H1M052
