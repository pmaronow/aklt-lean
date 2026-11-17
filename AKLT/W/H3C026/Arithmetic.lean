module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

set_option maxHeartbeats 4000000

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Gen.Packed

namespace AKLT.W.H3C026

theorem diagonal_ceiling (φ : Phase) (k : StepKind) :
    coefficientCeiling (phaseDiagonal φ k) = diagonal φ k := by
  cases φ <;> cases k <;>
    norm_num [coefficientCeiling, certificateCoefficientScale, phaseDiagonal,
      passageFactor, localThreshold, diagonal, qs, qt, q3, q5]

theorem fifth_ceiling : coefficientCeiling ((1 : ℚ) / 5) = q5 := by
  norm_num [coefficientCeiling, certificateCoefficientScale, q5]

theorem zero_ceiling : coefficientCeiling 0 = 0 := by
  norm_num [coefficientCeiling]

private theorem compass_univ : (Finset.univ : Finset Compass) =
    {.east, .north, .west, .south} := rfl

private theorem plane_zero : (0 : Plane) = (0,0) := rfl

private theorem pairs_singleton (x : Plane) : ({x} : Finset Plane).powersetCard 2 = ∅ :=
  Finset.powersetCard_eq_empty.mpr (by simp)

private theorem pairs_empty : (∅ : Finset Plane).powersetCard 2 = ∅ :=
  Finset.powersetCard_eq_empty.mpr (by simp)

private theorem pair_eq_pair (a b c d : Plane) :
    ({a,b} : Finset Plane) = {c,d} ↔ (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  constructor
  · intro h
    have ha : a=c ∨ a=d := by
      have : a ∈ ({c,d} : Finset Plane) := by rw [←h]; simp
      simpa using this
    have hb : b=c ∨ b=d := by
      have : b ∈ ({c,d} : Finset Plane) := by rw [←h]; simp
      simpa using this
    have hc : c=a ∨ c=b := by
      have : c ∈ ({a,b} : Finset Plane) := by rw [h]; simp
      simpa using this
    have hd : d=a ∨ d=b := by
      have : d ∈ ({a,b} : Finset Plane) := by rw [h]; simp
      simpa using this
    grind
  · rintro (⟨rfl,rfl⟩ | ⟨rfl,rfl⟩) <;> simp [Finset.pair_comm]

/-- Each near-center response entry is the ceiling of the complete exact
response sum, with the sum taken before rounding. -/
theorem near_response_ceiling (ain d : Compass) (j : Fin 4)
    (hr : d ≠ ain.reverse) :
    coefficientCeiling (passageFactor (decide (d=ain)) *
      relaxedReward (-(direction j.val).step) ain d {kernelCentre} / 3) =
      response (directionCode ain) (directionCode d) j.val := by
  fin_cases j <;> cases ain <;> cases d <;> norm_num [Compass.reverse] at hr <;>
    norm_num [relaxedReward, neighbours, compass_univ, Compass.step, Compass.reverse,
      responsePairType, kernelWitness, betaPrimeBound, betaBound, alphaBound,
      kernelCentre, coefficientCeiling, certificateCoefficientScale,
      passageFactor, localThreshold, response, responseTable, direction, directionCode,
      Finset.powersetCard_succ_insert, Finset.powersetCard_zero,
      Finset.powersetCard_one, Finset.erase_insert, Finset.erase_singleton,
      Finset.erase_insert_of_ne, Finset.sdiff_singleton_eq_erase, Prod.mk.injEq,
      pairs_singleton, pairs_empty, pair_eq_pair, plane_zero] <;>
    simp only [plane_zero] <;>
    norm_num [relaxedReward, neighbours, compass_univ, Compass.step, Compass.reverse,
      responsePairType, kernelWitness, betaPrimeBound, betaBound, alphaBound,
      kernelCentre, coefficientCeiling, certificateCoefficientScale,
      passageFactor, localThreshold, response, responseTable, direction, directionCode,
      Finset.powersetCard_succ_insert, Finset.powersetCard_zero,
      Finset.powersetCard_one, Finset.erase_insert, Finset.erase_singleton,
      Finset.erase_insert_of_ne, Finset.sdiff_singleton_eq_erase, Prod.mk.injEq,
      pairs_singleton, pairs_empty, pair_eq_pair, plane_zero]

theorem far_response_ceiling (ain d : Compass) (hr : d ≠ ain.reverse) :
    coefficientCeiling (passageFactor (decide (d=ain)) *
      relaxedReward (0,0) ain d ∅ / 3) =
      response (directionCode ain) (directionCode d) 4 := by
  cases ain <;> cases d <;> norm_num [Compass.reverse] at hr <;>
    norm_num [relaxedReward, neighbours, compass_univ, Compass.step, Compass.reverse,
      responsePairType, kernelWitness, betaPrimeBound, betaBound, alphaBound,
      kernelCentre, coefficientCeiling, certificateCoefficientScale,
      passageFactor, localThreshold, response, responseTable, direction, directionCode,
      Finset.powersetCard_succ_insert, Finset.powersetCard_zero,
      Finset.powersetCard_one, Finset.erase_insert, Finset.erase_singleton,
      Finset.erase_insert_of_ne, Finset.sdiff_singleton_eq_erase, Prod.mk.injEq,
      pairs_singleton, pairs_empty, pair_eq_pair, plane_zero]

end AKLT.W.H3C026

#print axioms AKLT.W.H3C026.diagonal_ceiling
#print axioms AKLT.W.H3C026.fifth_ceiling
#print axioms AKLT.W.H3C026.zero_ceiling
#print axioms AKLT.W.H3C026.near_response_ceiling
#print axioms AKLT.W.H3C026.far_response_ceiling
