import CertData.H3.Kernel.Rows

namespace AKLT.W.H3C056
open AKLT.Defs AKLT.Cert.H3
set_option maxRecDepth 2048
set_option maxHeartbeats 2000000

theorem powerset_two_singleton {α : Type*} (a : α) :
    Finset.powersetCard 2 {a} = ∅ := by simp

theorem powerset_two_empty {α : Type*} : Finset.powersetCard 2 (∅ : Finset α) = ∅ := by simp

theorem powerset_two_pair {α : Type*} [DecidableEq α] (a b : α) (h : a ≠ b) :
    Finset.powersetCard 2 {a,b} = {{a,b}} := by
  simpa [h] using Finset.powersetCard_self ({a,b} : Finset α)

theorem diagonal_ceiling (φ : Phase) (k : StepKind) :
    coefficientCeiling (phaseDiagonal φ k) = diagonal φ k := by
  cases φ <;> cases k <;>
    norm_num [coefficientCeiling, certificateCoefficientScale, phaseDiagonal, diagonal,
      qs, qt, q3, q5, passageFactor, localThreshold]

@[simp] theorem ceiling_zero : coefficientCeiling 0 = 0 := by
  norm_num [coefficientCeiling]

theorem ceiling_fifth : coefficientCeiling ((1:ℚ)/5) = q5 := by
  norm_num [coefficientCeiling, certificateCoefficientScale, q5]

/-- The sixty admitted direction/dead-neighbour entries, rounded only after
summing the exact rational response reward. -/
theorem response_ceiling (incoming outgoing : Compass) (j : Fin 5)
    (h : outgoing ≠ incoming.reverse) :
    coefficientCeiling (passageFactor (decide (outgoing=incoming)) *
      relaxedReward (0,0) incoming outgoing
        (if j.val<4 then {(direction j.val).step} else ∅) / 3) =
      response (directionCode incoming) (directionCode outgoing) j.val := by
  cases incoming <;> cases outgoing <;> simp only [Compass.reverse] at h <;> try contradiction
  all_goals fin_cases j
  all_goals
    norm_num [coefficientCeiling, certificateCoefficientScale, passageFactor, localThreshold,
      relaxedReward, neighbours, Compass.step, responsePairType, kernelWitness,
      alphaBound, betaBound, betaPrimeBound, response, responseTable, direction, directionCode,
      show (Finset.univ : Finset Compass) = {.east,.north,.west,.south} from rfl,
      Finset.erase_insert, Finset.erase_insert_of_ne, Finset.powersetCard_succ_insert,
      Finset.powersetCard_one, powerset_two_singleton, powerset_two_empty,
      powerset_two_pair, Finset.sdiff_singleton_eq_erase] <;>
    (try simp (disch := decide +kernel) only [Finset.sum_insert, Finset.sum_singleton]) <;>
    norm_num [Finset.mem_insert, Finset.mem_singleton, responsePairType]

end AKLT.W.H3C056
