module
public import AKLT.Blueprint.H1.NodesStructure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ComplexOrder
open AKLT.Defs
open AKLT.Blueprint.H1

namespace AKLT.W.H1M055

theorem main : AKLT.Blueprint.H1.PairExpansionTransferStatement := by
  intro J j k O unitOnly hExpansion hSupport hExchange
  rcases hExpansion with ⟨t, η, hη, w, n, H, hNorm, hAux, hO⟩
  let P := symmetricPairProjection J j k
  let X := exchangeOperator J j k
  constructor
  · intro hu
    rw [hO]
    symm
    calc
      P * (∑ a, w a • (pairTerm J j k η (n a) * H a)) * P =
          ∑ a, P * (w a • (pairTerm J j k η (n a) * H a)) * P := by
            simp only [Finset.mul_sum, Finset.sum_mul]
      _ = ∑ a, w a • (pairTerm J j k η (n a) * H a) := by
        apply Finset.sum_congr rfl
        intro a ha
        have hPair := hSupport η hη (n a) ((hNorm a).2 hu)
        have hPairP : P * pairTerm J j k η (n a) = pairTerm J j k η (n a) := by
          simpa [P] using hPair.1
        have hPairRight : pairTerm J j k η (n a) * P = pairTerm J j k η (n a) := by
          simpa [P] using hPair.2
        have hAuxP : H a * P = P * H a := by
          exact (hAux a).2.eq
        calc
          P * (w a • (pairTerm J j k η (n a) * H a)) * P =
              w a • (P * (pairTerm J j k η (n a) * H a) * P) := by
                simp only [mul_smul_comm, smul_mul_assoc]
          _ = w a • (pairTerm J j k η (n a) * H a) := by
            congr 1
            calc
              P * (pairTerm J j k η (n a) * H a) * P =
                  (P * pairTerm J j k η (n a)) * (H a * P) := by
                    simp [mul_assoc]
              _ = pairTerm J j k η (n a) * (H a * P) := by rw [hPairP]
              _ = pairTerm J j k η (n a) * (P * H a) := by rw [hAuxP]
              _ = (pairTerm J j k η (n a) * P) * H a := by rw [← mul_assoc]
              _ = pairTerm J j k η (n a) * H a := by rw [hPairRight]
  · rw [hO]
    change
      (∑ a, w a • (pairTerm J j k η (n a) * H a)) * X =
        X * (∑ a, w a • (pairTerm J j k η (n a) * H a))
    simp only [Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    have hPairX := hExchange η (n a)
    have hPairEq : pairTerm J j k η (n a) * X = X * pairTerm J j k η (n a) := hPairX.eq
    have hAuxX : H a * X = X * H a := (hAux a).1.eq
    calc
      (w a • (pairTerm J j k η (n a) * H a)) * X =
          w a • ((pairTerm J j k η (n a) * H a) * X) := by rw [smul_mul_assoc]
      _ = w a • (X * (pairTerm J j k η (n a) * H a)) := by
        congr 1
        calc
          (pairTerm J j k η (n a) * H a) * X =
              pairTerm J j k η (n a) * (H a * X) := by rw [← mul_assoc]
          _ = pairTerm J j k η (n a) * (X * H a) := by rw [hAuxX]
          _ = (pairTerm J j k η (n a) * X) * H a := by rw [mul_assoc]
          _ = (X * pairTerm J j k η (n a)) * H a := by rw [hPairEq]
          _ = X * (pairTerm J j k η (n a) * H a) := by rw [mul_assoc]
      _ = X * (w a • (pairTerm J j k η (n a) * H a)) := by rw [mul_smul_comm]

end AKLT.W.H1M055

end
