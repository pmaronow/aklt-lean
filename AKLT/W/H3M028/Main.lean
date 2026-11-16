import AKLT.Blueprint.H3.NodesKernel

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.H3

namespace AKLT.W.H3M028

private theorem exposureSum_finset_linear {ι : Type}
    {n : ℕ} (w : DirectionWord n) (S : Finset ι) (c : ι → ℚ)
    (r : ι → Fin n → ℚ) (l : List (Fin n)) :
    exposureSum w (fun i => ∑ a ∈ S, c a * r a i) l =
      ∑ a ∈ S, c a * exposureSum w (r a) l := by
  induction l with
  | nil => simp [exposureSum]
  | cons i rest ih =>
      simp only [exposureSum]
      rw [ih]
      calc
        passageFactor (wordStraight kernelIncoming w i) *
            ((∑ a ∈ S, c a * r a i) +
              ∑ a ∈ S, c a * exposureSum w (r a) rest) =
            ∑ a ∈ S, passageFactor (wordStraight kernelIncoming w i) *
              (c a * r a i + c a * exposureSum w (r a) rest) := by
          calc
            _ = passageFactor (wordStraight kernelIncoming w i) *
                  (∑ a ∈ S, c a * r a i) +
                passageFactor (wordStraight kernelIncoming w i) *
                  (∑ a ∈ S, c a * exposureSum w (r a) rest) := by ring
            _ = (∑ a ∈ S, passageFactor (wordStraight kernelIncoming w i) *
                    (c a * r a i)) +
                ∑ a ∈ S, passageFactor (wordStraight kernelIncoming w i) *
                    (c a * exposureSum w (r a) rest) := by
              rw [Finset.mul_sum, Finset.mul_sum]
            _ = ∑ a ∈ S, (passageFactor (wordStraight kernelIncoming w i) *
                  (c a * r a i) + passageFactor (wordStraight kernelIncoming w i) *
                  (c a * exposureSum w (r a) rest)) := by
              rw [← Finset.sum_add_distrib]
            _ = _ := by
              apply Finset.sum_congr rfl
              intro a ha
              ring
        _ = ∑ a ∈ S, c a *
              (passageFactor (wordStraight kernelIncoming w i) *
                (r a i + exposureSum w (r a) rest)) := by
          apply Finset.sum_congr rfl
          intro a ha
          ring

private theorem pairShift_mem_lengthShifts {n : ℕ} (X : PairType)
    (w : DirectionWord n) (i : Fin n) (p : Finset Plane)
    (hp : p ∈ responsePairs w i) : pairShift X p ∈ lengthShifts X n := by
  classical
  unfold lengthShifts
  simp only [Finset.mem_biUnion]
  refine ⟨w, Finset.mem_univ w, ?_⟩
  refine ⟨i, Finset.mem_univ i, ?_⟩
  simp only [Finset.mem_image]
  exact ⟨p, hp, rfl⟩

private theorem sum_response_type_shift_word {n : ℕ} (L : Finset ℕ)
    (f : PairType → ℕ → DirectionWord n → ℚ) :
    (∑ Y : PairType, ∑ s ∈ L, ∑ w : DirectionWord n, f Y s w) =
      ∑ w : DirectionWord n, ∑ Y : PairType, ∑ s ∈ L, f Y s w := by
  calc
    (∑ Y : PairType, ∑ s ∈ L, ∑ w : DirectionWord n, f Y s w) =
        ∑ Y : PairType, ∑ w : DirectionWord n, ∑ s ∈ L, f Y s w := by
      apply Finset.sum_congr rfl
      intro Y hY
      exact Finset.sum_comm
    _ = ∑ w : DirectionWord n, ∑ Y : PairType, ∑ s ∈ L, f Y s w := by
      exact Finset.sum_comm

private theorem responseKappa_partition {n : ℕ} (X : PairType)
    (w : DirectionWord n) (i : Fin n) :
    ∑ Y : PairType, ∑ s ∈ lengthShifts X n,
      kernelWitness Y * responseKappa X Y s w i = witnessKappa w i := by
  classical
  unfold witnessKappa responseKappa
  calc
    (∑ Y : PairType, ∑ s ∈ lengthShifts X n,
        kernelWitness Y *
          ∑ p ∈ responsePairs w i,
            (if responsePairType p = Y ∧ pairShift X p = s then
              pairCoefficient w i p else 0)) =
        ∑ Y : PairType, ∑ s ∈ lengthShifts X n, ∑ p ∈ responsePairs w i,
          (if responsePairType p = Y ∧ pairShift X p = s then
            pairCoefficient w i p else 0) * kernelWitness Y := by
      apply Finset.sum_congr rfl
      intro Y hY
      apply Finset.sum_congr rfl
      intro s hs
      calc
        kernelWitness Y *
            ∑ p ∈ responsePairs w i,
              (if responsePairType p = Y ∧ pairShift X p = s then
                pairCoefficient w i p else 0) =
            ∑ p ∈ responsePairs w i, kernelWitness Y *
              (if responsePairType p = Y ∧ pairShift X p = s then
                pairCoefficient w i p else 0) :=
          Finset.mul_sum (responsePairs w i)
            (fun p => if responsePairType p = Y ∧ pairShift X p = s then
              pairCoefficient w i p else 0) (kernelWitness Y)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro p hp
          ring
    _ = ∑ Y : PairType, ∑ p ∈ responsePairs w i, ∑ s ∈ lengthShifts X n,
          (if responsePairType p = Y ∧ pairShift X p = s then pairCoefficient w i p else 0) *
            kernelWitness Y := by
      apply Finset.sum_congr rfl
      intro Y hY
      exact Finset.sum_comm
    _ = ∑ p ∈ responsePairs w i, ∑ Y : PairType, ∑ s ∈ lengthShifts X n,
          (if responsePairType p = Y ∧ pairShift X p = s then pairCoefficient w i p else 0) *
            kernelWitness Y := by
      exact Finset.sum_comm
    _ = ∑ p ∈ responsePairs w i,
          pairCoefficient w i p * kernelWitness (responsePairType p) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hs := pairShift_mem_lengthShifts X w i p hp
      let Y₀ := responsePairType p
      let s₀ := pairShift X p
      let c₀ := pairCoefficient w i p
      let G : PairType → ℚ := fun Y => ∑ s ∈ lengthShifts X n,
        (if Y₀ = Y ∧ s₀ = s then c₀ else 0) * kernelWitness Y
      have hsingle : (∑ Y : PairType, G Y) = G Y₀ := by
        apply Finset.sum_eq_single Y₀
        · intro Y hmem hne
          have hneq : ¬ Y₀ = Y := fun heq => hne heq.symm
          apply Finset.sum_eq_zero
          intro s hs
          simp [hneq]
        · simp
      calc
        (∑ Y : PairType, ∑ s ∈ lengthShifts X n,
            (if responsePairType p = Y ∧ pairShift X p = s then
              pairCoefficient w i p else 0) * kernelWitness Y) =
            G Y₀ := by
          change (∑ Y : PairType, G Y) = G Y₀
          exact hsingle
        _ = ∑ s ∈ lengthShifts X n,
              (if s₀ = s then c₀ else 0) * kernelWitness Y₀ := by
          simp [G]
        _ = (∑ s ∈ lengthShifts X n, if s₀ = s then c₀ else 0) *
              kernelWitness Y₀ :=
          (Finset.sum_mul (lengthShifts X n)
            (fun s => if s₀ = s then c₀ else 0) (kernelWitness Y₀)).symm
        _ = c₀ * kernelWitness Y₀ := by
          rw [Finset.sum_ite_eq (lengthShifts X n) s₀ (fun _ => c₀), if_pos hs]
        _ = pairCoefficient w i p * kernelWitness (responsePairType p) := rfl

private theorem weighted_exposure_partition {n : ℕ} (X : PairType)
    (w : DirectionWord n) :
    (∑ Y : PairType, ∑ s ∈ lengthShifts X n,
      kernelWitness Y * exposureSum w (responseKappa X Y s w) (kernelOrdering w)) =
        exposureSum w (witnessKappa w) (kernelOrdering w) := by
  classical
  let S : Finset (PairType × ℕ) := Finset.univ ×ˢ lengthShifts X n
  have hagg : (fun i : Fin n =>
      ∑ a ∈ S, kernelWitness a.1 * responseKappa X a.1 a.2 w i) =
        (fun i => witnessKappa w i) := by
    funext i
    change (∑ a ∈ Finset.univ ×ˢ lengthShifts X n,
      kernelWitness a.1 * responseKappa X a.1 a.2 w i) = witnessKappa w i
    calc
      (∑ a ∈ Finset.univ ×ˢ lengthShifts X n,
          kernelWitness a.1 * responseKappa X a.1 a.2 w i) =
        ∑ Y : PairType, ∑ s ∈ lengthShifts X n,
          kernelWitness Y * responseKappa X Y s w i :=
          Finset.sum_product' Finset.univ (lengthShifts X n)
            (fun Y s => kernelWitness Y * responseKappa X Y s w i)
      _ = witnessKappa w i := responseKappa_partition X w i
  have hlin := exposureSum_finset_linear w S
    (fun a => kernelWitness a.1) (fun a i => responseKappa X a.1 a.2 w i)
    (kernelOrdering w)
  calc
    (∑ Y : PairType, ∑ s ∈ lengthShifts X n,
        kernelWitness Y * exposureSum w (responseKappa X Y s w) (kernelOrdering w)) =
        ∑ a ∈ S, kernelWitness a.1 *
          exposureSum w (responseKappa X a.1 a.2 w) (kernelOrdering w) := by
      change (∑ Y : PairType, ∑ s ∈ lengthShifts X n,
        kernelWitness Y * exposureSum w (responseKappa X Y s w) (kernelOrdering w)) =
        ∑ a ∈ Finset.univ ×ˢ lengthShifts X n, kernelWitness a.1 *
          exposureSum w (responseKappa X a.1 a.2 w) (kernelOrdering w)
      exact (Finset.sum_product' Finset.univ (lengthShifts X n)
        (fun Y s => kernelWitness Y *
          exposureSum w (responseKappa X Y s w) (kernelOrdering w))).symm
    _ = exposureSum w (fun i =>
          ∑ a ∈ S, kernelWitness a.1 * responseKappa X a.1 a.2 w i)
          (kernelOrdering w) := hlin.symm
    _ = exposureSum w (witnessKappa w) (kernelOrdering w) := by rw [hagg]

end AKLT.W.H3M028

namespace AKLT.W.H3M028

theorem main : AKLT.Blueprint.H3.LengthRewardPartitionStatement := by
  intro X n
  classical
  unfold kernelLengthRow
  symm
  calc
    (∑ Y : PairType, ∑ s ∈ lengthShifts X n,
        kernelLengthCoefficient X Y s n * kernelWitness Y) =
        ∑ w : DirectionWord n, ∑ Y : PairType, ∑ s ∈ lengthShifts X n,
          (if ClosedTrail X w then
            trailBaseWeight kernelStart w * exposureSum w (responseKappa X Y s w)
              (kernelOrdering w) else 0) * kernelWitness Y := by
      unfold kernelLengthCoefficient
      simp_rw [Finset.sum_mul]
      exact sum_response_type_shift_word (lengthShifts X n) (fun Y s w =>
        (if ClosedTrail X w then
          trailBaseWeight kernelStart w * exposureSum w (responseKappa X Y s w)
            (kernelOrdering w) else 0) * kernelWitness Y)
    _ = ∑ w : DirectionWord n, if ClosedTrail X w then closedContribution w else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      by_cases hclosed : ClosedTrail X w
      · simp only [if_pos hclosed, closedContribution]
        calc
          (∑ Y : PairType, ∑ s ∈ lengthShifts X n,
              (trailBaseWeight kernelStart w *
                exposureSum w (responseKappa X Y s w) (kernelOrdering w)) * kernelWitness Y) =
              trailBaseWeight kernelStart w *
                (∑ Y : PairType, ∑ s ∈ lengthShifts X n,
                  kernelWitness Y * exposureSum w (responseKappa X Y s w) (kernelOrdering w)) := by
            calc
              _ = ∑ Y : PairType, ∑ s ∈ lengthShifts X n,
                    trailBaseWeight kernelStart w *
                      (kernelWitness Y * exposureSum w (responseKappa X Y s w) (kernelOrdering w)) := by
                apply Finset.sum_congr rfl
                intro Y hY
                apply Finset.sum_congr rfl
                intro s hs
                ring
              _ = trailBaseWeight kernelStart w *
                    (∑ Y : PairType, ∑ s ∈ lengthShifts X n,
                      kernelWitness Y * exposureSum w (responseKappa X Y s w)
                        (kernelOrdering w)) := by
                calc
                  _ = ∑ Y : PairType, trailBaseWeight kernelStart w *
                        (∑ s ∈ lengthShifts X n,
                          kernelWitness Y * exposureSum w (responseKappa X Y s w)
                            (kernelOrdering w)) := by
                    apply Finset.sum_congr rfl
                    intro Y hY
                    rw [← Finset.mul_sum]
                  _ = _ := by rw [← Finset.mul_sum]
          _ = trailBaseWeight kernelStart w *
                exposureSum w (witnessKappa w) (kernelOrdering w) := by
            rw [weighted_exposure_partition]
      · simp [hclosed]

end AKLT.W.H3M028
