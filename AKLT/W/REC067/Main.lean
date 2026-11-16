import AKLT.Blueprint.Rec.NodesKernel

set_option maxHeartbeats 100000

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC067

private def rowLength (X : PairType) (n : ℕ) : ℚ := by
  classical
  exact ∑ w : DirectionWord n, if ClosedTrail X w then closedContribution w else 0

private def rowShifts (X : PairType) (n : ℕ) : Finset ℕ := by
  classical
  exact Finset.univ.biUnion fun w : DirectionWord n =>
    Finset.univ.biUnion fun i : Fin n => (responsePairs w i).image (pairShift X)

private theorem pairCoefficient_nonneg {n : ℕ} (w : DirectionWord n) (i : Fin n)
    (p : Finset Plane) : 0 ≤ pairCoefficient w i p := by
  unfold pairCoefficient
  split_ifs <;> cases wordStraight kernelIncoming w i <;>
    norm_num [alphaBound, betaBound, betaPrimeBound]

private theorem witnessKappa_nonneg {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    0 ≤ witnessKappa w i := by
  unfold witnessKappa
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (pairCoefficient_nonneg w i p) (by
    cases responsePairType p <;> norm_num [kernelWitness])

private theorem responseKappa_nonneg {n : ℕ} (X Y : PairType) (s : ℕ)
    (w : DirectionWord n) (i : Fin n) : 0 ≤ responseKappa X Y s w i := by
  unfold responseKappa
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact pairCoefficient_nonneg w i p
  · exact le_rfl

private theorem exposureSum_nonneg {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ)
    (hr : ∀ i, 0 ≤ r i) (l : List (Fin n)) : 0 ≤ exposureSum w r l := by
  induction l with
  | nil => exact le_rfl
  | cons i l ih =>
    exact mul_nonneg (by
      have h : 0 < passageFactor (wordStraight kernelIncoming w i) := by
        cases wordStraight kernelIncoming w i <;> norm_num [passageFactor, localThreshold]
      exact h.le) (add_nonneg (hr i) ih)

private theorem kernelCoeff_nonneg (X Y : PairType) (s n : ℕ) :
    0 ≤ kernelLengthCoefficient X Y s n := by
  classical
  unfold kernelLengthCoefficient
  apply Finset.sum_nonneg
  intro w hw
  split_ifs with hc
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro i hi
      split_ifs <;> norm_num
    · exact exposureSum_nonneg w _ (responseKappa_nonneg X Y s w) _
  · exact le_rfl

private theorem rowLength_nonneg (X : PairType) (n : ℕ) : 0 ≤ rowLength X n := by
  classical
  unfold rowLength
  apply Finset.sum_nonneg
  intro w hw
  split_ifs with hc
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro i hi
      split_ifs <;> norm_num
    · exact exposureSum_nonneg w _ (fun i => witnessKappa_nonneg w i) _
  · exact le_rfl

private theorem responseKappa_eq_zero_of_not_shift {n : ℕ} (X Y : PairType)
    (w : DirectionWord n) (i : Fin n) (s : ℕ)
    (hs : ∀ p ∈ responsePairs w i, pairShift X p ≠ s) :
    responseKappa X Y s w i = 0 := by
  unfold responseKappa
  apply Finset.sum_eq_zero
  intro p hp
  simp only [ite_eq_right_iff]
  intro h
  exact ((hs p hp) h.2).elim

private theorem exposureSum_zero {n : ℕ} (w : DirectionWord n) (l : List (Fin n))
    (r : Fin n → ℚ) (hr : ∀ i, r i = 0) : exposureSum w r l = 0 := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp [exposureSum, hr i, ih]

private theorem kernelCoeff_zero_outside (X Y : PairType) (n s : ℕ)
    (hs : s ∉ rowShifts X n) : kernelLengthCoefficient X Y s n = 0 := by
  classical
  unfold kernelLengthCoefficient
  apply Finset.sum_eq_zero
  intro w hw
  have hlocal : ∀ i : Fin n, ∀ p ∈ responsePairs w i, pairShift X p ≠ s := by
    intro i p hp heq
    apply hs
    have hin : s ∈ rowShifts X n := by
      simp only [rowShifts, Finset.mem_biUnion]
      refine ⟨w, Finset.mem_univ w, i, Finset.mem_univ i, ?_⟩
      exact Finset.mem_image.mpr ⟨p, hp, heq⟩
    exact hin
  have hz : ∀ i : Fin n, responseKappa X Y s w i = 0 := by
    intro i
    exact responseKappa_eq_zero_of_not_shift X Y w i s (hlocal i)
  by_cases hc : ClosedTrail X w
  · simp [hc, exposureSum_zero w (kernelOrdering w) _ hz]
  · simp [hc]

private theorem exposureSum_finset_sum {α : Type} {n : ℕ} (w : DirectionWord n)
    (t : Finset α) (r : α → Fin n → ℚ) (l : List (Fin n)) :
    (∑ a ∈ t, exposureSum w (r a) l) =
      exposureSum w (fun i => ∑ a ∈ t, r a i) l := by
  induction l with
  | nil => simp [exposureSum]
  | cons i l ih =>
    simp only [exposureSum, mul_add, Finset.sum_add_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum, ih]

private theorem exposureSum_mul {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ)
    (l : List (Fin n)) (c : ℚ) :
    exposureSum w (fun i => r i * c) l = exposureSum w r l * c := by
  induction l with
  | nil => simp [exposureSum]
  | cons i l ih =>
    simp only [exposureSum]
    rw [ih]
    ring

private theorem responseTotal_eq_witness {n : ℕ} (X : PairType) (S : Finset ℕ)
    (w : DirectionWord n) (i : Fin n)
    (hS : ∀ p ∈ responsePairs w i, pairShift X p ∈ S) :
    (∑ Y : PairType, ∑ s ∈ S,
      responseKappa X Y s w i * kernelWitness Y) = witnessKappa w i := by
  classical
  let g : Finset Plane → PairType × ℕ := fun p => (responsePairType p, pairShift X p)
  let f : Finset Plane → ℚ := fun p => pairCoefficient w i p * kernelWitness (responsePairType p)
  let k : PairType × ℕ → ℚ := fun q => responseKappa X q.1 q.2 w i * kernelWitness q.1
  calc
    (∑ Y : PairType, ∑ s ∈ S,
      responseKappa X Y s w i * kernelWitness Y) =
        ∑ q ∈ Finset.univ.product S,
          ∑ p ∈ responsePairs w i with g p = q, f p := by
      change Finset.univ.sum (fun Y : PairType => S.sum (fun s => k (Y, s))) = _
      rw [← Finset.sum_product]
      apply Finset.sum_congr rfl
      intro q hq
      rcases q with ⟨Y, s⟩
      change responseKappa X Y s w i * kernelWitness Y = _
      rw [Finset.sum_filter]
      unfold responseKappa
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      by_cases h : responsePairType p = Y ∧ pairShift X p = s
      · simp [h, g, f]
      · simp [h, g, f]
    _ = ∑ p ∈ responsePairs w i with g p ∈ Finset.univ.product S, f p :=
      Finset.sum_fiberwise_eq_sum_filter (responsePairs w i) (Finset.univ.product S) g f
    _ = ∑ p ∈ responsePairs w i, f p := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      simp [g, hS p hp]
    _ = witnessKappa w i := by simp [witnessKappa, f]

private theorem sum3_swap {α β γ : Type} [Fintype α] [Fintype γ]
    (S : Finset β) (f : α → β → γ → ℚ) :
    (∑ a : α, ∑ b ∈ S, ∑ c : γ, f a b c) =
      ∑ c : γ, ∑ a : α, ∑ b ∈ S, f a b c := by
  calc
    (∑ a : α, ∑ b ∈ S, ∑ c : γ, f a b c) =
        ∑ a : α, ∑ c : γ, ∑ b ∈ S, f a b c := by
      apply Finset.sum_congr rfl
      intro a ha
      exact Finset.sum_comm
    _ = ∑ c : γ, ∑ a : α, ∑ b ∈ S, f a b c := Finset.sum_comm

private theorem rowLength_eq_coeff_sum (X : PairType) (n : ℕ) :
    rowLength X n = ∑ Y : PairType, ∑ s ∈ rowShifts X n,
      kernelLengthCoefficient X Y s n * kernelWitness Y := by
  classical
  let S := rowShifts X n
  have hS : ∀ (w : DirectionWord n) (i : Fin n) (p : Finset Plane),
      p ∈ responsePairs w i → pairShift X p ∈ S := by
    intro w i p hp
    simp [S, rowShifts]
    exact ⟨w, i, p, hp, rfl⟩
  have hExp : ∀ w : DirectionWord n,
      (∑ Y : PairType, ∑ s ∈ S,
        exposureSum w (fun i => responseKappa X Y s w i * kernelWitness Y)
          (kernelOrdering w)) =
        exposureSum w (fun i => witnessKappa w i) (kernelOrdering w) := by
    intro w
    calc
      (∑ Y : PairType, ∑ s ∈ S,
        exposureSum w (fun i => responseKappa X Y s w i * kernelWitness Y)
          (kernelOrdering w)) =
        ∑ Y : PairType, exposureSum w (fun i => ∑ s ∈ S,
          responseKappa X Y s w i * kernelWitness Y) (kernelOrdering w) := by
            apply Finset.sum_congr rfl
            intro Y hY
            exact exposureSum_finset_sum w S
              (fun s i => responseKappa X Y s w i * kernelWitness Y) _
      _ = exposureSum w (fun i => ∑ Y : PairType, ∑ s ∈ S,
          responseKappa X Y s w i * kernelWitness Y) (kernelOrdering w) := by
            exact exposureSum_finset_sum w Finset.univ
              (fun Y i => ∑ s ∈ S, responseKappa X Y s w i * kernelWitness Y) _
      _ = exposureSum w (fun i => witnessKappa w i) (kernelOrdering w) := by
            apply congrArg (fun r : Fin n → ℚ => exposureSum w r (kernelOrdering w))
            funext i
            exact responseTotal_eq_witness X S w i (hS w i)
  have hword : ∀ w : DirectionWord n,
      (∑ Y : PairType, ∑ s ∈ S,
        (if ClosedTrail X w then
          trailBaseWeight kernelStart w *
            exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w)
          else 0) * kernelWitness Y) =
        (if ClosedTrail X w then closedContribution w else 0) := by
    intro w
    by_cases hc : ClosedTrail X w
    · simp [hc]
      calc
        (∑ Y : PairType, ∑ s ∈ S,
          (trailBaseWeight kernelStart w *
            exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w)) *
              kernelWitness Y) =
          ∑ Y : PairType, ∑ s ∈ S,
            trailBaseWeight kernelStart w *
              (exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) *
                kernelWitness Y) := by
                  apply Finset.sum_congr rfl
                  intro Y hY
                  apply Finset.sum_congr rfl
                  intro s hs
                  ring
        _ = ∑ Y : PairType, trailBaseWeight kernelStart w *
              (∑ s ∈ S,
                exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) *
                  kernelWitness Y) := by
                  apply Finset.sum_congr rfl
                  intro Y hY
                  rw [← Finset.mul_sum]
        _ = trailBaseWeight kernelStart w *
              (∑ Y : PairType, ∑ s ∈ S,
                exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) *
                  kernelWitness Y) := by rw [← Finset.mul_sum]
        _ = closedContribution w := by
          have hscale : (∑ Y : PairType, ∑ s ∈ S,
              exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) *
                kernelWitness Y) =
              ∑ Y : PairType, ∑ s ∈ S,
                exposureSum w (fun i => responseKappa X Y s w i * kernelWitness Y)
                  (kernelOrdering w) := by
            apply Finset.sum_congr rfl
            intro Y hY
            apply Finset.sum_congr rfl
            intro s hs
            exact (exposureSum_mul w (fun i => responseKappa X Y s w i)
              (kernelOrdering w) (kernelWitness Y)).symm
          rw [hscale, hExp w]
          rfl
    · simp [hc]
  calc
    rowLength X n = ∑ Y : PairType, ∑ s ∈ S,
        kernelLengthCoefficient X Y s n * kernelWitness Y := by
      unfold rowLength
      simp only [kernelLengthCoefficient, Finset.sum_mul]
      rw [sum3_swap S (fun Y s w =>
        (if ClosedTrail X w then
          trailBaseWeight kernelStart w *
            exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w)
          else 0) * kernelWitness Y)]
      apply Finset.sum_congr rfl
      intro w hw
      exact (hword w).symm
    _ = ∑ Y : PairType, ∑ s ∈ rowShifts X n,
        kernelLengthCoefficient X Y s n * kernelWitness Y := by rfl

private theorem rowEntry_eq (X : PairType) (n : ℕ) :
    (∑ Y : PairType, ∑' s : ℕ,
      ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
        ENNReal.ofReal (witnessReal Y)) = ENNReal.ofReal (rowLength X n : ℝ) := by
  classical
  let S := rowShifts X n
  have htsum : ∀ Y : PairType,
      (∑' s : ℕ, ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
        ENNReal.ofReal (witnessReal Y)) =
      ∑ s ∈ S, ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
        ENNReal.ofReal (witnessReal Y) := by
    intro Y
    apply tsum_eq_sum
    intro s hs
    simp [kernelCoeff_zero_outside X Y n s hs]
  have hreal : (rowLength X n : ℝ) =
      ∑ Y : PairType, ∑ s ∈ S,
        (kernelLengthCoefficient X Y s n : ℝ) * (kernelWitness Y : ℝ) := by
    exact_mod_cast rowLength_eq_coeff_sum X n
  calc
    (∑ Y : PairType, ∑' s : ℕ,
      ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
        ENNReal.ofReal (witnessReal Y)) =
      ∑ Y : PairType, ∑ s ∈ S,
        ENNReal.ofReal ((kernelLengthCoefficient X Y s n : ℝ) *
          (kernelWitness Y : ℝ)) := by
            apply Finset.sum_congr rfl
            intro Y hY
            rw [htsum Y]
            apply Finset.sum_congr rfl
            intro s hs
            rw [← ENNReal.ofReal_mul]
            · simp [witnessReal]
            · exact_mod_cast kernelCoeff_nonneg X Y s n
    _ = ∑ Y : PairType, ENNReal.ofReal
          (∑ s ∈ S, (kernelLengthCoefficient X Y s n : ℝ) *
            (kernelWitness Y : ℝ)) := by
            apply Finset.sum_congr rfl
            intro Y hY
            exact (ENNReal.ofReal_sum_of_nonneg (s := S) (f := fun s =>
              (kernelLengthCoefficient X Y s n : ℝ) * (kernelWitness Y : ℝ))
              (by
                intro s hs
                exact mul_nonneg (by exact_mod_cast kernelCoeff_nonneg X Y s n)
                  (by cases Y <;> norm_num [kernelWitness]))).symm
    _ = ENNReal.ofReal (∑ Y : PairType, ∑ s ∈ S,
          (kernelLengthCoefficient X Y s n : ℝ) * (kernelWitness Y : ℝ)) := by
            exact (ENNReal.ofReal_sum_of_nonneg (s := Finset.univ) (f := fun Y =>
              ∑ s ∈ S, (kernelLengthCoefficient X Y s n : ℝ) * (kernelWitness Y : ℝ))
              (by
                intro Y hY
                apply Finset.sum_nonneg
                intro s hs
                exact mul_nonneg (by exact_mod_cast kernelCoeff_nonneg X Y s n)
                  (by cases Y <;> norm_num [kernelWitness]))).symm
    _ = ENNReal.ofReal (rowLength X n : ℝ) := by rw [hreal.symm]

private theorem weightedShifted_eq_tsum_row (X : PairType) :
    (∑ Y : PairType,
      shiftedKernel 1 X Y * ENNReal.ofReal (witnessReal Y)) =
      ∑' n : ℕ, ENNReal.ofReal (rowLength X n : ℝ) := by
  calc
    (∑ Y : PairType,
      shiftedKernel 1 X Y * ENNReal.ofReal (witnessReal Y)) =
      ∑ Y : PairType,
        (∑' s : ℕ, ∑' n : ℕ,
          ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ)) *
            ENNReal.ofReal (witnessReal Y) := by
              apply Finset.sum_congr rfl
              intro Y hY
              simp [shiftedKernel, shiftKernel]
    _ = ∑ Y : PairType, ∑' s : ℕ,
          (∑' n : ℕ, ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ)) *
            ENNReal.ofReal (witnessReal Y) := by
              apply Finset.sum_congr rfl
              intro Y hY
              exact ENNReal.tsum_mul_right.symm
    _ = ∑ Y : PairType, ∑' s : ℕ, ∑' n : ℕ,
          ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
            ENNReal.ofReal (witnessReal Y) := by
              apply Finset.sum_congr rfl
              intro Y hY
              apply tsum_congr
              intro s
              exact ENNReal.tsum_mul_right.symm
    _ = ∑ Y : PairType, ∑' n : ℕ, ∑' s : ℕ,
          ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
            ENNReal.ofReal (witnessReal Y) := by
              apply Finset.sum_congr rfl
              intro Y hY
              exact ENNReal.tsum_comm
    _ = ∑' n : ℕ, ∑ Y : PairType, ∑' s : ℕ,
          ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
            ENNReal.ofReal (witnessReal Y) := by
              calc
                (∑ Y : PairType, ∑' n : ℕ, ∑' s : ℕ,
                  ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
                    ENNReal.ofReal (witnessReal Y)) =
                    ∑' Y : PairType, ∑' n : ℕ, ∑' s : ℕ,
                      ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
                        ENNReal.ofReal (witnessReal Y) := (tsum_fintype _).symm
                _ = ∑' n : ℕ, ∑' Y : PairType, ∑' s : ℕ,
                      ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
                        ENNReal.ofReal (witnessReal Y) := ENNReal.tsum_comm
                _ = ∑' n : ℕ, ∑ Y : PairType, ∑' s : ℕ,
                      ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
                        ENNReal.ofReal (witnessReal Y) := by
                          apply tsum_congr
                          intro n
                          exact tsum_fintype _
    _ = ∑' n : ℕ, ENNReal.ofReal (rowLength X n : ℝ) := by
          apply tsum_congr
          intro n
          exact rowEntry_eq X n

private theorem rowLength_zero (X : PairType) : rowLength X 0 = 0 := by
  classical
  have hn : ∀ w : DirectionWord 0, ¬ ClosedTrail X w := by
    intro w hw
    have heq := hw.2.1
    cases X <;> norm_num [wordVertex, kernelStart, kernelTarget] at heq
  simp [rowLength, hn]

private theorem finiteRowBound (hH3 : AKLT.Blueprint.Top.H3Statement) (X : PairType) (R : ℕ) :
    (∑ n ∈ Finset.Icc 1 R, ENNReal.ofReal (rowLength X n : ℝ)) ≤
      ENNReal.ofReal ((kernelRho * kernelWitness X : ℚ) : ℝ) := by
  have hq : (∑ n ∈ Finset.Icc 1 R, rowLength X n) ≤ kernelRho * kernelWitness X := by
    simpa [kernelPartialRow, rowLength] using hH3 X R
  have hr : (∑ n ∈ Finset.Icc 1 R, (rowLength X n : ℝ)) ≤
      ((kernelRho * kernelWitness X : ℚ) : ℝ) := by exact_mod_cast hq
  calc
    (∑ n ∈ Finset.Icc 1 R, ENNReal.ofReal (rowLength X n : ℝ)) =
        ENNReal.ofReal (∑ n ∈ Finset.Icc 1 R, (rowLength X n : ℝ)) := by
          exact (ENNReal.ofReal_sum_of_nonneg (s := Finset.Icc 1 R)
            (f := fun n => (rowLength X n : ℝ)) (by
              intro n hn
              exact_mod_cast rowLength_nonneg X n)).symm
    _ ≤ ENNReal.ofReal ((kernelRho * kernelWitness X : ℚ) : ℝ) :=
          ENNReal.ofReal_le_ofReal hr

private theorem fullRowBound (hH3 : AKLT.Blueprint.Top.H3Statement) (X : PairType) :
    (∑' n : ℕ, ENNReal.ofReal (rowLength X n : ℝ)) ≤
      ENNReal.ofReal ((kernelRho * kernelWitness X : ℚ) : ℝ) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro N
  let f : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (rowLength X n : ℝ)
  have hsubset : Finset.range N ⊆ insert 0 (Finset.Icc 1 N) := by
    intro n hn
    simp only [Finset.mem_range] at hn
    simp only [Finset.mem_insert, Finset.mem_Icc]
    by_cases hz : n = 0
    · exact Or.inl hz
    · exact Or.inr ⟨by omega, by omega⟩
  have hzero : f 0 = 0 := by simp [f, rowLength_zero]
  have hinsert : (∑ n ∈ insert 0 (Finset.Icc 1 N), f n) =
      ∑ n ∈ Finset.Icc 1 N, f n := by
    rw [Finset.sum_insert (by simp)]
    simp [f, hzero]
  calc
    (∑ n ∈ Finset.range N, f n) ≤ ∑ n ∈ insert 0 (Finset.Icc 1 N), f n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro n hn hnot
        exact bot_le)
    _ = ∑ n ∈ Finset.Icc 1 N, f n := hinsert
    _ ≤ ENNReal.ofReal ((kernelRho * kernelWitness X : ℚ) : ℝ) := finiteRowBound hH3 X N

theorem main : AKLT.Blueprint.Rec.UnshiftedWitnessStatement := by
  intro hH3 X
  rw [weightedShifted_eq_tsum_row X]
  simpa [witnessReal] using fullRowBound hH3 X

#print axioms main

end AKLT.W.REC067

