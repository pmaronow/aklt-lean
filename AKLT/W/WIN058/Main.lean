import AKLT.Blueprint.Win.NodesRemoval

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN058

open AKLT.Blueprint.Win

private theorem weighted_sum_sum {ι κ : Type*} [Fintype ι]
    (S : Finset κ) (w : ι → ℝ) (f : κ → ι → ℝ) :
    (∑ i, w i * ∑ k ∈ S, f k i) = ∑ k ∈ S, ∑ i, w i * f k i := by
  calc
    (∑ i, w i * ∑ k ∈ S, f k i) = ∑ i, ∑ k ∈ S, w i * f k i := by
      congr 1
      funext i
      rw [Finset.mul_sum]
    _ = ∑ k ∈ S, ∑ i, w i * f k i := Finset.sum_comm

private theorem subtype_prod_attach {α : Type*} (S : Finset α) (f : ↥S → ℝ) :
    (∏ x : S, f x) = ∏ x ∈ S.attach, f x := by
  rw [Finset.univ_eq_attach]

private theorem partSum_sum (pinned : Bool) (G Y : Finset Plane)
    (τ : PinAssignment G) (S : Finset Plane)
    (f : Plane → (Plane → Vec3) → ℝ) :
    partSum pinned G Y τ (fun n => ∑ z ∈ S, f z n) =
      ∑ z ∈ S, partSum pinned G Y τ (f z) := by
  classical
  unfold partSum
  by_cases hp : pinned
  · simp only [ite_eq_left hp]
    unfold pinnedSum
    dsimp
    let wt : (↥(G \ Y) → IcoLetter) → ℝ := fun n =>
      (1 / 12 : ℝ) ^ (G \ Y).card *
        (∏ e ∈ internalBonds (G \ Y),
          (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))) *
        ∏ e : originalLegs G,
          if e.val.1 ∈ G \ Y then 1 + dot (τ e).val (extendIcoSpins n e.val.1) else 1
    calc
      (∑ n, ((1 / 12 : ℝ) ^ (G \ Y).card *
          (∑ z ∈ S, f z (extendIcoSpins n)) *
          (∏ e ∈ internalBonds (G \ Y),
            (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))) *
          ∏ e : originalLegs G,
            if e.val.1 ∈ G \ Y then 1 + dot (τ e).val (extendIcoSpins n e.val.1) else 1))
        = ∑ n, wt n * ∑ z ∈ S, f z (extendIcoSpins n) := by
            apply Finset.sum_congr rfl
            intro n hn
            simp only [wt]
            ring_nf
      _ = ∑ z ∈ S, ∑ n, wt n * f z (extendIcoSpins n) := weighted_sum_sum S wt _
      _ = ∑ z ∈ S, pinnedSum G Y τ (f z) := by
            apply Finset.sum_congr rfl
            intro z hz
            unfold pinnedSum
            dsimp
            apply Finset.sum_congr rfl
            intro n hn
            simp only [wt]
            rw [subtype_prod_attach]
            ring_nf
  · simp only [ite_eq_right hp]
    unfold freeSum
    dsimp
    let wt : (↥(G \ Y) → IcoLetter) → ℝ := fun n =>
      (1 / 12 : ℝ) ^ (G \ Y).card *
        ∏ e ∈ internalBonds (G \ Y),
          (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))
    calc
      (∑ n, ((1 / 12 : ℝ) ^ (G \ Y).card *
          (∑ z ∈ S, f z (extendIcoSpins n)) *
          ∏ e ∈ internalBonds (G \ Y),
            (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))))
        = ∑ n, wt n * ∑ z ∈ S, f z (extendIcoSpins n) := by
            apply Finset.sum_congr rfl
            intro n hn
            simp only [wt]
            ring
      _ = ∑ z ∈ S, ∑ n, wt n * f z (extendIcoSpins n) := weighted_sum_sum S wt _
      _ = ∑ z ∈ S, freeSum G Y (f z) := by
            apply Finset.sum_congr rfl
            intro z hz
            unfold freeSum
            apply Finset.sum_congr rfl
            intro n hn
            simp only [wt]
            ring

private theorem partSum_smul (pinned : Bool) (G Y : Finset Plane)
    (τ : PinAssignment G) (c : ℝ) (f : (Plane → Vec3) → ℝ) :
    partSum pinned G Y τ (fun n => c * f n) =
      c * partSum pinned G Y τ f := by
  classical
  unfold partSum
  by_cases hp : pinned
  · simp only [ite_eq_left hp]
    unfold pinnedSum
    dsimp
    calc
      (∑ n, ((1 / 12 : ℝ) ^ (G \ Y).card * (c * f (extendIcoSpins n)) *
          (∏ e ∈ internalBonds (G \ Y),
            (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))) *
          ∏ e : originalLegs G,
            if e.val.1 ∈ G \ Y then 1 + dot (τ e).val (extendIcoSpins n e.val.1) else 1))
        = ∑ n, c * ((1 / 12 : ℝ) ^ (G \ Y).card * f (extendIcoSpins n) *
          (∏ e ∈ internalBonds (G \ Y),
            (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))) *
          ∏ e : originalLegs G,
            if e.val.1 ∈ G \ Y then 1 + dot (τ e).val (extendIcoSpins n e.val.1) else 1) := by
              apply Finset.sum_congr rfl
              intro n hn
              ring
      _ = c * ∑ n, ((1 / 12 : ℝ) ^ (G \ Y).card * f (extendIcoSpins n) *
          (∏ e ∈ internalBonds (G \ Y),
            (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))) *
          ∏ e : originalLegs G,
            if e.val.1 ∈ G \ Y then 1 + dot (τ e).val (extendIcoSpins n e.val.1) else 1) := by
              rw [← Finset.mul_sum]
  · simp only [ite_eq_right hp]
    unfold freeSum
    dsimp
    calc
      (∑ n, ((1 / 12 : ℝ) ^ (G \ Y).card * (c * f (extendIcoSpins n)) *
          ∏ e ∈ internalBonds (G \ Y),
            (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))) )
        = ∑ n, c * ((1 / 12 : ℝ) ^ (G \ Y).card * f (extendIcoSpins n) *
          ∏ e ∈ internalBonds (G \ Y),
            (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))) := by
              apply Finset.sum_congr rfl
              intro n hn
              ring
      _ = c * ∑ n, ((1 / 12 : ℝ) ^ (G \ Y).card * f (extendIcoSpins n) *
          ∏ e ∈ internalBonds (G \ Y),
            (1 + dot (extendIcoSpins n e.1) (extendIcoSpins n e.2))) := by
              rw [← Finset.mul_sum]

private theorem partMean_smul (pinned : Bool) (G Y : Finset Plane)
    (τ : PinAssignment G) (c : ℝ) (f : (Plane → Vec3) → ℝ) :
    partMean pinned G Y τ (fun n => c * f n) =
      c * partMean pinned G Y τ f := by
  unfold partMean
  rw [partSum_smul]
  ring

private theorem partMean_zero (pinned : Bool) (G Y : Finset Plane)
    (τ : PinAssignment G) :
    partMean pinned G Y τ (fun _ => 0) = 0 := by
  simpa using (partMean_smul pinned G Y τ (0 : ℝ) (fun _ => (1 : ℝ)))

private theorem partMean_sum (pinned : Bool) (G Y : Finset Plane)
    (τ : PinAssignment G) (S : Finset Plane)
    (f : Plane → (Plane → Vec3) → ℝ) :
    partMean pinned G Y τ (fun n => ∑ z ∈ S, f z n) =
      ∑ z ∈ S, partMean pinned G Y τ (f z) := by
  classical
  unfold partMean
  rw [partSum_sum]
  rw [Finset.sum_div]

private def pairTerm (v w : Plane) (n : Plane → Vec3) : ℝ :=
  if v = w then 0 else dot (n v) (n w)

private theorem partMean_pairSum (pinned : Bool) (G Y : Finset Plane)
    (τ : PinAssignment G) (V : Finset Plane) :
    partMean pinned G Y τ (pairSum V) =
      (1 / 2 : ℝ) *
        ∑ v ∈ V, ∑ w ∈ V, partMean pinned G Y τ (pairTerm v w) := by
  calc
    partMean pinned G Y τ (pairSum V) =
        partMean pinned G Y τ
          (fun n => (1 / 2 : ℝ) * ∑ v ∈ V, ∑ w ∈ V, pairTerm v w n) := by
            rfl
    _ = (1 / 2 : ℝ) *
        partMean pinned G Y τ (fun n => ∑ v ∈ V, ∑ w ∈ V, pairTerm v w n) :=
          partMean_smul pinned G Y τ (1 / 2 : ℝ) _
    _ = (1 / 2 : ℝ) *
        ∑ v ∈ V, partMean pinned G Y τ (fun n => ∑ w ∈ V, pairTerm v w n) := by
          rw [partMean_sum]
    _ = (1 / 2 : ℝ) *
        ∑ v ∈ V, ∑ w ∈ V, partMean pinned G Y τ (pairTerm v w) := by
          congr 2
          funext v
          exact partMean_sum pinned G Y τ V (pairTerm v)

theorem main : AKLT.Blueprint.Win.PairDifferenceStatement := by
  classical
  intro G Y τ _x V hV d hd hpair
  let δ : Plane → Plane → ℝ := fun v w =>
    partMean true G Y τ (pairTerm v w) - partMean false G Y τ (pairTerm v w)
  have hδ : ∀ v ∈ V, ∀ w ∈ V, v ≠ w → |δ v w| ≤ d := by
    intro v hv w hw hne
    change |partMean true G Y τ (pairTerm v w) -
      partMean false G Y τ (pairTerm v w)| ≤ d
    have hterm : pairTerm v w = (fun n => dot (n v) (n w)) := by
      funext n
      simp [pairTerm, hne]
    rw [hterm]
    exact hpair v hv w hw hne
  have hdiag : ∀ v, δ v v = 0 := by
    intro v
    change partMean true G Y τ (pairTerm v v) -
      partMean false G Y τ (pairTerm v v) = 0
    have hterm : pairTerm v v = (fun _ => (0 : ℝ)) := by
      funext n
      simp [pairTerm]
    rw [hterm, partMean_zero, partMean_zero]
    ring
  have hdiff :
      partMean true G Y τ (pairSum V) - partMean false G Y τ (pairSum V) =
        (1 / 2 : ℝ) * ∑ v ∈ V, ∑ w ∈ V, δ v w := by
    rw [partMean_pairSum, partMean_pairSum]
    rw [← mul_sub]
    congr 1
    rw [← Finset.sum_sub_distrib]
    congr 1
    funext v
    rw [← Finset.sum_sub_distrib]
  have hsumAbs :
      |∑ v ∈ V, ∑ w ∈ V, δ v w| ≤ (V.card : ℝ) * ((V.card : ℝ) - 1) * d := by
    calc
      |∑ v ∈ V, ∑ w ∈ V, δ v w| ≤ ∑ v ∈ V, |∑ w ∈ V, δ v w| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v ∈ V, ∑ w ∈ V, |δ v w| := by
        apply Finset.sum_le_sum
        intro v hv
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ v ∈ V, ((V.card : ℝ) - 1) * d := by
        apply Finset.sum_le_sum
        intro v hv
        have hsplit := Finset.sum_erase_add V (fun w => |δ v w|) hv
        rw [hdiag v, abs_zero, add_zero] at hsplit
        rw [← hsplit]
        calc
          ∑ w ∈ V.erase v, |δ v w| ≤ ∑ w ∈ V.erase v, d := by
            apply Finset.sum_le_sum
            intro w hw
            have hmem := Finset.mem_erase.mp hw
            exact hδ v hv w (Finset.mem_of_mem_erase hw) hmem.1.symm
          _ = ((V.erase v).card : ℝ) * d := by
            simp [Finset.sum_const, nsmul_eq_mul]
          _ = ((V.card : ℝ) - 1) * d := by
            rw [Finset.card_erase_of_mem hv]
            have hcard : 1 ≤ V.card := Finset.one_le_card.mpr ⟨v, hv⟩
            rw [Nat.cast_sub hcard]
            ring
      _ = (V.card : ℝ) * ((V.card : ℝ) - 1) * d := by
        simp [Finset.sum_const, nsmul_eq_mul]
        ring
  have hcoef :
      (1 / 2 : ℝ) * (V.card : ℝ) * ((V.card : ℝ) - 1) ≤
        (if V.card = 4 then 6 else 3) := by
    have hcases : V.card = 0 ∨ V.card = 1 ∨ V.card = 2 ∨ V.card = 3 ∨ V.card = 4 := by
      omega
    rcases hcases with h | h | h | h | h
    · norm_num [h]
    · norm_num [h]
    · norm_num [h]
    · norm_num [h]
    · norm_num [h]
  calc
    |partMean true G Y τ (pairSum V) - partMean false G Y τ (pairSum V)| =
        |(1 / 2 : ℝ) * ∑ v ∈ V, ∑ w ∈ V, δ v w| := by rw [hdiff]
    _ = (1 / 2 : ℝ) * |∑ v ∈ V, ∑ w ∈ V, δ v w| := by
      rw [abs_mul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * ((V.card : ℝ) * ((V.card : ℝ) - 1) * d) :=
      mul_le_mul_of_nonneg_left hsumAbs (by norm_num)
    _ = ((1 / 2 : ℝ) * (V.card : ℝ) * ((V.card : ℝ) - 1)) * d := by ring
    _ ≤ (if V.card = 4 then 6 else 3) * d := mul_le_mul_of_nonneg_right hcoef hd


end AKLT.W.WIN058
