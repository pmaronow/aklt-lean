import AKLT.Blueprint.Win.NodesRemoval

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN060

open AKLT.Blueprint.Win

private theorem partSum_add (G Y : Finset Plane) (τ : PinAssignment G)
    (pinned : Bool) (f g : (Plane → Vec3) → ℝ) :
    partSum pinned G Y τ (fun n => f n + g n) =
      partSum pinned G Y τ f + partSum pinned G Y τ g := by
  classical
  cases pinned <;>
    simp only [partSum, Bool.false_eq_true, ↓reduceIte, pinnedSum, freeSum] <;>
    simp only [mul_add, add_mul, Finset.sum_add_distrib]

private theorem partSum_const (G Y : Finset Plane) (τ : PinAssignment G)
    (pinned : Bool) (c : ℝ) :
    partSum pinned G Y τ (fun _ => c) =
      c * partSum pinned G Y τ (fun _ => 1) := by
  classical
  cases pinned <;>
    simp only [partSum, Bool.false_eq_true, ↓reduceIte, pinnedSum, freeSum] <;>
    rw [Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro n hn <;> ring

private theorem partSum_smul (G Y : Finset Plane) (τ : PinAssignment G)
    (pinned : Bool) (c : ℝ) (f : (Plane → Vec3) → ℝ) :
    partSum pinned G Y τ (fun n => c * f n) =
      c * partSum pinned G Y τ f := by
  classical
  cases pinned <;>
    simp only [partSum, Bool.false_eq_true, ↓reduceIte, pinnedSum, freeSum] <;>
    rw [Finset.mul_sum] <;>
    apply Finset.sum_congr rfl <;> intro n hn <;> ring

private theorem partMean_add (G Y : Finset Plane) (τ : PinAssignment G)
    (pinned : Bool) (f g : (Plane → Vec3) → ℝ) :
    partMean pinned G Y τ (fun n => f n + g n) =
      partMean pinned G Y τ f + partMean pinned G Y τ g := by
  unfold partMean
  rw [partSum_add]
  exact add_div _ _ _

private theorem partMean_const (G Y : Finset Plane) (τ : PinAssignment G)
    (pinned : Bool) (c : ℝ)
    (hZ : partSum pinned G Y τ (fun _ => 1) ≠ 0) :
    partMean pinned G Y τ (fun _ => c) = c := by
  unfold partMean
  rw [partSum_const]
  field_simp [hZ]

private theorem partMean_smul (G Y : Finset Plane) (τ : PinAssignment G)
    (pinned : Bool) (c : ℝ) (f : (Plane → Vec3) → ℝ) :
    partMean pinned G Y τ (fun n => c * f n) =
      c * partMean pinned G Y τ f := by
  unfold partMean
  rw [partSum_smul]
  ring

private theorem partMean_div (G Y : Finset Plane) (τ : PinAssignment G)
    (pinned : Bool) (f : (Plane → Vec3) → ℝ) (c : ℝ) :
    partMean pinned G Y τ (fun n => f n / c) =
      partMean pinned G Y τ f / c := by
  have hfun : (fun n => f n / c) = fun n => c⁻¹ * f n := by
    funext n
    simp [div_eq_mul_inv, mul_comm]
  rw [hfun, partMean_smul]
  simp [div_eq_mul_inv, mul_comm]

private theorem mean_removal (G Y : Finset Plane) (τ : PinAssignment G)
    (pinned : Bool) (x : Plane) (V : Finset Plane)
    (hZ : partSum pinned G Y τ (fun _ => 1) ≠ 0) :
    partMean pinned G Y τ (removalPolynomial x V) =
      1 + partMean pinned G Y τ (pairSum V) / 3 +
        (if V.card = 4 then partMean pinned G Y τ (quartic x) / 15 else 0) := by
  classical
  unfold removalPolynomial
  by_cases hk : V.card = 4
  · simp only [if_pos hk]
    rw [partMean_add, partMean_add, partMean_const G Y τ pinned 1 hZ,
      partMean_div, partMean_div]
  · simp only [if_neg hk]
    rw [partMean_add, partMean_add, partMean_const G Y τ pinned 1 hZ,
      partMean_div]
    rw [partMean_const G Y τ pinned 0 hZ]

theorem main : AKLT.Blueprint.Win.LocalLogEstimateStatement := by
  intro hlip G Y τ x V hV d hd hmeans hpair
  let a := partMean true G Y τ (removalPolynomial x V)
  let b := partMean false G Y τ (removalPolynomial x V)
  have hza : partSum true G Y τ (fun _ => 1) ≠ 0 := (hmeans true).1.ne'
  have hzb : partSum false G Y τ (fun _ => 1) ≠ 0 := (hmeans false).1.ne'
  have ha : a = 1 + partMean true G Y τ (pairSum V) / 3 +
      (if V.card = 4 then partMean true G Y τ (quartic x) / 15 else 0) :=
    mean_removal G Y τ true x V hza
  have hb : b = 1 + partMean false G Y τ (pairSum V) / 3 +
      (if V.card = 4 then partMean false G Y τ (quartic x) / 15 else 0) :=
    mean_removal G Y τ false x V hzb
  have hlog := hlip a b ((hmeans true).2.1) ((hmeans false).2.1)
  by_cases hk : V.card = 4
  · have hq : |partMean true G Y τ (quartic x) -
        partMean false G Y τ (quartic x)| ≤ 6 := by
      calc
        _ ≤ |partMean true G Y τ (quartic x)| +
            |partMean false G Y τ (quartic x)| := abs_sub _ _
        _ ≤ 3 + 3 := add_le_add (hmeans true).2.2 (hmeans false).2.2
        _ = 6 := by norm_num
    have hab : a - b =
        (partMean true G Y τ (pairSum V) -
          partMean false G Y τ (pairSum V)) / 3 +
        (partMean true G Y τ (quartic x) -
          partMean false G Y τ (quartic x)) / 15 := by
      rw [ha, hb]
      simp [hk]
      ring_nf
    have hp : |(partMean true G Y τ (pairSum V) -
        partMean false G Y τ (pairSum V)) / 3| ≤ 2 * d := by
      have h := hpair
      simp only [hk, if_pos] at h
      calc
        _ = |partMean true G Y τ (pairSum V) -
            partMean false G Y τ (pairSum V)| / 3 := by rw [abs_div]; norm_num
        _ ≤ (6 * d) / 3 := div_le_div_of_nonneg_right h (by norm_num)
        _ = 2 * d := by ring
    have hq' : |(partMean true G Y τ (quartic x) -
        partMean false G Y τ (quartic x)) / 15| ≤ 2 / 5 := by
      calc
        _ = |partMean true G Y τ (quartic x) -
            partMean false G Y τ (quartic x)| / 15 := by rw [abs_div]; norm_num
        _ ≤ 6 / 15 := div_le_div_of_nonneg_right hq (by norm_num)
        _ = 2 / 5 := by norm_num
    have habound : |a - b| ≤ 2 * d + 2 / 5 := by
      rw [hab]
      calc
        _ ≤ |(partMean true G Y τ (pairSum V) -
            partMean false G Y τ (pairSum V)) / 3| +
            |(partMean true G Y τ (quartic x) -
            partMean false G Y τ (quartic x)) / 15| := abs_add_le _ _
        _ ≤ 2 * d + 2 / 5 := add_le_add hp hq'
    have hfinish : 2 * |a - b| ≤ 1 + 4 * d := by nlinarith
    simpa [hk] using hlog.trans hfinish
  · have hpair' : |partMean true G Y τ (pairSum V) -
        partMean false G Y τ (pairSum V)| ≤ 3 * d := by
      simpa [hk] using hpair
    have hab : a - b =
        (partMean true G Y τ (pairSum V) -
          partMean false G Y τ (pairSum V)) / 3 := by
      rw [ha, hb]
      simp [hk]
      ring
    have habound : |a - b| ≤ d := by
      rw [hab]
      calc
        _ = |partMean true G Y τ (pairSum V) -
            partMean false G Y τ (pairSum V)| / 3 := by rw [abs_div]; norm_num
        _ ≤ (3 * d) / 3 := div_le_div_of_nonneg_right hpair' (by norm_num)
        _ = d := by ring
    have hfinish : 2 * |a - b| ≤ 2 * d := by nlinarith
    simpa [hk] using hlog.trans hfinish

end AKLT.W.WIN060
