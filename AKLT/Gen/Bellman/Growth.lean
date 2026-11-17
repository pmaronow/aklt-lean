module
public import Mathlib

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-!
# Positive-vector bounds for a finite one-step matrix

The matrix is indexed as `M source destination`. Thus the right witness `M h ≤ q h`
controls a *forward* sequence `A (n+1) destination ≤ ∑ source, A n source * M source destination`
by pairing that sequence with `h`. The finite-prefix theorem is the generic form of `l:alm`.
-/

namespace AKLT.Gen.Bellman

open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {I : Type*} [Fintype I]

/-- Pair a nonnegative row distribution with a positive column witness. -/
def moment (a h : I → ℝ) : ℝ := ∑ i, a i * h i

/-- A dominated forward step contracts the weighted moment by the right witness bound. -/
theorem moment_step_le (M : I → I → ℝ) (a b h : I → ℝ) (q : ℝ)
    (ha : ∀ i, 0 ≤ a i) (hh : ∀ i, 0 ≤ h i)
    (hstep : ∀ j, b j ≤ ∑ i, a i * M i j)
    (hwitness : ∀ i, ∑ j, M i j * h j ≤ q * h i) :
    moment b h ≤ q * moment a h := by
  calc
    moment b h ≤ ∑ j, (∑ i, a i * M i j) * h j := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (hstep j) (hh j)
    _ = ∑ i, a i * (∑ j, M i j * h j) := by
      simp_rw [Finset.sum_mul, mul_assoc]
      rw [Finset.sum_comm]
      simp_rw [Finset.mul_sum]
    _ ≤ ∑ i, a i * (q * h i) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hwitness i) (ha i)
    _ = q * moment a h := by
      simp only [moment, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Iterating the single checked inequality bounds every weighted moment. -/
theorem moment_growth (M : I → I → ℝ) (A : ℕ → I → ℝ) (h : I → ℝ) (q : ℝ)
    (hq : 0 ≤ q) (hA : ∀ n i, 0 ≤ A n i) (hh : ∀ i, 0 ≤ h i)
    (hstep : ∀ n j, A (n + 1) j ≤ ∑ i, A n i * M i j)
    (hwitness : ∀ i, ∑ j, M i j * h j ≤ q * h i) (n : ℕ) :
    moment (A n) h ≤ q ^ n * moment (A 0) h := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      moment (A (n + 1)) h ≤ q * moment (A n) h :=
        moment_step_le M _ _ h q (hA n) hh (hstep n) hwitness
      _ ≤ q * (q ^ n * moment (A 0) h) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (n + 1) * moment (A 0) h := by ring

/-- Bounds on the positive witness convert moment growth into ordinary total-mass growth. -/
theorem mass_growth (M : I → I → ℝ) (A : ℕ → I → ℝ) (h : I → ℝ)
    (q lo hi : ℝ) (hq : 0 ≤ q) (hlo : 0 < lo)
    (hA : ∀ n i, 0 ≤ A n i) (hlower : ∀ i, lo ≤ h i) (hupper : ∀ i, h i ≤ hi)
    (hstep : ∀ n j, A (n + 1) j ≤ ∑ i, A n i * M i j)
    (hwitness : ∀ i, ∑ j, M i j * h j ≤ q * h i) (n : ℕ) :
    (∑ i, A n i) ≤ (hi / lo) * (∑ i, A 0 i) * q ^ n := by
  have hl : lo * (∑ i, A n i) ≤ moment (A n) h := by
    rw [moment, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [hA n i, hlower i]
  have hu : moment (A 0) h ≤ hi * (∑ i, A 0 i) := by
    rw [moment, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [hA 0 i, hupper i]
  have hm := moment_growth M A h q hq hA (fun i => hlo.le.trans (hlower i))
    hstep hwitness n
  have hb := hl.trans (hm.trans (mul_le_mul_of_nonneg_left hu (pow_nonneg hq n)))
  calc
    (∑ i, A n i) ≤ (q ^ n * (hi * ∑ i, A 0 i)) / lo :=
      (le_div_iff₀ hlo).2 (by nlinarith [hb])
    _ = (hi / lo) * (∑ i, A 0 i) * q ^ n := by ring

/-- Minimum of a finite, nonempty witness vector. -/
noncomputable def minWitness [Nonempty I] (h : I → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty h

/-- Maximum of a finite, nonempty witness vector. -/
noncomputable def maxWitness [Nonempty I] (h : I → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty h

theorem minWitness_le [Nonempty I] (h : I → ℝ) (i : I) : minWitness h ≤ h i :=
  Finset.inf'_le h (Finset.mem_univ i)

theorem le_maxWitness [Nonempty I] (h : I → ℝ) (i : I) : h i ≤ maxWitness h :=
  Finset.le_sup' h (Finset.mem_univ i)

theorem minWitness_pos [Nonempty I] (h : I → ℝ) (hh : ∀ i, 0 < h i) :
    0 < minWitness h := by
  exact (Finset.lt_inf'_iff _).2 fun i _ => hh i

/-- The exact `max h / min h` form used in the one-step lemma. -/
theorem positive_vector_growth [Nonempty I] (M : I → I → ℝ) (A : ℕ → I → ℝ)
    (h : I → ℝ) (q : ℝ) (hq : 0 ≤ q) (hA : ∀ n i, 0 ≤ A n i)
    (hh : ∀ i, 0 < h i)
    (hstep : ∀ n j, A (n + 1) j ≤ ∑ i, A n i * M i j)
    (hwitness : ∀ i, ∑ j, M i j * h j ≤ q * h i) (n : ℕ) :
    (∑ i, A n i) ≤ (maxWitness h / minWitness h) * (∑ i, A 0 i) * q ^ n :=
  mass_growth M A h q _ _ hq (minWitness_pos h hh) hA
    (minWitness_le h) (le_maxWitness h) hstep hwitness n

/-- The finite matrix path sum, with terminal vector `b` and exactly `n` steps. -/
def walkSum (M : I → I → ℝ) (b : I → ℝ) : ℕ → I → ℝ
  | 0 => b
  | n + 1 => fun i => ∑ j, M i j * walkSum M b n j

/-- A positive-vector witness bounds arbitrary terminal vectors dominated by a multiple of it. -/
theorem walkSum_le (M : I → I → ℝ) (b h : I → ℝ) (q C : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hq : 0 ≤ q) (hC : 0 ≤ C)
    (hb : ∀ i, b i ≤ C * h i)
    (hwitness : ∀ i, ∑ j, M i j * h j ≤ q * h i) (n : ℕ) (i : I) :
    walkSum M b n i ≤ C * q ^ n * h i := by
  induction n generalizing i with
  | zero => simpa [walkSum] using hb i
  | succ n ih =>
    calc
      walkSum M b (n + 1) i ≤ ∑ j, M i j * (C * q ^ n * h j) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (ih j) (hM i j)
      _ = (C * q ^ n) * (∑ j, M i j * h j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ ≤ (C * q ^ n) * (q * h i) :=
        mul_le_mul_of_nonneg_left (hwitness i) (mul_nonneg hC (pow_nonneg hq n))
      _ = C * q ^ (n + 1) * h i := by ring

/-- In particular, the sum of weights of *all* length-`n` paths is at most `C q^n`. -/
theorem all_length_path_bound [Nonempty I] (M : I → I → ℝ) (h : I → ℝ) (q : ℝ)
    (hM : ∀ i j, 0 ≤ M i j) (hq : 0 ≤ q) (hh : ∀ i, 0 < h i)
    (hwitness : ∀ i, ∑ j, M i j * h j ≤ q * h i) (n : ℕ) (i : I) :
    walkSum M (fun _ => 1) n i ≤ (maxWitness h / minWitness h) * q ^ n := by
  have hlo := minWitness_pos h hh
  have hb : ∀ j, (1 : ℝ) ≤ (1 / minWitness h) * h j := by
    intro j
    have hj : (1 : ℝ) ≤ h j / minWitness h :=
      (le_div_iff₀ hlo).2 (by simpa using minWitness_le h j)
    convert hj using 1
    ring
  have hg := walkSum_le M (fun _ => 1) h q (1 / minWitness h) hM hq
    (by positivity) hb hwitness n i
  calc
    walkSum M (fun _ => 1) n i ≤ (1 / minWitness h) * q ^ n * h i := hg
    _ ≤ (1 / minWitness h) * q ^ n * maxWitness h :=
      mul_le_mul_of_nonneg_left (le_maxWitness h i)
        (mul_nonneg (by positivity) (pow_nonneg hq n))
    _ = (maxWitness h / minWitness h) * q ^ n := by ring

/-- A convenient finite-prefix constant: a maximum over every short length and the tail bound. -/
noncomputable def growthConstant [Nonempty I] (h : I → ℝ) (W : ℕ → ℝ)
    (q : ℝ) (m : ℕ) (hm : 0 < m) : ℝ :=
  max ((Finset.range m).sup' (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hm))
    (fun r => W r / q ^ r))
    ((maxWitness h / minWitness h) * W m / q ^ m)

/-- The finite-prefix form of `l:alm`, permitting any larger supplied constant. -/
theorem alm_of_constant [Nonempty I] (M : I → I → ℝ) (A : ℕ → I → ℝ)
    (h : I → ℝ) (W : ℕ → ℝ) (q C : ℝ) (m : ℕ)
    (hq : 0 < q) (hA : ∀ n i, 0 ≤ A n i) (hh : ∀ i, 0 < h i)
    (hstep : ∀ n, m ≤ n → ∀ j, A (n + 1) j ≤ ∑ i, A n i * M i j)
    (hwitness : ∀ i, ∑ j, M i j * h j ≤ q * h i)
    (hW : ∀ n, m ≤ n → W n = ∑ i, A n i)
    (hprefix : ∀ r, r < m → W r / q ^ r ≤ C)
    (htail : (maxWitness h / minWitness h) * W m / q ^ m ≤ C) :
    ∀ n, W n ≤ C * q ^ n := by
  intro n
  by_cases hn : n < m
  · exact (div_le_iff₀ (pow_pos hq n)).1 (hprefix n hn)
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
    have hg := positive_vector_growth M (fun k => A (m + k)) h q hq.le
      (fun k i => hA (m + k) i) hh
      (fun k j => by simpa [Nat.add_assoc] using hstep (m + k) (Nat.le_add_right m k) j)
      hwitness k
    have hb : W (m + k) ≤ (maxWitness h / minWitness h) * W m * q ^ k := by
      simpa only [hW (m + k) (Nat.le_add_right m k), Nat.add_zero, hW m le_rfl] using hg
    calc
      W (m + k) ≤ (maxWitness h / minWitness h) * W m * q ^ k := hb
      _ ≤ (C * q ^ m) * q ^ k :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ (pow_pos hq m)).1 htail)
          (pow_nonneg hq.le k)
      _ = C * q ^ (m + k) := by rw [pow_add]; ring

/-- The explicit maximum in `l:alm` bounds every length, including the short prefix. -/
theorem alm [Nonempty I] (M : I → I → ℝ) (A : ℕ → I → ℝ)
    (h : I → ℝ) (W : ℕ → ℝ) (q : ℝ) (m : ℕ) (hm : 0 < m)
    (hq : 0 < q) (hA : ∀ n i, 0 ≤ A n i) (hh : ∀ i, 0 < h i)
    (hstep : ∀ n, m ≤ n → ∀ j, A (n + 1) j ≤ ∑ i, A n i * M i j)
    (hwitness : ∀ i, ∑ j, M i j * h j ≤ q * h i)
    (hW : ∀ n, m ≤ n → W n = ∑ i, A n i) :
    ∀ n, W n ≤ growthConstant h W q m hm * q ^ n := by
  apply alm_of_constant M A h W q _ m hq hA hh hstep hwitness hW
  · intro r hr
    exact (Finset.le_sup' (fun r => W r / q ^ r) (Finset.mem_range.mpr hr)).trans
      (le_max_left _ _)
  · exact le_max_right _ _

end AKLT.Gen.Bellman
