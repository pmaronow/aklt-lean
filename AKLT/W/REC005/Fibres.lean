module
public import AKLT.W.REC005.Bounds

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

namespace AKLT.W.REC005

def localWeight (s : Status) (l : List SpinLetter) (j : SpinLetter) : ℝ :=
  spinWeight s j * letterProduct l (spinVector j)

def localMass (s : Status) (l : List SpinLetter) : ℝ :=
  ∑ j, localWeight s l j

def localNumerator (s : Status) (l : List SpinLetter) : Vec3 := fun i =>
  ∑ j, localWeight s l j * spinVector j i

lemma local_mass_bound (s : Status) (l : List SpinLetter) (hl : l.length ≤ 3) :
    0 ≤ localMass s l ∧ normSq (localNumerator s l) ≤ (9 / 25 : ℝ) * localMass s l ^ 2 := by
  have heq : localNumerator s l =
      fun i => siteFunctional s (fun v => v i * letterProduct l v) := by
    funext i
    unfold localNumerator localWeight siteFunctional
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  convert local_bound s l hl using 1 <;> norm_num [localMass, localWeight, siteFunctional]

lemma local_pair_bound (s t : Status) (l r : List SpinLetter)
    (hl : l.length ≤ 3) (hr : r.length ≤ 3) :
    -(9 / 25 : ℝ) * localMass s l * localMass t r ≤
        dot (localNumerator s l) (localNumerator t r) ∧
      dot (localNumerator s l) (localNumerator t r) ≤
        (9 / 25 : ℝ) * localMass s l * localMass t r := by
  have hA := local_mass_bound s l hl
  have hB := local_mass_bound t r hr
  have hc := dot_sq_le (localNumerator s l) (localNumerator t r)
  have hp := mul_le_mul hA.2 hB.2 (normSq_nonneg _) (by positivity)
  have hn : 0 ≤ (9 / 25 : ℝ) * localMass s l * localMass t r :=
    mul_nonneg (mul_nonneg (by norm_num) hA.1) hB.1
  constructor <;> nlinarith

lemma sum_pair_mass (C : ℝ) (u v : SpinLetter → ℝ) :
    (∑ a, ∑ b, C * u a * v b) = C * (∑ a, u a) * (∑ b, v b) := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

lemma sum_pair_dot (C : ℝ) (u v : SpinLetter → ℝ) :
    (∑ a, ∑ b, C * u a * v b * dot (spinVector a) (spinVector b)) =
      C * dot (fun i => ∑ a, u a * spinVector a i)
        (fun i => ∑ b, v b * spinVector b i) := by
  have hc (i : Fin 3) :
      (∑ a, ∑ b, C * u a * v b * (spinVector a i * spinVector b i)) =
        C * (∑ a, u a * spinVector a i) * (∑ b, v b * spinVector b i) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  simp only [dot, Fin.sum_univ_three, mul_add, Finset.sum_add_distrib, hc]
  ring

lemma fibre_bound (C : ℝ) (hC : 0 ≤ C) (s t : Status) (l r : List SpinLetter)
    (hl : l.length ≤ 3) (hr : r.length ≤ 3) :
    let A := ∑ a, ∑ b, C * localWeight s l a * localWeight t r b
    let B := ∑ a, ∑ b,
      C * localWeight s l a * localWeight t r b * dot (spinVector a) (spinVector b)
    0 ≤ A ∧ -(9 / 25 : ℝ) * A ≤ B ∧ B ≤ (9 / 25 : ℝ) * A := by
  dsimp only
  rw [sum_pair_mass, sum_pair_dot]
  change 0 ≤ C * localMass s l * localMass t r ∧
    -(9 / 25 : ℝ) * (C * localMass s l * localMass t r) ≤
      C * dot (localNumerator s l) (localNumerator t r) ∧
    C * dot (localNumerator s l) (localNumerator t r) ≤
      (9 / 25 : ℝ) * (C * localMass s l * localMass t r)
  have h := local_pair_bound s t l r hl hr
  refine ⟨mul_nonneg (mul_nonneg hC (local_mass_bound s l hl).1)
    (local_mass_bound t r hr).1, ?_, ?_⟩
  · nlinarith [mul_le_mul_of_nonneg_left h.1 hC]
  · nlinarith [mul_le_mul_of_nonneg_left h.2 hC]

def exchangeCoordinate {ι α : Type*} [DecidableEq ι] (x : ι) :
    ((ι → α) × α) ≃ ((ι → α) × α) :=
  { toFun := fun p => (Function.update p.1 x p.2, p.1 x)
    invFun := fun p => (Function.update p.1 x p.2, p.1 x)
    left_inv := by rintro ⟨σ, a⟩; simp
    right_inv := by rintro ⟨σ, a⟩; simp }

lemma sum_updates {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq ι]
    (x : ι) (f : (ι → α) → ℝ) :
    (∑ σ, ∑ a, f (Function.update σ x a)) = (Fintype.card α : ℝ) * ∑ σ, f σ := by
  classical
  have h := (exchangeCoordinate (α := α) x).sum_comp (fun p => f p.1)
  simpa [exchangeCoordinate, Fintype.sum_prod_type, Finset.mul_sum, nsmul_eq_mul,
    mul_comm] using h

def updatePair {ι : Type*} [DecidableEq ι] (x y : ι) (σ : ι → SpinLetter)
    (a b : SpinLetter) : ι → SpinLetter := Function.update (Function.update σ x a) y b

lemma sum_pair_updates {ι : Type*} [Fintype ι] [DecidableEq ι] (x y : ι)
    (f : (ι → SpinLetter) → ℝ) :
    (∑ σ, ∑ a, ∑ b, f (updatePair x y σ a b)) = (169 : ℝ) * ∑ σ, f σ := by
  unfold updatePair
  rw [sum_updates x (fun τ => ∑ b, f (Function.update τ y b)), sum_updates y f]
  norm_num [SpinLetter, IcoLetter, Fintype.card_prod]
  ring

/-- Explicit finite averaging, with no normalization of zero-mass fibres. -/
theorem pair_bound_of_fibres {ι : Type*} [Fintype ι] [DecidableEq ι]
    (w : (ι → SpinLetter) → ℝ) (x y : ι) (hxy : x ≠ y) (s t : Status)
    (hF : ∀ σ : ι → SpinLetter, ∃ (C : ℝ) (l r : List SpinLetter),
      0 ≤ C ∧ l.length ≤ 3 ∧ r.length ≤ 3 ∧
      ∀ a b, w (updatePair x y σ a b) = C * localWeight s l a * localWeight t r b) :
    -(9 / 25 : ℝ) ≤ (∑ σ, w σ * dot (spinVector (σ x)) (spinVector (σ y))) / ∑ σ, w σ ∧
      (∑ σ, w σ * dot (spinVector (σ x)) (spinVector (σ y))) / ∑ σ, w σ ≤ 9 / 25 := by
  classical
  let Z := ∑ σ, w σ
  let N := ∑ σ, w σ * dot (spinVector (σ x)) (spinVector (σ y))
  have hpoint (σ : ι → SpinLetter) :
      0 ≤ ∑ a, ∑ b, w (updatePair x y σ a b) ∧
      -(9 / 25 : ℝ) * (∑ a, ∑ b, w (updatePair x y σ a b)) ≤
        ∑ a, ∑ b, w (updatePair x y σ a b) * dot (spinVector a) (spinVector b) ∧
      (∑ a, ∑ b, w (updatePair x y σ a b) * dot (spinVector a) (spinVector b)) ≤
        (9 / 25 : ℝ) * (∑ a, ∑ b, w (updatePair x y σ a b)) := by
    obtain ⟨C, l, r, hC, hl, hr, heq⟩ := hF σ
    simp_rw [heq]
    exact fibre_bound C hC s t l r hl hr
  have hZ : 0 ≤ (169 : ℝ) * Z := by
    rw [← sum_pair_updates x y w]
    exact Finset.sum_nonneg (fun σ _ => (hpoint σ).1)
  have hlo := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => (hpoint σ).2.1)
  have hhi := Finset.sum_le_sum (fun σ (_ : σ ∈ Finset.univ) => (hpoint σ).2.2)
  have heq : (∑ σ, ∑ a, ∑ b,
      w (updatePair x y σ a b) * dot (spinVector a) (spinVector b)) = (169 : ℝ) * N := by
    convert sum_pair_updates x y
      (fun σ => w σ * dot (spinVector (σ x)) (spinVector (σ y))) using 1
    apply Finset.sum_congr rfl
    intro σ _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    simp [updatePair, hxy, Ne.symm hxy]
  simp only [← Finset.mul_sum, sum_pair_updates, heq] at hlo hhi
  change -(9 / 25 : ℝ) * (169 * Z) ≤ 169 * N at hlo
  change 169 * N ≤ (9 / 25 : ℝ) * (169 * Z) at hhi
  change -(9 / 25 : ℝ) ≤ N / Z ∧ N / Z ≤ 9 / 25
  by_cases hz : Z = 0
  · norm_num [hz]
  · have hzpos : 0 < Z := lt_of_le_of_ne (by nlinarith) (Ne.symm hz)
    constructor
    · apply (le_div_iff₀ hzpos).2
      nlinarith
    · apply (div_le_iff₀ hzpos).2
      nlinarith

end AKLT.W.REC005
