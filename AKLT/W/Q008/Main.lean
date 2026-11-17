module
public import AKLT.Blueprint.Q.NodesTight

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Q

namespace AKLT.W.Q008

private lemma normSqPair (x y : ℝ) :
    Complex.normSq ((x : ℂ) + Complex.I * (y : ℂ)) = x^2 + y^2 := by
  rw [Complex.normSq_apply]
  simp
  ring

private lemma spinDensity00 (v : Vec3) :
    spinDensity v 0 0 = ((1 + v 2 : ℝ) / 2 : ℂ) := by
  simp [spinDensity, pauli, Fin.sum_univ_succ]
  norm_num; ring

private lemma spinDensity01 (v : Vec3) :
    spinDensity v 0 1 = ((v 0 : ℂ) - Complex.I * (v 1 : ℂ)) / 2 := by
  simp [spinDensity, pauli, Fin.sum_univ_succ]
  norm_num; ring

private lemma spinDensity10 (v : Vec3) :
    spinDensity v 1 0 = ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) / 2 := by
  simp [spinDensity, pauli, Fin.sum_univ_succ]
  norm_num; ring

private lemma spinDensity11 (v : Vec3) :
    spinDensity v 1 1 = ((1 - v 2 : ℝ) / 2 : ℂ) := by
  simp [spinDensity, pauli, Fin.sum_univ_succ]
  norm_num; ring

private lemma cross01 (x y A : ℝ) (hA : A ≠ 0) :
    (A : ℂ) * star (((x : ℂ) + Complex.I * (y : ℂ)) / ((2*A : ℝ) : ℂ)) =
      ((x : ℂ) - Complex.I * (y : ℂ)) / 2 := by
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA
  have hc : (starRingEnd ℂ) ((x : ℂ) + Complex.I * (y : ℂ)) = (x : ℂ) - Complex.I * (y : ℂ) := by
    simp
    ring
  change (A : ℂ) * (starRingEnd ℂ) (((x : ℂ) + Complex.I * (y : ℂ)) / ((2*A : ℝ) : ℂ)) = _
  rw [map_div₀, hc]
  simp only [map_mul, Complex.conj_ofReal, Complex.ofReal_mul]
  field_simp [hAc]
  norm_num

private lemma cross10 (x y A : ℝ) (hA : A ≠ 0) :
    (((x : ℂ) + Complex.I * (y : ℂ)) / ((2*A : ℝ) : ℂ)) * (A : ℂ) =
      ((x : ℂ) + Complex.I * (y : ℂ)) / 2 := by
  have hAc : (A : ℂ) ≠ 0 := by exact_mod_cast hA
  field_simp [hAc]
  norm_num; ring

/-- The explicit north-chart spinor is compatible with every unit vector,
with the south pole handled by its separate branch. -/
theorem main : AKLT.Blueprint.Q.SpinorChoiceStatement := by
  intro v hv
  change (∑ k : Fin 2, Complex.normSq (chosenSpinor v k)) = 1 ∧
    (fun k l => chosenSpinor v k * star (chosenSpinor v l)) = spinDensity v
  have hv' : v 0 * v 0 + (v 1 * v 1 + v 2 * v 2) = 1 := by
    simpa [normSq, dot, Fin.sum_univ_succ] using hv
  by_cases hpole : v 2 = -1
  · have hx : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have hy : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    constructor
    · simp [chosenSpinor, hpole]
    · funext k l
      fin_cases k <;> fin_cases l
      all_goals simp [chosenSpinor, hpole, spinDensity, pauli, Fin.sum_univ_succ, hx, hy]
      all_goals norm_num
  · have hbound : -1 ≤ v 2 ∧ v 2 ≤ 1 := by
      constructor <;> nlinarith [sq_nonneg (v 0), sq_nonneg (v 1)]
    have hzgt : -1 < v 2 := lt_of_le_of_ne hbound.1 (Ne.symm hpole)
    have hplus : 0 < 1 + v 2 := by linarith
    have hrad : 0 < (1 + v 2) / 2 := by positivity
    let A : ℝ := Real.sqrt ((1 + v 2) / 2)
    have hA : 0 < A := by dsimp [A]; positivity
    have hA2 : A * A = (1 + v 2) / 2 := by
      dsimp [A]
      exact Real.mul_self_sqrt (le_of_lt hrad)
    have hD : Real.sqrt (2 * (1 + v 2)) = 2 * A := by
      apply (Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)).2
      dsimp [A]
      nlinarith [Real.mul_self_sqrt (le_of_lt hrad)]
    have hSpos : 0 < Real.sqrt ((1 + v 2) / 2) := by positivity
    have hD0 : Real.sqrt (2 * (1 + v 2)) = 2 * Real.sqrt ((1 + v 2) / 2) := by
      simpa [A] using hD
    have hDc0 : (Real.sqrt (2 * (1 + v 2)) : ℂ) =
        ((2 * Real.sqrt ((1 + v 2) / 2) : ℝ) : ℂ) :=
      congrArg (fun r : ℝ => (r : ℂ)) hD0
    have hxy : v 0 ^ 2 + v 1 ^ 2 = 1 - v 2 ^ 2 := by nlinarith [hv']
    have hdenSq : (2 * A) * (2 * A) = 2 * (1 + v 2) := by
      nlinarith [hA2]
    have hnormB : Complex.normSq
        (((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) / ((2 * Real.sqrt ((1 + v 2) / 2) : ℝ) : ℂ)) = (1 - v 2) / 2 := by
      rw [Complex.normSq_div, normSqPair, Complex.normSq_ofReal, hdenSq]
      field_simp [ne_of_gt hplus]
      nlinarith [hxy]
    have hnormA0 : Complex.normSq (Real.sqrt ((1 + v 2) / 2) : ℂ) =
        (1 + v 2) / 2 := by
      rw [Complex.normSq_ofReal]
      exact Real.mul_self_sqrt (le_of_lt hrad)
    have hnormB0 : Complex.normSq
        (((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) /
          ((Real.sqrt (2 * (1 + v 2)) : ℝ) : ℂ)) = (1 - v 2) / 2 := by
      rw [Complex.normSq_div, normSqPair, Complex.normSq_ofReal,
        Real.mul_self_sqrt (by positivity : 0 ≤ 2 * (1 + v 2))]
      field_simp [ne_of_gt hplus]
      nlinarith [hxy]
    have hcoord0 : chosenSpinor v 0 = (Real.sqrt ((1 + v 2) / 2) : ℂ) := by
      simp only [chosenSpinor, ite_eq_right hpole]
      rfl
    have hcoord1 : chosenSpinor v 1 =
        ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) /
          (Real.sqrt (2 * (1 + v 2)) : ℂ) := by
      simp only [chosenSpinor, ite_eq_right hpole]
      rfl
    constructor
    · simp only [chosenSpinor, ite_eq_right hpole, Fin.sum_univ_succ, Fin.sum_univ_zero,
        Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
      rw [hnormA0, hnormB0]
      ring
    · funext k l
      fin_cases k <;> fin_cases l
      · change chosenSpinor v (0 : Fin 2) * star (chosenSpinor v (0 : Fin 2)) =
          (spinDensity v) (0 : Fin 2) (0 : Fin 2)
        rw [hcoord0]
        change (Real.sqrt ((1 + v 2) / 2) : ℂ) *
          (starRingEnd ℂ) (Real.sqrt ((1 + v 2) / 2) : ℂ) =
          (spinDensity v) (0 : Fin 2) (0 : Fin 2)
        rw [Complex.mul_conj, hnormA0, spinDensity00]
        push_cast
        ring
      · change chosenSpinor v (0 : Fin 2) * star (chosenSpinor v (1 : Fin 2)) =
          (spinDensity v) (0 : Fin 2) (1 : Fin 2)
        rw [hcoord0, hcoord1, hDc0]
        rw [cross01 (v 0) (v 1) (Real.sqrt ((1 + v 2) / 2)) (ne_of_gt hSpos), spinDensity01]
      · change chosenSpinor v (1 : Fin 2) * star (chosenSpinor v (0 : Fin 2)) =
          (spinDensity v) (1 : Fin 2) (0 : Fin 2)
        rw [hcoord0, hcoord1, hDc0]
        change (((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) / ((2 * Real.sqrt ((1 + v 2) / 2) : ℝ) : ℂ)) *
          (starRingEnd ℂ) (Real.sqrt ((1 + v 2) / 2) : ℂ) =
          (spinDensity v) (1 : Fin 2) (0 : Fin 2)
        simp only [Complex.conj_ofReal]
        rw [cross10 (v 0) (v 1) (Real.sqrt ((1 + v 2) / 2)) (ne_of_gt hSpos), spinDensity10]
      · change chosenSpinor v (1 : Fin 2) * star (chosenSpinor v (1 : Fin 2)) =
          (spinDensity v) (1 : Fin 2) (1 : Fin 2)
        rw [hcoord1, hDc0]
        change ((((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) / ((2 * Real.sqrt ((1 + v 2) / 2) : ℝ) : ℂ)) *
          (starRingEnd ℂ) (((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) /
            ((2 * Real.sqrt ((1 + v 2) / 2) : ℝ) : ℂ))) =
          (spinDensity v) (1 : Fin 2) (1 : Fin 2)
        rw [Complex.mul_conj, hnormB, spinDensity11]
        push_cast
        ring

end AKLT.W.Q008
