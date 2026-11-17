module
public import AKLT.W.REC022.Sum

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC022

variable {G : Finset Plane}

def scalarI (n : Plane → Vec3) (o f g : Plane) : ℝ :=
  1 + (dot (n f) (n g) + dot (n f) (n o) + dot (n g) (n o)) / 3

def scalarJ (n : Plane → Vec3) (f g : Plane) : ℝ :=
  1 + dot (n f) (n g) / 5

theorem partition_add (D : Network G) (τ : PinAssignment G) (b : Bool)
    (f g : (Plane → Vec3) → ℝ) :
    D.partition τ b (fun n => f n + g n) = D.partition τ b f + D.partition τ b g := by
  simp only [partition_sum,mul_add,Finset.sum_add_distrib]

theorem partition_div (D : Network G) (τ : PinAssignment G) (b : Bool)
    (f : (Plane → Vec3) → ℝ) (c : ℝ) :
    D.partition τ b (fun n => f n / c) = D.partition τ b f / c := by
  simp only [partition_sum,mul_div_assoc,Finset.sum_div]

theorem partition_const (D : Network G) (τ : PinAssignment G) (b : Bool) (c : ℝ) :
    D.partition τ b (fun _ => c) = D.partition τ b (fun _ => 1) * c := by
  simp only [partition_sum,mul_one,Finset.sum_mul]

theorem partition_nonneg (D : Network G) (τ : PinAssignment G) (b : Bool) :
    0 ≤ D.partition τ b (fun _ => 1) := by
  simp only [partition_sum,mul_one]
  exact Finset.sum_nonneg fun σ _ => netWeight_nonneg D τ b σ

theorem partition_zero (D : Network G) (τ : PinAssignment G) (b : Bool)
    (hz : D.partition τ b (fun _ => 1) = 0) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = 0 := by
  rw [partition_sum] at hz ⊢
  simp only [mul_one] at hz
  have hw := (Finset.sum_eq_zero_iff_of_nonneg
    (fun σ _ => netWeight_nonneg D τ b σ)).mp hz
  apply Finset.sum_eq_zero
  intro σ hσ
  rw [hw σ hσ, zero_mul]

theorem partition_lower (D : Network G) (τ : PinAssignment G) (b : Bool)
    (f : (Plane → Vec3) → ℝ) (c : ℝ)
    (h : ∀ σ : D.active → SpinLetter, c ≤ f (D.spins σ)) :
    D.partition τ b (fun _ => 1) * c ≤ D.partition τ b f := by
  rw [← partition_const,partition_sum,partition_sum]
  exact Finset.sum_le_sum fun σ _ =>
    mul_le_mul_of_nonneg_left (h σ) (netWeight_nonneg D τ b σ)

theorem scalarI_partition (D : Network G) (τ : PinAssignment G) (b : Bool)
    (y o f g : Plane) :
    (removeSite D y).partition τ b (fun n => scalarI n o f g) =
      (removeSite D y).partition τ b (fun _ => 1) * responseI D τ b y o f g := by
  let E := removeSite D y
  by_cases hz : E.partition τ b (fun _ => 1) = 0
  · rw [partition_zero E τ b hz, hz, zero_mul]
  · unfold scalarI
    rw [partition_add,partition_div,partition_add,partition_add]
    unfold responseI removedPairMean Network.expectation
    change _ = E.partition τ b (fun _ => 1) * (1 +
      (E.partition τ b (fun n => dot (n f) (n g)) / E.partition τ b (fun _ => 1) +
        E.partition τ b (fun n => dot (n f) (n o)) / E.partition τ b (fun _ => 1) +
        E.partition τ b (fun n => dot (n g) (n o)) / E.partition τ b (fun _ => 1)) / 3)
    field_simp
    ring

theorem scalarJ_partition (D : Network G) (τ : PinAssignment G) (b : Bool)
    (y f g : Plane) :
    (removeSite D y).partition τ b (fun n => scalarJ n f g) =
      (removeSite D y).partition τ b (fun _ => 1) * responseJ D τ b y f g := by
  let E := removeSite D y
  by_cases hz : E.partition τ b (fun _ => 1) = 0
  · rw [partition_zero E τ b hz, hz, zero_mul]
  · unfold scalarJ
    rw [partition_add,partition_div]
    unfold responseJ removedPairMean Network.expectation
    change _ = E.partition τ b (fun _ => 1) * (1 +
      E.partition τ b (fun n => dot (n f) (n g)) / E.partition τ b (fun _ => 1) / 5)
    field_simp
    ring

theorem responseI_pos (D : Network G) (τ : PinAssignment G) (b : Bool)
    (y o f g : Plane) : 0 < responseI D τ b y o f g := by
  let E := removeSite D y
  by_cases hz : E.partition τ b (fun _ => 1) = 0
  · simp [responseI,removedPairMean,Network.expectation,show
        (removeSite D y).partition τ b (fun _ => 1) = 0 from hz]
  · have hp : 0 < E.partition τ b (fun _ => 1) :=
      lt_of_le_of_ne (partition_nonneg E τ b) (Ne.symm hz)
    have hl := partition_lower E τ b (fun n => scalarI n o f g) (1/2) (by
      intro σ
      exact three_scalar_lower _ _ _ (spins_ball E σ f)
        (spins_ball E σ g) (spins_ball E σ o))
    rw [scalarI_partition] at hl
    have hc : (1/2 : ℝ) ≤ responseI D τ b y o f g :=
      (mul_le_mul_iff_right₀ hp).mp hl
    linarith

theorem responseJ_pos (D : Network G) (τ : PinAssignment G) (b : Bool)
    (y f g : Plane) : 0 < responseJ D τ b y f g := by
  let E := removeSite D y
  by_cases hz : E.partition τ b (fun _ => 1) = 0
  · simp [responseJ,removedPairMean,Network.expectation,show
        (removeSite D y).partition τ b (fun _ => 1) = 0 from hz]
  · have hp : 0 < E.partition τ b (fun _ => 1) :=
      lt_of_le_of_ne (partition_nonneg E τ b) (Ne.symm hz)
    have hl := partition_lower E τ b (fun n => scalarJ n f g) (4/5) (by
      intro σ
      exact two_scalar_lower _ _ (spins_ball E σ f) (spins_ball E σ g))
    rw [scalarJ_partition] at hl
    have hc : (4/5 : ℝ) ≤ responseJ D τ b y f g :=
      (mul_le_mul_iff_right₀ hp).mp hl
    linarith

end AKLT.W.REC022
