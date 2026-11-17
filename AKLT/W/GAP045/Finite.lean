module
public import AKLT.Blueprint.Gap.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP045

attribute [local instance] Classical.propDecidable
local instance (α : Type) : DecidableEq α := Classical.decEq α

variable {Ω Ξ Λ : Type} [Fintype Ω] [Fintype Ξ] [Fintype Λ]
  [DecidableEq Ξ] [DecidableEq Λ]

lemma marginal_total (p : Weight Ω) (f : Ω → Ξ) :
    ∑ b, marginal p f b = ∑ x, p x := by
  classical
  simp only [marginal]
  rw [Finset.sum_comm]
  simp

lemma marginal_nonnegative {p : Weight Ω} (hp : ∀ x, 0 ≤ p x) (f : Ω → Ξ) (b : Ξ) :
    0 ≤ marginal p f b := by
  classical
  unfold marginal
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp_all

lemma marginal_event (p : Weight Ω) (f : Ω → Ξ) (b : Ξ) :
    marginal p f b = eventMass p (fun x => f x = b) := by
  unfold marginal eventMass
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : f x = b <;> simp [h]

lemma conditional_event (p : Weight Ω) (E A : Ω → Prop) :
    conditionalProbability p E A = eventMass p (fun x => E x ∧ A x) / eventMass p E := by
  unfold conditionalProbability eventMass
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : E x ∧ A x <;> simp [h]

lemma marginal_probability {p : Weight Ω} (hp : Probability p) (f : Ω → Ξ) :
    Probability (marginal p f) := by
  classical
  exact ⟨marginal_nonnegative hp.1 f, by rw [marginal_total, hp.2]⟩

lemma marginal_comp (p : Weight Ω) (f : Ω → Ξ) (g : Ξ → Λ) :
    marginal (marginal p f) g = marginal p (g ∘ f) := by
  classical
  funext z
  simp only [marginal]
  have hi (b : Ξ) :
      (if g b = z then ∑ x, if f x = b then p x else 0 else 0) =
      ∑ x, if f x = b then (if g b = z then p x else 0) else 0 := by
    by_cases hb : g b = z <;> simp [hb]
  simp_rw [hi]
  rw [Finset.sum_comm]
  simp [Function.comp_def]

lemma marginal_test (p : Weight Ω) (f : Ω → Ξ) (g : Ξ → ℝ) :
    ∑ b, marginal p f b * g b = ∑ x, p x * g (f x) := by
  classical
  simp only [marginal, Finset.sum_mul]
  rw [Finset.sum_comm]
  congr 1
  funext x
  simp

lemma event_nonnegative {p : Weight Ω} (hp : ∀ x, 0 ≤ p x) (E : Ω → Prop) :
    0 ≤ eventMass p E := by
  classical
  unfold eventMass
  exact Finset.sum_nonneg fun x _ => by split_ifs <;> simp_all

lemma event_mono {p q : Weight Ω} {E F : Ω → Prop}
    (hp : ∀ x, 0 ≤ p x) (hpq : ∀ x, p x ≤ q x) (hEF : ∀ x, E x → F x) :
    eventMass p E ≤ eventMass q F := by
  classical
  apply Finset.sum_le_sum
  intro x _
  by_cases hE : E x
  · simp only [hE, hEF x hE, ite_true]
    exact hpq x
  · by_cases hF : F x
    · simpa [hE, hF] using (hp x).trans (hpq x)
    · simp [hE, hF]

lemma event_le_one {p : Weight Ω} (hp : Probability p) (E : Ω → Prop) :
    eventMass p E ≤ 1 := by
  classical
  rw [← hp.2]
  apply Finset.sum_le_sum
  intro x _
  split_ifs <;> simp_all [hp.1]

lemma condition_probability {p : Weight Ω} (hp : ∀ x, 0 ≤ p x)
    (E : Ω → Prop) (he : 0 < eventMass p E) : Probability (conditionOn p E) := by
  classical
  constructor
  · intro x
    change 0 ≤ (if E x then p x else 0) / eventMass p E
    exact div_nonneg (by split_ifs <;> simp_all) he.le
  · change (∑ x, (if E x then p x else 0) / eventMass p E) = 1
    rw [← Finset.sum_div]
    exact div_self he.ne'

lemma condition_support {p : Weight Ω} (E : Ω → Prop) (x : Ω)
    (hx : 0 < conditionOn p E x) : E x := by
  classical
  by_contra hn
  simp [conditionOn, Defs.normalize, hn] at hx

lemma event_pos_of_atom {p : Weight Ω} (hp : ∀ x, 0 ≤ p x) (E : Ω → Prop)
    (x : Ω) (hx : E x) (hpx : 0 < p x) : 0 < eventMass p E := by
  classical
  have hh := Finset.single_le_sum (f := fun y => if E y then p y else 0)
    (fun y _ => by split_ifs <;> simp_all) (Finset.mem_univ x)
  exact hpx.trans_le (by simpa [eventMass, hx] using hh)

lemma coupling_probability {p : Weight Ω} {q : Weight Ξ} (hp : Probability p)
    (c : Coupling p q) : Probability (fun v : Ω × Ξ => c.mass v.1 v.2) := by
  refine ⟨fun v => c.nonnegative _ _, ?_⟩
  rw [Fintype.sum_prod_type]
  simp_rw [c.first_marginal]
  exact hp.2

lemma coupling_atom_first {p : Weight Ω} {q : Weight Ξ} (c : Coupling p q) (x : Ω) (y : Ξ) :
    c.mass x y ≤ p x := by
  rw [← c.first_marginal x]
  exact Finset.single_le_sum (fun z _ => c.nonnegative x z) (Finset.mem_univ y)

lemma coupling_atom_second {p : Weight Ω} {q : Weight Ξ} (c : Coupling p q) (x : Ω) (y : Ξ) :
    c.mass x y ≤ q y := by
  rw [← c.second_marginal y]
  exact Finset.single_le_sum (fun z _ => c.nonnegative z y) (Finset.mem_univ x)

/-- Complete an arbitrary subcoupling by coupling its two residual marginals. -/
theorem complete_subcoupling {p : Weight Ω} {q : Weight Ξ}
    (hp : Probability p) (hq : Probability q) (k : Ω → Ξ → ℝ)
    (hk : ∀ x y, 0 ≤ k x y)
    (hkp : ∀ x, ∑ y, k x y ≤ p x) (hkq : ∀ y, ∑ x, k x y ≤ q y) :
    ∃ c : Coupling p q, ∀ x y, k x y ≤ c.mass x y := by
  classical
  let a : Weight Ω := fun x => p x - ∑ y, k x y
  let b : Weight Ξ := fun y => q y - ∑ x, k x y
  let d : ℝ := 1 - ∑ x, ∑ y, k x y
  have ha : ∀ x, 0 ≤ a x := fun x => sub_nonneg.mpr (hkp x)
  have hb : ∀ y, 0 ≤ b y := fun y => sub_nonneg.mpr (hkq y)
  have had : ∑ x, a x = d := by dsimp [a, d]; rw [Finset.sum_sub_distrib, hp.2]
  have hbd : ∑ y, b y = d := by
    dsimp [b, d]; rw [Finset.sum_sub_distrib, hq.2, Finset.sum_comm]
  have hd : 0 ≤ d := had ▸ Finset.sum_nonneg (fun x _ => ha x)
  have hrow : ∀ x, (∑ y, a x * b y / d) = a x := by
    intro x
    rw [← Finset.sum_div, ← Finset.mul_sum, hbd]
    by_cases hd0 : d = 0
    · have hx : a x = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => ha x)).mp
        (had.trans hd0) x (Finset.mem_univ x)
      simp [hd0, hx]
    · exact mul_div_cancel_right₀ _ hd0
  have hcol : ∀ y, (∑ x, a x * b y / d) = b y := by
    intro y
    rw [← Finset.sum_div, ← Finset.sum_mul, had]
    by_cases hd0 : d = 0
    · have hy : b y = 0 := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => hb y)).mp
        (hbd.trans hd0) y (Finset.mem_univ y)
      simp [hd0, hy]
    · rw [mul_comm]; exact mul_div_cancel_right₀ _ hd0
  let c : Coupling p q := {
    mass := fun x y => k x y + a x * b y / d
    nonnegative := fun x y => add_nonneg (hk x y) (div_nonneg (mul_nonneg (ha x) (hb y)) hd)
    first_marginal := fun x => by rw [Finset.sum_add_distrib, hrow]; dsimp [a]; ring
    second_marginal := fun y => by rw [Finset.sum_add_distrib, hcol]; dsimp [b]; ring }
  exact ⟨c, fun x y => le_add_of_nonneg_right (div_nonneg (mul_nonneg (ha x) (hb y)) hd)⟩

/-- Total variation is one minus the finite overlap. -/
lemma tv_overlap {p q : Weight Ω} (hp : Probability p) (hq : Probability q) :
    totalVariation p q = 1 - ∑ x, min (p x) (q x) := by
  have he : ∀ x, |p x - q x| = p x + q x - 2 * min (p x) (q x) := by
    intro x
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
  simp_rw [totalVariation, he, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, hp.2, hq.2]
  ring

end AKLT.W.GAP045

namespace AKLT.W.GAP045
attribute [local instance] Classical.propDecidable
local instance (α : Type) : DecidableEq α := Classical.decEq α
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

lemma tv_marginal {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    [DecidableEq Ξ] (p q : Weight Ω) (f : Ω → Ξ) :
    totalVariation (marginal p f) (marginal q f) ≤ totalVariation p q := by
  have h (b : Ξ) : |marginal p f b - marginal q f b| ≤
      marginal (fun x => |p x - q x|) f b := by
    unfold marginal
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ x, |(if f x = b then p x else 0) - (if f x = b then q x else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by apply Finset.sum_congr rfl; intro x _; split_ifs <;> simp
  unfold totalVariation
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact (Finset.sum_le_sum fun b _ => h b).trans_eq (marginal_total _ _)

end AKLT.W.GAP045
