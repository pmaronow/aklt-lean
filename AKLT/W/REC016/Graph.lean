module
public import AKLT.W.REC016.Conditioning

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC016
namespace FiniteGraph

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]

def Inc (l r : β → α) (x : α) (e : β) : Prop := l e = x ∨ r e = x

instance (l r : β → α) (x : α) (e : β) : Decidable (Inc l r x e) :=
  inferInstanceAs (Decidable (_ ∨ _))

def other (l r : β → α) (x : α) (e : β) : α := if l e = x then r e else l e

def weight (s : α → Status) (l r : β → α) (P : (α → SpinLetter) → ℝ)
    (σ : α → SpinLetter) : ℝ :=
  (∏ z, spinWeight (s z) (σ z)) *
    (∏ e, (1 + dot (spinVector (σ (l e))) (spinVector (σ (r e))))) * P σ

theorem weight_nonneg (s : α → Status) (l r : β → α) (P : (α → SpinLetter) → ℝ)
    (hP : ∀ σ, 0 ≤ P σ) (σ : α → SpinLetter) : 0 ≤ weight s l r P σ := by
  apply mul_nonneg (mul_nonneg ?_ ?_) (hP σ)
  · exact Finset.prod_nonneg (fun z _ => spinWeight_nonneg _ _)
  · exact Finset.prod_nonneg (fun e _ => by
      have h := (ball_dot (spinVector (σ (l e))) (spinVector (σ (r e)))
          (spin_ball _) (spin_ball _)).1
      linarith)

theorem other_ne (l r : β → α) (hloop : ∀ e, l e ≠ r e)
    (x : α) (e : {e // Inc l r x e}) : other l r x e ≠ x := by
  by_cases h : l e = x
  · simp only [other, h, ↓reduceIte]
    intro he
    exact hloop e (h.trans he.symm)
  · simpa [other, h] using h

theorem other_ne_second (l r : β → α) (x y : α)
    (hsep : ∀ e, Inc l r x e → ¬Inc l r y e)
    (e : {e // Inc l r x e}) : other l r x e ≠ y := by
  have h := hsep e e.property
  by_cases hl : l e = x <;> simp only [other, hl, ↓reduceIte]
  · exact fun hr => h (Or.inr hr)
  · exact fun hh => h (Or.inl hh)

theorem refresh_other (l r : β → α) (hloop : ∀ e, l e ≠ r e)
    {x y : α} (hsep : ∀ e, Inc l r x e → ¬Inc l r y e)
    (σ : α → SpinLetter) (a b : SpinLetter) (e : {e // Inc l r x e}) :
    Function.update (Function.update σ x a) y b (other l r x e) = σ (other l r x e) := by
  rw [Function.update_of_ne (other_ne_second l r x y hsep e),
    Function.update_of_ne (other_ne l r hloop x e)]

theorem vertex_product (s : α → Status) {x y : α} (hxy : x ≠ y)
    (σ : α → SpinLetter) (a b : SpinLetter) :
    (∏ z, spinWeight (s z) (Function.update (Function.update σ x a) y b z)) =
      spinWeight (s x) a * spinWeight (s y) b *
        ∏ z ∈ (Finset.univ.erase x).erase y, spinWeight (s z) (σ z) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ x),
    ← Finset.mul_prod_erase (Finset.univ.erase x) _ (Finset.mem_erase.mpr
      ⟨hxy.symm, Finset.mem_univ y⟩)]
  simp only [Function.update_of_ne hxy, Function.update_self]
  rw [mul_assoc]
  congr 2
  apply Finset.prod_congr rfl
  intro z hz
  have hy := (Finset.mem_erase.mp hz).1
  have hx := (Finset.mem_erase.mp (Finset.mem_erase.mp hz).2).1
  rw [Function.update_of_ne hy, Function.update_of_ne hx]

theorem fibre_factorization (s : α → Status) (l r : β → α)
    (hloop : ∀ e, l e ≠ r e) {x y : α} (hxy : x ≠ y)
    (hsep : ∀ e, Inc l r x e → ¬Inc l r y e)
    (P : (α → SpinLetter) → ℝ) (hP : ∀ σ, 0 ≤ P σ)
    (hrefresh : ∀ σ a b, P (Function.update (Function.update σ x a) y b) = P σ)
    (σ : α → SpinLetter) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b,
      weight s l r P (Function.update (Function.update σ x a) y b) =
        C * (spinWeight (s x) a * ∏ e : {e // Inc l r x e},
          (1 + dot (spinVector a) (spinVector (σ (other l r x e))))) *
        (spinWeight (s y) b * ∏ e : {e // Inc l r y e},
          (1 + dot (spinVector b) (spinVector (σ (other l r y e))))) := by
  classical
  let C := (∏ z ∈ (Finset.univ.erase x).erase y, spinWeight (s z) (σ z)) *
    (∏ e : {e // ¬Inc l r x e ∧ ¬Inc l r y e},
      (1 + dot (spinVector (σ (l e))) (spinVector (σ (r e))))) * P σ
  refine ⟨C, ?_, ?_⟩
  · apply mul_nonneg (mul_nonneg ?_ ?_) (hP σ)
    · exact Finset.prod_nonneg (fun z _ => spinWeight_nonneg _ _)
    · exact Finset.prod_nonneg (fun e _ => by
        have h := (ball_dot (spinVector (σ (l e))) (spinVector (σ (r e)))
          (spin_ball _) (spin_ball _)).1
        linarith)
  · intro a b
    have hsep' : ∀ e, Inc l r y e → ¬Inc l r x e :=
      fun e hy hx => hsep e hx hy
    have hx (e : {e // Inc l r x e}) :
        1 + dot (spinVector (Function.update (Function.update σ x a) y b (l e)))
          (spinVector (Function.update (Function.update σ x a) y b (r e))) =
        1 + dot (spinVector a) (spinVector (σ (other l r x e))) := by
      have ho := refresh_other l r hloop hsep σ a b e
      by_cases hl : l e = x
      · simpa only [other, hl, ↓reduceIte, Function.update_of_ne hxy,
          Function.update_self] using congrArg (fun z => 1 + dot (spinVector a) (spinVector z)) ho
      · have hr : r e = x := e.property.resolve_left hl
        rw [show l e = other l r x e by simp [other, hl], ho, hr,
          Function.update_of_ne hxy, Function.update_self, dot_comm]
    have hy (e : {e // Inc l r y e}) :
        1 + dot (spinVector (Function.update (Function.update σ x a) y b (l e)))
          (spinVector (Function.update (Function.update σ x a) y b (r e))) =
        1 + dot (spinVector b) (spinVector (σ (other l r y e))) := by
      have ho : Function.update (Function.update σ x a) y b (other l r y e) =
          σ (other l r y e) := by
        rw [Function.update_of_ne (other_ne l r hloop y e),
          Function.update_of_ne (other_ne_second l r y x hsep' e)]
      by_cases hl : l e = y
      · simpa only [other, hl, ↓reduceIte, Function.update_self] using
          congrArg (fun z => 1 + dot (spinVector b) (spinVector z)) ho
      · have hr : r e = y := e.property.resolve_left hl
        rw [show l e = other l r y e by simp [other, hl], ho, hr,
          Function.update_self, dot_comm]
    have hoff (e : {e // ¬Inc l r x e ∧ ¬Inc l r y e}) :
        1 + dot (spinVector (Function.update (Function.update σ x a) y b (l e)))
          (spinVector (Function.update (Function.update σ x a) y b (r e))) =
        1 + dot (spinVector (σ (l e))) (spinVector (σ (r e))) := by
      have h := e.property
      simp only [Inc, not_or] at h
      rw [Function.update_of_ne h.2.1, Function.update_of_ne h.1.1,
        Function.update_of_ne h.2.2, Function.update_of_ne h.1.2]
    unfold weight
    rw [vertex_product s hxy, hrefresh,
      prod_partition3 (Inc l r x) (Inc l r y) hsep]
    simp_rw [hx, hy, hoff]
    dsimp [C]
    ring

theorem pair_lower (s : α → Status) (l r : β → α)
    (hloop : ∀ e, l e ≠ r e) {x y : α} (hxy : x ≠ y)
    (hsep : ∀ e, Inc l r x e → ¬Inc l r y e)
    (hxdeg : Fintype.card {e // Inc l r x e} ≤ 3)
    (hydeg : Fintype.card {e // Inc l r y e} ≤ 3)
    (hsx : s x = .U ∨ s x = .D) (hsy : s y = .U ∨ s y = .D)
    (P : (α → SpinLetter) → ℝ) (hP : ∀ σ, 0 ≤ P σ)
    (hrefresh : ∀ σ a b, P (Function.update (Function.update σ x a) y b) = P σ) :
    -(9 / 25 : ℝ) ≤
      (∑ σ, weight s l r P σ * dot (spinVector (σ x)) (spinVector (σ y))) /
        (∑ σ, weight s l r P σ) := by
  classical
  let H : (α → SpinLetter) → ℝ := fun σ => weight s l r P σ *
    (dot (spinVector (σ x)) (spinVector (σ y)) + 9 / 25)
  have hfibre (σ : α → SpinLetter) :
      0 ≤ ∑ a, ∑ b, H (Function.update (Function.update σ x a) y b) := by
    obtain ⟨C, hC, hfactor⟩ := fibre_factorization s l r hloop hxy hsep P hP hrefresh σ
    have hlocal := local_pair_lower hxdeg hydeg
      (fun e : {e // Inc l r x e} => spinVector (σ (other l r x e)))
      (fun e : {e // Inc l r y e} => spinVector (σ (other l r y e)))
      (fun _ => spin_ball _) (fun _ => spin_ball _) (s x) (s y) hsx hsy
    have heq : (∑ a, ∑ b, H (Function.update (Function.update σ x a) y b)) =
        C * (∑ a, ∑ b,
          (spinWeight (s x) a * ∏ e : {e // Inc l r x e},
            (1 + dot (spinVector a) (spinVector (σ (other l r x e))))) *
          (spinWeight (s y) b * ∏ e : {e // Inc l r y e},
            (1 + dot (spinVector b) (spinVector (σ (other l r y e))))) *
          (dot (spinVector a) (spinVector b) + 9 / 25)) := by
      dsimp [H]
      simp only [hfactor, Function.update_of_ne hxy, Function.update_self,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    rw [heq]
    exact mul_nonneg hC hlocal
  have htotal : 0 ≤ ∑ σ, H σ := by
    have h := Finset.sum_nonneg (fun σ (_ : σ ∈ Finset.univ) => hfibre σ)
    rw [sum_refresh_pair x y H] at h
    have hcard : 0 < (Fintype.card SpinLetter : ℝ)^2 := by
      norm_num [SpinLetter, IcoLetter, Fintype.card_option, Fintype.card_prod]
    exact (mul_nonneg_iff_of_pos_left hcard).mp h
  have hZ : 0 ≤ ∑ σ, weight s l r P σ :=
    Finset.sum_nonneg (fun σ _ => weight_nonneg s l r P hP σ)
  by_cases hz : (∑ σ, weight s l r P σ) = 0
  · norm_num [hz]
  · apply (le_div_iff₀ (lt_of_le_of_ne hZ (Ne.symm hz))).2
    dsimp [H] at htotal
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul] at htotal
    linarith

#print axioms pair_lower

end FiniteGraph
end AKLT.W.REC016
