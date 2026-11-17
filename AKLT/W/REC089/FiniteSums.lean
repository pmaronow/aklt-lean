module
public import AKLT.W.REC089.Template

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC089

attribute [local instance] Classical.propDecidable

@[simp] theorem joinSpins_inside {ι : Type} (p : ι → Prop) [DecidablePred p]
    (η : {x // p x} → SpinLetter) (ω : {x // ¬p x} → SpinLetter) (x : {x // p x}) :
    joinSpins p η ω x.val = η x := by
  simp [joinSpins, Equiv.piEquivPiSubtypeProd, x.property]

@[simp] theorem joinSpins_outside {ι : Type} (p : ι → Prop) [DecidablePred p]
    (η : {x // p x} → SpinLetter) (ω : {x // ¬p x} → SpinLetter) (x : {x // ¬p x}) :
    joinSpins p η ω x.val = ω x := by
  simp [joinSpins, Equiv.piEquivPiSubtypeProd, x.property]

/-- Splitting spin coordinates along an arbitrary finite disjoint union. -/
def sumAssignmentEquiv {A C T : Type} (e : A ≃ C ⊕ T) :
    (A → SpinLetter) ≃ (C → SpinLetter) × (T → SpinLetter) where
  toFun n := (fun c => n (e.symm (.inl c)), fun t => n (e.symm (.inr t)))
  invFun p := fun a => Sum.elim p.1 p.2 (e a)
  left_inv n := by
    funext a
    cases h : e a with
    | inl c =>
      simp only [h, Sum.elim_inl]
      exact congrArg n ((congrArg e.symm h).symm.trans (e.symm_apply_apply a))
    | inr t =>
      simp only [h, Sum.elim_inr]
      exact congrArg n ((congrArg e.symm h).symm.trans (e.symm_apply_apply a))
  right_inv p := by
    apply Prod.ext <;> funext x <;> simp

/-- A finite sum with independent leaves can be evaluated one leaf at a time. -/
theorem sum_eliminate_leaves {A C T : Type} [Fintype A] [Fintype C] [Fintype T]
    [DecidableEq A] [DecidableEq C] [DecidableEq T]
    (e : A ≃ C ⊕ T) (w : A → SpinLetter → ℝ)
    (K : (C → SpinLetter) → ℝ)
    (L : (C → SpinLetter) → T → SpinLetter → ℝ) :
    (∑ n : A → SpinLetter, (∏ a, w a (n a)) *
      K (fun c => n (e.symm (.inl c))) *
      ∏ t, L (fun c => n (e.symm (.inl c))) t (n (e.symm (.inr t)))) =
    ∑ σ : C → SpinLetter, (∏ c, w (e.symm (.inl c)) (σ c)) * K σ *
      ∏ t, ∑ d : SpinLetter, w (e.symm (.inr t)) d * L σ t d := by
  classical
  rw [← (sumAssignmentEquiv e).symm.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro σ _
  have hprod (d : T → SpinLetter) :
      (∏ a, w a ((sumAssignmentEquiv e).symm (σ, d) a)) =
        (∏ c, w (e.symm (.inl c)) (σ c)) *
        ∏ t, w (e.symm (.inr t)) (d t) := by
    rw [← e.symm.prod_comp, Fintype.prod_sum_type]
    simp [sumAssignmentEquiv]
  simp_rw [hprod]
  simp only [sumAssignmentEquiv, Equiv.coe_fn_symm_mk, Equiv.apply_symm_apply,
    Sum.elim_inl, Sum.elim_inr]
  rw [Fintype.prod_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.prod_mul_distrib]
  ring

#print axioms sum_eliminate_leaves

end AKLT.W.REC089
