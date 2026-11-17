module
public import AKLT.Blueprint.Mom.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Mom

namespace AKLT.W.MOM017

private theorem sum_if_subtype {Ω : Type*} [Fintype Ω] (P : Ω → Prop)
    [DecidablePred P] (f : Ω → ℝ) :
    (∑ x, if P x then f x else 0) = ∑ x : {x // P x}, f x := by
  classical
  calc
    (∑ x, if P x then f x else 0) = ∑ x, if x ∈ Finset.univ.filter P then f x else 0 := by
      congr 1
      funext x
      simp
    _ = ∑ x ∈ Finset.univ.filter P, f x := Finset.sum_ite_mem_eq _ _
    _ = ∑ x, if P x then f x else 0 := by rw [Finset.sum_filter]
    _ = ∑ x ∈ Finset.univ.filter P, f x := by rw [← Finset.sum_filter]
    _ = ∑ x : {x // P x}, f x :=
      Finset.sum_subtype (s := Finset.univ.filter P) (h := by simp) f

private def fibreConfig {n : ℕ} (x y : Fin n) (σ : Fin n → SpinLetter)
    (a b : SpinLetter) : Fin n → SpinLetter :=
  Function.update (Function.update σ x a) y b

private theorem fibreConfig_mem {n : ℕ} (x y : Fin n)
    (σ : Fin n → SpinLetter) (a b : SpinLetter) :
    twoSiteFibre x y σ (fibreConfig x y σ a b) := by
  intro z hzx hzy
  simp [fibreConfig, Function.update_of_ne hzy, Function.update_of_ne hzx]

private def fibreEquiv {n : ℕ} (x y : Fin n) (hxy : x ≠ y)
    (σ : Fin n → SpinLetter) :
    {τ : Fin n → SpinLetter // twoSiteFibre x y σ τ} ≃ SpinLetter × SpinLetter where
  toFun τ := (τ.1 x, τ.1 y)
  invFun ab := ⟨fibreConfig x y σ ab.1 ab.2, fibreConfig_mem x y σ ab.1 ab.2⟩
  left_inv := by
    intro τ
    apply Subtype.ext
    funext z
    by_cases hx : z = x
    · subst z
      simp [fibreConfig, hxy]
    · by_cases hy : z = y
      · subst z
        simp [fibreConfig]
      · calc
          fibreConfig x y σ (τ.1 x) (τ.1 y) z = σ z := by
            simp [fibreConfig, Function.update_of_ne hy, Function.update_of_ne hx]
          _ = τ.1 z := (τ.2 z hx hy).symm
  right_inv := by
    rintro ⟨a, b⟩
    simp [fibreConfig, Function.update_of_ne hxy, Function.update_self]

private theorem sum_on_fibre {n : ℕ} (x y : Fin n) (hxy : x ≠ y)
    (σ : Fin n → SpinLetter) (f : (Fin n → SpinLetter) → ℝ) :
    eventMass f (twoSiteFibre x y σ) =
      ∑ a : SpinLetter, ∑ b : SpinLetter, f (fibreConfig x y σ a b) := by
  classical
  unfold eventMass
  rw [sum_if_subtype]
  calc
    (∑ τ : {τ : Fin n → SpinLetter // twoSiteFibre x y σ τ}, f τ.1) =
        ∑ ab : SpinLetter × SpinLetter, f (fibreConfig x y σ ab.1 ab.2) :=
      Fintype.sum_equiv (fibreEquiv x y hxy σ) (fun τ => f τ.1)
        (fun ab => f (fibreConfig x y σ ab.1 ab.2)) (by
          intro τ
          congr 1
          exact (congrArg Subtype.val ((fibreEquiv x y hxy σ).left_inv τ)).symm)
    _ = ∑ a : SpinLetter, ∑ b : SpinLetter, f (fibreConfig x y σ a b) := by
      simp [Fintype.sum_prod_type]

private theorem eventMass_inter_fibre {n : ℕ} (x y : Fin n) (hxy : x ≠ y)
    (σ : Fin n → SpinLetter) (w : (Fin n → SpinLetter) → ℝ)
    (P : (Fin n → SpinLetter) → Prop) [DecidablePred P] :
    eventMass w (fun τ => twoSiteFibre x y σ τ ∧ P τ) =
      ∑ a : SpinLetter, ∑ b : SpinLetter,
        if P (fibreConfig x y σ a b) then w (fibreConfig x y σ a b) else 0 := by
  classical
  rw [show eventMass w (fun τ => twoSiteFibre x y σ τ ∧ P τ) =
      eventMass (fun τ => if P τ then w τ else 0) (twoSiteFibre x y σ) by
        unfold eventMass
        congr 1
        funext τ
        by_cases hf : twoSiteFibre x y σ τ <;> simp [hf]]
  rw [sum_on_fibre x y hxy σ]

private theorem sum_indicator_pair {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] (a : α) (b : β) (f : α → β → ℝ) :
    (∑ c, ∑ d, if c = a ∧ d = b then f c d else 0) = f a b := by
  classical
  calc
    (∑ c, ∑ d, if c = a ∧ d = b then f c d else 0) =
        ∑ c, if c = a then f c b else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : c = a
      · subst c
        simp only [true_and]
        rw [Fintype.sum_ite_eq' b (fun d => f a d)]
        simp
      · simp [h]
    _ = f a b := by rw [Fintype.sum_ite_eq' a]

private theorem sum_indicator_first {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] (a : α) (f : α → β → ℝ) :
    (∑ c, ∑ d, if c = a then f c d else 0) = ∑ d, f a d := by
  classical
  calc
    (∑ c, ∑ d, if c = a then f c d else 0) =
        ∑ c, if c = a then ∑ d, f c d else 0 := by
      apply Finset.sum_congr rfl
      intro c _
      by_cases h : c = a <;> simp [h]
    _ = ∑ d, f a d := by rw [Fintype.sum_ite_eq' a]

private theorem sum_indicator_second {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (b : β) (f : α → β → ℝ) :
    (∑ c, ∑ d, if d = b then f c d else 0) = ∑ c, f c b := by
  classical
  apply Finset.sum_congr rfl
  intro c _
  rw [Fintype.sum_ite_eq' b (fun d => f c d)]

private theorem eventMass_normalize {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (E : Ω → Prop) :
    AKLT.Defs.eventMass (AKLT.Defs.normalize w) E =
      AKLT.Defs.eventMass w E / ∑ x, w x := by
  classical
  unfold AKLT.Defs.eventMass AKLT.Defs.normalize
  simp_rw [div_eq_mul_inv]
  simpa [mul_ite] using
    (Finset.sum_mul (s := Finset.univ)
      (f := fun x => if E x then w x else 0) (∑ x, w x)⁻¹).symm

private theorem conditionalProbability_normalize {Ω : Type*} [Fintype Ω]
    (w : Ω → ℝ) (E A : Ω → Prop)
    (hE : 0 < eventMass (normalize w) E) :
    conditionalProbability (normalize w) E A =
      eventMass w (fun x => E x ∧ A x) / eventMass w E := by
  classical
  unfold conditionalProbability
  have hnum := eventMass_normalize w (fun x => E x ∧ A x)
  have hden := eventMass_normalize w E
  have hnum' : (∑ x, if E x ∧ A x then normalize w x else 0) =
      eventMass w (fun x => E x ∧ A x) / ∑ x, w x := by
    calc
      (∑ x, if E x ∧ A x then normalize w x else 0) =
          eventMass (normalize w) (fun x => E x ∧ A x) := by
        unfold eventMass
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : E x ∧ A x <;> simp [hx]
      _ = eventMass w (fun x => E x ∧ A x) / ∑ x, w x := hnum
  have hden' : (∑ x, if E x then normalize w x else 0) =
      eventMass w E / ∑ x, w x := by
    calc
      (∑ x, if E x then normalize w x else 0) =
          eventMass (normalize w) E := by
        unfold eventMass
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : E x <;> simp [hx]
      _ = eventMass w E / ∑ x, w x := hden
  rw [hnum', hden']
  have hT : (∑ x, w x) ≠ 0 := by
    intro hT
    rw [eventMass_normalize] at hE
    simp [hT] at hE
  have hM : eventMass w E ≠ 0 := by
    intro hM
    rw [eventMass_normalize] at hE
    simp [hM] at hE
  field_simp

private theorem factorized_sums {n : ℕ} (x y : Fin n) (hxy : x ≠ y)
    (σ : Fin n → SpinLetter) (w : (Fin n → SpinLetter) → ℝ)
    (C : ℝ) (u v : SpinLetter → ℝ)
    (hw : ∀ τ, twoSiteFibre x y σ τ → w τ = C * u (τ x) * v (τ y)) :
    let F := twoSiteFibre x y σ
    eventMass w F = C * (∑ a : SpinLetter, u a) * (∑ b : SpinLetter, v b) ∧
    (∀ a b, eventMass w (fun τ => F τ ∧ τ x = a ∧ τ y = b) = C * u a * v b) ∧
    (∀ a, eventMass w (fun τ => F τ ∧ τ x = a) = C * u a * ∑ b : SpinLetter, v b) ∧
    (∀ b, eventMass w (fun τ => F τ ∧ τ y = b) = C * (∑ a : SpinLetter, u a) * v b) := by
  classical
  let F : (Fin n → SpinLetter) → Prop := twoSiteFibre x y σ
  have hcx : ∀ a b, fibreConfig x y σ a b x = a := by
    intro a b
    simp [fibreConfig, hxy]
  have hcy : ∀ a b, fibreConfig x y σ a b y = b := by
    intro a b
    simp [fibreConfig]
  have hall : eventMass w F = ∑ a : SpinLetter, ∑ b : SpinLetter,
      C * u a * v b := by
    rw [sum_on_fibre x y hxy σ]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [hw _ (fibreConfig_mem x y σ a b), hcx, hcy]
  have hj : ∀ a b, eventMass w (fun τ => F τ ∧ τ x = a ∧ τ y = b) =
      C * u a * v b := by
    intro a b
    rw [eventMass_inter_fibre x y hxy σ w (fun τ => τ x = a ∧ τ y = b)]
    simp_rw [hw _ (fibreConfig_mem x y σ _ _), hcx, hcy]
    exact sum_indicator_pair a b (fun c d => C * u c * v d)
  have hl : ∀ a, eventMass w (fun τ => F τ ∧ τ x = a) =
      C * u a * ∑ b : SpinLetter, v b := by
    intro a
    rw [eventMass_inter_fibre x y hxy σ w (fun τ => τ x = a)]
    simp_rw [hw _ (fibreConfig_mem x y σ _ _), hcx, hcy]
    calc
      (∑ c : SpinLetter, ∑ d : SpinLetter,
          if c = a then C * u c * v d else 0) =
          ∑ d : SpinLetter, C * u a * v d := by
        simp
      _ = C * u a * ∑ d : SpinLetter, v d := by
        simpa [mul_assoc] using
          (Finset.mul_sum (s := Finset.univ) (f := v) (C * u a)).symm
  have hr : ∀ b, eventMass w (fun τ => F τ ∧ τ y = b) =
      C * (∑ a : SpinLetter, u a) * v b := by
    intro b
    rw [eventMass_inter_fibre x y hxy σ w (fun τ => τ y = b)]
    simp_rw [hw _ (fibreConfig_mem x y σ _ _), hcx, hcy]
    calc
      (∑ c : SpinLetter, ∑ d : SpinLetter,
          if d = b then C * u c * v d else 0) =
          ∑ c : SpinLetter, C * u c * v b := by
        simp
      _ = C * (∑ c : SpinLetter, u c) * v b := by
        calc
          (∑ c : SpinLetter, C * u c * v b) =
              (∑ c : SpinLetter, C * u c) * v b := by
            simpa using (Finset.sum_mul (s := Finset.univ)
              (f := fun c => C * u c) (v b)).symm
          _ = C * (∑ c : SpinLetter, u c) * v b := by
            rw [(Finset.mul_sum (s := Finset.univ) (f := u) C).symm]
  refine ⟨?_, hj, hl, hr⟩
  rw [hall]
  calc
    (∑ a : SpinLetter, ∑ b : SpinLetter, C * u a * v b) =
        ∑ a : SpinLetter, (C * u a) * ∑ b : SpinLetter, v b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.mul_sum]
    _ = C * (∑ a : SpinLetter, u a) * ∑ b : SpinLetter, v b := by
      calc
        (∑ a : SpinLetter, (C * u a) * ∑ b : SpinLetter, v b) =
            (∑ a : SpinLetter, C * u a) * ∑ b : SpinLetter, v b := by
          simpa using (Finset.sum_mul (s := Finset.univ)
            (f := fun a : SpinLetter => C * u a) (∑ b : SpinLetter, v b)).symm
        _ = C * (∑ a : SpinLetter, u a) * ∑ b : SpinLetter, v b := by
          rw [(Finset.mul_sum (s := Finset.univ) (f := u) C).symm]

theorem main : AKLT.Blueprint.Mom.FactorizedConditioningStatement := by
  classical
  intro n w hw x y hxy σ C u v hfactor hpos a b
  let F : (Fin n → SpinLetter) → Prop := twoSiteFibre x y σ
  obtain ⟨hmass, hjoint, hleft, hright⟩ :=
    factorized_sums x y hxy σ w C u v hfactor
  have htotalnonneg : 0 ≤ ∑ τ, w τ := Finset.sum_nonneg fun τ _ => hw τ
  have hnorm : eventMass (normalize w) F = eventMass w F / ∑ τ, w τ :=
    eventMass_normalize w F
  have hmasspos : 0 < eventMass w F := by
    have hpos' : 0 < eventMass (normalize w) F := by simpa [F] using hpos
    rw [hnorm] at hpos'
    rcases (div_pos_iff.mp hpos') with ⟨hm, _⟩ | ⟨hm, ht⟩
    · exact hm
    · linarith
  have hden : eventMass w F ≠ 0 := ne_of_gt hmasspos
  rw [conditionalProbability_normalize w F (fun τ => τ x = a ∧ τ y = b) hpos,
    conditionalProbability_normalize w F (fun τ => τ x = a) hpos,
    conditionalProbability_normalize w F (fun τ => τ y = b) hpos]
  rw [hjoint a b, hleft a, hright b, hmass]
  field_simp [hden]

end AKLT.W.MOM017

#print axioms AKLT.W.MOM017.main
