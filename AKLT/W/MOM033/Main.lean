module
public import AKLT.Blueprint.Mom.NodesConsequences

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM033

private def fiberEquiv {n : ℕ} (x : Fin n) (σ : Fin n → SpinLetter) :
    SpinLetter ≃ {τ : Fin n → SpinLetter // AKLT.Blueprint.Mom.oneSiteFiber x σ τ} where
  toFun a := ⟨Function.update σ x a, by
    intro z hz
    exact Function.update_of_ne (a := z) (a' := x) hz a σ⟩
  invFun τ := τ.1 x
  left_inv := by intro a; simp [Function.update_self]
  right_inv := by
    intro τ
    apply Subtype.ext
    funext z
    by_cases hz : z = x
    · subst z
      simp [Function.update_self]
    · change Function.update σ x (τ.1 x) z = τ.1 z
      rw [Function.update_of_ne (a := z) (a' := x) hz]
      exact (τ.2 z hz).symm

private theorem sum_fiber {n : ℕ} (x : Fin n) (σ : Fin n → SpinLetter)
    (f : (Fin n → SpinLetter) → ℝ)
    [DecidablePred (fun τ : Fin n → SpinLetter => AKLT.Blueprint.Mom.oneSiteFiber x σ τ)] :
    (∑ τ, if AKLT.Blueprint.Mom.oneSiteFiber x σ τ then f τ else 0) =
      ∑ a : SpinLetter, f (Function.update σ x a) := by
  classical
  rw [Finset.sum_ite]
  simp only [Finset.sum_const_zero, add_zero]
  change (∑ τ ∈ Finset.univ.filter (fun τ : Fin n → SpinLetter =>
    AKLT.Blueprint.Mom.oneSiteFiber x σ τ), f τ) = _
  rw [@Finset.sum_subtype _ _ _ (fun τ : Fin n → SpinLetter =>
    AKLT.Blueprint.Mom.oneSiteFiber x σ τ) _ (Finset.univ.filter fun τ : Fin n → SpinLetter =>
    AKLT.Blueprint.Mom.oneSiteFiber x σ τ) (by intro τ; simp) f]
  symm
  exact Fintype.sum_equiv (fiberEquiv x σ) (fun a => f (Function.update σ x a))
    (fun τ => f τ.1) (by intro a; rfl)


private theorem golden_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold goldenRatio
  nlinarith

private theorem radius_sq : icoRadius ^ 2 = goldenRatio + 2 := by
  have hp : 0 ≤ goldenRatio + 2 := by
    unfold goldenRatio
    positivity
  exact Real.sq_sqrt hp

private theorem ico_norm (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hr : icoRadius ≠ 0 := by
    have hp : 0 < goldenRatio + 2 := by
      unfold goldenRatio
      positivity
    have hs : 0 < Real.sqrt (goldenRatio + 2) := Real.sqrt_pos.2 hp
    simpa [icoRadius] using hs.ne'
  rcases j with ⟨axis, s, t⟩
  fin_cases axis <;> fin_cases s <;> fin_cases t <;>
    simp [normSq, dot, icoVector, signValue, Fin.sum_univ_three] <;>
    field_simp [hr] <;> nlinarith [golden_sq, radius_sq]

private theorem spin_norm_le (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => simpa [spinVector] using (le_of_eq (ico_norm j))

private theorem dot_ball_lower (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have hcs : dot a b ^ 2 ≤ normSq a * normSq b := by
    simpa [dot, normSq, pow_two] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => a i) (fun i => b i)
  have hna : 0 ≤ normSq a := by
    unfold normSq dot
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))
  have hnb : 0 ≤ normSq b := by
    unfold normSq dot
    exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (b i))
  nlinarith [sq_nonneg (dot a b)]

private theorem network_weight_nonneg {n : ℕ} (D : FiniteSpinNetwork n)
    (hD : D.Valid) (pinned : Bool) (σ : Fin n → SpinLetter) : 0 ≤ D.weight pinned σ := by
  classical
  unfold FiniteSpinNetwork.weight
  apply mul_nonneg
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro x hx
      have hs := hD.1 x
      rcases hs with hs | hs <;> cases σ x <;> norm_num [spinWeight, hs]
    · apply Finset.prod_nonneg
      intro e he
      apply dot_ball_lower <;> exact spin_norm_le _
  · apply Finset.prod_nonneg
    intro x hx
    apply Finset.prod_nonneg
    intro j hj
    cases pinned with
    | false => norm_num
    | true => exact dot_ball_lower _ _ (le_of_eq (D.pin x j).property) (spin_norm_le _)


private def incidentAt {n : ℕ} (x : Fin n) (e : Fin n × Fin n) : Prop :=
  e.1 = x ∨ e.2 = x

private def edgeNeighbor {n : ℕ} (x : Fin n) (σ : Fin n → SpinLetter)
    (e : Fin n × Fin n) : SpinLetter :=
  if e.1 = x then σ e.2 else σ e.1

private theorem dot_comm3 (a b : Vec3) : dot a b = dot b a := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i hi
  ring

private theorem incident_factor {n : ℕ} (D : FiniteSpinNetwork n)
    (hD : D.Valid) (x : Fin n) (σ τ : Fin n → SpinLetter)
    (hτ : AKLT.Blueprint.Mom.oneSiteFiber x σ τ)
    (e : Fin n × Fin n) (heB : e ∈ D.bonds) (heI : incidentAt x e) :
    1 + dot (spinVector (τ e.1)) (spinVector (τ e.2)) =
      1 + dot (spinVector (τ x)) (spinVector (edgeNeighbor x σ e)) := by
  have horient := hD.2.1 e heB
  rcases heI with hfirst | hsecond
  · have hother : e.2 ≠ x := by
      intro h
      simp [hfirst, h] at horient
    have hfixed := hτ e.2 hother
    simp [edgeNeighbor, hfirst, hfixed]
  · have hother : e.1 ≠ x := by
      intro h
      simp [h, hsecond] at horient
    have hfixed := hτ e.1 hother
    rw [edgeNeighbor]
    simp [hother, hsecond, hfixed]
    rw [dot_comm3]

private theorem fiber_weight_factorization {n : ℕ} (D : FiniteSpinNetwork n)
    (hD : D.Valid) (pinned : Bool) (x : Fin n) (hpin : D.pinCount x = 0)
    (hdeg : (D.bonds.filter (fun e => e.1 = x ∨ e.2 = x)).card ≤ 3)
    (σ : Fin n → SpinLetter) :
    ∃ k : ℕ, k ≤ 3 ∧ ∃ a : Fin k → Vec3,
      (∀ j, normSq (a j) ≤ 1) ∧ ∃ C : ℝ, ∀ τ,
        AKLT.Blueprint.Mom.oneSiteFiber x σ τ →
        D.weight pinned τ = C *
          (spinWeight (D.status x) (τ x) * localProduct a (spinVector (τ x))) := by
  classical
  let I := D.bonds.filter (incidentAt x)
  let k := Fintype.card {e : Fin n × Fin n // e ∈ I}
  let eFin : {e : Fin n × Fin n // e ∈ I} ≃ Fin k := Fintype.equivFin _
  let a : Fin k → Vec3 := fun j => spinVector (edgeNeighbor x σ (eFin.symm j).1)
  have hI : I = D.bonds.filter (fun e => e.1 = x ∨ e.2 = x) := by
    ext e
    simp [I, incidentAt]
  have hk : k ≤ 3 := by
    dsimp [k]
    rw [Fintype.card_coe, hI]
    exact hdeg
  have ha : ∀ j, normSq (a j) ≤ 1 := by
    intro j
    exact spin_norm_le _
  let siteExt : ℝ := ∏ z ∈ Finset.univ.erase x, spinWeight (D.status z) (σ z)
  let edgeExt : ℝ := ∏ e ∈ D.bonds.filter (fun e => ¬ incidentAt x e),
    (1 + dot (spinVector (σ e.1)) (spinVector (σ e.2)))
  let pinExt : ℝ := ∏ z ∈ Finset.univ.erase x, ∏ j : Fin (D.pinCount z),
    if pinned then 1 + dot (D.pin z j).val (spinVector (σ z)) else 1
  let C := siteExt * edgeExt * pinExt
  have hlocal (τ : Fin n → SpinLetter) (hτ : AKLT.Blueprint.Mom.oneSiteFiber x σ τ) :
      localProduct a (spinVector (τ x)) =
        ∏ e ∈ I, (1 + dot (spinVector (τ x)) (spinVector (edgeNeighbor x σ e))) := by
    unfold localProduct
    calc
      (∏ j : Fin k, (1 + dot (spinVector (τ x)) (a j))) =
          ∏ e : {e : Fin n × Fin n // e ∈ I},
            (1 + dot (spinVector (τ x)) (spinVector (edgeNeighbor x σ e.1))) := by
          exact Fintype.prod_equiv eFin.symm
            (fun j : Fin k => 1 + dot (spinVector (τ x)) (a j))
            (fun e : {e : Fin n × Fin n // e ∈ I} =>
              1 + dot (spinVector (τ x)) (spinVector (edgeNeighbor x σ e.1)))
            (by intro j; rfl)
      _ = ∏ e ∈ I, (1 + dot (spinVector (τ x)) (spinVector (edgeNeighbor x σ e))) := by
          simpa using (Finset.prod_coe_sort I
            (fun e : Fin n × Fin n => 1 + dot (spinVector (τ x))
              (spinVector (edgeNeighbor x σ e))))
  have hsite (τ : Fin n → SpinLetter) (hτ : AKLT.Blueprint.Mom.oneSiteFiber x σ τ) :
      (∏ z, spinWeight (D.status z) (τ z)) =
        spinWeight (D.status x) (τ x) * siteExt := by
    rw [← Finset.mul_prod_erase Finset.univ (fun z => spinWeight (D.status z) (τ z))
      (Finset.mem_univ x)]
    dsimp [siteExt]
    congr 1
    apply Finset.prod_congr rfl
    intro z hz
    have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
    rw [hτ z hzx]
  have hedge (τ : Fin n → SpinLetter) (hτ : AKLT.Blueprint.Mom.oneSiteFiber x σ τ) :
      (∏ e ∈ D.bonds, (1 + dot (spinVector (τ e.1)) (spinVector (τ e.2)))) =
        (∏ e ∈ I, (1 + dot (spinVector (τ e.1)) (spinVector (τ e.2)))) * edgeExt := by
    rw [← Finset.prod_filter_mul_prod_filter_not D.bonds (incidentAt x)
      (fun e => 1 + dot (spinVector (τ e.1)) (spinVector (τ e.2)))]
    dsimp [I, edgeExt]
    congr 1
    apply Finset.prod_congr rfl
    intro e he
    have hnot := (Finset.mem_filter.mp he).2
    have he1 : e.1 ≠ x := by intro hx; exact hnot (Or.inl hx)
    have he2 : e.2 ≠ x := by intro hx; exact hnot (Or.inr hx)
    rw [hτ e.1 he1, hτ e.2 he2]
  have hpinprod (τ : Fin n → SpinLetter) (hτ : AKLT.Blueprint.Mom.oneSiteFiber x σ τ) :
      (∏ z, ∏ j : Fin (D.pinCount z),
        if pinned then 1 + dot (D.pin z j).val (spinVector (τ z)) else 1) = pinExt := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun z => ∏ j : Fin (D.pinCount z),
        if pinned then 1 + dot (D.pin z j).val (spinVector (τ z)) else 1)
      (Finset.mem_univ x)]
    have hxpin : (∏ j : Fin (D.pinCount x),
        if pinned then 1 + dot (D.pin x j).val (spinVector (τ x)) else 1) = 1 := by
      simp [hpin]
    rw [hxpin]
    dsimp [pinExt]
    simp only [one_mul]
    apply Finset.prod_congr rfl
    intro z hz
    have hzx : z ≠ x := (Finset.mem_erase.mp hz).1
    apply Finset.prod_congr rfl
    intro j hj
    rw [hτ z hzx]
  have hincidentProd (τ : Fin n → SpinLetter)
      (hτ : AKLT.Blueprint.Mom.oneSiteFiber x σ τ) :
      (∏ e ∈ I, (1 + dot (spinVector (τ e.1)) (spinVector (τ e.2)))) =
        ∏ e ∈ I, (1 + dot (spinVector (τ x)) (spinVector (edgeNeighbor x σ e))) := by
    apply Finset.prod_congr rfl
    intro e he
    have he' := Finset.mem_filter.mp he
    exact incident_factor D hD x σ τ hτ e he'.1 he'.2
  refine ⟨k, hk, a, ha, C, ?_⟩
  intro τ hτ
  unfold FiniteSpinNetwork.weight
  rw [hsite τ hτ, hedge τ hτ, hpinprod τ hτ]
  rw [hincidentProd τ hτ, ← hlocal τ hτ]
  dsimp [C, siteExt, edgeExt, pinExt]
  ring


private theorem siteWeight_nonneg_active (s : Status) (hs : s = .U ∨ s = .D)
    (u : SpinLetter) : 0 ≤ spinWeight s u := by
  rcases hs with rfl | rfl <;> cases u <;> norm_num [spinWeight]

private theorem localProduct_nonneg {k : ℕ} (a : Fin k → Vec3)
    (ha : ∀ j, normSq (a j) ≤ 1) (u : SpinLetter) :
    0 ≤ localProduct a (spinVector u) := by
  unfold localProduct
  apply Finset.prod_nonneg
  intro j hj
  exact dot_ball_lower _ _ (spin_norm_le u) (ha j)

private theorem siteFunctional_local_nonneg {k : ℕ} (s : Status)
    (hs : s = .U ∨ s = .D) (a : Fin k → Vec3)
    (ha : ∀ j, normSq (a j) ≤ 1) :
    0 ≤ siteFunctional s (localProduct a) := by
  unfold siteFunctional
  apply Finset.sum_nonneg
  intro u hu
  exact mul_nonneg (siteWeight_nonneg_active s hs u) (localProduct_nonneg a ha u)

theorem normalized_indicator_sum {α : Type} [Fintype α]
    (E : α → Prop) [DecidablePred E] (w : α → ℝ) (g : α → ℝ)
    (hZ : (∑ y, w y) ≠ 0) :
    (∑ x, if E x then AKLT.Defs.normalize w x * g x else 0) =
      (∑ x, if E x then w x * g x else 0) / (∑ y, w y) := by
  classical
  unfold AKLT.Defs.normalize
  calc
    (∑ x, if E x then w x / (∑ y, w y) * g x else 0) =
        ∑ x, (if E x then w x * g x else 0) / (∑ y, w y) := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hE : E x
      · simp [hE]
        field_simp [hZ]
      · simp [hE]
    _ = (∑ x, if E x then w x * g x else 0) / (∑ y, w y) := by
      symm
      exact Finset.sum_div Finset.univ (fun x => if E x then w x * g x else 0)
        (∑ y, w y)

private theorem update_fiber {n : ℕ} (x : Fin n) (σ : Fin n → SpinLetter)
    (u : SpinLetter) :
    AKLT.Blueprint.Mom.oneSiteFiber x σ (Function.update σ x u) := by
  intro z hz
  exact Function.update_of_ne (a := z) (a' := x) hz u σ

end AKLT.W.MOM033

namespace AKLT.W.MOM033

theorem main : AKLT.Blueprint.Mom.OneSiteConditionalReductionStatement := by
  classical
  intro n D hD pinned x hpin hdeg σ hMass
  obtain ⟨k, hk, fields, hfields, C, hfactor⟩ :=
    fiber_weight_factorization D hD pinned x hpin hdeg σ
  let Z : ℝ := ∑ τ, D.weight pinned τ
  have hZnon : 0 ≤ Z := by
    dsimp [Z]
    exact Finset.sum_nonneg (fun τ _ => network_weight_nonneg D hD pinned τ)
  have hZne : Z ≠ 0 := by
    intro hz
    have hzsum : (∑ τ, D.weight pinned τ) = 0 := by simpa [Z] using hz
    have hzero : eventMass (AKLT.Defs.normalize (D.weight pinned))
        (AKLT.Blueprint.Mom.oneSiteFiber x σ) = 0 := by
      unfold eventMass
      simp [AKLT.Defs.normalize, hzsum]
    exact (ne_of_gt hMass) hzero
  have hZpos : 0 < Z := by
    rcases lt_or_eq_of_le hZnon with h | h
    · exact h
    · exact False.elim (hZne h.symm)
  let M : ℝ := ∑ τ, if AKLT.Blueprint.Mom.oneSiteFiber x σ τ then
    D.weight pinned τ else 0
  have hmassNorm : eventMass (AKLT.Defs.normalize (D.weight pinned))
      (AKLT.Blueprint.Mom.oneSiteFiber x σ) = M / Z := by
    simpa [eventMass, M, Z] using
      AKLT.W.MOM033.normalized_indicator_sum
        (AKLT.Blueprint.Mom.oneSiteFiber x σ) (D.weight pinned) (fun _ => 1) hZne
  have hMpos : 0 < M := by
    have hdiv : 0 < M / Z := by rw [← hmassNorm]; exact hMass
    rcases (div_pos_iff.mp hdiv) with ⟨hM, hZ⟩ | ⟨hM, hZ⟩
    · exact hM
    · linarith
  have hA_nonneg : 0 ≤ siteFunctional (D.status x) (localProduct fields) :=
    siteFunctional_local_nonneg (D.status x) (hD.1 x) fields hfields
  let A : ℝ := siteFunctional (D.status x) (localProduct fields)
  have hMfactor : M = C * A := by
    dsimp [M]
    rw [sum_fiber x σ (fun τ => D.weight pinned τ)]
    calc
      (∑ u : SpinLetter, D.weight pinned (Function.update σ x u)) =
          ∑ u : SpinLetter, C *
            (spinWeight (D.status x) u * localProduct fields (spinVector u)) := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [hfactor _ (update_fiber x σ u)]
          simp [Function.update_self]
      _ = C * A := by
          unfold A siteFunctional
          rw [← Finset.mul_sum]
  have hApos : 0 < A := by
    have hAne : A ≠ 0 := by
      intro hA0
      rw [hMfactor, hA0] at hMpos
      norm_num at hMpos
    exact lt_of_le_of_ne hA_nonneg (Ne.symm hAne)
  have hCpos : 0 < C := by
    have hprod : 0 < C * A := by rw [← hMfactor]; exact hMpos
    exact (mul_pos_iff_of_pos_right hApos).mp hprod
  have hMne : M ≠ 0 := ne_of_gt hMpos
  have hCne : C ≠ 0 := ne_of_gt hCpos
  refine ⟨k, hk, fields, hfields, hApos, ?_⟩
  funext i
  let N : ℝ := ∑ τ, if AKLT.Blueprint.Mom.oneSiteFiber x σ τ then
    D.weight pinned τ * spinVector (τ x) i else 0
  let B : ℝ := siteFunctional (D.status x)
    (fun v => v i * localProduct fields v)
  have hNfactor : N = C * B := by
    dsimp [N]
    rw [sum_fiber x σ (fun τ => D.weight pinned τ * spinVector (τ x) i)]
    calc
      (∑ u : SpinLetter,
        D.weight pinned (Function.update σ x u) * spinVector
          ((Function.update σ x u) x) i) =
          ∑ u : SpinLetter, C *
            (spinWeight (D.status x) u * localProduct fields (spinVector u)) *
              spinVector u i := by
          apply Finset.sum_congr rfl
          intro u hu
          rw [hfactor _ (update_fiber x σ u)]
          simp [Function.update_self]
      _ = C * B := by
          unfold B siteFunctional
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro u hu
          ring
  have hnumNorm :
      (∑ τ, if AKLT.Blueprint.Mom.oneSiteFiber x σ τ then
        AKLT.Defs.normalize (D.weight pinned) τ * spinVector (τ x) i else 0) = N / Z := by
    rw [AKLT.W.MOM033.normalized_indicator_sum (AKLT.Blueprint.Mom.oneSiteFiber x σ)
      (D.weight pinned) (fun τ => spinVector (τ x) i) hZne]
  change
    ((∑ τ, if AKLT.Blueprint.Mom.oneSiteFiber x σ τ then
        AKLT.Defs.normalize (D.weight pinned) τ * spinVector (τ x) i else 0) /
      eventMass (AKLT.Defs.normalize (D.weight pinned)) (AKLT.Blueprint.Mom.oneSiteFiber x σ)) =
      (siteFunctional (D.status x) (fun v => v i * localProduct fields v)) /
        siteFunctional (D.status x) (localProduct fields)
  rw [hnumNorm, hmassNorm, hNfactor, hMfactor]
  change ((C * B / Z) / (C * A / Z)) = B / A
  field_simp [hZne, hCne, hApos.ne']

end AKLT.W.MOM033

