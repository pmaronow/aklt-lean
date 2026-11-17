module
public import AKLT.Blueprint.Mom.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.MOM016

private lemma goldenRatio_sq : goldenRatio ^ 2 = goldenRatio + 1 := by
  have h5 : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold goldenRatio
  nlinarith

private lemma icoVector_normSq (j : IcoLetter) : normSq (icoVector j) = 1 := by
  have hphi : 0 < goldenRatio := by
    unfold goldenRatio
    positivity
  have hr : icoRadius ^ 2 = goldenRatio + 2 := by
    unfold icoRadius
    rw [Real.sq_sqrt (by linarith : 0 ≤ goldenRatio + 2)]
  rcases j with ⟨k, s, t⟩
  fin_cases k <;> fin_cases s <;> fin_cases t <;>
    simp [normSq, dot, icoVector, signValue, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt (Real.sqrt_pos.2 (by linarith : 0 < goldenRatio + 2))] <;>
    rw [hr] <;> rw [goldenRatio_sq] <;>
    field_simp [ne_of_gt (by linarith : 0 < goldenRatio + 2)] <;> ring

private lemma spinVector_normSq_le_one (a : SpinLetter) : normSq (spinVector a) ≤ 1 := by
  cases a with
  | none => norm_num [spinVector, normSq, dot]
  | some j => simpa [spinVector] using le_of_eq (icoVector_normSq j)

private lemma ball_dot_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have hsq : 0 ≤ normSq (fun i => a i + b i) := AKLT.Blueprint.Mom.normSq_nonneg _
  have hid : normSq (fun i => a i + b i) = normSq a + 2 * dot a b + normSq b := by
    calc
      normSq (fun i => a i + b i) =
          ∑ i, (a i * a i + 2 * (a i * b i) + b i * b i) := by
        unfold normSq dot
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = normSq a + 2 * dot a b + normSq b := by
        simp [normSq, dot, Finset.sum_add_distrib, Finset.mul_sum]
  linarith

private lemma ballDotBounds : AKLT.Blueprint.Mom.BallDotBoundsStatement := by
  intro a b ha hb
  refine ⟨ball_dot_nonneg a b ha hb, ?_⟩
  have hba := ball_dot_nonneg a (-b) ha (by simpa [normSq, dot] using hb)
  have hd : dot a (-b) = -dot a b := by
    simp [dot]
  rw [hd] at hba
  linarith


private lemma prod_split_two {α : Type*} [DecidableEq α] (s : Finset α)
    (p q : α → Prop) [DecidablePred p] [DecidablePred q]
    (hpq : ∀ a ∈ s, p a → ¬ q a) (f : α → ℝ) :
    (∏ a ∈ s, f a) =
      (∏ a ∈ s.filter p, f a) * (∏ a ∈ s.filter q, f a) *
        ∏ a ∈ s.filter (fun a => ¬ p a ∧ ¬ q a), f a := by
  classical
  have hq : s.filter q = (s.filter (fun a => ¬ p a)).filter q := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨ha, hqa⟩
      exact ⟨⟨ha, fun hpa => hpq a ha hpa hqa⟩, hqa⟩
    · rintro ⟨⟨ha, _⟩, hqa⟩
      exact ⟨ha, hqa⟩
  have hrest : (s.filter (fun a => ¬ p a)).filter (fun a => ¬ q a) =
      s.filter (fun a => ¬ p a ∧ ¬ q a) := by
    ext a
    simp only [Finset.mem_filter]
    tauto
  calc
    (∏ a ∈ s, f a) =
        (∏ a ∈ s.filter p, f a) * ∏ a ∈ s.filter (fun a => ¬ p a), f a :=
      (Finset.prod_filter_mul_prod_filter_not s p f).symm
    _ = (∏ a ∈ s.filter p, f a) *
        ((∏ a ∈ (s.filter (fun a => ¬ p a)).filter q, f a) *
          ∏ a ∈ (s.filter (fun a => ¬ p a)).filter (fun a => ¬ q a), f a) := by
      exact congrArg (fun t : ℝ => (∏ a ∈ s.filter p, f a) * t)
        ((Finset.prod_filter_mul_prod_filter_not
          (s := s.filter (fun a => ¬ p a)) (p := q) (f := f)).symm)
    _ = (∏ a ∈ s.filter p, f a) * (∏ a ∈ s.filter q, f a) *
        ∏ a ∈ s.filter (fun a => ¬ p a ∧ ¬ q a), f a := by
      rw [← hq, ← hrest]
      ring

private lemma prod_split_sites {n : ℕ} (f : Fin n → ℝ) (x y : Fin n) (hxy : x ≠ y) :
    (∏ z, f z) = f x * f y *
      ∏ z ∈ (Finset.univ : Finset (Fin n)).filter (fun z => z ≠ x ∧ z ≠ y), f z := by
  classical
  have h := prod_split_two (s := (Finset.univ : Finset (Fin n)))
    (fun z => z = x) (fun z => z = y)
    (by
      intro z hz hx hy
      exact hxy (hx.symm.trans hy)) f
  have hxset : (Finset.univ : Finset (Fin n)).filter (fun z => z = x) = {x} := by
    ext z
    simp
  have hyset : (Finset.univ : Finset (Fin n)).filter (fun z => z = y) = {y} := by
    ext z
    simp
  have hx : (∏ z ∈ (Finset.univ : Finset (Fin n)).filter (fun z => z = x), f z) = f x := by
    rw [hxset]
    simp
  have hy : (∏ z ∈ (Finset.univ : Finset (Fin n)).filter (fun z => z = y), f z) = f y := by
    rw [hyset]
    simp
  simpa [hx, hy] using h

private def siteMass {n : ℕ} (D : FiniteSpinNetwork n) (σ : Fin n → SpinLetter)
    (z : Fin n) : ℝ := spinWeight (D.status z) (σ z)

private def pinMass {n : ℕ} (D : FiniteSpinNetwork n) (pinned : Bool)
    (σ : Fin n → SpinLetter) (z : Fin n) : ℝ :=
  ∏ j : Fin (D.pinCount z),
    if pinned then 1 + dot (D.pin z j).val (spinVector (σ z)) else 1

private def edgeAt {n : ℕ} (σ : Fin n → SpinLetter) (e : Fin n × Fin n) : ℝ :=
  1 + dot (spinVector (σ e.1)) (spinVector (σ e.2))

private def offSites {n : ℕ} (D : FiniteSpinNetwork n) (σ : Fin n → SpinLetter)
    (x y : Fin n) : ℝ :=
  ∏ z ∈ (Finset.univ : Finset (Fin n)).filter (fun z => z ≠ x ∧ z ≠ y), siteMass D σ z

private def incident {n : ℕ} (x : Fin n) (e : Fin n × Fin n) : Prop :=
  e.1 = x ∨ e.2 = x

private instance incidentDecidable {n : ℕ} (x : Fin n) : DecidablePred (incident x) := by
  intro e
  classical
  exact Classical.propDecidable _

private def offEdges {n : ℕ} (D : FiniteSpinNetwork n) (σ : Fin n → SpinLetter)
    (x y : Fin n) : ℝ := by
  classical
  exact ∏ e ∈ D.bonds.filter (fun e => ¬ incident x e ∧ ¬ incident y e), edgeAt σ e

private def offPins {n : ℕ} (D : FiniteSpinNetwork n) (pinned : Bool)
    (σ : Fin n → SpinLetter) (x y : Fin n) : ℝ :=
  ∏ z ∈ (Finset.univ : Finset (Fin n)).filter (fun z => z ≠ x ∧ z ≠ y),
    pinMass D pinned σ z

private def localFactor {n : ℕ} (D : FiniteSpinNetwork n) (pinned : Bool)
    (σ : Fin n → SpinLetter) (x : Fin n) (a : SpinLetter) : ℝ := by
  classical
  exact spinWeight (D.status x) a *
    (∏ e ∈ D.bonds.filter (incident x), edgeAt (Function.update σ x a) e) *
    pinMass D pinned (Function.update σ x a) x

private def offFactor {n : ℕ} (D : FiniteSpinNetwork n) (pinned : Bool)
    (σ : Fin n → SpinLetter) (x y : Fin n) : ℝ :=
  offSites D σ x y * offEdges D σ x y * offPins D pinned σ x y

private lemma edgeFactor_nonneg {n : ℕ} (σ : Fin n → SpinLetter) (e : Fin n × Fin n) :
    0 ≤ edgeAt σ e := by
  exact ball_dot_nonneg _ _ (spinVector_normSq_le_one _) (spinVector_normSq_le_one _)

private lemma siteMass_nonneg {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid)
    (σ : Fin n → SpinLetter) (z : Fin n) : 0 ≤ siteMass D σ z := by
  exact (AKLT.Blueprint.Mom.siteWeight (D.status z) (hD.1 z)).1 (σ z)

private lemma pinMass_nonneg {n : ℕ} (D : FiniteSpinNetwork n) (pinned : Bool)
    (σ : Fin n → SpinLetter) (z : Fin n) : 0 ≤ pinMass D pinned σ z := by
  unfold pinMass
  apply Finset.prod_nonneg
  intro j hj
  cases pinned with
  | false => norm_num
  | true =>
    exact ball_dot_nonneg _ _ (le_of_eq (D.pin z j).property) (spinVector_normSq_le_one _)

private lemma offFactor_nonneg {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid)
    (pinned : Bool) (σ : Fin n → SpinLetter) (x y : Fin n) :
    0 ≤ offFactor D pinned σ x y := by
  unfold offFactor offSites offEdges offPins
  apply mul_nonneg
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro z hz
      exact siteMass_nonneg D hD σ z
    · apply Finset.prod_nonneg
      intro e he
      exact edgeFactor_nonneg σ e
  · apply Finset.prod_nonneg
    intro z hz
    exact pinMass_nonneg D pinned σ z

private lemma localFactor_nonneg {n : ℕ} (D : FiniteSpinNetwork n) (hD : D.Valid)
    (pinned : Bool) (σ : Fin n → SpinLetter) (x : Fin n) (a : SpinLetter) :
    0 ≤ localFactor D pinned σ x a := by
  unfold localFactor
  apply mul_nonneg
  · apply mul_nonneg
    · exact (AKLT.Blueprint.Mom.siteWeight (D.status x) (hD.1 x)).1 a
    · apply Finset.prod_nonneg
      intro e he
      exact edgeFactor_nonneg (Function.update σ x a) e
  · exact pinMass_nonneg D pinned (Function.update σ x a) x


private lemma bond_products_split {n : ℕ} (D : FiniteSpinNetwork n) (x y : Fin n)
    (hxy : x ≠ y) (hxy1 : (x, y) ∉ D.bonds) (hxy2 : (y, x) ∉ D.bonds)
    (σ : Fin n → SpinLetter) :
    (∏ e ∈ D.bonds, edgeAt σ e) =
      (∏ e ∈ D.bonds.filter (incident x), edgeAt σ e) *
      (∏ e ∈ D.bonds.filter (incident y), edgeAt σ e) *
      (∏ e ∈ D.bonds.filter (fun e => ¬ incident x e ∧ ¬ incident y e), edgeAt σ e) := by
  classical
  exact prod_split_two D.bonds (incident x) (incident y)
    (by
      intro e he hx hy
      rcases hx with hx1 | hx2 <;> rcases hy with hy1 | hy2
      · exact hxy (hx1.symm.trans hy1)
      · apply hxy1
        have heq : e = (x, y) := Prod.ext hx1 hy2
        simpa [heq] using he
      · apply hxy2
        have heq : e = (y, x) := Prod.ext hy1 hx2
        simpa [heq] using he
      · exact hxy (hx2.symm.trans hy2))
    (edgeAt σ)

private lemma update_agrees_off {n : ℕ} (σ τ : Fin n → SpinLetter) (x y : Fin n)
    (a : SpinLetter) (hτ : AKLT.Blueprint.Mom.twoSiteFiber x y σ τ)
    (z : Fin n) (hzx : z ≠ x) (hzy : z ≠ y) :
    Function.update σ x a z = τ z := by
  have hz := hτ z hzx hzy
  simp [Function.update, hzx, hz]

theorem main : AKLT.Blueprint.Mom.TwoSiteFactorizationStatement := by
  classical
  intro n D hD pinned x y hxy hxy1 hxy2 σ
  refine ⟨offFactor D pinned σ x y,
    (fun a => localFactor D pinned σ x a),
    (fun b => localFactor D pinned σ y b), ?_, ?_, ?_, ?_⟩
  · exact offFactor_nonneg D hD pinned σ x y
  · intro a
    exact localFactor_nonneg D hD pinned σ x a
  · intro b
    exact localFactor_nonneg D hD pinned σ y b
  · intro τ hτ
    have hSites := prod_split_sites (fun z => siteMass D τ z) x y hxy
    have hBonds := bond_products_split D x y hxy hxy1 hxy2 τ
    have hPins := prod_split_sites (fun z => pinMass D pinned τ z) x y hxy
    have hSiteOff :
        (∏ z ∈ (Finset.univ : Finset (Fin n)).filter (fun z => z ≠ x ∧ z ≠ y),
          siteMass D τ z) = offSites D σ x y := by
      unfold offSites
      apply Finset.prod_congr rfl
      intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      exact congrArg (fun j => spinWeight (D.status z) j) (hτ z hz'.1 hz'.2)
    have hPinOff :
        (∏ z ∈ (Finset.univ : Finset (Fin n)).filter (fun z => z ≠ x ∧ z ≠ y),
          pinMass D pinned τ z) = offPins D pinned σ x y := by
      unfold offPins
      apply Finset.prod_congr rfl
      intro z hz
      have hz' := (Finset.mem_filter.mp hz).2
      unfold pinMass
      rw [hτ z hz'.1 hz'.2]
    have hPinX : pinMass D pinned τ x = pinMass D pinned (Function.update σ x (τ x)) x := by
      simp [pinMass, Function.update]
    have hPinY : pinMass D pinned τ y = pinMass D pinned (Function.update σ y (τ y)) y := by
      simp [pinMass, Function.update]
    have hBondX :
        (∏ e ∈ D.bonds.filter (incident x), edgeAt τ e) =
          (∏ e ∈ D.bonds.filter (incident x), edgeAt (Function.update σ x (τ x)) e) := by
      apply Finset.prod_congr rfl
      intro e he
      have heD := (Finset.mem_filter.mp he).1
      have hinc := (Finset.mem_filter.mp he).2
      have hstrict := hD.2.1 e heD
      have hneq : e.1 ≠ e.2 := ne_of_lt hstrict
      have hprof1 : Function.update σ x (τ x) e.1 = τ e.1 := by
        rcases hinc with h1 | h2
        · simp [Function.update, h1]
        · exact update_agrees_off σ τ x y (τ x) hτ e.1
            (fun hh => hneq (hh.trans h2.symm))
            (by
              intro hey
              apply hxy2
              have heq : e = (y, x) := Prod.ext hey h2
              simpa [heq] using heD)
      have hprof2 : Function.update σ x (τ x) e.2 = τ e.2 := by
        rcases hinc with h1 | h2
        · exact update_agrees_off σ τ x y (τ x) hτ e.2
            (fun hh => hneq (h1.trans hh.symm))
            (by
              intro hey
              apply hxy1
              have heq : e = (x, y) := Prod.ext h1 hey
              simpa [heq] using heD)
        · simp [Function.update, h2]
      unfold edgeAt
      rw [← hprof1, ← hprof2]
    have hτswap : AKLT.Blueprint.Mom.twoSiteFiber y x σ τ := by
      intro z hz1 hz2
      exact hτ z hz2 hz1
    have hBondY :
        (∏ e ∈ D.bonds.filter (incident y), edgeAt τ e) =
          (∏ e ∈ D.bonds.filter (incident y), edgeAt (Function.update σ y (τ y)) e) := by
      apply Finset.prod_congr rfl
      intro e he
      have heD := (Finset.mem_filter.mp he).1
      have hinc := (Finset.mem_filter.mp he).2
      have hstrict := hD.2.1 e heD
      have hneq : e.1 ≠ e.2 := ne_of_lt hstrict
      have hprof1 : Function.update σ y (τ y) e.1 = τ e.1 := by
        rcases hinc with h1 | h2
        · simp [Function.update, h1]
        · exact update_agrees_off σ τ y x (τ y) hτswap e.1
            (fun hh => hneq (hh.trans h2.symm))
            (by
              intro hey
              apply hxy1
              have heq : e = (x, y) := Prod.ext hey h2
              simpa [heq] using heD)
      have hprof2 : Function.update σ y (τ y) e.2 = τ e.2 := by
        rcases hinc with h1 | h2
        · exact update_agrees_off σ τ y x (τ y) hτswap e.2
            (fun hh => hneq (h1.trans hh.symm))
            (by
              intro hey
              apply hxy2
              have heq : e = (y, x) := Prod.ext h1 hey
              simpa [heq] using heD)
        · simp [Function.update, h2]
      unfold edgeAt
      rw [← hprof1, ← hprof2]
    have hBondOff :
        (∏ e ∈ D.bonds.filter (fun e => ¬ incident x e ∧ ¬ incident y e), edgeAt τ e) =
          offEdges D σ x y := by
      unfold offEdges
      apply Finset.prod_congr rfl
      intro e he
      have heD := (Finset.mem_filter.mp he).1
      have hno := (Finset.mem_filter.mp he).2
      have h1x : e.1 ≠ x := fun hh => hno.1 (Or.inl hh)
      have h2x : e.2 ≠ x := fun hh => hno.1 (Or.inr hh)
      have h1y : e.1 ≠ y := fun hh => hno.2 (Or.inl hh)
      have h2y : e.2 ≠ y := fun hh => hno.2 (Or.inr hh)
      unfold edgeAt
      rw [hτ e.1 h1x h1y, hτ e.2 h2x h2y]
    change ((∏ z, siteMass D τ z) * (∏ e ∈ D.bonds, edgeAt τ e) *
      (∏ z, pinMass D pinned τ z)) = _
    rw [hSites, hBonds, hPins]
    rw [hSiteOff, hPinOff, hPinX, hPinY, hBondX, hBondY, hBondOff]
    unfold offFactor localFactor siteMass edgeAt
    ring

end AKLT.W.MOM016

