module
public import AKLT.W.GAP045.Finite

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

lemma weighted_div_self {w U : ℝ} (hw : 0 ≤ w) (hU : 0 ≤ U) (h : w ≤ U) :
    w * U / U = w := by
  by_cases h0 : U = 0
  · have : w = 0 := le_antisymm (h.trans_eq h0) hw
    simp [h0, this]
  · exact mul_div_cancel_right₀ _ h0

lemma scaled_le {w a U : ℝ} (ha : 0 ≤ a) (hU : 0 ≤ U) (h : w ≤ U) :
    w * a / U ≤ a := by
  rcases hU.eq_or_lt with h0 | h0
  · simp [← h0, ha]
  · apply (div_le_iff₀ h0).mpr
    nlinarith [mul_le_mul_of_nonneg_right h ha]

/-- Match arbitrary labeled submeasures and complete the remaining mass. -/
theorem match_submeasures {p : Weight Ω} {q : Weight Ξ}
    (hp : Probability p) (hq : Probability q)
    (u : Λ → Weight Ω) (v : Λ → Weight Ξ) (w : Weight Λ)
    (hu : ∀ b x, 0 ≤ u b x) (hv : ∀ b y, 0 ≤ v b y) (hw : ∀ b, 0 ≤ w b)
    (hup : ∀ x, ∑ b, u b x ≤ p x) (hvq : ∀ y, ∑ b, v b y ≤ q y)
    (hwu : ∀ b, w b ≤ ∑ x, u b x) (hwv : ∀ b, w b ≤ ∑ y, v b y)
    (E : Ω × Ξ → Prop)
    (hE : ∀ b x y, 0 < u b x → 0 < v b y → E (x,y)) :
    ∃ c : Coupling p q, (∑ b, w b) ≤ eventMass (fun z => c.mass z.1 z.2) E := by
  classical
  let U : Weight Λ := fun b => ∑ x, u b x
  let V : Weight Λ := fun b => ∑ y, v b y
  have hU : ∀ b, 0 ≤ U b := fun b => Finset.sum_nonneg fun x _ => hu b x
  have hV : ∀ b, 0 ≤ V b := fun b => Finset.sum_nonneg fun y _ => hv b y
  let k : Ω → Ξ → ℝ := fun x y =>
    ∑ b, (w b * u b x / U b) * v b y / V b
  have hk : ∀ x y, 0 ≤ k x y := by
    intro x y
    exact Finset.sum_nonneg fun b _ =>
      div_nonneg (mul_nonneg (div_nonneg (mul_nonneg (hw b) (hu b x)) (hU b))
        (hv b y)) (hV b)
  have kr : ∀ x, ∑ y, k x y = ∑ b, w b * u b x / U b := by
    intro x
    dsimp [k]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.sum_div, ← Finset.mul_sum]
    change (w b * u b x / U b) * V b / V b = _
    by_cases h0 : V b = 0
    · have hw0 : w b = 0 := le_antisymm ((hwv b).trans_eq h0) (hw b)
      simp [hw0]
    · exact mul_div_cancel_right₀ _ h0
  have kc : ∀ y, ∑ x, k x y = ∑ b, w b * v b y / V b := by
    intro y
    dsimp [k]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    calc
      _ = (w b * (∑ x, u b x) / U b) * v b y / V b := by
        rw [Finset.mul_sum, Finset.sum_div, Finset.sum_mul, Finset.sum_div]
      _ = _ := by rw [weighted_div_self (hw b) (hU b) (hwu b)]
  have hkp : ∀ x, ∑ y, k x y ≤ p x := by
    intro x
    rw [kr]
    exact (Finset.sum_le_sum fun b _ => scaled_le (hu b x) (hU b) (hwu b)).trans (hup x)
  have hkq : ∀ y, ∑ x, k x y ≤ q y := by
    intro y
    rw [kc]
    exact (Finset.sum_le_sum fun b _ => scaled_le (hv b y) (hV b) (hwv b)).trans (hvq y)
  have hkt : ∑ x, ∑ y, k x y = ∑ b, w b := by
    simp_rw [kr]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.sum_div, ← Finset.mul_sum]
    exact weighted_div_self (hw b) (hU b) (hwu b)
  have hks : ∀ x y, ¬ E (x,y) → k x y = 0 := by
    intro x y hn
    apply Finset.sum_eq_zero
    intro b _
    by_cases hu0 : u b x = 0
    · simp [hu0]
    by_cases hv0 : v b y = 0
    · simp [hv0]
    exact (hn (hE b x y (lt_of_le_of_ne (hu b x) (Ne.symm hu0))
      (lt_of_le_of_ne (hv b y) (Ne.symm hv0)))).elim
  obtain ⟨c, hc⟩ := complete_subcoupling hp hq k hk hkp hkq
  refine ⟨c, ?_⟩
  calc
    (∑ b, w b) = eventMass (fun z : Ω × Ξ => k z.1 z.2) E := by
      rw [eventMass, Fintype.sum_prod_type, ← hkt]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      by_cases he : E (x,y) <;> simp [he, hks x y]
    _ ≤ _ := event_mono (fun z => hk _ _) (fun z => hc _ _) (fun _ he => he)

/-- An event in each fiber supplies a matchable submeasure on that label. -/
theorem match_events {p : Weight Ω} {q : Weight Ξ}
    (hp : Probability p) (hq : Probability q) (f : Ω → Λ) (g : Ξ → Λ)
    (G : Ω → Prop) (H : Ξ → Prop) (w : Weight Λ)
    (hw : ∀ b, 0 ≤ w b)
    (hwp : ∀ b, w b ≤ eventMass p (fun x => f x = b ∧ G x))
    (hwq : ∀ b, w b ≤ eventMass q (fun y => g y = b ∧ H y))
    (E : Ω × Ξ → Prop) (hE : ∀ x y, G x → H y → f x = g y → E (x,y)) :
    ∃ c : Coupling p q, (∑ b, w b) ≤ eventMass (fun z => c.mass z.1 z.2) E := by
  classical
  let u : Λ → Weight Ω := fun b x => if f x = b ∧ G x then p x else 0
  let v : Λ → Weight Ξ := fun b y => if g y = b ∧ H y then q y else 0
  have hu : ∀ b x, 0 ≤ u b x := by intro b x; dsimp [u]; split_ifs <;> simp_all [hp.1]
  have hv : ∀ b y, 0 ≤ v b y := by intro b y; dsimp [v]; split_ifs <;> simp_all [hq.1]
  apply match_submeasures hp hq u v w hu hv hw ?_ ?_ ?_ ?_ E ?_
  · intro x
    dsimp [u]
    by_cases hx : G x <;> simp [hx, hp.1]
  · intro y
    dsimp [v]
    by_cases hy : H y <;> simp [hy, hq.1]
  · intro b
    convert hwp b using 1
    apply Finset.sum_congr rfl
    intro x _
    by_cases he : f x = b ∧ G x <;> simp [u, he]
  · intro b
    convert hwq b using 1
    apply Finset.sum_congr rfl
    intro y _
    by_cases he : g y = b ∧ H y <;> simp [v, he]
  · intro b x y hx hy
    have hx' : f x = b ∧ G x := by
      by_contra hn; simp [u, hn] at hx
    have hy' : g y = b ∧ H y := by
      by_contra hn; simp [v, hn] at hy
    exact hE x y hx'.2 hy'.2 (hx'.1.trans hy'.1.symm)

/-- A coupling can be pushed forward separately in its two coordinates. -/
def mapCoupling {p : Weight Ω} {q : Weight Ξ} (c : Coupling p q)
    {Ω' Ξ' : Type} [Fintype Ω'] [Fintype Ξ'] [DecidableEq Ω'] [DecidableEq Ξ'] (f : Ω → Ω') (g : Ξ → Ξ') :
    Coupling (marginal p f) (marginal q g) where
  mass a b := ∑ x, ∑ y, if f x = a ∧ g y = b then c.mass x y else 0
  nonnegative a b := Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => by
    split_ifs <;> simp_all [c.nonnegative]
  first_marginal a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    by_cases hx : f x = a
    · simp [hx, c.first_marginal]
    · simp [hx]
  second_marginal b := by
    change (∑ a, ∑ x, ∑ y, if f x = a ∧ g y = b then c.mass x y else 0) =
      ∑ y, if g y = b then q y else 0
    calc
      _ = ∑ x, ∑ y, if g y = b then c.mass x y else 0 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro x _
        rw [Finset.sum_comm]
        simp [ite_and]
      _ = _ := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : g y = b <;> simp [hy, c.second_marginal]

lemma event_marginal [DecidableEq Ξ] (p : Weight Ω) (f : Ω → Ξ) (E : Ξ → Prop) :
    eventMass (marginal p f) E = eventMass p (fun x => E (f x)) := by
  simpa [eventMass, mul_ite] using marginal_test p f (fun b => if E b then 1 else 0)

lemma mapCoupling_event {p : Weight Ω} {q : Weight Ξ} (c : Coupling p q)
    {Ω' Ξ' : Type} [Fintype Ω'] [Fintype Ξ'] [DecidableEq Ω'] [DecidableEq Ξ'] (f : Ω → Ω') (g : Ξ → Ξ')
    (E : Ω' × Ξ' → Prop) :
    eventMass (fun z => (mapCoupling c f g).mass z.1 z.2) E =
      eventMass (fun z : Ω × Ξ => c.mass z.1 z.2) (fun z => E (f z.1, g z.2)) := by
  classical
  have he : (fun z => (mapCoupling c f g).mass z.1 z.2) =
      marginal (fun z : Ω × Ξ => c.mass z.1 z.2) (fun z => (f z.1, g z.2)) := by
    funext z
    rcases z with ⟨a,b⟩
    simp [mapCoupling, marginal, Fintype.sum_prod_type]
  rw [he]
  exact event_marginal (fun z : Ω × Ξ => c.mass z.1 z.2)
    (fun z : Ω × Ξ => (f z.1, g z.2)) E

end AKLT.W.GAP045

namespace AKLT.W.GAP045
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable
local instance (α : Type) : DecidableEq α := Classical.decEq α

variable {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]

def independentCoupling {p : Weight Ω} {q : Weight Ξ} (hp : Probability p) (hq : Probability q) :
    Coupling p q where
  mass x y := p x * q y
  nonnegative x y := mul_nonneg (hp.1 x) (hq.1 y)
  first_marginal x := by rw [← Finset.mul_sum, hq.2, mul_one]
  second_marginal y := by rw [← Finset.sum_mul, hp.2, one_mul]

def diagonalCoupling {p q : Weight Ω} (hp : ∀ x, 0 ≤ p x) (he : p = q) : Coupling p q where
  mass x y := if x = y then p x else 0
  nonnegative x y := by split_ifs <;> simp_all
  first_marginal x := by simp
  second_marginal y := by simp [← he]

lemma diagonal_positive {p q : Weight Ω} (hp : ∀ x, 0 ≤ p x) (he : p = q)
    (x y : Ω) (h : 0 < (diagonalCoupling hp he).mass x y) : x = y := by
  by_contra hn
  simp [diagonalCoupling, hn] at h

lemma mapCoupling_positive {p : Weight Ω} {q : Weight Ξ} (c : Coupling p q)
    {Ω' Ξ' : Type} [Fintype Ω'] [Fintype Ξ'] [DecidableEq Ω'] [DecidableEq Ξ'] (f : Ω → Ω') (g : Ξ → Ξ')
    (a : Ω') (b : Ξ') (h : 0 < (mapCoupling c f g).mass a b) :
    ∃ x y, 0 < c.mass x y ∧ f x = a ∧ g y = b := by
  have hn : ∀ x y, 0 ≤ (if f x = a ∧ g y = b then c.mass x y else 0) := by
    intro x y; split_ifs <;> simp_all [c.nonnegative]
  obtain ⟨x, _, hx⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun x _ => Finset.sum_nonneg fun y _ => hn x y)).mp h
  obtain ⟨y, _, hy⟩ := (Finset.sum_pos_iff_of_nonneg (fun y _ => hn x y)).mp hx
  by_cases he : f x = a ∧ g y = b
  · exact ⟨x,y,by simpa [he] using hy, he⟩
  · simp [he] at hy

lemma event_eq_one_of_support {p : Weight Ω} (hp : Probability p) (E : Ω → Prop)
    (hs : ∀ x, 0 < p x → E x) : eventMass p E = 1 := by
  rw [← hp.2]
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : E x
  · simp [he]
  · have hx : p x = 0 := le_antisymm (le_of_not_gt (fun hh => he (hs x hh))) (hp.1 x)
    simp [he, hx]

end AKLT.W.GAP045
