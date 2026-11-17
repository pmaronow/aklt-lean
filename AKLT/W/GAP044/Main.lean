module
public import AKLT.Blueprint.Gap.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP044

local instance (α : Type) : DecidableEq α := Classical.decEq α

private abbrev oneFiber {ι : Type} [DecidableEq ι] {S : ι → Type}
    (x : ι) (σ τ : Config S) : Prop :=
  AgreeOutside ({x} : Finset ι) σ τ

private def fiberEquiv {ι : Type} [DecidableEq ι] [Fintype ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (x : ι) (τ : Config S) :
    {σ : Config S // oneFiber x σ τ} ≃ S x where
  toFun σ := σ.1 x
  invFun s := ⟨Function.update τ x s, by
    intro y hy
    have hyx : y ≠ x := by simpa [Finset.mem_singleton] using hy
    simp [oneFiber, AgreeOutside, hyx]⟩
  left_inv σ := by
    apply Subtype.ext
    funext y
    by_cases hy : y = x
    · subst y
      simp
    · have h := σ.2 y (by simpa [Finset.mem_singleton, hy])
      simpa [hy] using h.symm
  right_inv s := by simp

private lemma fiberCard {ι : Type} [DecidableEq ι] [Fintype ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (x : ι) (τ : Config S) :
    (Finset.univ.filter fun σ : Config S => oneFiber x σ τ).card = Fintype.card (S x) := by
  classical
  have hsub : Fintype.card {σ : Config S // oneFiber x σ τ} =
      (Finset.univ.filter fun σ : Config S => oneFiber x σ τ).card := by
    rw [Fintype.card_subtype]
  calc
    (Finset.univ.filter fun σ : Config S => oneFiber x σ τ).card =
        Fintype.card {σ : Config S // oneFiber x σ τ} := hsub.symm
    _ = Fintype.card (S x) := Fintype.card_congr (fiberEquiv x τ)

private lemma sumIfCongr {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (E F : Ω → Prop) (h : ∀ x, E x ↔ F x) :
    (∑ x, if E x then p x else 0) = ∑ x, if F x then p x else 0 := by
  classical
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : E x
  · have hf := (h x).mp he
    simp [he, hf]
  · have hf : ¬ F x := fun hf => he ((h x).mpr hf)
    simp [he, hf]

private lemma fiberCountRestricted {ι : Type} [DecidableEq ι] [Fintype ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (x : ι) (E : Config S → Prop)
    (hE : ∀ σ τ, oneFiber x σ τ → (E σ ↔ E τ)) (τ : Config S) :
    (∑ σ : Config S, if E σ ∧ oneFiber x σ τ then (1 : ℝ) else 0) =
      if E τ then (Fintype.card (S x) : ℝ) else 0 := by
  classical
  have hsum :
      (∑ σ : Config S, if E σ ∧ oneFiber x σ τ then (1 : ℝ) else 0) =
        ∑ σ : Config S, if E τ ∧ oneFiber x σ τ then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hf : oneFiber x σ τ
    · have h := hE σ τ hf
      by_cases he : E τ <;> simp [hf, he, h]
    · simp [hf]
  rw [hsum]
  by_cases he : E τ
  · simp [he, fiberCard]
  · simp [he]

private lemma sumFiberMass {ι : Type} [DecidableEq ι] [Fintype ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (x : ι) (p : Weight (Config S))
    (E Q : Config S → Prop)
    (hE : ∀ σ τ, oneFiber x σ τ → (E σ ↔ E τ)) :
    (∑ σ : Config S, if E σ then
        eventMass p (fun τ => oneFiber x σ τ ∧ Q τ) else 0) =
      (Fintype.card (S x) : ℝ) * eventMass p (fun τ => E τ ∧ Q τ) := by
  classical
  have hleft :
      (∑ σ : Config S, if E σ then
          eventMass p (fun τ => oneFiber x σ τ ∧ Q τ) else 0) =
        ∑ σ : Config S, if E σ then
          (∑ τ, if oneFiber x σ τ ∧ Q τ then p τ else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro σ _
    by_cases he : E σ
    · simp only [if_pos he]
      unfold eventMass
      apply Finset.sum_congr rfl
      intro τ _
      by_cases h : oneFiber x σ τ ∧ Q τ <;> simp [h]
    · simp only [if_neg he]
  have hright : eventMass p (fun τ => E τ ∧ Q τ) =
      (∑ τ, if E τ ∧ Q τ then p τ else 0) := by
    unfold eventMass
    apply Finset.sum_congr rfl
    intro τ _
    by_cases h : E τ ∧ Q τ <;> simp [h]
  rw [hleft, hright]
  rw [← Finset.sum_filter]
  rw [Finset.sum_comm]
  have hinner (τ : Config S) :
      (∑ σ ∈ Finset.univ.filter E,
          if oneFiber x σ τ ∧ Q τ then p τ else 0) =
        if E τ ∧ Q τ then (Fintype.card (S x) : ℝ) * p τ else 0 := by
    rw [Finset.sum_filter]
    calc
      _ = if Q τ then p τ *
          (∑ σ : Config S, if E σ ∧ oneFiber x σ τ then (1 : ℝ) else 0) else 0 := by
        by_cases hq : Q τ
        · simp only [hq, if_true]
          calc
            _ = ∑ σ : Config S, if E σ ∧ oneFiber x σ τ then p τ else 0 := by
              apply Finset.sum_congr rfl
              intro σ _
              by_cases he : E σ <;> by_cases hf : oneFiber x σ τ <;>
                simp [he, hf]
            _ = p τ * (∑ σ : Config S,
                if E σ ∧ oneFiber x σ τ then (1 : ℝ) else 0) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro σ _
              by_cases h : E σ ∧ oneFiber x σ τ <;> simp [h]
        · simp [hq]
      _ = if E τ ∧ Q τ then (Fintype.card (S x) : ℝ) * p τ else 0 := by
        rw [fiberCountRestricted x E hE τ]
        by_cases he : E τ
        · by_cases hq : Q τ
          · simp [he, hq, mul_comm]
          · simp [he, hq]
        · simp [he]
  calc
    (∑ τ, ∑ σ ∈ Finset.univ.filter E,
        if oneFiber x σ τ ∧ Q τ then p τ else 0) =
      ∑ τ, if E τ ∧ Q τ then (Fintype.card (S x) : ℝ) * p τ else 0 := by
        apply Finset.sum_congr rfl
        intro τ _
        exact hinner τ
    _ = (Fintype.card (S x) : ℝ) *
        (∑ τ, if E τ ∧ Q τ then p τ else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro τ _
        by_cases h : E τ ∧ Q τ <;> simp [h]

private lemma eventMass_pos {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : ∀ σ, 0 < p σ) (E : Ω → Prop) (a : Ω) (ha : E a) :
    0 < eventMass p E := by
  classical
  unfold eventMass
  rw [← Finset.sum_filter]
  apply Finset.sum_pos
  · intro σ hσ
    exact hp σ
  · exact ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ha⟩⟩

private lemma eventMass_congr {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (E F : Ω → Prop) (h : ∀ x, E x ↔ F x) : eventMass p E = eventMass p F := by
  classical
  unfold eventMass
  apply Finset.sum_congr rfl
  intro x _
  by_cases he : E x
  · simp [(h x).mp he, he]
  · have hf : ¬ F x := fun hf => he ((h x).mpr hf)
    simp [he, hf]

private lemma eventMassPair_eq_sum {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (E F : Ω → Prop) :
    eventMass p (fun x => E x ∧ F x) =
      (∑ x, if E x ∧ F x then p x else 0) := by
  classical
  unfold eventMass
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : E x ∧ F x <;> simp [h]

private lemma agreeOn_oneFiber_iff {ι : Type} [DecidableEq ι] [Fintype ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (x : ι) (V : Finset ι)
    (hx : x ∉ V) (a : Config S) (σ τ : Config S)
    (hστ : oneFiber x σ τ) : AgreeOn V σ a ↔ AgreeOn V τ a := by
  constructor
  · intro h y hy
    have hyx : y ≠ x := fun hEq => hx (hEq ▸ hy)
    calc
      τ y = σ y := (hστ y (by simpa [oneFiber, Finset.mem_singleton, hyx])).symm
      _ = a y := h y hy
  · intro h y hy
    have hyx : y ≠ x := fun hEq => hx (hEq ▸ hy)
    calc
      σ y = τ y := hστ y (by simpa [oneFiber, Finset.mem_singleton, hyx])
      _ = a y := h y hy

private lemma partialSiteMass {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p)
    (α : ℝ) (hα : 0 < α)
    (hsite : ∀ x σ a, α ≤ conditionalProbability p (AgreeOutside {x} σ)
      (fun τ => τ x = a))
    (x : ι) (b : S x) (E : Config S → Prop)
    (hE : ∀ σ τ, oneFiber x σ τ → (E σ ↔ E τ)) :
    α * eventMass p E ≤ eventMass p (fun σ => E σ ∧ σ x = b) := by
  classical
  have hlocal (σ : Config S) :
      α * eventMass p (oneFiber x σ) ≤
        eventMass p (fun τ => oneFiber x σ τ ∧ τ x = b) := by
    have hden : 0 < eventMass p (oneFiber x σ) :=
      eventMass_pos p hp.1 (oneFiber x σ) σ (by simp [oneFiber, AgreeOutside])
    have hr := hsite x σ b
    have hraw : α ≤
        (∑ τ, if AgreeOutside {x} σ τ ∧ τ x = b then p τ else 0) /
          (∑ τ, if AgreeOutside {x} σ τ then p τ else 0) := by
      simpa [conditionalProbability] using hr
    have hnum : eventMass p (fun τ => oneFiber x σ τ ∧ τ x = b) =
        (∑ τ, if AgreeOutside {x} σ τ ∧ τ x = b then p τ else 0) := by
      unfold eventMass
      apply Finset.sum_congr rfl
      intro τ _
      by_cases hh : AgreeOutside {x} σ τ ∧ τ x = b <;> simp [oneFiber, hh]
    have hdenEq : eventMass p (oneFiber x σ) =
        (∑ τ, if AgreeOutside {x} σ τ then p τ else 0) := by
      unfold eventMass
      apply Finset.sum_congr rfl
      intro τ _
      by_cases hh : AgreeOutside {x} σ τ <;> simp [oneFiber, hh]
    have hr' : α ≤ eventMass p (fun τ => oneFiber x σ τ ∧ τ x = b) /
        eventMass p (oneFiber x σ) := by
      rw [hnum, hdenEq]
      exact hraw
    exact (le_div_iff₀ hden).mp hr'
  have hsum :
      (∑ σ : Config S, if E σ then α * eventMass p (oneFiber x σ) else 0) ≤
        ∑ σ : Config S, if E σ then
          eventMass p (fun τ => oneFiber x σ τ ∧ τ x = b) else 0 := by
    apply Finset.sum_le_sum
    intro σ _
    by_cases he : E σ
    · simpa only [if_pos he] using hlocal σ
    · rw [if_neg he, if_neg he]
  have hleft : (∑ σ : Config S, if E σ then α * eventMass p (oneFiber x σ) else 0) =
      α * (∑ σ : Config S, if E σ then eventMass p (oneFiber x σ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases he : E σ <;> simp [he]
  have hdenSum :
      (∑ σ : Config S, if E σ then eventMass p (oneFiber x σ) else 0) =
        ∑ σ : Config S, if E σ then
          eventMass p (fun τ => oneFiber x σ τ ∧ True) else 0 := by
    apply Finset.sum_congr rfl
    intro σ _
    by_cases he : E σ
    · simp only [if_pos he]
      unfold eventMass
      apply Finset.sum_congr rfl
      intro τ _
      by_cases hf : oneFiber x σ τ <;> simp [hf]
    · rw [if_neg he, if_neg he]
  rw [hleft, hdenSum, sumFiberMass x p E (fun _ => True) hE,
      sumFiberMass x p E (fun σ => σ x = b) hE] at hsum
  have hcard : 0 < (Fintype.card (S x) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (S x))
  have hsum' : (Fintype.card (S x) : ℝ) * (α * eventMass p E) ≤
      (Fintype.card (S x) : ℝ) * eventMass p (fun σ => E σ ∧ σ x = b) := by
    simpa [mul_assoc, mul_left_comm, mul_comm, eventMass] using hsum
  exact (mul_le_mul_iff_of_pos_left hcard).mp hsum'

private lemma assignmentMassBound {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p)
    (α : ℝ) (hα : 0 < α)
    (hsite : ∀ x σ a, α ≤ conditionalProbability p (AgreeOutside {x} σ)
      (fun τ => τ x = a)) :
    ∀ (U J : Finset ι), Disjoint U J → ∀ a b : Config S,
      α ^ U.card * eventMass p (fun σ => AgreeOn J σ a) ≤
        eventMass p (fun σ => AgreeOn J σ a ∧ AgreeOn U σ b) := by
  classical
  intro U
  induction U using Finset.induction_on with
  | empty =>
      intro J _ a b
      have heq : eventMass p (fun σ => AgreeOn J σ a ∧ AgreeOn (∅ : Finset ι) σ b) =
          eventMass p (fun σ => AgreeOn J σ a) := by
        apply eventMass_congr
        intro σ
        simp [AgreeOn]
      rw [heq]
      simp
  | @insert x U hx ih =>
      intro J hdisj a b
      have hUJ : Disjoint U J := by
        apply Finset.disjoint_left.mpr
        intro y hyU hyJ
        exact (Finset.disjoint_left.mp hdisj) (Finset.mem_insert_of_mem hyU) hyJ
      have hxJ : x ∉ J := by
        intro hxj
        exact (Finset.disjoint_left.mp hdisj) (Finset.mem_insert_self x U) hxj
      let E : Config S → Prop := fun σ => AgreeOn J σ a ∧ AgreeOn U σ b
      have hE : ∀ σ τ, oneFiber x σ τ → (E σ ↔ E τ) := by
        intro σ τ hf
        change (AgreeOn J σ a ∧ AgreeOn U σ b) ↔
          (AgreeOn J τ a ∧ AgreeOn U τ b)
        constructor
        · rintro ⟨hJ, hU⟩
          exact ⟨(agreeOn_oneFiber_iff x J hxJ a σ τ hf).mp hJ,
            (agreeOn_oneFiber_iff x U hx b σ τ hf).mp hU⟩
        · rintro ⟨hJ, hU⟩
          exact ⟨(agreeOn_oneFiber_iff x J hxJ a σ τ hf).mpr hJ,
            (agreeOn_oneFiber_iff x U hx b σ τ hf).mpr hU⟩
      have hstep := partialSiteMass S p hp α hα hsite x (b x) E hE
      have hIH := ih J hUJ a b
      have hmul := mul_le_mul_of_nonneg_left hIH (le_of_lt hα)
      have htarget : eventMass p (fun σ => E σ ∧ σ x = b x) =
          eventMass p (fun σ => AgreeOn J σ a ∧ AgreeOn (insert x U) σ b) := by
        apply eventMass_congr
        intro σ
        simp [E, AgreeOn, Finset.mem_insert, and_assoc, and_left_comm, and_comm]
      calc
        α ^ (insert x U).card * eventMass p (fun σ => AgreeOn J σ a)
            = α * (α ^ U.card * eventMass p (fun σ => AgreeOn J σ a)) := by
                rw [Finset.card_insert_of_notMem hx, pow_succ]
                ring
        _ ≤ α * eventMass p E := hmul
        _ ≤ eventMass p (fun σ => E σ ∧ σ x = b x) := hstep
        _ = eventMass p (fun σ => AgreeOn J σ a ∧ AgreeOn (insert x U) σ b) := htarget

theorem main : AKLT.Blueprint.Gap.FiniteEnergyChainStatement := by
  classical
  unfold AKLT.Blueprint.Gap.FiniteEnergyChainStatement
  intro ι instι instEq S instS instNonempty p hp α hα hαone hsite U J hdisj a b
  have hmass := assignmentMassBound S p hp α hα hsite U J hdisj a b
  have hden : 0 < eventMass p (fun σ => AgreeOn J σ a) :=
    eventMass_pos p hp.1 (fun σ => AgreeOn J σ a) a (by intro x hx; rfl)
  have hdenRaw : 0 < (∑ σ, if AgreeOn J σ a then p σ else 0) := by
    simpa [eventMass] using hden
  have hmulRaw : α ^ U.card * (∑ σ, if AgreeOn J σ a then p σ else 0) ≤
      ∑ σ, if AgreeOn J σ a ∧ AgreeOn U σ b then p σ else 0 := by
    calc
      _ = α ^ U.card * eventMass p (fun σ => AgreeOn J σ a) := by
        rfl
      _ ≤ eventMass p (fun σ => AgreeOn J σ a ∧ AgreeOn U σ b) := hmass
      _ = ∑ σ, if AgreeOn J σ a ∧ AgreeOn U σ b then p σ else 0 :=
        eventMassPair_eq_sum p (fun σ => AgreeOn J σ a) (fun σ => AgreeOn U σ b)
  have hratio := (le_div_iff₀ hdenRaw).2 hmulRaw
  simpa [conditionalProbability] using hratio

end AKLT.W.GAP044
