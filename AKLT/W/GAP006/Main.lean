import AKLT.Blueprint.Gap.NodesFinite

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP006

local instance (α : Type) : DecidableEq α := Classical.decEq α

private def residual {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (p : Weight Ω) (r : Ω → Ξ) (a : Ξ) (fallback : Ω) : Weight Ω :=
  fun x => if 0 < marginal p r a then
    if r x = a then p x / marginal p r a else 0
  else if x = fallback then 1 else 0

private lemma marginal_nonneg {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (p : Weight Ω) (r : Ω → Ξ) (hp : Probability p) (a : Ξ) :
    0 ≤ marginal p r a := by
  classical
  unfold marginal
  apply Finset.sum_nonneg
  intro x hx
  split_ifs
  · exact hp.1 x
  · exact le_rfl

private lemma residual_nonneg {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (p : Weight Ω) (r : Ω → Ξ) (hp : Probability p) (a : Ξ)
    (fallback x : Ω) : 0 ≤ residual p r a fallback x := by
  classical
  unfold residual
  split_ifs with hpos hmem hfallback
  · exact div_nonneg (hp.1 x) (le_of_lt hpos)
  · exact show (0 : ℝ) ≤ 0 from le_rfl
  · exact show (0 : ℝ) ≤ 1 from by norm_num
  · exact show (0 : ℝ) ≤ 0 from le_rfl

private lemma residual_sum {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (p : Weight Ω) (r : Ω → Ξ) (hp : Probability p) (a : Ξ)
    (fallback : Ω) : ∑ x, residual p r a fallback x = 1 := by
  classical
  unfold residual
  by_cases hpos : 0 < marginal p r a
  · simp only [if_pos hpos]
    have hsum : (∑ x, if r x = a then p x / marginal p r a else 0) =
        ∑ x, (if r x = a then p x else 0) / marginal p r a := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : r x = a <;> simp [h]
    rw [hsum, ← Finset.sum_div]
    have hm : (∑ x, if r x = a then p x else 0) = marginal p r a := rfl
    rw [hm, div_self (ne_of_gt hpos)]
  · simp only [if_neg hpos]
    simp

private lemma residual_fiber_sum {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (p : Weight Ω) (r : Ω → Ξ) (hp : Probability p) (a : Ξ)
    (fallback : Ω) (hpos : 0 < marginal p r a) :
    (∑ x, if r x = a then residual p r a fallback x else 0) = 1 := by
  classical
  calc
    (∑ x, if r x = a then residual p r a fallback x else 0) =
        ∑ x, residual p r a fallback x := by
          apply Finset.sum_congr rfl
          intro x hx
          by_cases heq : r x = a
          · simp [heq, residual, hpos]
          · simp [heq, residual, hpos]
    _ = 1 := residual_sum p r hp a fallback

private lemma residual_support {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (p : Weight Ω) (r : Ω → Ξ) (a : Ξ) (fallback x : Ω)
    (hpos : 0 < marginal p r a) (hneq : r x ≠ a) :
    residual p r a fallback x = 0 := by
  simp [residual, hpos, hneq]

private lemma zero_atom_of_zero_marginal {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (p : Weight Ω) (r : Ω → Ξ) (hp : Probability p) (x : Ω)
    (hzero : marginal p r (r x) = 0) : p x = 0 := by
  classical
  have hle : p x ≤ marginal p r (r x) := by
    unfold marginal
    calc
      p x = (if r x = r x then p x else 0) := by simp
      _ ≤ ∑ z, if r z = r x then p z else 0 := by
        apply Finset.single_le_sum (s := Finset.univ)
          (f := fun z => if r z = r x then p z else 0)
        · intro z hz
          split_ifs with h
          · exact hp.1 z
          · exact le_rfl
        · exact Finset.mem_univ x
  exact le_antisymm (by simpa [hzero] using hle) (hp.1 x)

private lemma zero_coupling_row {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    {p : Weight Ω} {q : Weight Ξ} (c : Coupling p q)
    (a : Ω) (b : Ξ) (hzero : p a = 0) : c.mass a b = 0 := by
  classical
  have hle : c.mass a b ≤ p a := by
    rw [← c.first_marginal a]
    apply Finset.single_le_sum (s := Finset.univ) (f := fun y => c.mass a y)
    · intro y hy
      exact c.nonnegative a y
    · exact Finset.mem_univ b
  exact le_antisymm (by simpa [hzero] using hle) (c.nonnegative a b)

private lemma zero_coupling_col {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    {p : Weight Ω} {q : Weight Ξ} (c : Coupling p q)
    (a : Ω) (b : Ξ) (hzero : q b = 0) : c.mass a b = 0 := by
  classical
  have hle : c.mass a b ≤ q b := by
    rw [← c.second_marginal b]
    apply Finset.single_le_sum (s := Finset.univ) (f := fun x => c.mass x b)
    · intro x hx
      exact c.nonnegative x b
    · exact Finset.mem_univ a
  exact le_antisymm (by simpa [hzero] using hle) (c.nonnegative a b)

private lemma sum_fiberwise_indicator {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (r : Ω → Ξ) (f : Ω → ℝ) :
    ∑ x, f x = ∑ a, ∑ x, if r x = a then f x else 0 := by
  classical
  have h := Finset.sum_fiberwise_of_maps_to
    (s := Finset.univ) (t := Finset.univ) (g := r)
    (fun x hx => Finset.mem_univ _) f
  simpa only [Finset.sum_filter] using h.symm

private lemma sum_weighted_fiber {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (r : Ω → Ξ) (f : Ξ → ℝ) (g : Ξ → Ω → ℝ) :
    (∑ x, f (r x) * g (r x) x) =
      ∑ a, ∑ x, if r x = a then f a * g a x else 0 := by
  classical
  calc
    (∑ x, f (r x) * g (r x) x) =
        ∑ a, ∑ x, if r x = a then f (r x) * g (r x) x else 0 :=
          sum_fiberwise_indicator r (fun x => f (r x) * g (r x) x)
    _ = ∑ a, ∑ x, if r x = a then f a * g a x else 0 := by
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : r x = a <;> simp [h]

private lemma rectangular_sum {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    (P : Ω → Prop) (Q : Ξ → Prop) [DecidablePred P] [DecidablePred Q]
    (K : ℝ) (f : Ω → ℝ) (g : Ξ → ℝ) :
    (∑ x, ∑ y, if P x ∧ Q y then K * f x * g y else 0) =
      K * (∑ x, if P x then f x else 0) * (∑ y, if Q y then g y else 0) := by
  classical
  let A := Finset.univ.filter P
  let B := Finset.univ.filter Q
  calc
    (∑ x, ∑ y, if P x ∧ Q y then K * f x * g y else 0) =
        ∑ x ∈ A, ∑ y ∈ B, K * f x * g y := by
          simp only [A, B, Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro x hx
          by_cases hP : P x <;> simp [hP]
    _ = K * (∑ x ∈ A, f x) * (∑ y ∈ B, g y) := by
          calc
            (∑ x ∈ A, ∑ y ∈ B, K * f x * g y) =
                (∑ x ∈ A, K * f x) * (∑ y ∈ B, g y) := by
                  symm
                  rw [Finset.sum_mul_sum]
            _ = K * (∑ x ∈ A, f x) * (∑ y ∈ B, g y) := by
                  rw [← Finset.mul_sum]
    _ = K * (∑ x, if P x then f x else 0) * (∑ y, if Q y then g y else 0) := by
          simp [A, B, Finset.sum_filter]

end AKLT.W.GAP006

theorem AKLT.W.GAP006.main : AKLT.Blueprint.Gap.MarginalCompletionStatement := by
  classical
  intro Ω Ξ hΩ hΞ p q hp hq r c
  letI := hΩ
  letI := hΞ
  letI : DecidableEq Ω := Classical.decEq Ω
  letI : DecidableEq Ξ := Classical.decEq Ξ
  have hΩne : Nonempty Ω := by
    by_contra hne
    letI : IsEmpty Ω := ⟨fun x => hne ⟨x⟩⟩
    have hsum : (∑ x : Ω, p x) = 0 := by simp
    rw [hp.2] at hsum
    norm_num at hsum
  let x₀ : Ω := Classical.choice hΩne
  let liftMass : Ω → Ω → ℝ := fun x y => c.mass (r x) (r y) *
      residual p r (r x) x₀ x * residual q r (r y) x₀ y
  let d : Coupling p q := {
    mass := liftMass
    nonnegative := by
      intro x y
      exact mul_nonneg (mul_nonneg (c.nonnegative (r x) (r y))
        (residual_nonneg p r hp (r x) x₀ x))
        (residual_nonneg q r hq (r y) x₀ y)
    first_marginal := by
      intro x
      let a := r x
      have hfactor : (∑ y, liftMass x y) =
          residual p r a x₀ x * marginal p r a := by
        calc
          (∑ y, liftMass x y) = residual p r a x₀ x *
              (∑ y, c.mass a (r y) * residual q r (r y) x₀ y) := by
                change (∑ y, c.mass a (r y) * residual p r a x₀ x *
                  residual q r (r y) x₀ y) = _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro y hy
                ring
          _ = residual p r a x₀ x *
              (∑ b, ∑ y, if r y = b then
                c.mass a b * residual q r b x₀ y else 0) := by
                rw [sum_weighted_fiber r (fun b => c.mass a b)
                  (fun b y => residual q r b x₀ y)]
          _ = residual p r a x₀ x * (∑ b, c.mass a b) := by
                congr 1
                apply Finset.sum_congr rfl
                intro b hb
                by_cases hbpos : 0 < marginal q r b
                · calc
                    (∑ y, if r y = b then c.mass a b * residual q r b x₀ y else 0) =
                        c.mass a b * (∑ y, if r y = b then residual q r b x₀ y else 0) := by
                          rw [Finset.mul_sum]
                          apply Finset.sum_congr rfl
                          intro y hy
                          by_cases h : r y = b <;> simp [h]
                    _ = c.mass a b := by
                          rw [residual_fiber_sum q r hq b x₀ hbpos]
                          ring
                · have hqzero : marginal q r b = 0 :=
                    le_antisymm (le_of_not_gt hbpos) (marginal_nonneg q r hq b)
                  have hczero : c.mass a b = 0 :=
                    zero_coupling_col c a b (by simpa [hqzero])
                  simp [hczero]
          _ = residual p r a x₀ x * marginal p r a := by
                rw [c.first_marginal a]
      by_cases hapos : 0 < marginal p r a
      · have hres : residual p r a x₀ x = p x / marginal p r a := by
          simp [residual, hapos, a]
        rw [hfactor, hres]
        exact div_mul_cancel₀ (p x) (ne_of_gt hapos)
      · have hpbarzero : marginal p r a = 0 :=
          le_antisymm (le_of_not_gt hapos) (marginal_nonneg p r hp a)
        have hpzero : p x = 0 := by
          apply zero_atom_of_zero_marginal p r hp x
          simpa [a] using hpbarzero
        rw [hfactor, hpbarzero, hpzero]
        simp
    second_marginal := by
      intro y
      let b := r y
      have hfactor : (∑ x, liftMass x y) =
          residual q r b x₀ y * marginal q r b := by
        calc
          (∑ x, liftMass x y) = residual q r b x₀ y *
              (∑ x, c.mass (r x) b * residual p r (r x) x₀ x) := by
                change (∑ x, c.mass (r x) b * residual p r (r x) x₀ x *
                  residual q r b x₀ y) = _
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x hx
                ring
          _ = residual q r b x₀ y *
              (∑ a, ∑ x, if r x = a then
                c.mass a b * residual p r a x₀ x else 0) := by
                rw [sum_weighted_fiber r (fun a => c.mass a b)
                  (fun a x => residual p r a x₀ x)]
          _ = residual q r b x₀ y * (∑ a, c.mass a b) := by
                congr 1
                apply Finset.sum_congr rfl
                intro a ha
                by_cases hapos : 0 < marginal p r a
                · calc
                    (∑ x, if r x = a then c.mass a b * residual p r a x₀ x else 0) =
                        c.mass a b * (∑ x, if r x = a then residual p r a x₀ x else 0) := by
                          rw [Finset.mul_sum]
                          apply Finset.sum_congr rfl
                          intro x hx
                          by_cases h : r x = a <;> simp [h]
                    _ = c.mass a b := by
                          rw [residual_fiber_sum p r hp a x₀ hapos]
                          ring
                · have hpbarzero : marginal p r a = 0 :=
                    le_antisymm (le_of_not_gt hapos) (marginal_nonneg p r hp a)
                  have hczero : c.mass a b = 0 :=
                    zero_coupling_row c a b (by simpa [hpbarzero])
                  simp [hczero]
          _ = residual q r b x₀ y * marginal q r b := by
                rw [c.second_marginal b]
      by_cases hbpos : 0 < marginal q r b
      · have hres : residual q r b x₀ y = q y / marginal q r b := by
          simp [residual, hbpos, b]
        rw [hfactor, hres]
        exact div_mul_cancel₀ (q y) (ne_of_gt hbpos)
      · have hqbarzero : marginal q r b = 0 :=
          le_antisymm (le_of_not_gt hbpos) (marginal_nonneg q r hq b)
        have hqzero : q y = 0 := by
          apply zero_atom_of_zero_marginal q r hq y
          simpa [b] using hqbarzero
        rw [hfactor, hqbarzero, hqzero]
        simp
  }
  refine ⟨d, ?_⟩
  intro a b
  have hpush : (∑ x, ∑ y, if r x = a ∧ r y = b then d.mass x y else 0) =
      c.mass a b *
        (∑ x, if r x = a then residual p r a x₀ x else 0) *
        (∑ y, if r y = b then residual q r b x₀ y else 0) := by
    calc
      (∑ x, ∑ y, if r x = a ∧ r y = b then d.mass x y else 0) =
          ∑ x, ∑ y, if r x = a ∧ r y = b then
            c.mass a b * residual p r a x₀ x * residual q r b x₀ y else 0 := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              by_cases hxa : r x = a <;> by_cases hyb : r y = b <;>
                simp [d, liftMass, hxa, hyb]
      _ = c.mass a b *
          (∑ x, if r x = a then residual p r a x₀ x else 0) *
          (∑ y, if r y = b then residual q r b x₀ y else 0) := by
            exact rectangular_sum (fun x => r x = a) (fun y => r y = b)
              (c.mass a b) (fun x => residual p r a x₀ x)
              (fun y => residual q r b x₀ y)
  by_cases hapos : 0 < marginal p r a
  · by_cases hbpos : 0 < marginal q r b
    · rw [hpush, residual_fiber_sum p r hp a x₀ hapos,
        residual_fiber_sum q r hq b x₀ hbpos]
      ring
    · have hqbarzero : marginal q r b = 0 :=
        le_antisymm (le_of_not_gt hbpos) (marginal_nonneg q r hq b)
      have hczero : c.mass a b = 0 :=
        zero_coupling_col c a b (by simpa [hqbarzero])
      rw [hpush, hczero]
      simp
  · have hpbarzero : marginal p r a = 0 :=
      le_antisymm (le_of_not_gt hapos) (marginal_nonneg p r hp a)
    have hczero : c.mass a b = 0 :=
      zero_coupling_row c a b (by simpa [hpbarzero])
    rw [hpush, hczero]
    simp

