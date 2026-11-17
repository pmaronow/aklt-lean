module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP003

def outsideKey {ι : Type} [DecidableEq ι] {S : ι → Type}
    (U : Finset ι) (σ : Config S) : (x : {x // x ∉ U}) → S x.1 :=
  fun x => σ x.1

lemma agreeOutside_iff_key {ι : Type} [DecidableEq ι] {S : ι → Type}
    (U : Finset ι) (σ τ : Config S) :
    AgreeOutside U σ τ ↔ outsideKey U σ = outsideKey U τ := by
  constructor
  · intro h
    funext x
    exact h x.1 x.2
  · intro h x hx
    exact congrFun h ⟨x, hx⟩

def keyMass {Ω K : Type} [Fintype Ω] [DecidableEq K] (p : Weight Ω) (g : Ω → K) (b : K) : ℝ :=
  ∑ x, if g x = b then p x else 0

def keyNumerator {Ω K : Type} [Fintype Ω] [DecidableEq K] (p : Weight Ω) (g : Ω → K)
    (f : Ω → ℂ) (b : K) : ℂ :=
  ∑ x, if g x = b then (p x : ℂ) * f x else 0

lemma keyMass_pos {Ω K : Type} [Fintype Ω] [DecidableEq K]
    (p : Weight Ω) (g : Ω → K) (hp : ∀ x, 0 < p x) (x : Ω) :
    0 < keyMass p g (g x) := by
  unfold keyMass
  have hle := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun y => if g y = g x then p y else 0)
    (fun y hy => by
      by_cases h : g y = g x
      · simpa [h] using le_of_lt (hp y)
      · simp [h])
    (a := x) (Finset.mem_univ x)
  exact lt_of_lt_of_le (by simpa using hp x) (by
    simpa using hle)

lemma keyMass_mul_div {Ω K : Type} [Fintype Ω] [DecidableEq K]
    (p : Weight Ω) (g : Ω → K) (b : K) (z : ℂ) :
    (∑ x, if g x = b then (p x : ℂ) * z else 0) =
      (keyMass p g b : ℂ) * z := by
  have hpoint : ∀ x, (if g x = b then (p x : ℂ) * z else 0) =
      (if g x = b then (p x : ℂ) else 0) * z := by
    intro x
    split_ifs <;> simp
  calc
    (∑ x, if g x = b then (p x : ℂ) * z else 0) =
        Finset.univ.sum (fun x => if g x = b then (p x : ℂ) * z else 0) := rfl
    _ = Finset.univ.sum (fun x => (if g x = b then (p x : ℂ) else 0) * z) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hpoint x
    _ = (Finset.univ.sum fun x => if g x = b then (p x : ℂ) else 0) * z := by
      exact (Finset.sum_mul _ _ _).symm
    _ = (keyMass p g b : ℂ) * z := by
      congr 1
      change (Finset.univ.sum fun x => if g x = b then (p x : ℂ) else 0) =
        (↑(Finset.univ.sum fun x => if g x = b then p x else 0) : ℂ)
      rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro x hx
      split_ifs <;> simp

local instance outsideKeyDecidableEq {ι : Type} [DecidableEq ι] {S : ι → Type}
    (U : Finset ι) : DecidableEq ((x : {x // x ∉ U}) → S x.1) := Classical.decEq _

lemma sum_if_cast {Ω : Type} [Fintype Ω] (P : Ω → Prop) [DecidablePred P]
    (p : Ω → ℝ) :
    (∑ x, if P x then (p x : ℂ) else 0) =
      (∑ x, (if P x then p x else 0 : ℝ) : ℂ) := by
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs <;> simp

lemma conditionalExpectation_key_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (U : Finset ι) (f : Config S → ℂ) (σ : Config S) :
    conditionalExpectation p U f σ =
      keyNumerator p (outsideKey U) f (outsideKey U σ) /
        (keyMass p (outsideKey U) (outsideKey U σ) : ℂ) := by
  classical
  simp [conditionalExpectation, keyNumerator, keyMass, agreeOutside_iff_key, eq_comm]
  congr 1
  exact sum_if_cast (fun x => outsideKey U σ = outsideKey U x) p

lemma conditionalExpectation_fiberConstant {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (U : Finset ι) (f : Config S → ℂ) {σ τ : Config S}
    (h : AgreeOutside U σ τ) : conditionalExpectation p U f σ = conditionalExpectation p U f τ := by
  rw [conditionalExpectation_key_eq, conditionalExpectation_key_eq,
    (agreeOutside_iff_key U σ τ).mp h]

lemma key_residual_sum {Ω K : Type} [Fintype Ω] [DecidableEq K]
    (p : Weight Ω) (g : Ω → K) (f : Ω → ℂ) (b : K)
    (hD : keyMass p g b ≠ 0) :
    (∑ x, if g x = b then (p x : ℂ) *
      (f x - keyNumerator p g f b / (keyMass p g b : ℂ)) else 0) = 0 := by
  have hfirst : (∑ x, if g x = b then (p x : ℂ) * f x else 0) =
      keyNumerator p g f b := by rfl
  have hsecond : (∑ x, if g x = b then
      (p x : ℂ) * (keyNumerator p g f b / (keyMass p g b : ℂ)) else 0) =
      (keyMass p g b : ℂ) *
        (keyNumerator p g f b / (keyMass p g b : ℂ)) :=
    keyMass_mul_div p g b (keyNumerator p g f b / (keyMass p g b : ℂ))
  calc
    _ = (∑ x, if g x = b then (p x : ℂ) * f x else 0) -
        (∑ x, if g x = b then
          (p x : ℂ) * (keyNumerator p g f b / (keyMass p g b : ℂ)) else 0) := by
      symm
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxb : g x = b <;> simp [hxb, mul_sub]
    _ = keyNumerator p g f b -
        (keyMass p g b : ℂ) *
          (keyNumerator p g f b / (keyMass p g b : ℂ)) := by rw [hfirst, hsecond]
    _ = 0 := by
      have hDc : (keyMass p g b : ℂ) ≠ 0 := by exact_mod_cast hD
      rw [mul_div_cancel₀ _ hDc]
      exact sub_self _

lemma conditionalResidual_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (U : Finset ι) (f : Config S → ℂ) (hp : ∀ σ, 0 < p σ) :
    ∑ σ, (p σ : ℂ) * (f σ - conditionalExpectation p U f σ) = 0 := by
  classical
  let g : Config S → ((x : {x // x ∉ U}) → S x.1) := fun σ => outsideKey U σ
  let T := Finset.univ.image g
  have hmap : ∀ σ ∈ (Finset.univ : Finset (Config S)), g σ ∈ T := by
    intro σ hσ
    exact Finset.mem_image.mpr ⟨σ, hσ, rfl⟩
  have hsum := Finset.sum_fiberwise_of_maps_to hmap
    (fun σ => (p σ : ℂ) * (f σ - conditionalExpectation p U f σ))
  rw [← hsum]
  apply Finset.sum_eq_zero
  intro b hb
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hb
  have hD : keyMass p g (g σ) ≠ 0 := ne_of_gt (keyMass_pos p g hp σ)
  have hclass := key_residual_sum p g f (g σ) hD
  have heq : ∀ τ, g τ = g σ →
      conditionalExpectation p U f τ =
        keyNumerator p g f (g σ) / (keyMass p g (g σ) : ℂ) := by
    intro τ hτ
    have hk : outsideKey U τ = outsideKey U σ := by simpa [g] using hτ
    rw [conditionalExpectation_key_eq, hk]
  have hclassCE :
      (∑ τ, if g τ = g σ then (p τ : ℂ) *
        (f τ - conditionalExpectation p U f τ) else 0) =
      (∑ τ, if g τ = g σ then (p τ : ℂ) *
        (f τ - keyNumerator p g f (g σ) / (keyMass p g (g σ) : ℂ)) else 0) := by
    apply Finset.sum_congr rfl
    intro τ hτ
    by_cases h : g τ = g σ
    · simp [h, heq τ h]
    · simp [h]
  simpa [g, Finset.sum_filter] using hclassCE.trans hclass

lemma residual_orthogonal {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (U : Finset ι) (f h : Config S → ℂ) (hp : ∀ σ, 0 < p σ)
    (hconst : ∀ σ τ, AgreeOutside U σ τ → h σ = h τ) :
    ∑ σ, (p σ : ℂ) * star (h σ) * (f σ - conditionalExpectation p U f σ) = 0 := by
  classical
  let g : Config S → ((x : {x // x ∉ U}) → S x.1) := fun σ => outsideKey U σ
  let T := Finset.univ.image g
  have hmap : ∀ σ ∈ (Finset.univ : Finset (Config S)), g σ ∈ T := by
    intro σ hσ
    exact Finset.mem_image.mpr ⟨σ, hσ, rfl⟩
  have hsum := Finset.sum_fiberwise_of_maps_to hmap
    (fun σ => (p σ : ℂ) * star (h σ) * (f σ - conditionalExpectation p U f σ))
  rw [← hsum]
  apply Finset.sum_eq_zero
  intro b hb
  obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hb
  have hD : keyMass p g (g σ) ≠ 0 := ne_of_gt (keyMass_pos p g hp σ)
  have hclass := key_residual_sum p g f (g σ) hD
  have heqCE : ∀ τ, g τ = g σ →
      conditionalExpectation p U f τ =
        keyNumerator p g f (g σ) / (keyMass p g (g σ) : ℂ) := by
    intro τ hτ
    have hk : outsideKey U τ = outsideKey U σ := by simpa [g] using hτ
    rw [conditionalExpectation_key_eq, hk]
  have hclassOrth :
      (∑ τ, if g τ = g σ then (p τ : ℂ) * star (h τ) *
        (f τ - conditionalExpectation p U f τ) else 0) = 0 := by
    calc
      _ = ∑ τ, star (h σ) *
          (if g τ = g σ then (p τ : ℂ) *
            (f τ - keyNumerator p g f (g σ) /
              (keyMass p g (g σ) : ℂ)) else 0) := by
        apply Finset.sum_congr rfl
        intro τ hτ'
        by_cases hτ : g τ = g σ
        · have hout : AgreeOutside U τ σ := by
            exact (agreeOutside_iff_key U τ σ).mpr (by simpa [g] using hτ)
          rw [hconst τ σ hout, heqCE τ hτ]
          simp [hτ, mul_assoc, mul_left_comm]
        · simp [hτ]
      _ = star (h σ) *
          (∑ τ, if g τ = g σ then (p τ : ℂ) *
            (f τ - keyNumerator p g f (g σ) /
              (keyMass p g (g σ) : ℂ)) else 0) := by
        exact (Finset.mul_sum _ _ _).symm
      _ = 0 := by rw [hclass]; simp
  simpa [g, Finset.sum_filter] using hclassOrth

lemma weightedInner_blockDirichlet {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (U : Finset ι) (f : Config S → ℂ) (hp : ∀ σ, 0 < p σ) :
    (weightedInner p f (fun σ => f σ - conditionalExpectation p U f σ)).re =
      blockDirichlet p U f := by
  classical
  let c : Config S → ℂ := conditionalExpectation p U f
  let r : Config S → ℂ := fun σ => f σ - c σ
  have hconst : ∀ σ τ, AgreeOutside U σ τ → c σ = c τ := by
    intro σ τ h
    exact conditionalExpectation_fiberConstant p U f h
  have horth := residual_orthogonal p U f c hp hconst
  have hpoint (σ : Config S) :
      (star (f σ) * r σ).re = Complex.normSq (r σ) + (star (c σ) * r σ).re := by
    have hdecomp : f σ = r σ + c σ := by simp [r, c]
    have hnorm : (star (r σ) * r σ).re = Complex.normSq (r σ) := by
      have hh := congrArg Complex.re
        (Complex.normSq_eq_conj_mul_self (z := r σ)).symm
      simpa using hh
    calc
      (star (f σ) * r σ).re = (star (r σ + c σ) * r σ).re := by rw [hdecomp]
      _ = ( (star (r σ) + star (c σ)) * r σ).re := by rw [star_add]
      _ = (star (r σ) * r σ).re + (star (c σ) * r σ).re := by
        rw [add_mul, Complex.add_re]
      _ = _ := by rw [hnorm]
  have hcross :
      (∑ σ, p σ * (star (c σ) * r σ).re) = 0 := by
    calc
      (∑ σ, p σ * (star (c σ) * r σ).re) =
          (∑ σ, (p σ : ℂ) * star (c σ) * r σ).re := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro σ hσ
        simp [mul_assoc]
      _ = 0 := by rw [horth]; simp
  unfold weightedInner
  change (∑ σ, (p σ : ℂ) * star (f σ) *
      (f σ - conditionalExpectation p U f σ)).re = _
  rw [Complex.re_sum]
  simp_rw [mul_assoc, Complex.re_ofReal_mul]
  change (∑ σ, p σ * (star (f σ) * r σ).re) = _
  calc
    (∑ σ, p σ * (star (f σ) * r σ).re) =
        ∑ σ, p σ * (Complex.normSq (r σ) + (star (c σ) * r σ).re) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [hpoint σ]
    _ = ∑ σ, (p σ * Complex.normSq (r σ) +
          p σ * (star (c σ) * r σ).re) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
    _ = (∑ σ, p σ * Complex.normSq (r σ)) +
        (∑ σ, p σ * (star (c σ) * r σ).re) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ σ, p σ * Complex.normSq (r σ)) + 0 := by rw [hcross]
    _ = blockDirichlet p U f := by
      simp [blockDirichlet, r, c]

def keyEnergy {Ω K : Type} [Fintype Ω] [DecidableEq K]
    (p : Weight Ω) (g : Ω → K) (f : Ω → ℂ) (b : K) : ℝ :=
  ∑ x, if g x = b then
    p x * Complex.normSq (f x - keyNumerator p g f b / (keyMass p g b : ℂ)) else 0

lemma conditionalVariance_key_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (U : Finset ι) (f : Config S → ℂ) (σ : Config S) :
    conditionalVariance p U f σ =
      keyEnergy p (outsideKey U) f (outsideKey U σ) /
        keyMass p (outsideKey U) (outsideKey U σ) := by
  classical
  let g : Config S → ((x : {x // x ∉ U}) → S x.1) := fun τ => outsideKey U τ
  have hnum :
      (∑ τ, if AgreeOutside U σ τ then p τ *
        Complex.normSq (f τ - conditionalExpectation p U f τ) else 0) =
        keyEnergy p g f (g σ) := by
    unfold keyEnergy
    apply Finset.sum_congr rfl
    intro τ hτ'
    by_cases ha : AgreeOutside U σ τ
    · have hk : g τ = g σ := by
        exact (agreeOutside_iff_key U σ τ).mp ha |>.symm
      have hc : conditionalExpectation p U f σ =
          keyNumerator p g f (g σ) / (keyMass p g (g σ) : ℂ) := by
        rw [conditionalExpectation_key_eq]
      have hcτ : conditionalExpectation p U f τ =
          keyNumerator p g f (g σ) / (keyMass p g (g σ) : ℂ) :=
        (conditionalExpectation_fiberConstant p U f ha).symm.trans hc
      simp [ha, hk, hcτ]
    · have hk : g τ ≠ g σ := by
        intro heq
        apply ha
        exact (agreeOutside_iff_key U σ τ).mpr heq.symm
      simp [ha, hk]
  have hden :
      (∑ τ, if AgreeOutside U σ τ then p τ else 0) = keyMass p g (g σ) := by
    unfold keyMass
    apply Finset.sum_congr rfl
    intro τ hτ'
    by_cases ha : AgreeOutside U σ τ
    · have hk : g τ = g σ := by
        exact (agreeOutside_iff_key U σ τ).mp ha |>.symm
      simp [ha, hk]
    · have hk : g τ ≠ g σ := by
        intro heq
        apply ha
        exact (agreeOutside_iff_key U σ τ).mpr heq.symm
      simp [ha, hk]
  unfold conditionalVariance
  change (∑ τ, if AgreeOutside U σ τ then p τ *
      Complex.normSq (f τ - conditionalExpectation p U f τ) else 0) /
      (∑ τ, if AgreeOutside U σ τ then p τ else 0) = _
  rw [hnum, hden]

lemma keyMass_mul_real {Ω K : Type} [Fintype Ω] [DecidableEq K]
    (p : Weight Ω) (g : Ω → K) (b : K) (z : ℝ) :
    (∑ x, if g x = b then p x * z else 0) = keyMass p g b * z := by
  have hpoint : ∀ x, (if g x = b then p x * z else 0) =
      (if g x = b then p x else 0) * z := by
    intro x
    split_ifs <;> simp
  calc
    (∑ x, if g x = b then p x * z else 0) =
        Finset.univ.sum (fun x => if g x = b then p x * z else 0) := rfl
    _ = Finset.univ.sum (fun x => (if g x = b then p x else 0) * z) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hpoint x
    _ = (Finset.univ.sum fun x => if g x = b then p x else 0) * z := by
      exact (Finset.sum_mul _ _ _).symm

lemma conditionalVariance_integral {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (U : Finset ι) (f : Config S → ℂ) (hp : ∀ σ, 0 < p σ) :
    expectation p (conditionalVariance p U f) = blockDirichlet p U f := by
  classical
  let g : Config S → ((x : {x // x ∉ U}) → S x.1) := fun σ => outsideKey U σ
  let T := Finset.univ.image g
  have hmap : ∀ σ ∈ (Finset.univ : Finset (Config S)), g σ ∈ T := by
    intro σ hσ
    exact Finset.mem_image.mpr ⟨σ, hσ, rfl⟩
  have hsumCV := Finset.sum_fiberwise_of_maps_to hmap
    (fun σ => p σ * conditionalVariance p U f σ)
  have hsumEnergy := Finset.sum_fiberwise_of_maps_to hmap
    (fun σ => p σ * Complex.normSq (f σ - conditionalExpectation p U f σ))
  have hEnergyClass (b : _) :
      (∑ τ, if g τ = b then p τ *
        Complex.normSq (f τ - conditionalExpectation p U f τ) else 0) =
        keyEnergy p g f b := by
    apply Finset.sum_congr rfl
    intro τ hτ'
    by_cases hτ : g τ = b
    · have hce : conditionalExpectation p U f τ =
          keyNumerator p g f b / (keyMass p g b : ℂ) := by
        rw [conditionalExpectation_key_eq]
        simp [g, hτ]
      simp [hτ, hce]
    · simp [hτ]
  have hkeyBlock : (∑ b ∈ T, keyEnergy p g f b) = blockDirichlet p U f := by
    calc
      (∑ b ∈ T, keyEnergy p g f b) =
          ∑ b ∈ T, ∑ τ with g τ = b,
            p τ * Complex.normSq (f τ - conditionalExpectation p U f τ) := by
        apply Finset.sum_congr rfl
        intro b hb
        obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hb
        simpa [Finset.sum_filter] using (hEnergyClass (g σ)).symm
      _ = ∑ σ, p σ * Complex.normSq (f σ - conditionalExpectation p U f σ) := hsumEnergy
      _ = blockDirichlet p U f := rfl
  unfold expectation
  calc
    (∑ σ, p σ * conditionalVariance p U f σ) =
        ∑ b ∈ T, ∑ σ with g σ = b,
          p σ * conditionalVariance p U f σ := hsumCV.symm
    _ = ∑ b ∈ T, keyEnergy p g f b := by
      apply Finset.sum_congr rfl
      intro b hb
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hb
      have hD : keyMass p g (g σ) ≠ 0 :=
        ne_of_gt (keyMass_pos p g hp σ)
      have hclass :
          (∑ τ with g τ = g σ, p τ * conditionalVariance p U f τ) =
            keyEnergy p g f (g σ) := by
        calc
          _ = ∑ τ with g τ = g σ,
              p τ * (keyEnergy p g f (g σ) / keyMass p g (g σ)) := by
            apply Finset.sum_congr rfl
            intro τ hτ'
            have hτ : g τ = g σ := (Finset.mem_filter.mp hτ').2
            have hcv : conditionalVariance p U f τ =
                keyEnergy p g f (g σ) / keyMass p g (g σ) := by
              rw [conditionalVariance_key_eq]
              simp [g, hτ]
            rw [hcv]
          _ = keyMass p g (g σ) *
              (keyEnergy p g f (g σ) / keyMass p g (g σ)) := by
            simpa [Finset.sum_filter] using
              keyMass_mul_real p g (g σ)
                (keyEnergy p g f (g σ) / keyMass p g (g σ))
          _ = keyEnergy p g f (g σ) := by
            rw [mul_div_cancel₀ _ hD]
      simpa [Finset.sum_filter] using hclass
    _ = blockDirichlet p U f := hkeyBlock

lemma variance_decomposition {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (U : Finset ι) (f : Config S → ℂ) (hp : ∀ σ, 0 < p σ) :
    variance p f = blockDirichlet p U f +
      variance p (conditionalExpectation p U f) := by
  classical
  let c : Config S → ℂ := conditionalExpectation p U f
  let r : Config S → ℂ := fun σ => f σ - c σ
  have hres := conditionalResidual_sum (p := p) U f hp
  have hsumDiff :
      (∑ σ, (p σ : ℂ) * f σ) - (∑ σ, (p σ : ℂ) * c σ) = 0 := by
    have hsum :
        (∑ σ, (p σ : ℂ) * (f σ - c σ)) =
          (∑ σ, (p σ : ℂ) * f σ) - (∑ σ, (p σ : ℂ) * c σ) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
    rw [← hsum]
    exact hres
  have hmean : complexMean p f = complexMean p c := by
    unfold complexMean
    exact sub_eq_zero.mp hsumDiff
  have hconstC : ∀ σ τ, AgreeOutside U σ τ → c σ = c τ := by
    intro σ τ h
    exact conditionalExpectation_fiberConstant p U f h
  let q : Config S → ℂ := fun σ => c σ - complexMean p f
  have hconstQ : ∀ σ τ, AgreeOutside U σ τ → q σ = q τ := by
    intro σ τ h
    simp only [q]
    rw [hconstC σ τ h]
  have horth := residual_orthogonal p U f q hp hconstQ
  have hcross : (∑ σ, p σ * (r σ * star (q σ)).re) = 0 := by
    calc
      (∑ σ, p σ * (r σ * star (q σ)).re) =
          (∑ σ, (p σ : ℂ) * star (q σ) * r σ).re := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro σ hσ
        calc
          p σ * (r σ * star (q σ)).re =
              ((p σ : ℂ) * (r σ * star (q σ))).re := by
            rw [Complex.re_ofReal_mul]
          _ = ((p σ : ℂ) * star (q σ) * r σ).re := by
            congr 1
            ring
      _ = 0 := by rw [horth]; simp
  have hdecomp (σ : Config S) : f σ - complexMean p f = r σ + q σ := by
    simp [r, q, c]
  have hsum3 (a b d : Config S → ℝ) :
      (∑ σ, (a σ + b σ + d σ)) = (∑ σ, a σ) + (∑ σ, b σ) + (∑ σ, d σ) := by
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hthird : (∑ σ, p σ * (2 * (r σ * star (q σ)).re)) =
      2 * (∑ σ, p σ * (r σ * star (q σ)).re) := by
    calc
      (∑ σ, p σ * (2 * (r σ * star (q σ)).re)) =
          ∑ σ, 2 * (p σ * (r σ * star (q σ)).re) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        ring
      _ = 2 * (∑ σ, p σ * (r σ * star (q σ)).re) := by
        exact (Finset.mul_sum _ _ _).symm
  unfold variance
  calc
    (∑ σ, p σ * Complex.normSq (f σ - complexMean p f)) =
        ∑ σ, (p σ * Complex.normSq (r σ) +
          p σ * Complex.normSq (q σ) +
          p σ * (2 * (r σ * star (q σ)).re)) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [hdecomp σ, Complex.normSq_add]
      simp only [starRingEnd_apply]
      ring_nf
    _ = (∑ σ, p σ * Complex.normSq (r σ)) +
        (∑ σ, p σ * Complex.normSq (q σ)) +
        (∑ σ, p σ * (2 * (r σ * star (q σ)).re)) := hsum3 _ _ _
    _ = blockDirichlet p U f + variance p c := by
      rw [hthird, hcross]
      simp [blockDirichlet, variance, r, q, c, hmean]

theorem main : AKLT.Blueprint.Gap.ConditionalVarianceStatement := by
  classical
  intro ι hι hιdec S hS hSf p hp U f
  exact ⟨weightedInner_blockDirichlet p U f hp.1,
    conditionalVariance_integral p U f hp.1,
    variance_decomposition p U f hp.1⟩

end AKLT.W.GAP003
