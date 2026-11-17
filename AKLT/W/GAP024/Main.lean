module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP024

private def classMass {Ω : Type} [Fintype Ω] (p : Weight Ω) (E : Ω → Ω → Prop)
    [DecidableRel E] (x : Ω) : ℝ :=
  ∑ y, if E x y then p y else 0

private def classKernel {Ω : Type} [Fintype Ω] (p : Weight Ω) (E : Ω → Ω → Prop)
    [DecidableRel E] (x y : Ω) : ℝ :=
  (if E x y then p y else 0) / classMass p E x

private def classMean {Ω : Type} [Fintype Ω] (p : Weight Ω) (E : Ω → Ω → Prop)
    [DecidableRel E] (f : Ω → ℂ) (x : Ω) : ℂ :=
  ∑ y, (classKernel p E x y : ℂ) * f y

private theorem classMass_pos {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : ∀ x, 0 < p x) (E : Ω → Ω → Prop) [DecidableRel E]
    (hrefl : ∀ x, E x x) (x : Ω) : 0 < classMass p E x := by
  classical
  unfold classMass
  apply Finset.sum_pos'
  · intro y hy
    split_ifs with h
    · exact le_of_lt (hp y)
    · exact le_rfl
  · exact ⟨x, by simp, by simp [hrefl, hp]⟩

private theorem classMass_eq {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (E : Ω → Ω → Prop) [DecidableRel E]
    (hsymm : ∀ x y, E x y → E y x) (htrans : ∀ x y z, E x y → E y z → E x z)
    {x y : Ω} (hxy : E x y) : classMass p E x = classMass p E y := by
  classical
  unfold classMass
  apply Finset.sum_congr rfl
  intro z hz
  have heq : E x z ↔ E y z := by
    constructor
    · intro hxz
      exact htrans y x z (hsymm x y hxy) hxz
    · intro hyz
      exact htrans x y z hxy hyz
  simp [heq]

private theorem classKernel_prob {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : ∀ x, 0 < p x) (E : Ω → Ω → Prop) [DecidableRel E]
    (hrefl : ∀ x, E x x) : ∀ x, Probability (classKernel p E x) := by
  classical
  intro x
  have hd : 0 < classMass p E x := classMass_pos p hp E hrefl x
  constructor
  · intro y
    unfold classKernel
    apply div_nonneg
    · by_cases h : E x y <;> simp [h]
      exact le_of_lt (hp y)
    · exact le_of_lt hd
  · unfold classKernel
    simp_rw [div_eq_mul_inv]
    rw [← Finset.sum_mul]
    unfold classMass at hd ⊢
    exact mul_inv_cancel₀ (ne_of_gt hd)

private theorem classKernel_reversible {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : ∀ x, 0 < p x) (E : Ω → Ω → Prop) [DecidableRel E]
    (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hrefl : ∀ x, E x x) : ∀ x y,
      p x * classKernel p E x y = p y * classKernel p E y x := by
  classical
  intro x y
  by_cases hxy : E x y
  · have hmass := classMass_eq p E hsymm htrans hxy
    simp [classKernel, hxy, hsymm x y hxy, hmass]
    ring
  · have hyx : ¬ E y x := fun h => hxy (hsymm y x h)
    simp [classKernel, hxy, hyx]

private theorem classMean_const_on_class {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : ∀ x, 0 < p x) (E : Ω → Ω → Prop) [DecidableRel E]
    (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hrefl : ∀ x, E x x) (f : Ω → ℂ) {x y : Ω} (hxy : E x y) :
      classMean p E f x = classMean p E f y := by
  classical
  unfold classMean
  have hm := classMass_eq p E hsymm htrans hxy
  apply Finset.sum_congr rfl
  intro z hz
  have heq : E x z ↔ E y z := by
    constructor
    · intro hxz
      exact htrans y x z (hsymm x y hxy) hxz
    · intro hyz
      exact htrans x y z hxy hyz
  simp [classKernel, heq, hm]

private theorem classKernel_eq_on_class {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : ∀ x, 0 < p x) (E : Ω → Ω → Prop) [DecidableRel E]
    (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    {x y : Ω} (hxy : E x y) : ∀ z, classKernel p E x z = classKernel p E y z := by
  classical
  intro z
  have hm := classMass_eq p E hsymm htrans hxy
  have heq : E x z ↔ E y z := by
    constructor
    · intro hxz
      exact htrans y x z (hsymm x y hxy) hxz
    · intro hyz
      exact htrans x y z hxy hyz
  simp [classKernel, heq, hm]

private theorem classMean_idem {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : ∀ x, 0 < p x) (E : Ω → Ω → Prop) [DecidableRel E]
    (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hrefl : ∀ x, E x x) (f : Ω → ℂ) :
      classMean p E (classMean p E f) = classMean p E f := by
  classical
  funext x
  have hrowR : ∑ y, classKernel p E x y = 1 := (classKernel_prob p hp E hrefl x).2
  have hrow : ∑ y, (classKernel p E x y : ℂ) = 1 := by exact_mod_cast hrowR
  calc
    classMean p E (classMean p E f) x =
        ∑ y, (classKernel p E x y : ℂ) * classMean p E f y := rfl
    _ = ∑ y, (classKernel p E x y : ℂ) * classMean p E f x := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hxy : E x y
      · rw [classMean_const_on_class p hp E hsymm htrans hrefl f hxy]
      · simp [classKernel, hxy]
    _ = (∑ y, (classKernel p E x y : ℂ)) * classMean p E f x := by
      rw [Finset.sum_mul]
    _ = classMean p E f x := by rw [hrow]; simp

private theorem classMean_adjoint {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : ∀ x, 0 < p x) (E : Ω → Ω → Prop) [DecidableRel E]
    (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hrefl : ∀ x, E x x) (f g : Ω → ℂ) :
      (∑ x, (p x : ℂ) * star (f x) * classMean p E g x) =
        ∑ x, (p x : ℂ) * star (classMean p E f x) * g x := by
  classical
  calc
    (∑ x, (p x : ℂ) * star (f x) * classMean p E g x) =
        ∑ x, ∑ y, (p x : ℂ) * (classKernel p E x y : ℂ) * star (f x) * g y := by
          simp only [classMean, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          ring
    _ = ∑ y, ∑ x, (p y : ℂ) * (classKernel p E y x : ℂ) * star (f x) * g y := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro x hx
          apply Finset.sum_congr rfl
          intro y hy
          have hdb := classKernel_reversible p hp E hsymm htrans hrefl y x
          have hcast : (p x : ℂ) * (classKernel p E x y : ℂ) =
              (p y : ℂ) * (classKernel p E y x : ℂ) := by exact_mod_cast hdb.symm
          rw [hcast]
    _ = ∑ x, (p x : ℂ) * star (classMean p E f x) * g x := by
          apply Finset.sum_congr rfl
          intro x hx
          calc
            (∑ i, (p x : ℂ) * (classKernel p E x i : ℂ) *
                star (f i) * g x) =
                ∑ i, (p x : ℂ) * ((star (f i) *
                  (classKernel p E x i : ℂ)) * g x) := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  ring
            _ = (p x : ℂ) * ((∑ i, star (f i) *
                (classKernel p E x i : ℂ)) * g x) := by
                  rw [← Finset.mul_sum, ← Finset.sum_mul]
            _ = (p x : ℂ) * star (classMean p E f x) * g x := by
                  simp only [classMean, star_sum, star_mul, Complex.star_def,
                    Complex.conj_ofReal]
                  ring

private theorem classMean_form {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : ∀ x, 0 < p x) (E : Ω → Ω → Prop) [DecidableRel E]
    (hsymm : ∀ x y, E x y → E y x)
    (htrans : ∀ x y z, E x y → E y z → E x z)
    (hrefl : ∀ x, E x x) (f : Ω → ℂ) :
      (∑ x, (p x : ℂ) * star (f x) * (f x - classMean p E f x)).re =
        ∑ x, p x * Complex.normSq (f x - classMean p E f x) := by
  classical
  have hid := classMean_idem p hp E hsymm htrans hrefl f
  have hpg : classMean p E (fun x => f x - classMean p E f x) = 0 := by
    funext x
    have hsum : (∑ y, (classKernel p E x y : ℂ) *
        (f y - classMean p E f y)) =
      (∑ y, (classKernel p E x y : ℂ) * f y) -
        ∑ y, (classKernel p E x y : ℂ) * classMean p E f y := by
      rw [show (fun y => (classKernel p E x y : ℂ) *
          (f y - classMean p E f y)) =
        (fun y => (classKernel p E x y : ℂ) * f y) -
          (fun y => (classKernel p E x y : ℂ) * classMean p E f y) by
            funext y
            change (classKernel p E x y : ℂ) * (f y - classMean p E f y) =
              (classKernel p E x y : ℂ) * f y -
                (classKernel p E x y : ℂ) * classMean p E f y
            ring]
      exact Finset.sum_sub_distrib _ _
    change (∑ y, (classKernel p E x y : ℂ) *
      (f y - classMean p E f y)) = 0
    rw [hsum]
    change classMean p E f x - classMean p E (classMean p E f) x = 0
    rw [hid]
    ring
  have hadj := classMean_adjoint p hp E hsymm htrans hrefl (classMean p E f)
    (fun x => f x - classMean p E f x)
  have hzero : (∑ x, (p x : ℂ) * star (classMean p E f x) *
      (f x - classMean p E f x)) = 0 := by
    calc
      _ = (∑ x, (p x : ℂ) * star (classMean p E (classMean p E f) x) *
          (f x - classMean p E f x)) := by rw [hid]
      _ = (∑ x, (p x : ℂ) * star (classMean p E f x) *
          classMean p E (fun x => f x - classMean p E f x) x) := hadj.symm
      _ = 0 := by rw [hpg]; simp
  have hsplit : (∑ x, (p x : ℂ) * star (f x) *
      (f x - classMean p E f x)) =
      ∑ x, (p x : ℂ) * star (f x - classMean p E f x) *
        (f x - classMean p E f x) := by
    calc
      _ = (∑ x, (p x : ℂ) * star (f x - classMean p E f x) *
          (f x - classMean p E f x)) +
          ∑ x, (p x : ℂ) * star (classMean p E f x) *
            (f x - classMean p E f x) := by
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro x hx
              have hstar : star (f x) =
                  star (f x - classMean p E f x) + star (classMean p E f x) := by
                calc
                  star (f x) = star ((f x - classMean p E f x) + classMean p E f x) := by
                    congr 1
                    ring
                  _ = _ := by
                    simpa only [Complex.star_def] using
                      (map_add (starRingEnd ℂ) (f x - classMean p E f x)
                        (classMean p E f x))
              rw [hstar]
              ring
      _ = _ := by rw [hzero]; simp
  rw [hsplit]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.normSq_apply]
  <;> ring

private def blockRel {ι : Type} (S : ι → Type) (U : Finset ι) :
    Config S → Config S → Prop := AgreeOutside U

private theorem blockRel_refl {ι : Type} {S : ι → Type} (U : Finset ι)
    (σ : Config S) : AgreeOutside U σ σ := by
  intro x hx
  rfl

private theorem blockRel_symm {ι : Type} {S : ι → Type} (U : Finset ι)
    {σ τ : Config S} (h : AgreeOutside U σ τ) : AgreeOutside U τ σ := by
  intro x hx
  exact (h x hx).symm

private theorem blockRel_trans {ι : Type} {S : ι → Type} (U : Finset ι)
    {σ τ ρ : Config S} (h₁ : AgreeOutside U σ τ) (h₂ : AgreeOutside U τ ρ) :
    AgreeOutside U σ ρ := by
  intro x hx
  exact (h₁ x hx).trans (h₂ x hx)

private theorem fiber_eq_classKernel {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (U : Finset ι) [DecidableRel (blockRel S U)] (σ τ : Config S) :
      fiber p U σ τ = classKernel p (blockRel S U) σ τ := by
  classical
  simp only [fiber, conditionOn, AKLT.Defs.normalize, classKernel, classMass]
  congr 1
  · by_cases h : AgreeOutside U σ τ <;> simp [h, blockRel]
  · apply Finset.sum_congr rfl
    intro y hy
    by_cases h : AgreeOutside U σ y <;> simp [h, blockRel]

private theorem classMean_eq_conditionalExpectation {ι : Type} [Fintype ι]
    [DecidableEq ι] {S : ι → Type} [∀ x, Fintype (S x)]
    (p : Weight (Config S)) (hp : ∀ σ, 0 < p σ) (U : Finset ι)
    [DecidableRel (blockRel S U)] (f : Config S → ℂ) (σ : Config S) :
      classMean p (blockRel S U) f σ = conditionalExpectation p U f σ := by
  classical
  let E : Config S → Config S → Prop := blockRel S U
  let d : ℝ := ∑ τ, if E σ τ then p τ else 0
  let n : ℂ := ∑ τ, if E σ τ then (p τ : ℂ) * f τ else 0
  have hden : (d : ℂ) = ∑ τ, if E σ τ then (p τ : ℂ) else 0 := by
    dsimp [d]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro τ hτ
    by_cases h : E σ τ <;> simp [h]
  have hmean : classMean p E f σ = n / (d : ℂ) := by
    dsimp [n, d]
    unfold classMean classKernel classMass
    calc
      (∑ τ, ((if E σ τ then p τ else 0) /
          (∑ z, if E σ z then p z else 0) : ℝ) * f τ) =
          ∑ τ, ((if E σ τ then (p τ : ℂ) else 0) /
            (∑ z, if E σ z then (p z : ℂ) else 0)) * f τ := by
              apply Finset.sum_congr rfl
              intro τ hτ
              by_cases h : E σ τ
              · simp only [if_pos h, Complex.ofReal_div]
                rw [hden]
              · simp [h]
      _ = (∑ τ, if E σ τ then (p τ : ℂ) * f τ else 0) /
            (∑ z, if E σ z then (p z : ℂ) else 0) := by
              calc
                _ = ∑ τ, (if E σ τ then (p τ : ℂ) * f τ else 0) /
                    (∑ z, if E σ z then (p z : ℂ) else 0) := by
                      apply Finset.sum_congr rfl
                      intro τ hτ
                      by_cases h : E σ τ
                      · simp [h]
                        ring
                      · simp [h]
                _ = _ := by rw [← Finset.sum_div]
      _ = n / (d : ℂ) := by rw [hden]
  have hce : conditionalExpectation p U f σ = n / (d : ℂ) := by
    unfold conditionalExpectation
    dsimp [n, E]
    have hden' : (∑ τ, if AgreeOutside U σ τ then (p τ : ℂ) else 0) =
        (d : ℂ) := by simpa [E, blockRel] using hden.symm
    have hnum' : (∑ τ, if AgreeOutside U σ τ then (p τ : ℂ) * f τ else 0) = n := by
      dsimp [n, E]
      apply Finset.sum_congr rfl
      intro τ hτ
      by_cases h : AgreeOutside U σ τ <;> simp [h, blockRel]
    rw [hden']
    rw [hnum']
  exact hmean.trans hce.symm

private theorem blockKernel_form {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (hp : ∀ σ, 0 < p σ) (U : Finset ι)
    (f : Config S → ℂ) :
      (weightedInner p f (fun σ => f σ -
        ∑ τ, (fiber p U σ τ : ℂ) * f τ)).re = blockDirichlet p U f := by
  classical
  have haction : ∀ σ, (∑ τ, (fiber p U σ τ : ℂ) * f τ) =
      conditionalExpectation p U f σ := by
    intro σ
    letI : DecidableRel (blockRel S U) :=
      fun (σ τ : Config S) => Classical.propDecidable (blockRel S U σ τ)
    rw [← classMean_eq_conditionalExpectation p hp U f σ]
    unfold classMean
    apply Finset.sum_congr rfl
    intro τ hτ
    rw [fiber_eq_classKernel p U σ τ]
  have haction' : ∀ σ, (∑ τ, (fiber p U σ τ : ℂ) * f τ) =
      classMean p (blockRel S U) f σ := by
    intro σ
    letI : DecidableRel (blockRel S U) :=
      fun (σ τ : Config S) => Classical.propDecidable (blockRel S U σ τ)
    rw [haction σ, classMean_eq_conditionalExpectation p hp U f σ]
  rw [blockDirichlet]
  simp only [weightedInner]
  simp_rw [haction']
  letI : DecidableRel (blockRel S U) :=
    fun (σ τ : Config S) => Classical.propDecidable (blockRel S U σ τ)
  simp_rw [← classMean_eq_conditionalExpectation p hp U f]
  exact classMean_form p hp (blockRel S U)
    (fun x y h => blockRel_symm U h)
    (fun x y z h₁ h₂ => blockRel_trans U h₁ h₂)
    (blockRel_refl U) f

private theorem blockAverage_action {ι J : Type} [Fintype ι] [DecidableEq ι]
    [Fintype J] {S : ι → Type} [∀ x, Fintype (S x)]
    (p : Weight (Config S)) (B : J → Finset ι) (σ : Config S)
    (f : Config S → ℂ) :
      (∑ τ, (blockAverage p B σ τ : ℂ) * f τ) =
        (∑ a, ∑ τ, (fiber p (B a) σ τ : ℂ) * f τ) /
          (Fintype.card J : ℂ) := by
  classical
  have hpoint : ∀ τ,
      (blockAverage p B σ τ : ℂ) =
        (∑ a, (fiber p (B a) σ τ : ℂ)) / (Fintype.card J : ℂ) := by
    intro τ
    simp [blockAverage, Complex.ofReal_div, Complex.ofReal_sum]
  simp_rw [hpoint]
  calc
    (∑ τ, ((∑ a, (fiber p (B a) σ τ : ℂ)) /
        (Fintype.card J : ℂ)) * f τ) =
        ∑ τ, ((∑ a, (fiber p (B a) σ τ : ℂ)) * f τ) /
          (Fintype.card J : ℂ) := by
            apply Finset.sum_congr rfl
            intro τ hτ
            ring
    _ = (∑ τ, (∑ a, (fiber p (B a) σ τ : ℂ)) * f τ) /
          (Fintype.card J : ℂ) := by rw [← Finset.sum_div]
    _ = (∑ a, ∑ τ, (fiber p (B a) σ τ : ℂ) * f τ) /
          (Fintype.card J : ℂ) := by
            congr 1
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro τ hτ
            rw [Finset.sum_mul]

theorem main : AKLT.Blueprint.Gap.BlockAverageFormStatement := by
  classical
  unfold AKLT.Blueprint.Gap.BlockAverageFormStatement
  intro J ι hι hιeq hJ hJne S hS hSne p hp B
  letI : Fintype J := hι
  letI : DecidableEq J := hιeq
  letI : Fintype ι := hJ
  letI : Nonempty ι := hJne
  let Ω := Config S
  have hpos : ∀ σ : Config S, 0 < p σ := hp.1
  have hcardN : 0 < Fintype.card ι := Fintype.card_pos
  have hcardR : 0 < (Fintype.card ι : ℝ) := by exact_mod_cast hcardN
  have hcardC : (Fintype.card ι : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcardN)
  have hsingleProb : ∀ (U : Finset J) (σ : Config S), Probability (fiber p U σ) := by
    intro U σ
    letI : DecidableRel (blockRel S U) :=
      fun (σ τ : Config S) => Classical.propDecidable (blockRel S U σ τ)
    have hrow := classKernel_prob p hpos (blockRel S U)
      (fun x => blockRel_refl U x) σ
    constructor
    · intro τ
      rw [fiber_eq_classKernel p U σ τ]
      exact hrow.1 τ
    · calc
        (∑ τ, fiber p U σ τ) = ∑ τ, classKernel p (blockRel S U) σ τ := by
          apply Finset.sum_congr rfl
          intro τ hτ
          rw [fiber_eq_classKernel p U σ τ]
        _ = 1 := hrow.2
  have hsingleDB : ∀ (U : Finset J) (σ τ : Config S),
      p σ * fiber p U σ τ = p τ * fiber p U τ σ := by
    intro U σ τ
    letI : DecidableRel (blockRel S U) :=
      fun (σ τ : Config S) => Classical.propDecidable (blockRel S U σ τ)
    have hdb := classKernel_reversible p hpos (blockRel S U)
      (fun x y h => blockRel_symm U h)
      (fun x y z h₁ h₂ => blockRel_trans U h₁ h₂)
      (fun x => blockRel_refl U x) σ τ
    rw [fiber_eq_classKernel p U σ τ, fiber_eq_classKernel p U τ σ]
    exact hdb
  have hkernelProb : ∀ σ : Config S, Probability (blockAverage p B σ) := by
    intro σ
    constructor
    · intro τ
      unfold blockAverage
      apply div_nonneg
      · apply Finset.sum_nonneg
        intro a ha
        exact (hsingleProb (B a) σ).1 τ
      · exact le_of_lt hcardR
    · unfold blockAverage
      calc
        (∑ τ, (∑ a, fiber p (B a) σ τ) / (Fintype.card ι : ℝ)) =
            (∑ τ, ∑ a, fiber p (B a) σ τ) / (Fintype.card ι : ℝ) := by
              rw [← Finset.sum_div]
        _ = (∑ a, ∑ τ, fiber p (B a) σ τ) / (Fintype.card ι : ℝ) := by
              congr 1
              rw [Finset.sum_comm]
        _ = (∑ a, (1 : ℝ)) / (Fintype.card ι : ℝ) := by
              congr 1
              apply Finset.sum_congr rfl
              intro a ha
              exact (hsingleProb (B a) σ).2
        _ = 1 := by simp [hcardN]
  constructor
  · constructor
    · exact hkernelProb
    · intro σ τ
      unfold blockAverage
      calc
        p σ * ((∑ a, fiber p (B a) σ τ) / (Fintype.card ι : ℝ)) =
            (∑ a, p σ * fiber p (B a) σ τ) / (Fintype.card ι : ℝ) := by
              calc
                _ = (p σ * (∑ a, fiber p (B a) σ τ)) / (Fintype.card ι : ℝ) := by ring
                _ = _ := by rw [Finset.mul_sum]
        _ = (∑ a, p τ * fiber p (B a) τ σ) / (Fintype.card ι : ℝ) := by
              congr 1
              apply Finset.sum_congr rfl
              intro a ha
              exact hsingleDB (B a) σ τ
        _ = (p τ * (∑ a, fiber p (B a) τ σ)) / (Fintype.card ι : ℝ) := by
              congr 1
              rw [Finset.mul_sum]
        _ = p τ * ((∑ a, fiber p (B a) τ σ) / (Fintype.card ι : ℝ)) := by ring
  · intro f
    let m : ι → Config S → ℂ := fun a σ =>
      ∑ τ, (fiber p (B a) σ τ : ℂ) * f τ
    let avg : Config S → ℂ := fun σ =>
      (∑ a, m a σ) / (Fintype.card ι : ℂ)
    have hpoint : ∀ σ, (Fintype.card ι : ℂ) * (f σ - avg σ) =
        ∑ a, (f σ - m a σ) := by
      intro σ
      have hsum : (Fintype.card ι : ℂ) = ∑ a : ι, (1 : ℂ) := by simp
      dsimp [avg]
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, one_mul]
      field_simp [hcardC]
    have hcomplex : (Fintype.card ι : ℂ) *
        weightedInner p f (fun σ => f σ - avg σ) =
        ∑ a, weightedInner p f (fun σ => f σ - m a σ) := by
      unfold weightedInner
      rw [Finset.mul_sum]
      have hpoint' (σ : Config S) (c : ℂ) :
          c * ((Fintype.card ι : ℂ) * (f σ - avg σ)) =
            ∑ a, c * (f σ - m a σ) := by
        calc
          _ = c * (∑ a, (f σ - m a σ)) := by rw [hpoint]
          _ = _ := by rw [Finset.mul_sum]
      calc
        (∑ σ, (Fintype.card ι : ℂ) *
            ((p σ : ℂ) * star (f σ) * (f σ - avg σ))) =
            ∑ σ, ∑ a, (p σ : ℂ) * star (f σ) * (f σ - m a σ) := by
              apply Finset.sum_congr rfl
              intro σ hσ
              calc
                (Fintype.card ι : ℂ) *
                    ((p σ : ℂ) * star (f σ) * (f σ - avg σ)) =
                  ((p σ : ℂ) * star (f σ)) *
                    ((Fintype.card ι : ℂ) * (f σ - avg σ)) := by ring
                _ = ∑ a, (p σ : ℂ) * star (f σ) * (f σ - m a σ) :=
                    hpoint' σ ((p σ : ℂ) * star (f σ))
        _ = ∑ a, weightedInner p f (fun σ => f σ - m a σ) := by
              rw [Finset.sum_comm]
              simp only [weightedInner]
    have hreal : (Fintype.card ι : ℝ) *
        (weightedInner p f (fun σ => f σ - avg σ)).re =
        ∑ a, (weightedInner p f (fun σ => f σ - m a σ)).re := by
      have hr := congrArg Complex.re hcomplex
      simpa [Complex.re_sum, Complex.mul_re] using hr
    unfold kernelForm blockForm
    have havg : (fun σ => ∑ τ, (blockAverage p B σ τ : ℂ) * f τ) = avg := by
      funext σ
      simpa [avg, m] using blockAverage_action p B σ f
    have havg' : (fun σ => f σ - ∑ τ, (blockAverage p B σ τ : ℂ) * f τ) =
        (fun σ => f σ - avg σ) := by
      funext σ
      rw [congrFun havg σ]
    rw [havg']
    calc
      (Fintype.card ι : ℝ) *
          (weightedInner p f (fun σ => f σ - avg σ)).re =
          ∑ a, (weightedInner p f (fun σ => f σ - m a σ)).re := hreal
      _ = ∑ a, blockDirichlet p (B a) f := by
            apply Finset.sum_congr rfl
            intro a ha
            exact blockKernel_form p hpos (B a) f

end AKLT.W.GAP024

