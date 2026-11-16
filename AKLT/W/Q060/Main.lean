import AKLT.Blueprint.Q.NodesEnergy

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.Q060

lemma weighted_mean_min {β : Type} [Fintype β] (w g : β → ℝ)
    (hw : ∀ b, 0 < w b) [Nonempty β] (c : ℝ) :
    (∑ b, w b * (g b - (∑ z, w z * g z) / (∑ z, w z)) ^ 2) ≤
      ∑ b, w b * (g b - c) ^ 2 := by
  classical
  let W : ℝ := ∑ z, w z
  let μ : ℝ := (∑ z, w z * g z) / W
  have hW : 0 < W := by
    dsimp [W]
    exact Finset.sum_pos (fun z hz => hw z) Finset.univ_nonempty
  have hWne : W ≠ 0 := ne_of_gt hW
  have hmean : ∑ b, w b * (g b - μ) = 0 := by
    dsimp [μ]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    dsimp [W]
    field_simp [hWne]
    have hsum : (∑ i, w i) ≠ 0 := by simpa [W] using hWne
    simp [hsum]
  have hid : (∑ b, w b * (g b - c) ^ 2) =
      (∑ b, w b * (g b - μ) ^ 2) + W * (μ - c) ^ 2 := by
    calc
      (∑ b, w b * (g b - c) ^ 2) =
          ∑ b, w b * ((g b - μ) + (μ - c)) ^ 2 := by
            congr 1
            funext b
            ring
      _ = (∑ b, w b * (g b - μ) ^ 2) +
          2 * (μ - c) * (∑ b, w b * (g b - μ)) + W * (μ - c) ^ 2 := by
            calc
              _ = ∑ b, (w b * (g b - μ) ^ 2 +
                    2 * (μ - c) * (w b * (g b - μ)) +
                    w b * (μ - c) ^ 2) := by
                      congr 1
                      funext b
                      ring
              _ = _ := by
                    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
                    dsimp [W]
      _ = _ := by rw [hmean]; ring
  rw [show (∑ z, w z * g z) / (∑ z, w z) = μ by rfl]
  rw [hid]
  have hn : 0 ≤ W * (μ - c) ^ 2 := mul_nonneg hW.le (sq_nonneg _)
  linarith

lemma weighted_complex_mean_min {β : Type} [Fintype β] (w : β → ℝ) (f : β → ℂ)
    (hw : ∀ b, 0 < w b) [Nonempty β] (c : ℂ) :
    (∑ b, w b * Complex.normSq
      (f b - (∑ z, (w z : ℂ) * f z) / (∑ z, (w z : ℂ)))) ≤
      ∑ b, w b * Complex.normSq (f b - c) := by
  classical
  let W : ℝ := ∑ z, w z
  let μ : ℂ := (∑ z, (w z : ℂ) * f z) / (W : ℂ)
  have hW : 0 < W := by
    dsimp [W]
    exact Finset.sum_pos (fun z hz => hw z) Finset.univ_nonempty
  have hμre : μ.re = (∑ z, w z * (f z).re) / W := by
    dsimp [μ]
    rw [Complex.div_ofReal_re]
    simp [W]
  have hμim : μ.im = (∑ z, w z * (f z).im) / W := by
    dsimp [μ]
    rw [Complex.div_ofReal_im]
    simp [W]
  have hr := weighted_mean_min w (fun z => (f z).re) hw c.re
  have hi := weighted_mean_min w (fun z => (f z).im) hw c.im
  have hden : (∑ z, (w z : ℂ)) = (W : ℂ) := by
    simp [W]
  rw [hden]
  rw [show (∑ z, (w z : ℂ) * f z) / (W : ℂ) = μ by rfl]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im]
  rw [hμre, hμim]
  have hsumR : (∑ b, w b * ((f b).re - (∑ z, w z * (f z).re) / W) ^ 2) ≤
      ∑ b, w b * ((f b).re - c.re) ^ 2 := by simpa [W] using hr
  have hsumI : (∑ b, w b * ((f b).im - (∑ z, w z * (f z).im) / W) ^ 2) ≤
      ∑ b, w b * ((f b).im - c.im) ^ 2 := by simpa [W] using hi
  simpa only [pow_two, mul_add, Finset.sum_add_distrib] using add_le_add hsumR hsumI

def fiberCenter {A B : Type} [Fintype A] (w : B × A → ℝ) (f : B × A → ℂ) (b : B) : ℂ :=
  (∑ a, (w (b, a) : ℂ) * f (b, a)) / (∑ a, (w (b, a) : ℂ))

def fiberDirichlet {A B : Type} [Fintype A] [Fintype B]
    (w : B × A → ℝ) (f : B × A → ℂ) : ℝ :=
  ∑ z, w z * Complex.normSq (f z - fiberCenter w f z.1)

lemma fiberDirichlet_lower {A B : Type} [Fintype A] [Fintype B] [Nonempty A]
    (p q : B × A → ℝ) (hp : ∀ z, 0 < p z)
    (m : ℝ) (hm : 0 ≤ m) (hdom : ∀ z, m * p z ≤ q z) (f : B × A → ℂ) :
    m * fiberDirichlet p f ≤ fiberDirichlet q f := by
  classical
  simp only [fiberDirichlet]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro b hb
  let cp := fiberCenter p f b
  let cq := fiberCenter q f b
  have hpoint : m * (∑ a, p (b, a) * Complex.normSq (f (b, a) - cq)) ≤
      ∑ a, q (b, a) * Complex.normSq (f (b, a) - cq) := by
    calc
      m * (∑ a, p (b, a) * Complex.normSq (f (b, a) - cq)) =
          ∑ a, m * (p (b, a) * Complex.normSq (f (b, a) - cq)) := by rw [Finset.mul_sum]
      _ ≤ ∑ a, q (b, a) * Complex.normSq (f (b, a) - cq) := by
        apply Finset.sum_le_sum
        intro a ha
        simpa [mul_assoc] using mul_le_mul_of_nonneg_right (hdom (b, a)) (Complex.normSq_nonneg _)
  have hmin : (∑ a, p (b, a) * Complex.normSq (f (b, a) - cp)) ≤
      ∑ a, p (b, a) * Complex.normSq (f (b, a) - cq) := by
    simpa [cp, fiberCenter] using weighted_complex_mean_min
      (w := fun a => p (b, a)) (f := fun a => f (b, a)) (hw := fun a => hp (b, a)) cq
  have hscaled := mul_le_mul_of_nonneg_left hmin hm
  dsimp [fiberDirichlet, fiberCenter] at *
  calc
    m * (∑ a, p (b, a) * Complex.normSq (f (b, a) - cp)) ≤
        m * (∑ a, p (b, a) * Complex.normSq (f (b, a) - cq)) := hscaled
    _ ≤ ∑ a, q (b, a) * Complex.normSq (f (b, a) - cq) := hpoint

lemma sum_first_fiber {A B M : Type} [Fintype A] [Fintype B] [DecidableEq B]
    [AddCommMonoid M] (b : B) (g : B × A → M) :
    (∑ z, if b = z.1 then g z else 0) = ∑ a, g (b, a) := by
  classical
  rw [Fintype.sum_prod_type]
  have hinner (x : B) : (∑ a, if b = x then g (x, a) else 0) =
      if b = x then ∑ a, g (x, a) else 0 := by
    by_cases h : b = x <;> simp [h]
  simp_rw [hinner]
  exact Fintype.sum_ite_eq b (fun x => ∑ a, g (x, a))

variable {ι : Type} [Fintype ι] [DecidableEq ι]
variable (S : ι → Type) [∀ x, Fintype (S x)]

abbrev Rest (x : ι) := (y : {z // z ≠ x}) → S y.1

def splitAt (x : ι) : ((z : ι) → S z) ≃ Rest S x × S x :=
  (Equiv.piSplitAt x S).trans (Equiv.prodComm (S x) (Rest S x))

omit [Fintype ι] [∀ x, Fintype (S x)] in
lemma agreeOutside_iff_split {x : ι} (σ τ : (z : ι) → S z) :
    AKLT.Defs.AgreeOutside ({x} : Finset ι) σ τ ↔ (splitAt S x σ).1 = (splitAt S x τ).1 := by
  classical
  constructor
  · intro h
    funext y
    have hy : y.1 ∉ ({x} : Finset ι) := by simp [y.2]
    have hh := h y.1 hy
    simpa [splitAt, Rest, Equiv.piSplitAt] using hh
  · intro h z hz
    have hzx : z ≠ x := by simpa using hz
    have hh := congrFun h ⟨z, hzx⟩
    simpa [splitAt, Rest, Equiv.piSplitAt] using hh

lemma blockDirichlet_eq_fiber {x : ι} (p : ((z : ι) → S z) → ℝ)
    (f : ((z : ι) → S z) → ℂ) :
    AKLT.Defs.blockDirichlet p {x} f =
      fiberDirichlet (fun z => p ((splitAt S x).symm z))
        (fun z => f ((splitAt S x).symm z)) := by
  classical
  let e := splitAt S x
  let pp : Rest S x × S x → ℝ := fun z => p (e.symm z)
  let ff : Rest S x × S x → ℂ := fun z => f (e.symm z)
  have hce (σ : (z : ι) → S z) :
      AKLT.Defs.conditionalExpectation p {x} f σ = fiberCenter pp ff (e σ).1 := by
    unfold AKLT.Defs.conditionalExpectation
    have hnum : (∑ τ, if AKLT.Defs.AgreeOutside ({x} : Finset ι) σ τ then
          (p τ : ℂ) * f τ else 0) =
        ∑ z : Rest S x × S x, if (e σ).1 = z.1 then (pp z : ℂ) * ff z else 0 := by
      let g : Rest S x × S x → ℂ := fun z =>
        if (e σ).1 = z.1 then (pp z : ℂ) * ff z else 0
      calc
        _ = ∑ τ, g (e τ) := by
          apply Finset.sum_congr rfl
          intro τ hτ
          simp [g, pp, ff, e, agreeOutside_iff_split, eq_comm]
        _ = ∑ z, g z := e.sum_comp g
        _ = _ := rfl
    have hden : (∑ τ, if AKLT.Defs.AgreeOutside ({x} : Finset ι) σ τ then
          (p τ : ℂ) else 0) =
        ∑ z : Rest S x × S x, if (e σ).1 = z.1 then (pp z : ℂ) else 0 := by
      let g : Rest S x × S x → ℂ := fun z =>
        if (e σ).1 = z.1 then (pp z : ℂ) else 0
      calc
        _ = ∑ τ, g (e τ) := by
          apply Finset.sum_congr rfl
          intro τ hτ
          simp [g, pp, e, agreeOutside_iff_split, eq_comm]
        _ = ∑ z, g z := e.sum_comp g
        _ = _ := rfl
    rw [hnum, hden]
    rw [sum_first_fiber, sum_first_fiber]
    rfl
  unfold AKLT.Defs.blockDirichlet
  calc
    _ = ∑ σ, p σ * Complex.normSq
          (f σ - fiberCenter pp ff (e σ).1) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [hce]
    _ = ∑ z, pp z * Complex.normSq (ff z - fiberCenter pp ff z.1) := by
          simpa [pp, ff, e] using e.sum_comp (fun z => pp z * Complex.normSq (ff z - fiberCenter pp ff z.1))
    _ = fiberDirichlet pp ff := rfl

theorem main : AKLT.Blueprint.Q.DensityDirichletStatement := by
  classical
  intro ι _ _ S hFin p q hp _hq m hm hdom f
  letI : ∀ x, Fintype (S x) := hFin
  let Ω := (x : ι) → S x
  have hΩ : Nonempty Ω := by
    by_contra hne
    letI : IsEmpty Ω := ⟨fun σ => hne ⟨σ⟩⟩
    have htotal : (∑ σ, p σ) = 1 := hp.2
    simp at htotal
  have hS : ∀ x, Nonempty (S x) := fun x => ⟨(Classical.choice hΩ) x⟩
  change m * (∑ x, AKLT.Defs.blockDirichlet p {x} f) ≤
    (∑ x, AKLT.Defs.blockDirichlet q {x} f)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  letI : Nonempty (S x) := hS x
  rw [blockDirichlet_eq_fiber (S := S) (x := x) p f,
    blockDirichlet_eq_fiber (S := S) (x := x) q f]
  exact fiberDirichlet_lower
    (p := fun z => p ((splitAt S x).symm z))
    (q := fun z => q ((splitAt S x).symm z))
    (hp := fun z => hp.1 ((splitAt S x).symm z))
    (m := m) hm
    (hdom := fun z => hdom ((splitAt S x).symm z))
    (f := fun z => f ((splitAt S x).symm z))

#print axioms weighted_mean_min
#print axioms weighted_complex_mean_min
#print axioms sum_first_fiber
#print axioms fiberDirichlet_lower
#print axioms agreeOutside_iff_split
#print axioms blockDirichlet_eq_fiber
#print axioms main

end AKLT.W.Q060
