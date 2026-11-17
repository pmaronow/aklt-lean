module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP002

local instance (α : Type) : DecidableEq α := Classical.decEq α

abbrev Config {ι : Type} (S : ι → Type) := (x : ι) → S x

def exteriorKey {ι : Type} {S : ι → Type} (U : Finset ι) (σ : Config S) :
    (x : {x : ι // x ∉ U}) → S x := fun x => σ x

theorem agreeOutside_iff_exteriorKey_eq {ι : Type} {S : ι → Type} (U : Finset ι)
    (σ τ : Config S) :
    AgreeOutside U σ τ ↔ exteriorKey U σ = exteriorKey U τ := by
  constructor
  · intro h
    funext x
    exact h x.val x.property
  · intro h x hx
    exact congrFun h ⟨x, hx⟩

namespace FiniteProjection

variable {Ω K : Type} [Fintype Ω] [Fintype K] [DecidableEq K]

def fiber (r : Ω → K) (k : K) : Finset Ω := Finset.univ.filter fun x => r x = k

def mass (r : Ω → K) (p : Ω → ℝ) (k : K) : ℝ :=
  ∑ x ∈ fiber r k, p x

def weightedSum (r : Ω → K) (p : Ω → ℝ) (f : Ω → ℂ) (k : K) : ℂ :=
  ∑ x ∈ fiber r k, (p x : ℂ) * f x

def mean (r : Ω → K) (p : Ω → ℝ) (f : Ω → ℂ) (x : Ω) : ℂ :=
  weightedSum r p f (r x) / (mass r p (r x) : ℂ)

omit [Fintype K] in
lemma mass_cast (r : Ω → K) (p : Ω → ℝ) (k : K) :
    (mass r p k : ℂ) = ∑ x ∈ fiber r k, (p x : ℂ) := by
  simp [mass, Complex.ofReal_sum]

lemma sum_fiberwise (r : Ω → K) (g : Ω → ℂ) :
    (∑ k, ∑ x ∈ fiber r k, g x) = ∑ x, g x := by
  classical
  simpa [fiber, Finset.sum_filter] using
    (Finset.sum_fiberwise (s := Finset.univ) r g)

lemma sum_ite_cast (P : Ω → Prop) [DecidablePred P] (p : Ω → ℝ) :
    (∑ x, if P x then (p x : ℂ) else 0) =
      ((∑ x, if P x then p x else 0 : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : P x <;> simp [h]

omit [Fintype K] in
lemma mass_pos (r : Ω → K) (p : Ω → ℝ) (hp : ∀ x, 0 < p x) (x : Ω) :
    0 < mass r p (r x) := by
  unfold mass fiber
  apply Finset.sum_pos
  · intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    exact hp y
  · exact ⟨x, by simp⟩

lemma mean_eq_conditionalExpectation {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S)) (U : Finset ι)
    (f : Config S → ℂ) (σ : Config S) :
    mean (exteriorKey U) p f σ = conditionalExpectation p U f σ := by
  classical
  rw [conditionalExpectation]
  simp_rw [agreeOutside_iff_exteriorKey_eq]
  simp [mean, weightedSum, mass, fiber, Finset.sum_filter, Complex.ofReal_sum, eq_comm]
  rw [← Complex.ofReal_sum]
  rw [sum_ite_cast (fun τ => exteriorKey U σ = exteriorKey U τ) p]

omit [Fintype K] in
lemma mean_idempotent (r : Ω → K) (p : Ω → ℝ) (hp : ∀ x, 0 < p x)
    (f : Ω → ℂ) (x : Ω) :
    mean r p (fun y => mean r p f y) x = mean r p f x := by
  classical
  let k := r x
  let d := mass r p k
  let n := weightedSum r p f k
  have hdR : 0 < d := by simpa [d, k] using mass_pos r p hp x
  have hd : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdR.ne'
  have hconst : ∀ y ∈ fiber r k, mean r p f y = n / (d : ℂ) := by
    intro y hy
    have hyk : r y = k := (Finset.mem_filter.mp hy).2
    simp [mean, n, d, hyk]
  have hnum : weightedSum r p (fun y => mean r p f y) k =
      (d : ℂ) * (n / (d : ℂ)) := by
    unfold weightedSum
    calc
      (∑ y ∈ fiber r k, (p y : ℂ) * mean r p f y) =
          ∑ y ∈ fiber r k, (p y : ℂ) * (n / (d : ℂ)) := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [hconst y hy]
      _ = (∑ y ∈ fiber r k, (p y : ℂ)) * (n / (d : ℂ)) := by
            rw [Finset.sum_mul]
      _ = (d : ℂ) * (n / (d : ℂ)) := by rw [← mass_cast]
  change weightedSum r p (fun y => mean r p f y) k / (d : ℂ) = n / (d : ℂ)
  rw [hnum]
  field_simp [hd]

lemma mean_preserves (r : Ω → K) (p : Ω → ℝ) (hp : ∀ x, 0 < p x)
    (f : Ω → ℂ) :
    (∑ x, (p x : ℂ) * mean r p f x) = ∑ x, (p x : ℂ) * f x := by
  classical
  calc
    (∑ x, (p x : ℂ) * mean r p f x) =
        ∑ k, ∑ x ∈ fiber r k, (p x : ℂ) * mean r p f x := by
          symm
          exact sum_fiberwise r (fun x => (p x : ℂ) * mean r p f x)
    _ = ∑ k, ∑ x ∈ fiber r k, (p x : ℂ) * f x := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hne : (fiber r k).Nonempty
      · let d := mass r p k
        let n := weightedSum r p f k
        have hdR : 0 < d := by
          unfold d mass
          apply Finset.sum_pos
          · intro y hy
            exact hp y
          · exact hne
        have hd : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdR.ne'
        have hconst : ∀ y ∈ fiber r k, mean r p f y = n / (d : ℂ) := by
          intro y hy
          have hyk : r y = k := (Finset.mem_filter.mp hy).2
          simp [mean, n, d, hyk]
        calc
          (∑ y ∈ fiber r k, (p y : ℂ) * mean r p f y) =
              ∑ y ∈ fiber r k, (p y : ℂ) * (n / (d : ℂ)) := by
                apply Finset.sum_congr rfl
                intro y hy
                rw [hconst y hy]
          _ = (∑ y ∈ fiber r k, (p y : ℂ)) * (n / (d : ℂ)) := by
                rw [Finset.sum_mul]
          _ = (d : ℂ) * (n / (d : ℂ)) := by rw [← mass_cast]
          _ = n := by field_simp [hd]
      · have hempty : fiber r k = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        simp [hempty]
    _ = ∑ x, (p x : ℂ) * f x := sum_fiberwise r (fun x => (p x : ℂ) * f x)

omit [Fintype K] in
lemma mean_const (r : Ω → K) (p : Ω → ℝ) (hp : ∀ x, 0 < p x) (x : Ω) :
    mean r p (fun _ => (1 : ℂ)) x = 1 := by
  classical
  have hdR : 0 < mass r p (r x) := mass_pos r p hp x
  have hd : (mass r p (r x) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdR.ne'
  have hnum : weightedSum r p (fun _ => (1 : ℂ)) (r x) =
      (mass r p (r x) : ℂ) := by
    unfold weightedSum
    simp only [mul_one]
    rw [← mass_cast]
  unfold mean
  rw [hnum]
  exact div_self hd

omit [Fintype K] in
lemma weightedSum_star (r : Ω → K) (p : Ω → ℝ) (f : Ω → ℂ) (k : K) :
    star (weightedSum r p f k) =
      ∑ x ∈ fiber r k, (p x : ℂ) * star (f x) := by
  classical
  unfold weightedSum
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp

lemma mean_selfAdjoint (r : Ω → K) (p : Ω → ℝ) (hp : ∀ x, 0 < p x)
    (f h : Ω → ℂ) :
    (∑ x, (p x : ℂ) * star (f x) * mean r p h x) =
      (∑ x, (p x : ℂ) * star (mean r p f x) * h x) := by
  classical
  calc
    (∑ x, (p x : ℂ) * star (f x) * mean r p h x) =
        ∑ k, ∑ x ∈ fiber r k, (p x : ℂ) * star (f x) * mean r p h x := by
          symm
          exact sum_fiberwise r (fun x => (p x : ℂ) * star (f x) * mean r p h x)
    _ = ∑ k, ∑ x ∈ fiber r k, (p x : ℂ) * star (mean r p f x) * h x := by
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hne : (fiber r k).Nonempty
      · let d := mass r p k
        let nf := weightedSum r p f k
        let nh := weightedSum r p h k
        have hdR : 0 < d := by
          unfold d mass
          apply Finset.sum_pos
          · intro y hy
            exact hp y
          · exact hne
        have hd : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hdR.ne'
        have hfconst : ∀ y ∈ fiber r k, mean r p f y = nf / (d : ℂ) := by
          intro y hy
          have hyk : r y = k := (Finset.mem_filter.mp hy).2
          simp [mean, nf, d, hyk]
        have hhconst : ∀ y ∈ fiber r k, mean r p h y = nh / (d : ℂ) := by
          intro y hy
          have hyk : r y = k := (Finset.mem_filter.mp hy).2
          simp [mean, nh, d, hyk]
        have hl :
            (∑ y ∈ fiber r k, (p y : ℂ) * star (f y) * mean r p h y) =
              star nf * (nh / (d : ℂ)) := by
          calc
            (∑ y ∈ fiber r k, (p y : ℂ) * star (f y) * mean r p h y) =
                ∑ y ∈ fiber r k, ((p y : ℂ) * star (f y)) * (nh / (d : ℂ)) := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  rw [hhconst y hy]
            _ = (∑ y ∈ fiber r k, (p y : ℂ) * star (f y)) * (nh / (d : ℂ)) := by
                  rw [Finset.sum_mul]
            _ = star nf * (nh / (d : ℂ)) := by rw [← weightedSum_star]
        have hr :
            (∑ y ∈ fiber r k, (p y : ℂ) * star (mean r p f y) * h y) =
              star (nf / (d : ℂ)) * nh := by
          calc
            (∑ y ∈ fiber r k, (p y : ℂ) * star (mean r p f y) * h y) =
                ∑ y ∈ fiber r k, star (nf / (d : ℂ)) * ((p y : ℂ) * h y) := by
                  apply Finset.sum_congr rfl
                  intro y hy
                  rw [hfconst y hy]
                  ring
            _ = star (nf / (d : ℂ)) * (∑ y ∈ fiber r k, (p y : ℂ) * h y) := by
                  rw [Finset.mul_sum]
            _ = star (nf / (d : ℂ)) * nh := by rfl
        rw [hl, hr]
        have hstar : star (nf / (d : ℂ)) = star nf / (d : ℂ) := by
          simp [div_eq_mul_inv, star_mul]
          ring
        rw [hstar]
        field_simp [hd]
      · have hempty : fiber r k = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        simp [hempty]
    _ = ∑ x, (p x : ℂ) * star (mean r p f x) * h x :=
          sum_fiberwise r (fun x => (p x : ℂ) * star (mean r p f x) * h x)

end FiniteProjection

open FiniteProjection

theorem main : AKLT.Blueprint.Gap.ConditionalProjectionStatement := by
  intro ι _ _ S _ _ p hp U
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro f
    funext σ
    rw [← mean_eq_conditionalExpectation p U (conditionalExpectation p U f) σ]
    have hfun : conditionalExpectation p U f =
        fun y => mean (exteriorKey U) p f y := by
      funext y
      exact (mean_eq_conditionalExpectation p U f y).symm
    rw [hfun]
    exact mean_idempotent (exteriorKey U) p hp.1 f σ
  · funext σ
    rw [← mean_eq_conditionalExpectation p U (fun _ => (1 : ℂ)) σ]
    exact mean_const (exteriorKey U) p hp.1 σ
  · intro f
    unfold complexMean
    simp_rw [← mean_eq_conditionalExpectation p U f]
    exact mean_preserves (exteriorKey U) p hp.1 f
  · intro f h
    unfold AKLT.Blueprint.Gap.weightedInner
    simp_rw [← mean_eq_conditionalExpectation p U h,
      ← mean_eq_conditionalExpectation p U f]
    exact mean_selfAdjoint (exteriorKey U) p hp.1 f h

end AKLT.W.GAP002
