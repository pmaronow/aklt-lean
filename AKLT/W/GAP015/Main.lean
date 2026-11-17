module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP015

private lemma weightedResidualSum {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (f : Ω → ℂ) (hp : ∑ x, p x = 1) :
    ∑ x, (p x : ℂ) * (f x - complexMean p f) = 0 := by
  classical
  calc
    (∑ x, (p x : ℂ) * (f x - complexMean p f)) =
        ∑ x, ((p x : ℂ) * f x - (p x : ℂ) * complexMean p f) := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [mul_sub]
    _ = (∑ x, (p x : ℂ) * f x) -
        (∑ x, (p x : ℂ) * complexMean p f) := by
          exact (Finset.sum_sub_distrib (s := Finset.univ)
            (f := fun x => (p x : ℂ) * f x)
            (g := fun x => (p x : ℂ) * complexMean p f))
    _ = 0 := by
      rw [← Finset.sum_mul]
      simp [complexMean, ← Complex.ofReal_sum, hp]

private lemma weightedNormExpansion {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (f m h : Ω → ℂ) :
    (∑ x, p x * Complex.normSq (f x - h x)) =
      (∑ x, p x * Complex.normSq (f x - m x)) +
      (∑ x, p x * Complex.normSq (m x - h x)) +
      2 * (∑ x, p x * ((f x - m x) * star (m x - h x)).re) := by
  classical
  calc
    (∑ x, p x * Complex.normSq (f x - h x)) =
        ∑ x, p x * (Complex.normSq (f x - m x) +
          Complex.normSq (m x - h x) +
          2 * ((f x - m x) * star (m x - h x)).re) := by
      apply Finset.sum_congr rfl
      intro x hx
      have heq : f x - h x = (f x - m x) + (m x - h x) := by ring
      rw [heq, Complex.normSq_add]
      simp only [Complex.star_def]
    _ = _ := by
      calc
        (∑ x, p x * (Complex.normSq (f x - m x) +
          Complex.normSq (m x - h x) +
          2 * ((f x - m x) * star (m x - h x)).re)) =
            (∑ x, p x * Complex.normSq (f x - m x)) +
            (∑ x, p x * Complex.normSq (m x - h x)) +
            (∑ x, p x * (2 * ((f x - m x) * star (m x - h x)).re)) := by
          simp_rw [mul_add]
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        _ = (∑ x, p x * Complex.normSq (f x - m x)) +
            (∑ x, p x * Complex.normSq (m x - h x)) +
            2 * (∑ x, p x * ((f x - m x) * star (m x - h x)).re) := by
          congr 1
          have hmul := Finset.mul_sum (Finset.univ : Finset Ω)
            (fun x => p x * ((f x - m x) * star (m x - h x)).re) (2 : ℝ)
          have hterm : ∀ x, p x * (2 * ((f x - m x) * star (m x - h x)).re) =
              2 * (p x * ((f x - m x) * star (m x - h x)).re) := by
            intro x
            ring
          rw [hmul]
          apply Finset.sum_congr rfl
          intro x hx
          exact hterm x

private lemma condExpectation_fiber_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (U : Finset ι) (f : Config S → ℂ) {σ τ : Config S}
    (hστ : AgreeOutside U σ τ) :
    conditionalExpectation p U f σ = conditionalExpectation p U f τ := by
  classical
  unfold conditionalExpectation
  congr 1
  · apply Finset.sum_congr rfl
    intro ρ _
    have heq : AgreeOutside U σ ρ ↔ AgreeOutside U τ ρ := by
      constructor
      · intro h x hx
        exact (hστ x hx).symm.trans (h x hx)
      · intro h x hx
        exact (hστ x hx).trans (h x hx)
    by_cases h : AgreeOutside U σ ρ
    · have ht := heq.mp h
      simp only [ite_eq_left h, ite_eq_left ht]
    · have ht : ¬ AgreeOutside U τ ρ := fun ht => h (heq.mpr ht)
      simp only [ite_eq_right h, ite_eq_right ht]
  · apply Finset.sum_congr rfl
    intro ρ _
    have heq : AgreeOutside U σ ρ ↔ AgreeOutside U τ ρ := by
      constructor
      · intro h x hx
        exact (hστ x hx).symm.trans (h x hx)
      · intro h x hx
        exact (hστ x hx).trans (h x hx)
    by_cases h : AgreeOutside U σ ρ
    · have ht := heq.mp h
      simp only [ite_eq_left h, ite_eq_left ht]
    · have ht : ¬ AgreeOutside U τ ρ := fun ht => h (heq.mpr ht)
      simp only [ite_eq_right h, ite_eq_right ht]

private lemma conditionalResidualSum {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (U : Finset ι) (f : Config S → ℂ) (hp : PositiveProbability p)
    (σ : Config S) :
    (∑ τ, if AgreeOutside U σ τ then
      (p τ : ℂ) * (f τ - conditionalExpectation p U f σ) else 0) = 0 := by
  classical
  let d : ℝ := ∑ τ, if AgreeOutside U σ τ then p τ else 0
  let n : ℂ := ∑ τ, if AgreeOutside U σ τ then (p τ : ℂ) * f τ else 0
  have hdpos : 0 < d := by
    dsimp [d]
    apply Finset.sum_pos'
    · intro τ hτ
      by_cases h : AgreeOutside U σ τ
      · simpa [h] using le_of_lt (hp.1 τ)
      · simp [h]
    · refine ⟨σ, Finset.mem_univ _, ?_⟩
      simpa [AgreeOutside] using hp.1 σ
  have hdcast : (∑ τ, if AgreeOutside U σ τ then (p τ : ℂ) else 0) = (d : ℂ) := by
    dsimp [d]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro τ _
    by_cases h : AgreeOutside U σ τ <;> simp [h]
  have hdc : (d : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hdpos)
  have hnum : (∑ τ, if AgreeOutside U σ τ then
      (p τ : ℂ) * (f τ - conditionalExpectation p U f σ) else 0) =
      n - d * conditionalExpectation p U f σ := by
    calc
      _ = ∑ τ, ((if AgreeOutside U σ τ then (p τ : ℂ) * f τ else 0) -
          (if AgreeOutside U σ τ then (p τ : ℂ) else 0) *
            conditionalExpectation p U f σ) := by
        apply Finset.sum_congr rfl
        intro τ _
        by_cases h : AgreeOutside U σ τ <;> simp [h, mul_sub]
      _ = (∑ τ, if AgreeOutside U σ τ then (p τ : ℂ) * f τ else 0) -
          (∑ τ, if AgreeOutside U σ τ then (p τ : ℂ) else 0) *
            conditionalExpectation p U f σ := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul]
      _ = n - d * conditionalExpectation p U f σ := by
        rw [← hdcast]
  have hce : conditionalExpectation p U f σ = n / (d : ℂ) := by
      simp [conditionalExpectation, n, d, hdcast]
  rw [hnum, hce]
  field_simp [hdc]
  ring

private lemma blockCrossTermZero {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (U : Finset ι) (f h : Config S → ℂ) (hp : PositiveProbability p)
    (hh : ∀ σ τ, AgreeOutside U σ τ → h σ = h τ) :
    ∑ σ, p σ * ((f σ - conditionalExpectation p U f σ) *
      star (conditionalExpectation p U f σ - h σ)).re = 0 := by
  classical
  let m : Config S → ℂ := conditionalExpectation p U f
  let out : Config S → ((x : {x // x ∉ U}) → S x.1) := fun σ x => σ x
  have hout {σ τ : Config S} : out σ = out τ ↔ AgreeOutside U σ τ := by
    constructor
    · intro he x hx
      exact congrFun he ⟨x, hx⟩
    · intro he
      funext x
      exact he x.1 x.2
  have hm {σ τ : Config S} (he : AgreeOutside U σ τ) : m σ = m τ := by
    exact condExpectation_fiber_eq p U f he
  have htotal :
      ∑ σ, (p σ : ℂ) * (f σ - m σ) * star (m σ - h σ) = 0 := by
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Config S)) out
      (fun σ => (p σ : ℂ) * (f σ - m σ) * star (m σ - h σ))]
    apply Finset.sum_eq_zero
    intro k hk
    by_cases hex : ∃ ρ, out ρ = k
    · obtain ⟨ρ, rfl⟩ := hex
      have hclass : ∀ σ, out σ = out ρ → m σ = m ρ ∧ h σ = h ρ := by
        intro σ he
        have hr : AgreeOutside U ρ σ := hout.mp he.symm
        have hm' : m ρ = m σ := hm hr
        have hh' : h ρ = h σ := hh ρ σ hr
        exact ⟨hm'.symm, hh'.symm⟩
      have hinner :
          (∑ σ ∈ Finset.univ with out σ = out ρ,
            (p σ : ℂ) * (f σ - m σ) * star (m σ - h σ)) = 0 := by
        rw [Finset.sum_filter]
        calc
          (∑ σ, if out σ = out ρ then
              (p σ : ℂ) * (f σ - m σ) * star (m σ - h σ) else 0) =
            ∑ σ, if AgreeOutside U ρ σ then
              (p σ : ℂ) * (f σ - m ρ) * star (m ρ - h ρ) else 0 := by
                apply Finset.sum_congr rfl
                intro σ _
                by_cases he : out σ = out ρ
                · have hr : AgreeOutside U ρ σ := hout.mp he.symm
                  have heq := hclass σ he
                  simp only [ite_eq_left he, ite_eq_left hr]
                  rw [heq.1, heq.2]
                · have hr : ¬ AgreeOutside U ρ σ := by
                    intro hr
                    exact he (hout.mpr hr).symm
                  simp only [ite_eq_right he, ite_eq_right hr]
          _ = (∑ σ, if AgreeOutside U ρ σ then
                (p σ : ℂ) * (f σ - m ρ) else 0) * star (m ρ - h ρ) := by
            have hmul := Finset.sum_mul (Finset.univ : Finset (Config S))
              (fun σ => if AgreeOutside U ρ σ then
                (p σ : ℂ) * (f σ - m ρ) else 0) (star (m ρ - h ρ))
            simpa [mul_assoc] using hmul.symm
          _ = 0 := by
            rw [conditionalResidualSum p U f hp ρ]
            simp
      simpa using hinner
    · simp only [Finset.sum_filter]
      apply Finset.sum_eq_zero
      intro σ hs
      simp only [not_exists] at hex
      simp [hex σ]
  have hreal :
      (∑ σ, (p σ : ℂ) * (f σ - m σ) * star (m σ - h σ)).re =
        ∑ σ, p σ * ((f σ - m σ) * star (m σ - h σ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_congr rfl
    intro σ _
    simp [Complex.mul_re]
    ring
  have := congrArg Complex.re htotal
  rw [hreal] at this
  simpa [m] using this

theorem main : AKLT.Blueprint.Gap.VariationalCenteringStatement := by
  classical
  intro ι hι hιDec S hS hSN p hp f
  constructor
  · intro z
    let m := complexMean p f
    have hres := weightedResidualSum p f hp.2
    have hcross : ∑ σ, p σ * ((f σ - m) * star (m - z)).re = 0 := by
      have hc : ∑ σ, (p σ : ℂ) * (f σ - m) * star (m - z) = 0 := by
        rw [← Finset.sum_mul, hres]
        simp
      have hre := congrArg Complex.re hc
      have hreal :
          (∑ σ, (p σ : ℂ) * (f σ - m) * star (m - z)).re =
            ∑ σ, p σ * ((f σ - m) * star (m - z)).re := by
        rw [Complex.re_sum]
        apply Finset.sum_congr rfl
        intro σ _
        simp [Complex.mul_re]
        ring
      rw [hreal] at hre
      have hterm : ∀ σ, ((p σ : ℂ) * (f σ - m) * star (m - z)).re =
          p σ * ((f σ - m) * star (m - z)).re := by
        intro σ
        simp [Complex.mul_re]
        ring
      simpa [m] using hre
    have hid := weightedNormExpansion p f (fun _ => m) (fun _ => z)
    have hvar : (∑ σ, p σ * Complex.normSq (f σ - m)) = variance p f := by
      simp [variance, m]
    have hconst : (∑ σ, p σ * Complex.normSq (m - z)) = Complex.normSq (m-z) := by
      rw [← Finset.sum_mul]
      simp [hp.2]
    rw [hid, hvar, hconst, hcross]
    simpa using (le_add_of_nonneg_right (Complex.normSq_nonneg (m - z)) :
      variance p f ≤ variance p f + Complex.normSq (m - z))
  · intro U h hAdmissible
    let m := conditionalExpectation p U f
    have hcross := blockCrossTermZero p U f h hp hAdmissible
    have hid := weightedNormExpansion p f m h
    have hdir : (∑ σ, p σ * Complex.normSq (f σ - m σ)) = blockDirichlet p U f := by
      simp [m, blockDirichlet]
    rw [hid, hdir, hcross]
    have hnonneg : 0 ≤ ∑ σ, p σ * Complex.normSq (m σ - h σ) :=
      Finset.sum_nonneg fun σ _ =>
        mul_nonneg (le_of_lt (hp.1 σ)) (Complex.normSq_nonneg _)
    simpa using (le_add_of_nonneg_right hnonneg :
      blockDirichlet p U f ≤ blockDirichlet p U f +
        ∑ σ, p σ * Complex.normSq (m σ - h σ))

end AKLT.W.GAP015
