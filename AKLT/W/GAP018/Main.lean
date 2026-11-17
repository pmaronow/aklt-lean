module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap

namespace AKLT.W.GAP018

local instance (α : Type) : DecidableEq α := Classical.decEq α
attribute [local instance] Classical.propDecidable

private def glue {ι : Type} [DecidableEq ι] {S : ι → Type} (U : Finset ι)
    (η : (x : U) → S x) (ξ : (x : {x // x ∉ U}) → S x) : Config S :=
  fun x => if hx : x ∈ U then η ⟨x, hx⟩ else ξ ⟨x, hx⟩

private def splitEquiv {ι : Type} [DecidableEq ι] (S : ι → Type) (U : Finset ι) :
    Config S ≃ ((x : U) → S x) × ((x : {x // x ∉ U}) → S x) :=
  Equiv.piEquivPiSubtypeProd (fun x => x ∈ U) S

private def outside {ι : Type} [DecidableEq ι] {S : ι → Type} (U : Finset ι)
    (σ : Config S) : (x : {x // x ∉ U}) → S x := fun x => σ x

private lemma glue_restrict {ι : Type} [DecidableEq ι] {S : ι → Type} (U : Finset ι)
    (η : (x : U) → S x) (ξ : (x : {x // x ∉ U}) → S x) : restrict U (glue U η ξ) = η := by
  funext x
  simp [restrict, glue]

private lemma outside_glue {ι : Type} [DecidableEq ι] {S : ι → Type} (U : Finset ι)
    (η : (x : U) → S x) (ξ : (x : {x // x ∉ U}) → S x) :
    outside U (glue U η ξ) = ξ := by
  funext x
  simp [outside, glue, x.property]

private lemma glue_agreeOutside_iff {ι : Type} [DecidableEq ι] {S : ι → Type} (U : Finset ι)
    (σ : Config S) (η : (x : U) → S x) (ξ : (x : {x // x ∉ U}) → S x) :
    AgreeOutside U σ (glue U η ξ) ↔ ξ = outside U σ := by
  constructor
  · intro h
    funext x
    cases x with
    | mk x hx => simpa [glue, outside, hx] using (h x hx).symm
  · intro h x hx
    subst ξ
    simp [glue, outside, hx]

private lemma sum_config_glue {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] {M : Type} [AddCommMonoid M]
    (U : Finset ι) (F : Config S → M) :
    (∑ σ, F σ) = ∑ η, ∑ ξ, F (glue U η ξ) := by
  let T := (x : U) → S x
  let V := (x : {x // x ∉ U}) → S x
  calc
    (∑ σ, F σ) = ∑ z : T × V, F (glue U z.1 z.2) :=
      Fintype.sum_equiv (splitEquiv S U) F (fun z : T × V => F (glue U z.1 z.2)) (by
        intro σ
        congr 1
        funext x
        by_cases hx : x ∈ U <;> simp [glue, splitEquiv, Equiv.piEquivPiSubtypeProd, hx])
    _ = ∑ η : T, ∑ ξ : V, F (glue U η ξ) :=
      @Fintype.sum_prod_type M T V _ _ _ (fun z => F (glue U z.1 z.2))

private lemma condition_mass_eq_slice {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] (p : Weight (Config S)) (U : Finset ι)
    (σ : Config S) :
    (∑ τ, if AgreeOutside U σ τ then p τ else 0) =
      ∑ η, p (glue U η (outside U σ)) := by
  classical
  rw [sum_config_glue (S := S) (U := U)
    (F := fun τ => if AgreeOutside U σ τ then p τ else 0)]
  simp [glue_agreeOutside_iff]

private theorem blockLaw_eq_slice_normalize {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] (p : Weight (Config S)) (U : Finset ι)
    (σ : Config S) (η : (x : U) → S x) :
    blockLaw p U σ η = p (glue U η (outside U σ)) /
      (∑ θ, p (glue U θ (outside U σ))) := by
  classical
  have hnum : (∑ τ, if restrict U τ = η then
      if AgreeOutside U σ τ then p τ else 0 else 0) = p (glue U η (outside U σ)) := by
    rw [sum_config_glue (S := S) (U := U)
      (F := fun τ => if restrict U τ = η then
        if AgreeOutside U σ τ then p τ else 0 else 0)]
    simp [glue_restrict, glue_agreeOutside_iff]
  unfold blockLaw marginal fibre conditionOn AKLT.Defs.normalize
  rw [condition_mass_eq_slice (S := S) p U σ]
  have hsum :
      (∑ τ, if restrict U τ = η then
        (if AgreeOutside U σ τ then p τ else 0) /
          (∑ θ, p (glue U θ (outside U σ))) else 0) =
      (∑ τ, if restrict U τ = η then
        if AgreeOutside U σ τ then p τ else 0 else 0) /
          (∑ θ, p (glue U θ (outside U σ))) := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro τ hτ
    by_cases h : restrict U τ = η <;> simp [h]
  rw [hsum, hnum]

private lemma sum_glue_fiber {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] {M : Type} [AddCommMonoid M]
    (U : Finset ι) (η : (x : U) → S x) (ξ : (x : {x // x ∉ U}) → S x)
    (F : Config S → M) :
    (∑ τ, if AgreeOutside U (glue U η ξ) τ then F τ else 0) =
      ∑ θ, F (glue U θ ξ) := by
  classical
  rw [sum_config_glue (S := S) (U := U)
    (F := fun τ => if AgreeOutside U (glue U η ξ) τ then F τ else 0)]
  simp [glue_agreeOutside_iff, outside_glue]

private lemma glue_single_fiber_iff {ι : Type} [DecidableEq ι] {S : ι → Type}
    (U : Finset ι) (x : ι) (hx : x ∈ U)
    (η θ : (y : U) → S y) (ξ ζ : (y : {y // y ∉ U}) → S y) :
    AgreeOutside {x} (glue U η ξ) (glue U θ ζ) ↔
      AgreeOutside {⟨x, hx⟩} η θ ∧ ζ = ξ := by
  classical
  constructor
  · intro h
    constructor
    · intro y hy
      have hne : y.1 ≠ x := by
        intro he
        have he' : y = (⟨x, hx⟩ : U) := Subtype.ext he
        exact hy (by simpa using he')
      have hy' : y.1 ∉ ({x} : Finset ι) := by simpa using hne
      have hh := h y.1 hy'
      simpa [glue, y.2, hne] using hh
    · funext y
      have hne : y.1 ≠ x := by
        intro he
        exact y.2 (he ▸ hx)
      have hy' : y.1 ∉ ({x} : Finset ι) := by simpa using hne
      have hh := h y.1 hy'
      simpa [glue, y.2, hne] using hh.symm
  · rintro ⟨hblock, hout⟩ y hy
    by_cases hmem : y ∈ U
    · have hne : (⟨y, hmem⟩ : U) ≠ ⟨x, hx⟩ := by
        intro he
        have : y = x := congrArg Subtype.val he
        subst y
        exact hy (by simp)
      have hh := hblock ⟨y, hmem⟩ (by simpa using hne)
      simpa [glue, hmem, hne] using hh
    · have hh := congrFun hout ⟨y, hmem⟩
      simpa [glue, hmem] using hh.symm

private lemma sum_glue_single_fiber {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] {M : Type} [AddCommMonoid M]
    (U : Finset ι) (x : ι) (hx : x ∈ U)
    (η : (y : U) → S y) (ξ : (y : {y // y ∉ U}) → S y)
    (F : Config S → M) :
    (∑ τ, if AgreeOutside {x} (glue U η ξ) τ then F τ else 0) =
      ∑ θ, if AgreeOutside {⟨x, hx⟩} η θ then F (glue U θ ξ) else 0 := by
  classical
  rw [sum_config_glue (S := S) (U := U)
    (F := fun τ => if AgreeOutside {x} (glue U η ξ) τ then F τ else 0)]
  have hp (θ : (y : U) → S y) (ζ : (y : {y // y ∉ U}) → S y) :
      AgreeOutside {x} (glue U η ξ) (glue U θ ζ) ↔
        AgreeOutside {⟨x, hx⟩} η θ ∧ ζ = ξ :=
    glue_single_fiber_iff U x hx η θ ξ ζ
  simp_rw [hp]
  apply Finset.sum_congr rfl
  intro θ hθ
  by_cases h : AgreeOutside {⟨x, hx⟩} η θ <;> simp [h]

private lemma condition_mass_pos {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] (p : Weight (Config S))
    (hp : PositiveProbability p) (U : Finset ι) (σ : Config S) :
    0 < ∑ τ, if AgreeOutside U σ τ then p τ else 0 := by
  classical
  have hle : p σ ≤ ∑ τ, if AgreeOutside U σ τ then p τ else 0 := by
    have h := Finset.single_le_sum (s := Finset.univ)
      (f := fun τ => if AgreeOutside U σ τ then p τ else 0)
      (fun τ hτ => by
        by_cases he : AgreeOutside U σ τ
        · simp [he]
          exact le_of_lt (hp.1 τ)
        · simp [he]) (Finset.mem_univ σ)
    simpa [AgreeOutside] using h
  exact lt_of_lt_of_le (hp.1 σ) hle

private lemma conditionalExpectation_eq_slice {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] (p : Weight (Config S)) (U : Finset ι)
    (f : Config S → ℂ) (η : (x : U) → S x) (ξ : (x : {x // x ∉ U}) → S x) :
    conditionalExpectation p U f (glue U η ξ) =
      (∑ θ, (p (glue U θ ξ) : ℂ) * f (glue U θ ξ)) /
        (∑ θ, (p (glue U θ ξ) : ℂ)) := by
  classical
  have hnum := sum_glue_fiber (S := S) (U := U) η ξ
    (F := fun τ => (p τ : ℂ) * f τ)
  have hden := sum_glue_fiber (S := S) (U := U) η ξ
    (F := fun τ => (p τ : ℂ))
  unfold conditionalExpectation
  rw [hnum, hden]

private theorem complexMean_blockLaw_eq_conditionalExpectation {ι : Type} [Fintype ι]
    [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    (p : Weight (Config S)) (U : Finset ι) (f : Config S → ℂ)
    (η : (x : U) → S x) (ξ : (x : {x // x ∉ U}) → S x) :
    complexMean (blockLaw p U (glue U η ξ)) (fun θ => f (glue U θ ξ)) =
      conditionalExpectation p U f (glue U η ξ) := by
  classical
  let Z := ∑ θ, p (glue U θ ξ)
  calc
    complexMean (blockLaw p U (glue U η ξ)) (fun θ => f (glue U θ ξ)) =
        ∑ θ, ((p (glue U θ ξ) / Z : ℝ) : ℂ) * f (glue U θ ξ) := by
      unfold complexMean
      apply Finset.sum_congr rfl
      intro θ hθ
      rw [blockLaw_eq_slice_normalize (S := S) p U (glue U η ξ) θ]
      simp [Z, outside_glue]
    _ = ∑ θ, ((p (glue U θ ξ) : ℂ) * f (glue U θ ξ)) / (Z : ℂ) := by
      apply Finset.sum_congr rfl
      intro θ hθ
      simp [Complex.ofReal_div]
      ring
    _ = (∑ θ, (p (glue U θ ξ) : ℂ) * f (glue U θ ξ)) / (Z : ℂ) := by
      rw [← Finset.sum_div]
    _ = conditionalExpectation p U f (glue U η ξ) := by
      rw [conditionalExpectation_eq_slice (S := S) p U f η ξ]
      simp [Z, Complex.ofReal_sum]

private lemma sum_ite_div {α : Type} [Fintype α] {R : Type} [DivisionSemiring R]
    (P : α → Prop) [DecidablePred P] (a : α → R) (z : R) :
    (∑ x, if P x then a x / z else 0) =
      (∑ x, if P x then a x else 0) / z := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : P x <;> simp [h]

private theorem conditionalExpectation_normalize {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)]
    (w : Weight (Config S)) (Z : ℝ) (U : Finset ι)
    (f : Config S → ℂ) (σ : Config S)
    (hZ : Z ≠ 0) :
    conditionalExpectation (fun τ => w τ / Z) U f σ =
      (∑ τ, if AgreeOutside U σ τ then (w τ : ℂ) * f τ else 0) /
        (∑ τ, if AgreeOutside U σ τ then (w τ : ℂ) else 0) := by
  classical
  let P : Config S → Prop := fun τ => AgreeOutside U σ τ
  have hnum : (∑ τ, if P τ then ((w τ / Z : ℝ) : ℂ) * f τ else 0) =
      (∑ τ, if P τ then (w τ : ℂ) * f τ else 0) / (Z : ℂ) := by
    calc
      _ = ∑ τ, if P τ then ((w τ : ℂ) * f τ) / (Z : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro τ hτ
        by_cases h : P τ
        · simp [h, Complex.ofReal_div]
          ring
        · simp [h]
      _ = _ := sum_ite_div P _ _
  have hden : (∑ τ, if P τ then ((w τ / Z : ℝ) : ℂ) else 0) =
      (∑ τ, if P τ then (w τ : ℂ) else 0) / (Z : ℂ) := by
    calc
      _ = ∑ τ, if P τ then (w τ : ℂ) / (Z : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro τ hτ
        by_cases h : P τ <;> simp [h, Complex.ofReal_div]
      _ = _ := sum_ite_div P _ _
  unfold conditionalExpectation
  change (∑ τ, if P τ then ((w τ / Z : ℝ) : ℂ) * f τ else 0) /
      (∑ τ, if P τ then ((w τ / Z : ℝ) : ℂ) else 0) = _
  rw [hnum, hden]
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ
  exact div_div_div_cancel_right₀ hZc _ _

private lemma sliceMass_pos {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] (p : Weight (Config S))
    (hp : PositiveProbability p) (U : Finset ι)
    (η : (x : U) → S x) (ξ : (x : {x // x ∉ U}) → S x) :
    0 < ∑ θ, p (glue U θ ξ) := by
  have hm := condition_mass_pos S p hp U (glue U η ξ)
  rw [condition_mass_eq_slice (S := S) p U (glue U η ξ)] at hm
  simpa [outside_glue] using hm

private theorem nested_single_site_conditionalExpectation {ι : Type} [Fintype ι]
    [DecidableEq ι] (S : ι → Type) [∀ x, Fintype (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p) (U : Finset ι)
    (x : ι) (hx : x ∈ U) (f : Config S → ℂ)
    (η : (y : U) → S y) (ξ : (y : {y // y ∉ U}) → S y) :
    conditionalExpectation (blockLaw p U (glue U η ξ)) {⟨x, hx⟩}
      (fun θ => f (glue U θ ξ)) η =
      conditionalExpectation p {x} f (glue U η ξ) := by
  classical
  let w : Weight ((y : U) → S y) := fun θ => p (glue U θ ξ)
  let Z : ℝ := ∑ θ, w θ
  have hZ : Z ≠ 0 := ne_of_gt (by simpa [Z, w] using sliceMass_pos S p hp U η ξ)
  have hlaw : blockLaw p U (glue U η ξ) = fun θ => w θ / Z := by
    funext θ
    simpa [w, Z, outside_glue] using
      (blockLaw_eq_slice_normalize (S := S) p U (glue U η ξ) θ)
  have hnum := sum_glue_single_fiber (S := S) (U := U) (x := x) hx η ξ
    (F := fun τ => (p τ : ℂ) * f τ)
  have hden := sum_glue_single_fiber (S := S) (U := U) (x := x) hx η ξ
    (F := fun τ => (p τ : ℂ))
  rw [hlaw]
  rw [conditionalExpectation_normalize (S := fun y : U => S y) w Z
    {⟨x, hx⟩} (fun θ => f (glue U θ ξ)) η hZ]
  unfold conditionalExpectation
  rw [hnum, hden]

private theorem blockLaw_eq_normalized_slice {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] (p : Weight (Config S)) (U : Finset ι)
    (η : (x : U) → S x) (ξ : (x : {x // x ∉ U}) → S x) :
    blockLaw p U (glue U η ξ) =
      fun θ => p (glue U θ ξ) / (∑ θ, p (glue U θ ξ)) := by
  funext θ
  simpa [outside_glue] using
    (blockLaw_eq_slice_normalize (S := S) p U (glue U η ξ) θ)

private lemma weighted_blockVariance_slice {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p) (U : Finset ι)
    (f : Config S → ℂ) (ξ : (x : {x // x ∉ U}) → S x) :
    (∑ η, p (glue U η ξ)) *
        variance (blockLaw p U (glue U (fun x => Classical.choice (inferInstance : Nonempty (S x))) ξ))
          (fun η => f (glue U η ξ)) =
      ∑ η, p (glue U η ξ) * Complex.normSq
        (f (glue U η ξ) - conditionalExpectation p U f (glue U η ξ)) := by
  classical
  let η₀ : (x : U) → S x := fun x => Classical.choice (inferInstance : Nonempty (S x))
  let Z : ℝ := ∑ η, p (glue U η ξ)
  have hZ : Z ≠ 0 := ne_of_gt (by simpa [Z] using sliceMass_pos S p hp U η₀ ξ)
  have hlaw := blockLaw_eq_normalized_slice (S := S) p U η₀ ξ
  have hq (η : (x : U) → S x) :
      blockLaw p U (glue U η₀ ξ) = blockLaw p U (glue U η ξ) := by
    calc
      blockLaw p U (glue U η₀ ξ) = fun θ => p (glue U θ ξ) / Z := by
        simpa [Z] using hlaw
      _ = blockLaw p U (glue U η ξ) := by
        symm
        simpa [Z] using (blockLaw_eq_normalized_slice (S := S) p U η ξ)
  change Z * variance (blockLaw p U (glue U η₀ ξ)) (fun η => f (glue U η ξ)) = _
  rw [variance]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η hη
  rw [hq η]
  rw [complexMean_blockLaw_eq_conditionalExpectation (S := S) p U f η ξ]
  rw [blockLaw_eq_normalized_slice (S := S) p U η ξ]
  simp only [Z]
  have hsum : (∑ η, p (glue U η ξ)) ≠ 0 := by simpa [Z] using hZ
  field_simp [hsum]

private lemma weighted_siteDirichlet_slice {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p) (U : Finset ι)
    (f : Config S → ℂ) (ξ : (x : {x // x ∉ U}) → S x) (x : U) :
    (∑ η, p (glue U η ξ)) *
        blockDirichlet (blockLaw p U (glue U (fun y => Classical.choice (inferInstance : Nonempty (S y))) ξ))
          {x} (fun η => f (glue U η ξ)) =
      ∑ η, p (glue U η ξ) * Complex.normSq
        (f (glue U η ξ) - conditionalExpectation p {x.1} f (glue U η ξ)) := by
  classical
  let η₀ : (y : U) → S y := fun y => Classical.choice (inferInstance : Nonempty (S y))
  let Z : ℝ := ∑ η, p (glue U η ξ)
  have hZ : Z ≠ 0 := ne_of_gt (by simpa [Z] using sliceMass_pos S p hp U η₀ ξ)
  have hq (η : (y : U) → S y) :
      blockLaw p U (glue U η₀ ξ) = blockLaw p U (glue U η ξ) := by
    calc
      blockLaw p U (glue U η₀ ξ) = fun θ => p (glue U θ ξ) / Z := by
        simpa [Z] using (blockLaw_eq_normalized_slice (S := S) p U η₀ ξ)
      _ = blockLaw p U (glue U η ξ) := by
        symm
        simpa [Z] using (blockLaw_eq_normalized_slice (S := S) p U η ξ)
  change Z * blockDirichlet (blockLaw p U (glue U η₀ ξ)) {x}
      (fun η => f (glue U η ξ)) = _
  rw [blockDirichlet]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro η hη
  rw [hq η]
  rw [nested_single_site_conditionalExpectation (S := S) p hp U x.1 x.2 f η ξ]
  rw [blockLaw_eq_normalized_slice (S := S) p U η ξ]
  simp only [Z]
  have hsum : (∑ η, p (glue U η ξ)) ≠ 0 := by simpa [Z] using hZ
  field_simp [hsum]

private lemma integrated_blockVariance_slice {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p) (U : Finset ι)
    (f : Config S → ℂ) :
    (∑ ξ, (∑ η, p (glue U η ξ)) *
        variance (blockLaw p U
          (glue U (fun x => Classical.choice (inferInstance : Nonempty (S x))) ξ))
          (fun η => f (glue U η ξ))) = blockDirichlet p U f := by
  classical
  let η₀ : (x : U) → S x := fun x => Classical.choice (inferInstance : Nonempty (S x))
  calc
    _ = ∑ ξ, ∑ η, p (glue U η ξ) * Complex.normSq
        (f (glue U η ξ) - conditionalExpectation p U f (glue U η ξ)) := by
      apply Fintype.sum_congr
      intro ξ
      exact weighted_blockVariance_slice S p hp U f ξ
    _ = ∑ η, ∑ ξ, p (glue U η ξ) * Complex.normSq
        (f (glue U η ξ) - conditionalExpectation p U f (glue U η ξ)) := by
      rw [Finset.sum_comm]
    _ = blockDirichlet p U f := by
      unfold blockDirichlet
      symm
      exact sum_config_glue (S := S) (U := U)
        (F := fun σ => p σ * Complex.normSq (f σ - conditionalExpectation p U f σ))

private lemma integrated_siteDirichlet_slice {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p) (U : Finset ι)
    (f : Config S → ℂ) (x : ι) (hx : x ∈ U) :
    (∑ ξ, (∑ η, p (glue U η ξ)) *
        blockDirichlet (blockLaw p U
          (glue U (fun y => Classical.choice (inferInstance : Nonempty (S y))) ξ))
          {⟨x, hx⟩} (fun η => f (glue U η ξ))) = blockDirichlet p {x} f := by
  classical
  let η₀ : (y : U) → S y := fun y => Classical.choice (inferInstance : Nonempty (S y))
  calc
    _ = ∑ ξ, ∑ η, p (glue U η ξ) * Complex.normSq
        (f (glue U η ξ) - conditionalExpectation p {x} f (glue U η ξ)) := by
      apply Fintype.sum_congr
      intro ξ
      exact weighted_siteDirichlet_slice S p hp U f ξ ⟨x, hx⟩
    _ = ∑ η, ∑ ξ, p (glue U η ξ) * Complex.normSq
        (f (glue U η ξ) - conditionalExpectation p {x} f (glue U η ξ)) := by
      rw [Finset.sum_comm]
    _ = blockDirichlet p {x} f := by
      unfold blockDirichlet
      symm
      exact sum_config_glue (S := S) (U := U)
        (F := fun σ => p σ * Complex.normSq (f σ - conditionalExpectation p {x} f σ))

private theorem conditional_block_gap_integrated {ι : Type} [Fintype ι] [DecidableEq ι]
    (S : ι → Type) [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p) (U : Finset ι)
    (g : ℝ)
    (hgap : ∀ σ, PoincareLower (blockLaw p U σ) g) (f : Config S → ℂ) :
    g * blockDirichlet p U f ≤ ∑ x : U, blockDirichlet p {x.1} f := by
  classical
  let η₀ : (x : U) → S x := fun x => Classical.choice (inferInstance : Nonempty (S x))
  have hpoint (ξ : (x : {x // x ∉ U}) → S x) :
      (∑ η, p (glue U η ξ)) *
          (g * variance (blockLaw p U (glue U η₀ ξ)) (fun η => f (glue U η ξ))) ≤
        (∑ η, p (glue U η ξ)) *
          dirichlet (blockLaw p U (glue U η₀ ξ)) (fun η => f (glue U η ξ)) := by
    have hgapξ := hgap (glue U η₀ ξ)
    have hlocal := hgapξ (fun η => f (glue U η ξ))
    exact mul_le_mul_of_nonneg_left hlocal
      (le_of_lt (sliceMass_pos S p hp U η₀ ξ))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun ξ hξ => hpoint ξ)
  calc
    g * blockDirichlet p U f =
        g * (∑ ξ, (∑ η, p (glue U η ξ)) *
          variance (blockLaw p U (glue U η₀ ξ)) (fun η => f (glue U η ξ))) := by
      rw [← integrated_blockVariance_slice S p hp U f]
    _ = ∑ ξ, (∑ η, p (glue U η ξ)) *
          (g * variance (blockLaw p U (glue U η₀ ξ)) (fun η => f (glue U η ξ))) := by
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro ξ
      ring
    _ ≤ ∑ ξ, (∑ η, p (glue U η ξ)) *
          dirichlet (blockLaw p U (glue U η₀ ξ)) (fun η => f (glue U η ξ)) := hsum
    _ = ∑ x : U, blockDirichlet p {x.1} f := by
      calc
        _ = ∑ ξ, ∑ x : U,
              (∑ η, p (glue U η ξ)) *
                blockDirichlet (blockLaw p U (glue U η₀ ξ)) {x}
                  (fun η => f (glue U η ξ)) := by
          apply Fintype.sum_congr
          intro ξ
          simp only [dirichlet]
          rw [Finset.mul_sum]
        _ = ∑ x : U, ∑ ξ,
              (∑ η, p (glue U η ξ)) *
                blockDirichlet (blockLaw p U (glue U η₀ ξ)) {x}
                  (fun η => f (glue U η ξ)) := by
          rw [Finset.sum_comm]
        _ = ∑ x : U, blockDirichlet p {x.1} f := by
          apply Fintype.sum_congr
          intro x
          exact integrated_siteDirichlet_slice S p hp U f x.1 x.2

private lemma sum_labeled_block_sites {ι J : Type} [Fintype ι] [DecidableEq ι]
    [Fintype J] (B : J → Finset ι) (d : ι → ℝ) :
    (∑ a, ∑ x : B a, d x.1) =
      ∑ x, ((Finset.univ.filter fun a => x ∈ B a).card : ℝ) * d x := by
  classical
  calc
    (∑ a, ∑ x : B a, d x.1) = ∑ a, ∑ x ∈ B a, d x := by
      apply Fintype.sum_congr
      intro a
      symm
      exact Finset.sum_subtype (B a) (fun x => Iff.rfl) d
    _ = ∑ a, ∑ x, if x ∈ B a then d x else 0 := by
      apply Fintype.sum_congr
      intro a
      rw [← Finset.sum_filter (s := Finset.univ) (p := fun x => x ∈ B a) (f := d)]
      simp
    _ = ∑ x, ∑ a, if x ∈ B a then d x else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ x, ((Finset.univ.filter fun a => x ∈ B a).card : ℝ) * d x := by
      apply Fintype.sum_congr
      intro x
      rw [← Finset.sum_filter (s := Finset.univ) (p := fun a => x ∈ B a)
        (f := fun _ => d x)]
      simp [Finset.sum_const, nsmul_eq_mul]

theorem main : AKLT.Blueprint.Gap.ConditionalBlockComparisonStatement := by
  intro ι J hι hιDec hJ S hSfin hSnon p hp B g _hg hgap f
  have hblocks (a : J) :
      g * blockDirichlet p (B a) f ≤ ∑ x : B a, blockDirichlet p {x.1} f :=
    conditional_block_gap_integrated S p hp (B a) g (fun σ => hgap a σ) f
  calc
    g * blockForm p B f = ∑ a, g * blockDirichlet p (B a) f := by
      unfold blockForm
      rw [Finset.mul_sum]
    _ ≤ ∑ a, ∑ x : B a, blockDirichlet p {x.1} f :=
      Finset.sum_le_sum (fun a ha => hblocks a)
    _ = ∑ x, ((Finset.univ.filter fun a => x ∈ B a).card : ℝ) * blockDirichlet p {x} f :=
      sum_labeled_block_sites B (fun x => blockDirichlet p {x} f)

end AKLT.W.GAP018
