module
public import AKLT.Blueprint.Win.NodesRemoval

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN049

private lemma normSq_nonneg (a : Vec3) : 0 ≤ normSq a := by
  unfold normSq dot
  apply Finset.sum_nonneg
  intro i hi
  nlinarith [sq_nonneg (a i)]

private lemma normSq_add (a b : Vec3) :
    normSq (fun i => a i + b i) = normSq a + 2 * dot a b + normSq b := by
  unfold normSq dot
  calc
    (∑ i, (a i + b i) * (a i + b i)) =
        ∑ i, (a i * a i + 2 * (a i * b i) + b i * b i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, a i * a i) + 2 * (∑ i, a i * b i) + (∑ i, b i * b i) := by
      simp [Finset.sum_add_distrib, Finset.mul_sum, add_assoc]

private lemma dot_lower_bound (a b : Vec3) (ha : normSq a = 1) (hb : normSq b = 1) :
    -1 ≤ dot a b := by
  have h := normSq_nonneg (fun i => a i + b i)
  rw [normSq_add, ha, hb] at h
  nlinarith

private lemma partWeight_factor_nonneg
    (hMom : AKLT.Blueprint.Top.MomentsStatement)
    (G Y : Finset Plane) (τ : PinAssignment G) (pinned : Bool)
    (σ : PlaneConfiguration (G \ Y)) :
    0 ≤ AKLT.Blueprint.Win.partWeight pinned G Y τ σ := by
  rcases hMom with ⟨_, hIcoUnit, _⟩
  have hspin : ∀ z ∈ G \ Y, normSq (extendIcoSpins σ z) = 1 := by
    intro z hz
    simp [extendIcoSpins, hz, hIcoUnit]
  unfold AKLT.Blueprint.Win.partWeight
  apply mul_nonneg
  · apply mul_nonneg
    · positivity
    · apply Finset.prod_nonneg
      intro e he
      have he1 : e.1 ∈ G \ Y := by
        have hp : e ∈ AKLT.Defs.internalBonds (G \ Y) := he
        rcases Finset.mem_biUnion.mp hp with ⟨x, hx, hx'⟩
        rcases Finset.mem_image.mp hx' with ⟨y, hy, hxy⟩
        have hfst : e.1 = x := (congrArg Prod.fst hxy).symm
        simpa [hfst] using hx
      have he2 : e.2 ∈ G \ Y := by
        have hp : e ∈ AKLT.Defs.internalBonds (G \ Y) := he
        rcases Finset.mem_biUnion.mp hp with ⟨x, hx, hx'⟩
        rcases Finset.mem_image.mp hx' with ⟨y, hy, hxy⟩
        have hsnd : e.2 = y := (congrArg Prod.snd hxy).symm
        have hmem : y ∈ G \ Y := (Finset.mem_inter.mp hy).2
        simpa [hsnd] using hmem
      have hdot := dot_lower_bound (extendIcoSpins σ e.1) (extendIcoSpins σ e.2)
        (hspin e.1 he1) (hspin e.2 he2)
      linarith
  · apply Finset.prod_nonneg
    intro e he
    by_cases h : pinned ∧ e.val.1 ∈ G \ Y
    · rw [if_pos h]
      have hp : normSq (τ e).val = 1 := (τ e).property
      have hs : normSq (extendIcoSpins σ e.val.1) = 1 := hspin e.val.1 h.2
      have hdot := dot_lower_bound (τ e).val (extendIcoSpins σ e.val.1) hp hs
      linarith
    · rw [if_neg h]
      norm_num

private lemma sum_partWeight_eq_partSum
    (pinned : Bool) (G Y : Finset Plane) (τ : PinAssignment G)
    (f : (Plane → Vec3) → ℝ) :
    (∑ σ : PlaneConfiguration (G \ Y),
      AKLT.Blueprint.Win.partWeight pinned G Y τ σ * f (extendIcoSpins σ)) =
        AKLT.Blueprint.Win.partSum pinned G Y τ f := by
  classical
  cases pinned with
  | false =>
      simp [AKLT.Blueprint.Win.partWeight, AKLT.Blueprint.Win.partSum,
        AKLT.Defs.freeSum]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring
  | true =>
      simp [AKLT.Blueprint.Win.partWeight, AKLT.Blueprint.Win.partSum,
        AKLT.Defs.pinnedSum]
      apply Finset.sum_congr rfl
      intro σ hσ
      ring

private lemma sum_partWeight_eq_normalizer
    (pinned : Bool) (G Y : Finset Plane) (τ : PinAssignment G) :
    (∑ σ : PlaneConfiguration (G \ Y),
      AKLT.Blueprint.Win.partWeight pinned G Y τ σ) =
        AKLT.Blueprint.Win.partSum pinned G Y τ (fun _ => 1) := by
  classical
  simpa only [mul_one] using
    (sum_partWeight_eq_partSum pinned G Y τ (fun _ => 1))

private lemma expectation_normalize
    {Ω : Type*} [Fintype Ω] (w f : Ω → ℝ)
    (hw : ∑ x, w x ≠ 0) :
    expectation (normalize w) f = (∑ x, w x * f x) / (∑ x, w x) := by
  classical
  unfold expectation AKLT.Defs.normalize
  calc
    (∑ x, (w x / (∑ y, w y)) * f x) =
        ∑ x, (w x * f x) / (∑ y, w y) := by
      apply Finset.sum_congr rfl
      intro x hx
      field_simp [hw]
    _ = (∑ x, w x * f x) / (∑ y, w y) := by rw [Finset.sum_div]

theorem main : AKLT.Blueprint.Win.PartLawBridgeStatement := by
  intro hMom G Y τ pinned hZ
  classical
  let w : PlaneConfiguration (G \ Y) → ℝ :=
    AKLT.Blueprint.Win.partWeight pinned G Y τ
  have hsum : (∑ σ, w σ) = AKLT.Blueprint.Win.partSum pinned G Y τ (fun _ => 1) := by
    exact sum_partWeight_eq_normalizer pinned G Y τ
  have hsum_pos : 0 < ∑ σ, w σ := by
    rw [hsum]
    exact hZ
  have hprob : Probability (AKLT.Blueprint.Win.partLaw pinned G Y τ) := by
    constructor
    · intro σ
      change 0 ≤ w σ / ∑ ρ, w ρ
      exact div_nonneg (partWeight_factor_nonneg hMom G Y τ pinned σ) (le_of_lt hsum_pos)
    · change (∑ σ, w σ / ∑ ρ, w ρ) = 1
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hsum_pos)
  constructor
  · exact hprob
  · intro f
    rw [AKLT.Blueprint.Win.partMean]
    rw [← sum_partWeight_eq_partSum pinned G Y τ f, ← hsum]
    unfold AKLT.Blueprint.Win.partLaw
    simpa [w] using
      (expectation_normalize (AKLT.Blueprint.Win.partWeight pinned G Y τ)
        (fun σ => f (extendIcoSpins σ))
        (by simpa [w] using ne_of_gt hsum_pos)).symm

end AKLT.W.WIN049
