module
public import AKLT.Blueprint.Gap.NodesPeriodic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Challenge
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP031

open AKLT.Blueprint.Gap

private def fillBlock {ι : Type} [DecidableEq ι] {S : ι → Type} (U : Finset ι) (η : Config S)
    (b : (x : U) → S x.val) : Config S :=
  fun x => if hx : x ∈ U then b ⟨x, hx⟩ else η x

private lemma fillBlock_outside {ι : Type} [DecidableEq ι] {S : ι → Type} (U : Finset ι) (η : Config S)
    (b : (x : U) → S x.val) : AgreeOutside U η (fillBlock U η b) := by
  intro x hx
  simp [fillBlock, hx]

private lemma fillBlock_restrict {ι : Type} [DecidableEq ι] {S : ι → Type} (U : Finset ι) (η : Config S)
    (b : (x : U) → S x.val) : restrict U (fillBlock U η b) = b := by
  funext x
  simp [restrict, fillBlock]

private lemma fillBlock_unique {ι : Type} [DecidableEq ι] {S : ι → Type} (U : Finset ι) (η τ : Config S)
    (hτ : AgreeOutside U η τ) (b : (x : U) → S x.val)
    (hb : restrict U τ = b) : τ = fillBlock U η b := by
  funext x
  by_cases hx : x ∈ U
  · have hx' : (⟨x, hx⟩ : U) = ⟨x, hx⟩ := rfl
    have := congrFun hb ⟨x, hx⟩
    simpa [restrict, fillBlock, hx] using this
  · simp [fillBlock, hx, hτ x hx]

private lemma fiber_zero_of_not_agree {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)]
    (p : Weight (Config S)) (U : Finset ι) (η τ : Config S)
    (h : ¬ AgreeOutside U η τ) : fiber p U η τ = 0 := by
  simp [fiber, conditionOn, AKLT.Defs.normalize, h]

private lemma fiber_probability {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (p : Weight (Config S)) (hp : PositiveProbability p)
    (U : Finset ι) (η : Config S) : Probability (fiber p U η) := by
  classical
  let w : Config S → ℝ := fun τ => if AgreeOutside U η τ then p τ else 0
  have hw_nonneg : ∀ τ, 0 ≤ w τ := by
    intro τ
    simp only [w]
    split_ifs
    · exact le_of_lt (hp.1 τ)
    · exact le_rfl
  have hw_pos : 0 < ∑ τ, w τ := by
    apply Finset.sum_pos' (fun τ hτ => hw_nonneg τ)
    refine ⟨η, Finset.mem_univ _, ?_⟩
    simp [w, AgreeOutside, hp.1]
  refine ⟨?_, ?_⟩
  · intro τ
    simp only [fiber, conditionOn, AKLT.Defs.normalize]
    exact div_nonneg (hw_nonneg τ) hw_pos.le
  · simp only [fiber, conditionOn, AKLT.Defs.normalize]
    rw [← Finset.sum_div]
    exact div_self hw_pos.ne'

private lemma marginal_probability {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (p : Weight Ω) (hp : Probability p) (r : Ω → Ξ) : Probability (marginal p r) := by
  classical
  refine ⟨?_, ?_⟩
  · intro z
    apply Finset.sum_nonneg
    intro x hx
    split_ifs
    · exact hp.1 x
    · exact le_rfl
  · simpa [marginal, Finset.sum_comm] using hp.2

private lemma blockLaw_probability {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (p : Weight (Config S)) (hp : PositiveProbability p)
    (U : Finset ι) (η : Config S) : Probability (blockLaw p U η) := by
  exact marginal_probability (fiber p U η) (fiber_probability p hp U η) (restrict U)

private lemma blockLaw_fill {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (p : Weight (Config S)) (U : Finset ι) (η : Config S)
    (b : (x : U) → S x.val) : blockLaw p U η b = fiber p U η (fillBlock U η b) := by
  classical
  unfold blockLaw marginal
  rw [Finset.sum_eq_single (fillBlock U η b)]
  · simp [fillBlock_restrict]
  · intro τ hmem hneq
    by_cases hr : restrict U τ = b
    · by_cases he : AgreeOutside U η τ
      · have hu := fillBlock_unique U η τ he b hr
        exact False.elim (hneq hu)
      · simp only [ite_eq_left hr]
        exact fiber_zero_of_not_agree p U η τ he
    · simp [hr]
  · intro hmem
    exact (hmem (Finset.mem_univ _)).elim

private def blockOutsideEquiv {ι : Type} [DecidableEq ι] {S : ι → Type} (U : Finset ι)
    (η : Config S) : {τ : Config S // AgreeOutside U η τ} ≃ ((x : U) → S x.val) where
  toFun τ := restrict U τ.1
  invFun b := ⟨fillBlock U η b, fillBlock_outside U η b⟩
  left_inv τ := by
    apply Subtype.ext
    exact (fillBlock_unique U η τ.1 τ.2 (restrict U τ.1) rfl).symm
  right_inv b := fillBlock_restrict U η b

private lemma sum_agree_restrict {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (U : Finset ι) (η : Config S)
    (f : ((x : U) → S x.val) → ℝ) :
    (∑ τ, if AgreeOutside U η τ then f (restrict U τ) else 0) = ∑ b, f b := by
  classical
  rw [← Finset.sum_filter]
  rw [← Finset.sum_subtype_eq_sum_filter]
  rw [Finset.subtype_univ]
  exact Fintype.sum_equiv (blockOutsideEquiv U η)
    (fun τ => f (restrict U τ.1)) f (by intro τ; rfl)

private lemma sum_agree_fill {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (U : Finset ι) (η : Config S) (f : Config S → ℝ) :
    (∑ τ, if AgreeOutside U η τ then f τ else 0) = ∑ b, f (fillBlock U η b) := by
  classical
  rw [← Finset.sum_filter]
  rw [← Finset.sum_subtype_eq_sum_filter]
  rw [Finset.subtype_univ]
  exact Fintype.sum_equiv (blockOutsideEquiv U η)
    (fun τ => f τ.1) (fun b => f (fillBlock U η b)) (by
      intro τ
      congr 1
      exact fillBlock_unique U η τ.1 τ.2 (restrict U τ.1) rfl)

private def liftBlockMass {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (p q : Weight (Config S)) (U : Finset ι) (η ξ : Config S)
    (c : Coupling (blockLaw p U η) (blockLaw q U ξ)) :
    Config S → Config S → ℝ := fun σ τ =>
      if AgreeOutside U η σ then
        if AgreeOutside U ξ τ then c.mass (restrict U σ) (restrict U τ) else 0
      else 0

private def liftBlockCoupling {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p q : Weight (Config S)) (U : Finset ι) (η ξ : Config S)
    (c : Coupling (blockLaw p U η) (blockLaw q U ξ)) :
    Coupling (fiber p U η) (fiber q U ξ) := by
  classical
  let mass := liftBlockMass p q U η ξ c
  refine ⟨mass, ?_, ?_, ?_⟩
  · intro σ τ
    change 0 ≤ liftBlockMass p q U η ξ c σ τ
    by_cases hσ : AgreeOutside U η σ
    · by_cases hτ : AgreeOutside U ξ τ <;> simp [liftBlockMass, hσ, hτ, c.nonnegative]
    · simp [liftBlockMass, hσ]
  · intro σ
    by_cases hσ : AgreeOutside U η σ
    · have hfill : fillBlock U η (restrict U σ) = σ :=
        (fillBlock_unique U η σ hσ (restrict U σ) rfl).symm
      change (∑ τ, liftBlockMass p q U η ξ c σ τ) = fiber p U η σ
      simp only [liftBlockMass, ite_eq_left hσ]
      rw [sum_agree_restrict U ξ (fun b => c.mass (restrict U σ) b)]
      rw [c.first_marginal, blockLaw_fill, hfill]
    · change (∑ τ, liftBlockMass p q U η ξ c σ τ) = fiber p U η σ
      simp [liftBlockMass, hσ, fiber_zero_of_not_agree p U η σ hσ]
  · intro τ
    by_cases hτ : AgreeOutside U ξ τ
    · have hfill : fillBlock U ξ (restrict U τ) = τ :=
        (fillBlock_unique U ξ τ hτ (restrict U τ) rfl).symm
      change (∑ σ, liftBlockMass p q U η ξ c σ τ) = fiber q U ξ τ
      simp only [liftBlockMass, ite_eq_left hτ]
      rw [sum_agree_restrict U η (fun b => c.mass b (restrict U τ))]
      rw [c.second_marginal, blockLaw_fill, hfill]
    · change (∑ σ, liftBlockMass p q U η ξ c σ τ) = fiber q U ξ τ
      simp [liftBlockMass, hτ, fiber_zero_of_not_agree q U ξ τ hτ]

private lemma liftBlockCoupling_cost {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p q : Weight (Config S)) (U : Finset ι) (η ξ : Config S)
    (c : Coupling (blockLaw p U η) (blockLaw q U ξ)) :
    couplingCost (liftBlockCoupling p q U η ξ c) =
      ∑ b, ∑ b', c.mass b b' * (hamming (fillBlock U η b) (fillBlock U ξ b') : ℝ) := by
  classical
  change (∑ σ, ∑ τ, liftBlockMass p q U η ξ c σ τ * (hamming σ τ : ℝ)) = _
  have hInner (σ : Config S) :
      (∑ τ, if AgreeOutside U ξ τ then
        c.mass (restrict U σ) (restrict U τ) * (hamming σ τ : ℝ) else 0) =
      ∑ b', c.mass (restrict U σ) b' * (hamming σ (fillBlock U ξ b') : ℝ) := by
    rw [sum_agree_fill U ξ (fun τ =>
      c.mass (restrict U σ) (restrict U τ) * (hamming σ τ : ℝ))]
    simp [fillBlock_restrict]
  have hOuter (b' : (x : U) → S x.val) :
      (∑ σ, if AgreeOutside U η σ then
        c.mass (restrict U σ) b' * (hamming σ (fillBlock U ξ b') : ℝ) else 0) =
      ∑ b, c.mass b b' * (hamming (fillBlock U η b) (fillBlock U ξ b') : ℝ) := by
    rw [sum_agree_fill U η (fun σ =>
      c.mass (restrict U σ) b' * (hamming σ (fillBlock U ξ b') : ℝ))]
    simp [fillBlock_restrict]
  have hbase :
      (∑ σ, ∑ τ, liftBlockMass p q U η ξ c σ τ * (hamming σ τ : ℝ)) =
      ∑ σ, if AgreeOutside U η σ then
        ∑ τ, if AgreeOutside U ξ τ then
          c.mass (restrict U σ) (restrict U τ) * (hamming σ τ : ℝ) else 0 else 0 := by
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hσ : AgreeOutside U η σ
    · simp only [liftBlockMass, ite_eq_left hσ]
      apply Finset.sum_congr rfl
      intro τ _
      by_cases hτ : AgreeOutside U ξ τ <;> simp [hτ]
    · simp [liftBlockMass, hσ]
  calc
    _ = ∑ σ, if AgreeOutside U η σ then
          ∑ τ, if AgreeOutside U ξ τ then
            c.mass (restrict U σ) (restrict U τ) * (hamming σ τ : ℝ) else 0 else 0 := hbase
    _ = ∑ σ, if AgreeOutside U η σ then
          ∑ b', c.mass (restrict U σ) b' * (hamming σ (fillBlock U ξ b') : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hσ : AgreeOutside U η σ <;> simp [hσ, hInner]
    _ = ∑ σ, ∑ b', if AgreeOutside U η σ then
          c.mass (restrict U σ) b' * (hamming σ (fillBlock U ξ b') : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro σ _
      by_cases hσ : AgreeOutside U η σ <;> simp [hσ]
    _ = ∑ b', ∑ σ, if AgreeOutside U η σ then
          c.mass (restrict U σ) b' * (hamming σ (fillBlock U ξ b') : ℝ) else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ b', ∑ b, c.mass b b' *
          (hamming (fillBlock U η b) (fillBlock U ξ b') : ℝ) := by
      apply Finset.sum_congr rfl
      intro b' _
      exact hOuter b'
    _ = ∑ b, ∑ b', c.mass b b' *
          (hamming (fillBlock U η b) (fillBlock U ξ b') : ℝ) := by
      rw [Finset.sum_comm]

private lemma hamming_fill_le_one_add {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (U : Finset ι) (η ξ : Config S)
    (x : ι) (hout : AgreeOutside {x} η ξ)
    (b b' : (y : U) → S y.val) :
    hamming (fillBlock U η b) (fillBlock U ξ b') ≤ 1 + hamming b b' := by
  classical
  let D : Finset ι := Finset.univ.filter fun y =>
    fillBlock U η b y ≠ fillBlock U ξ b' y
  let B : Finset U := Finset.univ.filter fun y => b y ≠ b' y
  let I : Finset ι := B.image fun y : U => y.val
  have hsubset : D ⊆ insert x I := by
    intro y hy
    have hyneq : fillBlock U η b y ≠ fillBlock U ξ b' y :=
      (Finset.mem_filter.mp hy).2
    by_cases hxy : y = x
    · subst y
      exact Finset.mem_insert_self x I
    · by_cases hyU : y ∈ U
      · have hbneq : b ⟨y, hyU⟩ ≠ b' ⟨y, hyU⟩ := by
          simpa [fillBlock, hyU] using hyneq
        apply Finset.mem_insert_of_mem
        apply Finset.mem_image.mpr
        exact ⟨⟨y, hyU⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbneq⟩, rfl⟩
      · have hsame := hout y (by simp [hxy])
        have hEq : fillBlock U η b y = fillBlock U ξ b' y := by
          simp [fillBlock, hyU, hsame]
        exact (hyneq hEq).elim
  have hImage : I.card = B.card := by
    simp only [I, B]
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hcard : D.card ≤ I.card + 1 :=
    (Finset.card_le_card hsubset).trans (Finset.card_insert_le x I)
  simpa [hamming, D, B, Nat.add_comm, hImage] using hcard

private lemma liftBlockCoupling_cost_le {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p) (U : Finset ι)
    (η ξ : Config S) (x : ι) (hout : AgreeOutside {x} η ξ)
    (c : Coupling (blockLaw p U η) (blockLaw p U ξ)) :
    couplingCost (liftBlockCoupling p p U η ξ c) ≤ 1 + couplingCost c := by
  classical
  rw [liftBlockCoupling_cost]
  have htotal : ∑ b, ∑ b', c.mass b b' = 1 := by
    calc
      ∑ b, ∑ b', c.mass b b' = ∑ b, blockLaw p U η b := by
        apply Finset.sum_congr rfl
        intro b _
        exact c.first_marginal b
      _ = 1 := (blockLaw_probability p hp U η).2
  have hterm (b b' : (y : U) → S y.val) :
      c.mass b b' * (hamming (fillBlock U η b) (fillBlock U ξ b') : ℝ) ≤
        c.mass b b' * (1 + (hamming b b' : ℝ)) := by
    apply mul_le_mul_of_nonneg_left _ (c.nonnegative b b')
    have hh := hamming_fill_le_one_add U η ξ x hout b b'
    exact_mod_cast hh
  calc
    _ ≤ ∑ b, ∑ b', c.mass b b' * (1 + (hamming b b' : ℝ)) := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro b' _
      exact hterm b b'
    _ = (∑ b, ∑ b', c.mass b b') + couplingCost c := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      simp [couplingCost]
    _ = 1 + couplingCost c := by rw [htotal]

private def diagonalCoupling {Ω : Type} [Fintype Ω] (p : Weight Ω)
    (hp : ∀ x, 0 ≤ p x) : Coupling p p := by
  classical
  refine ⟨fun x y => if x = y then p x else 0, ?_, ?_, ?_⟩
  · intro x y
    split_ifs <;> simp [hp]
  · intro x
    simp
  · intro y
    simp

private def diagonalCouplingOfEq {Ω : Type} [Fintype Ω] (p q : Weight Ω) (h : p = q)
    (hp : ∀ x, 0 ≤ p x) : Coupling p q := by
  classical
  refine ⟨fun x y => if x = y then p x else 0, ?_, ?_, ?_⟩
  · intro x y
    split_ifs <;> simp [hp]
  · intro x
    simp
  · intro y
    rw [← h]
    simp

private lemma diagonalCoupling_cost {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] (p : Weight (Config S))
    (hp : ∀ x, 0 ≤ p x) : couplingCost (diagonalCoupling p hp) = 0 := by
  classical
  simp [couplingCost, diagonalCoupling, hamming]

private lemma diagonalCouplingOfEq_cost {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] {p q : Weight (Config S)}
    (h : p = q) (hp : ∀ x, 0 ≤ p x) :
    couplingCost (diagonalCouplingOfEq p q h hp) = 0 := by
  classical
  simp [couplingCost, diagonalCouplingOfEq, hamming]

private lemma fiber_eq_of_agree {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    [∀ x, Fintype (S x)] (p : Weight (Config S)) (U : Finset ι) (η ξ : Config S)
    (h : AgreeOutside U η ξ) : fiber p U η = fiber p U ξ := by
  classical
  have hPred : AgreeOutside U η = AgreeOutside U ξ := by
    funext τ
    apply propext
    constructor
    · intro hτ z hz
      calc
        ξ z = η z := (h z hz).symm
        _ = τ z := hτ z hz
    · intro hτ z hz
      calc
        η z = ξ z := h z hz
        _ = τ z := hτ z hz
  unfold fiber
  rw [hPred]

private lemma hamming_one_site {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type}
    (σ τ : Config S) (h : hamming σ τ = 1) :
    ∃ x, AgreeOutside {x} σ τ ∧ σ x ≠ τ x := by
  classical
  let D : Finset ι := Finset.univ.filter fun x => σ x ≠ τ x
  have hD : D.card = 1 := by simpa [D, hamming] using h
  obtain ⟨x, hDx⟩ := Finset.card_eq_one.mp hD
  refine ⟨x, ?_, ?_⟩
  · intro y hy
    by_contra hne
    have hmem : y ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    rw [hDx] at hmem
    exact hy (by simpa using hmem)
  · have hmem : x ∈ D := by rw [hDx]; simp
    exact (Finset.mem_filter.mp hmem).2

private lemma blockLaw_eq_of_fiber_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)]
    (p : Weight (Config S)) (U : Finset ι) (η ξ : Config S)
    (h : fiber p U η = fiber p U ξ) : blockLaw p U η = blockLaw p U ξ := by
  simp [blockLaw, h]

private def averageCoupling {Ω J : Type} [Fintype Ω] [Fintype J]
    (p q : J → Weight Ω) (c : ∀ a, Coupling (p a) (q a))
    (hJ : 0 < Fintype.card J) :
    Coupling (fun x => (∑ a, p a x) / (Fintype.card J : ℝ))
      (fun y => (∑ a, q a y) / (Fintype.card J : ℝ)) := by
  classical
  let A : ℝ := (Fintype.card J : ℝ)
  have hApos : 0 < A := by dsimp [A]; exact_mod_cast hJ
  refine ⟨fun x y => (∑ a, (c a).mass x y) / A, ?_, ?_, ?_⟩
  · intro x y
    apply div_nonneg
    · exact Finset.sum_nonneg fun a ha => (c a).nonnegative x y
    · exact hApos.le
  · intro x
    calc
      (∑ y, (∑ a, (c a).mass x y) / A) =
          (∑ y, ∑ a, (c a).mass x y) / A := by rw [← Finset.sum_div]
      _ = (∑ a, ∑ y, (c a).mass x y) / A := by rw [Finset.sum_comm]
      _ = (∑ a, p a x) / A := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        exact (c a).first_marginal x
  · intro y
    calc
      (∑ x, (∑ a, (c a).mass x y) / A) =
          (∑ x, ∑ a, (c a).mass x y) / A := by rw [← Finset.sum_div]
      _ = (∑ a, ∑ x, (c a).mass x y) / A := by rw [Finset.sum_comm]
      _ = (∑ a, q a y) / A := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        exact (c a).second_marginal y

private lemma averageCoupling_cost {Ω J : Type} [Fintype Ω] [DecidableEq Ω] [Fintype J]
    {S : Ω → Type} [∀ x, Fintype (S x)] (p q : J → Weight (Config S))
    (c : ∀ a, Coupling (p a) (q a)) (hJ : 0 < Fintype.card J) :
    couplingCost (averageCoupling p q c hJ) =
      (∑ a, couplingCost (c a)) / (Fintype.card J : ℝ) := by
  classical
  let A : ℝ := (Fintype.card J : ℝ)
  change (∑ σ, ∑ τ,
    ((∑ a, (c a).mass σ τ) / A) * (hamming σ τ : ℝ)) = _
  have hmul (σ τ : Config S) :
      ((∑ a, (c a).mass σ τ) / A) * (hamming σ τ : ℝ) =
      (∑ a, (c a).mass σ τ * (hamming σ τ : ℝ)) / A := by
    rw [div_mul_eq_mul_div, Finset.sum_mul]
  calc
    _ = ∑ σ, ∑ τ,
        (∑ a, (c a).mass σ τ * (hamming σ τ : ℝ)) / A := by
      apply Finset.sum_congr rfl
      intro σ _
      apply Finset.sum_congr rfl
      intro τ _
      exact hmul σ τ
    _ = (∑ σ, ∑ τ, ∑ a,
        (c a).mass σ τ * (hamming σ τ : ℝ)) / A := by
      symm
      simp_rw [Finset.sum_div]
    _ = (∑ a, ∑ σ, ∑ τ,
        (c a).mass σ τ * (hamming σ τ : ℝ)) / A := by
      congr 1
      calc
        (∑ σ, ∑ τ, ∑ a, (c a).mass σ τ * (hamming σ τ : ℝ)) =
            ∑ σ, ∑ a, ∑ τ, (c a).mass σ τ * (hamming σ τ : ℝ) := by
          apply Finset.sum_congr rfl
          intro σ _
          rw [Finset.sum_comm]
        _ = ∑ a, ∑ σ, ∑ τ, (c a).mass σ τ * (hamming σ τ : ℝ) := by
          rw [Finset.sum_comm]
    _ = (∑ a, couplingCost (c a)) / A := by simp [couplingCost]

private lemma sum_indicator_const {J : Type} [Fintype J] [DecidableEq J]
    (E : Finset J) (r : ℝ) :
    (∑ a, if a ∈ E then r else 0) = (E.card : ℝ) * r := by
  classical
  calc
    (∑ a, if a ∈ E then r else 0) = ∑ a ∈ E, r := by
      rw [← Finset.sum_filter]
      simp
    _ = (E.card : ℝ) * r := by simp

private lemma sum_indicator_not_one {J : Type} [Fintype J] [DecidableEq J]
    (E : Finset J) :
    (∑ a, if a ∈ E then (0 : ℝ) else 1) =
      ((Fintype.card J - E.card : ℕ) : ℝ) := by
  classical
  have hform (a : J) : (if a ∈ E then (0 : ℝ) else 1) =
      (if a ∉ E then (1 : ℝ) else 0) := by by_cases ha : a ∈ E <;> simp [ha]
  simp_rw [hform]
  calc
    (∑ a, if a ∉ E then (1 : ℝ) else 0) =
        ∑ a ∈ Finset.univ.filter (fun a => a ∉ E), (1 : ℝ) := by
      rw [← Finset.sum_filter]
    _ = ((Finset.univ.filter (fun a => a ∉ E)).card : ℝ) := by simp
    _ = ((Fintype.card J - E.card : ℕ) : ℝ) := by
      congr 1
      rw [show Finset.univ.filter (fun a : J => a ∉ E) = Finset.univ \ E by
        ext a
        simp]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ E)]
      simp

private lemma periodic_label_cap_sum {L N : Size} (M : ℕ) (K : ℝ)
    (hCounts : PeriodicCounts L N M) (x : Site L N) :
    (∑ a : Site L N,
      if x ∈ torusSquare L N M a then (0 : ℝ)
      else if x ∈ torusHalo L N M a \ torusSquare L N M a then 1 + K else 1) =
      (Fintype.card (Site L N) : ℝ) - (volumeCount M : ℝ) +
        (haloCount M : ℝ) * K := by
  classical
  let C : Finset (Site L N) := Finset.univ.filter fun a => x ∈ torusSquare L N M a
  let E : Finset (Site L N) := Finset.univ.filter fun a =>
    x ∈ torusHalo L N M a \ torusSquare L N M a
  have hC : C.card = volumeCount M := hCounts.1 x
  have hE : E.card = haloCount M := hCounts.2.1 x
  have hpoint (a : Site L N) :
      (if x ∈ torusSquare L N M a then (0 : ℝ)
        else if x ∈ torusHalo L N M a \ torusSquare L N M a then 1 + K else 1) =
      (if a ∈ C then (0 : ℝ) else 1) + (if a ∈ E then K else 0) := by
    by_cases hc : x ∈ torusSquare L N M a
    · simp [C, E, hc]
    · by_cases he : x ∈ torusHalo L N M a \ torusSquare L N M a
      · have hhalo : x ∈ torusHalo L N M a := (Finset.mem_sdiff.mp he).1
        simp [C, E, hc, he, hhalo]
      · have hnotHalo : x ∉ torusHalo L N M a := by
          intro hh
          exact he (Finset.mem_sdiff.mpr ⟨hh, hc⟩)
        simp [C, E, hc, he, hnotHalo]
  have hfirst : (∑ a : Site L N, if a ∈ C then (0 : ℝ) else 1) =
      (Fintype.card (Site L N) : ℝ) - (volumeCount M : ℝ) := by
    rw [sum_indicator_not_one C, hC]
    rw [Nat.cast_sub hCounts.2.2]
  calc
    _ = ∑ a : Site L N,
          ((if a ∈ C then (0 : ℝ) else 1) + (if a ∈ E then K else 0)) := by
      apply Finset.sum_congr rfl
      intro a _
      exact hpoint a
    _ = (∑ a : Site L N, if a ∈ C then (0 : ℝ) else 1) +
          (∑ a : Site L N, if a ∈ E then K else 0) := Finset.sum_add_distrib
    _ = (Fintype.card (Site L N) : ℝ) - (volumeCount M : ℝ) +
          (haloCount M : ℝ) * K := by
      rw [hfirst, sum_indicator_const E K, hE]

private lemma labelCoupling {L N : Size} {S : Site L N → Type}
    [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (μ : Weight (Config S)) (hμ : PositiveProbability μ) (M : ℕ) (K : ℝ)
    (hRange : TorusRangeOne μ M) (hInfluence : BlockInfluence μ M K)
    {σ τ : Config S} (x : Site L N) (hDiff : AgreeOutside {x} σ τ) :
    ∀ a : Site L N,
      ∃ c : Coupling (fiber μ (torusSquare L N M a) σ)
          (fiber μ (torusSquare L N M a) τ),
        couplingCost c ≤
          if x ∈ torusSquare L N M a then 0
          else if x ∈ torusHalo L N M a \ torusSquare L N M a then 1 + K else 1 := by
  classical
  intro a
  let U := torusSquare L N M a
  let V := torusHalo L N M a \ torusSquare L N M a
  by_cases hxU : x ∈ U
  · have hAgree : AgreeOutside U σ τ := by
      intro y hy
      apply hDiff
      simp only [Finset.mem_singleton]
      intro hxy
      exact hy (hxy ▸ hxU)
    have hfib := fiber_eq_of_agree μ U σ τ hAgree
    have hnonneg : ∀ z, 0 ≤ fiber μ U σ z :=
      (fiber_probability μ hμ U σ).1
    let c := diagonalCouplingOfEq (fiber μ U σ) (fiber μ U τ) hfib hnonneg
    refine ⟨c, ?_⟩
    simpa [c, U, hxU] using (diagonalCouplingOfEq_cost hfib hnonneg).le
  · by_cases hxV : x ∈ V
    · obtain ⟨d, hd⟩ := hInfluence a x hxV σ τ hDiff
      let c := liftBlockCoupling μ μ U σ τ d
      refine ⟨c, ?_⟩
      have hcost := liftBlockCoupling_cost_le μ hμ U σ τ x hDiff d
      have hcBound : couplingCost c ≤ 1 + K := calc
        couplingCost c ≤ 1 + couplingCost d := by simpa [c, U] using hcost
        _ ≤ 1 + K := by linarith
      simpa [U, V, hxU, hxV] using hcBound
    · have hAgree : AgreeOn V σ τ := by
        intro y hy
        apply hDiff
        simp only [Finset.mem_singleton]
        intro hxy
        subst y
        exact hxV hy
      have hLaw := hRange a σ τ hAgree
      have hblockProb := blockLaw_probability μ hμ U σ
      have hblockNonneg : ∀ b, 0 ≤ blockLaw μ U σ b := hblockProb.1
      let d := diagonalCouplingOfEq (blockLaw μ U σ) (blockLaw μ U τ) hLaw hblockNonneg
      let c := liftBlockCoupling μ μ U σ τ d
      refine ⟨c, ?_⟩
      have hcost := liftBlockCoupling_cost_le μ hμ U σ τ x hDiff d
      have hdiag' : couplingCost d = 0 := by
        simpa [d] using diagonalCouplingOfEq_cost hLaw hblockNonneg
      simpa [c, U, V, hxU, hxV, hdiag'] using hcost

theorem main : AKLT.Blueprint.Gap.PeriodicNeighborCouplingStatement := by
  classical
  intro L N S hS hSnonempty μ hμ M K hM hK hCounts hRange hInfluence σ τ hH
  obtain ⟨x, hDiff, hxDiff⟩ := hamming_one_site σ τ hH
  have hPerLabel := labelCoupling μ hμ M K hRange hInfluence x hDiff
  let cLabel : ∀ a : Site L N,
      Coupling (fiber μ (torusSquare L N M a) σ)
        (fiber μ (torusSquare L N M a) τ) := fun a => Classical.choose (hPerLabel a)
  have hLabelCost (a : Site L N) :
      couplingCost (cLabel a) ≤
        if x ∈ torusSquare L N M a then 0
        else if x ∈ torusHalo L N M a \ torusSquare L N M a then 1 + K else 1 :=
    Classical.choose_spec (hPerLabel a)
  have hCardPos : 0 < Fintype.card (Site L N) := by
    have hVol : 0 < volumeCount M := by unfold volumeCount; positivity
    exact lt_of_lt_of_le hVol hCounts.2.2
  have hCardPosR : 0 < (Fintype.card (Site L N) : ℝ) := by exact_mod_cast hCardPos
  let c : Coupling (blockAverage μ (torusSquare L N M) σ)
      (blockAverage μ (torusSquare L N M) τ) :=
    averageCoupling
      (fun a => fiber μ (torusSquare L N M a) σ)
      (fun a => fiber μ (torusSquare L N M a) τ) cLabel hCardPos
  have hCostEq : couplingCost c =
      (∑ a, couplingCost (cLabel a)) / (Fintype.card (Site L N) : ℝ) := by
    change couplingCost (averageCoupling
      (fun a => fiber μ (torusSquare L N M a) σ)
      (fun a => fiber μ (torusSquare L N M a) τ) cLabel hCardPos) = _
    exact averageCoupling_cost
      (fun a => fiber μ (torusSquare L N M a) σ)
      (fun a => fiber μ (torusSquare L N M a) τ) cLabel hCardPos
  have hSum : (∑ a : Site L N, couplingCost (cLabel a)) ≤
      (Fintype.card (Site L N) : ℝ) - (volumeCount M : ℝ) +
        (haloCount M : ℝ) * K := by
    calc
      (∑ a : Site L N, couplingCost (cLabel a)) ≤
          ∑ a : Site L N,
            (if x ∈ torusSquare L N M a then (0 : ℝ)
              else if x ∈ torusHalo L N M a \ torusSquare L N M a then 1 + K else 1) := by
        apply Finset.sum_le_sum
        intro a _
        exact hLabelCost a
      _ = (Fintype.card (Site L N) : ℝ) - (volumeCount M : ℝ) +
          (haloCount M : ℝ) * K := periodic_label_cap_sum M K hCounts x
  refine ⟨c, ?_⟩
  calc
    couplingCost c =
        (∑ a, couplingCost (cLabel a)) / (Fintype.card (Site L N) : ℝ) := hCostEq
    _ ≤ ((Fintype.card (Site L N) : ℝ) - (volumeCount M : ℝ) +
        (haloCount M : ℝ) * K) / (Fintype.card (Site L N) : ℝ) :=
      div_le_div_of_nonneg_right hSum hCardPosR.le
    _ = 1 - ((volumeCount M : ℝ) - (haloCount M : ℝ) * K) /
        (Fintype.card (Site L N) : ℝ) := by
      field_simp [hCardPosR.ne']
      ring

end AKLT.W.GAP031
