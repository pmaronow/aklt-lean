module
public import AKLT.Blueprint.Gap.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP010

local instance (α : Type) : DecidableEq α := Classical.decEq α

private theorem overlap_eq_one_sub_tv {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (p q : Weight Ω) (hp : Probability p) (hq : Probability q) :
    (∑ x, min (p x) (q x)) = 1 - totalVariation p q := by
  unfold totalVariation
  have habs : ∀ x, |p x - q x| = p x + q x - 2 * min (p x) (q x) := by
    intro x
    rcases le_total (p x) (q x) with h | h
    · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
    · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
  rw [show (∑ x, |p x - q x|) = ∑ x, (p x + q x - 2 * min (p x) (q x)) by
    apply Finset.sum_congr rfl
    intro x hx
    exact habs x]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hp.2, hq.2,
    ← Finset.mul_sum]
  ring

private theorem sum_comm_fintype {α β γ : Type} [Fintype α] [Fintype β]
    [AddCommMonoid γ] (f : α → β → γ) :
    (∑ a, ∑ b, f a b) = ∑ b, ∑ a, f a b := by
  calc
    (∑ a, ∑ b, f a b) = ∑ z : α × β, f z.1 z.2 := by
      rw [Fintype.sum_prod_type]
    _ = ∑ z : β × α, f z.2 z.1 := by
      exact Fintype.sum_equiv (Equiv.prodComm α β) _ _ (fun _ => rfl)
    _ = ∑ b, ∑ a, f a b := by rw [Fintype.sum_prod_type]

private theorem marginal_pos {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p) (B : Finset ι)
    (b : (x : B) → S x) : 0 < marginal p (restrict B) b := by
  classical
  let base : Config S := fun x => Classical.choice (inferInstance : Nonempty (S x))
  let ext : Config S := fun x => if hx : x ∈ B then b ⟨x, hx⟩ else base x
  have hext : restrict B ext = b := by
    funext x
    simp [ext, restrict]
  unfold marginal
  rw [← Finset.sum_filter]
  apply Finset.sum_pos'
  · intro σ hσ
    exact (hp.1 σ).le
  · exact ⟨ext, by simpa [hext] using hp.1 ext⟩

private theorem marginal_probability {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    [DecidableEq Ξ] (p : Weight Ω) (r : Ω → Ξ) (hp : Probability p) :
    Probability (marginal p r) := by
  classical
  refine ⟨?_, ?_⟩
  · intro z
    unfold marginal
    apply Finset.sum_nonneg
    intro x hx
    by_cases h : r x = z
    · simp [h, hp.1 x]
    · simp [h]
  · unfold marginal
    calc
      (∑ z, ∑ x, if r x = z then p x else 0) =
          ∑ x, ∑ z, if r x = z then p x else 0 :=
        sum_comm_fintype (fun z x => if r x = z then p x else 0)
      _ = ∑ x, p x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp
      _ = 1 := hp.2

private def defaultConfig {ι : Type} {S : ι → Type} [∀ x, Nonempty (S x)] : Config S :=
  fun x => Classical.choice (inferInstance : Nonempty (S x))

private def conditionalCompletion {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (B : Finset ι) (σ : Config S) : ℝ :=
  p σ / marginal p (restrict B) (restrict B σ)

private def extendOn {ι : Type} {S : ι → Type} (B : Finset ι)
    (b : (x : B) → S x) (base : Config S) : Config S :=
  fun x => if hx : x ∈ B then b ⟨x, hx⟩ else base x

private theorem agreeOn_extend_iff {ι : Type} [DecidableEq ι] {S : ι → Type}
    (B : Finset ι) (b : (x : B) → S x) (base σ : Config S) :
    AgreeOn B σ (extendOn B b base) ↔ restrict B σ = b := by
  constructor
  · intro h
    funext x
    have hx := h x x.property
    simpa [extendOn, restrict] using hx
  · intro h x hx
    have hx' := congrFun h ⟨x, hx⟩
    simpa [extendOn, restrict, hx] using hx'

private theorem assignmentCompletion_event {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p) (α : ℝ) (A B : Finset ι)
    (hbound : AssignmentBound p α) (hdisj : Disjoint A B)
    (base : Config S) (b : (x : B) → S x) :
    α ^ A.card ≤
      ∑ σ, if restrict B σ = b ∧ AgreeOn A σ base then
        conditionalCompletion p B σ else 0 := by
  classical
  let bfull := extendOn B b base
  have hbpos := marginal_pos p hp B b
  have hrel : ∀ σ, AgreeOn B σ bfull ↔ restrict B σ = b := by
    intro σ
    exact agreeOn_extend_iff B b base σ
  have hden : (∑ σ, if AgreeOn B σ bfull then p σ else 0) =
      marginal p (restrict B) b := by
    simp [marginal, hrel]
  have hnum : (∑ σ, if AgreeOn B σ bfull ∧ AgreeOn A σ base then p σ else 0) =
      ∑ σ, if restrict B σ = b ∧ AgreeOn A σ base then p σ else 0 := by
    apply Finset.sum_congr rfl
    intro σ hσ
    simp [hrel]
  have hcomp :
      (∑ σ, if restrict B σ = b ∧ AgreeOn A σ base then
        conditionalCompletion p B σ else 0) =
      (∑ σ, if restrict B σ = b ∧ AgreeOn A σ base then p σ else 0) /
        marginal p (restrict B) b := by
    have hterms : ∀ σ,
        (if restrict B σ = b ∧ AgreeOn A σ base then conditionalCompletion p B σ else 0) =
        (if restrict B σ = b ∧ AgreeOn A σ base then p σ else 0) /
          marginal p (restrict B) b := by
      intro σ
      by_cases h : restrict B σ = b ∧ AgreeOn A σ base
      · simp [conditionalCompletion, h]
      · simp [h]
    rw [show (∑ σ, if restrict B σ = b ∧ AgreeOn A σ base then
          conditionalCompletion p B σ else 0) =
        ∑ σ, (if restrict B σ = b ∧ AgreeOn A σ base then p σ else 0) /
          marginal p (restrict B) b by
          apply Finset.sum_congr rfl
          intro σ hσ
          exact hterms σ]
    rw [← Finset.sum_div]
  have hprob : conditionalProbability p (AgreeOn B · bfull) (AgreeOn A · base) =
      (∑ σ, if restrict B σ = b ∧ AgreeOn A σ base then p σ else 0) /
        marginal p (restrict B) b := by
    unfold conditionalProbability
    rw [hnum, hden]
  have hassign := hbound A B hdisj bfull base
  rw [hprob, ← hcomp] at hassign
  exact hassign

private theorem conditionalCompletion_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (B : Finset ι)
    (hp : PositiveProbability p) (b : (x : B) → S x) :
    (∑ σ, if restrict B σ = b then conditionalCompletion p B σ else 0) = 1 := by
  classical
  have hbpos := marginal_pos p hp B b
  have hterm : ∀ σ, (if restrict B σ = b then conditionalCompletion p B σ else 0) =
      (if restrict B σ = b then p σ else 0) / marginal p (restrict B) b := by
    intro σ
    by_cases h : restrict B σ = b
    · simp [conditionalCompletion, h]
    · simp [h]
  rw [show (∑ σ, if restrict B σ = b then conditionalCompletion p B σ else 0) =
      ∑ σ, (if restrict B σ = b then p σ else 0) / marginal p (restrict B) b by
    apply Finset.sum_congr rfl
    intro σ hσ
    exact hterm σ]
  rw [← Finset.sum_div]
  have hpos : 0 < (∑ σ, if restrict B σ = b then p σ else 0) := by
    simpa [marginal] using hbpos
  simp [marginal, hpos.ne']

private def residualLeft {Ω : Type} (p q : Weight Ω) (x : Ω) : ℝ :=
  p x - min (p x) (q x)

private def residualRight {Ω : Type} (p q : Weight Ω) (x : Ω) : ℝ :=
  q x - min (p x) (q x)

private theorem maximalFiniteCoupling {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (p q : Weight Ω) (hp : Probability p) (hq : Probability q) :
    ∃ c : Coupling p q, ∀ x, min (p x) (q x) ≤ c.mass x x := by
  classical
  let o : ℝ := ∑ x, min (p x) (q x)
  let d : ℝ := 1 - o
  have ho_le : o ≤ 1 := by
    dsimp [o]
    calc
      (∑ x, min (p x) (q x)) ≤ ∑ x, p x := by
        apply Finset.sum_le_sum
        intro x hx
        exact min_le_left _ _
      _ = 1 := hp.2
  have hd_nonneg : 0 ≤ d := by dsimp [d]; linarith
  have hleft_sum : (∑ x, residualLeft p q x) = d := by
    dsimp [residualLeft, d, o]
    rw [Finset.sum_sub_distrib, hp.2]
  have hright_sum : (∑ x, residualRight p q x) = d := by
    dsimp [residualRight, d, o]
    rw [Finset.sum_sub_distrib, hq.2]
  have hleft_nonneg : ∀ x, 0 ≤ residualLeft p q x := by
    intro x
    exact sub_nonneg.mpr (min_le_left _ _)
  have hright_nonneg : ∀ x, 0 ≤ residualRight p q x := by
    intro x
    exact sub_nonneg.mpr (min_le_right _ _)
  have hleft_zero : d = 0 → ∀ x, residualLeft p q x = 0 := by
    intro hd0 x
    have hz : (∑ x, residualLeft p q x) = 0 := by rw [hleft_sum, hd0]
    have hnonneg : ∀ x ∈ (Finset.univ : Finset Ω), 0 ≤ residualLeft p q x :=
      fun x _ => hleft_nonneg x
    have hz' : ∑ x ∈ (Finset.univ : Finset Ω), residualLeft p q x = 0 := by simpa using hz
    have hxz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz'
    exact hxz x (Finset.mem_univ x)
  have hright_zero : d = 0 → ∀ x, residualRight p q x = 0 := by
    intro hd0 x
    have hz : (∑ x, residualRight p q x) = 0 := by rw [hright_sum, hd0]
    have hnonneg : ∀ x ∈ (Finset.univ : Finset Ω), 0 ≤ residualRight p q x :=
      fun x _ => hright_nonneg x
    have hz' : ∑ x ∈ (Finset.univ : Finset Ω), residualRight p q x = 0 := by simpa using hz
    have hxz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hz'
    exact hxz x (Finset.mem_univ x)
  let c : Coupling p q := {
    mass := fun x y => (if x = y then min (p x) (q x) else 0) +
      (if d = 0 then 0 else residualLeft p q x * residualRight p q y / d)
    nonnegative := by
      intro x y
      by_cases hxy : x = y
      · subst y
        have hp0 := hp.1 x
        have hq0 := hq.1 x
        by_cases hd : d = 0
        · simp [hd]
          exact ⟨hp0, hq0⟩
        · simp [hd]
          have hleft := hleft_nonneg x
          have hright := hright_nonneg x
          positivity
      · simp only [hxy, ↓reduceIte]
        by_cases hd : d = 0
        · simp [hd]
        · have hdpos : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm hd)
          have hleft := hleft_nonneg x
          have hright := hright_nonneg y
          positivity
    first_marginal := by
      intro x
      by_cases hd : d = 0
      · simp [hd]
        have hz := hleft_zero hd x
        dsimp [residualLeft] at hz
        by_cases h : q x < p x
        · rw [min_eq_right (le_of_lt h)] at hz
          linarith
        · rw [min_eq_left (le_of_not_gt h)] at hz
          linarith
      · have hdpos : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm hd)
        have hextra : (∑ y, residualLeft p q x * residualRight p q y / d) =
            residualLeft p q x := by
          rw [← Finset.sum_div, ← Finset.mul_sum, hright_sum]
          field_simp
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_ite_eq (Finset.univ) x (fun _ => min (p x) (q x))]
        simp only [Finset.mem_univ, if_true]
        rw [Finset.sum_ite_irrel]
        simp only [hd, if_false]
        rw [hextra]
        dsimp [residualLeft]
        ring
    second_marginal := by
      intro y
      by_cases hd : d = 0
      · simp [hd]
        have hz := hright_zero hd y
        dsimp [residualRight] at hz
        by_cases h : p y < q y
        · rw [min_eq_left (le_of_lt h)] at hz
          linarith
        · rw [min_eq_right (le_of_not_gt h)] at hz
          linarith
      · have hdpos : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm hd)
        have hextra : (∑ x, residualLeft p q x * residualRight p q y / d) =
            residualRight p q y := by
          rw [← Finset.sum_div, ← Finset.sum_mul, hleft_sum]
          field_simp
        simp only [Finset.sum_add_distrib]
        rw [Finset.sum_ite_eq' (Finset.univ) y (fun x => min (p x) (q x))]
        simp only [Finset.mem_univ, if_true]
        rw [Finset.sum_ite_irrel]
        simp only [hd, if_false]
        rw [hextra]
        dsimp [residualRight]
        ring }
  refine ⟨c, ?_⟩
  intro x
  by_cases hd : d = 0
  · simp [c, hd]
  · have hdpos : 0 < d := lt_of_le_of_ne hd_nonneg (Ne.symm hd)
    have hleft := hleft_nonneg x
    have hright := hright_nonneg x
    have hnonneg : 0 ≤ residualLeft p q x * residualRight p q x / d := by positivity
    dsimp [c]
    simp [hd]
    linarith

private theorem offDiagonal_le_one {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (p q : Weight Ω) (hp : Probability p) (c : Coupling p q) :
    (∑ x, ∑ y, if x = y then 0 else c.mass x y) =
      1 - ∑ x, c.mass x x := by
  have hrow : (∑ x, ∑ y, c.mass x y) = 1 := by
    calc
      (∑ x, ∑ y, c.mass x y) = ∑ x, p x := by
        congr 1
        funext x
        exact c.first_marginal x
      _ = 1 := hp.2
  have hinner : ∀ x, (∑ y, if x = y then 0 else c.mass x y) =
      (∑ y, c.mass x y) - c.mass x x := by
    intro x
    have hpoint : ∀ y, (if x = y then 0 else c.mass x y) =
        c.mass x y - (if x = y then c.mass x y else 0) := by
      intro y
      by_cases h : x = y <;> simp [h]
    rw [show (∑ y, if x = y then 0 else c.mass x y) =
      ∑ y, (c.mass x y - (if x = y then c.mass x y else 0)) by
        apply Finset.sum_congr rfl
        intro y hy
        exact hpoint y]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq (Finset.univ) x (fun y => c.mass x y)]
    simp
  calc
    (∑ x, ∑ y, if x = y then 0 else c.mass x y) =
        ∑ x, ((∑ y, c.mass x y) - c.mass x x) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact hinner x
    _ = (∑ x, ∑ y, c.mass x y) - ∑ x, c.mass x x := by rw [Finset.sum_sub_distrib]
    _ = 1 - ∑ x, c.mass x x := by rw [hrow]

private theorem disagreement_eq_one_sub_agreement {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] {p q : Weight (Config S)}
    (hp : Probability p) (c : Coupling p q) (U : Finset ι) :
    disagreement c U = 1 -
      (∑ σ, ∑ τ, if AgreeOn U σ τ then c.mass σ τ else 0) := by
  classical
  have htotal : (∑ σ, ∑ τ, c.mass σ τ) = 1 := by
    calc
      (∑ σ, ∑ τ, c.mass σ τ) = ∑ σ, p σ := by
        congr 1
        funext σ
        exact c.first_marginal σ
      _ = 1 := hp.2
  have hpoint : ∀ σ τ,
      (if AgreeOn U σ τ then 0 else c.mass σ τ) =
        c.mass σ τ - (if AgreeOn U σ τ then c.mass σ τ else 0) := by
    intro σ τ
    by_cases h : AgreeOn U σ τ <;> simp [h]
  unfold disagreement
  rw [show (∑ σ, ∑ τ, if AgreeOn U σ τ then 0 else c.mass σ τ) =
      ∑ σ, ∑ τ, (c.mass σ τ - (if AgreeOn U σ τ then c.mass σ τ else 0)) by
        apply Finset.sum_congr rfl
        intro σ hσ
        apply Finset.sum_congr rfl
        intro τ hτ
        exact hpoint σ τ]
  rw [show (∑ σ, ∑ τ, (c.mass σ τ -
      (if AgreeOn U σ τ then c.mass σ τ else 0))) =
      ∑ σ, ((∑ τ, c.mass σ τ) - (∑ τ, if AgreeOn U σ τ then c.mass σ τ else 0)) by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [Finset.sum_sub_distrib]]
  rw [Finset.sum_sub_distrib]
  rw [htotal]

private def liftFullCoupling {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p q : Weight (Config S)) (B : Finset ι)
    (hp : PositiveProbability p) (hq : PositiveProbability q)
    (c : Coupling (marginal p (restrict B)) (marginal q (restrict B))) : Coupling p q := by
  classical
  refine {
    mass := fun σ τ => c.mass (restrict B σ) (restrict B τ) *
      conditionalCompletion p B σ * conditionalCompletion q B τ
    nonnegative := ?_
    first_marginal := ?_
    second_marginal := ?_ }
  · intro σ τ
    have hpden := marginal_pos p hp B (restrict B σ)
    have hqden := marginal_pos q hq B (restrict B τ)
    have hpcond : 0 ≤ conditionalCompletion p B σ := by
      unfold conditionalCompletion
      exact div_nonneg (hp.1 σ).le (marginal_pos p hp B (restrict B σ)).le
    have hqcond : 0 ≤ conditionalCompletion q B τ := by
      unfold conditionalCompletion
      exact div_nonneg (hq.1 τ).le (marginal_pos q hq B (restrict B τ)).le
    exact mul_nonneg (mul_nonneg (c.nonnegative _ _) hpcond) hqcond
  · intro σ
    classical
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Config S)) (restrict B)
      (fun τ => c.mass (restrict B σ) (restrict B τ) *
        conditionalCompletion p B σ * conditionalCompletion q B τ)]
    have hfiber : ∀ b : (x : B) → S x,
        (∑ τ ∈ (Finset.univ : Finset (Config S)) with restrict B τ = b,
          c.mass (restrict B σ) (restrict B τ) *
            conditionalCompletion p B σ * conditionalCompletion q B τ) =
          c.mass (restrict B σ) b * conditionalCompletion p B σ := by
      intro b
      have heq : (∑ τ ∈ (Finset.univ : Finset (Config S)) with restrict B τ = b,
          c.mass (restrict B σ) (restrict B τ) *
            conditionalCompletion p B σ * conditionalCompletion q B τ) =
          c.mass (restrict B σ) b * conditionalCompletion p B σ *
            (∑ τ ∈ (Finset.univ : Finset (Config S)) with restrict B τ = b,
              conditionalCompletion q B τ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro τ hτ
        rcases Finset.mem_filter.mp hτ with ⟨_, hτ⟩
        rw [hτ]
      rw [heq]
      have hsumq := conditionalCompletion_sum q B hq b
      rw [← Finset.sum_filter] at hsumq
      rw [hsumq]
      ring
    calc
      (∑ b, ∑ τ ∈ (Finset.univ : Finset (Config S)) with restrict B τ = b,
          c.mass (restrict B σ) (restrict B τ) *
            conditionalCompletion p B σ * conditionalCompletion q B τ) =
          ∑ b, c.mass (restrict B σ) b * conditionalCompletion p B σ := by
            apply Finset.sum_congr rfl
            intro b hb
            exact hfiber b
      _ = (∑ b, c.mass (restrict B σ) b) * conditionalCompletion p B σ := by
            rw [Finset.sum_mul]
      _ = p σ := by
            rw [c.first_marginal (restrict B σ)]
            unfold conditionalCompletion
            have hpos := marginal_pos p hp B (restrict B σ)
            field_simp [hpos.ne']
  · intro τ
    classical
    rw [← Finset.sum_fiberwise (Finset.univ : Finset (Config S)) (restrict B)
      (fun σ => c.mass (restrict B σ) (restrict B τ) *
        conditionalCompletion p B σ * conditionalCompletion q B τ)]
    have hfiber : ∀ b : (x : B) → S x,
        (∑ σ ∈ (Finset.univ : Finset (Config S)) with restrict B σ = b,
          c.mass (restrict B σ) (restrict B τ) *
            conditionalCompletion p B σ * conditionalCompletion q B τ) =
          c.mass b (restrict B τ) * conditionalCompletion q B τ := by
      intro b
      have heq : (∑ σ ∈ (Finset.univ : Finset (Config S)) with restrict B σ = b,
          c.mass (restrict B σ) (restrict B τ) *
            conditionalCompletion p B σ * conditionalCompletion q B τ) =
          c.mass b (restrict B τ) * conditionalCompletion q B τ *
            (∑ σ ∈ (Finset.univ : Finset (Config S)) with restrict B σ = b,
              conditionalCompletion p B σ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro σ hσ
        rcases Finset.mem_filter.mp hσ with ⟨_, hσ⟩
        rw [hσ]
        ring
      rw [heq]
      have hsumP := conditionalCompletion_sum p B hp b
      rw [← Finset.sum_filter] at hsumP
      rw [hsumP]
      ring
    calc
      (∑ b, ∑ σ ∈ (Finset.univ : Finset (Config S)) with restrict B σ = b,
          c.mass (restrict B σ) (restrict B τ) *
            conditionalCompletion p B σ * conditionalCompletion q B τ) =
          ∑ b, c.mass b (restrict B τ) * conditionalCompletion q B τ := by
            apply Finset.sum_congr rfl
            intro b hb
            exact hfiber b
      _ = (∑ b, c.mass b (restrict B τ)) * conditionalCompletion q B τ := by
            rw [Finset.sum_mul]
      _ = q τ := by
            rw [c.second_marginal (restrict B τ)]
            unfold conditionalCompletion
            have hpos := marginal_pos q hq B (restrict B τ)
            field_simp [hpos.ne']

private def hitMass {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (A B : Finset ι) (base : Config S)
    (b : (x : B) → S x) : ℝ :=
  ∑ σ, if restrict B σ = b ∧ AgreeOn A σ base then
    conditionalCompletion p B σ else 0

private def assignmentPairTerm {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p q : Weight (Config S)) (A B : Finset ι) (base : Config S)
    (b : (x : B) → S x) (σ τ : Config S) : ℝ :=
  (if restrict B σ = b ∧ AgreeOn A σ base then conditionalCompletion p B σ else 0) *
  (if restrict B τ = b ∧ AgreeOn A τ base then conditionalCompletion q B τ else 0)

private def prescribedPairMass {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p q : Weight (Config S)) (A B : Finset ι) (base : Config S)
    (c : Coupling (marginal p (restrict B)) (marginal q (restrict B))) : ℝ :=
  ∑ b, c.mass b b * hitMass p A B base b * hitMass q A B base b

private def prescribedPairEventMass {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p q : Weight (Config S)) (hp : PositiveProbability p) (hq : PositiveProbability q)
    (A B : Finset ι) (base : Config S)
    (c : Coupling (marginal p (restrict B)) (marginal q (restrict B))) : ℝ :=
  ∑ σ, ∑ τ, if restrict B σ = restrict B τ ∧
      AgreeOn A σ base ∧ AgreeOn A τ base then
    (liftFullCoupling p q B hp hq c).mass σ τ
    else 0

private theorem fixed_assignment_pair_factor {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p q : Weight (Config S)) (A B : Finset ι) (base : Config S)
    (c : Coupling (marginal p (restrict B)) (marginal q (restrict B)))
    (b : (x : B) → S x) :
    c.mass b b * hitMass p A B base b * hitMass q A B base b =
      ∑ σ, ∑ τ, assignmentPairTerm p q A B base b σ τ * c.mass b b := by
  classical
  let P := fun σ : Config S =>
    if restrict B σ = b ∧ AgreeOn A σ base then conditionalCompletion p B σ else 0
  let Q := fun τ : Config S =>
    if restrict B τ = b ∧ AgreeOn A τ base then conditionalCompletion q B τ else 0
  calc
    c.mass b b * hitMass p A B base b * hitMass q A B base b =
        c.mass b b * (∑ σ, P σ) * (∑ τ, Q τ) := by rfl
    _ = ∑ σ, ∑ τ, P σ * Q τ * c.mass b b := by
      calc
        c.mass b b * (∑ σ, P σ) * (∑ τ, Q τ) =
            (∑ σ, P σ) * (∑ τ, Q τ) * c.mass b b := by ring
        _ = (∑ σ, P σ * (∑ τ, Q τ)) * c.mass b b := by rw [Finset.sum_mul]
        _ = ∑ σ, (P σ * (∑ τ, Q τ)) * c.mass b b := by rw [Finset.sum_mul]
        _ = ∑ σ, ∑ τ, P σ * Q τ * c.mass b b := by
              apply Finset.sum_congr rfl
              intro σ hσ
              calc
                (P σ * (∑ τ, Q τ)) * c.mass b b =
                    (∑ τ, P σ * Q τ) * c.mass b b := by rw [Finset.mul_sum]
                _ = ∑ τ, P σ * Q τ * c.mass b b := by rw [Finset.sum_mul]

private theorem one_block_sum_eq_event {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p q : Weight (Config S)) (A B : Finset ι) (base : Config S)
    (hp : PositiveProbability p) (hq : PositiveProbability q)
    (c : Coupling (marginal p (restrict B)) (marginal q (restrict B)))
    (σ τ : Config S) :
    (∑ b, assignmentPairTerm p q A B base b σ τ * c.mass b b) =
      if restrict B σ = restrict B τ ∧ AgreeOn A σ base ∧ AgreeOn A τ base then
        (liftFullCoupling p q B hp hq c).mass σ τ else 0 := by
  classical
  by_cases hσ : AgreeOn A σ base
  · by_cases hτ : AgreeOn A τ base
    · by_cases hB : restrict B σ = restrict B τ
      · have hsum :
            (∑ b, assignmentPairTerm p q A B base b σ τ * c.mass b b) =
              assignmentPairTerm p q A B base (restrict B σ) σ τ *
                c.mass (restrict B σ) (restrict B σ) :=
            Fintype.sum_eq_single (restrict B σ) (by
              intro b hb
              have hnotσ : restrict B σ ≠ b := fun h => hb h.symm
              simp [assignmentPairTerm, hnotσ])
        rw [hsum]
        simp [assignmentPairTerm, hσ, hτ, hB, liftFullCoupling]
        ring
      · have hzero : ∀ b, assignmentPairTerm p q A B base b σ τ = 0 := by
          intro b
          by_cases hσb : restrict B σ = b
          · have hτb : restrict B τ ≠ b := by
              intro h
              exact hB (hσb.trans h.symm)
            simp [assignmentPairTerm, hσ, hτ, hσb, hτb]
          · simp [assignmentPairTerm, hσ, hσb]
        simp [hB, hσ, hτ, hzero]
    · have hzero : ∀ b, assignmentPairTerm p q A B base b σ τ = 0 := by
        intro b
        simp [assignmentPairTerm, hσ, hτ]
      simp [hτ, hzero]
  · have hzero : ∀ b, assignmentPairTerm p q A B base b σ τ = 0 := by
      intro b
      simp [assignmentPairTerm, hσ]
    simp [hσ, hzero]

private theorem prescribedPairMass_eq_eventMass {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p q : Weight (Config S)) (hp : PositiveProbability p) (hq : PositiveProbability q)
    (A B : Finset ι) (base : Config S)
    (c : Coupling (marginal p (restrict B)) (marginal q (restrict B))) :
    prescribedPairMass p q A B base c = prescribedPairEventMass p q hp hq A B base c := by
  classical
  unfold prescribedPairMass prescribedPairEventMass
  calc
    (∑ b, c.mass b b * hitMass p A B base b * hitMass q A B base b) =
        ∑ b, ∑ σ, ∑ τ,
          assignmentPairTerm p q A B base b σ τ * c.mass b b := by
            apply Finset.sum_congr rfl
            intro b hb
            exact fixed_assignment_pair_factor p q A B base c b
    _ = ∑ σ, ∑ τ, ∑ b,
          assignmentPairTerm p q A B base b σ τ * c.mass b b := by
            calc
              (∑ b, ∑ σ, ∑ τ, assignmentPairTerm p q A B base b σ τ * c.mass b b) =
                  ∑ σ, ∑ b, ∑ τ, assignmentPairTerm p q A B base b σ τ * c.mass b b := by
                    exact sum_comm_fintype (fun b σ => ∑ τ,
                      assignmentPairTerm p q A B base b σ τ * c.mass b b)
              _ = ∑ σ, ∑ τ, ∑ b,
                    assignmentPairTerm p q A B base b σ τ * c.mass b b := by
                    apply Finset.sum_congr rfl
                    intro σ hσ
                    exact sum_comm_fintype (fun b τ =>
                      assignmentPairTerm p q A B base b σ τ * c.mass b b)
    _ = ∑ σ, ∑ τ, if restrict B σ = restrict B τ ∧
          AgreeOn A σ base ∧ AgreeOn A τ base then
          (liftFullCoupling p q B hp hq c).mass σ τ else 0 := by
            apply Finset.sum_congr rfl
            intro σ hσ
            apply Finset.sum_congr rfl
            intro τ hτ
            exact one_block_sum_eq_event p q A B base hp hq c σ τ

private theorem hitMass_nonneg {ι : Type} [Fintype ι] [DecidableEq ι]
    {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config S)) (hp : PositiveProbability p) (A B : Finset ι)
    (base : Config S) (b : (x : B) → S x) : 0 ≤ hitMass p A B base b := by
  classical
  unfold hitMass
  apply Finset.sum_nonneg
  intro σ hσ
  by_cases h : restrict B σ = b ∧ AgreeOn A σ base
  · simp [h]
    unfold conditionalCompletion
    exact div_nonneg (hp.1 σ).le (marginal_pos p hp B (restrict B σ)).le
  · simp [h]

private theorem prescribedPairEventMass_le_agreement {ι : Type} [Fintype ι]
    [DecidableEq ι] {S : ι → Type} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p q : Weight (Config S)) (hp : PositiveProbability p) (hq : PositiveProbability q)
    (A B : Finset ι) (base : Config S)
    (c : Coupling (marginal p (restrict B)) (marginal q (restrict B))) :
    prescribedPairEventMass p q hp hq A B base c ≤
      (∑ σ, ∑ τ, if AgreeOn (A ∪ B) σ τ then
        (liftFullCoupling p q B hp hq c).mass σ τ else 0) := by
  classical
  unfold prescribedPairEventMass
  apply Finset.sum_le_sum
  intro σ hσ
  apply Finset.sum_le_sum
  intro τ hτ
  by_cases h : restrict B σ = restrict B τ ∧ AgreeOn A σ base ∧ AgreeOn A τ base
  · have hB : AgreeOn B σ τ := by
      intro x hx
      have heq := congrFun h.1 ⟨x, hx⟩
      simpa [restrict] using heq
    have hA : AgreeOn A σ τ := by
      intro x hx
      calc
        σ x = base x := h.2.1 x hx
        _ = τ x := (h.2.2 x hx).symm
    have hAB : AgreeOn (A ∪ B) σ τ := by
      intro x hx
      rcases Finset.mem_union.mp hx with hxA | hxB
      · exact hA x hxA
      · exact hB x hxB
    simp [h, hAB]
  · have hnonneg := (liftFullCoupling p q B hp hq c).nonnegative σ τ
    simp only [h, ↓reduceIte]
    split_ifs <;> linarith

theorem main : AKLT.Blueprint.Gap.ConditionalPatchCouplingStatement := by
  classical
  intro ι hι hdec S hS hSne p q hp hq A B α t hdisj hα hα1 ht ht1 hpbound hqbound htv
  let pB := marginal p (restrict B)
  let qB := marginal q (restrict B)
  have hpProb : Probability p := ⟨fun σ => (hp.1 σ).le, hp.2⟩
  have hqProb : Probability q := ⟨fun σ => (hq.1 σ).le, hq.2⟩
  have hpB : Probability pB := by
    exact marginal_probability p (restrict B) hpProb
  have hqB : Probability qB := by
    exact marginal_probability q (restrict B) hqProb
  obtain ⟨cB, hcBdiag⟩ := maximalFiniteCoupling pB qB hpB hqB
  have hoverlap := overlap_eq_one_sub_tv pB qB hpB hqB
  have htOverlap : t ≤ ∑ b, min (pB b) (qB b) := by
    rw [hoverlap]
    linarith
  have hdiag : (∑ b, min (pB b) (qB b)) ≤ ∑ b, cB.mass b b := by
    apply Finset.sum_le_sum
    intro b hb
    exact hcBdiag b
  have htDiag : t ≤ ∑ b, cB.mass b b := htOverlap.trans hdiag
  let base : Config S := defaultConfig
  let c := liftFullCoupling p q B hp hq cB
  let n : ℝ := α ^ A.card
  let target : ℝ := α ^ (2 * A.card)
  have hn : 0 ≤ n := by dsimp [n]; positivity
  have htarget : target = n * n := by
    dsimp [target, n]
    rw [two_mul, pow_add]
  have htargetNonneg : 0 ≤ target := by rw [htarget]; positivity
  have hsub : target * (∑ b, cB.mass b b) ≤
      prescribedPairMass p q A B base cB := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hhp := assignmentCompletion_event p hp α A B hpbound hdisj base b
    have hhq := assignmentCompletion_event q hq α A B hqbound hdisj base b
    have hnp := hitMass_nonneg p hp A B base b
    have hnq := hitMass_nonneg q hq A B base b
    have hprod := mul_le_mul hhp hhq hn hnp
    have hscaled := mul_le_mul_of_nonneg_left hprod (cB.nonnegative b b)
    have heq : target * cB.mass b b = cB.mass b b * (n * n) := by
      rw [htarget]
      ring
    rw [heq]
    calc
      cB.mass b b * (n * n) ≤ cB.mass b b *
          (hitMass p A B base b * hitMass q A B base b) := hscaled
      _ = cB.mass b b * hitMass p A B base b * hitMass q A B base b := by ring
  have hsuccess : t * target ≤ prescribedPairMass p q A B base cB := by
    calc
      t * target = target * t := by ring
      _ ≤ target * (∑ b, cB.mass b b) :=
        mul_le_mul_of_nonneg_left htDiag htargetNonneg
      _ ≤ prescribedPairMass p q A B base cB := hsub
  have hsuccessAgreement : t * target ≤
      (∑ σ, ∑ τ, if AgreeOn (A ∪ B) σ τ then c.mass σ τ else 0) := by
    calc
      t * target ≤ prescribedPairMass p q A B base cB := hsuccess
      _ = prescribedPairEventMass p q hp hq A B base cB :=
        prescribedPairMass_eq_eventMass p q hp hq A B base cB
      _ ≤ ∑ σ, ∑ τ, if AgreeOn (A ∪ B) σ τ then c.mass σ τ else 0 := by
        simpa [c] using prescribedPairEventMass_le_agreement p q hp hq A B base cB
  refine ⟨c, ?_⟩
  have hdis := disagreement_eq_one_sub_agreement hpProb c (A ∪ B)
  rw [hdis]
  linarith

end AKLT.W.GAP010
