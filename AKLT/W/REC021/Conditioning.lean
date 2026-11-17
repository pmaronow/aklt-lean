module
public import AKLT.W.REC021.NetworkFactors

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC021

def pinWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (n : Plane → Vec3) : ℝ :=
  ∏ e : originalLegs G,
    if pinned = true ∧ e.val.1 ∈ D.active then 1 + dot (τ e).val (n e.val.1) else 1

def networkWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (σ : D.active → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (σ x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins σ e.1) (D.spins σ e.2))) *
    pinWeight D τ pinned (D.spins σ)

theorem partition_as_weight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ pinned f = ∑ σ, networkWeight D τ pinned σ * f (D.spins σ) := by
  unfold Network.partition
  apply Finset.sum_congr rfl
  intro σ _
  dsimp [networkWeight, pinWeight]
  ring

theorem pinWeight_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (σ : D.active → SpinLetter) : 0 ≤ pinWeight D τ pinned (D.spins σ) := by
  unfold pinWeight
  apply Finset.prod_nonneg
  intro e _
  split_ifs
  · exact one_add_dot_nonneg (τ e).property.le (spins_ball D σ e.val.1)
  · norm_num

theorem networkWeight_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (σ : D.active → SpinLetter) : 0 ≤ networkWeight D τ pinned σ := by
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg fun x _ => spinWeight_nonneg _ _
    · exact Finset.prod_nonneg fun e _ => one_add_dot_nonneg (spins_ball D σ e.1) (spins_ball D σ e.2)
  · exact pinWeight_nonneg D τ pinned σ

theorem spins_update {G : Finset Plane} (D : Network G) (σ : D.active → SpinLetter)
    (x : D.active) (j : SpinLetter) :
    D.spins (Function.update σ x j) = Function.update (D.spins σ) x.val (spinVector j) := by
  funext z
  by_cases hzx : z = x.val
  · subst z
    simp [Network.spins, x.property, Function.update_apply]
  · by_cases hz : z ∈ D.active
    · have hsub : (⟨z, hz⟩ : D.active) ≠ x := by
        intro he
        exact hzx (congrArg Subtype.val he)
      simp [Network.spins, hz, hzx, hsub, Function.update_apply]
    · simp [Network.spins, hz, hzx, Function.update_apply]

theorem spins_blockUpdate {G : Finset Plane} (D : Network G) (σ : D.active → SpinLetter)
    (x : Fin 3 → D.active) (j : Fin 3 → SpinLetter) :
    D.spins (blockUpdate x σ j) =
      blockUpdate (fun i => (x i).val) (D.spins σ) (fun i => spinVector (j i)) := by
  simp only [blockUpdate, spins_update]

theorem pinWeight_blockUpdate {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (σ : D.active → SpinLetter) (x : Fin 3 → D.active)
    (hpin : ∀ e : originalLegs G, ∀ i, e.val.1 ≠ (x i).val) (j : Fin 3 → SpinLetter) :
    pinWeight D τ pinned (D.spins (blockUpdate x σ j)) = pinWeight D τ pinned (D.spins σ) := by
  rw [spins_blockUpdate]
  apply Finset.prod_congr rfl
  intro e _
  simp [pinWeight, blockUpdate, Function.update_apply, hpin e 0, hpin e 1, hpin e 2]

theorem active_status {G : Finset Plane} (D : Network G) (x : D.active) :
    D.status x = .U ∨ D.status x = .D := by
  have h := (Finset.mem_filter.mp x.property).2
  cases hs : D.status x <;> simp_all

/-- Collect the factors at three unpinned, mutually nonadjacent sites. -/
theorem network_cubicFibre {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (x : Fin 3 → D.active) (hinj : Function.Injective x)
    (hnobond : ∀ e ∈ D.bonds, ∀ i j, ¬ (e.1 = (x i).val ∧ e.2 = (x j).val))
    (hdegree : ∀ i, (D.presentNeighbours (x i).val).card ≤ 3)
    (hpin : ∀ e : originalLegs G, ∀ i, e.val.1 ≠ (x i).val)
    (σ : D.active → SpinLetter) :
    ∃ F : CubicFibre, ∀ j, networkWeight D τ pinned (blockUpdate x σ j) = F.weight j := by
  let xp : Fin 3 → Plane := fun i => (x i).val
  have hxp : Function.Injective xp := Subtype.val_injective.comp hinj
  have hfields (i : Fin 3) : ∃ a : Fin 3 → Vec3, (∀ k, normSq (a k) ≤ 1) ∧
      ∀ n : Vec3, localBondProduct D (D.spins σ) (xp i) n = cubicWeight (a 0) (a 1) (a 2) n := by
    exact three_fields (incidentBonds D (xp i)) (fun e => D.spins σ (otherEnd (xp i) e))
      ((incident_card_le D (xp i)).trans (hdegree i)) (fun e _ => spins_ball D σ _)
  choose fields hfieldsball hfieldsprod using hfields
  let C : ℝ :=
    (∏ u : D.active, if u = x 0 ∨ u = x 1 ∨ u = x 2 then 1 else spinWeight (D.status u) (σ u)) *
      outsideBondProduct D (D.spins σ) xp * pinWeight D τ pinned (D.spins σ)
  have hC : 0 ≤ C := by
    apply mul_nonneg
    · apply mul_nonneg
      · apply Finset.prod_nonneg
        intro u _
        split_ifs
        · norm_num
        · exact spinWeight_nonneg _ _
      · unfold outsideBondProduct
        apply Finset.prod_nonneg
        intro e _
        split_ifs
        · exact one_add_dot_nonneg (spins_ball D σ e.1) (spins_ball D σ e.2)
        · norm_num
    · exact pinWeight_nonneg D τ pinned σ
  let F : CubicFibre :=
    { coefficient := C
      coefficient_nonneg := hC
      status := fun i => D.status (x i).val
      status_active := fun i => active_status D (x i)
      field := fields
      field_ball := hfieldsball }
  refine ⟨F, ?_⟩
  intro j
  unfold networkWeight
  rw [pinWeight_blockUpdate D τ pinned σ x hpin j,
    three_site_factorization (fun u : D.active => spinWeight (D.status u)) x hinj σ j,
    spins_blockUpdate]
  rw [three_bond_factorization D (D.spins σ) xp hxp hnobond (fun i => spinVector (j i)),
    hfieldsprod 0, hfieldsprod 1, hfieldsprod 2]
  dsimp [F, CubicFibre.weight, CubicFibre.localFactor, C, xp]
  simp only [Fin.prod_univ_three]
  ring

theorem blockUpdate_at {ι Ω : Type*} [DecidableEq ι]
    (x : Fin 3 → ι) (hinj : Function.Injective x) (σ : ι → Ω) (j : Fin 3 → Ω) (i : Fin 3) :
    blockUpdate x σ j (x i) = j i := by
  have hx01 : x 0 ≠ x 1 := hinj.ne (by decide)
  have hx02 : x 0 ≠ x 2 := hinj.ne (by decide)
  have hx12 : x 1 ≠ x 2 := hinj.ne (by decide)
  fin_cases i <;> simp [blockUpdate, Function.update_apply, hx01, hx02, hx12]

theorem spins_at {G : Finset Plane} (D : Network G) (σ : D.active → SpinLetter) (x : D.active) :
    D.spins σ x.val = spinVector (σ x) := by
  simp [Network.spins, x.property]

theorem partition_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) : 0 ≤ D.partition τ pinned (fun _ => 1) := by
  rw [partition_as_weight]
  simp only [mul_one]
  exact Finset.sum_nonneg fun σ _ => networkWeight_nonneg D τ pinned σ

theorem partition_add {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (f g : (Plane → Vec3) → ℝ) :
    D.partition τ pinned (fun n => f n + g n) = D.partition τ pinned f + D.partition τ pinned g := by
  simp only [partition_as_weight, mul_add, Finset.sum_add_distrib]

/-- Sum all fibres explicitly. Uniform resampling contributes the positive
factor 13³; no division by an outside-spin fibre mass is used. -/
theorem network_three_pair_lower {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (x : Fin 3 → D.active) (hinj : Function.Injective x)
    (hnobond : ∀ e ∈ D.bonds, ∀ i j, ¬ (e.1 = (x i).val ∧ e.2 = (x j).val))
    (hdegree : ∀ i, (D.presentNeighbours (x i).val).card ≤ 3)
    (hpin : ∀ e : originalLegs G, ∀ i, e.val.1 ≠ (x i).val) :
    -(27 / 50 : ℝ) * D.partition τ pinned (fun _ => 1) ≤
      D.partition τ pinned (fun n => dot (n (x 0).val) (n (x 1).val) +
        dot (n (x 0).val) (n (x 2).val) + dot (n (x 1).val) (n (x 2).val)) := by
  let W := networkWeight D τ pinned
  let P (σ : D.active → SpinLetter) : ℝ :=
    dot (D.spins σ (x 0).val) (D.spins σ (x 1).val) +
    dot (D.spins σ (x 0).val) (D.spins σ (x 2).val) +
    dot (D.spins σ (x 1).val) (D.spins σ (x 2).val)
  have hrow (σ : D.active → SpinLetter) :
      -(27 / 50 : ℝ) * (∑ j, W (blockUpdate x σ j)) ≤
        ∑ j, W (blockUpdate x σ j) * P (blockUpdate x σ j) := by
    obtain ⟨F, hF⟩ := network_cubicFibre D τ pinned x hinj hnobond hdegree hpin σ
    have hp (j : Fin 3 → SpinLetter) : P (blockUpdate x σ j) =
        dot (spinVector (j 0)) (spinVector (j 1)) +
        dot (spinVector (j 0)) (spinVector (j 2)) +
        dot (spinVector (j 1)) (spinVector (j 2)) := by
      simp only [P, spins_at, blockUpdate_at x hinj]
    dsimp [W]
    simp_rw [hF, hp]
    rw [F.sum_weight, F.sum_weight_pairs]
    exact F.pairMass_lower
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hrow σ)
  rw [← Finset.mul_sum] at hs
  rw [sum_blockUpdate x W, sum_blockUpdate x (fun σ => W σ * P σ)] at hs
  norm_num [Fintype.card_option, Fintype.card_prod, Fintype.card_fin] at hs
  simp only [partition_as_weight, mul_one]
  change -(27 / 50 : ℝ) * (∑ σ, W σ) ≤ ∑ σ, W σ * P σ
  linarith

end AKLT.W.REC021
