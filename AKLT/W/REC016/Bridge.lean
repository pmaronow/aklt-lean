module
public import AKLT.W.REC016.Model
public import AKLT.W.REC016.Graph

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC016

@[simp] theorem spins_at {G : Finset Plane} (D : Network G)
    (σ : D.active → SpinLetter) (x : D.active) :
    D.spins σ x = spinVector (σ x) := by
  simp [Network.spins]

theorem spins_ball {G : Finset Plane} (D : Network G)
    (σ : D.active → SpinLetter) (x : Plane) : normSq (D.spins σ x) ≤ 1 := by
  unfold Network.spins
  split_ifs
  · exact spin_ball _
  · simp [normSq, dot]

def legWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (σ : D.active → SpinLetter) : ℝ :=
  ∏ e : originalLegs G, if b = true ∧ e.val.1 ∈ D.active then
    1 + dot (τ e).val (D.spins σ e.val.1) else 1

theorem legWeight_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (σ : D.active → SpinLetter) : 0 ≤ legWeight D τ b σ := by
  apply Finset.prod_nonneg
  intro e _
  split_ifs
  · have h := (ball_dot (τ e).val (D.spins σ e.val.1) (τ e).property.le
      (spins_ball D σ e.val.1)).1
    linarith
  · norm_num

theorem bond_product {G : Finset Plane} (D : Network G) (σ : D.active → SpinLetter) :
    (∏ e : D.bonds, (1 + dot (spinVector (σ (bondLeft D e)))
      (spinVector (σ (bondRight D e))))) =
      ∏ e ∈ D.bonds, (1 + dot (D.spins σ e.1) (D.spins σ e.2)) := by
  rw [← Finset.prod_coe_sort D.bonds
    (fun e => 1 + dot (D.spins σ e.1) (D.spins σ e.2))]
  apply Finset.prod_congr rfl
  intro e _
  simp [Network.spins, bondLeft, bondRight]

theorem partition_graph {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f =
      ∑ σ : D.active → SpinLetter,
        FiniteGraph.weight (fun x : D.active => D.status x) (bondLeft D) (bondRight D)
          (legWeight D τ b) σ * f (D.spins σ) := by
  classical
  unfold Network.partition
  apply Finset.sum_congr (by ext; simp)
  intro σ _
  unfold FiniteGraph.weight legWeight
  rw [bond_product]
  ring

theorem partition_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) : 0 ≤ D.partition τ b (fun _ => 1) := by
  rw [partition_graph]
  exact Finset.sum_nonneg (fun σ _ => mul_nonneg
    (FiniteGraph.weight_nonneg _ _ _ _ (legWeight_nonneg D τ b) σ) (by norm_num))

theorem legWeight_refresh {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (x y : D.active)
    (hx : ∀ e : originalLegs G, e.val.1 ≠ x.val)
    (hy : ∀ e : originalLegs G, e.val.1 ≠ y.val)
    (σ : D.active → SpinLetter) (a c : SpinLetter) :
    legWeight D τ b (Function.update (Function.update σ x a) y c) = legWeight D τ b σ := by
  classical
  unfold legWeight
  apply Finset.prod_congr rfl
  intro e _
  have hspin : D.spins (Function.update (Function.update σ x a) y c) e.val.1 =
      D.spins σ e.val.1 := by
    unfold Network.spins
    split_ifs with h
    · have hnx : (⟨e.val.1, h⟩ : D.active) ≠ x :=
        fun he => hx e (congrArg Subtype.val he)
      have hny : (⟨e.val.1, h⟩ : D.active) ≠ y :=
        fun he => hy e (congrArg Subtype.val he)
      rw [Function.update_of_ne hny, Function.update_of_ne hnx]
    · rfl
  rw [hspin]

theorem incident_other_injective {G : Finset Plane} (D : Network G) (x : D.active) :
    Function.Injective (fun e : {e : D.bonds // FiniteGraph.Inc (bondLeft D) (bondRight D) x e} =>
      (FiniteGraph.other (bondLeft D) (bondRight D) x e.val).val) := by
  classical
  intro e d heq
  apply Subtype.ext
  apply Subtype.ext
  by_cases he : bondLeft D e.val = x
  · by_cases hd : bondLeft D d.val = x
    · have h := congrArg Subtype.val he
      have h' := congrArg Subtype.val hd
      have ho : e.val.val.2 = d.val.val.2 := by
        have ho0 := heq
        simp only [FiniteGraph.other, he, hd, ↓reduceIte] at ho0
        simpa only [bondLeft, bondRight] using ho0
      exact Prod.ext (h.trans h'.symm) ho
    · have hdr : bondRight D d.val = x := d.property.resolve_left hd
      have h := congrArg Subtype.val he
      have h' := congrArg Subtype.val hdr
      have ho : e.val.val.2 = d.val.val.1 := by
        have ho0 := heq
        simp only [FiniteGraph.other, he, hd, ↓reduceIte] at ho0
        simpa only [bondLeft, bondRight] using ho0
      have hp := bond_positive e.val
      have hp' := bond_positive d.val
      change e.val.val.1 = x.val at h
      change d.val.val.2 = x.val at h'
      rw [h] at hp
      rw [h', ← ho] at hp'
      omega
  · have her : bondRight D e.val = x := e.property.resolve_left he
    by_cases hd : bondLeft D d.val = x
    · have h := congrArg Subtype.val her
      have h' := congrArg Subtype.val hd
      have ho : e.val.val.1 = d.val.val.2 := by
        have ho0 := heq
        simp only [FiniteGraph.other, he, hd, ↓reduceIte] at ho0
        simpa only [bondLeft, bondRight] using ho0
      have hp := bond_positive e.val
      have hp' := bond_positive d.val
      change e.val.val.2 = x.val at h
      change d.val.val.1 = x.val at h'
      rw [h] at hp
      rw [h', ← ho] at hp'
      omega
    · have hdr : bondRight D d.val = x := d.property.resolve_left hd
      have h := congrArg Subtype.val her
      have h' := congrArg Subtype.val hdr
      have ho : e.val.val.1 = d.val.val.1 := by
        have ho0 := heq
        simp only [FiniteGraph.other, he, hd, ↓reduceIte] at ho0
        simpa only [bondLeft, bondRight] using ho0
      exact Prod.ext ho (h.trans h'.symm)

theorem incident_card_le {G : Finset Plane} (D : Network G)
    (hkept : ∀ z, D.kept z ⊆ neighbours z ∩ G) (x : D.active) :
    Fintype.card {e : D.bonds // FiniteGraph.Inc (bondLeft D) (bondRight D) x e} ≤
      (D.presentNeighbours x).card := by
  classical
  let f : {e : D.bonds // FiniteGraph.Inc (bondLeft D) (bondRight D) x e} →
      D.presentNeighbours x := fun e => ⟨(FiniteGraph.other (bondLeft D) (bondRight D) x e.val).val, by
        have hp := bond_present e.val
        by_cases he : bondLeft D e.val = x
        · have h := congrArg Subtype.val he
          change e.val.val.1 = x.val at h
          rw [h] at hp
          simp only [FiniteGraph.other, he, ↓reduceIte]
          exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp (hkept _ hp.2.2.2.1)).1, hp⟩
        · have hr := e.property.resolve_left he
          have h := congrArg Subtype.val hr
          change e.val.val.2 = x.val at h
          rw [h] at hp
          have hp := present_symm hp
          simp only [FiniteGraph.other, he, ↓reduceIte]
          exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp (hkept _ hp.2.2.2.1)).1, hp⟩⟩
  have hi : Function.Injective f := by
    intro e d h
    apply incident_other_injective D x
    exact congrArg (fun z : D.presentNeighbours x => z.val) h
  simpa using Fintype.card_le_of_injective f hi

theorem bond_separate {G : Finset Plane} (D : Network G) {x y : D.active}
    (hxy : x ≠ y) (hnot : ¬Adjacent x.val y.val) :
    ∀ e, FiniteGraph.Inc (bondLeft D) (bondRight D) x e →
      ¬FiniteGraph.Inc (bondLeft D) (bondRight D) y e := by
  intro e hx hy
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · exact hxy (hx.symm.trans hy)
  · have hp := (bond_present e).2.2.1
    have hx := congrArg Subtype.val hx
    have hy := congrArg Subtype.val hy
    change e.val.1 = x.val at hx
    change e.val.2 = y.val at hy
    rw [hx, hy] at hp
    exact hnot hp
  · have hp := adjacent_symm (bond_present e).2.2.1
    have hx := congrArg Subtype.val hx
    have hy := congrArg Subtype.val hy
    change e.val.2 = x.val at hx
    change e.val.1 = y.val at hy
    rw [hx, hy] at hp
    exact hnot hp
  · exact hxy (hx.symm.trans hy)

theorem active_status {G : Finset Plane} (D : Network G) (x : D.active) :
    D.status x = .U ∨ D.status x = .D := by
  have h := (Finset.mem_filter.mp x.property).2
  cases hs : D.status x <;> simp_all

#print axioms partition_nonneg
#print axioms incident_card_le

end AKLT.W.REC016
