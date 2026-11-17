module
public import AKLT.W.REC005.Graph
public import AKLT.W.REC005.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

set_option maxHeartbeats 1000000
set_option maxRecDepth 2000

namespace AKLT.W.REC005

lemma bond_present {G : Finset Plane} (D : Network G) (e : D.bonds) :
    D.Present e.val.1 e.val.2 := (Finset.mem_filter.mp e.property).2

def netL {G : Finset Plane} (D : Network G) (e : D.bonds) : D.active :=
  ⟨e.val.1, (bond_present D e).1⟩

def netR {G : Finset Plane} (D : Network G) (e : D.bonds) : D.active :=
  ⟨e.val.2, (bond_present D e).2.1⟩

lemma bond_increases {G : Finset Plane} (D : Network G) (e : D.bonds) :
    e.val.1.1 + e.val.1.2 < e.val.2.1 + e.val.2.2 := by
  have h := (Finset.mem_filter.mp e.property).1
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image, Finset.mem_inter] at h
  obtain ⟨u, _, v, hv, he⟩ := h
  have hp := hv.1
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hp
  rw [← he]
  rcases hp with rfl | rfl <;> simp

lemma net_no_loop {G : Finset Plane} (D : Network G) (e : D.bonds) : netL D e ≠ netR D e := by
  intro he
  have hv : e.val.1 = e.val.2 := congrArg Subtype.val he
  have h := bond_increases D e
  rw [hv] at h
  exact lt_irrefl _ h

lemma other_injective {G : Finset Plane} (D : Network G) (x : D.active) :
    Set.InjOn (fun e : D.bonds => (otherEnd (netL D) (netR D) x e).val)
      (↑(incident (netL D) (netR D) x) : Set D.bonds) := by
  intro e he f hf h
  have hei : netL D e = x ∨ netR D e = x := by simpa [incident] using he
  have hfi : netL D f = x ∨ netR D f = x := by simpa [incident] using hf
  have hranke := bond_increases D e
  have hrankf := bond_increases D f
  rcases hei with heL | heR
  · rcases hfi with hfL | hfR
    · have hL : e.val.1 = f.val.1 := congrArg Subtype.val (heL.trans hfL.symm)
      have hR : e.val.2 = f.val.2 := by
        simp only [otherEnd, heL, hfL, ↓reduceIte] at h
        simpa only [netL, netR] using h
      exact Subtype.ext (Prod.ext hL hR)
    · have hfL : netL D f ≠ x := by
        intro hfL
        exact net_no_loop D f (hfL.trans hfR.symm)
      have hLR : e.val.1 = f.val.2 := congrArg Subtype.val (heL.trans hfR.symm)
      have hRL : e.val.2 = f.val.1 := by
        simp only [otherEnd, heL, hfL, ↓reduceIte] at h
        simpa only [netL, netR] using h
      rw [hLR, hRL] at hranke
      omega
  · have heL : netL D e ≠ x := by
      intro heL
      exact net_no_loop D e (heL.trans heR.symm)
    rcases hfi with hfL | hfR
    · have hRL : e.val.2 = f.val.1 := congrArg Subtype.val (heR.trans hfL.symm)
      have hLR : e.val.1 = f.val.2 := by
        simp only [otherEnd, heL, hfL, ↓reduceIte] at h
        simpa only [netL, netR] using h
      rw [hLR, hRL] at hranke
      omega
    · have hfL : netL D f ≠ x := by
        intro hfL
        exact net_no_loop D f (hfL.trans hfR.symm)
      have hR : e.val.2 = f.val.2 := congrArg Subtype.val (heR.trans hfR.symm)
      have hL : e.val.1 = f.val.1 := by
        simp only [otherEnd, heL, hfL, ↓reduceIte] at h
        simpa only [netL, netR] using h
      exact Subtype.ext (Prod.ext hL hR)

lemma other_neighbour {G : Finset Plane} (D : Network G) (x : D.active) (e : D.bonds)
    (he : e ∈ incident (netL D) (netR D) x) :
    (otherEnd (netL D) (netR D) x e).val ∈ neighbours x.val := by
  have hei : netL D e = x ∨ netR D e = x := by simpa [incident] using he
  have hadj := (bond_present D e).2.2.1
  change Adjacent (netL D e).val (netR D e).val at hadj
  by_cases heL : netL D e = x
  · rw [heL] at hadj
    simpa [otherEnd, heL] using adjacent_mem_neighbours _ _ hadj
  · have heR := hei.resolve_left heL
    rw [heR] at hadj
    have hsym : Adjacent x.val (netL D e).val := by
      unfold Adjacent at *
      rw [dist_symm]
      exact hadj
    simpa [otherEnd, heL] using adjacent_mem_neighbours _ _ hsym

lemma net_degree_le_three {G : Finset Plane} (D : Network G) (x : D.active)
    (y : Plane) (hy : y ∉ D.active) (hx : x.val ∈ neighbours y) :
    (incident (netL D) (netR D) x).card ≤ 3 := by
  classical
  have hcard : (incident (netL D) (netR D) x).card ≤ ((neighbours x.val).erase y).card := by
    apply Finset.card_le_card_of_injOn (fun e : D.bonds => (otherEnd (netL D) (netR D) x e).val)
    · intro e he
      apply Finset.mem_erase.mpr
      refine ⟨?_, other_neighbour D x e he⟩
      intro h
      apply hy
      rw [← h]
      exact (otherEnd (netL D) (netR D) x e).property
    · exact other_injective D x
  have hymem : y ∈ neighbours x.val := by
    apply adjacent_mem_neighbours
    unfold Adjacent
    rw [dist_symm]
    exact neighbour_dist _ _ hx
  rw [Finset.card_erase_of_mem hymem, neighbour_card] at hcard
  exact hcard

def netPins {G : Finset Plane} (D : Network G) (τ : PinAssignment G) (pinned : Bool)
    (σ : D.active → SpinLetter) : ℝ :=
  ∏ e : originalLegs G,
    if pinned = true ∧ e.val.1 ∈ D.active then 1 + dot (τ e).val (D.spins σ e.val.1) else 1

lemma spins_norm_le {G : Finset Plane} (D : Network G) (σ : D.active → SpinLetter) (x : Plane) :
    normSq (D.spins σ x) ≤ 1 := by
  unfold Network.spins
  split_ifs
  · exact spin_norm_le _
  · simp [normSq, dot]

lemma netPins_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (σ : D.active → SpinLetter) : 0 ≤ netPins D τ pinned σ := by
  apply Finset.prod_nonneg
  intro e _
  split_ifs
  · have h := dot_ball_bounds (τ e).val (D.spins σ e.val.1) (τ e).property.le (spins_norm_le D σ _)
    linarith
  · norm_num

lemma spins_updatePair {G : Finset Plane} (D : Network G) (x y : D.active)
    (σ : D.active → SpinLetter) (a b : SpinLetter) (z : Plane)
    (hzx : z ≠ x.val) (hzy : z ≠ y.val) :
    D.spins (updatePair x y σ a b) z = D.spins σ z := by
  unfold Network.spins
  split_ifs with hz
  · have hix : (⟨z, hz⟩ : D.active) ≠ x := by intro h; exact hzx (congrArg Subtype.val h)
    have hiy : (⟨z, hz⟩ : D.active) ≠ y := by intro h; exact hzy (congrArg Subtype.val h)
    simp [updatePair, hix, hiy]
  · rfl

lemma netPins_fixed {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (x y : D.active)
    (hx : ∀ e ∈ originalLegs G, e.1 ≠ x.val) (hy : ∀ e ∈ originalLegs G, e.1 ≠ y.val)
    (σ : D.active → SpinLetter) (a b : SpinLetter) :
    netPins D τ pinned (updatePair x y σ a b) = netPins D τ pinned σ := by
  apply Finset.prod_congr rfl
  intro e _
  rw [spins_updatePair D x y σ a b e.val.1 (hx e e.property) (hy e e.property)]

lemma partition_graph {G : Finset Plane} (D : Network G) (τ : PinAssignment G) (pinned : Bool)
    (f : (Plane → Vec3) → ℝ) :
    D.partition τ pinned f = ∑ σ : D.active → SpinLetter,
      graphWeight (fun x : D.active => D.status x) (netL D) (netR D) (netPins D τ pinned) σ *
        f (D.spins σ) := by
  classical
  have hb (σ : D.active → SpinLetter) :
      (∏ e ∈ D.bonds, (1 + dot (D.spins σ e.1) (D.spins σ e.2))) =
      ∏ e : D.bonds, (1 + dot (spinVector (σ (netL D e))) (spinVector (σ (netR D e)))) := by
    have hc (e : D.bonds) :
        (1 + dot (D.spins σ e.val.1) (D.spins σ e.val.2)) =
          1 + dot (spinVector (σ (netL D e))) (spinVector (σ (netR D e))) := by
      unfold Network.spins
      rw [dite_eq_left (bond_present D e).1, dite_eq_left (bond_present D e).2.1]
      rfl
    rw [Finset.prod_coe_sort_eq_attach]
    simp_rw [← hc]
    exact (Finset.prod_attach D.bonds (fun e => 1 + dot (D.spins σ e.1) (D.spins σ e.2))).symm
  unfold Network.partition graphWeight netPins
  simp_rw [hb]
  apply Finset.sum_congr rfl
  intro σ _
  ring

lemma spins_at {G : Finset Plane} (D : Network G) (σ : D.active → SpinLetter) (x : D.active) :
    D.spins σ x.val = spinVector (σ x) := by
  simp [Network.spins, x.property]

lemma network_pair_bound {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (pinned : Bool) (x y : D.active) (hxy : x ≠ y)
    (hnonadj : ¬ Adjacent x.val y.val)
    (hlegx : ∀ e ∈ originalLegs G, e.1 ≠ x.val)
    (hlegy : ∀ e ∈ originalLegs G, e.1 ≠ y.val)
    (hdegx : (incident (netL D) (netR D) x).card ≤ 3)
    (hdegy : (incident (netL D) (netR D) y).card ≤ 3) :
    -(9 / 25 : ℝ) ≤ D.expectation τ pinned (fun n => dot (n x.val) (n y.val)) ∧
      D.expectation τ pinned (fun n => dot (n x.val) (n y.val)) ≤ 9 / 25 := by
  have hcross (e : D.bonds) :
      ¬ (netL D e = x ∧ netR D e = y) ∧ ¬ (netL D e = y ∧ netR D e = x) := by
    have ha := (bond_present D e).2.2.1
    change Adjacent (netL D e).val (netR D e).val at ha
    constructor
    · rintro ⟨hl, hr⟩
      rw [hl, hr] at ha
      exact hnonadj ha
    · rintro ⟨hl, hr⟩
      rw [hl, hr] at ha
      apply hnonadj
      unfold Adjacent at *
      rw [dist_symm]
      exact ha
  have hf := graph_fibre_reduction (fun x : D.active => D.status x) (netL D) (netR D)
    (netPins D τ pinned) (netPins_nonneg D τ pinned) x y hxy (net_no_loop D) hcross
    hdegx hdegy (netPins_fixed D τ pinned x y hlegx hlegy)
  have h := pair_bound_of_fibres
    (graphWeight (fun x : D.active => D.status x) (netL D) (netR D) (netPins D τ pinned))
    x y hxy (D.status x) (D.status y) hf
  unfold Network.expectation
  rw [partition_graph, partition_graph]
  simpa only [spins_at, mul_one] using h

/-- Two distinct neighbors of an interior departure have bounded correlation
in the departure-deleted network, for either choice of pins. -/
theorem removed_pair_bound {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y a b : Plane) (hy : y ∈ D.active) (hp : y ∉ protectedSites G)
    (ha : a ∈ D.presentNeighbours y) (hb : b ∈ D.presentNeighbours y) (hab : a ≠ b)
    (pinned : Bool) :
    -(9 / 25 : ℝ) ≤ removedPairMean D τ pinned y a b ∧
      removedPairMean D τ pinned y a b ≤ 9 / 25 := by
  have hNa := (present_mem_active D ha).2.2
  have hNb := (present_mem_active D hb).2.2
  have hay : a ≠ y := by
    intro h
    have hd := neighbour_dist y a hNa
    rw [h] at hd
    simpa [latticeDist] using hd
  have hby : b ≠ y := by
    intro h
    have hd := neighbour_dist y b hNb
    rw [h] at hd
    simpa [latticeDist] using hd
  let E := removeSite D y
  have haE : a ∈ E.active := by
    rw [removed_active]
    exact Finset.mem_erase.mpr ⟨hay, (present_mem_active D ha).2.1⟩
  have hbE : b ∈ E.active := by
    rw [removed_active]
    exact Finset.mem_erase.mpr ⟨hby, (present_mem_active D hb).2.1⟩
  let x : E.active := ⟨a, haE⟩
  let z : E.active := ⟨b, hbE⟩
  have hxz : x ≠ z := by intro h; exact hab (congrArg Subtype.val h)
  have hyE : y ∉ E.active := by rw [removed_active]; simp
  exact network_pair_bound E τ pinned x z hxz (neighbours_nonadjacent y a b hNa hNb)
    (no_neighbour_legs D y a hy hp hNa) (no_neighbour_legs D y b hy hp hNb)
    (net_degree_le_three E x y hyE hNa) (net_degree_le_three E z y hyE hNb)

end AKLT.W.REC005
