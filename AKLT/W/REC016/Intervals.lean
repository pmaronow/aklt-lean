module
public import AKLT.W.REC016.Bridge

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Rec (Departure responseI₂)

namespace AKLT.W.REC016

theorem neighbor_survives {G : Finset Plane} (D : Network G) {y x : Plane}
    (hx : x ∈ D.presentNeighbors y) : x ∈ (removeSite D y).active := by
  have hp := (Finset.mem_filter.mp hx).2
  apply (removed_active D y x).2
  refine ⟨hp.2.1, ?_⟩
  intro h
  have hA := hp.2.2.1
  rw [h] at hA
  simpa [Adjacent, latticeDist] using hA

theorem network_pair_lower {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (x y : D.active) (hxy : x ≠ y) (hnonadj : ¬Adjacent x.val y.val)
    (hxdeg : Fintype.card {e : D.bonds //
      FiniteGraph.Inc (bondLeft D) (bondRight D) x e} ≤ 3)
    (hydeg : Fintype.card {e : D.bonds //
      FiniteGraph.Inc (bondLeft D) (bondRight D) y e} ≤ 3)
    (hxleg : ∀ e : originalLegs G, e.val.1 ≠ x.val)
    (hyleg : ∀ e : originalLegs G, e.val.1 ≠ y.val) :
    -(9 / 25 : ℝ) ≤ D.expectation τ b (fun v => dot (v x.val) (v y.val)) := by
  classical
  have h := FiniteGraph.pair_lower (fun z : D.active => D.status z)
    (bondLeft D) (bondRight D) (bond_no_loop) hxy (bond_separate D hxy hnonadj)
    hxdeg hydeg (active_status D x) (active_status D y) (legWeight D τ b)
    (legWeight_nonneg D τ b) (legWeight_refresh D τ b x y hxleg hyleg)
  unfold Network.expectation
  rw [partition_graph, partition_graph]
  simpa only [spins_at, mul_one] using h

theorem removed_pair_lower (a : Departure) {x z : Plane}
    (hx : x ∈ a.D.presentNeighbors a.y) (hz : z ∈ a.D.presentNeighbors a.y)
    (hxz : x ≠ z) (b : Bool) :
    -(9 / 25 : ℝ) ≤ removedPairMean a.D a.τ b a.y x z := by
  classical
  let E := removeSite a.D a.y
  let X : E.active := ⟨x, neighbor_survives a.D hx⟩
  let Z : E.active := ⟨z, neighbor_survives a.D hz⟩
  have hXZ : X ≠ Z := fun h => hxz (congrArg Subtype.val h)
  have hxN := (Finset.mem_filter.mp hx).1
  have hzN := (Finset.mem_filter.mp hz).1
  have hkept : ∀ v, E.kept v ⊆ neighbors v ∩ a.G := a.auxiliary.1.2.1
  have hdx : Fintype.card {e : E.bonds //
      FiniteGraph.Inc (bondLeft E) (bondRight E) X e} ≤ 3 :=
    (incident_card_le E hkept X).trans (removed_degree a.auxiliary.1 hx)
  have hdz : Fintype.card {e : E.bonds //
      FiniteGraph.Inc (bondLeft E) (bondRight E) Z e} ≤ 3 :=
    (incident_card_le E hkept Z).trans (removed_degree a.auxiliary.1 hz)
  exact network_pair_lower E a.τ b X Z hXZ (neighbors_nonadjacent hxN hzN) hdx hdz
    (fun e => neighbor_no_leg a.start hxN e.val e.property)
    (fun e => neighbor_no_leg a.start hzN e.val e.property)

theorem removed_pair_free_nonneg (a : Departure) {x z : Plane}
    (hx : x ∈ a.D.presentNeighbors a.y) (hz : z ∈ a.D.presentNeighbors a.y) :
    0 ≤ removedPairMean a.D a.τ false a.y x z := by
  let E := removeSite a.D a.y
  let X : E.active := ⟨x, neighbor_survives a.D hx⟩
  let Z : E.active := ⟨z, neighbor_survives a.D hz⟩
  exact div_nonneg (free_pair_nonneg E a.τ X Z) (partition_nonneg E a.τ false)

theorem two_mean_lower (a : Departure) (f : Plane)
    (hPresent : a.D.presentNeighbors a.y = {a.o, f}) (hne : a.o ≠ f) :
    (22 / 25 : ℝ) ≤ responseI₂ a.D a.τ true a.y a.o f ∧
      1 ≤ responseI₂ a.D a.τ false a.y a.o f := by
  have hf : f ∈ a.D.presentNeighbors a.y := by simp [hPresent]
  have ho : a.o ∈ a.D.presentNeighbors a.y := a.present
  have htrue := removed_pair_lower a hf ho hne.symm true
  have hfalse := removed_pair_free_nonneg a hf ho
  dsimp only [responseI₂]
  constructor <;> linarith

#print axioms two_mean_lower

end AKLT.W.REC016
