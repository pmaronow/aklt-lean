module
public import AKLT.Blueprint.Win.NodesTopology

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN027

private theorem joinedIn_mono {α : Type*} {R : α → α → Prop}
    {S T : Set α} {x y : α} (hST : S ⊆ T)
    (h : AKLT.Blueprint.Win.JoinedIn R S x y) :
    AKLT.Blueprint.Win.JoinedIn R T x y := by
  unfold AKLT.Blueprint.Win.JoinedIn at h ⊢
  induction h with
  | refl => exact .refl
  | tail hpath hstep ih =>
      exact .tail ih ⟨hST hstep.1, hST hstep.2.1, hstep.2.2⟩

private theorem cross_subset_thicken (X₀ : Finset Plane) {x : Plane}
    (hx : x ∈ X₀) : (↑(cross x) : Set Plane) ⊆ ↑(thicken X₀) := by
  intro z hz
  change z ∈ thicken X₀
  exact Finset.mem_biUnion.mpr ⟨x, hx, hz⟩

private theorem crossPathJoin (X₀ : Finset Plane)
    (hcross : ∀ x : Plane, ConnectedIn Adjacent (↑(cross x)))
    (hoverlap : ∀ x y : Plane, StarAdjacent x y →
      (cross x ∩ cross y).Nonempty) :
    ∀ {a b : Plane}, a ∈ X₀ → b ∈ X₀ →
      JoinedIn StarAdjacent (↑X₀) a b →
      ∀ z : Plane, z ∈ cross a → ∀ w : Plane, w ∈ cross b →
        JoinedIn Adjacent (↑(thicken X₀)) z w := by
  intro a b ha hb hab
  have hmain :
      (a ∈ X₀ → ∀ z : Plane, z ∈ cross a → ∀ w : Plane,
        w ∈ cross b → JoinedIn Adjacent (↑(thicken X₀)) z w) := by
    refine Relation.ReflTransGen.head_induction_on
      (motive := fun u (_ : JoinedIn StarAdjacent (↑X₀) u b) =>
        u ∈ X₀ → ∀ z : Plane, z ∈ cross u → ∀ w : Plane,
          w ∈ cross b → JoinedIn Adjacent (↑(thicken X₀)) z w)
      hab ?_ ?_
    · intro hu z hz w hw
      exact joinedIn_mono (cross_subset_thicken X₀ hu)
        ((hcross b).2 z hz w hw)
    · intro u v huv hpath ih hu z hz w hw
      have hqne : (cross u ∩ cross v).Nonempty := hoverlap u v huv.2.2
      let q : Plane := hqne.choose
      have hqmem : q ∈ cross u ∩ cross v := hqne.choose_spec
      have hqu : q ∈ cross u := (Finset.mem_inter.mp hqmem).1
      have hqv : q ∈ cross v := (Finset.mem_inter.mp hqmem).2
      have hfirst : JoinedIn Adjacent (↑(thicken X₀)) z q :=
        joinedIn_mono (cross_subset_thicken X₀ hu)
          ((hcross u).2 z hz q hqu)
      have hlast : JoinedIn Adjacent (↑(thicken X₀)) q w :=
        ih huv.2.1 q hqv w hw
      exact hfirst.trans hlast
  exact hmain ha

theorem main : AKLT.Blueprint.Win.CrossUnionStatement := by
  intro X₀ hcenters hcross hoverlap
  rcases hcenters.1 with ⟨a, ha⟩
  refine ⟨?_, ?_⟩
  · change (thicken X₀).Nonempty
    exact ⟨a, Finset.mem_biUnion.mpr ⟨a, ha, by simp [cross]⟩⟩
  · intro z hz w hw
    change z ∈ thicken X₀ at hz
    change w ∈ thicken X₀ at hw
    obtain ⟨x, hx, hzx⟩ := Finset.mem_biUnion.mp hz
    obtain ⟨y, hy, hwy⟩ := Finset.mem_biUnion.mp hw
    exact crossPathJoin X₀ hcross hoverlap hx hy
      (hcenters.2 x hx y hy) z hzx w hwy

end AKLT.W.WIN027

#print axioms AKLT.W.WIN027.main
