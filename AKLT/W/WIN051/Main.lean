module
public import AKLT.Blueprint.Win.NodesRemoval

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN051

private lemma latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  have h₁ := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
  have h₂ := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
  have h₁' : (x.1 - z.1).natAbs ≤ (x.1 - y.1).natAbs + (y.1 - z.1).natAbs := by
    rw [show (x.1 - y.1) + (y.1 - z.1) = x.1 - z.1 by ring] at h₁
    exact h₁
  have h₂' : (x.2 - z.2).natAbs ≤ (x.2 - y.2).natAbs + (y.2 - z.2).natAbs := by
    rw [show (x.2 - y.2) + (y.2 - z.2) = x.2 - z.2 by ring] at h₂
    exact h₂
  unfold latticeDist at *
  omega

private lemma neighbors_card (x : Plane) : (neighbors x).card = 4 := by
  have hinj : Function.Injective (fun d : Compass => x + d.step) := by
    intro d e h
    cases d <;> cases e <;> simp [Compass.step] at h ⊢
  unfold neighbors
  rw [Finset.card_image_of_injective _ hinj]
  have hcard : Fintype.card Compass = 4 := by decide
  simp [hcard]

private lemma adjacent_of_mem_neighbors {x z : Plane} (hz : z ∈ neighbors x) :
    Adjacent x z := by
  rcases Finset.mem_image.mp hz with ⟨d, -, rfl⟩
  cases d <;> simp [Adjacent, latticeDist, Compass.step]

private lemma mem_neighbors_of_adjacent {x z : Plane} (h : Adjacent x z) :
    z ∈ neighbors x := by
  simp only [neighbors, Finset.mem_image, Finset.mem_univ, true_and]
  unfold Adjacent latticeDist at h
  have h₁ : (x.1 - z.1).natAbs = 0 ∨ (x.1 - z.1).natAbs = 1 := by omega
  have h₂ : (x.2 - z.2).natAbs = 0 ∨ (x.2 - z.2).natAbs = 1 := by omega
  have hcoord₁ : x.1 - z.1 = 0 ∨ x.1 - z.1 = 1 ∨ x.1 - z.1 = -1 := by
    rcases h₁ with h₁ | h₁
    · rcases Int.natAbs_eq (x.1 - z.1) with h | h <;> rw [h₁] at h <;> omega
    · rcases Int.natAbs_eq (x.1 - z.1) with h | h <;> rw [h₁] at h <;> omega
  have hcoord₂ : x.2 - z.2 = 0 ∨ x.2 - z.2 = 1 ∨ x.2 - z.2 = -1 := by
    rcases h₂ with h₂ | h₂
    · rcases Int.natAbs_eq (x.2 - z.2) with h | h <;> rw [h₂] at h <;> omega
    · rcases Int.natAbs_eq (x.2 - z.2) with h | h <;> rw [h₂] at h <;> omega
  rcases hcoord₁ with h₁ | h₁ | h₁ <;> rcases hcoord₂ with h₂ | h₂ | h₂
  all_goals
    first
    | (refine ⟨Compass.east, ?_⟩; apply Prod.ext <;> simp [Compass.step] <;> omega)
    | (refine ⟨Compass.west, ?_⟩; apply Prod.ext <;> simp [Compass.step] <;> omega)
    | (refine ⟨Compass.north, ?_⟩; apply Prod.ext <;> simp [Compass.step] <;> omega)
    | (refine ⟨Compass.south, ?_⟩; apply Prod.ext <;> simp [Compass.step] <;> omega)

private lemma neighbors_ne_self (x : Plane) : ∀ z ∈ neighbors x, z ≠ x := by
  intro z hz heq
  have hadj := adjacent_of_mem_neighbors hz
  subst z
  simp [Adjacent, latticeDist] at hadj

private lemma neighbors_pair_dist {x z w : Plane}
    (hz : z ∈ neighbors x) (hw : w ∈ neighbors x) (hzw : z ≠ w) :
    latticeDist z w = 2 := by
  rcases Finset.mem_image.mp hz with ⟨d, -, rfl⟩
  rcases Finset.mem_image.mp hw with ⟨e, -, rfl⟩
  cases d <;> cases e <;>
    (try simp_all [Compass.step, Prod.mk.injEq]) <;>
    (try ring_nf at *) <;> norm_num [latticeDist] at *

private lemma depth_ge_two_of_adjacent (G : Finset Plane) (x z : Plane)
    (hx : (3 : ℕ∞) ≤ boundaryDepth G x) (hxz : Adjacent x z) :
    (2 : ℕ∞) ≤ boundaryDepth G z := by
  rw [boundaryDepth, setDistance]
  apply le_iInf
  intro y
  have hx' : (3 : ℕ∞) ≤ ⨅ y : {q : Plane // q ∉ G}, (latticeDist x y.val : ℕ∞) := hx
  have hxy := (le_iInf_iff.mp hx') y
  have hxyN : 3 ≤ latticeDist x y.val := ENat.natCast_le_natCast.mp hxy
  have hxzN : latticeDist x z = 1 := hxz
  have htri := latticeDist_triangle x z y.val
  have hzy : 2 ≤ latticeDist z y.val := by omega
  exact_mod_cast hzy

private lemma all_neighbors_in_of_depth (G : Finset Plane) (x : Plane)
    (hx : (3 : ℕ∞) ≤ boundaryDepth G x) : ∀ z ∈ neighbors x, z ∈ G := by
  intro z hz
  by_contra hout
  have hle : boundaryDepth G x ≤ (latticeDist x z : ℕ∞) := by
    unfold boundaryDepth setDistance
    change (⨅ y : {q : Plane // q ∉ G}, (latticeDist x y.val : ℕ∞)) ≤ _
    exact iInf_le (fun y : {q : Plane // q ∉ G} => (latticeDist x y.val : ℕ∞)) ⟨z, hout⟩
  have hadj := adjacent_of_mem_neighbors hz
  have hdist : latticeDist x z = 1 := hadj
  have hle1 : boundaryDepth G x ≤ (1 : ℕ∞) := by simpa [hdist] using hle
  have hbad : (3 : ℕ∞) ≤ (1 : ℕ∞) := hx.trans hle1
  norm_num at hbad

/-- The frozen survivor-geometry leaf. -/
theorem main : AKLT.Blueprint.Win.SurvivorGeometryStatement := by
  intro G Y x hstep
  rcases hstep with ⟨_, _, hxdepth⟩
  have hdepth : (3 : ℕ∞) ≤ boundaryDepth G x := by exact_mod_cast hxdepth
  have hsub : survivors G Y x ⊆ neighbors x := by
    intro z hz
    exact (Finset.mem_inter.mp hz).1
  have hcard : (survivors G Y x).card ≤ 4 := by
    calc
      (survivors G Y x).card ≤ (neighbors x).card := Finset.card_le_card hsub
      _ = 4 := neighbors_card x
  refine ⟨hcard, ?_, ?_, ?_, ?_⟩
  · intro hY
    have hG : ∀ z ∈ neighbors x, z ∈ G := all_neighbors_in_of_depth G x hdepth
    have hne : ∀ z ∈ neighbors x, z ≠ x := neighbors_ne_self x
    have hs : survivors G Y x = neighbors x := by
      ext z
      simp only [survivors, Finset.mem_inter, Finset.mem_sdiff, hY,
        Finset.mem_insert, Finset.notMem_empty, or_false]
      constructor
      · rintro ⟨hz, _, _⟩
        exact hz
      · intro hz
        exact ⟨hz, hG z hz, hne z hz⟩
    rw [hs, neighbors_card]
  · rintro ⟨c, hcY, hxc⟩
    have hcn : c ∈ neighbors x := mem_neighbors_of_adjacent hxc
    have hsub' : survivors G Y x ⊆ (neighbors x).erase c := by
      intro z hz
      have hzN := (Finset.mem_inter.mp hz).1
      have hzrest := (Finset.mem_inter.mp hz).2
      apply Finset.mem_erase.mpr
      refine ⟨?_, hzN⟩
      intro hzc
      have hzY : z ∈ Y := by simpa [hzc] using hcY
      exact (Finset.mem_sdiff.mp hzrest).2 (Finset.mem_insert_of_mem hzY)
    calc
      (survivors G Y x).card ≤ ((neighbors x).erase c).card := Finset.card_le_card hsub'
      _ = 3 := by rw [Finset.card_erase_of_mem hcn, neighbors_card]
  · intro z hz
    have hzN := (Finset.mem_inter.mp hz).1
    have hxz := adjacent_of_mem_neighbors hzN
    exact depth_ge_two_of_adjacent G x z hdepth hxz
  · intro z hz w hw hzw
    exact neighbors_pair_dist (Finset.mem_inter.mp hz).1 (Finset.mem_inter.mp hw).1 hzw

#print axioms main

end AKLT.W.WIN051
