module
public import AKLT.Blueprint.Win.NodesRemoval

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN052

theorem dot_symm (a b : Vec3) : dot a b = dot b a := by
  exact Finset.sum_congr rfl (fun i _ => mul_comm (a i) (b i))

theorem neighbours_explicit (x : Plane) :
    neighbours x = {x + Compass.east.step, x + Compass.north.step,
      x + Compass.west.step, x + Compass.south.step} := by
  ext z
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨d, rfl⟩
    cases d <;> simp
  · simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (rfl | rfl | rfl | rfl)
    · exact ⟨.east, rfl⟩
    · exact ⟨.north, rfl⟩
    · exact ⟨.west, rfl⟩
    · exact ⟨.south, rfl⟩

theorem neighbour_ne (x : Plane) : x ∉ neighbours x := by
  simp [neighbours_explicit, Compass.step, Prod.ext_iff]

theorem neighbour_dist {x z : Plane} (hz : z ∈ neighbours x) : latticeDist x z = 1 := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hz
  cases d <;> simp [Compass.step, latticeDist]

theorem neighbours_in_volume {G : Finset Plane} {x : Plane}
    (hdepth : 3 ≤ boundaryDepth G x) : neighbours x ⊆ G := by
  intro z hz
  by_contra hnot
  have hle : boundaryDepth G x ≤ (latticeDist x z : ℕ∞) :=
    iInf_le (fun y : {z | z ∉ G} => (latticeDist x y.val : ℕ∞)) ⟨z, hnot⟩
  rw [neighbour_dist hz] at hle
  have : (3 : ℕ∞) ≤ 1 := hdepth.trans hle
  norm_num at this

theorem leg_source_ne {G : Finset Plane} {x : Plane}
    (hdepth : 3 ≤ boundaryDepth G x) (e : originalLegs G) : e.val.1 ≠ x := by
  have he := e.property
  obtain ⟨a, _, hab⟩ := Finset.mem_biUnion.mp he
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hab
  have hs : a = e.val.1 := congrArg Prod.fst heq
  have hzG := (Finset.mem_sdiff.mp hz).2
  intro h
  apply hzG
  apply neighbours_in_volume hdepth
  simpa only [hs, h] using (Finset.mem_sdiff.mp hz).1

theorem mem_bonds {D : Finset Plane} {a b : Plane} :
    (a, b) ∈ internalBonds D ↔ a ∈ D ∧ b ∈ D ∧ b ∈ positiveNeighbours a := by
  simp [internalBonds, Finset.mem_biUnion, and_comm, and_left_comm, and_assoc]

theorem neighbour_orientation (x z : Plane) :
    z ∈ neighbours x ↔ z ∈ positiveNeighbours x ∨ x ∈ positiveNeighbours z := by
  rcases x with ⟨a, b⟩
  rcases z with ⟨c, d⟩
  simp [neighbours_explicit, positiveNeighbours, Compass.step, Prod.ext_iff]
  omega

theorem orientation_exclusive (x z : Plane) :
    z ∈ positiveNeighbours x → x ∉ positiveNeighbours z := by
  rcases x with ⟨a, b⟩
  rcases z with ⟨c, d⟩
  simp [positiveNeighbours, Prod.ext_iff]
  omega

def edgeAt (x z : Plane) : Plane × Plane :=
  if z ∈ positiveNeighbours x then (x, z) else (z, x)

theorem edgeAt_injective (x : Plane) : Function.Injective (edgeAt x) := by
  intro a b h
  unfold edgeAt at h
  split_ifs at h <;> simp only [Prod.mk.injEq] at h <;> grind

theorem edgeAt_bond {E : Finset Plane} {x z : Plane}
    (hz : z ∈ neighbours x ∩ E) : edgeAt x z ∈ internalBonds (insert x E) := by
  rcases Finset.mem_inter.mp hz with ⟨hzn, hzE⟩
  unfold edgeAt
  split_ifs with h
  · exact mem_bonds.mpr ⟨by simp, by simp [hzE], h⟩
  · exact mem_bonds.mpr ⟨by simp [hzE], by simp,
      (neighbour_orientation x z).mp hzn |>.resolve_left h⟩

theorem bonds_insert {E : Finset Plane} {x : Plane} (_hx : x ∉ E) :
    internalBonds (insert x E) =
      internalBonds E ∪ (neighbours x ∩ E).image (edgeAt x) := by
  ext e
  rcases e with ⟨a, b⟩
  constructor
  · intro he
    rcases mem_bonds.mp he with ⟨ha, hb, hab⟩
    by_cases hax : a = x
    · subst a
      have hbx : b ≠ x := by
        intro h
        subst b
        exact neighbour_ne x ((neighbour_orientation x x).mpr (Or.inl hab))
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨b, Finset.mem_inter.mpr ⟨(neighbour_orientation x b).mpr (.inl hab),
        (Finset.mem_insert.mp hb).resolve_left hbx⟩, ?_⟩
      simp [edgeAt, hab]
    · by_cases hbx : b = x
      · subst b
        apply Finset.mem_union_right
        apply Finset.mem_image.mpr
        refine ⟨a, Finset.mem_inter.mpr ⟨(neighbour_orientation x a).mpr (.inr hab),
          (Finset.mem_insert.mp ha).resolve_left hax⟩, ?_⟩
        simp [edgeAt, orientation_exclusive a x hab]
      · exact Finset.mem_union_left _ (mem_bonds.mpr
          ⟨(Finset.mem_insert.mp ha).resolve_left hax,
           (Finset.mem_insert.mp hb).resolve_left hbx, hab⟩)
  · intro he
    rcases Finset.mem_union.mp he with he | he
    · rcases mem_bonds.mp he with ⟨ha, hb, hab⟩
      exact mem_bonds.mpr ⟨by simp [ha], by simp [hb], hab⟩
    · obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp he
      rw [← heq]
      exact edgeAt_bond hz

theorem bonds_insert_disjoint {E : Finset Plane} {x : Plane} (hx : x ∉ E) :
    Disjoint (internalBonds E) ((neighbours x ∩ E).image (edgeAt x)) := by
  apply Finset.disjoint_left.mpr
  intro e he hinc
  obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hinc
  unfold edgeAt at he
  split_ifs at he
  · exact hx (mem_bonds.mp he).1
  · exact hx (mem_bonds.mp he).2.1

theorem bondProduct_insert {E : Finset Plane} {x : Plane} (hx : x ∉ E)
    (n : Plane → Vec3) :
    (∏ e ∈ internalBonds (insert x E), (1 + dot (n e.1) (n e.2))) =
      (∏ e ∈ internalBonds E, (1 + dot (n e.1) (n e.2))) *
      ∏ z ∈ neighbours x ∩ E, (1 + dot (n x) (n z)) := by
  rw [bonds_insert hx, Finset.prod_union (bonds_insert_disjoint hx),
    Finset.prod_image (edgeAt_injective x).injOn]
  congr 1
  apply Finset.prod_congr rfl
  intro z _
  unfold edgeAt
  split_ifs
  · rfl
  · exact congrArg (1 + ·) (dot_symm _ _)

end AKLT.W.WIN052
