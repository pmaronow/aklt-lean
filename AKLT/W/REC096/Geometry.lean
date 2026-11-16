import AKLT.Blueprint.Rec.NodesV2Closure

noncomputable section
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC096

theorem natAbs_sub_comm (a b : ℤ) : (a - b).natAbs = (b - a).natAbs := by
  simpa using Int.natAbs_neg (b - a)

theorem natAbs_neg_add (a b : ℤ) : (-a + b).natAbs = (a - b).natAbs := by
  rw [show -a + b = -(a - b) by omega, Int.natAbs_neg]

theorem step_injective : Function.Injective Compass.step := by
  intro a b h
  cases a <;> cases b <;> simp_all [Compass.step]

theorem neighbours_card (x : Plane) : (neighbours x).card = 4 := by
  rw [neighbours, Finset.card_image_of_injective _
    (fun _ _ h => step_injective (add_left_cancel h))]
  rfl

theorem adjacent_iff (x z : Plane) :
    Adjacent x z ↔ z ∈ neighbours x := by
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rcases x with ⟨a, b⟩
    rcases z with ⟨c, d⟩
    intro h
    change (a - c).natAbs + (b - d).natAbs = 1 at h
    have hs : ((a - c).natAbs = 0 ∧ (b - d).natAbs = 1) ∨
        ((a - c).natAbs = 1 ∧ (b - d).natAbs = 0) := by omega
    simp only [Int.natAbs_eq_iff] at hs
    rcases hs with ⟨ha, hb | hb⟩ | ⟨ha | ha, hb⟩
    · exact ⟨.south, by ext <;> simp [Compass.step] <;> omega⟩
    · exact ⟨.north, by ext <;> simp [Compass.step] <;> omega⟩
    · exact ⟨.west, by ext <;> simp [Compass.step] <;> omega⟩
    · exact ⟨.east, by ext <;> simp [Compass.step] <;> omega⟩
  · rintro ⟨d, rfl⟩
    cases d <;> simp [Adjacent, latticeDist, Compass.step]

theorem adjacent_symm {x z : Plane} (h : Adjacent x z) : Adjacent z x := by
  simpa only [Adjacent, latticeDist, natAbs_sub_comm] using h

theorem adjacent_ne {x z : Plane} (h : Adjacent x z) : x ≠ z := by
  rintro rfl
  simp [Adjacent, latticeDist] at h

theorem step_adjacent (x : Plane) (d : Compass) : Adjacent x (x + d.step) := by
  rw [adjacent_iff]
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩

def chart (y : Plane) (d : Compass) : Plane ≃ Plane where
  toFun z := y + normalizeRotation d z
  invFun z := match d with
    | .north => z - y
    | .east => (-(z - y).2, (z - y).1)
    | .south => (-(z - y).1, -(z - y).2)
    | .west => ((z - y).2, -(z - y).1)
  left_inv z := by cases d <;> ext <;> simp [normalizeRotation]
  right_inv z := by cases d <;> ext <;> simp [normalizeRotation]

@[simp] theorem chart_apply (y : Plane) (d : Compass) (z : Plane) :
    chart y d z = y + normalizeRotation d z := rfl

@[simp] theorem chart_zero (y : Plane) (d : Compass) : chart y d (0, 0) = y := by
  cases d <;> simp [normalizeRotation]

@[simp] theorem chart_south (y : Plane) (d : Compass) :
    chart y d (0, -1) = y - d.step := by
  cases d <;> ext <;> simp [normalizeRotation, Compass.step] <;> omega

theorem chart_dist (y x z : Plane) (d : Compass) :
    latticeDist (chart y d x) (chart y d z) = latticeDist x z := by
  cases d <;> simp [latticeDist, normalizeRotation, natAbs_neg_add,
    Nat.add_comm]

theorem chart_adjacent (y x z : Plane) (d : Compass) :
    Adjacent (chart y d x) (chart y d z) ↔ Adjacent x z := by
  unfold Adjacent
  rw [chart_dist]

theorem chart_neighbours (y x : Plane) (d : Compass) :
    (neighbours x).image (chart y d) = neighbours (chart y d x) := by
  ext z
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (adjacent_iff _ _).mp ((chart_adjacent _ _ _ _).mpr ((adjacent_iff _ _).mpr ht))
  · intro hz
    refine ⟨(chart y d).symm z, ?_, by simp⟩
    rw [← adjacent_iff, ← chart_adjacent y x _ d]
    simpa using (adjacent_iff _ _).mpr hz

theorem interior_ball {G : Finset Plane} {y : Plane}
    (hy : y ∈ G) (hS : y ∉ protectedSites G) {z : Plane}
    (hz : latticeDist y z ≤ 2) : z ∈ G := by
  classical
  by_contra hout
  apply hS
  simp only [protectedSites, Finset.mem_filter]
  refine ⟨hy, ?_⟩
  have hle : boundaryDepth G y ≤ (latticeDist y z : ℕ∞) :=
    iInf_le_of_le ⟨z, hout⟩ le_rfl
  exact hle.trans (by exact_mod_cast hz)

theorem template_dist {z : Plane} (hz : z ∈ templateSites) :
    latticeDist (0, 0) z ≤ 2 := by
  have := (Finset.mem_filter.mp hz).2
  simpa only [latticeDist, natAbs_sub_comm] using this

theorem template_interior {G : Finset Plane} {y : Plane}
    (hy : y ∈ G) (hS : y ∉ protectedSites G) (d : Compass)
    {z : Plane} (hz : z ∈ templateSites) : chart y d z ∈ G := by
  apply interior_ball hy hS
  have := chart_dist y (0, 0) z d
  rw [chart_zero] at this
  rw [this]
  exact template_dist hz

end AKLT.W.REC096
