module
public import AKLT.Blueprint.Rec.NodesV2Closure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.W.REC098

theorem adjacent_iff (x z : Plane) : Adjacent x z ↔ z ∈ neighbours x := by
  rcases x with ⟨x₁, x₂⟩
  rcases z with ⟨z₁, z₂⟩
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · intro h
    have hd : (x₁ - z₁).natAbs + (x₂ - z₂).natAbs = 1 := h
    have hcases : (z₁ = x₁ + 1 ∧ z₂ = x₂) ∨ (z₁ = x₁ ∧ z₂ = x₂ + 1) ∨
        (z₁ = x₁ - 1 ∧ z₂ = x₂) ∨ (z₁ = x₁ ∧ z₂ = x₂ - 1) := by omega
    rcases hcases with h | h | h | h
    · exact ⟨.east, by ext <;> simp [Compass.step] <;> omega⟩
    · exact ⟨.north, by ext <;> simp [Compass.step] <;> omega⟩
    · exact ⟨.west, by ext <;> simp [Compass.step] <;> omega⟩
    · exact ⟨.south, by ext <;> simp [Compass.step] <;> omega⟩
  · rintro ⟨d, hd⟩
    rw [← hd]
    cases d <;> simp [Adjacent, latticeDist, Compass.step]

theorem adjacent_symm {x z : Plane} (h : Adjacent x z) : Adjacent z x := by
  unfold Adjacent latticeDist at *
  omega

theorem adjacent_ne {x z : Plane} (h : Adjacent x z) : x ≠ z := by
  rintro rfl
  simp [Adjacent, latticeDist] at h

theorem step_injective : Function.Injective Compass.step := by
  intro a b h
  cases a <;> cases b <;> simp_all [Compass.step]

theorem neighbours_card (x : Plane) : (neighbours x).card = 4 := by
  rw [neighbours, Finset.card_image_of_injective]
  · rfl
  · intro a b h
    exact step_injective (add_left_cancel h)

theorem interior_ball {G : Finset Plane} {y : Plane} (hyG : y ∈ G)
    (hyS : y ∉ protectedSites G) {z : Plane} (hz : latticeDist y z ≤ 2) : z ∈ G := by
  by_contra hzG
  apply hyS
  apply Finset.mem_filter.mpr
  refine ⟨hyG, ?_⟩
  exact le_trans (iInf_le_of_le ⟨z, hzG⟩ le_rfl) (by exact_mod_cast hz)

theorem interior_neighbours {G : Finset Plane} {y : Plane} (hyG : y ∈ G)
    (hyS : y ∉ protectedSites G) : neighbours y ∩ G = neighbours y := by
  apply Finset.inter_eq_left.mpr
  intro z hz
  exact interior_ball hyG hyS (by have := (adjacent_iff y z).mpr hz; unfold Adjacent at this; omega)

theorem wordVertex_zero {n : ℕ} (u : Plane) (w : DirectionWord n) :
    wordVertex u w 0 = u := by simp [wordVertex]

theorem wordVertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n) (j : ℕ) (hj : j < n) :
    wordVertex u w (j + 1) = wordVertex u w j + (w ⟨j, hj⟩).step := by
  have ht : ∀ k : Fin n,
      (if k.val < j + 1 then (w k).step else 0) =
      (if k.val < j then (w k).step else 0) +
      (if k = ⟨j, hj⟩ then (w k).step else 0) := by
    intro k
    by_cases hkj : k.val < j
    · have hne : k ≠ ⟨j, hj⟩ := by intro h; have hv : k.val = j := congrArg Fin.val h; omega
      simp [hkj, hne, show k.val < j + 1 by omega]
    · by_cases heq : k = ⟨j, hj⟩
      · subst k; simp
      · have hgt : ¬ k.val < j + 1 := by
          have : k.val ≠ j := by simpa [Fin.ext_iff] using heq
          omega
        simp [hkj, heq, hgt]
  simp only [wordVertex, ht, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true]
  abel

theorem wordVertex_adjacent {n : ℕ} (u : Plane) (w : DirectionWord n) (i : Fin n) :
    Adjacent (wordVertex u w i.val) (wordVertex u w (i.val + 1)) := by
  rw [wordVertex_succ u w i.val i.isLt, adjacent_iff]
  exact Finset.mem_image.mpr ⟨w i, Finset.mem_univ _, rfl⟩

end AKLT.W.REC098
