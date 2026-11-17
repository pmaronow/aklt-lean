module
public import AKLT.Blueprint.Win.NodesTopology

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN026

open AKLT.Blueprint.Win

private theorem mem_cross_iff (x z : Plane) :
    z ∈ cross x ↔
      z = x ∨
      (z.1 = x.1 + 1 ∧ z.2 = x.2) ∨
      (z.1 = x.1 ∧ z.2 = x.2 + 1) ∨
      (z.1 + 1 = x.1 ∧ z.2 = x.2) ∨
      (z.1 = x.1 ∧ z.2 + 1 = x.2) := by
  classical
  simp only [cross, Finset.mem_insert, neighbours, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · intro hz
    rcases hz with rfl | ⟨d, hd⟩
    · exact Or.inl rfl
    · cases d with
      | east =>
        simp [Compass.step, Prod.add_def] at hd
        change (x.1 + 1, x.2) = z at hd
        exact Or.inr (Or.inl ⟨(congrArg Prod.fst hd).symm, (congrArg Prod.snd hd).symm⟩)
      | north =>
        simp [Compass.step, Prod.add_def] at hd
        change (x.1, x.2 + 1) = z at hd
        exact Or.inr (Or.inr (Or.inl ⟨(congrArg Prod.fst hd).symm, (congrArg Prod.snd hd).symm⟩))
      | west =>
        simp [Compass.step, Prod.add_def] at hd
        change (x.1 - 1, x.2) = z at hd
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by have := congrArg Prod.fst hd; omega, (congrArg Prod.snd hd).symm⟩)))
      | south =>
        simp [Compass.step, Prod.add_def] at hd
        change (x.1, x.2 - 1) = z at hd
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨(congrArg Prod.fst hd).symm, by have := congrArg Prod.snd hd; omega⟩)))
  · intro hz
    rcases hz with rfl | hz
    · exact Or.inl rfl
    · rcases hz with hz | hz
      · refine Or.inr ⟨Compass.east, ?_⟩
        rcases hz with ⟨h1, h2⟩
        apply Prod.ext <;> simp [Compass.step, Prod.add_def] <;> omega
      · rcases hz with hz | hz
        · refine Or.inr ⟨Compass.north, ?_⟩
          rcases hz with ⟨h1, h2⟩
          apply Prod.ext <;> simp [Compass.step, Prod.add_def] <;> omega
        · rcases hz with hz | hz
          · refine Or.inr ⟨Compass.west, ?_⟩
            rcases hz with ⟨h1, h2⟩
            apply Prod.ext <;> simp [Compass.step, Prod.add_def] <;> omega
          · refine Or.inr ⟨Compass.south, ?_⟩
            rcases hz with ⟨h1, h2⟩
            apply Prod.ext <;> simp [Compass.step, Prod.add_def] <;> omega

theorem main : AKLT.Blueprint.Win.CrossOverlapStatement := by
  intro x y h
  change supDist x y = 1 at h
  have hmax : max (x.1 - y.1).natAbs (x.2 - y.2).natAbs = 1 := h
  have h1 : (x.1 - y.1).natAbs ≤ 1 := by
    calc
      _ ≤ max (x.1 - y.1).natAbs (x.2 - y.2).natAbs := le_max_left _ _
      _ = 1 := hmax
  have h2 : (x.2 - y.2).natAbs ≤ 1 := by
    calc
      _ ≤ max (x.1 - y.1).natAbs (x.2 - y.2).natAbs := le_max_right _ _
      _ = 1 := hmax
  have h1z : ((x.1 - y.1).natAbs : ℤ) ≤ 1 := by exact_mod_cast h1
  have h2z : ((x.2 - y.2).natAbs : ℤ) ≤ 1 := by exact_mod_cast h2
  have h1lo : -1 ≤ x.1 - y.1 := by
    rcases Int.natAbs_eq (x.1 - y.1) with hh | hh <;> omega
  have h1hi : x.1 - y.1 ≤ 1 := by
    rcases Int.natAbs_eq (x.1 - y.1) with hh | hh <;> omega
  have h2lo : -1 ≤ x.2 - y.2 := by
    rcases Int.natAbs_eq (x.2 - y.2) with hh | hh <;> omega
  have h2hi : x.2 - y.2 ≤ 1 := by
    rcases Int.natAbs_eq (x.2 - y.2) with hh | hh <;> omega
  classical
  by_cases hxeq : x.1 = y.1
  · by_cases hyeq : x.2 = y.2
    · have hxy : x = y := Prod.ext hxeq hyeq
      rw [hxy] at h
      simp [supDist] at h
    · have hstep : x.2 = y.2 + 1 ∨ y.2 = x.2 + 1 := by omega
      refine ⟨x, ?_⟩
      rw [Finset.mem_inter]
      constructor
      · exact (mem_cross_iff x x).2 (Or.inl rfl)
      · apply (mem_cross_iff y x).2
        rcases hstep with hs | hs
        · exact Or.inr (Or.inr (Or.inl ⟨hxeq, by omega⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hxeq, by omega⟩)))
  · by_cases hyeq : x.2 = y.2
    · have hstep : x.1 = y.1 + 1 ∨ y.1 = x.1 + 1 := by omega
      refine ⟨x, ?_⟩
      rw [Finset.mem_inter]
      constructor
      · exact (mem_cross_iff x x).2 (Or.inl rfl)
      · apply (mem_cross_iff y x).2
        rcases hstep with hs | hs
        · exact Or.inr (Or.inl ⟨by omega, hyeq⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, hyeq⟩)))
    · have h1step : x.1 = y.1 + 1 ∨ y.1 = x.1 + 1 := by omega
      have h2step : x.2 = y.2 + 1 ∨ y.2 = x.2 + 1 := by omega
      let z : Plane := (x.1, y.2)
      refine ⟨z, ?_⟩
      rw [Finset.mem_inter]
      constructor
      · apply (mem_cross_iff x z).2
        rcases h2step with hs | hs
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨by simp [z], by simp [z]; omega⟩)))
        · exact Or.inr (Or.inr (Or.inl ⟨by simp [z], by simp [z]; omega⟩))
      · apply (mem_cross_iff y z).2
        rcases h1step with hs | hs
        · exact Or.inr (Or.inl ⟨by simp [z]; omega, rfl⟩)
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by simp [z]; omega, rfl⟩)))

end AKLT.W.WIN026

#print axioms AKLT.W.WIN026.main
