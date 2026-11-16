import AKLT.W.H3C056.Masks

namespace AKLT.W.H3C056
open AKLT.Defs AKLT.Gen.Packed AKLT.Cert.H3
set_option maxRecDepth 2048

theorem mem_box (x : Plane) : x ∈ square (0,0) certificateRadius ↔
    (-70 ≤ x.1 ∧ x.1 ≤ 70) ∧ (-70 ≤ x.2 ∧ x.2 ≤ 70) := by
  simp [square, certificateRadius]

theorem index_grid (s : Nat) : siteIndex (gridSite s) = s := by
  simp only [siteIndex, gridSite, sub_add_cancel, Int.toNat_natCast]
  simpa [Nat.mul_comm] using Nat.div_add_mod s 141

theorem grid_index (x : Plane) (hx : x ∈ square (0,0) certificateRadius) :
    gridSite (siteIndex x) = x := by
  rw [mem_box] at hx
  obtain ⟨⟨hxl,hxu⟩,hyl,hyu⟩ := hx
  have hy : (x.2+70).toNat < 141 := by omega
  have hdiv : siteIndex x/141 = (x.1+70).toNat := by unfold siteIndex; omega
  have hmod : siteIndex x%141 = (x.2+70).toNat := by unfold siteIndex; omega
  simp only [gridSite, hdiv, hmod]
  ext <;> simp only [Prod.fst, Prod.snd] <;> omega

theorem grid_eq (s : Nat) (x : Plane) (hx : x ∈ square (0,0) certificateRadius) :
    gridSite s = x ↔ s = siteIndex x := by
  constructor
  · intro h
    simpa only [index_grid] using congrArg siteIndex h
  · intro h
    rw [h, grid_index x hx]

theorem step_box (s : Nat) (hs : s < 19881) (d : Compass) :
    gridSite s+d.step ∈ square (0,0) certificateRadius ↔ ¬boundary d s := by
  have hm := Nat.mod_lt s (by decide : 0<141)
  rw [mem_box]
  cases d <;>
    simp only [gridSite, Compass.step, Prod.fst_add, Prod.snd_add,
      Prod.fst, Prod.snd, boundary] <;> omega

theorem index_step (s : Nat) (hs : s < 19881) (d : Compass) (h : ¬boundary d s) :
    siteIndex (gridSite s+d.step) = match d with
      | .east => s+141 | .north => s+1 | .west => s-141 | .south => s-1 := by
  have hm := Nat.mod_lt s (by decide : 0<141)
  have hd := Nat.div_add_mod s 141
  have H (n : Nat) (e : Int) : ((n:ℤ)-70+e+70).toNat = ((n:ℤ)+e).toNat := by
    congr 1
    omega
  cases d <;>
    simp only [gridSite, Compass.step, siteIndex, Prod.fst_add, Prod.snd_add,
      Prod.fst, Prod.snd, boundary, H, add_zero, sub_add_cancel,
      Int.toNat_natCast] at *
  all_goals dsimp [boundary] at h
  all_goals omega

end AKLT.W.H3C056
