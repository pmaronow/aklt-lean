module
public import AKLT.Blueprint.Win.NodesTaper

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN035

/-- Move one maximal coordinate away from the center, choosing the positive sign at zero. -/
def stepAway (c z : Plane) : Plane :=
  if (z.2 - c.2).natAbs ≤ (z.1 - c.1).natAbs then
    if c.1 ≤ z.1 then (z.1 + 1, z.2) else (z.1 - 1, z.2)
  else
    if c.2 ≤ z.2 then (z.1, z.2 + 1) else (z.1, z.2 - 1)

theorem stepAway_adj (c z : Plane) : Adjacent z (stepAway c z) := by
  unfold stepAway
  split_ifs <;> simp [Adjacent, latticeDist]

theorem stepAway_supDist (c z : Plane) :
    supDist (stepAway c z) c = supDist z c + 1 := by
  unfold stepAway supDist
  split_ifs <;> omega

theorem supDist_lipschitz {z w : Plane} (h : Adjacent z w) (c : Plane) :
    (supDist z c : ℤ) ≤ (supDist w c : ℤ) + 1 := by
  unfold Adjacent latticeDist at h
  unfold supDist
  omega

theorem offset_lipschitz {z w : Plane} (h : Adjacent z w)
    (y : Plane) (u : ℕ) (i : ℤ) :
    (radialOffset y u i z : ℤ) ≤ (radialOffset y u i w : ℤ) + 1 := by
  have h₁ := supDist_lipschitz h y
  have hsym : Adjacent w z := by
    unfold Adjacent latticeDist at *
    have e₁ : w.1 - z.1 = -(z.1 - w.1) := by omega
    have e₂ : w.2 - z.2 = -(z.2 - w.2) := by omega
    simpa only [e₁, e₂, Int.natAbs_neg] using h
  have h₂ := supDist_lipschitz hsym y
  unfold radialOffset
  omega

theorem mem_square_iff (a z : Plane) (u : ℕ) :
    z ∈ square a u ↔ supDist z a ≤ u := by
  simp only [square, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Icc, supDist]
  omega

theorem setup_y_exterior {a y : Plane} {u : ℕ} {i : ℤ}
    (hs : CutSetup a y u i) : y ∉ square a u := by
  intro hy
  have hd : setDistance supDist y (↑(square a u) : Set Plane) = 1 := hs.1.2.2
  have hb : setDistance supDist y (↑(square a u) : Set Plane) ≤ 0 := by
    unfold setDistance
    simpa [supDist] using
      (iInf_le (fun z : (↑(square a u) : Set Plane) => (supDist y z.val : ℕ∞))
        ⟨y, hy⟩)
  rw [hd] at hb
  norm_num at hb

end AKLT.W.WIN035
