import AKLT.Blueprint.Win.NodesTopology

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN028

private theorem latticeDist_symm (x y : Plane) : latticeDist x y = latticeDist y x := by
  unfold latticeDist
  rw [show x.1 - y.1 = -(y.1 - x.1) by omega,
    show x.2 - y.2 = -(y.2 - x.2) by omega,
    Int.natAbs_neg, Int.natAbs_neg]

private theorem latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  have h₁ : (x.1 - z.1).natAbs ≤ (x.1 - y.1).natAbs + (y.1 - z.1).natAbs := by
    calc
      (x.1 - z.1).natAbs = ((x.1 - y.1) - (z.1 - y.1)).natAbs := by congr 1; omega
      _ ≤ (x.1 - y.1).natAbs + (z.1 - y.1).natAbs := Int.natAbs_sub_le _ _
      _ = (x.1 - y.1).natAbs + (y.1 - z.1).natAbs := by
        rw [show z.1 - y.1 = -(y.1 - z.1) by omega, Int.natAbs_neg]
  have h₂ : (x.2 - z.2).natAbs ≤ (x.2 - y.2).natAbs + (y.2 - z.2).natAbs := by
    calc
      (x.2 - z.2).natAbs = ((x.2 - y.2) - (z.2 - y.2)).natAbs := by congr 1; omega
      _ ≤ (x.2 - y.2).natAbs + (z.2 - y.2).natAbs := Int.natAbs_sub_le _ _
      _ = (x.2 - y.2).natAbs + (y.2 - z.2).natAbs := by
        rw [show z.2 - y.2 = -(y.2 - z.2) by omega, Int.natAbs_neg]
  unfold latticeDist
  omega

private theorem boundaryDepth_attained (G : Finset Plane) (x : Plane) :
    ∃ y : Plane, y ∉ G ∧ boundaryDepth G x = (latticeDist x y : ℕ∞) ∧
      ∀ w : Plane, w ∉ G → latticeDist x y ≤ latticeDist x w := by
  classical
  have hS : Set.Infinite {y : Plane | y ∉ G} := by
    have hplane : Set.Infinite (Set.univ : Set Plane) := Set.infinite_univ
    have hG : (↑G : Set Plane).Finite := G.finite_toSet
    have hdiff := Set.Infinite.sdiff hplane hG
    have hEq : Set.univ \ (↑G : Set Plane) = {y : Plane | y ∉ G} := by
      ext y
      simp
    rw [← hEq]
    exact hdiff
  have hS' : ∃ y : Plane, y ∉ G := hS.nonempty
  let S : Type := {y : Plane // y ∉ G}
  let f : S → ℕ := fun y => latticeDist x y.val
  let p : ℕ → Prop := fun n => ∃ y : S, f y = n
  have hp : ∃ n, p n := by
    let y₀ : S := ⟨hS'.choose, hS'.choose_spec⟩
    exact ⟨f y₀, ⟨y₀, rfl⟩⟩
  obtain ⟨y₀, hy₀⟩ := Nat.find_spec hp
  have hmin : ∀ w : S, f y₀ ≤ f w := by
    intro w
    calc
      f y₀ = Nat.find hp := hy₀
      _ ≤ f w := Nat.find_min' hp ⟨w, rfl⟩
  have hdepth : boundaryDepth G x = (f y₀ : ℕ∞) := by
    unfold boundaryDepth setDistance
    change (⨅ w : S, (f w : ℕ∞)) = (f y₀ : ℕ∞)
    apply le_antisymm
    · exact iInf_le _ y₀
    · apply le_iInf
      intro w
      exact ENat.natCast_le_natCast.mpr (hmin w)
  exact ⟨y₀.val, y₀.property, hdepth, fun w hw => hmin ⟨w, hw⟩⟩

private theorem depthNat_step (G : Finset Plane) (x z : Plane)
    (hstep : latticeDist z x ≤ 1) :
    (boundaryDepth G x).toNat ≤ (boundaryDepth G z).toNat + 1 := by
  obtain ⟨yx, hyx, hdx, hminx⟩ := boundaryDepth_attained G x
  obtain ⟨yz, hyz, hdz, hminz⟩ := boundaryDepth_attained G z
  have hdist : latticeDist x yx ≤ latticeDist z yz + 1 := by
    calc
      latticeDist x yx ≤ latticeDist x yz := hminx yz hyz
      _ ≤ latticeDist x z + latticeDist z yz := latticeDist_triangle x z yz
      _ ≤ 1 + latticeDist z yz := Nat.add_le_add_right (by simpa [latticeDist_symm] using hstep) _
      _ = latticeDist z yz + 1 := Nat.add_comm _ _
  simpa [hdx, hdz] using hdist

theorem main : AKLT.Blueprint.Win.NeighbourDecayStatement := by
  intro G θ hθ0 hθ1 x z hstep
  have hdepth := depthNat_step G x z hstep
  have hpow : θ ^ ((boundaryDepth G z).toNat + 1) ≤
      θ ^ (boundaryDepth G x).toNat :=
    pow_le_pow_of_le_one (le_of_lt hθ0) (le_of_lt hθ1) hdepth
  have hmul := mul_le_mul_of_nonneg_left hpow (inv_nonneg.mpr (le_of_lt hθ0))
  have hcancel : θ⁻¹ * θ ^ ((boundaryDepth G z).toNat + 1) =
      θ ^ (boundaryDepth G z).toNat := by
    rw [pow_succ]
    calc
      θ⁻¹ * (θ ^ (boundaryDepth G z).toNat * θ) =
          (θ⁻¹ * θ) * θ ^ (boundaryDepth G z).toNat := by ac_rfl
      _ = θ ^ (boundaryDepth G z).toNat := by
        rw [inv_mul_cancel₀ (ne_of_gt hθ0), one_mul]
  have hfinal : θ ^ (boundaryDepth G z).toNat ≤
      θ⁻¹ * θ ^ (boundaryDepth G x).toNat := by
    rw [← hcancel]
    exact hmul
  obtain ⟨_, _, hdz, _⟩ := boundaryDepth_attained G z
  obtain ⟨_, _, hdx, _⟩ := boundaryDepth_attained G x
  simpa [decay, hdz, hdx] using hfinal

#print axioms main

end AKLT.W.WIN028
