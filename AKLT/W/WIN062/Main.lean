import AKLT.Blueprint.Win.NodesRemoval

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN062

private theorem boundaryDepth_ne_top (G : Finset Plane) (x : Plane) :
    boundaryDepth G x ≠ ⊤ := by
  classical
  have hG : (↑G : Set Plane).Finite := G.finite_toSet
  have hex : ((↑G : Set Plane)ᶜ).Nonempty := hG.infinite_compl.nonempty
  obtain ⟨y, hy⟩ := hex
  have hle : boundaryDepth G x ≤ (latticeDist x y : ℕ∞) := by
    unfold boundaryDepth setDistance
    exact iInf_le (fun y : {z : Plane // z ∉ G} => (latticeDist x y.val : ℕ∞))
      ⟨y, by simpa using hy⟩
  exact ne_of_lt (lt_of_le_of_lt hle (ENat.natCast_lt_top _))

private theorem shift_power_eq (θ : ℝ) (hθ : 0 < θ) (n : ℕ) (hn : 3 ≤ n) :
    θ ^ (n - 3) = θ ^ (-3 : ℤ) * θ ^ n := by
  have hθ0 : θ ≠ 0 := ne_of_gt hθ
  rw [pow_sub₀ θ hθ0 hn]
  rw [zpow_neg]
  field_simp [hθ0]

theorem main : AKLT.Blueprint.Win.RemovalCostSumStatement := by
  classical
  intro G X τ e hdepth A θ hA hθ hθ1 hcost
  have hseed : θ ^ depthShift G (e.site 0) ≤ 1 := by
    exact pow_le_one₀ (le_of_lt hθ) hθ1.le
  have hthetaNeg_nonneg : 0 ≤ θ ^ (-3 : ℤ) := by positivity
  have hpower : ∀ j : Fin e.last,
      θ ^ depthShift G (e.site j.succ) =
        θ ^ (-3 : ℤ) * decay θ (boundaryDepth G (e.site j.succ)) := by
    intro j
    have hmem : e.site j.succ ∈ X := by
      have hx : e.site j.succ ∈ Finset.univ.image e.site :=
        Finset.mem_image.mpr ⟨j.succ, Finset.mem_univ _, rfl⟩
      simpa [e.image_eq] using hx
    let d := boundaryDepth G (e.site j.succ)
    have hfinite : d ≠ ⊤ := boundaryDepth_ne_top G (e.site j.succ)
    have hdn : 3 ≤ d.toNat := by
      have hh := ENat.toNat_le_toNat (hdepth (e.site j.succ) hmem) hfinite
      simpa using hh
    have hdecay : decay θ d = θ ^ d.toNat := by
      simp [decay, hfinite]
    change θ ^ (d.toNat - 3) = _
    rw [hdecay]
    exact shift_power_eq θ hθ d.toNat hdn
  let f : Plane → ℝ := fun z => decay θ (boundaryDepth G z)
  let g : Fin e.last → Plane := fun j => e.site j.succ
  have hginj : Set.InjOn g (↑(Finset.univ : Finset (Fin e.last))) := by
    intro a _ b _ hab
    apply Fin.ext
    have hs := e.injective hab
    have hv := congrArg Fin.val hs
    dsimp [g] at hv
    omega
  have himage_sum : (∑ z ∈ Finset.univ.image g, f z) =
      ∑ j : Fin e.last, f (g j) := by
    exact Finset.sum_image hginj
  have himage_sub : Finset.univ.image g ⊆ X := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨j, _, rfl⟩
    have hx : e.site j.succ ∈ Finset.univ.image e.site :=
      Finset.mem_image.mpr ⟨j.succ, Finset.mem_univ _, rfl⟩
    simpa [e.image_eq] using hx
  have hf_nonneg : ∀ z ∈ X, 0 ≤ f z := by
    intro z hz
    dsimp [f, decay]
    split_ifs <;> positivity
  have hsum_image : (∑ z ∈ Finset.univ.image g, f z) ≤ ∑ z ∈ X, f z :=
    Finset.sum_le_sum_of_subset_of_nonneg himage_sub (by
      intro z hz _
      exact hf_nonneg z hz)
  have hsum_nonseed :
      (∑ j : Fin e.last, θ ^ depthShift G (e.site j.succ)) ≤
        θ ^ (-3 : ℤ) * ∑ z ∈ X, decay θ (boundaryDepth G z) := by
    calc
      (∑ j : Fin e.last, θ ^ depthShift G (e.site j.succ)) =
          ∑ j : Fin e.last, θ ^ (-3 : ℤ) * f (g j) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hpower j
      _ = θ ^ (-3 : ℤ) * ∑ j : Fin e.last, f (g j) := by rw [Finset.mul_sum]
      _ = θ ^ (-3 : ℤ) * ∑ z ∈ Finset.univ.image g, f z := by rw [himage_sum]
      _ ≤ θ ^ (-3 : ℤ) * ∑ z ∈ X, f z :=
          mul_le_mul_of_nonneg_left hsum_image hthetaNeg_nonneg
      _ = θ ^ (-3 : ℤ) * ∑ z ∈ X, decay θ (boundaryDepth G z) := rfl
  have hseed_mul0 := mul_le_mul_of_nonneg_left hseed (show 0 ≤ (4 : ℝ) * A by positivity)
  have hseed_mul : 4 * A * θ ^ depthShift G (e.site 0) ≤ 4 * A := by
    nlinarith [hseed_mul0]
  have hsum_mul := mul_le_mul_of_nonneg_left hsum_nonseed (by positivity : 0 ≤ 2 * A)
  calc
    |cutError G X τ| ≤ 1 + 4 * A * θ ^ depthShift G (e.site 0) +
        2 * A * ∑ j : Fin e.last, θ ^ depthShift G (e.site j.succ) := hcost
    _ ≤ 1 + 4 * A + 2 * A * θ ^ (-3 : ℤ) *
        ∑ z ∈ X, decay θ (boundaryDepth G z) := by
          nlinarith [hseed_mul, hsum_mul]

#print axioms main

end AKLT.W.WIN062
