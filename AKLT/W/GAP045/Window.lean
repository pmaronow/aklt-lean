import AKLT.W.GAP045.Plane

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
namespace AKLT.W.GAP045
attribute [local instance] Classical.propDecidable
local instance (α : Type) : DecidableEq α := Classical.decEq α

lemma window_tv_reindex (P : PlaneSpec) (F B : Finset Plane) (η ξ : Config P.Letter) :
    totalVariation
      (marginal (P.law F η) (restrict (sitesInVolume F B)))
      (marginal (P.law F ξ) (restrict (sitesInVolume F B))) ≤
    totalVariation (specMarginal P F B η) (specMarginal P F B ξ) := by
  classical
  let r : PlaneConfig P B → ((x : sitesInVolume F B) → P.Letter x.val.val) :=
    fun b x => b ⟨x.val.val, (Finset.mem_filter.mp x.property).2⟩
  have he (ζ : Config P.Letter) :
      marginal (specMarginal P F B ζ) r =
        marginal (P.law F ζ) (restrict (sitesInVolume F B)) := by
    unfold specMarginal
    rw [marginal_comp]
    congr 1
    funext σ x
    dsimp [r, restrict, Function.comp_def]
    simp [fill, x.val.property]
  rw [← he η, ← he ξ]
  exact tv_marginal _ _ r

lemma sites_card_le (W V : Finset Plane) : (sitesInVolume W V).card ≤ V.card := by
  calc
    _ = ((sitesInVolume W V).image Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ ≤ V.card := Finset.card_le_card (by
      intro x hx
      obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hz).2)

lemma shell_partition (a y : Plane) (u l : ℕ) (i : ℤ) (F : Finset Plane) :
    sitesInVolume F (nearShell a y u l i) ∪ sitesInVolume F (window a y u l i) =
      sitesInVolume F (shell a y u i) := by
  ext x
  simp only [sitesInVolume, window, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_sdiff]
  have hn : x.val ∈ nearShell a y u l i → x.val ∈ shell a y u i := by
    intro h
    simp only [nearShell, Finset.mem_filter] at h
    exact h.1
  tauto

lemma shell_disjoint (a y : Plane) (u l : ℕ) (i : ℤ) (F : Finset Plane) :
    Disjoint (sitesInVolume F (nearShell a y u l i)) (sitesInVolume F (window a y u l i)) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' := (Finset.mem_filter.mp hx).2
  have hy' := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hy).2).2
  exact hy' hx'

lemma active_shell_bound (u h : ℕ) (hh : (h : ℝ) ≤ shellSpacing u) (j : Fin h) :
    (j.val + 2 : ℤ) ≤ lastShellIndex u := by
  have hf : (h : ℤ) ≤ ⌊shellSpacing u⌋ := Int.le_floor.mpr (by exact_mod_cast hh)
  unfold lastShellIndex
  have hj := j.isLt
  omega

/-- The numerical success bound, directly on the local far-volume law. -/
theorem local_success_coupling (P : PlaneSpec) (hP : RegularSpec P)
    (l : ℕ) (p : ℝ) (Mstar : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hEnergy : SpecEnergy P α) (hWindow : SpecWindow P l p Mstar)
    (a y : Plane) (u h : ℕ) (hu : Mstar ≤ u)
    (hy : setDistance supDist y (↑(square a u) : Set Plane) = 1)
    (hg : ShellGeometry l a y u) (hh : (h : ℝ) ≤ shellSpacing u)
    (j : Fin h) (hj : j.val + 2 ≤ h) (hex : (j.val + 2 : ℤ) ∉ exceptionalIndices a y u)
    (η ξ : Config P.Letter) :
    ∃ c : Coupling (P.law (farVolume a y u (j.val + 2)) η)
      (P.law (farVolume a y u (j.val + 2)) ξ),
      p * α ^ (16*l) ≤ eventMass
        (fun z : PlaneConfig P (farVolume a y u (j.val + 2)) ×
          PlaneConfig P (farVolume a y u (j.val + 2)) => c.mass z.1 z.2)
        (fun z => AgreeOn (sitesInVolume (farVolume a y u (j.val + 2))
          (shell a y u (j.val + 2))) z.1 z.2) := by
  let F := farVolume a y u (j.val + 2)
  let A := sitesInVolume F (nearShell a y u l (j.val + 2))
  let B := sitesInVolume F (window a y u l (j.val + 2))
  have hi : (2 : ℤ) ≤ j.val + 2 := by omega
  have his : ((j.val + 2 : ℤ) : ℝ) ≤ shellSpacing u :=
    (by exact_mod_cast hj : ((j.val + 2 : ℤ) : ℝ) ≤ h).trans hh
  have htv := hWindow.2.2.2.2 a u hu y hy (j.val+2) hi his hex η ξ
  have htv' : totalVariation (marginal (P.law F η) (restrict B))
      (marginal (P.law F ξ) (restrict B)) ≤ 1-p :=
    (window_tv_reindex P F (window a y u l (j.val+2)) η ξ).trans htv
  obtain ⟨c,hc⟩ := patch_coupling (hP.1 F η) (hP.1 F ξ) A B
    (shell_disjoint a y u l (j.val+2) F) α p hα.le
    (hEnergy F η) (hEnergy F ξ) htv'
  have hcard : A.card ≤ 16*l := by
    have hb := (hg.2.2.1 (j.val+2) hi (active_shell_bound u h hh j) hex)
    have ha := sites_card_le F (nearShell a y u l (j.val+2))
    dsimp [A]
    omega
  refine ⟨c, (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one hα.le hα1 hcard) hWindow.2.2.1.le).trans ?_⟩
  simpa only [A, B, shell_partition] using hc

end AKLT.W.GAP045
