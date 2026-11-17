import AKLT.Blueprint.Win.NodesShell

open AKLT.Defs

namespace AKLT.W.WIN009

private theorem natAbs_sub_le_add (a b c : ℤ) :
    (a - c).natAbs ≤ (a - b).natAbs + (b - c).natAbs := by
  have h := abs_sub_le a b c
  apply Int.ofNat_le.mp
  have hcast : ((a - c).natAbs : ℤ) ≤
      ((a - b).natAbs : ℤ) + ((b - c).natAbs : ℤ) := by
    rw [Int.natCast_natAbs, Int.natCast_natAbs, Int.natCast_natAbs]
    exact h
  simpa only [Int.natCast_add] using hcast

private theorem supDist_symm (x y : Plane) : supDist x y = supDist y x := by
  unfold supDist
  rw [show x.1 - y.1 = -(y.1 - x.1) by ring,
    show x.2 - y.2 = -(y.2 - x.2) by ring,
    Int.natAbs_neg, Int.natAbs_neg]

private theorem supDist_triangle (x y z : Plane) :
    supDist x z ≤ supDist x y + supDist y z := by
  unfold supDist
  apply max_le
  · calc
      (x.1 - z.1).natAbs ≤ (x.1 - y.1).natAbs + (y.1 - z.1).natAbs :=
        natAbs_sub_le_add x.1 y.1 z.1
      _ ≤ max (x.1 - y.1).natAbs (x.2 - y.2).natAbs +
          max (y.1 - z.1).natAbs (y.2 - z.2).natAbs :=
        Nat.add_le_add (le_max_left _ _) (le_max_left _ _)
  · calc
      (x.2 - z.2).natAbs ≤ (x.2 - y.2).natAbs + (y.2 - z.2).natAbs :=
        natAbs_sub_le_add x.2 y.2 z.2
      _ ≤ max (x.1 - y.1).natAbs (x.2 - y.2).natAbs +
          max (y.1 - z.1).natAbs (y.2 - z.2).natAbs :=
        Nat.add_le_add (le_max_right _ _) (le_max_right _ _)

private theorem setDistance_le_one_has_witness (x : Plane) (S : Set Plane)
    (h : setDistance supDist x S ≤ 1) :
    ∃ z ∈ S, supDist x z ≤ 1 := by
  classical
  have hw : ∃ z : S, (supDist x z.1 : ℕ∞) < 2 := by
    by_contra hn
    have hall : ∀ z : S, (2 : ℕ∞) ≤ (supDist x z.1 : ℕ∞) := by
      intro z
      by_contra hz
      exact hn ⟨z, lt_of_not_ge hz⟩
    have htwo : (2 : ℕ∞) ≤ setDistance supDist x S := by
      unfold setDistance
      exact le_iInf hall
    have hbad : (2 : ℕ∞) ≤ 1 := le_trans htwo h
    norm_num at hbad
  obtain ⟨z, hz⟩ := hw
  have hz' : supDist x z.1 < 2 := by
    exact (ENat.natCast_lt_natCast).mp hz
  refine ⟨z.1, z.2, ?_⟩
  omega

/-- The predecessor-shell clause of the window shell geometry lemma. -/
theorem main : AKLT.Blueprint.Win.PredecessorShellStatement := by
  classical
  intro a y u i hi x hx hdist
  obtain ⟨z, hzmem, hnear⟩ :=
    setDistance_le_one_has_witness x (↑(farVolume a y u i) : Set Plane) hdist
  let R : ℤ := supDist x y
  let S : ℤ := supDist z y
  let r : ℝ := ((i - 1 : ℤ) : ℝ) * shellSpacing u
  have hr : (((i : ℝ) - 1) * shellSpacing u) = r := by
    simp [r]
  have hxparts : x ∈ square a u ∧ x ∉ farVolume a y u i :=
    Finset.mem_sdiff.mp hx
  have hxnot : ¬ r < (R : ℝ) := by
    intro hlt
    apply hxparts.2
    have hmem : x ∈ farVolume a y u i := by
      change x ∈ (square a u).filter _
      apply Finset.mem_filter.mpr
      constructor
      · exact hxparts.1
      · simpa [hr, R] using hlt
    exact hmem
  have hRle : (R : ℝ) ≤ r := le_of_not_gt hxnot
  have hzfar : r < (S : ℝ) := by
    have hz' : z ∈ farVolume a y u i := hzmem
    have hzfilter :
        z ∈ (square a u).filter
          (fun w => ((i : ℝ) - 1) * shellSpacing u < supDist w y) := by
      simpa [farVolume] using hz'
    have h := (Finset.mem_filter.mp hzfilter).2
    simpa [hr, S] using h
  have hfloorS : ⌊r⌋ < S := Int.floor_lt.mpr hzfar
  have htri := supDist_triangle z x y
  have hsymm := supDist_symm z x
  rw [hsymm] at htri
  have htri' : supDist z y ≤ supDist x y + supDist x z := by
    simpa [Nat.add_comm] using htri
  have htriInt : S ≤ R + (supDist x z : ℤ) := by
    change (supDist z y : ℤ) ≤
      (supDist x y : ℤ) + (supDist x z : ℤ)
    exact_mod_cast htri'
  have hSle : S ≤ R + 1 := by
    have hnearInt : (supDist x z : ℤ) ≤ 1 := by exact_mod_cast hnear
    omega
  have hRfloor : R ≤ ⌊r⌋ := Int.le_floor.mpr hRle
  have hReq : R = ⌊r⌋ := by omega
  change x ∈ (square a u).filter
    (fun w => (supDist w y : ℤ) = shellRadius u (i - 1))
  apply Finset.mem_filter.mpr
  constructor
  · exact hxparts.1
  · simpa [R, r, shellRadius] using hReq

end AKLT.W.WIN009
