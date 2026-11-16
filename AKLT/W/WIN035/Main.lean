import AKLT.W.WIN035.Paths

noncomputable section
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN035

/-- Above the radial band, increasing the radius leads out of the finite square. -/
theorem outer_escape (a y : Plane) (u : ℕ) (i : ℤ) (z : Plane)
    (hρ : shellRadius u i ≤ (supDist z y : ℤ))
    (ht : shellSpacing u / 12 < (radialOffset y u i z : ℝ)) :
    ∃ w : Plane, w ∉ square a u ∧
      JoinedIn Adjacent {v | v ∉ taper a y u i} z w := by
  let S : Set Plane := {v | supDist z y ≤ supDist v y}
  have hST : S ⊆ {v | v ∉ taper a y u i} := by
    intro v hv hvt
    have hm : radialOffset y u i z ≤ radialOffset y u i v := by
      change supDist z y ≤ supDist v y at hv
      unfold radialOffset
      omega
    have hmR : (radialOffset y u i z : ℝ) ≤ (radialOffset y u i v : ℝ) := by
      exact_mod_cast hm
    have hband := (Finset.mem_filter.mp hvt).2.1
    exact (not_lt_of_ge (hmR.trans hband)) ht
  obtain ⟨w, hw, hzw⟩ := escape_of_increasing (square a u) S (fun v => supDist v y)
    (by
      intro v _ hv
      refine ⟨stepAway y v, ?_, stepAway_adj y v, ?_⟩
      · change supDist z y ≤ supDist (stepAway y v) y
        rw [stepAway_supDist]
        exact (show supDist z y ≤ supDist v y from hv).trans (Nat.le_succ _)
      · rw [stepAway_supDist]
        omega) z (by simp [S])
  exact ⟨w, hw, joined_mono hST hzw⟩

/-- Below the radial band, a path toward the exterior point y stays below the band. -/
theorem inner_escape (a y : Plane) (u : ℕ) (i : ℤ) (z : Plane)
    (hy : y ∉ square a u)
    (hρ : (supDist z y : ℤ) < shellRadius u i)
    (ht : shellSpacing u / 12 < (radialOffset y u i z : ℝ)) :
    ∃ w : Plane, w ∉ square a u ∧
      JoinedIn Adjacent {v | v ∉ taper a y u i} z w := by
  let S : Set Plane := {v | supDist v y ≤ supDist z y}
  have hST : S ⊆ {v | v ∉ taper a y u i} := by
    intro v hv hvt
    have hm : radialOffset y u i z ≤ radialOffset y u i v := by
      change supDist v y ≤ supDist z y at hv
      unfold radialOffset
      omega
    have hmR : (radialOffset y u i z : ℝ) ≤ (radialOffset y u i v : ℝ) := by
      exact_mod_cast hm
    have hband := (Finset.mem_filter.mp hvt).2.1
    exact (not_lt_of_ge (hmR.trans hband)) ht
  have hpath : JoinedIn Adjacent S z y := joined_to_point y
    (by
      intro v hv _
      exact (stepToward_supDist_le v y).trans hv) z (by simp [S])
  exact ⟨y, hy, joined_mono hST hpath⟩

/-- An outward step lowers the square depth by one and the offset by at most one. -/
theorem low_clearance_escape (a y : Plane) (u : ℕ) (i : ℤ) (z : Plane)
    (hz : squareDepth a u z < (radialOffset y u i z : ℤ) + 32) :
    ∃ w : Plane, w ∉ square a u ∧
      JoinedIn Adjacent {v | v ∉ taper a y u i} z w := by
  let S : Set Plane := {v | squareDepth a u v < (radialOffset y u i v : ℤ) + 32}
  have hST : S ⊆ {v | v ∉ taper a y u i} := by
    intro v hv hvt
    exact (not_lt_of_ge (Finset.mem_filter.mp hvt).2.2) hv
  obtain ⟨w, hw, hzw⟩ := escape_of_increasing (square a u) S (fun v => supDist v a)
    (by
      intro v hvF hv
      have hr : supDist v a ≤ u := (mem_square_iff a v u).mp hvF
      have hdepth : squareDepth a u (stepAway a v) = squareDepth a u v - 1 := by
        unfold squareDepth
        rw [stepAway_supDist]
        omega
      have ht := offset_lipschitz (stepAway_adj a v) y u i
      refine ⟨stepAway a v, ?_, stepAway_adj a v, ?_⟩
      · change squareDepth a u (stepAway a v) < (radialOffset y u i (stepAway a v) : ℤ) + 32
        change squareDepth a u v < (radialOffset y u i v : ℤ) + 32 at hv
        omega
      · rw [stepAway_supDist]
        omega) z hz
  exact ⟨w, hw, joined_mono hST hzw⟩

/-- Every site in the taper complement is joined there to the square exterior. -/
theorem main : AKLT.Blueprint.Win.ComplementEscapeStatement := by
  intro a y u i hsetup z hz
  by_cases hzSquare : z ∈ square a u
  · have hnot :
        ¬ ((radialOffset y u i z : ℝ) ≤ shellSpacing u / 12 ∧
          (radialOffset y u i z : ℤ) + 32 ≤ squareDepth a u z) := by
      intro hh
      exact hz (Finset.mem_filter.mpr ⟨hzSquare, hh⟩)
    by_cases hrad : (radialOffset y u i z : ℝ) ≤ shellSpacing u / 12
    · exact low_clearance_escape a y u i z (lt_of_not_ge (fun hd => hnot ⟨hrad, hd⟩))
    · have ht : shellSpacing u / 12 < (radialOffset y u i z : ℝ) := lt_of_not_ge hrad
      by_cases hρ : shellRadius u i ≤ (supDist z y : ℤ)
      · exact outer_escape a y u i z hρ ht
      · exact inner_escape a y u i z (setup_y_exterior hsetup) (by omega) ht
  · exact ⟨z, hzSquare, Relation.ReflTransGen.refl⟩

end AKLT.W.WIN035

#print axioms AKLT.W.WIN035.main
