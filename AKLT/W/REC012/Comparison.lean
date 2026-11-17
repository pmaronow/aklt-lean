import AKLT.W.REC012.Fibres

noncomputable section
open scoped BigOperators
open AKLT.Defs
namespace AKLT.W.REC012

lemma paddedWeight_nonneg (s : Status) (j : SpinLetter) : 0 ≤ paddedWeight s j := by
  cases s <;> cases j <;> norm_num [paddedWeight, spinWeight]

lemma ambientSpins_norm {G : Finset Plane} (n : G → SpinLetter) (x : Plane) :
    normSq (ambientSpins G n x) ≤ 1 := by
  by_cases hx : x ∈ G
  · simp only [ambientSpins, dite_eq_left hx]
    exact spinVector_normSq_le_one _
  · simp [ambientSpins, hx, normSq, dot]

lemma outsideFactor_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y : Plane) (n : G.erase y → SpinLetter) : 0 ≤ outsideFactor D τ y n := by
  apply mul_nonneg
  · apply mul_nonneg
    · exact Finset.prod_nonneg (fun x hx => paddedWeight_nonneg _ _)
    · apply Finset.prod_nonneg
      intro e he
      have hb := (dot_abs_le_one (ambientSpins_norm n e.1) (ambientSpins_norm n e.2)).1
      linarith
  · unfold pinProduct
    apply Finset.prod_nonneg
    intro e he
    split_ifs
    · have hb := (dot_abs_le_one (le_of_eq (τ e).property) (ambientSpins_norm n e.val.1)).1
      linarith
    · norm_num

lemma offBonds_trace {G : Finset Plane} (D : Network G) (y o : Plane) :
    offBonds (traceStep D y o) y = offBonds D y := by
  ext e
  simp only [offBonds, Network.bonds, Finset.mem_filter]
  by_cases h₁ : e.1 = y <;> by_cases h₂ : e.2 = y
  · simp [h₁]
  · simp [h₁]
  · simp [h₂]
  · rw [trace_present_off D y o e.1 e.2 h₁ h₂]

lemma outsideFactor_trace {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y o : Plane) (n : G.erase y → SpinLetter)
    (hlegs : ∀ e : originalLegs G, e.val.1 ≠ y) :
    outsideFactor (traceStep D y o) τ y n = outsideFactor D τ y n := by
  unfold outsideFactor
  rw [offBonds_trace]
  have hw : (∏ x : G.erase y, paddedWeight ((traceStep D y o).status x.val) (n x)) =
      ∏ x : G.erase y, paddedWeight (D.status x.val) (n x) := by
    apply Finset.prod_congr rfl
    intro x hx
    simp [traceStep, Function.update_of_ne (Finset.mem_erase.mp x.property).1]
  rw [hw]
  congr 1
  unfold pinProduct
  apply Finset.prod_congr rfl
  intro e he
  simp only [trace_active_off D y o e.val.1 (hlegs e)]

lemma localIntegral_U_lower {G : Finset Plane} (D : Network G) (y : Plane)
    (v : Plane → Vec3) (hv : ∀ x, normSq (v x) ≤ 1)
    (hU : D.status y = .U) (hcard : (D.presentNeighbours y).card ≤ 3) :
    1 / 2 ≤ localIntegral D y v := by
  unfold localIntegral
  simp only [paddedWeight, hU]
  exact site_U_lower (incident D y) (fun e => v (otherEnd y e))
    ((incident_card_le D y).trans hcard) (fun _ _ => hv _)

lemma localIntegral_D_upper {G : Finset Plane} (D : Network G) (y : Plane)
    (v : Plane → Vec3) (hv : ∀ x, normSq (v x) ≤ 1)
    (hD : D.status y = .D) (hcard : (D.presentNeighbours y).card ≤ 2) :
    localIntegral D y v ≤ 6 / 5 := by
  unfold localIntegral
  simp only [paddedWeight, hD]
  exact site_D_upper (incident D y) (fun e => v (otherEnd y e))
    ((incident_card_le D y).trans hcard) (fun _ _ => hv _)

lemma localIntegral_D_small {G : Finset Plane} (D : Network G) (y : Plane)
    (v : Plane → Vec3) (hD : D.status y = .D) (hcard : (D.presentNeighbours y).card ≤ 1) :
    localIntegral D y v = 1 := by
  unfold localIntegral
  simp only [paddedWeight, hD]
  exact site_D_small (incident D y) (fun e => v (otherEnd y e)) ((incident_card_le D y).trans hcard)

lemma localIntegral_X {G : Finset Plane} (D : Network G) (y : Plane)
    (v : Plane → Vec3) (hX : D.status y = .X) : localIntegral D y v = 1 := by
  simp [localIntegral, hX, paddedWeight, spinVector, dot]

lemma localIntegral_trace_le {G : Finset Plane} (D : Network G) (y o : Plane)
    (hy : D.AdmissibleStart y) (ho : o ∈ D.presentNeighbours y)
    (v : Plane → Vec3) (hv : ∀ x, normSq (v x) ≤ 1) :
    localIntegral (traceStep D y o) y v ≤ (12 / 5 : ℝ) * localIntegral D y v := by
  rcases hy.2.2 with ⟨hU,hcard⟩ | ⟨hD,hcard⟩
  · have hpre := localIntegral_U_lower D y v hv hU hcard
    have hpostD : (traceStep D y o).status y = .D := by simp [traceStep,hU]
    have hpostcard : ((traceStep D y o).presentNeighbours y).card ≤ 2 := by
      rw [trace_neighbours_U D y o hU ho, Finset.card_erase_of_mem ho]
      omega
    have hpost := localIntegral_D_upper (traceStep D y o) y v hv hpostD hpostcard
    linarith
  · have hpre := localIntegral_D_small D y v hD hcard
    have hpostX : (traceStep D y o).status y = .X := by simp [traceStep,hD]
    rw [localIntegral_X _ _ _ hpostX, hpre]
    norm_num

/-- The local comparison summed against the common nonnegative outside factor. -/
theorem pinned_partition_upper (a : AKLT.Blueprint.Rec.Departure) :
    (traceStep a.D a.y a.o).partition a.τ true (fun _ => 1) ≤
      (12 / 5 : ℝ) * a.D.partition a.τ true (fun _ => 1) := by
  have hyG : a.y ∈ a.G := (Finset.mem_filter.mp a.start.1).1
  have hlegs := no_legs_at_start a.D a.y a.start
  rw [partition_fibres (traceStep a.D a.y a.o) a.τ a.y hyG hlegs,
    partition_fibres a.D a.τ a.y hyG hlegs, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  rw [outsideFactor_trace a.D a.τ a.y a.o n hlegs]
  have hlocal := localIntegral_trace_le a.D a.y a.o a.start a.present
    (ambientSpins (a.G.erase a.y) n) (ambientSpins_norm n)
  have h := mul_le_mul_of_nonneg_left hlocal (outsideFactor_nonneg a.D a.τ a.y n)
  nlinarith

end AKLT.W.REC012
