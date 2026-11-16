import AKLT.W.REC080.Basic

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC080

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  simp only [dot, mul_comm]

/-- Bound each residual observable before taking the maximum of the two
pin-dependent trace ratios. The maximum remains inside the finite sum. -/
theorem expansion_abs_le_onePoint {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (u v : Plane) (b : Bool)
    (hExpansion : D.expectation τ b (fun a => dot (a u) (a v)) =
      stoppedSum D u (protectedSites G) fun n w =>
        (traceCoefficient D (wordVertices u w) : ℝ) *
          traceRatio D τ b (wordVertices u w) *
          (traceNetwork D (wordVertices u w)).expectation τ b
            (fun a => dot (a (wordVertex u w n)) (a v))) :
    |D.expectation τ b (fun a => dot (a u) (a v))| ≤ onePointSum D τ u := by
  classical
  rw [hExpansion]
  unfold stoppedSum onePointSum
  calc
    _ ≤ ∑ n ∈ Finset.range (D.bonds.card + 1),
        |∑ w ∈ stoppedNetworkTrails D u (protectedSites G) n,
          (traceCoefficient D (wordVertices u w) : ℝ) * traceRatio D τ b (wordVertices u w) *
          (traceNetwork D (wordVertices u w)).expectation τ b
            (fun a => dot (a (wordVertex u w n)) (a v))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro n _
      calc
        _ ≤ ∑ w ∈ stoppedNetworkTrails D u (protectedSites G) n,
            |(traceCoefficient D (wordVertices u w) : ℝ) * traceRatio D τ b (wordVertices u w) *
              (traceNetwork D (wordVertices u w)).expectation τ b
                (fun a => dot (a (wordVertex u w n)) (a v))| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro w _
          have hc : 0 ≤ (traceCoefficient D (wordVertices u w) : ℝ) := by
            exact_mod_cast traceCoefficient_nonneg D (wordVertices u w)
          have hr := traceRatio_nonneg D τ b (wordVertices u w)
          have hmax : traceRatio D τ b (wordVertices u w) ≤
              max (traceRatio D τ true (wordVertices u w))
                (traceRatio D τ false (wordVertices u w)) := by
            cases b
            · exact le_max_right _ _
            · exact le_max_left _ _
          rw [abs_mul, abs_of_nonneg (mul_nonneg hc hr)]
          calc
            _ ≤ (traceCoefficient D (wordVertices u w) : ℝ) * traceRatio D τ b (wordVertices u w) * 1 :=
              mul_le_mul_of_nonneg_left (pair_abs_le_one _ _ _ _ _) (mul_nonneg hc hr)
            _ ≤ _ := by
              rw [mul_one]
              exact mul_le_mul_of_nonneg_left hmax hc

theorem adjacent_direction {v c : Plane} (h : Adjacent v c) :
    ∃ d : Compass, v = c + d.step := by
  have hfour : v = c + Compass.east.step ∨ v = c + Compass.north.step ∨
      v = c + Compass.west.step ∨ v = c + Compass.south.step := by
    simp only [Adjacent, latticeDist] at h
    simp only [Compass.step, Prod.ext_iff, Prod.fst_add, Prod.snd_add]
    omega
  rcases hfour with h | h | h | h
  · exact ⟨.east, h⟩
  · exact ⟨.north, h⟩
  · exact ⟨.west, h⟩
  · exact ⟨.south, h⟩

def terminalNetwork (p : PairData) {n : ℕ} (w : DirectionWord n) : Network p.G :=
  normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c

theorem terminal_centre_removed (p : PairData) {n : ℕ} (w : DirectionWord n) :
    (terminalNetwork p w).status p.c = .X := by
  apply trace_removed p.normalized p.c _ (wordVertices p.u w)
  exact p.pair.2.2.2.2.1

theorem terminal_absent (p : PairData) {n : ℕ} (w : DirectionWord n)
    (incoming : Compass) (hi : p.v = p.c + incoming.step) :
    ¬ (terminalNetwork p w).Present (p.v - incoming.step) p.v := by
  have heq : p.v - incoming.step = p.c := by rw [hi]; abel
  rw [heq]
  intro h
  have hc := (Finset.mem_filter.mp h.1).2
  exact hc (terminal_centre_removed p w)

theorem terminal_expectation (p : PairData) {n : ℕ} (w : DirectionWord n)
    (b : Bool) (f : (Plane → Vec3) → ℝ) :
    (terminalNetwork p w).expectation p.τ b f =
      (traceNetwork p.normalized (wordVertices p.u w)).expectation p.τ b f := by
  apply normalize_expectation
  exact trace_removed p.normalized p.c p.pair.2.2.2.2.1 (wordVertices p.u w)

end AKLT.W.REC080
