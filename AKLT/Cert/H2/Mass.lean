import AKLT.Cert.H2.Trails

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Cert.H2

set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

theorem mass_nonneg (m n : ℕ) (u : Plane) (incoming : Compass) (ω : MemoryWindow m) :
    0 ≤ memoryTrailMass m n u incoming ω := by
  unfold memoryTrailMass
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact weight_nonneg _ _ _
  · rfl

theorem kind_nonneg (k : StepKind) : 0 ≤ kindWeight k := by
  cases k <;> norm_num [kindWeight, passageFactor, localThreshold]

theorem matrix_nonneg (m : ℕ) (ω ω' : MemoryWindow m) : 0 ≤ memoryMatrix m ω ω' := by
  unfold memoryMatrix
  exact Finset.sum_nonneg fun d _ => by split_ifs; exact kind_nonneg _; rfl

/-- The exact partition of true trails by their raw suffix window, with an arbitrary test vector. -/
theorem mass_pair {m n : ℕ} (hmn : m ≤ n) (u : Plane) (incoming : Compass)
    (f : MemoryWindow m → ℚ) :
    (∑ ω, memoryTrailMass m n u incoming ω * f ω) =
      ∑ w : DirectionWord n, if h : IsTrail u incoming w then
        trailWeight u incoming w * f ⟨lastWindowWord m w, lastWindow_raw u incoming w h hmn⟩ else 0 := by
  unfold memoryTrailMass
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  by_cases hw : IsTrail u incoming w
  · rw [dite_eq_left hw]
    let s : MemoryWindow m := ⟨lastWindowWord m w, lastWindow_raw u incoming w hw hmn⟩
    have he (ω : MemoryWindow m) : (IsTrail u incoming w ∧ lastWindowWord m w = ω.val) ↔ ω = s := by
      simp only [hw, true_and]
      exact ⟨fun h => (Subtype.ext h).symm, fun h => by subst ω; rfl⟩
    simp_rw [he]
    simp [s]
  · simp [hw]

theorem mass_total {m n : ℕ} (hmn : m ≤ n) (u : Plane) (incoming : Compass) :
    (∑ ω, memoryTrailMass m n u incoming ω) = openTrailTotal n u incoming := by
  simpa [openTrailTotal] using mass_pair hmn u incoming (fun _ => 1)

/-- Forgetting old bonds and departures can only enlarge the one-step true mass. -/
theorem mass_step {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) (u : Plane) (incoming : Compass)
    (ω' : MemoryWindow m) : memoryTrailMass m (n + 1) u incoming ω' ≤
      ∑ ω, memoryTrailMass m n u incoming ω * memoryMatrix m ω ω' := by
  rw [mass_pair hmn]
  unfold memoryTrailMass
  rw [sum_snoc]
  apply Finset.sum_le_sum
  intro w _
  by_cases hw : IsTrail u incoming w
  · rw [dite_eq_left hw]
    unfold memoryMatrix
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro d _
    by_cases ht : IsTrail u incoming (snoc w d) ∧ lastWindowWord m (snoc w d) = ω'.val
    · have ha := lastWindow_admissible u incoming w d hm hmn ht.1
      have he : windowSuccessor (lastWindowWord m w) d = ω'.val := by
        simpa only [lastWindow_snoc w d hm hmn] using ht.2
      simp only [ht, ite_true, ha, he, and_self, snoc_factor]
      exact mul_le_mul_of_nonneg_left (factor_memory_le u incoming w d hm hmn)
        (weight_nonneg u incoming w)
    · rw [ite_eq_right ht]
      exact mul_nonneg (weight_nonneg _ _ _)
        (by split_ifs; exact kind_nonneg _; rfl)
  · rw [dite_eq_right hw]
    have he (d : Compass) : ¬(IsTrail u incoming (snoc w d) ∧
        lastWindowWord m (snoc w d) = ω'.val) := by
      rintro ⟨h, _⟩
      exact hw (by simpa using trail_initWord u incoming (snoc w d) h)
    simp [he]

theorem east_vertex (n j : ℕ) (hj : j ≤ n) :
    wordVertex (0, 0) (fun _ : Fin n => Compass.east) j = ((j : ℤ), 0) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [vertex_succ (0, 0) (fun _ : Fin n => Compass.east) j (by omega), ih (by omega)]
    simp [Compass.step, Nat.cast_add, Nat.cast_one]

theorem east_raw (m : ℕ) : RawWindow (fun _ : Fin m => Compass.east) := by
  intro i j he
  have hi : ((i.val : ℤ), (0 : ℤ)) ∈ wordBond (0, 0) (fun _ : Fin m => Compass.east) j := by
    rw [← he]
    simp [wordBond, east_vertex m i.val (by omega)]
  have hj : (((i.val + 1 : ℕ) : ℤ), (0 : ℤ)) ∈ wordBond (0, 0) (fun _ : Fin m => Compass.east) j := by
    rw [← he]
    simp [wordBond, east_vertex m (i.val + 1) (by omega)]
  simp only [wordBond, east_vertex m j.val (by omega), east_vertex m (j.val + 1) (by omega),
    Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hi hj
  apply Fin.ext
  rcases hi with hi | hi <;> rcases hj with hj | hj <;> omega

instance memory_nonempty (m : ℕ) : Nonempty (MemoryWindow m) := ⟨⟨_, east_raw m⟩⟩

end AKLT.Cert.H2
