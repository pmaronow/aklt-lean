import AKLT.Cert.H2.Frames

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Cert.H2

set_option autoImplicit false
set_option maxHeartbeats 3000000
attribute [local instance] Classical.propDecidable

theorem total_nonneg (n : ℕ) (u : Plane) (incoming : Compass) :
    0 ≤ openTrailTotal n u incoming := by
  unfold openTrailTotal
  exact Finset.sum_nonneg fun w _ => by split_ifs; exact weight_nonneg _ _ _; rfl

@[simp] theorem total_zero (u : Plane) (incoming : Compass) :
    openTrailTotal 0 u incoming = 1 := by
  have ht (w : DirectionWord 0) : IsTrail u incoming w := by
    constructor
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  simp [openTrailTotal, ht, trailWeight]

theorem total_step (n : ℕ) (u : Plane) (incoming : Compass) :
    openTrailTotal (n + 1) u incoming ≤ openTrailTotal n u incoming * passageFactor false := by
  unfold openTrailTotal
  rw [sum_snoc, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro w _
  by_cases hw : IsTrail u incoming w
  · simp only [hw, ite_true]
    calc
      (∑ d : Compass, if IsTrail u incoming (snoc w d) then
          trailWeight u incoming (snoc w d) else 0) ≤
        ∑ d : Compass, if d ≠ (nextIncoming incoming w).reverse then
          trailWeight u incoming w * (passageFactor false / 3) else 0 := by
        apply Finset.sum_le_sum
        intro d _
        by_cases he : IsTrail u incoming (snoc w d)
        · rw [ite_eq_left he, ite_eq_left (snoc_nonreverse u incoming w d he), snoc_factor]
          exact mul_le_mul_of_nonneg_left (factor_le u incoming w d) (weight_nonneg _ _ _)
        · simp only [he, ite_false]
          split_ifs
          · exact mul_nonneg (weight_nonneg _ _ _) (by norm_num [passageFactor, localThreshold])
          · rfl
      _ = trailWeight u incoming w * passageFactor false := by
        have sum3 (a : Compass) (t : ℚ) : (∑ d : Compass, if d ≠ a then t else 0) = 3 * t := by
          have hu : (Finset.univ : Finset Compass) = {.east, .north, .west, .south} := rfl
          cases a <;> simp [hu] <;> ring
        rw [sum3]
        ring
  · have he (d : Compass) : ¬IsTrail u incoming (snoc w d) := by
      intro ht
      exact hw (by simpa using trail_initWord u incoming (snoc w d) ht)
    simp [hw, he]

/-- The elementary three-choice estimate is valid at every length. -/
theorem total_majorant (n : ℕ) (u : Plane) (incoming : Compass) :
    openTrailTotal n u incoming ≤ passageFactor false ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    exact (total_step n u incoming).trans (by
      simpa [pow_succ] using mul_le_mul_of_nonneg_right ih
        (by norm_num [passageFactor, localThreshold] : 0 ≤ passageFactor false))

theorem lastWindow_admissible {m n : ℕ} (u : Plane) (incoming : Compass)
    (w : DirectionWord n) (d : Compass) (hm : 1 ≤ m) (hmn : m ≤ n)
    (hw : IsTrail u incoming (snoc w d)) : WindowAdmissible (lastWindowWord m w) d := by
  constructor
  · rw [lastWindow_arrival incoming w hm hmn]
    exact snoc_nonreverse u incoming w d hw
  · intro i he
    have hs := lastWindow_slice w hmn
    let a := n - m
    let t := wordVertex u w a
    have hv : wordVertex (0, 0) (lastWindowWord m w) m = wordVertex u w n - t := by
      rw [hs, slice_vertex u w (n - m) m (by omega) m le_rfl]
      simp only [Nat.sub_add_cancel hmn]
      rfl
    have hb := slice_bond u w (n - m) m (by omega) i
    rw [← hs] at hb
    have he' : (wordBond u w ⟨a + i.val, by dsimp [a]; omega⟩).image (fun x => x - t) =
        ({wordVertex u w n, wordVertex u w n + d.step} : Finset Plane).image (fun x => x - t) := by
      rw [← hb]
      rw [he, hv]
      simp only [Finset.image_insert, Finset.image_singleton]
      congr 1
      abel_nf
    have hf := snoc_fresh u incoming w d hw ⟨a + i.val, by dsimp [a]; omega⟩
    exact hf (Finset.image_injective (fun x y hxy => sub_left_inj.mp hxy) he')

theorem window_revisit_true {m n : ℕ} (u : Plane) (w : DirectionWord n)
    (hmn : m ≤ n)
    (hr : 0 < departureCount (0, 0) (lastWindowWord m w) m
      (wordVertex (0, 0) (lastWindowWord m w) m)) :
    0 < departureCount u w n (wordVertex u w n) := by
  rw [departureCount, Finset.card_pos] at hr ⊢
  obtain ⟨j, hj⟩ := hr
  simp only [Finset.mem_filter, Finset.mem_range, min_self] at hj
  refine ⟨n - m + j, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_range, min_self]
  refine ⟨by omega, ?_⟩
  rw [lastWindow_slice w hmn,
    slice_vertex u w (n - m) m (by omega) j (by omega),
    slice_vertex u w (n - m) m (by omega) m le_rfl,
    Nat.sub_add_cancel hmn] at hj
  exact sub_left_inj.mp hj.2

theorem factor_memory_le {m n : ℕ} (u : Plane) (incoming : Compass)
    (w : DirectionWord n) (d : Compass) (hm : 1 ≤ m) (hmn : m ≤ n) :
    nextFactor u incoming w d ≤ kindWeight (windowKind (lastWindowWord m w) d) := by
  unfold windowKind
  split_ifs with hr hs
  · have ht := window_revisit_true u w hmn hr
    simp [nextFactor, ht, kindWeight]
  · rw [lastWindow_arrival incoming w hm hmn] at hs
    unfold nextFactor
    split_ifs <;> norm_num [hs, kindWeight, passageFactor, localThreshold]
  · rw [lastWindow_arrival incoming w hm hmn] at hs
    unfold nextFactor
    split_ifs <;> norm_num [hs, kindWeight, passageFactor, localThreshold]

end AKLT.Cert.H2
