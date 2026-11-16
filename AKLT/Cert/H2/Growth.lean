import AKLT.Cert.H2.Mass
import AKLT.Gen.Bellman.Growth

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Cert.H2

set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

theorem ratio_pos {m : ℕ} (v : MemoryWindow m → ℝ) (hv : ∀ ω, 0 < v ω) :
    0 < memoryWitnessRatio v := by
  obtain ⟨i, hi⟩ := (Set.range_nonempty v).csInf_mem (Set.finite_range v)
  obtain ⟨j, hj⟩ := (Set.range_nonempty v).csSup_mem (Set.finite_range v)
  unfold memoryWitnessRatio
  rw [← hi, ← hj]
  exact div_pos (hv j) (hv i)

theorem inf_pos {m : ℕ} (v : MemoryWindow m → ℝ) (hv : ∀ ω, 0 < v ω) :
    0 < sInf (Set.range v) := by
  obtain ⟨i, hi⟩ := (Set.range_nonempty v).csInf_mem (Set.finite_range v)
  rw [← hi]
  exact hv i

theorem prefix_set_finite (m : ℕ) (q : ℝ) :
    {r : ℝ | ∃ j < m, r = (openTrailTotal j (0, 0) .east : ℝ) * q ^ (-(j : ℤ))}.Finite := by
  apply Set.Finite.subset (s := (fun j : Fin m =>
    (openTrailTotal j.val (0, 0) .east : ℝ) * q ^ (-(j.val : ℤ))) '' Set.univ)
    (Set.finite_univ.image _)
  rintro r ⟨j, hj, rfl⟩
  exact ⟨⟨j, hj⟩, Set.mem_univ _, rfl⟩

theorem prefix_le_base {m : ℕ} (v : MemoryWindow m → ℝ) (q : ℝ) (r : ℕ) (hr : r < m) :
    (openTrailTotal r (0, 0) .east : ℝ) * q ^ (-(r : ℤ)) ≤ memoryBaseConstant m q v := by
  exact (le_csSup (prefix_set_finite m q).bddAbove ⟨r, hr, rfl⟩).trans (le_max_left _ _)

theorem base_ge_one {m : ℕ} (hm : 1 ≤ m) (v : MemoryWindow m → ℝ) (q : ℝ) :
    1 ≤ memoryBaseConstant m q v := by
  simpa using prefix_le_base v q 0 (by omega)

theorem total_cast (n : ℕ) (u : Plane) (incoming : Compass) :
    (openTrailTotal n u incoming : ℝ) =
      ∑ w : DirectionWord n, if IsTrail u incoming w then (trailWeight u incoming w : ℝ) else 0 := by
  simp only [openTrailTotal, Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro w _
  split_ifs <;> simp

theorem base_trail_bound {m : ℕ} (hm : 1 ≤ m) (v : MemoryWindow m → ℝ)
    (hv : ∀ ω, 0 < v ω) (q : ℝ) (hq : 0 < q)
    (hw : ∀ ω, (∑ ω', (memoryMatrix m ω ω' : ℝ) * v ω') ≤ q * v ω) :
    ∀ n : ℕ, ∀ u : Plane, ∀ incoming : Compass,
      (openTrailTotal n u incoming : ℝ) ≤ memoryBaseConstant m q v * q ^ n := by
  intro n u incoming
  rw [total_uniform n u incoming]
  by_cases hn : n < m
  · have hp := prefix_le_base v q n hn
    rw [zpow_neg, zpow_natCast, ← div_eq_mul_inv] at hp
    exact (div_le_iff₀ (pow_pos hq n)).mp hp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hn)
    let M : MemoryWindow m → MemoryWindow m → ℝ := fun ω ω' => memoryMatrix m ω ω'
    let A : ℕ → MemoryWindow m → ℝ := fun j ω => memoryTrailMass m (m + j) (0, 0) .east ω
    have ha : ∀ j ω, 0 ≤ A j ω := by
      intro j ω
      dsimp only [A]
      exact_mod_cast mass_nonneg m (m + j) (0, 0) .east ω
    have hs : ∀ j ω', A (j + 1) ω' ≤ ∑ ω, A j ω * M ω ω' := by
      intro j ω'
      have hh := mass_step hm (show m ≤ m + j by omega) (0, 0) .east ω'
      dsimp only [A, M]
      rw [← Nat.add_assoc]
      exact_mod_cast hh
    have hg := AKLT.Gen.Bellman.mass_growth M A v q (sInf (Set.range v)) (sSup (Set.range v))
      hq.le (inf_pos v hv) ha
      (fun ω => csInf_le (Set.finite_range v).bddBelow (Set.mem_range_self ω))
      (fun ω => le_csSup (Set.finite_range v).bddAbove (Set.mem_range_self ω)) hs hw k
    have htot (j : ℕ) : (∑ ω, A j ω) = (openTrailTotal (m + j) (0, 0) .east : ℝ) := by
      dsimp only [A]
      exact_mod_cast mass_total (show m ≤ m + j by omega) (0, 0) .east
    rw [htot k, htot 0, Nat.add_zero] at hg
    have hb : memoryWitnessRatio v * (openTrailTotal m (0, 0) .east : ℝ) / q ^ m ≤
        memoryBaseConstant m q v := by
      simpa only [memoryBaseConstant, zpow_neg, zpow_natCast, div_eq_mul_inv] using
        (le_max_right
          (sSup {r : ℝ | ∃ j < m, r = (openTrailTotal j (0, 0) .east : ℝ) * q ^ (-(j : ℤ))})
          (memoryWitnessRatio v * (openTrailTotal m (0, 0) .east : ℝ) * q ^ (-(m : ℤ))))
    calc
      (openTrailTotal (m + k) (0, 0) .east : ℝ) ≤
          memoryWitnessRatio v * (openTrailTotal m (0, 0) .east : ℝ) * q ^ k := hg
      _ ≤ (memoryBaseConstant m q v * q ^ m) * q ^ k :=
        mul_le_mul_of_nonneg_right ((div_le_iff₀ (pow_pos hq m)).mp hb) (pow_nonneg hq.le k)
      _ = memoryBaseConstant m q v * q ^ (m + k) := by rw [pow_add]; ring

theorem bound_mono {C D q : ℝ} (h : OpenTrailBound C q) (hCD : C ≤ D) :
    OpenTrailBound D q := by
  refine ⟨h.1.trans hCD, h.2.1, h.2.2.1, ?_⟩
  intro n u incoming
  exact (h.2.2.2 n u incoming).trans
    (mul_le_mul_of_nonneg_right hCD (pow_nonneg h.2.1.le n))

/-- The full Top ALM contract, for every positive memory length. -/
theorem alm : AKLT.Blueprint.Top.ALMStatement := by
  intro m hm
  refine ⟨?_, ?_⟩
  · intro n hn u incoming ω'
    exact mass_step hm hn u incoming ω'
  · intro v hv q hq hq1 hw
    have hb : OpenTrailBound (memoryBaseConstant m q v) q := by
      refine ⟨base_ge_one hm v q, hq, hq1, ?_⟩
      intro n u incoming
      rw [← total_cast]
      exact base_trail_bound hm v hv q hq hw n u incoming
    exact ⟨hb, fun _ hC => bound_mono hb hC⟩

end AKLT.Cert.H2
