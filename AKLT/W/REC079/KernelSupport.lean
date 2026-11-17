module
public import AKLT.W.REC079.KernelAlgebra

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec AKLT.Cert.H2

namespace AKLT.W.REC079

attribute [local instance] Classical.propDecidable

theorem latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  have h₁ := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
  have h₂ := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
  simp only [sub_add_sub_cancel] at h₁ h₂
  unfold latticeDist
  omega

@[simp] theorem latticeDist_symm (x y : Plane) : latticeDist x y = latticeDist y x := by
  unfold latticeDist
  omega

@[simp] theorem latticeDist_step (x : Plane) (a : Compass) :
    latticeDist (x + a.step) x = 1 := by cases a <;> simp [latticeDist, Compass.step]

/-- Every word vertex lies within its prefix length, without a trail hypothesis. -/
theorem vertex_distance_le {n : ℕ} (u : Plane) (w : DirectionWord n) (j : ℕ) (hj : j ≤ n) :
    latticeDist (wordVertex u w j) u ≤ j := by
  induction j with
  | zero => simp [latticeDist]
  | succ j ih =>
    rw [vertex_succ u w j (by omega)]
    exact (latticeDist_triangle _ (wordVertex u w j) u).trans
      (by rw [latticeDist_step]; have := ih (by omega); omega)

/-- Every pair counted by the kernel has its actual shift inside the frozen
finite range. This also applies to words that are not trails. -/
theorem responsePair_shift_le {n : ℕ} (X : PairType) (w : DirectionWord n) (i : Fin n)
    (p : Finset Plane) (hp : p ∈ responsePairs w i) : pairShift X p ≤ n + 1 := by
  apply Finset.sup_le
  intro z hz
  have hs : p ⊆ insert (wordVertex kernelStart w (i.val + 1)) (liveOtherNeighbours w i) :=
    (Finset.mem_powersetCard.mp hp).1
  have hz' := hs hz
  rcases Finset.mem_insert.mp hz' with hz' | hz'
  · subst z
    exact (min_le_left _ _).trans ((vertex_distance_le kernelStart w (i.val + 1) (by omega)).trans (by omega))
  · have hn : z ∈ neighbours (wordVertex kernelStart w i.val) := by
      exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_filter.mp hz').1)
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hn
    apply (min_le_left _ _).trans
    exact (latticeDist_triangle _ (wordVertex kernelStart w i.val) kernelStart).trans
      (by rw [latticeDist_step]; have := vertex_distance_le kernelStart w i.val (by omega); omega)

/-- Real response envelopes are nonnegative even before their boundedness is
proved; the unbounded real supremum convention is also zero. -/
theorem responseEnvelope_nonneg (X : PairType) (d : ℤ) : 0 ≤ responseEnvelope X d := by
  apply Real.sSup_nonneg
  rintro r (hr | ⟨G, τ, D, u, v, c, hp, hd, rfl⟩)
  · have : r = 0 := hr
    simp [this]
  · exact abs_nonneg _

theorem pairCoefficient_nonneg {n : ℕ} (w : DirectionWord n) (i : Fin n) (p : Finset Plane) :
    0 ≤ pairCoefficient w i p := by
  unfold pairCoefficient
  split_ifs <;> cases h : wordStraight kernelIncoming w i <;>
    norm_num [alphaBound, betaBound, betaPrimeBound]

theorem trailBaseWeight_nonneg {n : ℕ} (u : Plane) (w : DirectionWord n) :
    0 ≤ trailBaseWeight u w := by
  unfold trailBaseWeight
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> norm_num

/-- The ungrouped live-pair reward, keeping the actual type and shift. -/
def pairReward {n : ℕ} (X : PairType) (d : ℕ) (w : DirectionWord n) (i : Fin n) : ℝ :=
  ∑ p ∈ responsePairs w i, (pairCoefficient w i p : ℝ) *
    responseEnvelope (responsePairType p) ((d : ℤ) - pairShift X p)

/-- Regrouping by type and shift does not alter any departure reward. -/
theorem indexedReward_eq_pairReward {n : ℕ} (X : PairType) (d : ℕ)
    (w : DirectionWord n) (i : Fin n) : indexedReward X d w i = pairReward X d w i := by
  unfold indexedReward responseKappa pairReward
  simp only [Rat.cast_sum, apply_ite, Rat.cast_zero, Finset.sum_mul]
  simp_rw [Finset.sum_comm (s := Finset.range (n + 2)) (t := responsePairs w i)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  have hs : pairShift X p ∈ Finset.range (n + 2) :=
    Finset.mem_range.mpr (by have := responsePair_shift_le X w i p hp; omega)
  simp [ite_and, eq_comm, hs]

theorem indexedReward_nonneg {n : ℕ} (X : PairType) (d : ℕ) (w : DirectionWord n) (i : Fin n) :
    0 ≤ indexedReward X d w i := by
  rw [indexedReward_eq_pairReward]
  exact Finset.sum_nonneg fun p _ => mul_nonneg
    (Rat.cast_nonneg.mpr (pairCoefficient_nonneg w i p)) (responseEnvelope_nonneg _ _)

theorem canonicalBudget_nonneg {n : ℕ} (X : PairType) (d : ℕ) (w : DirectionWord n) :
    0 ≤ canonicalBudget X d w :=
  mul_nonneg (Rat.cast_nonneg.mpr (trailBaseWeight_nonneg _ _))
    (realExposure_nonneg _ _ (indexedReward_nonneg X d w) _)

end AKLT.W.REC079
