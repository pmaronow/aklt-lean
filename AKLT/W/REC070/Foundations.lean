import AKLT.Blueprint.Rec.NodesKernel
import AKLT.Cert.H2.Words

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC070

set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

lemma factor_one_le (b : Bool) : (1 : ℚ) ≤ passageFactor b := by
  cases b <;> norm_num [passageFactor, localThreshold]

lemma pairCoefficient_nonneg {n : ℕ} (w : DirectionWord n) (i : Fin n) (p : Finset Plane) :
    0 ≤ pairCoefficient w i p := by
  unfold pairCoefficient
  split_ifs <;> cases wordStraight kernelIncoming w i <;>
    norm_num [alphaBound, betaBound, betaPrimeBound]

lemma exposure_nonneg {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ)
    (hr : ∀ i, 0 ≤ r i) (l : List (Fin n)) : 0 ≤ exposureSum w r l := by
  induction l with
  | nil => simp [exposureSum]
  | cons i l ih =>
    exact mul_nonneg (le_trans (by norm_num) (factor_one_le _)) (add_nonneg (hr i) ih)

lemma base_nonneg {n : ℕ} (w : DirectionWord n) : 0 ≤ trailBaseWeight kernelStart w := by
  unfold trailBaseWeight
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> norm_num

lemma kappa_nonneg {n : ℕ} (X Y : PairType) (s : ℕ) (w : DirectionWord n) (i : Fin n) :
    0 ≤ responseKappa X Y s w i := by
  apply Finset.sum_nonneg
  intro p _
  split_ifs
  · exact pairCoefficient_nonneg w i p
  · rfl

lemma coefficient_nonneg (X Y : PairType) (s n : ℕ) :
    0 ≤ kernelLengthCoefficient X Y s n := by
  unfold kernelLengthCoefficient
  apply Finset.sum_nonneg
  intro w _
  split_ifs
  · exact mul_nonneg (base_nonneg w) (exposure_nonneg w _ (kappa_nonneg X Y s w) _)
  · rfl

lemma ordering_perm {n : ℕ} (w : DirectionWord n) :
    (kernelOrdering w).Perm (firstVisitList w) := by
  unfold kernelOrdering
  split_ifs
  · exact List.mergeSort_perm _ _
  · exact List.filter_append_perm _ _

lemma ordering_nodup {n : ℕ} (w : DirectionWord n) : (kernelOrdering w).Nodup :=
  (ordering_perm w).nodup_iff.mpr ((List.nodup_finRange n).filter _)

lemma ordering_length {n : ℕ} (w : DirectionWord n) : (kernelOrdering w).length ≤ n := by
  rw [(ordering_perm w).length_eq]
  exact (List.length_filter_le _ _).trans (by simp)

lemma lattice_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  have h1 := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
  have h2 := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
  have he1 : x.1 - y.1 + (y.1 - z.1) = x.1 - z.1 := by ring
  have he2 : x.2 - y.2 + (y.2 - z.2) = x.2 - z.2 := by ring
  rw [he1] at h1
  rw [he2] at h2
  unfold latticeDist
  omega

lemma lattice_symm (x y : Plane) : latticeDist x y = latticeDist y x := by
  unfold latticeDist
  omega

lemma neighbour_dist (v z : Plane) (hz : z ∈ neighbours v) : latticeDist z v = 1 := by
  obtain ⟨d, _, rfl⟩ := Finset.mem_image.mp hz
  cases d <;> simp [latticeDist, Compass.step]

lemma vertex_dist {n : ℕ} (w : DirectionWord n) (j : ℕ) (hj : j ≤ n) :
    latticeDist (wordVertex kernelStart w j) kernelStart ≤ j := by
  induction j with
  | zero => simp [AKLT.Cert.H2.vertex_zero, latticeDist]
  | succ j ih =>
    rw [AKLT.Cert.H2.vertex_succ _ _ j (by omega)]
    apply (lattice_triangle _ (wordVertex kernelStart w j) _).trans
    have hn : wordVertex kernelStart w j + (w ⟨j, by omega⟩).step ∈
        neighbours (wordVertex kernelStart w j) := by
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    rw [neighbour_dist _ _ hn]
    have := ih (by omega)
    omega

lemma response_near {n : ℕ} (w : DirectionWord n) (i : Fin n)
    (p : Finset Plane) (hp : p ∈ responsePairs w i) {z : Plane} (hz : z ∈ p) :
    z ∈ neighbours (wordVertex kernelStart w i.val) := by
  have hsub := (Finset.mem_powersetCard.mp hp).1 hz
  rcases Finset.mem_insert.mp hsub with he | he
  · subst z
    rw [AKLT.Cert.H2.vertex_succ _ _ i.val i.isLt]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_filter.mp he).1)

lemma pairShift_le {n : ℕ} (X : PairType) (w : DirectionWord n) (i : Fin n)
    (p : Finset Plane) (hp : p ∈ responsePairs w i) : pairShift X p ≤ n + 1 := by
  apply Finset.sup_le
  intro z hz
  apply (min_le_left _ _).trans
  apply (lattice_triangle _ (wordVertex kernelStart w i.val) _).trans
  rw [neighbour_dist _ _ (response_near w i p hp hz)]
  have := vertex_dist w i.val (Nat.le_of_lt i.isLt)
  omega

lemma coefficient_support (X Y : PairType) (n s : ℕ) (hs : n + 1 < s) :
    kernelLengthCoefficient X Y s n = 0 := by
  have hk (w : DirectionWord n) (i : Fin n) : responseKappa X Y s w i = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    have hne : pairShift X p ≠ s := by have := pairShift_le X w i p hp; omega
    simp [hne]
  have he (w : DirectionWord n) (l : List (Fin n)) : exposureSum w (responseKappa X Y s w) l = 0 := by
    induction l with
    | nil => rfl
    | cons i l ih => simp [exposureSum, hk, ih]
  simp [kernelLengthCoefficient, he]

end AKLT.W.REC070
