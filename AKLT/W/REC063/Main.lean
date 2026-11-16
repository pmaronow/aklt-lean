import AKLT.Cert.H2.Words
import AKLT.Blueprint.Rec.NodesKernel

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC063

private theorem latticeDist_add_le (x y z : Plane) :
    latticeDist (x + y) z ≤ latticeDist x z + latticeDist y (0, 0) := by
  unfold latticeDist
  have hx : (x.1 + y.1 - z.1).natAbs ≤ (x.1 - z.1).natAbs + y.1.natAbs := by
    have h : x.1 + y.1 - z.1 = (x.1 - z.1) + y.1 := by omega
    rw [h]
    exact Int.natAbs_add_le _ _
  have hy : (x.2 + y.2 - z.2).natAbs ≤ (x.2 - z.2).natAbs + y.2.natAbs := by
    have h : x.2 + y.2 - z.2 = (x.2 - z.2) + y.2 := by omega
    rw [h]
    exact Int.natAbs_add_le _ _
  dsimp [latticeDist] at hx hy ⊢
  omega

private theorem step_distance (d : Compass) : latticeDist d.step (0, 0) = 1 := by
  cases d <;> norm_num [latticeDist, Compass.step]

private theorem vertex_distance_bound {n : ℕ} (w : DirectionWord n) :
    ∀ j ≤ n, latticeDist (wordVertex kernelStart w j) kernelStart ≤ j := by
  intro j hj
  induction j with
  | zero => simp [AKLT.Cert.H2.vertex_zero, latticeDist, kernelStart]
  | succ j ih =>
      have hjn : j < n := by omega
      rw [AKLT.Cert.H2.vertex_succ kernelStart w j hjn]
      calc
        latticeDist (wordVertex kernelStart w j + (w ⟨j, hjn⟩).step) kernelStart
            ≤ latticeDist (wordVertex kernelStart w j) kernelStart +
                latticeDist (w ⟨j, hjn⟩).step (0, 0) := latticeDist_add_le _ _ _
        _ = latticeDist (wordVertex kernelStart w j) kernelStart + 1 := by
              rw [step_distance]
        _ ≤ j + 1 := Nat.add_le_add_right (ih (by omega)) 1

private theorem neighbor_distance_bound {n : ℕ} (w : DirectionWord n) (i : Fin n)
    {z : Plane} (hz : z ∈ neighbours (wordVertex kernelStart w i.val)) :
    latticeDist z kernelStart ≤ i.val + 1 := by
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and] at hz
  rcases hz with ⟨d, rfl⟩
  calc
    latticeDist (wordVertex kernelStart w i.val + d.step) kernelStart
        ≤ latticeDist (wordVertex kernelStart w i.val) kernelStart +
            latticeDist d.step (0, 0) := latticeDist_add_le _ _ _
    _ = latticeDist (wordVertex kernelStart w i.val) kernelStart + 1 := by
          rw [step_distance]
    _ ≤ i.val + 1 := Nat.add_le_add_right
          (vertex_distance_bound w i.val (by omega)) 1

private theorem responsePairs_subset_neighbors {n : ℕ} (w : DirectionWord n) (i : Fin n)
    (p : Finset Plane) (hp : p ∈ responsePairs w i) :
    p ⊆ neighbours (wordVertex kernelStart w i.val) := by
  classical
  intro z hz
  have hz' : z ∈ insert (wordVertex kernelStart w (i.val + 1)) (liveOtherNeighbours w i) :=
    (Finset.mem_powersetCard.mp (by simpa [responsePairs] using hp)).1 hz
  rcases Finset.mem_insert.mp hz' with hout | hother
  · subst z
    change wordVertex kernelStart w (i.val + 1) ∈
      Finset.univ.image (fun d : Compass => wordVertex kernelStart w i.val + d.step)
    rw [AKLT.Cert.H2.vertex_succ kernelStart w i.val (by omega)]
    exact Finset.mem_image.mpr ⟨w i, Finset.mem_univ _, rfl⟩
  · have hresp : z ∈ responseNeighbours w i := by
      change z ∈ ((responseNeighbours w i).erase
        (wordVertex kernelStart w (i.val + 1))).filter (fun z => ¬deadAt w i z) at hother
      have hf := Finset.mem_filter.mp hother
      exact (Finset.mem_erase.mp hf.1).2
    have hneigh : z ∈ neighbours (wordVertex kernelStart w i.val) := by
      exact (Finset.mem_erase.mp (show z ∈ (neighbours (wordVertex kernelStart w i.val)).erase
        (wordVertex kernelStart w i.val - (wordIncoming kernelIncoming w i).step) by
          exact hresp)).2
    exact hneigh

private theorem pairShift_le_departure {n : ℕ} (X : PairType) (w : DirectionWord n)
    (i : Fin n) (p : Finset Plane) (hp : p ∈ responsePairs w i) :
    pairShift X p ≤ i.val + 1 := by
  unfold pairShift
  apply Finset.sup_le
  intro z hz
  exact le_trans (min_le_left _ _) (neighbor_distance_bound w i
    (responsePairs_subset_neighbors w i p hp hz))

private theorem responseKappa_zero_of_large_shift {n : ℕ} (X Y : PairType)
    (w : DirectionWord n) (i : Fin n) (s : ℕ) (hs : n + 1 < s) :
    responseKappa X Y s w i = 0 := by
  unfold responseKappa
  apply Finset.sum_eq_zero
  intro p hp
  by_cases h : responsePairType p = Y ∧ pairShift X p = s
  · have hshift := h.2
    have hbound := pairShift_le_departure X w i p hp
    have : i.val + 1 < s := by omega
    have : pairShift X p < s := by omega
    omega
  · simp [h]

private theorem exposureSum_eq_zero {n : ℕ} (w : DirectionWord n) (reward : Fin n → ℚ)
    (h : ∀ i, reward i = 0) (l : List (Fin n)) : exposureSum w reward l = 0 := by
  induction l with
  | nil => rfl
  | cons i rest ih => simp [exposureSum, h i, ih]

private theorem coefficient_zero_of_large_shift (X Y : PairType) (n s : ℕ)
    (hs : n + 1 < s) : kernelLengthCoefficient X Y s n = 0 := by
  unfold kernelLengthCoefficient
  apply Finset.sum_eq_zero
  intro w hw
  by_cases hc : ClosedTrail X w
  · rw [ite_eq_left hc]
    have hk : ∀ i : Fin n, responseKappa X Y s w i = 0 := by
      intro i
      exact responseKappa_zero_of_large_shift X Y w i s hs
    rw [exposureSum_eq_zero w (responseKappa X Y s w) hk]
    simp
  · simp [hc]

private theorem coefficient_zero_at_length_zero (X Y : PairType) (s : ℕ) :
    kernelLengthCoefficient X Y s 0 = 0 := by
  cases X <;> simp [kernelLengthCoefficient, ClosedTrail, AKLT.Cert.H2.vertex_zero,
    kernelStart, kernelTarget]

theorem main : AKLT.Blueprint.Rec.KernelSupportStatement := by
  constructor
  · intro X Y s
    exact coefficient_zero_at_length_zero X Y s
  · intro X Y n s hs
    exact coefficient_zero_of_large_shift X Y n s hs

end AKLT.W.REC063

