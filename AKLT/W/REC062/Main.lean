import AKLT.Blueprint.Rec.NodesKernel

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC062

private theorem latticeDist_symm (a b : Plane) : latticeDist a b = latticeDist b a := by
  unfold latticeDist
  have h₁ : b.1 - a.1 = -(a.1 - b.1) := by ring
  have h₂ : b.2 - a.2 = -(a.2 - b.2) := by ring
  rw [h₁, h₂, Int.natAbs_neg, Int.natAbs_neg]

private theorem latticeDist_triangle (a b c : Plane) :
    latticeDist a b ≤ latticeDist a c + latticeDist c b := by
  unfold latticeDist
  have h₁ := Int.natAbs_add_le (a.1 - c.1) (c.1 - b.1)
  have h₂ := Int.natAbs_add_le (a.2 - c.2) (c.2 - b.2)
  have h₁' : (a.1 - b.1).natAbs ≤ (a.1 - c.1).natAbs + (c.1 - b.1).natAbs := by
    convert h₁ using 1 <;> ring_nf
  have h₂' : (a.2 - b.2).natAbs ≤ (a.2 - c.2).natAbs + (c.2 - b.2).natAbs := by
    convert h₂ using 1 <;> ring_nf
  omega

private theorem wordVertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n)
    (j : ℕ) (hj : j < n) :
    wordVertex u w (j + 1) = wordVertex u w j + (w ⟨j, hj⟩).step := by
  unfold wordVertex
  let m : Fin n := ⟨j, hj⟩
  have hpoint : ∀ k : Fin n,
      (if k.val < j + 1 then (w k).step else 0) =
        (if k.val < j then (w k).step else 0) + (if k = m then (w k).step else 0) := by
    intro k
    by_cases hk : k = m
    · subst k
      simp [m]
    · have hkval : k.val ≠ j := by
        intro he
        apply hk
        exact Fin.ext he
      by_cases hlt : k.val < j
      · have hsucc : k.val < j + 1 := by omega
        simp [hlt, hsucc, hk]
      · have hnot : ¬ k.val < j + 1 := by omega
        simp [hlt, hnot, hk]
  calc
    u + (∑ k : Fin n, if k.val < j + 1 then (w k).step else 0)
        = u + (∑ k : Fin n,
          ((if k.val < j then (w k).step else 0) +
            (if k = m then (w k).step else 0))) := by
              congr 1
              exact Finset.sum_congr rfl (fun k hk => hpoint k)
    _ = u + ((∑ k : Fin n, if k.val < j then (w k).step else 0) +
          ∑ k : Fin n, if k = m then (w k).step else 0) := by rw [Finset.sum_add_distrib]
    _ = u + (∑ k : Fin n, if k.val < j then (w k).step else 0) + (w m).step := by
      simp [m, add_assoc]

private theorem wordVertex_step_dist {n : ℕ} (u : Plane) (w : DirectionWord n)
    (j : ℕ) (hj : j < n) :
    latticeDist (wordVertex u w (j + 1)) (wordVertex u w j) = 1 := by
  rw [wordVertex_succ u w j hj]
  cases hdir : w ⟨j, hj⟩ <;>
    simp [latticeDist, Compass.step, hdir] <;> norm_num

private theorem wordVertex_dist_le {n : ℕ} (u : Plane) (w : DirectionWord n)
    (i j : ℕ) (hij : i ≤ j) (hjn : j ≤ n) :
    latticeDist (wordVertex u w i) (wordVertex u w j) ≤ j - i := by
  induction j generalizing i with
  | zero =>
      have hi : i = 0 := by omega
      subst i
      simp [latticeDist]
  | succ j ih =>
      by_cases h : i ≤ j
      · have hprev := ih i h (by omega)
        have hstep : latticeDist (wordVertex u w (j + 1)) (wordVertex u w j) = 1 :=
          wordVertex_step_dist u w j (by omega)
        calc
          latticeDist (wordVertex u w i) (wordVertex u w (j + 1))
              ≤ latticeDist (wordVertex u w i) (wordVertex u w j) +
                  latticeDist (wordVertex u w j) (wordVertex u w (j + 1)) :=
                latticeDist_triangle _ _ _
          _ = latticeDist (wordVertex u w i) (wordVertex u w j) + 1 := by
                have hstep' : latticeDist (wordVertex u w j) (wordVertex u w (j + 1)) = 1 := by
                  rw [latticeDist_symm]
                  exact hstep
                rw [hstep']
          _ ≤ (j - i) + 1 := Nat.add_le_add_right hprev 1
          _ = j + 1 - i := by omega
      · have hi : i = j + 1 := by omega
        subst i
        simp [latticeDist]

private theorem neighbours_dist_one {x z : Plane} (hz : z ∈ neighbours x) :
    latticeDist z x = 1 := by
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and] at hz
  rcases hz with ⟨d, rfl⟩
  cases d <;> simp [latticeDist, Compass.step] <;> norm_num

private theorem pair_site_neighbour {n : ℕ} (w : DirectionWord n) (i : Fin n)
    (z : Plane) (hz : z ∈ insert (wordVertex kernelStart w (i.val + 1))
      (liveOtherNeighbours w i)) :
    z ∈ neighbours (wordVertex kernelStart w i.val) := by
  classical
  rcases Finset.mem_insert.mp hz with hz | hz
  · subst z
    have hstep := wordVertex_succ kernelStart w i.val i.isLt
    rw [hstep]
    exact Finset.mem_image.mpr ⟨w i, Finset.mem_univ _, rfl⟩
  · have hfilter := Finset.mem_filter.mp hz
    have hresponse : z ∈ responseNeighbours w i := (Finset.mem_erase.mp hfilter.1).2
    exact (Finset.mem_erase.mp hresponse).2

private theorem shift_nat_bound {n : ℕ} (X : PairType) (w : DirectionWord n)
    (hclosed : ClosedTrail X w) (i : Fin n) (p : Finset Plane)
    (hp : p ∈ responsePairs w i) : pairShift X p ≤ n / 2 + 1 := by
  have htarget : wordVertex kernelStart w n = kernelTarget X := hclosed.2.1
  have hstart : latticeDist (wordVertex kernelStart w 0)
      (wordVertex kernelStart w i.val) ≤ i.val := by
    simpa [wordVertex] using
      (wordVertex_dist_le kernelStart w 0 i.val (Nat.zero_le _) (Nat.le_of_lt i.isLt))
  have hstart' : latticeDist (wordVertex kernelStart w i.val) kernelStart ≤ i.val := by
    have hzero : wordVertex kernelStart w 0 = kernelStart := by simp [wordVertex]
    calc
      latticeDist (wordVertex kernelStart w i.val) kernelStart =
          latticeDist (wordVertex kernelStart w i.val) (wordVertex kernelStart w 0) := by rw [hzero]
      _ = latticeDist (wordVertex kernelStart w 0) (wordVertex kernelStart w i.val) :=
          latticeDist_symm _ _
      _ ≤ i.val := hstart
  have htargetdist : latticeDist (wordVertex kernelStart w i.val)
      (wordVertex kernelStart w n) ≤ n - i.val :=
    wordVertex_dist_le kernelStart w i.val n (Nat.le_of_lt i.isLt) (Nat.le_refl _)
  have hpSubset := (Finset.mem_powersetCard.mp hp).1
  unfold pairShift
  apply Finset.sup_le_iff.mpr
  intro z hz
  have hzBase := hpSubset hz
  have hneigh : z ∈ neighbours (wordVertex kernelStart w i.val) :=
    pair_site_neighbour w i z hzBase
  have hstepdist : latticeDist z (wordVertex kernelStart w i.val) = 1 :=
    neighbours_dist_one hneigh
  have hleft : latticeDist z kernelStart ≤ i.val + 1 := by
    calc
      latticeDist z kernelStart ≤
          latticeDist z (wordVertex kernelStart w i.val) +
            latticeDist (wordVertex kernelStart w i.val) kernelStart :=
          latticeDist_triangle _ _ _
      _ ≤ 1 + i.val := by rw [hstepdist]; exact Nat.add_le_add_left hstart' 1
      _ = i.val + 1 := by omega
  have hright : latticeDist z (kernelTarget X) ≤ n - i.val + 1 := by
    rw [← htarget]
    calc
      latticeDist z (wordVertex kernelStart w n)
          ≤ latticeDist z (wordVertex kernelStart w i.val) +
              latticeDist (wordVertex kernelStart w i.val) (wordVertex kernelStart w n) :=
            latticeDist_triangle _ _ _
      _ ≤ 1 + (n - i.val) := by rw [hstepdist]; exact Nat.add_le_add_left htargetdist 1
      _ = n - i.val + 1 := by omega
  by_cases hmid : 2 * i.val ≤ n
  · have hi : i.val ≤ n / 2 := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
    exact ((Nat.min_le_left _ _).trans hleft).trans (Nat.add_le_add_right hi 1)
  · have hrest : n - i.val ≤ n / 2 := by
      apply (Nat.le_div_iff_mul_le (by omega)).2
      omega
    exact ((Nat.min_le_right _ _).trans hright).trans (Nat.add_le_add_right hrest 1)

theorem main : AKLT.Blueprint.Rec.ShiftGeometryStatement := by
  intro n X w hclosed i p hp
  have hnat := shift_nat_bound X w hclosed i p hp
  have hcast : (pairShift X p : ℝ) ≤ ((n / 2 + 1 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hdivNat : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2
  have hdiv : ((n / 2 : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
    have hdiv' : ((n / 2 : ℕ) : ℝ) * 2 ≤ (n : ℝ) := by exact_mod_cast hdivNat
    linarith
  norm_num at hcast ⊢
  linarith

end AKLT.W.REC062

#print axioms AKLT.W.REC062.main
