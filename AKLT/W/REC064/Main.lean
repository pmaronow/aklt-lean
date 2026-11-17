module
public import AKLT.Blueprint.Rec.NodesKernel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC064

theorem latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  unfold latticeDist
  have h1 := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
  have h2 := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
  have hx : x.1 - z.1 = (x.1 - y.1) + (y.1 - z.1) := by omega
  have hy : x.2 - z.2 = (x.2 - y.2) + (y.2 - z.2) := by omega
  rw [hx, hy]
  calc
    _ ≤ ((x.1 - y.1).natAbs + (y.1 - z.1).natAbs) +
        ((x.2 - y.2).natAbs + (y.2 - z.2).natAbs) := Nat.add_le_add h1 h2
    _ = ((x.1 - y.1).natAbs + (x.2 - y.2).natAbs) +
        ((y.1 - z.1).natAbs + (y.2 - z.2).natAbs) := by omega

theorem latticeDist_symm (x y : Plane) : latticeDist x y = latticeDist y x := by
  unfold latticeDist
  have h1 : y.1 - x.1 = -(x.1 - y.1) := by omega
  have h2 : y.2 - x.2 = -(x.2 - y.2) := by omega
  rw [h1, h2, Int.natAbs_neg, Int.natAbs_neg]

theorem wordVertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n) (i : Fin n) :
    wordVertex u w (i.val + 1) = wordVertex u w i.val + (w i).step := by
  classical
  have hpoint (k : Fin n) :
      (if k.val < i.val + 1 then (w k).step else (0 : Plane)) =
        (if k.val < i.val then (w k).step else (0 : Plane)) +
          (if k = i then (w k).step else (0 : Plane)) := by
    by_cases hlt : k.val < i.val
    · have hlt' : k.val < i.val + 1 := by omega
      have hki : k ≠ i := by intro h; subst k; omega
      simp [hlt, hlt', hki]
    · by_cases hki : k = i
      · subst k
        simp
      · have hlt' : ¬ k.val < i.val + 1 := by omega
        simp [hlt, hki, hlt']
  have hsum :
      Finset.univ.sum (fun k : Fin n => if k.val < i.val + 1 then (w k).step else (0 : Plane)) =
        (Finset.univ.sum (fun k : Fin n => if k.val < i.val then (w k).step else (0 : Plane))) +
          (w i).step := by
    calc
      _ = Finset.univ.sum (fun k : Fin n =>
          (if k.val < i.val then (w k).step else (0 : Plane)) +
            (if k = i then (w k).step else (0 : Plane))) := by
          apply Finset.sum_congr rfl
          intro k hk
          exact hpoint k
      _ = (Finset.univ.sum (fun k : Fin n =>
            if k.val < i.val then (w k).step else (0 : Plane))) +
          Finset.univ.sum (fun k : Fin n => if k = i then (w k).step else (0 : Plane)) := by
          rw [Finset.sum_add_distrib]
      _ = (Finset.univ.sum (fun k : Fin n =>
            if k.val < i.val then (w k).step else (0 : Plane))) + (w i).step := by
          simp [Finset.sum_ite_eq']
  unfold wordVertex
  rw [hsum]
  simp [add_assoc]

theorem neighbors_dist_one {x z : Plane} (hz : z ∈ neighbors x) : latticeDist z x = 1 := by
  classical
  unfold neighbors at hz
  rcases Finset.mem_image.mp hz with ⟨d, hd, rfl⟩
  cases d <;> norm_num [latticeDist, Compass.step]

theorem wordVertex_latticeDist_start_le {n : ℕ} (u : Plane) (w : DirectionWord n) (j : ℕ) :
    latticeDist u (wordVertex u w j) ≤ j := by
  classical
  let dx : ℤ := ∑ i : Fin n, if i.val < j then (w i).step.1 else 0
  let dy : ℤ := ∑ i : Fin n, if i.val < j then (w i).step.2 else 0
  have hsumF : (∑ i : Fin n, if i.val < j then (w i).step else (0 : Plane)).1 =
      ∑ i : Fin n, if i.val < j then (w i).step.1 else 0 := by
    rw [Prod.fst_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : i.val < j <;> simp [h]
  have hsumS : (∑ i : Fin n, if i.val < j then (w i).step else (0 : Plane)).2 =
      ∑ i : Fin n, if i.val < j then (w i).step.2 else 0 := by
    rw [Prod.snd_sum]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h : i.val < j <;> simp [h]
  have hv : wordVertex u w j = (u.1 + dx, u.2 + dy) := by
    unfold wordVertex
    apply Prod.ext
    · rw [Prod.fst_add, hsumF]
    · rw [Prod.snd_add, hsumS]
  have hjoint : dx.natAbs + dy.natAbs ≤ ∑ i : Fin n, if i.val < j then 1 else 0 := by
    calc
      dx.natAbs + dy.natAbs ≤
          (∑ i : Fin n, (if i.val < j then (w i).step.1 else 0).natAbs) +
          (∑ i : Fin n, (if i.val < j then (w i).step.2 else 0).natAbs) :=
        Nat.add_le_add (by simpa [dx] using (Int.natAbs_sum_le (Finset.univ : Finset (Fin n))
          (fun i => if i.val < j then (w i).step.1 else 0)))
          (by simpa [dy] using (Int.natAbs_sum_le (Finset.univ : Finset (Fin n))
          (fun i => if i.val < j then (w i).step.2 else 0)))
      _ = ∑ i : Fin n, ((if i.val < j then (w i).step.1 else 0).natAbs +
            (if i.val < j then (w i).step.2 else 0).natAbs) := by rw [← Finset.sum_add_distrib]
      _ = ∑ i : Fin n, if i.val < j then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases h : i.val < j <;> cases w i <;> simp [h, Compass.step]
  have hcnt : (∑ i : Fin n, if i.val < j then 1 else 0) ≤ j := by
    rw [Finset.sum_boole]
    let S : Finset (Fin n) := Finset.univ.filter fun i => i.val < j
    change S.card ≤ j
    have hinj : Set.InjOn Fin.val (↑S : Set (Fin n)) := by
      intro a ha b hb hab
      exact Fin.ext hab
    have himage : Finset.image Fin.val S ⊆ Finset.range j := by
      intro k hk
      rcases Finset.mem_image.mp hk with ⟨i, hi, rfl⟩
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    calc
      S.card = (Finset.image Fin.val S).card := (Finset.card_image_of_injOn hinj).symm
      _ ≤ (Finset.range j).card := Finset.card_le_card himage
      _ = j := Finset.card_range j
  rw [hv]
  unfold latticeDist
  have hx : u.1 - (u.1 + dx) = -dx := by omega
  have hy : u.2 - (u.2 + dy) = -dy := by omega
  rw [hx, hy, Int.natAbs_neg, Int.natAbs_neg]
  exact hjoint.trans hcnt

lemma responsePair_shift_le {n : ℕ} (X : PairType) (w : DirectionWord n)
    (i : Fin n) (p : Finset Plane) (hp : p ∈ responsePairs w i) :
    pairShift X p ≤ n + 1 := by
  classical
  change p.sup (fun z => min (latticeDist z kernelStart) (latticeDist z (kernelTarget X))) ≤ n + 1
  apply Finset.sup_le
  intro z hz
  have hsub : p ⊆ insert (wordVertex kernelStart w (i.val + 1)) (liveOtherNeighbors w i) :=
    (Finset.mem_powersetCard.mp hp).1
  have hneigh : z ∈ neighbors (wordVertex kernelStart w i.val) := by
    rcases Finset.mem_insert.mp (hsub hz) with hnext | hother
    · subst z
      rw [wordVertex_succ]
      exact Finset.mem_image.mpr ⟨w i, Finset.mem_univ _, rfl⟩
    · have hresp : z ∈ responseNeighbors w i := by
        unfold liveOtherNeighbors at hother
        rcases Finset.mem_filter.mp hother with ⟨hrest, _⟩
        exact (Finset.mem_erase.mp hrest).2
      exact Finset.erase_subset _ _ hresp
  have hdist : latticeDist z (wordVertex kernelStart w i.val) = 1 := neighbors_dist_one hneigh
  have hpath := wordVertex_latticeDist_start_le kernelStart w i.val
  calc
    min (latticeDist z kernelStart) (latticeDist z (kernelTarget X)) ≤ latticeDist z kernelStart := Nat.min_le_left _ _
    _ = latticeDist kernelStart z := latticeDist_symm _ _
    _ ≤ latticeDist kernelStart (wordVertex kernelStart w i.val) +
        latticeDist (wordVertex kernelStart w i.val) z := latticeDist_triangle _ _ _
    _ = latticeDist kernelStart (wordVertex kernelStart w i.val) + 1 := by
        rw [latticeDist_symm (wordVertex kernelStart w i.val) z, hdist]
    _ ≤ i.val + 1 := Nat.add_le_add_right hpath 1
    _ ≤ n + 1 := Nat.add_le_add_right i.isLt.le 1


theorem exposureSum_zero_of_reward_zero {n : ℕ} (w : DirectionWord n)
    (reward : Fin n → ℚ) (l : List (Fin n)) (h : ∀ i, reward i = 0) :
    exposureSum w reward l = 0 := by
  induction l with
  | nil => simp [exposureSum]
  | cons i rest ih => simp [exposureSum, h i, ih]

lemma responseKappa_zero_of_shift_gt {n : ℕ} (X Y : PairType) (s : ℕ)
    (w : DirectionWord n) (i : Fin n) (hs : n + 1 < s) :
    responseKappa X Y s w i = 0 := by
  classical
  unfold responseKappa
  apply Finset.sum_eq_zero
  intro p hp
  have hbound := responsePair_shift_le X w i p hp
  have hneq : pairShift X p ≠ s := by omega
  simp [hneq]

theorem kernelLengthCoefficient_zero_of_shift_gt (X Y : PairType) (s n : ℕ)
    (hs : n + 1 < s) : kernelLengthCoefficient X Y s n = 0 := by
  classical
  unfold kernelLengthCoefficient
  apply Finset.sum_eq_zero
  intro w hw
  by_cases hc : ClosedTrail X w
  · have hz : exposureSum w (responseKappa X Y s w) (kernelOrdering w) = 0 :=
      exposureSum_zero_of_reward_zero w (responseKappa X Y s w) (kernelOrdering w)
        (fun i => responseKappa_zero_of_shift_gt X Y s w i hs)
    simp [hc, hz]
  · simp [hc]

theorem kernelLengthCoefficient_zero_at_zero (X Y : PairType) (s : ℕ) :
    kernelLengthCoefficient X Y s 0 = 0 := by
  classical
  unfold kernelLengthCoefficient
  apply Finset.sum_eq_zero
  intro w hw
  have horder : kernelOrdering w = [] := by simp [kernelOrdering, firstVisitList]
  simp [horder, exposureSum]

theorem main : AKLT.Blueprint.Rec.KernelRegroupStatement := by
  intro θ hθ X Y
  have hfinite (n : ℕ) :
      (∑' s : ℕ, ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
          ENNReal.ofReal (θ ^ (-(s : ℤ)))) = shiftedLength θ X Y n := by
    unfold shiftedLength
    rw [tsum_eq_sum (s := Finset.range (n + 2)) (fun s hs => by
      have hnot : ¬ s < n + 2 := by simpa using hs
      have hsn : n + 1 < s := by omega
      rw [kernelLengthCoefficient_zero_of_shift_gt X Y s n hsn]
      simp)]
  calc
    shiftedKernel θ X Y =
        ∑' s : ℕ, ∑' n : ℕ,
          ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
            ENNReal.ofReal (θ ^ (-(s : ℤ))) := by
      simp_rw [shiftedKernel, shiftKernel, ← ENNReal.tsum_mul_right]
    _ = ∑' n : ℕ, ∑' s : ℕ,
          ENNReal.ofReal (kernelLengthCoefficient X Y s n : ℝ) *
            ENNReal.ofReal (θ ^ (-(s : ℤ))) := ENNReal.tsum_comm
    _ = ∑' n : ℕ, shiftedLength θ X Y n := by
      congr 1
      funext n
      exact hfinite n

end AKLT.W.REC064

#print axioms AKLT.W.REC064.main
#print axioms AKLT.W.REC064.latticeDist_triangle
#print axioms AKLT.W.REC064.latticeDist_symm
#print axioms AKLT.W.REC064.wordVertex_succ
#print axioms AKLT.W.REC064.neighbors_dist_one
#print axioms AKLT.W.REC064.wordVertex_latticeDist_start_le
#print axioms AKLT.W.REC064.responsePair_shift_le
#print axioms AKLT.W.REC064.exposureSum_zero_of_reward_zero
#print axioms AKLT.W.REC064.responseKappa_zero_of_shift_gt
#print axioms AKLT.W.REC064.kernelLengthCoefficient_zero_of_shift_gt
#print axioms AKLT.W.REC064.kernelLengthCoefficient_zero_at_zero
