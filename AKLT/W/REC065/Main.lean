module
public import AKLT.Blueprint.Rec.NodesKernel
public import AKLT.Blueprint.H3.Positivity
public import AKLT.W.REC070.TrailBound

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs
open AKLT.Blueprint.Rec

namespace AKLT.W.REC065

noncomputable def closedTrailMass (n : ℕ) (X : PairType) : ℝ := by
  classical
  exact ∑ w : DirectionWord n,
    if ClosedTrail X w then (trailWeight kernelStart kernelIncoming w : ℝ) else 0

private theorem wordVertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n)
    (j : ℕ) (hj : j < n) :
    wordVertex u w (j + 1) = wordVertex u w j + (w ⟨j, hj⟩).step := by
  classical
  unfold wordVertex
  have hs : (∑ i : Fin n, if i.val < j + 1 then (w i).step else 0) =
      (∑ i : Fin n, if i.val < j then (w i).step else 0) +
        (w ⟨j, hj⟩).step := by
    calc
      _ = ∑ i : Fin n, ((if i.val < j then (w i).step else 0) +
          (if i.val = j then (w i).step else 0)) := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hlt : i.val < j <;> by_cases heq : i.val = j <;>
          simp [hlt, heq] <;> omega
      _ = (∑ i : Fin n, if i.val < j then (w i).step else 0) +
          ∑ i : Fin n, if i.val = j then (w i).step else 0 := Finset.sum_add_distrib
      _ = _ := by
        congr 1
        rw [Finset.sum_eq_single ⟨j, hj⟩]
        · simp
        · intro i hi hne
          simp [Fin.ext_iff] at hne
          simp [hne]
        · simp
  rw [hs]
  simp [add_assoc]

private theorem latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  unfold latticeDist
  have hx : (x.1 - z.1).natAbs ≤ (x.1 - y.1).natAbs + (y.1 - z.1).natAbs := by
    calc
      (x.1 - z.1).natAbs = ((x.1 - y.1) + (y.1 - z.1)).natAbs := by congr 1 <;> omega
      _ ≤ _ := Int.natAbs_add_le _ _
  have hy : (x.2 - z.2).natAbs ≤ (x.2 - y.2).natAbs + (y.2 - z.2).natAbs := by
    calc
      (x.2 - z.2).natAbs = ((x.2 - y.2) + (y.2 - z.2)).natAbs := by congr 1 <;> omega
      _ ≤ _ := Int.natAbs_add_le _ _
  omega

private theorem latticeDist_symm (x y : Plane) : latticeDist x y = latticeDist y x := by
  unfold latticeDist
  have h₁ : (x.1 - y.1).natAbs = (y.1 - x.1).natAbs :=
    (Int.natAbs_eq_natAbs_iff).2 (Or.inr (by omega))
  have h₂ : (x.2 - y.2).natAbs = (y.2 - x.2).natAbs :=
    (Int.natAbs_eq_natAbs_iff).2 (Or.inr (by omega))
  exact congrArg₂ Nat.add h₁ h₂

private theorem latticeDist_step_right (x : Plane) (d : Compass) :
    latticeDist x (x + d.step) = 1 := by
  cases d <;> simp [latticeDist, Compass.step]

private theorem wordVertex_dist_start {n : ℕ} (w : DirectionWord n) :
    ∀ j ≤ n, latticeDist kernelStart (wordVertex kernelStart w j) ≤ j := by
  intro j hj
  induction j with
  | zero => simp [wordVertex, latticeDist]
  | succ j ih =>
      have hjn : j < n := by omega
      rw [wordVertex_succ kernelStart w j hjn]
      calc
        latticeDist kernelStart (wordVertex kernelStart w j + (w ⟨j, hjn⟩).step)
            ≤ latticeDist kernelStart (wordVertex kernelStart w j) +
                latticeDist (wordVertex kernelStart w j)
                  (wordVertex kernelStart w j + (w ⟨j, hjn⟩).step) :=
              latticeDist_triangle _ _ _
        _ ≤ j + 1 := by rw [latticeDist_step_right]; omega

private theorem wordVertex_dist_end_aux {n : ℕ} (w : DirectionWord n) :
    ∀ k j, j + k = n →
      latticeDist (wordVertex kernelStart w j) (wordVertex kernelStart w n) ≤ k := by
  intro k
  induction k with
  | zero =>
      intro j hj
      have : j = n := by omega
      subst j
      simp [latticeDist]
  | succ k ih =>
      intro j hj
      have hjn : j < n := by omega
      have hnext := ih (j + 1) (by omega)
      calc
        latticeDist (wordVertex kernelStart w j) (wordVertex kernelStart w n) ≤
            latticeDist (wordVertex kernelStart w j) (wordVertex kernelStart w (j + 1)) +
              latticeDist (wordVertex kernelStart w (j + 1)) (wordVertex kernelStart w n) :=
          latticeDist_triangle _ _ _
        _ ≤ k + 1 := by
          rw [wordVertex_succ kernelStart w j hjn, latticeDist_step_right]
          have hnext' : latticeDist (wordVertex kernelStart w j + (w ⟨j, hjn⟩).step)
              (wordVertex kernelStart w n) ≤ k := by
            simpa [wordVertex_succ kernelStart w j hjn] using hnext
          calc
            1 + latticeDist (wordVertex kernelStart w j + (w ⟨j, hjn⟩).step)
                (wordVertex kernelStart w n) ≤ 1 + k := Nat.add_le_add_left hnext' 1
            _ = k + 1 := Nat.add_comm _ _

private theorem wordVertex_dist_end {n : ℕ} (w : DirectionWord n) (j : ℕ) (hj : j ≤ n) :
    latticeDist (wordVertex kernelStart w j) (wordVertex kernelStart w n) ≤ n - j := by
  exact wordVertex_dist_end_aux w (n - j) j (by omega)

private theorem mem_neighbours_dist {x z : Plane} (hz : z ∈ neighbours x) :
    latticeDist z x = 1 := by
  classical
  unfold neighbours at hz
  rcases Finset.mem_image.mp hz with ⟨d, _, rfl⟩
  cases d <;> simp [latticeDist, Compass.step]

private theorem responsePair_mem_neighbours {n : ℕ} (X : PairType) (w : DirectionWord n)
    (hclosed : ClosedTrail X w) (i : Fin n) (p : Finset Plane)
    (hp : p ∈ responsePairs w i) {z : Plane} (hz : z ∈ p) :
    z ∈ neighbours (wordVertex kernelStart w i.val) := by
  classical
  have hsub := (Finset.mem_powersetCard.mp hp).1
  have hmem := hsub hz
  rcases Finset.mem_insert.mp hmem with h | h
  · subst z
    have hi : i.val < n := i.isLt
    rw [wordVertex_succ kernelStart w i.val hi]
    unfold neighbours
    apply Finset.mem_image.mpr
    exact ⟨w i, Finset.mem_univ _, rfl⟩
  · have hlive : z ∈ liveOtherNeighbours w i := h
    unfold liveOtherNeighbours at hlive
    have hresp' := (Finset.mem_filter.mp hlive).1
    have hresp := (Finset.mem_erase.mp hresp').2
    exact (Finset.mem_erase.mp hresp).2

private theorem pairShift_le_half_add_one {n : ℕ} (X : PairType) (w : DirectionWord n)
    (hclosed : ClosedTrail X w) (i : Fin n) (p : Finset Plane)
    (hp : p ∈ responsePairs w i) :
    (pairShift X p : ℝ) ≤ (n : ℝ) / 2 + 1 := by
  classical
  have hzbound : ∀ z ∈ p, min (latticeDist z kernelStart)
      (latticeDist z (kernelTarget X)) ≤ (n + 2) / 2 := by
    intro z hz
    have hzn := mem_neighbours_dist (responsePair_mem_neighbours X w hclosed i p hp hz)
    have hstart := wordVertex_dist_start w i.val (by omega)
    have hend := wordVertex_dist_end w i.val (by omega)
    have hstart' : latticeDist (wordVertex kernelStart w i.val) kernelStart ≤ i.val := by
      simpa [latticeDist_symm] using hstart
    have hstartz : latticeDist z kernelStart ≤ i.val + 1 := by
      calc
        latticeDist z kernelStart ≤ latticeDist z (wordVertex kernelStart w i.val) +
            latticeDist (wordVertex kernelStart w i.val) kernelStart :=
          latticeDist_triangle _ _ _
        _ ≤ i.val + 1 := by
          calc
            _ ≤ 1 + i.val := add_le_add hzn.le hstart'
            _ = i.val + 1 := Nat.add_comm _ _
    have htargetz : latticeDist z (kernelTarget X) ≤ n - i.val + 1 := by
      have hend' : wordVertex kernelStart w n = kernelTarget X := hclosed.2.1
      rw [← hend']
      calc
        latticeDist z (wordVertex kernelStart w n) ≤
            latticeDist z (wordVertex kernelStart w i.val) +
              latticeDist (wordVertex kernelStart w i.val)
                (wordVertex kernelStart w n) := latticeDist_triangle _ _ _
        _ ≤ n - i.val + 1 := by
          calc
            _ ≤ 1 + (n - i.val) := add_le_add hzn.le hend
            _ = n - i.val + 1 := Nat.add_comm _ _
    have hmin : min (i.val + 1) (n - i.val + 1) ≤ (n + 2) / 2 := by omega
    exact (min_le_min hstartz htargetz).trans hmin
  have hshift : pairShift X p ≤ (n + 2) / 2 := by
    unfold pairShift
    exact Finset.sup_le hzbound
  have hdouble : 2 * pairShift X p ≤ n + 2 := by
    have := Nat.mul_le_mul_left 2 hshift
    omega
  have hreal : (2 : ℝ) * (pairShift X p : ℝ) ≤ (n : ℝ) + 2 := by
    exact_mod_cast hdouble
  linarith

theorem shift_geometry : AKLT.Blueprint.Rec.ShiftGeometryStatement := by
  intro n X w hclosed i p hp
  exact pairShift_le_half_add_one X w hclosed i p hp

private def firstVisitFinset {n : ℕ} (w : DirectionWord n) : Finset (Fin n) :=
  Finset.univ.filter fun i => wordRevisit kernelStart w i = false

private theorem firstVisitList_nodup {n : ℕ} (w : DirectionWord n) :
    (firstVisitList w).Nodup := by
  unfold firstVisitList
  exact List.Nodup.filter _ (List.nodup_finRange n)

private theorem firstVisitList_toFinset {n : ℕ} (w : DirectionWord n) :
    (firstVisitList w).toFinset = firstVisitFinset w := by
  classical
  ext i
  simp [firstVisitList, firstVisitFinset, wordRevisit]

private theorem kernelOrdering_nodup {n : ℕ} (w : DirectionWord n) :
    (kernelOrdering w).Nodup := by
  by_cases h : n ≤ 12
  · rw [kernelOrdering, if_pos h]
    exact List.nodup_mergeSort.mpr (firstVisitList_nodup w)
  · rw [kernelOrdering, if_neg h]
    apply List.nodup_append.mpr
    refine ⟨(firstVisitList_nodup w).filter _, (firstVisitList_nodup w).filter _, ?_⟩
    intro i hi j hj hEq
    have hs : wordStraight kernelIncoming w i = true := (List.mem_filter.mp hi).2
    have ht : !wordStraight kernelIncoming w j = true := (List.mem_filter.mp hj).2
    subst j
    simp [hs] at ht

private theorem kernelOrdering_mem_firstVisitList {n : ℕ} (w : DirectionWord n)
    {i : Fin n} (hi : i ∈ kernelOrdering w) : i ∈ firstVisitList w := by
  by_cases h : n ≤ 12
  · have h' : i ∈ (firstVisitList w).mergeSort (shortOrderLE w) := by
      simpa [kernelOrdering, h] using hi
    exact (List.mem_mergeSort.mp h')
  · have h' : i ∈ (firstVisitList w).filter (wordStraight kernelIncoming w) ++
      (firstVisitList w).filter (fun j => !wordStraight kernelIncoming w j) := by
      simpa [kernelOrdering, h] using hi
    rcases List.mem_append.mp h' with hleft | hright
    · exact (List.mem_filter.mp hleft).1
    · exact (List.mem_filter.mp hright).1

private theorem kernelOrdering_mem_firstVisits {n : ℕ} (w : DirectionWord n)
    {i : Fin n} (hi : i ∈ kernelOrdering w) : i ∈ firstVisitFinset w := by
  rw [← firstVisitList_toFinset]
  exact List.mem_toFinset.mpr (kernelOrdering_mem_firstVisitList w hi)

private theorem kernelOrdering_length_le {n : ℕ} (w : DirectionWord n) :
    (kernelOrdering w).length ≤ n := by
  classical
  have hnd := kernelOrdering_nodup w
  have hcard : (kernelOrdering w).toFinset.card ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_le_card (Finset.subset_univ _)
  rw [List.toFinset_card_of_nodup hnd] at hcard
  simpa using hcard

private theorem passageFactor_ge_one (b : Bool) : (1 : ℚ) ≤ passageFactor b := by
  cases b <;> norm_num [passageFactor, localThreshold]

private theorem finset_prod_ge_one {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℚ) (hf : ∀ i ∈ s, 1 ≤ f i) : 1 ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      have hrest : ∀ i ∈ s, 1 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      calc
        1 = 1 * 1 := by ring
        _ ≤ f a * ∏ i ∈ s, f i :=
          mul_le_mul (hf a (Finset.mem_insert_self _ _)) (ih hrest) (by norm_num)
            (le_trans (by norm_num) (hf a (Finset.mem_insert_self _ _)))

private theorem exposureSum_bound {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ)
    (hr : ∀ i, 0 ≤ r i) (l : List (Fin n)) (hnd : l.Nodup) :
    exposureSum w r l ≤
      (∑ i ∈ l.toFinset, r i) *
        (∏ i ∈ l.toFinset, (passageFactor (wordStraight kernelIncoming w i) : ℚ)) := by
  induction l with
  | nil => simp [exposureSum]
  | cons i l ih =>
      have hi : i ∉ l := by
        intro hin
        exact (List.nodup_cons.mp hnd).1 hin
      have hi' : i ∉ l.toFinset := by
        intro hin
        exact hi (List.mem_toFinset.mp hin)
      have htail := ih hnd.tail
      have hx : 1 ≤ (passageFactor (wordStraight kernelIncoming w i) : ℚ) :=
        passageFactor_ge_one _
      have hP : 1 ≤ ∏ j ∈ l.toFinset,
          (passageFactor (wordStraight kernelIncoming w j) : ℚ) :=
        finset_prod_ge_one _ _ (fun j hj => passageFactor_ge_one _)
      have hS : 0 ≤ ∑ j ∈ l.toFinset, r j := Finset.sum_nonneg fun j hj => hr j
      rw [exposureSum, List.toFinset_cons, Finset.sum_insert hi', Finset.prod_insert hi']
      have h1 :
          (passageFactor (wordStraight kernelIncoming w i) : ℚ) * r i ≤
            (passageFactor (wordStraight kernelIncoming w i) : ℚ) *
              (∏ j ∈ l.toFinset, (passageFactor (wordStraight kernelIncoming w j) : ℚ)) * r i := by
        have := mul_le_mul_of_nonneg_right hP
          (mul_nonneg (by linarith [hx]) (hr i))
        nlinarith [this]
      have h2 :
          (passageFactor (wordStraight kernelIncoming w i) : ℚ) * exposureSum w r l ≤
            (passageFactor (wordStraight kernelIncoming w i) : ℚ) *
              ((∑ j ∈ l.toFinset, r j) *
                ∏ j ∈ l.toFinset, (passageFactor (wordStraight kernelIncoming w j) : ℚ)) :=
        mul_le_mul_of_nonneg_left htail (by linarith [hx])
      calc
        (passageFactor (wordStraight kernelIncoming w i) : ℚ) *
              (r i + exposureSum w r l) =
            (passageFactor (wordStraight kernelIncoming w i) : ℚ) * r i +
              (passageFactor (wordStraight kernelIncoming w i) : ℚ) * exposureSum w r l := by ring
        _ ≤ _ := add_le_add h1 h2
        _ = (r i + ∑ j ∈ l.toFinset, r j) *
              ((passageFactor (wordStraight kernelIncoming w i) : ℚ) *
                ∏ j ∈ l.toFinset, (passageFactor (wordStraight kernelIncoming w j) : ℚ)) := by ring

private theorem finset_prod_le_of_subset {ι : Type} [DecidableEq ι] (s t : Finset ι)
    (f : ι → ℚ) (hst : s ⊆ t) (hf : ∀ i ∈ t, 1 ≤ f i) :
    (∏ i ∈ s, f i) ≤ ∏ i ∈ t, f i := by
  classical
  have hdiff : 1 ≤ ∏ i ∈ t \ s, f i :=
    finset_prod_ge_one _ _ (by
      intro i hi
      exact hf i (Finset.mem_sdiff.mp hi).1)
  have hsnonneg : 0 ≤ ∏ i ∈ s, f i :=
    Finset.prod_nonneg fun i hi => le_trans (by norm_num) (hf i (hst hi))
  have hprod := Finset.prod_sdiff hst (f := f)
  calc
    (∏ i ∈ s, f i) = 1 * ∏ i ∈ s, f i := by ring
    _ ≤ (∏ i ∈ t \ s, f i) * ∏ i ∈ s, f i :=
      mul_le_mul_of_nonneg_right hdiff hsnonneg
    _ = ∏ i ∈ t, f i := hprod

private theorem responseKappa_shift_bound {n : ℕ} (X Y : PairType) (w : DirectionWord n)
    (hclosed : ClosedTrail X w) (i : Fin n) (s : ℕ)
    (hκ : responseKappa X Y s w i ≠ 0) :
    (s : ℝ) ≤ (n : ℝ) / 2 + 1 := by
  by_contra hs
  have hzero : responseKappa X Y s w i = 0 := by
    unfold responseKappa
    apply Finset.sum_eq_zero
    intro p hp
    split_ifs with hm
    · have hgeom := pairShift_le_half_add_one X w hclosed i p hp
      have hbound : (s : ℝ) ≤ (n : ℝ) / 2 + 1 := by simpa [hm.2] using hgeom
      exact False.elim (hs hbound)
    · rfl
  exact hκ hzero

private theorem responseKappa_power_le {n : ℕ} (X Y : PairType) (w : DirectionWord n)
    (hclosed : ClosedTrail X w) (i : Fin n) (s : ℕ) (θ : ℝ)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (responseKappa X Y s w i : ℝ) * θ ^ (-(s : ℤ)) ≤
      (responseKappa X Y s w i : ℝ) * Real.rpow θ (-(n : ℝ) / 2 - 1) := by
  have hκ : 0 ≤ (responseKappa X Y s w i : ℝ) := by
    exact_mod_cast AKLT.Blueprint.H3.responseKappa_nonneg X Y s w i
  by_cases hzero : responseKappa X Y s w i = 0
  · simp [hzero]
  · have hs := responseKappa_shift_bound X Y w hclosed i s hzero
    have hexp : -(n : ℝ) / 2 - 1 ≤ -(s : ℝ) := by linarith
    have hpow : θ ^ (-(s : ℤ)) ≤ Real.rpow θ (-(n : ℝ) / 2 - 1) := by
      rw [← Real.rpow_intCast θ (-(s : ℤ))]
      simp only [Int.cast_neg, Int.cast_natCast]
      exact Real.rpow_le_rpow_of_exponent_ge hθ hθ1 hexp
    exact mul_le_mul_of_nonneg_left hpow hκ

private theorem trailWeight_eq_base_mul_firstProduct {n : ℕ} (w : DirectionWord n) :
    trailWeight kernelStart kernelIncoming w =
      trailBaseWeight kernelStart w *
        ∏ i ∈ firstVisitFinset w, passageFactor (wordStraight kernelIncoming w i) := by
  classical
  unfold trailWeight trailBaseWeight firstVisitFinset
  simp only [Finset.prod_filter]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases hrev : wordRevisit kernelStart w i <;> simp [hrev] <;> ring

/-- The local coefficient budget, proved below by counting all live response pairs. -/
def Residual_DepartureBudget : Prop := by
  classical
  exact ∀ n : ℕ, ∀ X Y : PairType, ∀ w : DirectionWord n,
    ClosedTrail X w → ∀ i : Fin n,
      (∑ s ∈ Finset.range (n + 2), (responseKappa X Y s w i : ℝ)) ≤
        (18094 / 100000 + 2 * (36751 / 100000 : ℝ))

/-- A fixed response type is bounded by the total response budget.  The total
has at most one alpha pair and two beta pairs among the three nonarrival
neighbors; deleting dead neighbors only decreases this nonnegative sum. -/
theorem departure_budget : Residual_DepartureBudget := by
  classical
  intro n X Y w hclosed i
  have hq : (∑ s ∈ Finset.range (n + 2), responseKappa X Y s w i) ≤
      AKLT.W.REC070.responseCap := by
    calc
      _ ≤ ∑ Z : PairType, ∑ s ∈ Finset.range (n + 2), responseKappa X Z s w i :=
        Finset.single_le_sum
          (fun Z _ => Finset.sum_nonneg fun s _ =>
            AKLT.Blueprint.H3.responseKappa_nonneg X Z s w i)
          (Finset.mem_univ Y)
      _ = ∑ p ∈ responsePairs w i, pairCoefficient w i p :=
        AKLT.W.REC070.response_total X w i
      _ ≤ AKLT.W.REC070.responseCap := AKLT.W.REC070.pair_sum_cap w hclosed.1 i
  simpa [AKLT.W.REC070.responseCap] using (Rat.cast_le (K := ℝ)).mpr hq

private theorem orderedKappaShiftedSum_le {n : ℕ} (budget : Residual_DepartureBudget)
    (X Y : PairType) (w : DirectionWord n) (hclosed : ClosedTrail X w)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (∑ s ∈ Finset.range (n + 2),
      (∑ i ∈ (kernelOrdering w).toFinset, (responseKappa X Y s w i : ℝ)) *
        θ ^ (-(s : ℤ))) ≤
      Real.rpow θ (-(n : ℝ) / 2 - 1) *
        ((n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ))) := by
  classical
  let l := kernelOrdering w
  let S := (kernelOrdering w).toFinset
  have hnd := kernelOrdering_nodup w
  have hlen := kernelOrdering_length_le w
  have hcap : 0 ≤ (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) := by norm_num
  have hsum :
      (∑ i ∈ S, ∑ s ∈ Finset.range (n + 2), (responseKappa X Y s w i : ℝ)) ≤
        (n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) := by
    calc
      _ ≤ ∑ i ∈ S, (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) :=
        Finset.sum_le_sum fun i hi => budget n X Y w hclosed i
      _ = (S.card : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) := by simp <;> ring
      _ ≤ (n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) := by
        have hcard : S.card = l.length := by
          dsimp [S, l]
          exact List.toFinset_card_of_nodup hnd
        rw [hcard]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) hcap
  have hpowpos : 0 < Real.rpow θ (-(n : ℝ) / 2 - 1) := Real.rpow_pos_of_pos hθ _
  have hmajor :
      ∀ s ∈ Finset.range (n + 2),
        (∑ i ∈ S, (responseKappa X Y s w i : ℝ)) * θ ^ (-(s : ℤ)) ≤
          (∑ i ∈ S, (responseKappa X Y s w i : ℝ)) *
            Real.rpow θ (-(n : ℝ) / 2 - 1) := by
    intro s hs
    have hterm : ∀ i ∈ S,
        (responseKappa X Y s w i : ℝ) * θ ^ (-(s : ℤ)) ≤
          (responseKappa X Y s w i : ℝ) * Real.rpow θ (-(n : ℝ) / 2 - 1) := by
      intro i hi
      exact responseKappa_power_le X Y w hclosed i s θ hθ hθ1
    calc
      _ = ∑ i ∈ S, (responseKappa X Y s w i : ℝ) * θ ^ (-(s : ℤ)) := by rw [Finset.sum_mul]
      _ ≤ ∑ i ∈ S, (responseKappa X Y s w i : ℝ) *
            Real.rpow θ (-(n : ℝ) / 2 - 1) := Finset.sum_le_sum hterm
      _ = _ := by rw [← Finset.sum_mul] <;> ring
  calc
    _ ≤ ∑ s ∈ Finset.range (n + 2),
          (∑ i ∈ S, (responseKappa X Y s w i : ℝ)) *
            Real.rpow θ (-(n : ℝ) / 2 - 1) := Finset.sum_le_sum hmajor
    _ = Real.rpow θ (-(n : ℝ) / 2 - 1) *
          ∑ s ∈ Finset.range (n + 2), ∑ i ∈ S, (responseKappa X Y s w i : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = Real.rpow θ (-(n : ℝ) / 2 - 1) *
          ∑ i ∈ S, ∑ s ∈ Finset.range (n + 2), (responseKappa X Y s w i : ℝ) := by
      rw [Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hpowpos.le

private theorem trailBaseWeight_nonneg {n : ℕ} (w : DirectionWord n) :
    0 ≤ trailBaseWeight kernelStart w := by
  unfold trailBaseWeight
  apply Finset.prod_nonneg
  intro i hi
  split_ifs <;> norm_num

private theorem closedWordEntryBound {n : ℕ} (budget : Residual_DepartureBudget)
    (X Y : PairType) (w : DirectionWord n) (hclosed : ClosedTrail X w)
    (θ : ℝ) (hθ : 0 < θ) (hθ1 : θ ≤ 1) :
    (∑ s ∈ Finset.range (n + 2),
      (trailBaseWeight kernelStart w : ℝ) *
        (exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) : ℝ) *
        θ ^ (-(s : ℤ))) ≤
      (n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) *
        (trailWeight kernelStart kernelIncoming w : ℝ) *
          Real.rpow θ (-(n : ℝ) / 2 - 1) := by
  classical
  let l := kernelOrdering w
  let S := l.toFinset
  let f : Fin n → ℚ := fun i => passageFactor (wordStraight kernelIncoming w i)
  let P₀ : ℚ := ∏ i ∈ S, f i
  let P : ℚ := ∏ i ∈ firstVisitFinset w, f i
  let C : ℝ := 18094 / 100000 + 2 * (36751 / 100000 : ℝ)
  have hnd := kernelOrdering_nodup w
  have hlen := kernelOrdering_length_le w
  have hsub : S ⊆ firstVisitFinset w := by
    intro i hi
    exact kernelOrdering_mem_firstVisits w (List.mem_toFinset.mp hi)
  have hPbound : P₀ ≤ P := by
    dsimp [P₀, P, f, S, l]
    exact finset_prod_le_of_subset (kernelOrdering w).toFinset (firstVisitFinset w)
      (fun i => passageFactor (wordStraight kernelIncoming w i)) hsub
      (fun i hi => passageFactor_ge_one _)
  have hbaseq : 0 ≤ trailBaseWeight kernelStart w := trailBaseWeight_nonneg w
  have hbase : 0 ≤ (trailBaseWeight kernelStart w : ℝ) := by exact_mod_cast hbaseq
  have hP₀q : 0 ≤ P₀ := by
    dsimp [P₀, f, S, l]
    apply Finset.prod_nonneg
    intro i hi
    exact le_trans (by norm_num) (passageFactor_ge_one _)
  have hP₀nonneg : 0 ≤ (P₀ : ℝ) := by exact_mod_cast hP₀q
  have hP : (P₀ : ℝ) ≤ (P : ℝ) := by exact_mod_cast hPbound
  have hbaseP :
      (trailBaseWeight kernelStart w : ℝ) * (P : ℝ) =
        (trailWeight kernelStart kernelIncoming w : ℝ) := by
    exact_mod_cast (trailWeight_eq_base_mul_firstProduct w).symm
  have hsumPow := orderedKappaShiftedSum_le budget X Y w hclosed θ hθ hθ1
  have hsumUnweighted :
      (∑ s ∈ Finset.range (n + 2),
        ∑ i ∈ S, (responseKappa X Y s w i : ℝ)) ≤
        (n : ℝ) * C := by
    calc
      _ = ∑ i ∈ S, ∑ s ∈ Finset.range (n + 2), (responseKappa X Y s w i : ℝ) :=
        Finset.sum_comm
      _ ≤ ∑ i ∈ S, C := Finset.sum_le_sum fun i hi => budget n X Y w hclosed i
      _ = (S.card : ℝ) * C := by simp <;> ring
      _ ≤ (n : ℝ) * C := by
        have hcard : S.card = l.length := by
          dsimp [S, l]
          exact List.toFinset_card_of_nodup hnd
        rw [hcard]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (by dsimp [C]; norm_num)
  have hR : 0 ≤ Real.rpow θ (-(n : ℝ) / 2 - 1) :=
    (Real.rpow_pos_of_pos hθ _).le
  have horderedSum :
      ∀ s ∈ Finset.range (n + 2),
        0 ≤ ∑ i ∈ S, (responseKappa X Y s w i : ℝ) := by
    intro s hs
    exact Finset.sum_nonneg fun i hi => by
      exact_mod_cast AKLT.Blueprint.H3.responseKappa_nonneg X Y s w i
  have hexpo (s : ℕ) :
      (exposureSum w (fun i => responseKappa X Y s w i) l : ℝ) ≤
        (∑ i ∈ S, (responseKappa X Y s w i : ℝ)) * (P₀ : ℝ) := by
    have hq := exposureSum_bound w (fun i => responseKappa X Y s w i)
      (fun i => AKLT.Blueprint.H3.responseKappa_nonneg X Y s w i) l hnd
    exact_mod_cast hq
  have hpowNonneg : ∀ s : ℕ, 0 ≤ θ ^ (-(s : ℤ)) := fun s => (zpow_pos hθ _).le
  have hterm : ∀ s ∈ Finset.range (n + 2),
      (trailBaseWeight kernelStart w : ℝ) *
          (exposureSum w (fun i => responseKappa X Y s w i) l : ℝ) *
            θ ^ (-(s : ℤ)) ≤
        (trailBaseWeight kernelStart w : ℝ) * (P₀ : ℝ) *
          ((∑ i ∈ S, (responseKappa X Y s w i : ℝ)) *
            Real.rpow θ (-(n : ℝ) / 2 - 1)) := by
    intro s hs
    have hpow := orderedKappaShiftedSum_le budget X Y w hclosed θ hθ hθ1
    have hpowS :
        (∑ i ∈ S, (responseKappa X Y s w i : ℝ)) * θ ^ (-(s : ℤ)) ≤
          (∑ i ∈ S, (responseKappa X Y s w i : ℝ)) * Real.rpow θ (-(n : ℝ) / 2 - 1) := by
      have hpieces : ∀ i ∈ S,
          (responseKappa X Y s w i : ℝ) * θ ^ (-(s : ℤ)) ≤
            (responseKappa X Y s w i : ℝ) * Real.rpow θ (-(n : ℝ) / 2 - 1) := by
        intro i hi
        exact responseKappa_power_le X Y w hclosed i s θ hθ hθ1
      calc
        _ = ∑ i ∈ S, (responseKappa X Y s w i : ℝ) * θ ^ (-(s : ℤ)) := by rw [Finset.sum_mul]
        _ ≤ ∑ i ∈ S, (responseKappa X Y s w i : ℝ) *
              Real.rpow θ (-(n : ℝ) / 2 - 1) := Finset.sum_le_sum hpieces
        _ = _ := by rw [Finset.sum_mul]
    have hexpo' := hexpo s
    have hsumκ := horderedSum s hs
    have hR : 0 ≤ Real.rpow θ (-(n : ℝ) / 2 - 1) :=
      (Real.rpow_pos_of_pos hθ _).le
    calc
      _ ≤ (trailBaseWeight kernelStart w : ℝ) *
          ((∑ i ∈ S, (responseKappa X Y s w i : ℝ)) * (P₀ : ℝ)) *
            θ ^ (-(s : ℤ)) := by
        apply mul_le_mul_of_nonneg_right
        · exact mul_le_mul_of_nonneg_left hexpo' hbase
        · exact hpowNonneg s
      _ ≤ (trailBaseWeight kernelStart w : ℝ) * (P₀ : ℝ) *
          ((∑ i ∈ S, (responseKappa X Y s w i : ℝ)) *
            Real.rpow θ (-(n : ℝ) / 2 - 1)) := by
        nlinarith [mul_le_mul_of_nonneg_left hpowS (mul_nonneg hbase hP₀nonneg)]
  calc
    _ ≤ ∑ s ∈ Finset.range (n + 2),
          (trailBaseWeight kernelStart w : ℝ) * (P₀ : ℝ) *
            ((∑ i ∈ S, (responseKappa X Y s w i : ℝ)) *
              Real.rpow θ (-(n : ℝ) / 2 - 1)) := Finset.sum_le_sum hterm
    _ = (trailBaseWeight kernelStart w : ℝ) * (P₀ : ℝ) *
          (Real.rpow θ (-(n : ℝ) / 2 - 1) *
            ∑ s ∈ Finset.range (n + 2),
              ∑ i ∈ S, (responseKappa X Y s w i : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ ≤ (trailBaseWeight kernelStart w : ℝ) * (P₀ : ℝ) *
          (Real.rpow θ (-(n : ℝ) / 2 - 1) *
            ((n : ℝ) * C)) := by
      apply mul_le_mul_of_nonneg_left
      · exact mul_le_mul_of_nonneg_left hsumUnweighted hR
      · exact mul_nonneg hbase hP₀nonneg
    _ ≤ (n : ℝ) * C * (trailWeight kernelStart kernelIncoming w : ℝ) *
          Real.rpow θ (-(n : ℝ) / 2 - 1) := by
      have hcap : 0 ≤ (n : ℝ) * C := by
        apply mul_nonneg (Nat.cast_nonneg n)
        dsimp [C]
        norm_num
      have hbaseP₀ : (trailBaseWeight kernelStart w : ℝ) * (P₀ : ℝ) ≤
          (trailWeight kernelStart kernelIncoming w : ℝ) := by
        rw [← hbaseP]
        exact mul_le_mul_of_nonneg_left hP hbase
      calc
        _ ≤ ((n : ℝ) * C *
              ((trailBaseWeight kernelStart w : ℝ) * (P₀ : ℝ))) *
              Real.rpow θ (-(n : ℝ) / 2 - 1) := by
          apply le_of_eq
          ring
        _ ≤ ((n : ℝ) * C *
              (trailWeight kernelStart kernelIncoming w : ℝ)) *
              Real.rpow θ (-(n : ℝ) / 2 - 1) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_left hbaseP₀ hcap
          · exact hR
        _ = _ := by ring

/-- The weighted finite coefficient row is bounded by the mass of closed
trails at that length. -/
def Residual_ClosedRowMajorant : Prop := by
  classical
  exact ∀ n : ℕ, ∀ X Y : PairType, ∀ θ : ℝ, 0 < θ → θ ≤ 1 →
    (∑ s ∈ Finset.range (n + 2),
      (kernelLengthCoefficient X Y s n : ℝ) * θ ^ (-(s : ℤ))) ≤
      (n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) *
        Real.rpow θ (-(n : ℝ) / 2 - 1) * closedTrailMass n X

private theorem closedRowMajorant_of_departureBudget
    (budget : Residual_DepartureBudget) : Residual_ClosedRowMajorant := by
  classical
  intro n X Y θ hθ hθ1
  let A : ℝ := (n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) *
    Real.rpow θ (-(n : ℝ) / 2 - 1)
  have hrewrite :
      (∑ s ∈ Finset.range (n + 2),
        (kernelLengthCoefficient X Y s n : ℝ) * θ ^ (-(s : ℤ))) =
      ∑ w : DirectionWord n,
        if ClosedTrail X w then
          ∑ s ∈ Finset.range (n + 2),
            (trailBaseWeight kernelStart w : ℝ) *
              (exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) : ℝ) *
                θ ^ (-(s : ℤ))
        else 0 := by
    simp only [kernelLengthCoefficient, Rat.cast_sum]
    have hcast (s : ℕ) (w : DirectionWord n) :
        ((if ClosedTrail X w then
            trailBaseWeight kernelStart w *
              exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w)
          else 0 : ℚ) : ℝ) =
          if ClosedTrail X w then
            (trailBaseWeight kernelStart w : ℝ) *
              (exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) : ℝ)
          else 0 := by
      split_ifs <;> simp [Rat.cast_mul]
    simp_rw [hcast]
    change (∑ s ∈ Finset.range (n + 2),
        ((Finset.univ : Finset (DirectionWord n)).sum fun w =>
          if ClosedTrail X w then
            (trailBaseWeight kernelStart w : ℝ) *
              (exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) : ℝ)
          else 0) * θ ^ (-(s : ℤ))) =
      (Finset.univ : Finset (DirectionWord n)).sum fun w =>
        if ClosedTrail X w then
          ∑ s ∈ Finset.range (n + 2),
            (trailBaseWeight kernelStart w : ℝ) *
              (exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) : ℝ) *
                θ ^ (-(s : ℤ))
        else 0
    calc
      _ = ∑ s ∈ Finset.range (n + 2),
          (Finset.univ : Finset (DirectionWord n)).sum
            (fun w => (if ClosedTrail X w then
              (trailBaseWeight kernelStart w : ℝ) *
                (exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) : ℝ)
              else 0) * θ ^ (-(s : ℤ))) := by
        apply Finset.sum_congr rfl
        intro s hs
        exact (Finset.sum_mul (Finset.univ : Finset (DirectionWord n))
          (fun w => if ClosedTrail X w then
            (trailBaseWeight kernelStart w : ℝ) *
              (exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) : ℝ)
            else 0) (θ ^ (-(s : ℤ))))
      _ = ∑ w ∈ (Finset.univ : Finset (DirectionWord n)),
          ∑ s ∈ Finset.range (n + 2),
            (if ClosedTrail X w then
              (trailBaseWeight kernelStart w : ℝ) *
                (exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) : ℝ)
              else 0) * θ ^ (-(s : ℤ)) := Finset.sum_comm
      _ = ∑ w ∈ (Finset.univ : Finset (DirectionWord n)),
          if ClosedTrail X w then
            ∑ s ∈ Finset.range (n + 2),
              (trailBaseWeight kernelStart w : ℝ) *
                (exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) : ℝ) *
                  θ ^ (-(s : ℤ))
          else 0 := by
        apply Finset.sum_congr rfl
        intro w hw
        by_cases hc : ClosedTrail X w <;> simp [hc]
  calc
    _ = ∑ w : DirectionWord n,
        if ClosedTrail X w then
          ∑ s ∈ Finset.range (n + 2),
            (trailBaseWeight kernelStart w : ℝ) *
              (exposureSum w (fun i => responseKappa X Y s w i) (kernelOrdering w) : ℝ) *
                θ ^ (-(s : ℤ))
        else 0 := hrewrite
    _ ≤ ∑ w : DirectionWord n,
        A * if ClosedTrail X w then (trailWeight kernelStart kernelIncoming w : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro w hw
      by_cases hc : ClosedTrail X w
      · simpa [A, hc, mul_assoc, mul_left_comm, mul_comm] using closedWordEntryBound
          (n := n) budget X Y w hc θ hθ hθ1
      · simp [hc]
    _ = A * closedTrailMass n X := by
      rw [closedTrailMass, Finset.mul_sum]

private theorem closedTrailMass_le_open (CV q : ℝ) (hOpen : OpenTrailBound CV q)
    (n : ℕ) (X : PairType) :
    closedTrailMass n X ≤ CV * q ^ n := by
  classical
  rcases hOpen with ⟨_, _, _, hOpen⟩
  calc
    closedTrailMass n X ≤ ∑ w : DirectionWord n,
        if IsTrail kernelStart kernelIncoming w then
          (trailWeight kernelStart kernelIncoming w : ℝ) else 0 := by
      unfold closedTrailMass
      apply Finset.sum_le_sum
      intro w hw
      by_cases hc : ClosedTrail X w
      · simp [hc, hc.1]
      · simp only [hc, if_false]
        by_cases ht : IsTrail kernelStart kernelIncoming w
        · simp [ht]
          have hwt : 0 ≤ (trailWeight kernelStart kernelIncoming w : ℝ) := by
            have hq : 0 ≤ trailWeight kernelStart kernelIncoming w := by
              unfold trailWeight
              apply Finset.prod_nonneg
              intro i hi
              split_ifs
              · norm_num
              · exact div_nonneg (AKLT.Blueprint.H3.passageFactor_pos _).le (by norm_num)
            exact_mod_cast hq
          simpa [ht] using hwt
        · simp [ht]
    _ ≤ CV * q ^ n := hOpen n kernelStart kernelIncoming

private theorem majorant_of_departureBudget (hBudget : Residual_DepartureBudget) :
    AKLT.Blueprint.Rec.KernelLengthMajorantStatement := by
  have hResidual := closedRowMajorant_of_departureBudget hBudget
  intro CV q hOpen θ hqθ hθ1 X Y n
  have hθpos : 0 < θ := lt_of_le_of_lt (sq_nonneg q) hqθ
  have hmass := closedTrailMass_le_open CV q hOpen n X
  have hfactor : 0 ≤ (n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) *
      Real.rpow θ (-(n : ℝ) / 2 - 1) := by
    apply mul_nonneg
    · apply mul_nonneg
      · exact Nat.cast_nonneg n
      · norm_num
    · exact (Real.rpow_pos_of_pos hθpos _).le
  have hreal :
      (∑ s ∈ Finset.range (n + 2),
        (kernelLengthCoefficient X Y s n : ℝ) * θ ^ (-(s : ℤ))) ≤
      kernelMajorant CV q θ n := by
    calc
      _ ≤ (n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) *
          Real.rpow θ (-(n : ℝ) / 2 - 1) *
          closedTrailMass n X :=
        hResidual n X Y θ hθpos hθ1
      _ ≤ (n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) *
          Real.rpow θ (-(n : ℝ) / 2 - 1) * (CV * q ^ n) :=
        mul_le_mul_of_nonneg_left hmass hfactor
      _ = kernelMajorant CV q θ n := by
        simp [kernelMajorant]
        ring_nf
  have hcoeff : ∀ s ∈ Finset.range (n + 2),
      0 ≤ (kernelLengthCoefficient X Y s n : ℝ) := by
    intro s hs
    exact_mod_cast AKLT.Blueprint.H3.kernelLengthCoefficient_nonneg X Y s n
  have hpow : ∀ s : ℕ, 0 < θ ^ (-(s : ℤ)) := fun s => zpow_pos hθpos _
  have hsum_nonneg : ∀ s ∈ Finset.range (n + 2),
      0 ≤ (kernelLengthCoefficient X Y s n : ℝ) * θ ^ (-(s : ℤ)) := by
    intro s hs
    exact mul_nonneg (hcoeff s hs) (le_of_lt (hpow s))
  calc
    shiftedLength θ X Y n =
        ENNReal.ofReal (∑ s ∈ Finset.range (n + 2),
          (kernelLengthCoefficient X Y s n : ℝ) * θ ^ (-(s : ℤ)) ) := by
      unfold shiftedLength
      calc
        _ = ∑ s ∈ Finset.range (n + 2),
            ENNReal.ofReal ((kernelLengthCoefficient X Y s n : ℝ) * θ ^ (-(s : ℤ))) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [← ENNReal.ofReal_mul (hcoeff s hs)]
        _ = ENNReal.ofReal (∑ s ∈ Finset.range (n + 2),
            (kernelLengthCoefficient X Y s n : ℝ) * θ ^ (-(s : ℤ))) := by
          rw [← ENNReal.ofReal_sum_of_nonneg hsum_nonneg]
    _ ≤ ENNReal.ofReal (kernelMajorant CV q θ n) := ENNReal.ofReal_mono hreal

theorem main : AKLT.Blueprint.Rec.KernelLengthMajorantStatement :=
  majorant_of_departureBudget departure_budget

end AKLT.W.REC065

#print axioms AKLT.W.REC065.shift_geometry
#print axioms AKLT.W.REC065.departure_budget
#print axioms AKLT.W.REC065.main
