module
public import AKLT.W.REC070.Foundations

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC070
set_option maxHeartbeats 2000000
attribute [local instance] Classical.propDecidable

def responseCap : ℚ := 18094 / 100000 + 2 * (36751 / 100000)

lemma coefficient_cap {n : ℕ} (w : DirectionWord n) (i : Fin n) (p : Finset Plane) :
    pairCoefficient w i p ≤
      if wordVertex kernelStart w (i.val + 1) ∈ p then 36751 / 100000 else 18094 / 100000 := by
  unfold pairCoefficient
  split_ifs <;> cases wordStraight kernelIncoming w i <;>
    norm_num [alphaBound, betaBound, betaPrimeBound]

lemma step_injective : Function.Injective Compass.step := by
  intro a b h
  cases a <;> cases b <;> simp_all [Compass.step]

lemma nonreverse {n : ℕ} (w : DirectionWord n) (hw : IsTrail kernelStart kernelIncoming w)
    (i : Fin n) : w i ≠ (wordIncoming kernelIncoming w i).reverse := by
  by_cases hi : i.val = 0
  · simpa [wordIncoming, hi] using hw.2 i hi
  · intro h
    let j : Fin n := ⟨i.val - 1, by omega⟩
    have hj : j.val + 1 = i.val := by dsimp [j]; omega
    have hstep : w i = (w j).reverse := by simpa [wordIncoming, hi, j] using h
    have hv := AKLT.Cert.H2.vertex_succ kernelStart w j.val j.isLt
    rw [hj] at hv
    have he : wordBond kernelStart w j = wordBond kernelStart w i := by
      simp only [wordBond, AKLT.Cert.H2.vertex_succ kernelStart w i.val i.isLt,
        hj, hstep, AKLT.Cert.H2.reverse_step]
      rw [hv]
      have ha : wordVertex kernelStart w j.val + (w j).step + -(w j).step =
          wordVertex kernelStart w j.val := by abel
      rw [ha]
      exact Finset.pair_comm _ _
    have hh := congrArg Fin.val (hw.1 he)
    dsimp [j] at hh
    omega

lemma neighbors_card (v : Plane) : (neighbors v).card = 4 := by
  rw [neighbors, Finset.card_image_of_injective]
  · rfl
  · intro a b h
    exact step_injective (add_left_cancel h)

lemma responseNeighbors_card {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    (responseNeighbors w i).card = 3 := by
  have hm : wordVertex kernelStart w i.val - (wordIncoming kernelIncoming w i).step ∈
      neighbors (wordVertex kernelStart w i.val) := by
    apply Finset.mem_image.mpr
    refine ⟨(wordIncoming kernelIncoming w i).reverse, Finset.mem_univ _, ?_⟩
    simp [AKLT.Cert.H2.reverse_step, sub_eq_add_neg]
  rw [responseNeighbors, Finset.card_erase_of_mem hm, neighbors_card]

lemma outgoing_mem {n : ℕ} (w : DirectionWord n) (hw : IsTrail kernelStart kernelIncoming w)
    (i : Fin n) : wordVertex kernelStart w (i.val + 1) ∈ responseNeighbors w i := by
  rw [responseNeighbors, Finset.mem_erase]
  constructor
  · rw [AKLT.Cert.H2.vertex_succ kernelStart w i.val i.isLt]
    intro h
    have hs : (w i).step = -(wordIncoming kernelIncoming w i).step := by
      exact add_left_cancel (h.trans (sub_eq_add_neg _ _))
    rw [← AKLT.Cert.H2.reverse_step] at hs
    exact nonreverse w hw i (step_injective hs)
  · rw [AKLT.Cert.H2.vertex_succ kernelStart w i.val i.isLt]
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

lemma pair_sum_cap {n : ℕ} (w : DirectionWord n) (hw : IsTrail kernelStart kernelIncoming w)
    (i : Fin n) : (∑ p ∈ responsePairs w i, pairCoefficient w i p) ≤ responseCap := by
  let S := responseNeighbors w i
  let o := wordVertex kernelStart w (i.val + 1)
  let f : Finset Plane → ℚ := fun p => if o ∈ p then 36751 / 100000 else 18094 / 100000
  have hsub : responsePairs w i ⊆ S.powersetCard 2 := by
    apply Finset.powersetCard_mono
    apply Finset.insert_subset (outgoing_mem w hw i)
    intro z hz
    exact Finset.mem_of_mem_erase (Finset.mem_filter.mp hz).1
  have hyes : ((S.powersetCard 2).filter fun p => o ∈ p).card = 2 := by
    have := Finset.card_filter_powersetCard_subset {o} S 2
      (Finset.singleton_subset_iff.mpr (outgoing_mem w hw i)) (by simp)
    simpa [S, responseNeighbors_card, Finset.singleton_subset_iff] using this
  have hno : ((S.powersetCard 2).filter fun p => ¬o ∈ p).card = 1 := by
    have h := Finset.card_filter_add_card_filter_not (s := S.powersetCard 2) (fun p => o ∈ p)
    rw [hyes, Finset.card_powersetCard, show S.card = 3 from responseNeighbors_card w i] at h
    norm_num at h
    omega
  calc
    _ ≤ ∑ p ∈ responsePairs w i, f p :=
      Finset.sum_le_sum fun p _ => coefficient_cap w i p
    _ ≤ ∑ p ∈ S.powersetCard 2, f p :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro p _ _; dsimp [f]; split_ifs <;> norm_num)
    _ = responseCap := by norm_num [f, Finset.sum_ite, hyes, hno, responseCap]

lemma response_total {n : ℕ} (X : PairType) (w : DirectionWord n) (i : Fin n) :
    (∑ Y : PairType, ∑ s ∈ Finset.range (n + 2), responseKappa X Y s w i) =
      ∑ p ∈ responsePairs w i, pairCoefficient w i p := by
  unfold responseKappa
  calc
    _ = ∑ p ∈ responsePairs w i, ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
        if responsePairType p = Y ∧ pairShift X p = s then pairCoefficient w i p else 0 := by
      simp_rw [Finset.sum_comm (s := Finset.range (n + 2)) (t := responsePairs w i)]
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p hp
      have hs : pairShift X p ∈ Finset.range (n + 2) := by
        have := pairShift_le X w i p hp
        simp only [Finset.mem_range]
        omega
      simp [ite_and, eq_comm, hs]

lemma exposure_sum {n : ℕ} {α : Type*} (w : DirectionWord n) (t : Finset α)
    (r : α → Fin n → ℚ) (l : List (Fin n)) :
    exposureSum w (fun i => ∑ a ∈ t, r a i) l = ∑ a ∈ t, exposureSum w (r a) l := by
  induction l with
  | nil => simp [exposureSum]
  | cons i l ih => simp [exposureSum, ih, Finset.sum_add_distrib, Finset.mul_sum, mul_add]

lemma ordering_product {n : ℕ} (w : DirectionWord n) :
    trailBaseWeight kernelStart w *
      ((kernelOrdering w).map fun i => passageFactor (wordStraight kernelIncoming w i)).prod =
    trailWeight kernelStart kernelIncoming w := by
  have hfilter (l : List (Fin n)) :
      ((l.filter fun i => !wordRevisit kernelStart w i).map fun i => passageFactor (wordStraight kernelIncoming w i)).prod =
      (l.map fun i => if wordRevisit kernelStart w i then (1 : ℚ) else passageFactor (wordStraight kernelIncoming w i)).prod := by
    induction l with
    | nil => rfl
    | cons i l ih => cases h : wordRevisit kernelStart w i <;> simp [h, ih]
  rw [((ordering_perm w).map _).prod_eq]
  change trailBaseWeight kernelStart w *
    (((List.finRange n).filter _).map _).prod = _
  rw [hfilter, ← List.ofFn_eq_map, List.prod_ofFn]
  unfold trailBaseWeight trailWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases wordRevisit kernelStart w i <;> simp [div_eq_mul_inv, mul_comm]

lemma exposure_cap {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ)
    (hr : ∀ i, r i ≤ responseCap) (l : List (Fin n)) :
    exposureSum w r l ≤ (l.length : ℚ) * responseCap *
      (l.map fun i => passageFactor (wordStraight kernelIncoming w i)).prod := by
  induction l with
  | nil => simp [exposureSum]
  | cons i l ih =>
    have hprod : (1 : ℚ) ≤ (l.map fun i => passageFactor (wordStraight kernelIncoming w i)).prod := by
      apply List.one_le_prod
      intro x hx
      obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
      exact factor_one_le _
    have hC : 0 ≤ responseCap := by norm_num [responseCap]
    have hf := factor_one_le (wordStraight kernelIncoming w i)
    simp only [exposureSum, List.length_cons, Nat.cast_add, Nat.cast_one, List.map_cons, List.prod_cons]
    have hc : r i ≤ responseCap * (l.map fun i => passageFactor (wordStraight kernelIncoming w i)).prod :=
      (hr i).trans (le_mul_of_one_le_right hC hprod)
    have hh := mul_le_mul_of_nonneg_left (add_le_add hc ih) (le_trans (by norm_num) hf)
    convert hh using 1
    ring

end AKLT.W.REC070
