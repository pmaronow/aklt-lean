module
public import AKLT.Cert.H2.Words
public import AKLT.Blueprint.Rec.NodesKernel

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs
open AKLT.Blueprint.Rec
namespace AKLT.W.REC072

lemma vertexDist_le (n : ℕ) (w : DirectionWord n) (j : ℕ) :
    latticeDist (wordVertex kernelStart w j) kernelStart ≤ n := by
  simp only [latticeDist, wordVertex, kernelStart, Prod.fst_add, Prod.snd_add,
    Prod.fst_sum, Prod.snd_sum, add_sub_cancel_left]
  have hx : (∑ i : Fin n, (if i.val < j then (w i).step else (0 : Plane)).1).natAbs ≤
      ∑ i : Fin n, Int.natAbs ((if i.val < j then (w i).step else (0 : Plane)).1) := by
    simpa using Int.natAbs_sum_le (Finset.univ : Finset (Fin n))
      (fun i => (if i.val < j then (w i).step else (0 : Plane)).1)
  have hy : (∑ i : Fin n, (if i.val < j then (w i).step else (0 : Plane)).2).natAbs ≤
      ∑ i : Fin n, Int.natAbs ((if i.val < j then (w i).step else (0 : Plane)).2) := by
    simpa using Int.natAbs_sum_le (Finset.univ : Finset (Fin n))
      (fun i => (if i.val < j then (w i).step else (0 : Plane)).2)
  calc
    _ ≤ (∑ i : Fin n, Int.natAbs ((if i.val < j then (w i).step else (0 : Plane)).1)) +
        ∑ i : Fin n, Int.natAbs ((if i.val < j then (w i).step else (0 : Plane)).2) := Nat.add_le_add hx hy
    _ = ∑ i : Fin n,
        (Int.natAbs ((if i.val < j then (w i).step else (0 : Plane)).1) +
         Int.natAbs ((if i.val < j then (w i).step else (0 : Plane)).2)) := by rw [Finset.sum_add_distrib]
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => by
      split_ifs with h <;> cases w i <;> norm_num [Compass.step]
    _ = n := by simp

lemma latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  unfold latticeDist
  have hx : Int.natAbs (x.1 - z.1) ≤ Int.natAbs (x.1 - y.1) + Int.natAbs (y.1 - z.1) := by
    rw [show x.1 - z.1 = (x.1 - y.1) + (y.1 - z.1) by ring]
    exact Int.natAbs_add_le _ _
  have hy : Int.natAbs (x.2 - z.2) ≤ Int.natAbs (x.2 - y.2) + Int.natAbs (y.2 - z.2) := by
    rw [show x.2 - z.2 = (x.2 - y.2) + (y.2 - z.2) by ring]
    exact Int.natAbs_add_le _ _
  omega

lemma partition_perm {n : ℕ} (l : List (Fin n)) (p : Fin n → Bool) :
    (l.filter p ++ l.filter (fun i => !p i)).Perm l := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : p a
    · simp [h]
      exact ih
    · simp only [List.filter_cons, h, Bool.false_eq_true]
      have h₁ : (l.filter p ++ a :: l.filter (fun i => !p i)).Perm
          ((l.filter p ++ [a]) ++ l.filter (fun i => !p i)) := by
        simp [List.append_assoc]
      have h₂ : ((l.filter p ++ [a]) ++ l.filter (fun i => !p i)).Perm
          (([a] ++ l.filter p) ++ l.filter (fun i => !p i)) :=
        (List.perm_append_comm).append_right _
      have h₃ : (([a] ++ l.filter p) ++ l.filter (fun i => !p i)).Perm
          (a :: (l.filter p ++ l.filter (fun i => !p i))) := by simp
      have hmove := h₁.trans (h₂.trans h₃)
      exact hmove.trans (ih.cons a)

lemma firstVisit_nodup {n : ℕ} (w : DirectionWord n) :
    (firstVisitList w).Nodup := by
  unfold firstVisitList
  exact List.Nodup.filter _ (List.nodup_finRange n)

lemma kernelOrdering_perm {n : ℕ} (w : DirectionWord n) :
    (kernelOrdering w).Perm (firstVisitList w) := by
  unfold kernelOrdering
  split_ifs with hn
  · exact List.mergeSort_perm _ _
  · exact partition_perm _ _

lemma kernelOrdering_nodup {n : ℕ} (w : DirectionWord n) :
    (kernelOrdering w).Nodup :=
  (kernelOrdering_perm w).nodup_iff.mpr (firstVisit_nodup w)

lemma kernelOrdering_length_le {n : ℕ} (w : DirectionWord n) :
    (kernelOrdering w).length ≤ n := by
  rw [(kernelOrdering_perm w).length_eq]
  unfold firstVisitList
  exact (List.length_filter_le _ _).trans (by simp)


lemma passageFactor_ge_one (b : Bool) : 1 ≤ passageFactor b := by
  cases b <;> norm_num [passageFactor, localThreshold]

lemma passageFactor_pos (b : Bool) : 0 < passageFactor b := by
  have h := passageFactor_ge_one b
  linarith

lemma exposure_bound {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ)
    (l : List (Fin n)) (hl : l.Nodup)
    (hr : ∀ i, 0 ≤ r i) :
    exposureSum w r l ≤
      (∏ i ∈ l.toFinset, passageFactor (wordStraight kernelIncoming w i)) *
        (∑ i ∈ l.toFinset, r i) := by
  induction l with
  | nil => simp [exposureSum]
  | cons a l ih =>
    have hparts := List.nodup_cons.mp hl
    have hanot : a ∉ l := hparts.1
    have hltail : l.Nodup := hparts.2
    have hinsert : a ∉ l.toFinset := by simpa using hanot
    have hx := passageFactor_pos (wordStraight kernelIncoming w a)
    have hx1 := passageFactor_ge_one (wordStraight kernelIncoming w a)
    let P : ℚ := ∏ i ∈ l.toFinset, passageFactor (wordStraight kernelIncoming w i)
    let S : ℚ := ∑ i ∈ l.toFinset, r i
    have hP : 1 ≤ P := by
      dsimp [P]
      apply Finset.one_le_prod₀
      intro i hi
      exact passageFactor_ge_one _
    have hS : 0 ≤ S := by
      dsimp [S]
      exact Finset.sum_nonneg fun i hi => hr i
    have hE := ih hltail
    change exposureSum w r (a :: l) ≤ _
    simp only [exposureSum, List.toFinset_cons]
    rw [Finset.prod_insert hinsert, Finset.sum_insert hinsert]
    change passageFactor (wordStraight kernelIncoming w a) *
        (r a + exposureSum w r l) ≤
      passageFactor (wordStraight kernelIncoming w a) * P * (r a + S)
    calc
      _ ≤ passageFactor (wordStraight kernelIncoming w a) * (r a + P * S) := by
        have hE' : r a + exposureSum w r l ≤ r a + P * S := by
          nlinarith [hE]
        exact mul_le_mul_of_nonneg_left hE' hx.le
      _ = passageFactor (wordStraight kernelIncoming w a) * r a +
          passageFactor (wordStraight kernelIncoming w a) * (P * S) := by ring
      _ ≤ passageFactor (wordStraight kernelIncoming w a) * P * r a +
          passageFactor (wordStraight kernelIncoming w a) * (P * S) := by
        have hpr : r a ≤ P * r a := by
          simpa using mul_le_mul_of_nonneg_right hP (hr a)
        nlinarith [mul_le_mul_of_nonneg_left hpr hx.le]
      _ = passageFactor (wordStraight kernelIncoming w a) * P * (r a + S) := by ring


lemma pairCoefficient_nonneg {n : ℕ} (w : DirectionWord n) (i : Fin n) (p : Finset Plane) :
    0 ≤ pairCoefficient w i p := by
  unfold pairCoefficient
  split_ifs <;> cases wordStraight kernelIncoming w i <;>
    norm_num [alphaBound, betaBound, betaPrimeBound]

lemma pairCoefficient_le_one {n : ℕ} (w : DirectionWord n) (i : Fin n) (p : Finset Plane) :
    pairCoefficient w i p ≤ 1 := by
  unfold pairCoefficient
  split_ifs <;> cases wordStraight kernelIncoming w i <;>
    norm_num [alphaBound, betaBound, betaPrimeBound]

lemma responseKappa_nonneg {n : ℕ} (X Y : PairType) (s : ℕ)
    (w : DirectionWord n) (i : Fin n) : 0 ≤ responseKappa X Y s w i := by
  unfold responseKappa
  apply Finset.sum_nonneg
  intro p hp
  split_ifs <;> [exact pairCoefficient_nonneg _ _ _; exact le_rfl]

lemma step_mem_neighbors (x : Plane) (d : Compass) : x + d.step ∈ neighbors x := by
  unfold neighbors
  exact Finset.mem_image.mpr ⟨d, Finset.mem_univ _, rfl⟩

lemma step_latticeDist (x : Plane) (d : Compass) : latticeDist (x + d.step) x = 1 := by
  cases d <;> norm_num [latticeDist, Compass.step]

lemma neighbors_card_le_four (x : Plane) : (neighbors x).card ≤ 4 := by
  unfold neighbors
  calc
    (Finset.univ.image (fun d : Compass => x + d.step)).card ≤ Finset.univ.card := Finset.card_image_le
    _ = 4 := by decide

lemma responseCarrier_subset_neighbors {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    insert (wordVertex kernelStart w (i.val + 1)) (liveOtherNeighbors w i) ⊆
      neighbors (wordVertex kernelStart w i.val) := by
  classical
  intro z hz
  rcases Finset.mem_insert.mp hz with hz | hz
  · subst z
    rw [AKLT.Cert.H2.vertex_succ _ _ _ i.isLt]
    exact step_mem_neighbors _ _
  · unfold liveOtherNeighbors at hz
    rcases Finset.mem_filter.mp hz with ⟨hz, _⟩
    rcases Finset.mem_erase.mp hz with ⟨_, hz⟩
    rcases Finset.mem_erase.mp hz with ⟨_, hz⟩
    exact hz

set_option maxHeartbeats 500000 in
lemma responseKappa_le_six {n : ℕ} (X Y : PairType) (s : ℕ)
    (w : DirectionWord n) (i : Fin n) : responseKappa X Y s w i ≤ 6 := by
  unfold responseKappa
  calc
    _ ≤ ∑ p ∈ responsePairs w i, (1 : ℚ) := by
      apply Finset.sum_le_sum
      intro p hp
      split_ifs
      · exact pairCoefficient_le_one _ _ _
      · norm_num
    _ = (responsePairs w i).card := by simp
    _ ≤ 6 := by
      have hcard : (insert (wordVertex kernelStart w (i.val + 1)) (liveOtherNeighbors w i)).card ≤ 4 := by
        exact (Finset.card_le_card (responseCarrier_subset_neighbors w i)).trans (neighbors_card_le_four _)
      have hchoose : ((insert (wordVertex kernelStart w (i.val + 1)) (liveOtherNeighbors w i)).card).choose 2 ≤ 6 := by
        exact (Nat.choose_le_choose 2 hcard).trans (by decide)
      have hcardPairs : (responsePairs w i).card ≤ 6 := by
        calc
          (responsePairs w i).card =
              (insert (wordVertex kernelStart w (i.val + 1)) (liveOtherNeighbors w i)).card.choose 2 := by
            unfold responsePairs
            exact Finset.card_powersetCard 2 _
          _ ≤ 6 := hchoose
      exact_mod_cast hcardPairs

lemma responsePairShift_le {n : ℕ} (X : PairType) (w : DirectionWord n)
    (i : Fin n) (p : Finset Plane) (hp : p ∈ responsePairs w i) :
    pairShift X p ≤ n + 1 := by
  have hsubset := (Finset.mem_powersetCard.mp hp).1
  have hbound : ∀ z ∈ p, latticeDist z kernelStart ≤ n + 1 := by
    intro z hz
    have hzC : z ∈ insert (wordVertex kernelStart w (i.val + 1)) (liveOtherNeighbors w i) := hsubset hz
    have hzN : z ∈ neighbors (wordVertex kernelStart w i.val) :=
      responseCarrier_subset_neighbors w i hzC
    rcases Finset.mem_image.mp hzN with ⟨d, hd, heq⟩
    have hstep : latticeDist z (wordVertex kernelStart w i.val) = 1 := by
      rw [← heq]
      exact step_latticeDist _ _
    calc
      latticeDist z kernelStart ≤ latticeDist z (wordVertex kernelStart w i.val) +
          latticeDist (wordVertex kernelStart w i.val) kernelStart :=
        latticeDist_triangle z (wordVertex kernelStart w i.val) kernelStart
      _ ≤ 1 + n := by rw [hstep]; exact Nat.add_le_add_left (vertexDist_le n w i.val) 1
      _ = n + 1 := by omega
  unfold pairShift
  apply Finset.sup_le
  intro z hz
  exact (Nat.min_le_left _ _).trans (hbound z hz)

lemma responseKappa_zero_of_shift_large {n : ℕ} (X Y : PairType) (s : ℕ)
    (w : DirectionWord n) (i : Fin n) (hs : n + 1 < s) :
    responseKappa X Y s w i = 0 := by
  unfold responseKappa
  apply Finset.sum_eq_zero
  intro p hp
  split_ifs with h
  · have hshift := responsePairShift_le X w i p hp
    omega
  · rfl

lemma exposureSum_eq_zero_of_reward_zero {n : ℕ} (w : DirectionWord n)
    (r : Fin n → ℚ) (hr : ∀ i, r i = 0) (l : List (Fin n)) : exposureSum w r l = 0 := by
  induction l with
  | nil => simp [exposureSum]
  | cons i l ih => simp [exposureSum, hr i, ih]

lemma kernelLengthCoefficient_zero_of_shift_large (X Y : PairType) (n s : ℕ)
    (hs : n + 1 < s) : kernelLengthCoefficient X Y s n = 0 := by
  classical
  unfold kernelLengthCoefficient
  apply Finset.sum_eq_zero
  intro w hw
  have hr : ∀ i, responseKappa X Y s w i = 0 :=
    fun i => responseKappa_zero_of_shift_large X Y s w i hs
  by_cases hc : ClosedTrail X w
  · simp [hc, exposureSum_eq_zero_of_reward_zero w _ hr]
  · simp [hc]

lemma firstVisit_toFinset {n : ℕ} (w : DirectionWord n) :
    (firstVisitList w).toFinset = Finset.univ.filter (fun i => !wordRevisit kernelStart w i) := by
  simp [firstVisitList, List.toFinset_filter]

lemma trailWeight_eq_base_mul_firstVisits {n : ℕ} (w : DirectionWord n) :
    (trailWeight kernelStart kernelIncoming w : ℚ) = trailBaseWeight kernelStart w *
      ∏ i ∈ (firstVisitList w).toFinset, passageFactor (wordStraight kernelIncoming w i) := by
  rw [trailWeight, trailBaseWeight, firstVisit_toFinset, Finset.prod_filter]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases wordRevisit kernelStart w i <;>
    simp [passageFactor, localThreshold] <;> ring

lemma kernelOrdering_product_eq_firstVisits {n : ℕ} (w : DirectionWord n) :
    ∏ i ∈ (kernelOrdering w).toFinset, passageFactor (wordStraight kernelIncoming w i) =
      ∏ i ∈ (firstVisitList w).toFinset, passageFactor (wordStraight kernelIncoming w i) := by
  have hset : (kernelOrdering w).toFinset = (firstVisitList w).toFinset := by
    apply Finset.ext
    intro i
    simp only [List.mem_toFinset]
    exact (kernelOrdering_perm w).mem_iff
  rw [hset]

lemma kernelOrdering_reward_sum_le {n : ℕ} (w : DirectionWord n) (X Y : PairType) (s : ℕ) :
    (∑ i ∈ (kernelOrdering w).toFinset, responseKappa X Y s w i) ≤ (6 * n : ℚ) := by
  calc
    _ ≤ ∑ _i ∈ (kernelOrdering w).toFinset, (6 : ℚ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact responseKappa_le_six X Y s w i
    _ = ((kernelOrdering w).toFinset.card : ℚ) * 6 := by simp [mul_comm]
    _ ≤ (n : ℚ) * 6 := by
      have hcard : (kernelOrdering w).toFinset.card ≤ n := by
        rw [List.toFinset_card_of_nodup (kernelOrdering_nodup w)]
        exact kernelOrdering_length_le w
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by norm_num)
    _ = (6 * n : ℚ) := by ring

lemma exposedTrail_le {n : ℕ} (w : DirectionWord n) (X Y : PairType) (s : ℕ) :
    (trailBaseWeight kernelStart w * exposureSum w (responseKappa X Y s w) (kernelOrdering w) : ℚ) ≤
      (6 * n : ℚ) * (trailWeight kernelStart kernelIncoming w : ℚ) := by
  have hnonneg : ∀ i, 0 ≤ responseKappa X Y s w i := responseKappa_nonneg X Y s w
  have hexp := exposure_bound w (responseKappa X Y s w) (kernelOrdering w)
    (kernelOrdering_nodup w) hnonneg
  rw [kernelOrdering_product_eq_firstVisits w] at hexp
  have hb : 0 ≤ trailBaseWeight kernelStart w := by
    unfold trailBaseWeight
    apply Finset.prod_nonneg
    intro i hi
    split_ifs <;> norm_num
  have hr := kernelOrdering_reward_sum_le w X Y s
  have hPnonneg : 0 ≤ ∏ i ∈ (firstVisitList w).toFinset,
      passageFactor (wordStraight kernelIncoming w i) :=
    Finset.prod_nonneg fun i hi => (passageFactor_pos _).le
  calc
    trailBaseWeight kernelStart w * exposureSum w (responseKappa X Y s w) (kernelOrdering w)
        ≤ trailBaseWeight kernelStart w *
          ((∏ i ∈ (firstVisitList w).toFinset, passageFactor (wordStraight kernelIncoming w i)) *
            ∑ i ∈ (kernelOrdering w).toFinset, responseKappa X Y s w i) :=
      mul_le_mul_of_nonneg_left hexp hb
    _ = (trailBaseWeight kernelStart w *
          ∏ i ∈ (firstVisitList w).toFinset, passageFactor (wordStraight kernelIncoming w i)) *
            ∑ i ∈ (kernelOrdering w).toFinset, responseKappa X Y s w i := by ring
    _ ≤ (trailBaseWeight kernelStart w *
          ∏ i ∈ (firstVisitList w).toFinset, passageFactor (wordStraight kernelIncoming w i)) * (6 * n) :=
      mul_le_mul_of_nonneg_left hr (mul_nonneg hb hPnonneg)
    _ = (6 * n : ℚ) * (trailWeight kernelStart kernelIncoming w : ℚ) := by
      rw [trailWeight_eq_base_mul_firstVisits]
      ring


lemma exposureSum_nonneg {n : ℕ} (w : DirectionWord n) (r : Fin n → ℚ)
    (hr : ∀ i, 0 ≤ r i) : ∀ l : List (Fin n), 0 ≤ exposureSum w r l := by
  intro l
  induction l with
  | nil => simp [exposureSum]
  | cons i l ih =>
    exact mul_nonneg (passageFactor_pos _).le (add_nonneg (hr i) ih)

lemma trailWeight_nonneg {n : ℕ} (w : DirectionWord n) :
    0 ≤ (trailWeight kernelStart kernelIncoming w : ℚ) := by
  unfold trailWeight
  apply Finset.prod_nonneg
  intro i hi
  split_ifs
  · norm_num
  · exact div_nonneg (le_trans (by norm_num) (passageFactor_ge_one _)) (by norm_num)

lemma kernelLengthCoefficient_nonneg (X Y : PairType) (s n : ℕ) :
    0 ≤ kernelLengthCoefficient X Y s n := by
  classical
  unfold kernelLengthCoefficient
  apply Finset.sum_nonneg
  intro w hw
  split_ifs
  · apply mul_nonneg
    · unfold trailBaseWeight
      apply Finset.prod_nonneg
      intro i hi
      split_ifs <;> norm_num
    · exact exposureSum_nonneg w _ (responseKappa_nonneg X Y s w) (kernelOrdering w)
  · exact le_rfl

lemma kernelLengthCoefficient_bound {CV q : ℝ} (hbound : OpenTrailBound CV q)
    (X Y : PairType) (s n : ℕ) :
    (kernelLengthCoefficient X Y s n : ℝ) ≤ (6 * n : ℝ) * CV * q ^ n := by
  classical
  rcases hbound with ⟨hCV, hqpos, hqlt, htrail⟩
  have hterms : ∀ w : DirectionWord n,
      (if ClosedTrail X w then
          (trailBaseWeight kernelStart w * exposureSum w (responseKappa X Y s w) (kernelOrdering w) : ℚ)
        else 0 : ℝ) ≤
        (6 * n : ℝ) * (if IsTrail kernelStart kernelIncoming w then
          (trailWeight kernelStart kernelIncoming w : ℚ) else 0 : ℝ) := by
    intro w
    by_cases hc : ClosedTrail X w
    · have ht : IsTrail kernelStart kernelIncoming w := hc.1
      simp [hc, ht]
      exact_mod_cast exposedTrail_le w X Y s
    · by_cases ht : IsTrail kernelStart kernelIncoming w
      · simp [hc, ht]
        exact mul_nonneg (by positivity) (by exact_mod_cast trailWeight_nonneg w)
      · simp [hc, ht]
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun w hw => hterms w)
  have hH2 := htrail n kernelStart kernelIncoming
  have hscale : (0 : ℝ) ≤ 6 * n := by positivity
  have hsum2 := hsum
  rw [← Finset.mul_sum] at hsum2
  have hsum3 : (∑ w : DirectionWord n, ((if ClosedTrail X w then
        (trailBaseWeight kernelStart w * exposureSum w (responseKappa X Y s w) (kernelOrdering w) : ℚ)
      else 0 : ℚ) : ℝ)) ≤
      (6 * n : ℝ) * ∑ w : DirectionWord n, if IsTrail kernelStart kernelIncoming w then
        (trailWeight kernelStart kernelIncoming w : ℝ) else 0 := by
    calc
      _ = ∑ w : DirectionWord n, if ClosedTrail X w then
          ((trailBaseWeight kernelStart w * exposureSum w (responseKappa X Y s w) (kernelOrdering w) : ℚ) : ℝ)
        else 0 := by
          apply Finset.sum_congr rfl
          intro w hw
          by_cases hc : ClosedTrail X w <;> simp [hc]
      _ ≤ _ := hsum2
  have hcoeff : (kernelLengthCoefficient X Y s n : ℝ) =
      ∑ w : DirectionWord n, ((if ClosedTrail X w then
        (trailBaseWeight kernelStart w * exposureSum w (responseKappa X Y s w) (kernelOrdering w) : ℚ)
      else 0 : ℚ) : ℝ) := by
    unfold kernelLengthCoefficient
    rw [Rat.cast_sum]
  calc
    (kernelLengthCoefficient X Y s n : ℝ) =
        ∑ w : DirectionWord n, ((if ClosedTrail X w then
          (trailBaseWeight kernelStart w * exposureSum w (responseKappa X Y s w) (kernelOrdering w) : ℚ)
        else 0 : ℚ) : ℝ) := hcoeff
    _ ≤ (6 * n : ℝ) * ∑ w : DirectionWord n, if IsTrail kernelStart kernelIncoming w then
        (trailWeight kernelStart kernelIncoming w : ℝ) else 0 := hsum3
    _ ≤ (6 * n : ℝ) * (CV * q ^ n) := mul_le_mul_of_nonneg_left hH2 hscale
    _ = (6 * n : ℝ) * CV * q ^ n := by ring


lemma finite_cutoff_reorder (N : ℕ) (f : ℕ → PairType → ℕ → ℝ) :
    (∑ n ∈ Finset.range N, ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2), f n Y s) =
      ∑ Y : PairType, ∑ s ∈ Finset.range (N + 1), ∑ n ∈ Finset.range N,
        if s < n + 2 then f n Y s else 0 := by
  classical
  have hinner (n : ℕ) (hn : n ∈ Finset.range N) (Y : PairType) :
      (∑ s ∈ Finset.range (n + 2), f n Y s) =
        ∑ s ∈ Finset.range (N + 1), if s < n + 2 then f n Y s else 0 := by
    have hfilter : (Finset.range (N + 1)).filter (fun s => s < n + 2) =
        Finset.range (n + 2) := by
      ext s
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨hs, hlt⟩
        exact hlt
      · intro hs
        exact ⟨by have hn' : n < N := Finset.mem_range.mp hn; omega, hs⟩
    rw [← Finset.sum_filter, hfilter]
  calc
    _ = ∑ n ∈ Finset.range N, ∑ Y : PairType, ∑ s ∈ Finset.range (N + 1),
          if s < n + 2 then f n Y s else 0 := by
        apply Finset.sum_congr rfl
        intro n hn
        apply Finset.sum_congr rfl
        intro Y hY
        exact hinner n hn Y
    _ = ∑ Y : PairType, ∑ s ∈ Finset.range (N + 1), ∑ n ∈ Finset.range N,
          if s < n + 2 then f n Y s else 0 := by
        rw [Finset.sum_comm (s := Finset.range N) (t := Finset.univ)]
        simp_rw [Finset.sum_comm (s := Finset.range N) (t := Finset.range (N + 1))]

/-- Residual analytic bridge: H2 controls the individual coefficient series and the
full row, and `toReal` agrees with each coefficient tsum. The combinatorial comparison
and every finite cutoff estimate are proved separately above/below. -/
def ResidualKernelSeriesBridge : Prop :=
  ∀ CV q : ℝ, OpenTrailBound CV q → ∀ X : PairType,
    (∀ Y s, Summable (fun n : ℕ => (kernelLengthCoefficient X Y s n : ℝ))) ∧
    (∀ Y s, realKernel X Y s = ∑' n : ℕ, (kernelLengthCoefficient X Y s n : ℝ)) ∧
    (∀ Y s, 0 ≤ realKernel X Y s) ∧
    Summable (fun j : PairType × ℕ => realKernel X j.1 j.2 * 2)

theorem main_of_residual (hres : ResidualKernelSeriesBridge) :
    AKLT.Blueprint.Rec.FiniteKernelTailDominationStatement := by
  classical
  intro CV q hbound F hF X d N
  dsimp [ResidualKernelSeriesBridge] at hres
  rcases hres CV q hbound X with ⟨hcoef, hexpand, hreal, hrow⟩
  let g : PairType × ℕ → ℝ := fun j => realKernel X j.1 j.2 * F j.1 (d - (j.2 : ℤ))
  have hg_nonneg : ∀ j, 0 ≤ g j := by
    intro j
    dsimp [g]
    exact mul_nonneg (hreal j.1 j.2) (hF j.1 (d - (j.2 : ℤ))).1
  have hg_le : ∀ j, g j ≤ realKernel X j.1 j.2 * 2 := by
    intro j
    dsimp [g]
    exact mul_le_mul_of_nonneg_left (hF j.1 (d - (j.2 : ℤ))).2 (hreal j.1 j.2)
  have hgsum : Summable g := Summable.of_nonneg_of_le hg_nonneg hg_le hrow
  have hpair (Y : PairType) (s : ℕ) :
      (∑ n ∈ Finset.range N, (kernelLengthCoefficient X Y s n : ℝ) * F Y (d - (s : ℤ))) ≤
        realKernel X Y s * F Y (d - (s : ℤ)) := by
    let c : ℕ → ℝ := fun n => (kernelLengthCoefficient X Y s n : ℝ)
    have hc := hcoef Y s
    have hcf : Summable (fun n => c n * F Y (d - (s : ℤ))) := hc.mul_right _
    have hc0 (n : ℕ) : 0 ≤ c n := by
      dsimp [c]
      exact_mod_cast kernelLengthCoefficient_nonneg X Y s n
    have hsum := hcf.sum_le_tsum (Finset.range N) (by
      intro n hn
      exact mul_nonneg (hc0 n) (hF Y (d - (s : ℤ))).1)
    calc
      _ ≤ ∑' n : ℕ, c n * F Y (d - (s : ℤ)) := by simpa [c] using hsum
      _ = (∑' n : ℕ, c n) * F Y (d - (s : ℤ)) := hc.tsum_mul_right _
      _ = realKernel X Y s * F Y (d - (s : ℤ)) := by rw [← hexpand Y s]
  let f : ℕ → PairType → ℕ → ℝ := fun n Y s =>
    (kernelLengthCoefficient X Y s n : ℝ) * F Y (d - (s : ℤ))
  have hfinite := finite_cutoff_reorder N f
  rw [hfinite]
  calc
    (∑ Y : PairType, ∑ s ∈ Finset.range (N + 1), ∑ n ∈ Finset.range N,
        if s < n + 2 then f n Y s else 0) ≤
      ∑ Y : PairType, ∑ s ∈ Finset.range (N + 1),
        realKernel X Y s * F Y (d - (s : ℤ)) := by
          apply Finset.sum_le_sum
          intro Y hY
          apply Finset.sum_le_sum
          intro s hs
          calc
            _ ≤ ∑ n ∈ Finset.range N, f n Y s := by
              apply Finset.sum_le_sum
              intro n hn
              split_ifs
              · exact le_rfl
              · exact (mul_nonneg (by exact_mod_cast kernelLengthCoefficient_nonneg X Y s n)
                  (hF Y (d - (s : ℤ))).1)
            _ ≤ realKernel X Y s * F Y (d - (s : ℤ)) := by
              apply hpair
    _ ≤ ∑' j : PairType × ℕ, g j := by
      calc
        _ = ∑ j ∈ Finset.univ.product (Finset.range (N + 1)), g j := by
          symm
          change ∑ j ∈ Finset.univ ×ˢ Finset.range (N + 1),
              realKernel X j.1 j.2 * F j.1 (d - (j.2 : ℤ)) =
            ∑ Y : PairType, ∑ s ∈ Finset.range (N + 1),
              realKernel X Y s * F Y (d - (s : ℤ))
          exact Finset.sum_product' Finset.univ (Finset.range (N + 1))
            (fun Y s => realKernel X Y s * F Y (d - (s : ℤ)))
        _ ≤ ∑' j : PairType × ℕ, g j :=
          hgsum.sum_le_tsum (Finset.univ.product (Finset.range (N + 1)))
            (fun j hj => hg_nonneg j)
    _ = renewalOp realKernel F X d := by rfl

end AKLT.W.REC072
