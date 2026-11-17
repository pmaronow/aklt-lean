module
public import AKLT.Blueprint.Top.Computation

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Cert.H2

set_option maxHeartbeats 2000000

attribute [local instance] Classical.propDecidable

@[simp] theorem vertex_zero {n : ℕ} (u : Plane) (w : DirectionWord n) :
    wordVertex u w 0 = u := by simp [wordVertex]

theorem vertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n) (j : ℕ) (hj : j < n) :
    wordVertex u w (j + 1) = wordVertex u w j + (w ⟨j, hj⟩).step := by
  have hh (i : Fin n) :
      (if i.val < j + 1 then (w i).step else 0) =
      (if i.val < j then (w i).step else 0) +
        (if i = ⟨j, hj⟩ then (w i).step else 0) := by
    by_cases h : i.val < j
    · simp [h, show i.val < j + 1 by omega, show i ≠ ⟨j, hj⟩ by intro he; have := congrArg Fin.val he; simp at this; omega]
    · by_cases he : i = ⟨j, hj⟩
      · subst i; simp
      · simp [h, he, show ¬i.val < j + 1 by
          have : i.val ≠ j := fun h => he (Fin.ext h)
          omega]
  simp only [wordVertex, hh, Finset.sum_add_distrib]
  simp [add_assoc]

theorem vertex_translate {n : ℕ} (u : Plane) (w : DirectionWord n) (j : ℕ) :
    wordVertex u w j = u + wordVertex (0, 0) w j := by simp [wordVertex]

/-- A contiguous subword, with its endpoints retained in the index proof. -/
def slice {n : ℕ} (w : DirectionWord n) (a l : ℕ) (h : a + l ≤ n) : DirectionWord l :=
  fun i => w ⟨a + i.val, by omega⟩

theorem slice_vertex {n : ℕ} (u : Plane) (w : DirectionWord n) (a l : ℕ)
    (h : a + l ≤ n) (j : ℕ) (hj : j ≤ l) :
    wordVertex (0, 0) (slice w a l h) j = wordVertex u w (a + j) - wordVertex u w a := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [vertex_succ _ _ j (by omega), ih (by omega),
      show a + (j + 1) = (a + j) + 1 by omega, vertex_succ _ _ (a + j) (by omega)]
    simp [slice]; abel

theorem slice_bond {n : ℕ} (u : Plane) (w : DirectionWord n) (a l : ℕ)
    (h : a + l ≤ n) (i : Fin l) :
    wordBond (0, 0) (slice w a l h) i =
      (wordBond u w ⟨a + i.val, by omega⟩).image (fun x => x - wordVertex u w a) := by
  simp only [wordBond, slice_vertex u w a l h i.val (by omega),
    slice_vertex u w a l h (i.val + 1) (by omega)]
  simp [Finset.image_insert, Finset.image_singleton, Nat.add_assoc]

theorem raw_slice {n : ℕ} (u : Plane) (w : DirectionWord n)
    (hw : Function.Injective (wordBond u w)) (a l : ℕ) (h : a + l ≤ n) :
    RawWindow (slice w a l h) := by
  intro i j hij
  have he : wordBond u w ⟨a + i.val, by omega⟩ =
      wordBond u w ⟨a + j.val, by omega⟩ := by
    apply Finset.image_injective (f := fun x : Plane => x - wordVertex u w a)
      (fun x y hxy => (sub_left_inj).mp hxy)
    simpa only [slice_bond u w a l h] using hij
  have := congrArg Fin.val (hw he)
  exact Fin.ext (by simpa using this)

def initWord {n : ℕ} (w : DirectionWord (n + 1)) : DirectionWord n :=
  slice w 0 n (by omega)

def snoc {n : ℕ} (w : DirectionWord n) (d : Compass) : DirectionWord (n + 1) :=
  Fin.snoc w d

@[simp] theorem initWord_snoc {n : ℕ} (w : DirectionWord n) (d : Compass) :
    initWord (snoc w d) = w := by
  funext i
  simp only [initWord, slice, Nat.zero_add]
  change snoc w d i.castSucc = w i
  exact Fin.snoc_castSucc (α := fun _ => Compass) d w i

@[simp] theorem snoc_last {n : ℕ} (w : DirectionWord n) (d : Compass) :
    snoc w d (Fin.last n) = d := by simp [snoc]

theorem snoc_initWord {n : ℕ} (w : DirectionWord (n + 1)) :
    snoc (initWord w) (w (Fin.last n)) = w := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [snoc, Fin.snoc_castSucc, initWord, slice, Nat.zero_add]
    exact congrArg w (Fin.ext rfl)

def wordSnocEquiv (n : ℕ) : DirectionWord n × Compass ≃ DirectionWord (n + 1) where
  toFun p := snoc p.1 p.2
  invFun w := (initWord w, w (Fin.last n))
  left_inv p := by simp
  right_inv := snoc_initWord

theorem sum_snoc {n : ℕ} {R : Type*} [AddCommMonoid R] (f : DirectionWord (n + 1) → R) :
    (∑ w, f w) = ∑ w : DirectionWord n, ∑ d : Compass, f (snoc w d) := by
  rw [← Fintype.sum_prod_type (f := fun p : DirectionWord n × Compass => f (snoc p.1 p.2))]
  exact (Equiv.sum_comp (wordSnocEquiv n) f).symm

theorem initWord_vertex {n : ℕ} (u : Plane) (w : DirectionWord (n + 1))
    (j : ℕ) (hj : j ≤ n) : wordVertex u (initWord w) j = wordVertex u w j := by
  have := slice_vertex u w 0 n (by omega) j hj
  rw [vertex_translate]
  simpa [initWord] using congrArg (u + ·) this

theorem initWord_bond {n : ℕ} (u : Plane) (w : DirectionWord (n + 1)) (i : Fin n) :
    wordBond u (initWord w) i = wordBond u w i.castSucc := by
  simp [wordBond, initWord_vertex u w i.val (by omega),
    initWord_vertex u w (i.val + 1) (by omega)]

theorem trail_initWord {n : ℕ} (u : Plane) (incoming : Compass)
    (w : DirectionWord (n + 1)) (hw : IsTrail u incoming w) :
    IsTrail u incoming (initWord w) := by
  constructor
  · intro i j hij
    exact Fin.castSucc_injective n (hw.1 (by simpa only [initWord_bond] using hij))
  · intro i hi
    have he : initWord w i = w i.castSucc := congrArg w (Fin.ext (by simp))
    rw [he]
    exact hw.2 i.castSucc hi

theorem snoc_apply_lt {n : ℕ} (w : DirectionWord n) (d : Compass) (j : ℕ) (hj : j < n) :
    snoc w d ⟨j, by omega⟩ = w ⟨j, hj⟩ := by
  rw [show (⟨j, by omega⟩ : Fin (n + 1)) = (⟨j, hj⟩ : Fin n).castSucc by exact Fin.ext rfl]
  exact Fin.snoc_castSucc (α := fun _ => Compass) d w ⟨j, hj⟩

theorem snoc_vertex {n : ℕ} (u : Plane) (w : DirectionWord n) (d : Compass)
    (j : ℕ) (hj : j ≤ n) : wordVertex u (snoc w d) j = wordVertex u w j := by
  simpa using (initWord_vertex u (snoc w d) j hj).symm

theorem snoc_bond {n : ℕ} (u : Plane) (w : DirectionWord n) (d : Compass) (i : Fin n) :
    wordBond u (snoc w d) i.castSucc = wordBond u w i := by
  simpa using (initWord_bond u (snoc w d) i).symm

theorem snoc_departure {n : ℕ} (u : Plane) (w : DirectionWord n) (d : Compass)
    (j : ℕ) (hj : j ≤ n) (x : Plane) :
    departureCount u (snoc w d) j x = departureCount u w j x := by
  simp only [departureCount, min_eq_left hj, min_eq_left (show j ≤ n + 1 by omega)]
  congr 1
  ext k
  by_cases hk : k < j
  · simp [Finset.mem_filter, Finset.mem_range, hk, snoc_vertex u w d k (by omega)]
  · simp [Finset.mem_filter, Finset.mem_range, hk]

theorem snoc_old_revisit {n : ℕ} (u : Plane) (w : DirectionWord n) (d : Compass) (i : Fin n) :
    wordRevisit u (snoc w d) i.castSucc = wordRevisit u w i := by
  simp only [wordRevisit, Fin.val_castSucc, snoc_vertex u w d i.val (by omega),
    snoc_departure u w d i.val (by omega)]

theorem snoc_old_straight {n : ℕ} (incoming : Compass) (w : DirectionWord n) (d : Compass)
    (i : Fin n) : wordStraight incoming (snoc w d) i.castSucc = wordStraight incoming w i := by
  simp only [wordStraight, wordIncoming, Fin.val_castSucc, snoc, Fin.snoc_castSucc]
  split_ifs with h
  · rfl
  · rw [show Fin.snoc (α := fun _ => Compass) w d ⟨i.val - 1, by omega⟩ =
        w ⟨i.val - 1, by omega⟩ from snoc_apply_lt w d _ (by omega)]

def nextIncoming {n : ℕ} (incoming : Compass) (w : DirectionWord n) : Compass :=
  if h : 0 < n then w ⟨n - 1, by omega⟩ else incoming

def nextFactor {n : ℕ} (u : Plane) (incoming : Compass) (w : DirectionWord n)
    (d : Compass) : ℚ :=
  if 0 < departureCount u w n (wordVertex u w n) then 1 / 5
  else passageFactor (decide (d = nextIncoming incoming w)) / 3

theorem snoc_factor {n : ℕ} (u : Plane) (incoming : Compass) (w : DirectionWord n)
    (d : Compass) : trailWeight u incoming (snoc w d) =
      trailWeight u incoming w * nextFactor u incoming w d := by
  unfold trailWeight
  rw [Fin.prod_univ_castSucc]
  simp only [snoc_old_revisit, snoc_old_straight]
  congr 1
  have hi : wordIncoming incoming (snoc w d) (Fin.last n) = nextIncoming incoming w := by
    unfold wordIncoming nextIncoming
    by_cases hn : n = 0
    · subst n; simp
    · simp only [Fin.val_last, dite_eq_right hn, dite_eq_left (show 0 < n by omega)]
      exact snoc_apply_lt w d _ (by omega)
  simp only [wordRevisit, wordStraight, Fin.val_last,
    snoc_vertex u w d n le_rfl, snoc_departure u w d n le_rfl, snoc_last, hi,
    decide_eq_true_eq, nextFactor]

theorem factor_nonneg {n : ℕ} (u : Plane) (incoming : Compass) (w : DirectionWord n)
    (d : Compass) : 0 ≤ nextFactor u incoming w d := by
  unfold nextFactor
  split_ifs <;> cases h : decide (d = nextIncoming incoming w) <;>
    norm_num [passageFactor, localThreshold]

theorem factor_le {n : ℕ} (u : Plane) (incoming : Compass) (w : DirectionWord n)
    (d : Compass) : nextFactor u incoming w d ≤ passageFactor false / 3 := by
  unfold nextFactor
  split_ifs <;> cases h : decide (d = nextIncoming incoming w) <;>
    norm_num [passageFactor, localThreshold]

theorem weight_nonneg {n : ℕ} (u : Plane) (incoming : Compass) (w : DirectionWord n) :
    0 ≤ trailWeight u incoming w := by
  unfold trailWeight
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> cases h : wordStraight incoming w i <;>
    norm_num [passageFactor, localThreshold]

theorem snoc_last_bond {n : ℕ} (u : Plane) (w : DirectionWord n) (d : Compass) :
    wordBond u (snoc w d) (Fin.last n) = {wordVertex u w n, wordVertex u w n + d.step} := by
  simp only [wordBond, Fin.val_last, vertex_succ u (snoc w d) n (by omega),
    snoc_vertex u w d n le_rfl]
  rw [show (⟨n, by omega⟩ : Fin (n+1)) = Fin.last n by exact Fin.ext rfl, snoc_last]

theorem snoc_fresh {n : ℕ} (u : Plane) (incoming : Compass) (w : DirectionWord n)
    (d : Compass) (hw : IsTrail u incoming (snoc w d)) (i : Fin n) :
    wordBond u w i ≠ {wordVertex u w n, wordVertex u w n + d.step} := by
  intro he
  have hh := hw.1 (a₁ := i.castSucc) (a₂ := Fin.last n)
    (by simpa only [snoc_bond, snoc_last_bond] using he)
  have := congrArg Fin.val hh
  simp at this
  omega

@[simp] theorem reverse_step (d : Compass) : d.reverse.step = -d.step := by
  cases d <;> rfl

theorem snoc_nonreverse {n : ℕ} (u : Plane) (incoming : Compass) (w : DirectionWord n)
    (d : Compass) (hw : IsTrail u incoming (snoc w d)) :
    d ≠ (nextIncoming incoming w).reverse := by
  by_cases hn : n = 0
  · subst n
    have hh := hw.2 (Fin.last 0) rfl
    rw [snoc_last] at hh
    simpa [nextIncoming] using hh
  · intro hd
    have hn' : 0 < n := by omega
    have hf := snoc_fresh u incoming w d hw ⟨n - 1, by omega⟩
    apply hf
    have hv := vertex_succ u w (n - 1) (by omega)
    simp only [show n - 1 + 1 = n by omega] at hv
    have hd' : d = (w ⟨n - 1, by omega⟩).reverse := by
      simpa [nextIncoming, hn'] using hd
    simp only [wordBond, hd', reverse_step, show n - 1 + 1 = n by omega]
    rw [hv]
    have ha : wordVertex u w (n - 1) + (w ⟨n - 1, by omega⟩).step +
        -(w ⟨n - 1, by omega⟩).step = wordVertex u w (n - 1) := by abel
    rw [ha]
    exact Finset.pair_comm _ _

theorem raw_snoc {n : ℕ} (w : DirectionWord n) (d : Compass) (hw : RawWindow w)
    (hf : ∀ i, wordBond (0, 0) w i ≠
      {wordVertex (0, 0) w n, wordVertex (0, 0) w n + d.step}) : RawWindow (snoc w d) := by
  intro i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;> intro he
  · rfl
  · exact False.elim (hf _ (by simpa only [snoc_last_bond, snoc_bond] using he.symm))
  · exact False.elim (hf _ (by simpa only [snoc_last_bond, snoc_bond] using he))
  · exact congrArg Fin.castSucc (hw (by simpa only [snoc_bond] using he))

theorem successor_raw {m : ℕ} (w : DirectionWord m) (d : Compass)
    (hw : RawWindow w) (hd : WindowAdmissible w d) : RawWindow (windowSuccessor w d) := by
  by_cases hm : m = 0
  · subst m
    intro i; exact Fin.elim0 i
  have hs := raw_slice (0, 0) (snoc w d) (raw_snoc w d hw hd.2) 1 m (by omega)
  have he : slice (snoc w d) 1 m (by omega) = windowSuccessor w d := by
    funext i
    unfold slice windowSuccessor
    split_ifs with hi
    · rw [show snoc w d ⟨1 + i.val, by omega⟩ = w ⟨i.val + 1, hi⟩ by
        simpa [Nat.add_comm] using snoc_apply_lt w d (i.val + 1) hi]
    · have hi' : 1 + i.val = m := by omega
      simp only [hi']
      rw [show (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m by exact Fin.ext rfl, snoc_last]
  rwa [he] at hs

theorem lastWindow_slice {m n : ℕ} (w : DirectionWord n) (hm : m ≤ n) :
    lastWindowWord m w = slice w (n - m) m (by omega) := by
  funext i
  simp only [lastWindowWord, slice, dite_eq_left (show n - m + i.val < n by omega)]

theorem lastWindow_raw {m n : ℕ} (u : Plane) (incoming : Compass) (w : DirectionWord n)
    (hw : IsTrail u incoming w) (hm : m ≤ n) : RawWindow (lastWindowWord m w) := by
  rw [lastWindow_slice w hm]
  exact raw_slice u w hw.1 _ _ _

theorem lastWindow_snoc {m n : ℕ} (w : DirectionWord n) (d : Compass)
    (_hm : 1 ≤ m) (hmn : m ≤ n) :
    lastWindowWord m (snoc w d) = windowSuccessor (lastWindowWord m w) d := by
  funext i
  change (if h : n + 1 - m + i.val < n + 1 then
    snoc w d ⟨n + 1 - m + i.val, h⟩ else .east) = _
  rw [dite_eq_left (show n + 1 - m + i.val < n + 1 by omega)]
  unfold windowSuccessor
  split_ifs with hi
  · rw [snoc_apply_lt w d _ (by omega)]
    unfold lastWindowWord
    rw [dite_eq_left (show n - m + (i.val + 1) < n by omega)]
    exact congrArg w (Fin.ext (by simp; omega))
  · have he : n + 1 - m + i.val = n := by omega
    simp only [he]
    rw [show (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n by exact Fin.ext rfl, snoc_last]

theorem lastWindow_arrival {m n : ℕ} (incoming : Compass) (w : DirectionWord n)
    (hm : 1 ≤ m) (hmn : m ≤ n) :
    windowArrival (lastWindowWord m w) = nextIncoming incoming w := by
  unfold windowArrival nextIncoming lastWindowWord
  simp only [dite_eq_left (show 0 < m by omega), dite_eq_left (show 0 < n by omega),
    dite_eq_left (show n - m + (m - 1) < n by omega)]
  congr 1
  apply Fin.ext
  simp
  omega

end AKLT.Cert.H2
