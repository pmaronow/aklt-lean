import AKLT.Cert.H2.Words

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Cert.H2

set_option autoImplicit false
set_option maxHeartbeats 400000
attribute [local instance] Classical.propDecidable

/-- Affine changes of coordinates used only to make the initial data uniform. -/
structure FrameChange where
  point : Plane ≃ Plane
  direction : Compass ≃ Compass
  step : ∀ x d, point (x + d.step) = point x + (direction d).step
  reverse : ∀ d, direction d.reverse = (direction d).reverse

def FrameChange.word (F : FrameChange) {n : ℕ} (w : DirectionWord n) : DirectionWord n :=
  fun i => F.direction (w i)

theorem frame_vertex (F : FrameChange) {n : ℕ} (u : Plane) (w : DirectionWord n)
    (j : ℕ) (hj : j ≤ n) :
    wordVertex (F.point u) (F.word w) j = F.point (wordVertex u w j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [vertex_succ _ _ j (by omega), ih (by omega), vertex_succ _ _ j (by omega), F.step]
    rfl

theorem frame_bond (F : FrameChange) {n : ℕ} (u : Plane) (w : DirectionWord n) (i : Fin n) :
    wordBond (F.point u) (F.word w) i = (wordBond u w i).image F.point := by
  simp [wordBond, frame_vertex F u w i.val (by omega),
    frame_vertex F u w (i.val + 1) (by omega)]

theorem frame_trail (F : FrameChange) {n : ℕ} (u : Plane) (incoming : Compass)
    (w : DirectionWord n) :
    IsTrail (F.point u) (F.direction incoming) (F.word w) ↔ IsTrail u incoming w := by
  unfold IsTrail
  constructor
  · rintro ⟨hi, hr⟩
    constructor
    · intro i j hij
      apply hi
      simpa only [frame_bond] using congrArg (Finset.image F.point) hij
    · intro i hi he
      apply hr i hi
      simpa only [FrameChange.word, ← F.reverse] using congrArg F.direction he
  · rintro ⟨hi, hr⟩
    constructor
    · intro i j hij
      apply hi
      apply Finset.image_injective F.point.injective
      simpa only [frame_bond] using hij
    · intro i hi he
      apply hr i hi
      apply F.direction.injective
      simpa only [FrameChange.word, F.reverse] using he

theorem frame_revisit (F : FrameChange) {n : ℕ} (u : Plane) (w : DirectionWord n) (i : Fin n) :
    wordRevisit (F.point u) (F.word w) i = wordRevisit u w i := by
  have he : departureCount (F.point u) (F.word w) i.val
      (wordVertex (F.point u) (F.word w) i.val) =
      departureCount u w i.val (wordVertex u w i.val) := by
    unfold departureCount
    congr 1
    apply Finset.filter_congr
    intro j hj
    have hj' : j < min i.val n := Finset.mem_range.mp hj
    rw [frame_vertex F u w j (by omega), frame_vertex F u w i.val (by omega)]
    exact F.point.injective.eq_iff
  simp only [wordRevisit, he]

theorem frame_incoming (F : FrameChange) {n : ℕ} (incoming : Compass)
    (w : DirectionWord n) (i : Fin n) :
    wordIncoming (F.direction incoming) (F.word w) i = F.direction (wordIncoming incoming w i) := by
  unfold wordIncoming FrameChange.word
  split_ifs <;> rfl

theorem frame_weight (F : FrameChange) {n : ℕ} (u : Plane) (incoming : Compass)
    (w : DirectionWord n) : trailWeight (F.point u) (F.direction incoming) (F.word w) =
      trailWeight u incoming w := by
  unfold trailWeight
  apply Finset.prod_congr rfl
  intro i _
  have hs : wordStraight (F.direction incoming) (F.word w) i = wordStraight incoming w i := by
    simp only [wordStraight, frame_incoming, FrameChange.word, Equiv.apply_eq_iff_eq]
  rw [frame_revisit, hs]

def FrameChange.wordEquiv (F : FrameChange) (n : ℕ) : DirectionWord n ≃ DirectionWord n :=
  Equiv.arrowCongr (Equiv.refl _) F.direction

theorem frame_total (F : FrameChange) (n : ℕ) (u : Plane) (incoming : Compass) :
    openTrailTotal n (F.point u) (F.direction incoming) = openTrailTotal n u incoming := by
  unfold openTrailTotal
  rw [← Equiv.sum_comp (F.wordEquiv n)]
  apply Finset.sum_congr rfl
  intro w _
  change (if IsTrail (F.point u) (F.direction incoming) (F.word w) then
    trailWeight (F.point u) (F.direction incoming) (F.word w) else 0) = _
  rw [frame_trail, frame_weight]

def translation (u : Plane) : FrameChange where
  point :=
    { toFun := fun x => u + x
      invFun := fun x => x - u
      left_inv := by intro x; dsimp; abel
      right_inv := by intro x; dsimp; abel }
  direction := Equiv.refl _
  step := by intros; simp [add_assoc]
  reverse := by intros; rfl

def quarterTurn : FrameChange where
  point :=
    { toFun := fun p => (-p.2, p.1)
      invFun := fun p => (p.2, -p.1)
      left_inv := by intro p; simp
      right_inv := by intro p; simp }
  direction :=
    { toFun := turnLeft
      invFun := fun d => d.reverse |> turnLeft
      left_inv := by intro d; cases d <;> rfl
      right_inv := by intro d; cases d <;> rfl }
  step := by
    intro x d
    change (- (x + d.step).2, (x + d.step).1) = (-x.2, x.1) + (turnLeft d).step
    cases d <;> apply Prod.ext <;> dsimp [Compass.step, turnLeft] <;> omega
  reverse := by intro d; cases d <;> rfl

theorem total_uniform (n : ℕ) (u : Plane) (incoming : Compass) :
    openTrailTotal n u incoming = openTrailTotal n (0, 0) .east := by
  have ht := frame_total (translation u) n (0, 0) incoming
  simp only [translation, Equiv.coe_fn_mk, Equiv.refl_apply] at ht
  have hu : u + (0, 0) = u := by apply Prod.ext <;> simp
  rw [hu] at ht
  rw [ht]
  have hr (d : Compass) := frame_total quarterTurn n (0, 0) d
  simp only [quarterTurn, Equiv.coe_fn_mk, neg_zero] at hr
  cases incoming
  · rfl
  · exact hr .east
  · exact (hr .north).trans (hr .east)
  · exact (hr .west).trans ((hr .north).trans (hr .east))

end AKLT.Cert.H2
