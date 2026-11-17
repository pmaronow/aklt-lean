module
public import AKLT.Blueprint.Rec.NodesRecursion
public import AKLT.Cert.H2.Frames

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec AKLT.Cert.H2

namespace AKLT.W.REC079

/-- A single lattice chart, including its action on directions. -/
structure LatticeChart extends FrameChange where
  distance : ∀ x y : Plane, latticeDist (point x) (point y) = latticeDist x y

namespace LatticeChart

def trans (F H : LatticeChart) : LatticeChart where
  point := F.point.trans H.point
  direction := F.direction.trans H.direction
  step := by
    intro x d
    change H.point (F.point (x + d.step)) = _
    rw [F.step, H.step]
    rfl
  reverse := by
    intro d
    change H.direction (F.direction d.reverse) = _
    rw [F.reverse, H.reverse]
    rfl
  distance := by intro x y; exact (H.distance _ _).trans (F.distance _ _)

def translate (c : Plane) : LatticeChart where
  toFrameChange := translation c
  distance := by intro x y; simp [translation, latticeDist]

def flip (a b : Bool) : LatticeChart where
  point := Function.Involutive.toPerm
    (f := fun x : Plane => (if a then -x.1 else x.1, if b then -x.2 else x.2)) (by
      intro x; cases a <;> cases b <;> simp)
  direction := Function.Involutive.toPerm (f := fun d => match d with
    | .east => if a then .west else .east
    | .north => if b then .south else .north
    | .west => if a then .east else .west
    | .south => if b then .north else .south) (by
      intro d; cases a <;> cases b <;> cases d <;> rfl)
  step := by
    intro x d
    cases a <;> cases b <;> cases d <;>
      apply Prod.ext <;> simp [Function.Involutive.toPerm, Compass.step, add_comm]
  reverse := by intro d; cases a <;> cases b <;> cases d <;> rfl
  distance := by
    intro x y
    cases a <;> cases b <;> simp [latticeDist, Function.Involutive.toPerm,
      show -x.1 + y.1 = -(x.1 - y.1) by omega,
      show -x.2 + y.2 = -(x.2 - y.2) by omega] <;> omega

def swap (s : Bool) : LatticeChart where
  point := Function.Involutive.toPerm (f := fun x : Plane => if s then (x.2, x.1) else x)
    (by intro x; cases s <;> simp)
  direction := Function.Involutive.toPerm (f := fun d => if s then match d with
    | .east => .north | .north => .east | .west => .south | .south => .west
    else d) (by intro d; cases s <;> cases d <;> rfl)
  step := by intro x d; cases s <;> cases d <;> rfl
  reverse := by intro d; cases s <;> cases d <;> rfl
  distance := by intro x y; cases s <;> simp [Function.Involutive.toPerm, latticeDist, Nat.add_comm]

def orient (s a b : Bool) : LatticeChart := (swap s).trans (flip a b)

@[simp] theorem orient_zero (s a b : Bool) : (orient s a b).point (0, 0) = (0, 0) := by
  cases s <;> cases a <;> cases b <;> simp [orient, trans, swap, flip]

end LatticeChart

private theorem direction_chart : ∀ X : PairType, ∀ a b : Compass,
    HasPairType X a.step b.step → ∃ s ax ay : Bool,
      (LatticeChart.orient s ax ay).point a.step = kernelStart ∧
      (LatticeChart.orient s ax ay).point b.step = kernelTarget X := by
  unfold HasPairType
  decide +kernel

/-- Adjacency supplies one of the four actual lattice displacements. -/
theorem adjacent_direction {x y : Plane} (h : Adjacent x y) :
    ∃ a : Compass, x = y + a.step := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  change (x₁ - y₁).natAbs + (x₂ - y₂).natAbs = 1 at h
  have hcases :
      (x₁ = y₁ + 1 ∧ x₂ = y₂) ∨ (x₁ = y₁ ∧ x₂ = y₂ + 1) ∨
      (x₁ = y₁ - 1 ∧ x₂ = y₂) ∨ (x₁ = y₁ ∧ x₂ = y₂ - 1) := by omega
  rcases hcases with h | h | h | h
  · exact ⟨.east, by simpa [Compass.step, Prod.mk.injEq, sub_eq_add_neg] using h⟩
  · exact ⟨.north, by simpa [Compass.step, Prod.mk.injEq, sub_eq_add_neg] using h⟩
  · exact ⟨.west, by simpa [Compass.step, Prod.mk.injEq, sub_eq_add_neg] using h⟩
  · exact ⟨.south, by simpa [Compass.step, Prod.mk.injEq, sub_eq_add_neg] using h⟩

/-- The designated triple admits one fixed chart, for all its trail lengths. -/
theorem pair_chart (p : PairData) : ∃ F : LatticeChart,
    F.point p.c = kernelCentre ∧ F.point p.u = kernelStart ∧
      F.point p.v = kernelTarget p.X := by
  obtain ⟨a, ha⟩ := adjacent_direction p.pair.2.2.2.2.2.1
  obtain ⟨b, hb⟩ := adjacent_direction p.pair.2.2.2.2.2.2.1
  have ht : HasPairType p.X a.step b.step := by
    have ht := p.pair.2.2.2.2.2.2.2.1
    rw [ha, hb] at ht
    simpa [HasPairType, latticeDist] using ht
  obtain ⟨s, ax, ay, hu, hv⟩ := direction_chart p.X a b ht
  let Q := LatticeChart.orient s ax ay
  refine ⟨(LatticeChart.translate (-p.c)).trans Q, ?_, ?_, ?_⟩
  · change Q.point (-p.c + p.c) = kernelCentre
    rw [neg_add_cancel]
    exact LatticeChart.orient_zero s ax ay
  · change Q.point (-p.c + p.u) = kernelStart
    simpa [ha, add_assoc] using hu
  · change Q.point (-p.c + p.v) = kernelTarget p.X
    simpa [hb, add_assoc] using hv

end AKLT.W.REC079
