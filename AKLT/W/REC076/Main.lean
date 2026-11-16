import AKLT.Blueprint.Rec.NodesRecursion

noncomputable section
open AKLT.Defs

namespace AKLT.W.REC076

def flipX : Plane ≃ Plane := Equiv.prodCongr (Equiv.neg ℤ) (Equiv.refl ℤ)
def flipY : Plane ≃ Plane := Equiv.prodCongr (Equiv.refl ℤ) (Equiv.neg ℤ)
def flipBoth : Plane ≃ Plane := Equiv.prodCongr (Equiv.neg ℤ) (Equiv.neg ℤ)
def swapP : Plane ≃ Plane := Equiv.prodComm ℤ ℤ
def rotateA : Plane ≃ Plane := swapP.trans flipX
def rotateB : Plane ≃ Plane := swapP.trans flipY
def reflectSwap : Plane ≃ Plane := swapP.trans flipBoth

lemma flipX_dist (x y : Plane) : latticeDist (flipX x) (flipX y) = latticeDist x y := by
  change (-x.1 - -y.1).natAbs + (x.2 - y.2).natAbs =
    (x.1 - y.1).natAbs + (x.2 - y.2).natAbs
  rw [show -x.1 - -y.1 = -(x.1 - y.1) by ring, Int.natAbs_neg]

lemma flipY_dist (x y : Plane) : latticeDist (flipY x) (flipY y) = latticeDist x y := by
  change (x.1 - y.1).natAbs + (-x.2 - -y.2).natAbs =
    (x.1 - y.1).natAbs + (x.2 - y.2).natAbs
  rw [show -x.2 - -y.2 = -(x.2 - y.2) by ring, Int.natAbs_neg]

lemma flipBoth_dist (x y : Plane) : latticeDist (flipBoth x) (flipBoth y) = latticeDist x y := by
  change (-x.1 - -y.1).natAbs + (-x.2 - -y.2).natAbs =
    (x.1 - y.1).natAbs + (x.2 - y.2).natAbs
  rw [show -x.1 - -y.1 = -(x.1 - y.1) by ring,
    show -x.2 - -y.2 = -(x.2 - y.2) by ring, Int.natAbs_neg, Int.natAbs_neg]

lemma swapP_dist (x y : Plane) : latticeDist (swapP x) (swapP y) = latticeDist x y := by
  change (x.2 - y.2).natAbs + (x.1 - y.1).natAbs = _
  exact Nat.add_comm _ _

lemma rotateA_dist (x y : Plane) : latticeDist (rotateA x) (rotateA y) = latticeDist x y := by
  simp only [rotateA, Equiv.trans_apply]
  exact flipX_dist (swapP x) (swapP y) |>.trans (swapP_dist x y)

lemma rotateB_dist (x y : Plane) : latticeDist (rotateB x) (rotateB y) = latticeDist x y := by
  simp only [rotateB, Equiv.trans_apply]
  exact flipY_dist (swapP x) (swapP y) |>.trans (swapP_dist x y)

lemma reflectSwap_dist (x y : Plane) : latticeDist (reflectSwap x) (reflectSwap y) = latticeDist x y := by
  simp only [reflectSwap, Equiv.trans_apply]
  exact flipBoth_dist (swapP x) (swapP y) |>.trans (swapP_dist x y)

def canonicalQ : PairType → Compass → Compass → Plane ≃ Plane
  | .B, .east, .west => flipX
  | .B, .west, .east => Equiv.refl Plane
  | .B, .north, .south => rotateA
  | .B, .south, .north => swapP
  | .C, .east, .north => flipX
  | .C, .east, .south => flipBoth
  | .C, .west, .north => Equiv.refl Plane
  | .C, .west, .south => flipY
  | .C, .north, .east => rotateA
  | .C, .north, .west => reflectSwap
  | .C, .south, .east => swapP
  | .C, .south, .west => rotateB
  | _, _, _ => Equiv.refl Plane

def directionPairGood (X : PairType) (a b : Compass) : Prop :=
  match X with
  | .B => (a = .east ∧ b = .west) ∨ (a = .west ∧ b = .east) ∨
      (a = .north ∧ b = .south) ∨ (a = .south ∧ b = .north)
  | .C => (a = .east ∧ b = .north) ∨ (a = .east ∧ b = .south) ∨
      (a = .west ∧ b = .north) ∨ (a = .west ∧ b = .south) ∨
      (a = .north ∧ b = .east) ∨ (a = .north ∧ b = .west) ∨
      (a = .south ∧ b = .east) ∨ (a = .south ∧ b = .west)

lemma canonicalQ_dist (X : PairType) (a b : Compass) (x y : Plane) :
    latticeDist (canonicalQ X a b x) (canonicalQ X a b y) = latticeDist x y := by
  cases X <;> cases a <;> cases b <;>
    simp [canonicalQ, flipX_dist, flipY_dist, flipBoth_dist, swapP_dist,
      rotateA_dist, rotateB_dist, reflectSwap_dist]

lemma canonicalQ_maps (X : PairType) (a b : Compass) (h : directionPairGood X a b) :
    canonicalQ X a b a.step = kernelStart ∧
      canonicalQ X a b b.step = kernelTarget X := by
  cases X <;> cases a <;> cases b <;>
    simp_all [directionPairGood, canonicalQ, Compass.step, kernelStart, kernelTarget,
      flipX, flipY, flipBoth, swapP, rotateA, rotateB, reflectSwap]

lemma adjacent_as_step (x y : Plane) (h : Adjacent x y) :
    ∃ d : Compass, y = x + d.step := by
  have hdist : (y.1 - x.1).natAbs + (y.2 - x.2).natAbs = 1 := by
    dsimp [Adjacent, latticeDist] at h
    rw [show x.1 - y.1 = -(y.1 - x.1) by ring,
      show x.2 - y.2 = -(y.2 - x.2) by ring,
      Int.natAbs_neg, Int.natAbs_neg] at h
    exact h
  have hx : y.1 - x.1 = 0 ∨ y.1 - x.1 = 1 ∨ y.1 - x.1 = -1 := by
    have hle : (y.1 - x.1).natAbs ≤ 1 := by omega
    have hc : (y.1 - x.1).natAbs = 0 ∨ (y.1 - x.1).natAbs = 1 := by omega
    rcases hc with hc | hc
    · exact Or.inl (Int.natAbs_eq_zero.mp hc)
    · rcases Int.natAbs_eq (y.1 - x.1) with hpos | hneg
      · right; left; simpa [hc] using hpos
      · right; right; simpa [hc] using hneg
  have hy : y.2 - x.2 = 0 ∨ y.2 - x.2 = 1 ∨ y.2 - x.2 = -1 := by
    have hle : (y.2 - x.2).natAbs ≤ 1 := by omega
    have hc : (y.2 - x.2).natAbs = 0 ∨ (y.2 - x.2).natAbs = 1 := by omega
    rcases hc with hc | hc
    · exact Or.inl (Int.natAbs_eq_zero.mp hc)
    · rcases Int.natAbs_eq (y.2 - x.2) with hpos | hneg
      · right; left; simpa [hc] using hpos
      · right; right; simpa [hc] using hneg
  rcases hx with hx | hx | hx <;> rcases hy with hy | hy | hy
  · omega
  · refine ⟨.north, ?_⟩; ext <;> simp [Compass.step] <;> omega
  · refine ⟨.south, ?_⟩; ext <;> simp [Compass.step] <;> omega
  · refine ⟨.east, ?_⟩; ext <;> simp [Compass.step] <;> omega
  · omega
  · omega
  · refine ⟨.west, ?_⟩; ext <;> simp [Compass.step] <;> omega
  · omega
  · omega

lemma adjacent_symm (x y : Plane) (h : Adjacent x y) : Adjacent y x := by
  dsimp [Adjacent, latticeDist] at h ⊢
  rw [show y.1 - x.1 = -(x.1 - y.1) by ring,
    show y.2 - x.2 = -(x.2 - y.2) by ring,
    Int.natAbs_neg, Int.natAbs_neg]
  exact h

lemma translate_dist (c x y : Plane) :
    latticeDist (x - c) (y - c) = latticeDist x y := by
  change ((x.1 - c.1) - (y.1 - c.1)).natAbs +
      ((x.2 - c.2) - (y.2 - c.2)).natAbs =
    (x.1 - y.1).natAbs + (x.2 - y.2).natAbs
  rw [show (x.1 - c.1) - (y.1 - c.1) = x.1 - y.1 by ring,
    show (x.2 - c.2) - (y.2 - c.2) = x.2 - y.2 by ring]

lemma responsePair_directions (X : PairType) (c u v : Plane) (a b : Compass)
    (hu : u = c + a.step) (hv : v = c + b.step) (h : HasPairType X u v) :
    directionPairGood X a b := by
  cases X <;> cases a <;> cases b <;>
    simp_all [directionPairGood, HasPairType, latticeDist, Compass.step]

lemma canonicalQ_zero (X : PairType) (a b : Compass) :
    canonicalQ X a b (0, 0) = (0, 0) := by
  cases X <;> cases a <;> cases b <;>
    simp [canonicalQ, flipX, flipY, flipBoth, swapP, rotateA, rotateB, reflectSwap]

end AKLT.W.REC076

namespace AKLT.W.REC076

theorem main : AKLT.Blueprint.Rec.PairCanonicalGeometryStatement := by
  intro p
  rcases p.pair with ⟨_, _, _, _, _, hac, hbc, htype, _, _⟩
  obtain ⟨a, ha⟩ := adjacent_as_step p.c p.u (adjacent_symm p.u p.c hac)
  obtain ⟨b, hb⟩ := adjacent_as_step p.c p.v (adjacent_symm p.v p.c hbc)
  have hgood := responsePair_directions p.X p.c p.u p.v a b ha hb htype
  obtain ⟨hfirst, hsecond⟩ := canonicalQ_maps p.X a b hgood
  let φ : Plane ≃ Plane := (Equiv.subRight p.c).trans (canonicalQ p.X a b)
  have huc : p.u - p.c = a.step := by rw [ha]; abel
  have hvc : p.v - p.c = b.step := by rw [hb]; abel
  refine ⟨φ, ?_, ?_, ?_, ?_⟩
  · change canonicalQ p.X a b (p.c - p.c) = kernelCentre
    rw [sub_self]
    change canonicalQ p.X a b (0, 0) = (0, 0)
    exact canonicalQ_zero p.X a b
  · change canonicalQ p.X a b (p.u - p.c) = kernelStart
    rw [huc, hfirst]
  · change canonicalQ p.X a b (p.v - p.c) = kernelTarget p.X
    rw [hvc, hsecond]
  · intro x y
    change latticeDist (canonicalQ p.X a b (x - p.c))
      (canonicalQ p.X a b (y - p.c)) = latticeDist x y
    rw [canonicalQ_dist]
    exact translate_dist p.c x y

end AKLT.W.REC076
