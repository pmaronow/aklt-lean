module
public import AKLT.W.REC079.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec AKLT.Cert.H2

namespace AKLT.W.REC079

/-- Chosen once per designated triple, independently of every trail and length. -/
def canonicalChart (p : PairData) : LatticeChart := Classical.choose (pair_chart p)

@[simp] theorem canonicalChart_centre (p : PairData) :
    (canonicalChart p).point p.c = kernelCentre := (Classical.choose_spec (pair_chart p)).1

@[simp] theorem canonicalChart_start (p : PairData) :
    (canonicalChart p).point p.u = kernelStart := (Classical.choose_spec (pair_chart p)).2.1

@[simp] theorem canonicalChart_target (p : PairData) :
    (canonicalChart p).point p.v = kernelTarget p.X := (Classical.choose_spec (pair_chart p)).2.2

def canonicalWord (p : PairData) {n : ℕ} (w : DirectionWord n) : DirectionWord n :=
  (canonicalChart p).word w

theorem canonicalWord_injective (p : PairData) (n : ℕ) :
    Function.Injective (canonicalWord p (n := n)) := by
  intro w w' h
  funext i
  exact (canonicalChart p).direction.injective (congrFun h i)

theorem canonicalWord_vertex (p : PairData) {n : ℕ} (w : DirectionWord n)
    (j : ℕ) (hj : j ≤ n) :
    wordVertex kernelStart (canonicalWord p w) j =
      (canonicalChart p).point (wordVertex p.u w j) := by
  rw [← canonicalChart_start p]
  exact frame_vertex (canonicalChart p).toFrameChange p.u w j hj

theorem canonicalWord_baseWeight (p : PairData) {n : ℕ} (w : DirectionWord n) :
    trailBaseWeight kernelStart (canonicalWord p w) = trailBaseWeight p.u w := by
  rw [← canonicalChart_start p]
  unfold trailBaseWeight canonicalWord
  apply Finset.prod_congr rfl
  intro i _
  rw [frame_revisit]

theorem responsePair_endpoints_ne (p : PairData) : p.u ≠ p.v := by
  intro huv
  have hdist := p.pair.2.2.2.2.2.2.2.1.1
  rw [huv] at hdist
  simp [latticeDist] at hdist

private theorem pair_centre_removed (p : PairData) : p.normalized.status p.c = .X := by
  exact p.pair.2.2.2.2.1

private theorem pair_active_ne_centre (p : PairData) {x : Plane}
    (h : x ∈ p.normalized.active) : x ≠ p.c := by
  intro hx
  have hs : p.normalized.status x ≠ .X := (Finset.mem_filter.mp h).2
  exact hs (hx ▸ pair_centre_removed p)

/-- Every target-reaching true trace avoids the designated removed center. -/
theorem target_trail_avoids_centre (p : PairData) {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (hend : wordVertex p.u w n = p.v) (j : ℕ) (hj : j ≤ n) :
    wordVertex p.u w j ≠ p.c := by
  by_cases hlt : j < n
  · exact pair_active_ne_centre p (hw.2.1 ⟨j, hlt⟩).1
  · have hje : j = n := by omega
    rw [hje, hend]
    exact pair_active_ne_centre p p.pair.2.2.1

/-- A target-reaching true trace becomes a canonical ClosedTrail in the
single fixed chart. Both first-hit and forbidden-initial-reversal conditions
are proved from actual presence and removal. -/
theorem target_trail_closed (p : PairData) {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (hend : wordVertex p.u w n = p.v) : ClosedTrail p.X (canonicalWord p w) := by
  classical
  have hav := target_trail_avoids_centre p w hw hend
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [← canonicalChart_start p]
    intro i j hij
    apply hw.1
    apply Finset.image_injective (canonicalChart p).point.injective
    simpa only [canonicalWord, frame_bond] using hij
  · intro i hi hreversal
    have hn : 0 < n := by omega
    have hi0 : (⟨0, hn⟩ : Fin n) = i := Fin.ext hi.symm
    have hv := vertex_succ kernelStart (canonicalWord p w) 0 hn
    rw [vertex_zero, hi0, hreversal] at hv
    have hc : wordVertex kernelStart (canonicalWord p w) 1 = kernelCentre := by
      simpa [kernelStart, kernelCentre, kernelIncoming, Compass.reverse, Compass.step] using hv
    apply hav 1 (by omega)
    apply (canonicalChart p).point.injective
    rw [← canonicalWord_vertex p w 1 (by omega), hc, canonicalChart_centre]
  · rw [canonicalWord_vertex p w n le_rfl, hend, canonicalChart_target]
  · intro j hj h
    apply hav j hj
    apply (canonicalChart p).point.injective
    rw [← canonicalWord_vertex p w j hj, h, canonicalChart_centre]
  · intro j hj h
    have hv : wordVertex p.u w j = p.v := by
      apply (canonicalChart p).point.injective
      rw [← canonicalWord_vertex p w j (by omega), h, canonicalChart_target]
    exact (hw.2.2.1 j hj).1 (by simp [hv])

end AKLT.W.REC079
