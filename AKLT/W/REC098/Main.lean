module
public import AKLT.W.REC098.Local

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! The first protected hit becomes the sole fixed U kept-set defect for the
second trace. `second_state` preserves this invariant, and `state_covered`
extracts the shared present-bond template whenever that defect lies outside
the departure's radius-two diamond. -/

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Rec (normalizeStart prefixNetwork)

namespace AKLT.W.REC098

/-- Outside the first protected endpoint's radius-two diamond, a second-trace
U departure has a cover for the shared present-bond matcher. -/
theorem far_departure_covered
    (p : AKLT.Blueprint.Rec.PairSetup) (hpv : p.v ∉ protectedSites p.G)
    (n : ℕ) (w : DirectionWord n)
    (hfirst : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (he : wordVertex p.u w n ∈ protectedSites p.G)
    (incoming : Compass) (hin : p.v = p.c + incoming.step)
    (m : ℕ) (w' : DirectionWord m)
    (hsecond : StoppedNetworkTrail
      (normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c)
      p.v (protectedSites p.G) w') (i : Fin m)
    (hU : (prefixNetwork
      (normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c)
      p.v w' i.val).status (wordVertex p.v w' i.val) = .U)
    (hfar : 2 < latticeDist (wordVertex p.v w' i.val) (wordVertex p.u w n)) :
    AKLT.Defs.CoveredDepartureV2
      (prefixNetwork (normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c)
        p.v w' i.val) (wordVertex p.v w' i.val) (wordIncoming incoming w' i) (w' i) := by
  obtain ⟨hs, hp⟩ := second_state p hpv n w hfirst he incoming hin m w' hsecond i
  rw [wordVertex_succ p.v w' i.val i.isLt] at hp
  apply state_covered hs (hsecond.2.2.1 i.val i.isLt).2 hU hp
  intro z hz
  simp only [Finset.mem_singleton]
  intro heq
  have hd := chart_ball (wordVertex p.v w' i.val) (wordIncoming incoming w' i) hz
  rw [heq] at hd
  omega

/-- A second-trace departure is outside the protected set, while the first
trace endpoint belongs to it.  Thus their ambient lattice distance is positive. -/
theorem secondDeparture_distance_pos
    (p : AKLT.Blueprint.Rec.PairSetup)
    (n : ℕ) (w : DirectionWord n)
    (he : wordVertex p.u w n ∈ protectedSites p.G)
    (m : ℕ) (w' : DirectionWord m)
    (hsecond : StoppedNetworkTrail
      (AKLT.Blueprint.Rec.normalizeStart (traceNetwork p.normalized (wordVertices p.u w)) p.v p.c)
      p.v (protectedSites p.G) w')
    (i : Fin m) :
    0 < latticeDist (wordVertex p.v w' i.val) (wordVertex p.u w n) := by
  rcases hsecond with ⟨_, _, havoid, _⟩
  have hyS : wordVertex p.v w' i.val ∉ protectedSites p.G :=
    (havoid i.val i.isLt).2
  have hne : wordVertex p.v w' i.val ≠ wordVertex p.u w n := by
    intro heq
    apply hyS
    rw [heq]
    exact he
  by_contra hnot
  have hz : latticeDist (wordVertex p.v w' i.val) (wordVertex p.u w n) = 0 :=
    Nat.eq_zero_of_not_pos hnot
  simp [latticeDist] at hz
  apply hne
  rcases hz with ⟨h₁, h₂⟩
  exact Prod.ext (sub_eq_zero.mp h₁) (sub_eq_zero.mp h₂)

/-- Every shared-cover failure is in the punctured radius-two diamond about
 the first protected endpoint. -/
theorem main : AKLT.Blueprint.Rec.TerminalExceptionLocationStatementV2 := by
  intro p hpv n w hfirst he E incoming hin m w' hsecond i hU hbad
  have hpos := secondDeparture_distance_pos p n w he m w' hsecond i
  by_cases hdist : latticeDist (wordVertex p.v w' i.val) (wordVertex p.u w n) ≤ 2
  · exact ⟨hpos, hdist⟩
  · have hfar : 2 < latticeDist (wordVertex p.v w' i.val) (wordVertex p.u w n) := by omega
    exact False.elim (hbad (far_departure_covered p hpv n w hfirst he incoming hin m w' hsecond i hU hfar))

#print axioms far_departure_covered
#print axioms secondDeparture_distance_pos
#print axioms main

end AKLT.W.REC098
