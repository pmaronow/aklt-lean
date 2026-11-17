module
public import AKLT.W.H1C009.Degrees

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C009
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

/- The raw bits enumerate the actual bonds, with either edge orientation allowed. -/
set_option maxRecDepth 2000 in
set_option maxHeartbeats 2000000 in
theorem raw_edge (a : Input) (ha : inputCheck a = true) (i : Nat) (hi : i < 16) :
    let e := templateEdges.getD i ((0,0),(0,0))
    presentBond (inputPattern a) e.1 e.2 = (rawEdges a.axes a.corners).getD i false := by
  have h0 := statusAt_ring_ne a ha 0 (by omega)
  have h1 := statusAt_ring_ne a ha 1 (by omega)
  have h2 := statusAt_ring_ne a ha 2 (by omega)
  have h3 := statusAt_ring_ne a ha 3 (by omega)
  have h4 := statusAt_ring_ne a ha 4 (by omega)
  have h5 := statusAt_ring_ne a ha 5 (by omega)
  have h6 := statusAt_ring_ne a ha 6 (by omega)
  have h7 := statusAt_ring_ne a ha 7 (by omega)
  simp [ringSites, ringOptions_explicit] at h0 h1 h2 h3 h4 h5 h6 h7
  have ht0 := statusAt_tip a (2,0) (by simp [templateTips])
  have ht1 := statusAt_tip a (0,2) (by simp [templateTips])
  have ht2 := statusAt_tip a (-2,0) (by simp [templateTips])
  have ht3 := statusAt_tip a (0,-2) (by simp [templateTips])
  dsimp only
  rw [← oriented_edge (inputPattern a) i hi]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, PatternData.bonds, Finset.mem_filter, internal_at i hi, true_and]
  interval_cases i <;>
    simp [
      internalTemplateEdges, keptAt_center, keptAt_input, templateSites, square, latticeDist,
      templateTips, statusAt_center, ht0, ht1, ht2, ht3, h0, h1, h2, h3, h4, h5, h6, h7,
      Input.optionAt, ringSites, ringOptions_explicit, rawEdges, edgeDirections,
      List.range_succ, Bool.and_eq_true, beq_iff_eq] <;>
    clear h0 h1 h2 h3 h4 h5 h6 h7 ht0 ht1 ht2 ht3 ha <;> tauto

end AKLT.W.H1C009
