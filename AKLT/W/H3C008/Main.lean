import CertData.H3.Bridge.Interface

open AKLT.Defs
open AKLT.Cert.H3.Production

namespace AKLT.W.H3C008

theorem main : CertData.H3.Bridge.RevisitLeaf := by
  intro n u incoming w s hrep
  rcases hrep with ⟨_, hpos, _, _, hdeparted, _⟩
  rw [hdeparted, hpos]
  classical
  simp [departureCount]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, hi⟩⟩
  · rintro ⟨j, hj⟩
    rcases Finset.mem_filter.mp hj with ⟨hjrange, hvertex⟩
    exact ⟨⟨j, Finset.mem_range.mp hjrange⟩, hvertex⟩

end AKLT.W.H3C008

#print axioms AKLT.W.H3C008.main
