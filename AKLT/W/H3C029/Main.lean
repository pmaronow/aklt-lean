import AKLT.W.H3C029.Replay
import AKLT.W.H3C031.Main

noncomputable section
open scoped BigOperators

namespace AKLT.W.H3C029

open AKLT.Defs
open AKLT.Cert.H3
open AKLT.Cert.H3.Production
open CertData.H3.Bridge

/-- Full replay soundness follows from the single-step bridge. The replay
induction in `Replay.lean` handles all path checks and all target cutoffs. -/
theorem main_of_prefixStep (hstep : PrefixStepLeaf) :
    CertData.H3.Bridge.PrefixReplaySoundLeaf := by
  intro E hE X d₀ n c hn _hn12 hc s hs
  obtain ⟨hrep, htrail, hfirst, havoid⟩ :=
    replay_sound_of_prefixStep hstep E hE X d₀ n c hc s hs
  exact ⟨hrep, htrail, hfirst (by omega), havoid⟩

/-- Successful prefix replay represents the decoded word and yields a true
surviving prefix, using the proved single-step representation invariant. -/
theorem main : CertData.H3.Bridge.PrefixReplaySoundLeaf :=
  main_of_prefixStep AKLT.W.H3C031.main

#print axioms main_of_prefixStep
#print axioms main

end AKLT.W.H3C029

end
