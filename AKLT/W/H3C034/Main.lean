import AKLT.W.H3C034.Stem
import AKLT.W.H3C034.ReplaySound
import AKLT.W.H3C034.Short
import AKLT.W.H3C034.PrefixStep.Main

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge

namespace AKLT.W.H3C034

/-- Reduction to four named blueprint leaves; no per-stem correspondence is assumed. -/
theorem batch_sound_of_replay (hSound : PrefixReplaySoundLeaf) (hComplete : PrefixReplayCompleteLeaf)
    (hStep : PrefixStepLeaf) (hShort : ShortValueLeaf) : PrefixBatchSoundLeaf := by
  intro G T lookup E hv _ hb X d₀ depth start count hd hd12 hrange hok
  have hstems (i : Nat) (hi : i ∈ List.range count) :
      (prefixStem G lookup E X d₀.val depth (start+i)).ok = true := by
    apply fold_ok_member _ zeroResult hok _
    exact List.mem_map.mpr ⟨i, hi, rfl⟩
  have hzero : resultValue E zeroResult = 0 := by simp [resultValue, zeroResult]
  change resultValue E
    (((List.range count).map fun i => prefixStem G lookup E X d₀.val depth (start+i)).foldl
      PrefixResult.add zeroResult) = _
  rw [resultValue_fold, hzero, zero_add]
  unfold semanticBatch
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact prefixStem_sound hSound hComplete hStep hShort G T lookup E hv hb X d₀
    depth (start+i) hd hd12 (by have := List.mem_range.mp hi; omega) (hstems i hi)

/-- The batch interface follows from exact one-step state representation. -/
theorem main_of_deps (hStep : PrefixStepLeaf) : PrefixBatchSoundLeaf := by
  have hSound := prefixReplay_sound_of_step hStep
  have hComplete := prefixReplay_complete_of_sound hSound
  exact batch_sound_of_replay hSound hComplete hStep shortValue_sound

/-- Exact closed batch soundness, using the registered step-representation proof. -/
theorem main : CertData.H3.Bridge.PrefixBatchSoundLeaf :=
  main_of_deps PrefixStep.main

end AKLT.W.H3C034

#print axioms AKLT.W.H3C034.main_of_deps
#print axioms AKLT.W.H3C034.main
#print axioms AKLT.W.H3C034.prefixStem_sound
#print axioms AKLT.W.H3C034.prefixStem_flat
#print axioms AKLT.W.H3C034.lastWindowCode
