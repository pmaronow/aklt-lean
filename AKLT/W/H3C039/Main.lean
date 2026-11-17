module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C039

theorem main : CertData.H3.Bridge.PlaneBatchSoundLeaf := by
  intro G T X d₀ start count h i hi
  have hall : ∀ j ∈ List.range count,
      AKLT.Cert.H3.Production.planeCheck G T X d₀ (start + j) = true :=
    (List.all_eq_true.mp h)
  exact hall i (List.mem_range.mpr hi)

end AKLT.W.H3C039

#print axioms AKLT.W.H3C039.main
