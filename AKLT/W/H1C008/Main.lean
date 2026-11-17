module
public import AKLT.W.H1C008.Tokens

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C008

open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

 theorem main : AKLT.Cert.H1.Production.Leaves.compilerInversion := by
  intro a hcheck
  have hs := validStatuses_of_check a hcheck
  constructor
  · intro j hj
    have hmem := (inputInversion_mem a j).mp hj
    have ht := inversion_supported a hcheck j.val (List.contains_iff_mem.mp hmem)
    exact (inputTokens_mem_iff a hs j).mp ht
  · intro x hx hp
    obtain ⟨i,hi,hxi⟩ := compilerSite_exists x (Finset.mem_filter.mp hx).1
    rw [← hxi] at hx hp ⊢
    have htwo := (inputSlots_two a hs i hi).mpr ⟨hx,hp⟩
    have heq := inversion_pairs a hcheck i hi htwo
    rw [inputInversion_mem, inputInversion_mem,
      compilerSite_leader i hi, compilerSite_second i hi, heq]

#print axioms main

end AKLT.W.H1C008
