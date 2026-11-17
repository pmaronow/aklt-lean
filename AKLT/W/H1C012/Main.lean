module
public import AKLT.W.H1C012.Bridge

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C012

open AKLT.Defs AKLT.Cert.H1.Production

theorem main : AKLT.Cert.H1.Production.Leaves.parityCoverage := by
  intro c hc ε
  have hmem := input_parity_mem c.input hc.1 c.network hc.2.1 ε
  have hcheck := hc.2.2.2.2.2.2.2
  have hlist : c.bundles.map (fun b => b.block.parity) = exchangeParities c.network := by
    simpa only [parityCoverCheck, beq_iff_eq] using hcheck
  rw [← hlist] at hmem
  obtain ⟨b,hb,hparity⟩ := List.mem_map.mp hmem
  exact ⟨b,hb,hparity⟩

#print axioms main

end AKLT.W.H1C012
