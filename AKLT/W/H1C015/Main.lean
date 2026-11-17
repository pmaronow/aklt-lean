module
public import AKLT.W.H1C015.Linearity

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C015

open AKLT.Cert.H1 AKLT.Cert.H1.Production

/-- The accepted sector layout supplies the mixed-radix strides required by
the polynomial evaluation identity. -/
theorem main : AKLT.Cert.H1.Production.Leaves.sectorPackingExpansion := by
  intro c _ b hb row
  have hs := strides_of_check c.network b.block.parity b.sector hb.2.1
  simpa only [lanes] using
    threshold_expansion b.sector hs c.out row c.width c.p c.q

/- Axiom audit of every theorem exported by these four modules. -/
#print axioms value_injective
#print axioms value_zero
#print axioms value_one
#print axioms value_add
#print axioms value_scale
#print axioms gaussian_beq_zero_eq
#print axioms gaussian_mul_raw
#print axioms value_mul
#print axioms value_sum
#print axioms sum_list_range
#print axioms value_sum_range
#print axioms sum_blocks
#print axioms getD_map_range
#print axioms matrixEntry_map
#print axioms entry_mul
#print axioms value_trace
#print axioms weight_zero
#print axioms weight_add
#print axioms weight_pow
#print axioms value_pack_map
#print axioms lanes_nil
#print axioms lanes_cons
#print axioms strides_of_indexed
#print axioms strides_of_check
#print axioms digit_period
#print axioms direct_product_period
#print axioms entry_direct_site
#print axioms entry_packed_site
#print axioms digit_block
#print axioms product_expansion
#print axioms ring_expansion
#print axioms expands_zero
#print axioms expands_add
#print axioms expands_scale
#print axioms expands_sum
#print axioms expands_filterMap
#print axioms current_expansion
#print axioms filter_center_terms
#print axioms packed_threshold_eq
#print axioms threshold_expansion
#print axioms main

end AKLT.W.H1C015
