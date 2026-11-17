module
public import AKLT.Challenge.Sanity
public import AKLT.Uniq.BondAlgebra

@[expose] public section

/-! Additional sanity proofs, kept downstream to avoid a cycle through Sanity. -/

namespace AKLT.Challenge

/-- The nonvanishing sanity predicate follows from the proved polynomial argument. -/
theorem b_nonzero (L N : Size) : BNonzero L N := AKLT.Uniq.B_ne_zero L N

#print axioms b_nonzero

end AKLT.Challenge
