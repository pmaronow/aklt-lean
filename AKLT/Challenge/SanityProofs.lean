module
public import AKLT.Challenge.Sanity
public import AKLT.Challenge.BondRank

@[expose] public section

/-! Additional sanity proofs, kept downstream to avoid a cycle through Sanity. -/

namespace AKLT.Challenge

/-- The nonvanishing sanity predicate follows from the proved polynomial argument. -/
theorem b_nonzero (L N : Size) : BNonzero L N := AKLT.Uniq.B_ne_zero L N

/-- The spin-four projector has rank 9·5^(LN−2), including all spectator sites. -/
theorem bond_rank (L N : Size) : BondRank L N := SanityRank.bond_rank L N

/-- The 4×4 model satisfies all the geometric, nonvanishing, and rank checks. -/
theorem four_by_four_nondegenerate : FourByFourNondegenerate :=
  SanityRank.four_by_four_nondegenerate

#print axioms bond_rank
#print axioms four_by_four_nondegenerate
#print axioms b_nonzero

end AKLT.Challenge
