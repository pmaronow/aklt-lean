import AKLT.Uniq.Blueprint

/-!
# Uniqueness of the AKLT ground state on every torus of periods at least three

This is the exact first conjunct of `AKLT.Challenge.MainStatementV2`.
All objects are the frozen definitions in `AKLT.Challenge.Main`.
The proof uses the polynomial edge factorization and distinct prime bond
determinants, as in §3 of the revised paper.  Every blueprint node is proved.
-/

namespace AKLT.Uniq

theorem uniqueness : ∀ L N : AKLT.Challenge.Size, AKLT.Challenge.B L N ≠ 0 ∧
    LinearMap.ker (AKLT.Challenge.H L N) = Submodule.span ℂ {AKLT.Challenge.B L N} :=
  uniqueness_of_nodes casimirAction

#print axioms uniqueness

end AKLT.Uniq
