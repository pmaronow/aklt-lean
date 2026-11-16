import AKLT.Gen.Gram.Basic

namespace AKLT.Gen.Gram

/-- The zero-factor route stores each factor row as an empty zero-padded list. -/
theorem direct_example : (toMatrix [[2, 1], [1, 2]]).PosDef := by
  apply checker_sound (L := [[], []]) (g := 1) (d := 1) (S := 1)
  decide +kernel

/-- Nonunit scales and a nonzero ragged factor use the very same checker. -/
theorem scaled_example : (toMatrix [[2, 1], [1, 2]]).PosDef := by
  apply checker_sound (L := [[1], [1, 1]]) (g := 3) (d := 2) (S := 4)
  decide +kernel

end AKLT.Gen.Gram
