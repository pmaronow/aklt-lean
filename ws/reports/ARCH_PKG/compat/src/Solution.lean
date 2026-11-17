import AKLT.Final.Inputs

/-! The independent Challenge is not imported. Its identically named statement
objects are supplied by the original tree. Comparator must recursively compare
their complete reachable definitions; no definition-hole exemptions are used. -/


namespace AKLTPalomar

/-- The same pointwise local input as the independent Challenge. -/
def H1 : Prop := AKLT.Defs.LocalPatternBound (961 / 1000) (187 / 200)

/-- The same all-cutoff positive-vector input as the independent Challenge. -/
def H3 : Prop := AKLT.Defs.PositiveVectorBound

/-- The same all-parity headline as the independent Challenge. -/
def Main : Prop := AKLT.Challenge.MainStatementV2

/-- Explicit identification of the inlined H1 surface with the tree's input. -/
theorem h1_iff : H1 ↔ AKLT.Blueprint.Top.H1Statement := Iff.rfl

/-- Explicit identification of the inlined H3 surface with the tree's input. -/
theorem h3_iff : H3 ↔ AKLT.Blueprint.Top.H3Statement := Iff.rfl

/-- Explicit identification of the inlined headline with the tree's headline. -/
theorem main_iff : Main ↔ AKLT.Challenge.MainStatementV2 := Iff.rfl

/-- The all-parity AKLT result from exactly the two declared numerical inputs. -/
theorem aklt_gap_of_inputs : H1 → H3 → Main := by
  intro hH1 hH3
  exact main_iff.mpr (AKLT.Final.main_of_inputs (h1_iff.mp hH1) (h3_iff.mp hH3))

end AKLTPalomar
