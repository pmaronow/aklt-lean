module

public import AKLT.Final.Inputs

/-! The independent Challenge is not imported. Its identically named statement
objects are supplied by the original tree. Comparator must recursively compare
their complete reachable definitions; no definition-hole exemptions are used. -/

@[expose] public section

namespace AKLTPalomar

/-- The same pointwise local input as the independent Challenge. -/
def H1 : Prop := AKLT.Defs.LocalPatternBound (961 / 1000) (187 / 200)

/-- The same all-cutoff positive-vector input as the independent Challenge. -/
def H3 : Prop := AKLT.Defs.PositiveVectorBound

/-- The same all-parity headline as the independent Challenge. -/
def Main : Prop := AKLT.Challenge.MainStatementV2

/-- Reflexive identity between the H1 alias and its library definition (`Iff.rfl`).
The Comparator separately checks the independent Challenge copy. -/
theorem h1_iff : H1 ↔ AKLT.Blueprint.Top.H1Statement := Iff.rfl

/-- Reflexive identity between the H3 alias and its library definition (`Iff.rfl`).
The Comparator separately checks the independent Challenge copy. -/
theorem h3_iff : H3 ↔ AKLT.Blueprint.Top.H3Statement := Iff.rfl

/-- Reflexive definitional identity: `Main` is an alias, so this proof is `Iff.rfl`.
The identity of the independent Challenge copy with the library definitions is
established by mechanical generation and checked recursively by the Comparator. -/
theorem main_iff : Main ↔ AKLT.Challenge.MainStatementV2 := Iff.rfl

/-- The all-parity AKLT result from exactly the two declared numerical inputs. -/
theorem aklt_gap_of_inputs : H1 → H3 → Main := by
  intro hH1 hH3
  exact main_iff.mpr (AKLT.Final.main_of_inputs (h1_iff.mp hH1) (h3_iff.mp hH3))

end AKLTPalomar
