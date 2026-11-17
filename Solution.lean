module

public import CertData.Close.All

@[expose] public section

namespace AKLTPalomar

/-- The paper's unconditional, all-parity headline. -/
def Main : Prop := AKLT.Challenge.MainStatementV2

/-- Reflexive definitional identity: `Main` is an alias, so this proof is `Iff.rfl`.
The identity of the independent Challenge copy with the library definitions is
established by mechanical generation and checked recursively by the Comparator. -/
theorem main_iff : Main ↔ AKLT.Challenge.MainStatementV2 := Iff.rfl

/-- The square-lattice spin-2 AKLT theorem, including the finite certificates. -/
theorem aklt_gap : Main := main_iff.mpr CertData.Close.main

end AKLTPalomar
