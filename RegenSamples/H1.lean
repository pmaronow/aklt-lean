module

public import AKLT.Cert.H1.Production.Basic
public import AKLT.Cert.H1.Literals

@[expose] public section

namespace RegenSamples.H1
open AKLT.Cert.H1 AKLT.Gen.Gram

/-- A tiny literal with the same elaborator used by production H1 data. -/
def row : List Int := h1_row% "1"
def rows : IntRows := [row, [0, 1]]

/-- A kernel reduction through the imported checker and literal consumer. -/
theorem checked : lowerTriangularCheck rows = true := by decide +kernel

/-- Exercise signed packing in the production arithmetic interface. -/
def packed : Int := AKLT.Cert.H1.Production.sparsePack 4 [0, 1] [1, -1]
theorem packed_reduces : packed = -15 := by decide +kernel

end RegenSamples.H1
