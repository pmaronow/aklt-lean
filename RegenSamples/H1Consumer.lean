module

public import RegenSamples.H1

@[expose] public section

namespace RegenSamples.H1Consumer

/-- The next layer consumes a public certificate with the production soundness theorem. -/
theorem lowerTriangular (n : Nat) (i j : Fin n) (hij : i < j) :
    AKLT.Gen.Gram.matrix n RegenSamples.H1.rows i j = 0 :=
  AKLT.Cert.H1.lowerTriangularCheck_sound RegenSamples.H1.checked n i j hij

theorem literal_reduces : RegenSamples.H1.row = [1] := by decide +kernel

theorem packed_reduces_again : RegenSamples.H1.packed = -15 := by decide +kernel

end RegenSamples.H1Consumer
