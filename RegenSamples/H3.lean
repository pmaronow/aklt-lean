module

public import CertData.H3.Kernel.Production.Model
public import CertData.H3.Kernel.Literal

@[expose] public section

namespace RegenSamples.H3
open AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Gen.Packed

/-- A tiny ordinary numeral produced by the production hexadecimal elaborator. -/
def packed : Nat := h3_hex% "1"
def terms : List PackedTerm := [(1, packed)]

/-- Packed arithmetic and its Boolean checker reduce across module boundaries. -/
theorem checked : packedRowCheck 4 1 1 1 packed terms = true := by decide +kernel

theorem walk_step : (Walk.step rawInitial 0).pos = (1, 0) := by decide +kernel

end RegenSamples.H3
