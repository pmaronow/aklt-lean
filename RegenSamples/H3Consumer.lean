module

public import RegenSamples.H3

@[expose] public section

namespace RegenSamples.H3Consumer
open AKLT.Cert.H3 AKLT.Gen.Packed

/-- The next layer applies the actual packed-check soundness theorem. -/
theorem component_bound : ∀ s < 1,
    component 5 s RegenSamples.H3.terms ≤ lane RegenSamples.H3.packed 5 s := by
  simpa using (packedRowCheck_sound RegenSamples.H3.checked)

theorem literal_reduces : RegenSamples.H3.packed = 1 := by decide +kernel

end RegenSamples.H3Consumer
