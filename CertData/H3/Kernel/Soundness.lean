module
public import CertData.H3.Kernel.Automaton
public import CertData.H3.Kernel.View
public import AKLT.Gen.Bellman.Certificates

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.Cert.H3
open AKLT.Defs

/-- Per-word acceptance and checked representatives give exactly the Defs quotient contract. -/
theorem quotient_assembly (m q : Nat) (Q : MemoryQuotient m q)
    (representatives : ∀ a, RawWindow (Q.representative a) ∧ Q.project (Q.representative a) = a)
    (rows : ∀ w : DirectionWord m, RawWindow w → CorrectAt Q w) : Q.Correct := by
  exact ⟨representatives, fun w hw => (rows w hw).2⟩

/-- The Defs ceiling bounds every exact rational coefficient, including zero. -/
theorem coefficientCeiling_bound (t : ℚ) : t ≤
    (coefficientCeiling t : ℚ) / certificateCoefficientScale := by
  have hD : (0 : ℚ) < certificateCoefficientScale := by norm_num [certificateCoefficientScale]
  apply (le_div_iff₀ hD).mpr
  simpa [coefficientCeiling, mul_comm] using
    (Nat.le_ceil ((certificateCoefficientScale : ℚ) * t))

/-- The proved scaled-row library applies directly to the actual Defs coefficients. -/
theorem scaled_row_real {E : Type*} (edges : Finset E) (t : E → ℚ) (v : E → Nat) (u : Nat)
    (h : ∑ e ∈ edges, coefficientCeiling (t e) * v e ≤ certificateCoefficientScale * u) :
    (∑ e ∈ edges, (t e : ℝ) * ((v e : ℝ) / certificateValueScale)) ≤
      (u : ℝ) / certificateValueScale := by
  apply AKLT.Gen.Bellman.scaled_row_sound edges (fun e => (t e : ℝ))
    (fun e => coefficientCeiling (t e)) v certificateCoefficientScale certificateValueScale u
    (by norm_num [certificateCoefficientScale]) (by norm_num [certificateValueScale]) _ h
  intro e _
  have hh : (t e : ℝ) ≤ (((coefficientCeiling (t e) : ℚ) / certificateCoefficientScale : ℚ) : ℝ) :=
    Rat.cast_le.mpr (coefficientCeiling_bound (t e))
  simpa only [Rat.cast_div, Rat.cast_natCast] using hh

#print axioms quotient_assembly
#print axioms coefficientCeiling_bound
#print axioms scaled_row_real
end AKLT.Cert.H3
