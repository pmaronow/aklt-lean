import AKLT.Blueprint.Top.Windows
import AKLT.Challenge.MainV2
import AKLT.Blueprint.Top.InputsV2

/-! The proved top assembly. Every unproved mathematical part is a closed Prop;
all mathematical inputs remain explicit arguments. -/

namespace AKLT.Blueprint.Top
open AKLT.Defs AKLT.Challenge

/-- `t:main`: compose t:inputs, t:rec, t:cutMOS and t:mainW, then supply the
independent p:toruskernel at every size. This proves the assembly implication only. -/
theorem mainV2_of_parts : InputsStatement → RecStatement → CutMOSStatement →
    MainWStatement → TorusKernelStatement → MainStatementV2 := by
  intro hInputs hRec hCut hMainW hKernel
  obtain ⟨θ, ρ, _, _, _, _, _, hP⟩ := hRec 10 (certifiedRate : ℝ)
    hInputs.1 hInputs.2.1 hInputs.2.2.1
  obtain ⟨Mstar, hW⟩ := hCut (renewalAmplitude 10 (certifiedRate : ℝ) ρ) θ hP
  obtain ⟨c, hc, L₀, hL₀, hEventual⟩ := hMainW ⟨64, cutProbability
    (renewalAmplitude 10 (certifiedRate : ℝ) ρ) θ, Mstar, hW⟩
  constructor
  · intro L N
    exact ⟨(hKernel L N).2.2.2.1, (hKernel L N).2.2.2.2.1⟩
  · exact ⟨c, hc, L₀, hL₀, fun L N hL hN => (hEventual L N hL hN).2⟩

#print axioms mainV2_of_parts

/-- The top assembly with the repaired, archive-bound numerical input contract.
Only the semantic conclusions enter the analytic implication. The additional
finite-data obligations remain visible in its closed input proposition. -/
theorem mainV2_of_partsV2 : InputsStatementV2 → RecStatement → CutMOSStatement →
    MainWStatement → TorusKernelStatement → MainStatementV2 := by
  intro hInputs hRec hCut hMainW hKernel
  exact mainV2_of_parts hInputs.1 hRec hCut hMainW hKernel

#print axioms mainV2_of_partsV2

end AKLT.Blueprint.Top
