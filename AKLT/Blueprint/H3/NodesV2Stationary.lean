import AKLT.Blueprint.H3.Nodes
import AKLT.Blueprint.Top.ComputationV2

/-! New open bridges to the repaired centre-edge operator. The legacy node files are frozen.
No bridge is proved here, including the elementary coefficient identity. -/
noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.H3

/-- `d:stationary-walk`, ARCH_0 F9, Appendix C lines 517–553.
Away from a destination equal to the centre the corrected guard has no effect. Prove by
splitting the current-terminal/admissibility and known-site guards. No correctness or
nonnegativity premise is needed: the assertion compares the literal rational definitions. -/
def StationaryCoefficientOffCentreStatementV2 : Prop :=
  ∀ m q : ℕ, ∀ Q : MemoryQuotient m q, ∀ X : PairType, ∀ d₀ : Compass,
    ∀ φ : Phase, ∀ a : Fin q, ∀ x : Plane, ∀ d : Compass, ∀ ψ : Phase,
      x + d.step ≠ kernelCentre →
      stationaryCoefficientV2 Q X d₀ φ a x d ψ = stationaryCoefficient Q X d₀ φ a x d ψ

/-- `l:stationary-local-global`, ARCH_0 F9 / downstream adaptation, lines 763–826.
The operators agree on functions zero at the centre, even though they need not agree on
arbitrary functions. Split each finite direction/phase summand by its destination; a centre
summand has zero continuation value. No rounding or inequality premise is involved. -/
def StationaryCentreZeroOperatorStatementV2 : Prop :=
  ∀ m q : ℕ, ∀ Q : MemoryQuotient m q, ∀ X : PairType, ∀ d₀ : Compass,
    ∀ F : Phase → Fin q → Plane → ℚ, (∀ φ a, F φ a kernelCentre = 0) →
    ∀ φ a x, stationaryApplyV2 Q X d₀ F φ a x = stationaryApply Q X d₀ F φ a x

/-- `l:stationary-domination` / `l:Bellman-soundness`, ARCH_0 F9, Appendix C lines 555–686.
Both terminal-reward iterates remain zero at the centre. Induct on the iterate, identify
its corrected/legacy steps on centre-zero functions, then sum the finite horizon. This
bridge is about the fixed target reward, not arbitrary initial data. -/
def StationaryContinuationBridgeStatementV2 : Prop :=
  ∀ Q : MemoryQuotient 10 3741, ∀ X : PairType, ∀ d₀ : Compass,
    ∀ φ : Phase, ∀ a : Fin 3741, ∀ x : Plane, ∀ R : ℕ,
      stationaryContinuationSumV2 Q X d₀ φ a x R = stationaryContinuationSum Q X d₀ φ a x R

/-- `d:stationary-certificate`, ARCH_0 F9, Appendix C lines 688–760.
A corrected passing certificate also passes the legacy integer rows: all non-centre
coefficients agree, and every centre-destination rounded term is multiplied by the checked
zero extended value there. Keep the two integer scales distinct. Only this direction is
needed for reusing the frozen soundness assemblies; no finite witness is asserted. -/
def StationaryCertificateBridgeStatementV2 : Prop :=
  ∀ m q : ℕ, ∀ Q : MemoryQuotient m q, ∀ X : PairType, ∀ d₀ : Compass,
    ∀ C : StationaryData q, C.PassesV2 Q X d₀ → C.Passes Q X d₀

end AKLT.Blueprint.H3
