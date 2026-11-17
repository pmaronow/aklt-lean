module
public import AKLT.Blueprint.Mom.NodesCore

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Mom

/-- `l:moments`, lines 56–61: use the unique zero coordinate and the two
nonzero signs. Positivity of the radius prevents loss of information on division. -/
def IcoInjectivityStatement : Prop := Function.Injective icoVector

/-- `l:moments`, lines 56–57: each numerator has squared length `1+phi^2`.
Use `phi^2=phi+1` and the positive square root defining the radius. -/
def IcoUnitStatement : Prop := ∀ j, normSq (icoVector j) = 1

/-- `l:moments`, lines 60–61: reverse both independent signs in the label. -/
def IcoAntipodalStatement : Prop := ∀ j, ∃ k, icoVector k = -icoVector j

theorem icoAntipodal : IcoAntipodalStatement := by
  intro j
  refine ⟨(j.1, 1 - j.2.1, 1 - j.2.2), ?_⟩
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> funext i <;> fin_cases i <;>
    simp [icoVector, signValue] <;> ring

/-- `l:moments`, lines 63–65: pair each label with the label obtained by
flipping an odd coordinate. This holds in all degrees, not just through four. -/
def OddMonomialStatement : Prop :=
  ∀ m : Fin 3 → ℕ, (∃ i, Odd (m i)) → moment (mono m) = 0

/-- `l:moments`, line 68: sum the three groups, obtaining
`(1+phi^2)/(3*r^2)=1/3`. There are only three coordinate cases. -/
def SecondScalarMomentStatement : Prop :=
  ∀ i, moment (fun v => v i ^ 2) = 1 / 3

/-- `l:moments`, line 69: use `1+phi^4=3*phi^2` and `r^4=5*phi^2`. -/
def FourthScalarMomentStatement : Prop :=
  ∀ i, moment (fun v => v i ^ 4) = 1 / 5

/-- `l:moments`, line 70: exactly one group contributes to a distinct
coordinate pair, giving `phi^2/(3*r^4)=1/15`. -/
def MixedScalarMomentStatement : Prop :=
  ∀ i j, i ≠ j → moment (fun v => v i ^ 2 * v j ^ 2) = 1 / 15

/-- `l:moments`, line 40: twelve equally weighted labels give mass one. -/
def MomentConstantStatement : Prop := moment (fun _ => 1) = 1

theorem momentConstant : MomentConstantStatement := by
  norm_num [MomentConstantStatement, moment, IcoLetter, Fintype.card_prod]

/-- `d:moment`/`l:moments`, lines 17–18/86–89: identify the common-support
functional with the actual U law or its zero-atom mixture. Includes zero-weight labels. -/
def SiteLawDecompositionStatement : Prop :=
  (∀ f : Vec3 → ℝ, siteFunctional .U f = moment f) ∧
  ∀ f : Vec3 → ℝ, siteFunctional .D f = (3 / 5) * moment f + (2 / 5) * f 0

theorem siteLawDecomposition : SiteLawDecompositionStatement := by
  constructor
  · intro f
    simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, moment,
      Finset.mul_sum]
  · intro f
    simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector, moment,
      ← Finset.mul_sum]
    ring

/-- `l:finitefacts`, lines 141–146: U/D weights are nonnegative and every
unit label has positive weight. The zero label need not have positive weight. -/
def SiteWeightStatement : Prop :=
  ∀ s : Status, s = .U ∨ s = .D →
    (∀ j : SpinLetter, 0 ≤ spinWeight s j) ∧
    ∀ j : IcoLetter, 0 < spinWeight s (some j)

theorem siteWeight : SiteWeightStatement := by
  intro s hs
  rcases hs with rfl | rfl
  all_goals
    constructor
    · intro j; cases j <;> norm_num [spinWeight]
    · intro j; norm_num [spinWeight]

end AKLT.Blueprint.Mom
