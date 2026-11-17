module
public import AKLT.Blueprint.Top.Common

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.Blueprint.Top

/-- `h:H1`, equivalently `t:H1`: the frozen pointwise local input at the two exact thresholds. -/
def H1Statement : Prop := LocalPatternBound (961 / 1000) (187 / 200)

/-- `t:H1`: the operator-only local input theorem has precisely the semantic H1 conclusion. -/
def H1TheoremStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector,
    (if π.outgoing = .north then (961 / 1000 : ℝ) else 187 / 200) * patternNext π m ≤ patternCurrent π m

/-- `h:H2`: the selected all-length open-trail assertion, with C_V=10 and exact q_*. -/
def H2Statement : Prop := OpenTrailBound 10 (certifiedRate : ℝ)

/-- `h:H3`: all finite cutoffs of the type-dependent kernel, with its fixed dyadic vector and orderings. -/
def H3Statement : Prop := PositiveVectorBound

/-- `t:inputs`: the three semantic conclusions of the adopted certificate routes.
The finite reconstruction obligations and provenance are separate closed Props below. -/
def InputsStatement : Prop :=
  H1Statement ∧ H2Statement ∧ H3Statement ∧ certifiedRate < (2499 / 2500 : ℚ) ∧
    (2499 / 2500 : ℚ) < 1

/-- `h:P`: existence of the response property supplied to the window lane. -/
def PStatement : Prop := ∃ A θ : ℝ, ResponseProperty A θ

/-- `t:rec`: the exact amplitude furnished by bounded renewal and the same shifted vector. -/
def renewalAmplitude (CV q ρ : ℝ) : ℝ :=
  (max (kernelWitness .B : ℝ) (kernelWitness .C : ℝ) /
    min (kernelWitness .B : ℝ) (kernelWitness .C : ℝ)) *
      max 2 (2 * (12 / 5 : ℝ)^24 * (CV / (1 - q))^2) / (1 - ρ)

/-- `l:Mtheta`: a finite shifted positive-vector inequality in extended nonnegative reals. -/
def ShiftedWitness (θ ρ : ℝ) : Prop :=
  (∀ X Y : PairType, shiftedKernel θ X Y ≠ ⊤) ∧
  ∀ X : PairType, (∑ Y : PairType, shiftedKernel θ X Y * ENNReal.ofReal (kernelWitness Y : ℝ)) ≤
    ENNReal.ofReal (ρ * (kernelWitness X : ℝ))

/-- `t:rec`: for arbitrary finite C_V and 0<q<1, the fixed local input and fixed
type-dependent H3 produce P. The existential witnesses retain the displayed renewal amplitude. -/
def RecStatement : Prop :=
  ∀ CV q : ℝ, H1Statement → OpenTrailBound CV q → H3Statement →
    ∃ θ ρ : ℝ, q^2 < θ ∧ θ < 1 ∧ (kernelRho : ℝ) < ρ ∧ ρ < 1 ∧
      ShiftedWitness θ ρ ∧ ResponseProperty (renewalAmplitude CV q ρ) θ

/-- `l:Mtheta`: every admissible shifted entry is finite with the stated summable
majorant, and the same h works for a theta strictly below one. -/
def MThetaStatement : Prop :=
  ∀ CV q : ℝ, OpenTrailBound CV q → H3Statement →
    (∀ θ : ℝ, q^2 < θ → θ ≤ 1 → ∀ X Y : PairType,
      shiftedKernel θ X Y ≠ ⊤ ∧ shiftedKernel θ X Y ≤
        ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) *
          CV * q^n * Real.rpow θ (-(n : ℝ) / 2 - 1))) ∧
    (∀ n : ℕ, ∀ X : PairType, ∀ w : DirectionWord n, ClosedTrail X w →
      ∀ i : Fin n, ∀ p ∈ responsePairs w i, (pairShift X p : ℝ) ≤ (n : ℝ) / 2 + 1) ∧
    ∃ θ ρ : ℝ, q^2 < θ ∧ θ < 1 ∧ (kernelRho : ℝ) < ρ ∧ ρ < 1 ∧ ShiftedWitness θ ρ

end AKLT.Blueprint.Top
