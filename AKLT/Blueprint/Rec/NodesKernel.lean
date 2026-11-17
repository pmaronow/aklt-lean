module
public import AKLT.Blueprint.Rec.NodesClosure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `d:kernel-order`, §7 lines 573–588. Sorting/filtering enumerates
exactly the first departures, without repetitions, independently of theta. -/
def KernelOrderingStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n,
    (kernelOrdering w).Perm (firstVisitList w) ∧ (kernelOrdering w).Nodup

/-- `d:kernel`, §7 lines 517–554. Coefficients are nonnegative. Every
response pair has two distinct live neighbors and positive coefficient. -/
def KernelPositivityStatement : Prop :=
  (∀ n : ℕ, ∀ X Y : PairType, ∀ s : ℕ, 0 ≤ kernelLengthCoefficient X Y s n) ∧
  ∀ n : ℕ, ∀ w : DirectionWord n, ∀ i : Fin n, ∀ p ∈ responsePairs w i,
    p.card = 2 ∧ 0 < pairCoefficient w i p

/-- `l:Mtheta`, §7 lines 633–642. At departure i, distances to the two
endpoints are at most i and n-i. Each response site adds one lattice step. -/
def ShiftGeometryStatement : Prop :=
  ∀ n : ℕ, ∀ X : PairType, ∀ w : DirectionWord n, ClosedTrail X w →
    ∀ i : Fin n, ∀ p ∈ responsePairs w i, (pairShift X p : ℝ) ≤ (n : ℝ) / 2 + 1

/-- `d:kernel`, §7 lines 550–554. Every nonzero length-n coefficient
has shift≤n+1; length zero contributes nothing. This justifies finite regrouping. -/
def KernelSupportStatement : Prop :=
  (∀ X Y : PairType, ∀ s : ℕ, kernelLengthCoefficient X Y s 0 = 0) ∧
  ∀ X Y : PairType, ∀ n s : ℕ, n + 1 < s → kernelLengthCoefficient X Y s n = 0

/-- `d:kernel`, §7 lines 550–554, 612–618. Exchange nonnegative ENNReal
sums and discard zero shifts beyond n+1. No divergent real tsum is used. -/
def KernelRegroupStatement : Prop :=
  ∀ θ : ℝ, 0 < θ → ∀ X Y : PairType,
    shiftedKernel θ X Y = ∑' n : ℕ, shiftedLength θ X Y n

/-- `l:Mtheta`, §7 lines 643–656. The initial exposure product is bounded
by the full first-visit product since every passageFactor≥1. The coefficients
sum to at most alpha-bar+2 beta-bar; closed trails form a subset of H2. -/
def KernelLengthMajorantStatement : Prop :=
  ∀ CV q : ℝ, OpenTrailBound CV q → ∀ θ : ℝ, q^2 < θ → θ ≤ 1 →
    ∀ X Y : PairType, ∀ n : ℕ,
      shiftedLength θ X Y n ≤ ENNReal.ofReal (kernelMajorant CV q θ n)

/-- `l:Mtheta`, §7 lines 656–659. The ratio q/sqrt(theta) is strictly
less than one. Sum n r^n, with the zero term harmless. -/
def MajorantFiniteStatement : Prop :=
  ∀ CV q : ℝ, OpenTrailBound CV q → ∀ θ : ℝ, q^2 < θ → θ ≤ 1 →
    (∑' n : ℕ, ENNReal.ofReal (kernelMajorant CV q θ n)) ≠ ⊤

/-- `h:H3`, §7 lines 595–618. Nonnegative cutoff sums exhaust the full
row. Keep the same dyadic h and cutoff-twelve ordering. -/
def UnshiftedWitnessStatement : Prop :=
  Top.H3Statement → ∀ X : PairType,
    (∑ Y : PairType, shiftedKernel 1 X Y * ENNReal.ofReal (witnessReal Y)) ≤
      ENNReal.ofReal ((kernelRho : ℝ) * witnessReal X)

/-- `l:Mtheta`, §7 lines 681–689. Mean value bound for integer shifts,
including s=0. All bases are strictly positive. -/
def ShiftPowerIncrementStatement : Prop :=
  ∀ b θ : ℝ, 0 < b → b < θ → θ ≤ 1 → ∀ n s : ℕ, s ≤ n + 1 →
    0 ≤ θ^(-(s : ℤ)) - 1 ∧
      θ^(-(s : ℤ)) - 1 ≤ (1 - θ) * (n + 1 : ℝ) * b^(-(n : ℤ) - 2)

/-- `l:Mtheta`, §7 lines 660–680. Check the explicit epsilon choice,
including B_*>0. No lower bound stronger than 0<q<1 is used. -/
def TransportChoiceStatement : Prop :=
  ∀ CV q : ℝ, OpenTrailBound CV q →
    q^2 < transportTheta CV q ∧ transportTheta CV q < 1 ∧
    (kernelRho : ℝ) < transportRho ∧ transportRho < 1 ∧
    (1 + q) / 2 < transportTheta CV q ∧
    (kernelRho : ℝ) + (1 - transportTheta CV q) * transportB CV q ≤ transportRho

/-- `l:Mtheta`, §7 lines 690–701. Sum the nonnegative row increment
using n(n+1)r^n=2r/(1-r)^3 and h_Y/h_X≤H. The unshifted inequality
is a numerical premise about this row, not an assumed leaf proposition. -/
def WitnessPerturbationStatement : Prop :=
  ∀ CV q : ℝ, OpenTrailBound CV q → ∀ θ ρ : ℝ,
    (1 + q) / 2 < θ → θ ≤ 1 → 0 < ρ →
    (kernelRho : ℝ) + (1 - θ) * transportB CV q ≤ ρ →
    ∀ X : PairType,
    (∑ Y : PairType, shiftedKernel 1 X Y * ENNReal.ofReal (witnessReal Y)) ≤
      ENNReal.ofReal ((kernelRho : ℝ) * witnessReal X) →
    (∑ Y : PairType, shiftedKernel θ X Y * ENNReal.ofReal (witnessReal Y)) ≤
      ENNReal.ofReal (ρ * witnessReal X)

/-- `l:renewal`, §7 lines 947–1005. Convert finite ENNReal shifted
rows into genuinely summable real rows, justifying every toReal conversion. -/
def ShiftedRowsRealStatement : Prop :=
  ∀ θ ρ : ℝ, 0 < θ → θ < 1 → 0 < ρ → ρ < 1 →
    Top.ShiftedWitness θ ρ → RenewalRows realKernel witnessReal θ ρ

/-- `e:rec-T1`, §7 lines 858–870. A finite length cutoff is below the
full real kernel action on any bounded nonnegative function. First prove
finiteness from H2 at theta=1, then regroup n,Y,s and use toReal_tsum.
This separates analytic summation from the domain-to-trail comparison. -/
def FiniteKernelTailDominationStatement : Prop :=
  ∀ CV q : ℝ, OpenTrailBound CV q → ∀ F : PairType → ℤ → ℝ,
    (∀ X d, 0 ≤ F X d ∧ F X d ≤ 2) → ∀ X : PairType, ∀ d : ℤ, ∀ N : ℕ,
    (∑ n ∈ Finset.range N, ∑ Y : PairType, ∑ s ∈ Finset.range (n + 2),
      (kernelLengthCoefficient X Y s n : ℝ) * F Y (d - s)) ≤ renewalOp realKernel F X d

/-- The adopted positive vector and contraction ceiling have no hidden instances. -/
theorem witness_positive (X : PairType) : 0 < witnessReal X := by
  cases X <;> norm_num [witnessReal, kernelWitness]

theorem kernelRho_pos : (0 : ℝ) < kernelRho := by norm_num [kernelRho]

end AKLT.Blueprint.Rec
