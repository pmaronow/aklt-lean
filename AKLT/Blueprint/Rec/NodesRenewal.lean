module
public import AKLT.Blueprint.Rec.NodesRecursion

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.Blueprint.Rec

/-- `l:renewal`, §7 lines 949–966. A weighted summable row is also
unshifted summable since theta^-s≥1. The shift operator acts positively on
bounded functions. This prevents use of the default zero for divergent tsums. -/
def RenewalActionStatement : Prop :=
  ∀ m : PairType → PairType → ℕ → ℝ, ∀ h : PairType → ℝ, ∀ θ ρ : ℝ,
    0 < θ → θ < 1 → 0 < ρ → ρ < 1 → RenewalRows m h θ ρ →
    ∀ f : PairType → ℤ → ℝ, (∃ B : ℝ, ∀ X d, 0 ≤ f X d ∧ f X d ≤ B) →
    ∀ X d, Summable (fun j : PairType × ℕ => m X j.1 j.2 * f j.1 (d - j.2)) ∧
      0 ≤ renewalOp m f X d

/-- `e:rec-renewal-iterate`, §7 lines 968–970. Extend F≤KF+g to
nonpositive integers using F≤2. Induct k using positivity and linearity
on bounded functions. This is a finite iteration, with no fixed-point construction.
Its indices explicitly have different types: X is PairType and d is an integer. -/
def RenewalFiniteIterationStatement : Prop :=
  ∀ m : PairType → PairType → ℕ → ℝ, ∀ h : PairType → ℝ,
    ∀ q θ ρ CT : ℝ, 0 < q → q^2 < θ → θ < 1 → 0 < ρ → ρ < 1 → 0 ≤ CT →
    RenewalRows m h θ ρ → ∀ F : PairType → ℤ → ℝ,
    (∀ X d, 0 ≤ F X d ∧ F X d ≤ 2) →
    (∀ X : PairType, ∀ d : ℕ, 1 ≤ d →
      F X d ≤ renewalOp m F X d + CT * q^(2*d)) →
    ∀ k : ℕ, ∀ X : PairType, ∀ d : ℤ,
      F X d ≤ renewalIterate m F k X d +
        ∑ j ∈ Finset.range k, renewalIterate m (renewalSource CT q) j X d

/-- `e:rec-renewal-remainder`, §7 lines 972–980. Compare the bounded
F to the unshifted h, then iterate the unshifted row inequality. The result
is uniform in negative d, so arbitrary backward shifts cause no difficulty. -/
def RenewalRemainderStatement : Prop :=
  ∀ m : PairType → PairType → ℕ → ℝ, ∀ h : PairType → ℝ, ∀ θ ρ : ℝ,
    0 < θ → θ < 1 → 0 < ρ → ρ < 1 → RenewalRows m h θ ρ →
    ∀ F : PairType → ℤ → ℝ, (∀ X d, 0 ≤ F X d ∧ F X d ≤ 2) →
    ∀ k : ℕ, ∀ X : PairType, ∀ d : ℤ,
      renewalIterate m F k X d ≤ (2 / hmin h) * ρ^k * h X

/-- `l:renewal`, §7 lines 982–998. The source is below C_* h_X
theta^d/h_min on ALL integers. Apply the shifted row inequality repeatedly;
each nonnegative weighted sum is summable by RenewalRows. -/
def RenewalSourceStatement : Prop :=
  ∀ m : PairType → PairType → ℕ → ℝ, ∀ h : PairType → ℝ,
    ∀ q θ ρ CT : ℝ, 0 < q → q^2 < θ → θ < 1 → 0 < ρ → ρ < 1 → 0 ≤ CT →
    RenewalRows m h θ ρ → ∀ k : ℕ, ∀ X : PairType, ∀ d : ℤ,
      renewalIterate m (renewalSource CT q) k X d ≤
        (max 2 CT / hmin h) * ρ^k * h X * θ^d

/-- `l:renewal`, §7 lines 999–1007. Let k tend to infinity in the
finite scalar bound, using rho^k→0 and the geometric series. -/
def RenewalScalarLimitStatement : Prop :=
  ∀ x a b ρ : ℝ, 0 ≤ a → 0 ≤ b → 0 < ρ → ρ < 1 →
    (∀ k : ℕ, x ≤ a * ρ^k + b * ∑ j ∈ Finset.range k, ρ^j) → x ≤ b / (1 - ρ)

end AKLT.Blueprint.Rec
