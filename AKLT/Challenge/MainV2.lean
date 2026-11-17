module
public import Mathlib
public import AKLT.Challenge.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-!
# The all-parity AKLT challenge

This is the revised `t:main` of the revision plan. All physical objects are
the frozen definitions of `AKLT.Challenge.Main`.
-/

namespace AKLT.Challenge

/-- `t:main`: for every torus with both periods at least three, the VBS vector
is nonzero and spans the kernel. There are a positive constant and one size
threshold above which every nonzero eigenvalue has that uniform lower bound.
Both assertions allow every parity; uniqueness has no eventual-size restriction.
The subtype `Size` already expresses the lower bound three on each period. -/
def MainStatementV2 : Prop :=
  (∀ L N : Size, B L N ≠ 0 ∧
    LinearMap.ker (H L N) = Submodule.span ℂ {B L N}) ∧
  ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, 3 ≤ L₀ ∧
    ∀ L N : Size, L₀ ≤ L.val → L₀ ≤ N.val →
      ∀ μ : ℝ, μ ≠ 0 → (H L N).HasEigenvalue (μ : ℂ) → c ≤ μ

end AKLT.Challenge
