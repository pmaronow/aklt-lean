import AKLT.Gen.Bellman.Basic

/-!
# Finite modifications of a free supersolution

The stored box is any finite set of full states, and the free state can discard position.
Outside rows use the same edge labels, compatible projected destinations, and no larger
coefficients. The cap is required at every stored state, including the interior.
-/

namespace AKLT.Gen.Bellman

open scoped ENNReal
attribute [local instance] Classical.propDecidable

variable {S Q L : Type*}

/-- Extend a finite table by a position independent free potential. -/
noncomputable def patch (box : Finset S) (π : S → Q) (u : S → ℝ≥0∞)
    (z : Q → ℝ≥0∞) (x : S) : ℝ≥0∞ :=
  if x ∈ box then u x else z (π x)

theorem patch_eq_inside (box : Finset S) (π : S → Q) (u : S → ℝ≥0∞)
    (z : Q → ℝ≥0∞) {x : S} (hx : x ∈ box) : patch box π u z x = u x := by
  simp [patch, hx]

theorem patch_eq_outside (box : Finset S) (π : S → Q) (u : S → ℝ≥0∞)
    (z : Q → ℝ≥0∞) {x : S} (hx : x ∉ box) : patch box π u z x = z (π x) := by
  simp [patch, hx]

theorem patch_le_cap (box : Finset S) (π : S → Q) (u : S → ℝ≥0∞)
    (z : Q → ℝ≥0∞) (hcap : ∀ x ∈ box, u x ≤ z (π x)) (x : S) :
    patch box π u z x ≤ z (π x) := by
  by_cases hx : x ∈ box <;> simp [patch, hx, hcap x]

theorem patch_ne_top (box : Finset S) (π : S → Q) (u : S → ℝ≥0∞)
    (z : Q → ℝ≥0∞) (hu : ∀ x ∈ box, u x ≠ ∞) (hz : ∀ q, z q ≠ ∞) (x : S) :
    patch box π u z x ≠ ∞ := by
  by_cases hx : x ∈ box <;> simp [patch, hx, hu x, hz]

/-- Per-edge projection and coefficient bounds imply the outside row comparison. -/
theorem patch_step_le_free (T : System S L) (W : System Q L)
    (box : Finset S) (π : S → Q) (u : S → ℝ≥0∞) (z : Q → ℝ≥0∞)
    (hcap : ∀ x ∈ box, u x ≤ z (π x)) {x : S}
    (hnext : ∀ a, π (T.next x a) = W.next (π x) a)
    (hweight : ∀ a, T.weight x a ≤ W.weight (π x) a) :
    T.step (patch box π u z) x ≤ W.step z (π x) := by
  apply ENNReal.tsum_le_tsum
  intro a
  have hv : patch box π u z (T.next x a) ≤ z (W.next (π x) a) := by
    rw [← hnext a]
    exact patch_le_cap box π u z hcap _
  exact mul_le_mul (hweight a) hv (by positivity) (by positivity)

/-- Finite checked rows plus a free supersolution give a global additive Bellman inequality. -/
theorem local_global (T : System S L) (W : System Q L)
    (box : Finset S) (π : S → Q) (u : S → ℝ≥0∞) (z : Q → ℝ≥0∞)
    (g : S → ℝ≥0∞)
    (hcap : ∀ x ∈ box, u x ≤ z (π x))
    (hfree : ∀ q, W.step z q ≤ z q)
    (hnext : ∀ x, x ∉ box → ∀ a, π (T.next x a) = W.next (π x) a)
    (hweight : ∀ x, x ∉ box → ∀ a, T.weight x a ≤ W.weight (π x) a)
    (hg : ∀ x, x ∉ box → g x = 0)
    (hrows : ∀ x ∈ box, g x + T.step (patch box π u z) x ≤ u x)
    (x : S) : g x + T.step (patch box π u z) x ≤ patch box π u z x := by
  by_cases hx : x ∈ box
  · rw [patch_eq_inside box π u z hx]
    exact hrows x hx
  · rw [patch_eq_outside box π u z hx, hg x hx, zero_add]
    exact (patch_step_le_free T W box π u z hcap (hnext x hx) (hweight x hx)).trans
      (hfree (π x))

/-- The finite certificate therefore bounds the entire infinite path sum. -/
theorem local_global_total_le (T : System S L) (W : System Q L)
    (box : Finset S) (π : S → Q) (u : S → ℝ≥0∞) (z : Q → ℝ≥0∞)
    (g : S → ℝ≥0∞)
    (hcap : ∀ x ∈ box, u x ≤ z (π x))
    (hfree : ∀ q, W.step z q ≤ z q)
    (hnext : ∀ x, x ∉ box → ∀ a, π (T.next x a) = W.next (π x) a)
    (hweight : ∀ x, x ∉ box → ∀ a, T.weight x a ≤ W.weight (π x) a)
    (hg : ∀ x, x ∉ box → g x = 0)
    (hrows : ∀ x ∈ box, g x + T.step (patch box π u z) x ≤ u x)
    (x : S) : T.total g x ≤ patch box π u z x :=
  T.total_le g _ (local_global T W box π u z g hcap hfree hnext hweight hg hrows) x

/-- Generic prefix assembly: any dominated continuation can be replaced by its Bellman bound. -/
theorem prefix_domination (T : System S L) (g F : S → ℝ≥0∞)
    (hF : ∀ x, g x + T.step F x ≤ F x) {P : Type*}
    (p : P → ℝ≥0∞) (endpoint : P → S) (suffix : P → ℝ≥0∞)
    (hsuffix : ∀ a, suffix a ≤ T.total g (endpoint a)) (short : ℝ≥0∞) :
    short + ∑' a, p a * suffix a ≤ short + ∑' a, p a * F (endpoint a) := by
  apply add_le_add (le_refl short)
  apply ENNReal.tsum_le_tsum
  intro a
  exact mul_le_mul (le_refl _) ((hsuffix a).trans (T.total_le g F hF _))
    (by positivity) (by positivity)

end AKLT.Gen.Bellman
