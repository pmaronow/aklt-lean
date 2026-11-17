module
public import AKLT.W.REC004.Conditioning
public import AKLT.W.REC004.Geometry

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC004

/-- The remaining finite reindexing problem. The outside factors are `C r`;
missing incident factors are zero letters. This asserts an exact unnormalized
finite sum, with no bound on a response or on a conditional mean assumed. -/
def Residual_FiberExpansion : Prop :=
  ∀ a : AKLT.Blueprint.Rec.Departure, a.D.status a.y = .U →
    ∀ f g : Plane, a.D.presentNeighbors a.y = {a.o, f, g} →
    a.o ≠ f → a.o ≠ g → f ≠ g → ∀ b : Bool,
      ∃ (N : ℕ) (C : Fin N → ℝ) (s : Fin 3 → Status)
        (fields : Fin N → Fin 3 → Fin 3 → SpinLetter),
        (∀ r, 0 ≤ C r) ∧ (∀ j, s j = .U ∨ s j = .D) ∧
        ∀ F : (Fin 3 → Vec3) → ℝ,
          (removeSite a.D a.y).partition a.τ b
            (fun v => F ![v f, v g, v a.o]) =
          ∑ r, C r * ∑ t : Fin 3 → SpinLetter,
            (∏ j, fiberDensity s (fields r) j (t j)) *
              F (fun j => spinVector (t j))

/-- Average independent three-spin fibers with their actual nonnegative mass.
Zero outside factors make zero contributions and require no cancellation. -/
lemma fiber_average_bounds {α : Type*} [Fintype α]
    (C : α → ℝ) (hC : ∀ r, 0 ≤ C r)
    (s : Fin 3 → Status) (hs : ∀ j, s j = .U ∨ s j = .D)
    (fields : α → Fin 3 → Fin 3 → SpinLetter) :
    (-(9 / 25 : ℝ) ≤
        (∑ r, C r * fiberMass s (fields r) *
          dot (fiberMean s (fields r) 0) (fiberMean s (fields r) 1)) /
        (∑ r, C r * fiberMass s (fields r)) ∧
      (∑ r, C r * fiberMass s (fields r) *
          dot (fiberMean s (fields r) 0) (fiberMean s (fields r) 1)) /
        (∑ r, C r * fiberMass s (fields r)) ≤ 9 / 25) ∧
    (-(27 / 50 : ℝ) ≤
        (∑ r, C r * fiberMass s (fields r) *
          (dot (fiberMean s (fields r) 0) (fiberMean s (fields r) 1) +
           dot (fiberMean s (fields r) 0) (fiberMean s (fields r) 2) +
           dot (fiberMean s (fields r) 1) (fiberMean s (fields r) 2))) /
        (∑ r, C r * fiberMass s (fields r)) ∧
      (∑ r, C r * fiberMass s (fields r) *
          (dot (fiberMean s (fields r) 0) (fiberMean s (fields r) 1) +
           dot (fiberMean s (fields r) 0) (fiberMean s (fields r) 2) +
           dot (fiberMean s (fields r) 1) (fiberMean s (fields r) 2))) /
        (∑ r, C r * fiberMass s (fields r)) ≤ 27 / 25) := by
  have hW : ∀ r, 0 ≤ C r * fiberMass s (fields r) :=
    fun r => mul_nonneg (hC r) (le_of_lt (fiber_mass_pos s hs _))
  constructor
  · apply quotient_interval _ _ _ _ hW (by norm_num) (by norm_num)
    intro r
    have h := dot_bounds (by norm_num : (0 : ℝ) ≤ 9 / 25)
      (fiber_mean_bound s hs (fields r) 0) (fiber_mean_bound s hs (fields r) 1)
    constructor
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left h.1 (hW r)
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left h.2 (hW r)
  · apply quotient_interval _ _ _ _ hW (by norm_num) (by norm_num)
    intro r
    have h := triple_dot_bounds (fiber_mean_bound s hs (fields r) 0)
      (fiber_mean_bound s hs (fields r) 1) (fiber_mean_bound s hs (fields r) 2)
    constructor
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left h.1 (hW r)
    · simpa [mul_comm] using mul_le_mul_of_nonneg_left h.2 (hW r)

/-- All interval arithmetic is finished once the explicit fiber expansion is supplied. -/
theorem removed_pair_bounds_from_fibers (h : Residual_FiberExpansion)
    (a : AKLT.Blueprint.Rec.Departure) (hU : a.D.status a.y = .U)
    (f g : Plane) (hN : a.D.presentNeighbors a.y = {a.o, f, g})
    (hof : a.o ≠ f) (hog : a.o ≠ g) (hfg : f ≠ g) (b : Bool) :
    (-(9 / 25 : ℝ) ≤ removedPairMean a.D a.τ b a.y f g ∧
      removedPairMean a.D a.τ b a.y f g ≤ 9 / 25) ∧
    (-(27 / 50 : ℝ) ≤
      removedPairMean a.D a.τ b a.y f g + removedPairMean a.D a.τ b a.y f a.o +
        removedPairMean a.D a.τ b a.y g a.o ∧
      removedPairMean a.D a.τ b a.y f g + removedPairMean a.D a.τ b a.y f a.o +
        removedPairMean a.D a.τ b a.y g a.o ≤ 27 / 25) := by
  obtain ⟨N, C, s, fields, hC, hs, hE⟩ := h a hU f g hN hof hog hfg b
  have hZ := hE (fun _ => 1)
  have h01 := hE (fun v => dot (v 0) (v 1))
  have h02 := hE (fun v => dot (v 0) (v 2))
  have h12 := hE (fun v => dot (v 1) (v 2))
  simp only [mul_one, fiber_mass_eq] at hZ
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons,
    fiber_pair_eq s hs _ 0 1 (by decide),
    fiber_pair_eq s hs _ 0 2 (by decide),
    fiber_pair_eq s hs _ 1 2 (by decide)] at h01 h02 h12
  have hb := fiber_average_bounds C hC s hs fields
  have hp01 : removedPairMean a.D a.τ b a.y f g =
      (∑ r, C r * fiberMass s (fields r) *
        dot (fiberMean s (fields r) 0) (fiberMean s (fields r) 1)) /
        (∑ r, C r * fiberMass s (fields r)) := by
    unfold removedPairMean Network.expectation
    rw [hZ, h01]
    simp only [mul_assoc]
  have hp02 : removedPairMean a.D a.τ b a.y f a.o =
      (∑ r, C r * fiberMass s (fields r) *
        dot (fiberMean s (fields r) 0) (fiberMean s (fields r) 2)) /
        (∑ r, C r * fiberMass s (fields r)) := by
    unfold removedPairMean Network.expectation
    rw [hZ, h02]
    simp only [mul_assoc]
  have hp12 : removedPairMean a.D a.τ b a.y g a.o =
      (∑ r, C r * fiberMass s (fields r) *
        dot (fiberMean s (fields r) 1) (fiberMean s (fields r) 2)) /
        (∑ r, C r * fiberMass s (fields r)) := by
    unfold removedPairMean Network.expectation
    rw [hZ, h12]
    simp only [mul_assoc]
  rw [hp01, hp02, hp12]
  constructor
  · exact hb.1
  · simpa only [mul_add, Finset.sum_add_distrib, add_div] using hb.2

#print axioms removed_pair_bounds_from_fibers

end AKLT.W.REC004
