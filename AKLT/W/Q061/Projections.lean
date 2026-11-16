import Mathlib

noncomputable section

namespace AKLT.W.Q061

variable {I F : Type*}

/-- Successive coordinate projections, in the order of a finite list. -/
def averageList (E : I → F → F) : List I → F → F
  | [], f => f
  | x :: l, f => averageList E l (E x f)

theorem averageList_commute (E : I → F → F)
    (hc : ∀ x y f, E x (E y f) = E y (E x f))
    (x : I) (l : List I) (f : F) :
    E x (averageList E l f) = averageList E l (E x f) := by
  induction l generalizing f with
  | nil => rfl
  | cons y l ih =>
    simp only [averageList]
    rw [ih, hc]

theorem averageList_fixed (E : I → F → F)
    (hc : ∀ x y f, E x (E y f) = E y (E x f))
    (hi : ∀ x f, E x (E x f) = E x f)
    (x : I) (l : List I) (hx : x ∈ l) (f : F) :
    E x (averageList E l f) = averageList E l f := by
  induction l generalizing f with
  | nil => simp at hx
  | cons y l ih =>
    rcases List.mem_cons.mp hx with h | h
    · subst y
      simp only [averageList]
      rw [averageList_commute E hc, hi]
    · exact ih h (E y f)

/-- The finite commuting-projection argument for a nonnegative quadratic
form. Its Pythagorean identity supplies the contraction at each step. -/
theorem projection_tensorization [AddCommGroup F] (E : I → F → F) (q : F → ℝ)
    (hq : ∀ f, 0 ≤ q f)
    (hp : ∀ x f, q f = q (f - E x f) + q (E x f))
    (hc : ∀ x y f, E x (E y f) = E y (E x f))
    (hs : ∀ x f g, E x (f - g) = E x f - E x g)
    (l : List I) (f : F) :
    q f ≤ q (averageList E l f) + (l.map (fun x => q (f - E x f))).sum := by
  have contract (x : I) (g : F) : q (E x g) ≤ q g := by
    linarith [hp x g, hq (g - E x g)]
  induction l generalizing f with
  | nil => simp [averageList]
  | cons x l ih =>
    have term (y : I) : q (E x f - E y (E x f)) ≤ q (f - E y f) := by
      rw [← hc x y f, ← hs]
      exact contract x _
    have hsum : (l.map (fun y => q (E x f - E y (E x f)))).sum ≤
        (l.map (fun y => q (f - E y f))).sum := by
      exact List.sum_le_sum fun y _ => term y
    have h := ih (E x f)
    simp only [averageList, List.map_cons, List.sum_cons]
    linarith [hp x f]

end AKLT.W.Q061
