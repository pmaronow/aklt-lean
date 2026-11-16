import AKLT.W.REC043.Padding

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC043

private def fillLabels {ι : Type*} [DecidableEq ι] (i : ι)
    (n : {x : ι // x ≠ i} → SpinLetter) (j : SpinLetter) (x : ι) : SpinLetter :=
  if h : x = i then j else n ⟨x, h⟩

private def fibreEquiv {ι : Type*} [DecidableEq ι] (i : ι) :
    ({x : ι // x ≠ i} → SpinLetter) × SpinLetter ≃ (ι → SpinLetter) where
  toFun p := fillLabels i p.1 p.2
  invFun n := (fun x => n x.val, n i)
  left_inv p := by
    apply Prod.ext
    · funext x
      simp [fillLabels, x.property]
    · simp [fillLabels]
  right_inv n := by
    funext x
    by_cases h : x = i <;> simp [fillLabels, h]

/-- The fixed-volume spins at every site except the coordinate integrated out. -/
def fibreSpins {G : Finset Plane} (u : G)
    (n : {x : G // x ≠ u} → SpinLetter) : Plane → Vec3 :=
  volumeSpins (fillLabels u n none)

private theorem volumeSpins_fill {G : Finset Plane} (u : G)
    (n : {x : G // x ≠ u} → SpinLetter) (j : SpinLetter) :
    volumeSpins (fillLabels u n j) = Function.update (fibreSpins u n) u.val (spinVector j) := by
  funext x
  by_cases hxu : x = u.val
  · subst x
    simp [volumeSpins, fillLabels, u.property]
  · by_cases hxG : x ∈ G
    · have hne : (⟨x, hxG⟩ : G) ≠ u := fun h => hxu (congrArg Subtype.val h)
      simp [volumeSpins, fibreSpins, fillLabels, hxG, hne, hxu]
    · simp [volumeSpins, fibreSpins, hxG, hxu]

/-- Finite Fubini at one chosen site, with a common outside configuration.
It is valid for arbitrary functions, so original bond and leg factors can
be retained literally in H. -/
theorem finite_site_fibre {G : Finset Plane} (D : Network G) (u : G)
    (H : (Plane → Vec3) → ℝ) :
    (∑ n : (x : G) → SpinLetter, (∏ x : G, paddedWeight (D.status x.val) (n x)) *
        H (volumeSpins n)) =
      ∑ n : {x : G // x ≠ u} → SpinLetter,
        (∏ x : {x : G // x ≠ u}, paddedWeight (D.status x.val.val) (n x)) *
          ∑ j : SpinLetter, paddedWeight (D.status u.val) j *
            H (Function.update (fibreSpins u n) u.val (spinVector j)) := by
  classical
  rw [← Equiv.sum_comp (fibreEquiv u)]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  change (∏ x : G, paddedWeight (D.status x.val) (fillLabels u n j x)) *
      H (volumeSpins (fillLabels u n j)) = _
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ u, volumeSpins_fill]
  have hp : (∏ x : {x : G // x ≠ u},
      paddedWeight (D.status x.val.val) (fillLabels u n j x.val)) =
      ∏ x : {x : G // x ≠ u}, paddedWeight (D.status x.val.val) (n x) := by
    apply Finset.prod_congr rfl
    intro x hx
    simp [fillLabels, x.property]
  rw [hp]
  simp only [fillLabels, dite_true]
  ring

end AKLT.W.REC043
