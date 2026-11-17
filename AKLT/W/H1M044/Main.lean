module
public import AKLT.Blueprint.H1.NodesStructure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.W.H1M044

private theorem evaluate_invertPolynomial
    (I : Finset (Fin 20)) (p : AKLT.Blueprint.H1.VectorPolynomial)
    (u : Fin 20 → Vec3) :
    evaluateReduced (invertPolynomial I p) u = evaluateReduced p (invertVectors I u) := by
  classical
  unfold evaluateReduced invertPolynomial invertVectors
  let E : MvPolynomial (Fin 20 × Fin 3) ℚ →+* ℝ :=
    MvPolynomial.eval₂Hom (Rat.castHom ℝ) (fun v => u v.1 v.2)
  let H : MvPolynomial (Fin 20 × Fin 3) ℚ →+* MvPolynomial (Fin 20 × Fin 3) ℚ :=
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun v => (if v.1 ∈ I then -1 else 1) * MvPolynomial.X v)
  change (E.comp H) p = _
  rw [MvPolynomial.comp_eval₂Hom]
  have hcoeff : E.comp MvPolynomial.C = Rat.castHom ℝ := by
    ext q
    simp [E]
  have hvars : (fun v => E ((if v.1 ∈ I then -1 else 1) * MvPolynomial.X v)) =
      (fun v => (if v.1 ∈ I then -u v.1 else u v.1) v.2) := by
    funext v
    by_cases hv : v.1 ∈ I <;> simp [E, hv]
  rw [hcoeff, hvars]
  rfl

theorem main : AKLT.Blueprint.H1.InversionCovarianceStatement := by
  intro p hp I R hR u
  rw [evaluate_invertPolynomial, evaluate_invertPolynomial]
  have hcomm : invertVectors I (fun j => R.mulVec (u j)) =
      fun j => R.mulVec (invertVectors I u j) := by
    funext j
    simp only [invertVectors]
    split_ifs with hj
    · rw [Matrix.mulVec_neg]
    · rfl
  rw [hcomm]
  exact hp R hR (invertVectors I u)

end AKLT.W.H1M044
