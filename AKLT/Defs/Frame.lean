import AKLT.Defs.Moment

noncomputable section
open scoped BigOperators

namespace AKLT.Defs

/-- `d:frame`: finite frame data, before any moment or positivity assertion. -/
structure FrameData (n : ℕ) where
  point : Fin n → Vec3
  weight : Fin n → ℝ

/-- `d:frame`: precisely the positive degree-four moment-frame property. -/
def IsFrame {n : ℕ} (F : FrameData n) : Prop :=
  Function.Injective F.point ∧ (∀ j, normSq (F.point j) = 1) ∧
  (∀ j, 0 < F.weight j) ∧ (∑ j, F.weight j) = 1 ∧
  ∀ p : MvPolynomial (Fin 3) ℝ, DegreeFour p →
    (∑ j, F.weight j * MvPolynomial.eval (F.point j) p) =
      moment (fun a => MvPolynomial.eval a p)

/-- `l:exact`: a weighted moment law may repeat atoms; injectivity is not required. -/
def MomentLaw {n : ℕ} (F : FrameData n) : Prop :=
  (∀ j, normSq (F.point j) = 1) ∧ (∀ j, 0 < F.weight j) ∧ (∑ j, F.weight j) = 1 ∧
  ∀ p : MvPolynomial (Fin 3) ℝ, DegreeFour p →
    (∑ j, F.weight j * MvPolynomial.eval (F.point j) p) = moment (fun a => MvPolynomial.eval a p)

/-- `l:exact`: arbitrary finite moment law, optionally mixed with the zero atom. -/
def momentLawFunctional {n : ℕ} (F : FrameData n) (s : Status) (f : Vec3 → ℝ) : ℝ :=
  if s = .D then (3 / 5) * (∑ j, F.weight j * f (F.point j)) + (2 / 5) * f 0
  else ∑ j, F.weight j * f (F.point j)

/-- `l:threeframes`: the frozen rational rotation. -/
def frameRotation : Matrix (Fin 3) (Fin 3) ℝ :=
  !![99 / 101, -20 / 101, 0; 20 / 101, 99 / 101, 0; 0, 0, 1]

/-- `l:threeframes`: the actual vector in rotated alphabet `j`. -/
def frameVector (j : Fin 3) (a : IcoLetter) : Vec3 :=
  (frameRotation ^ j.val).mulVec (icoVector a)

/-- `l:threeframes`: the attained common interaction lower bound. -/
def frameBound : ℝ := (5 - Real.sqrt 5) / 505

/-- `l:threeframes`: the single-bond density ratio. -/
def frameRatio : ℝ := frameBound / (2 - frameBound)

/-- `l:planeenergy`: finite energy for admissible frame letters only. -/
def frameEnergy : ℝ := (1 / 12) * frameRatio ^ 4

/-- `d:poly`: spinors have two complex coordinates. -/
abbrev Spinor := Fin 2 → ℂ

/-- `d:Pauli`: identity and the three Pauli matrices, in x,y,z order. -/
def pauli : Fin 4 → Matrix (Fin 2) (Fin 2) ℂ
  | 0 => 1
  | 1 => !![0, 1; 1, 0]
  | 2 => !![0, -Complex.I; Complex.I, 0]
  | _ => !![1, 0; 0, -1]

/-- `d:Pauli`: the product-density building block `(I+a.sigma)/2`. -/
def spinDensity (a : Vec3) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 / 2 : ℂ) • (1 + ∑ k : Fin 3, (a k : ℂ) • pauli ⟨k.val + 1, by omega⟩)

/-- `d:poly`: an explicit choice on the finite family of frame letters only.
The pole branch avoids division by zero; its required identities are in `TightStatement`. -/
def frameSpinor (j : Fin 3) (a : IcoLetter) : Spinor :=
  let v := frameVector j a
  if v 2 = -1 then ![0, 1] else
    ![(Real.sqrt ((1 + v 2) / 2) : ℂ),
      ((v 0 : ℂ) + Complex.I * (v 1 : ℂ)) / (Real.sqrt (2 * (1 + v 2)) : ℂ)]

end AKLT.Defs
