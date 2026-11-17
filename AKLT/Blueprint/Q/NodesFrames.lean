module
public import AKLT.Blueprint.Q.Definitions

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.Blueprint.Q

/-- `l:threeframes`, sec3 lines 359–360: exact rational matrix arithmetic. -/
def RotationStatement : Prop :=
  frameRotation.transpose * frameRotation = 1 ∧ frameRotation.det = 1

/-- `l:threeframes`, lines 365–368: the three powers remain orthogonal. -/
def RotationPowersStatement : Prop :=
  ∀ j : Fin 3, (frameRotation ^ j.val).transpose * (frameRotation ^ j.val) = 1

/-- `l:threeframes`, lines 378–381, 422, 431; `l:planeenergy`, lines 731–732:
radical bounds and the resulting strictly positive scalar constants. -/
def FrameScalarsStatement : Prop :=
  0 < frameBound ∧ frameBound < 1 ∧ frameBound < 9 / 50 ∧
  0 < frameRatio ∧ frameRatio < 1 ∧ 0 < frameEnergy ∧ frameEnergy ≤ 1

/-- `l:threeframes`, lines 360–369: an orthogonal matrix preserves injectivity,
unit length, and antipodality of any labeled finite family. -/
def OrthogonalFamilyStatement : Prop :=
  ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
  ∀ v : IcoLetter → Vec3, Function.Injective v → (∀ a, normSq (v a) = 1) →
    (∀ a, ∃ b, v b = -v a) →
    Function.Injective (fun a => R.mulVec (v a)) ∧
    (∀ a, normSq (R.mulVec (v a)) = 1) ∧
    ∀ a, ∃ b, R.mulVec (v b) = -R.mulVec (v a)

/-- `l:threeframes`, lines 363–366: rename a polynomial into the one-site
product functional. This is the small bridge to the other part's `l:moments`;
it asserts no arbitrary-function rotation invariance. -/
def OneSiteMomentEncodingStatement : Prop :=
  ∀ p : MvPolynomial (Fin 3) ℝ, DegreeFour p →
    ∃ q : MvPolynomial (Fin 1 × Fin 3) ℝ, SeparateDegreeFour q ∧
      productFunctional (fun _ : Fin 1 => Status.U)
        (fun a => MvPolynomial.eval (fun v => a v.1 v.2) q) =
        moment (fun a => MvPolynomial.eval a p) ∧
      ∀ R : Matrix (Fin 3) (Fin 3) ℝ,
        productFunctional (fun _ : Fin 1 => Status.U)
          (fun a => MvPolynomial.eval (fun v => (R.mulVec (a v.1)) v.2) q) =
          moment (fun a => MvPolynomial.eval (R.mulVec a) p)

/-- `l:threeframes`, lines 398–409: distinct explicit ico labels have squared
distance strictly greater than one. Split by the three coordinate families
and four sign choices; use sqrt(5)^2=5 and positivity of the radius. -/
def IcoDistanceStatement : Prop :=
  ∀ a b : IcoLetter, a ≠ b → 1 < normSq (icoVector a - icoVector b)

/-- `l:threeframes`, lines 411–417: compute the displacement of T and T^2
on an arbitrary unit vector. Squared norms avoid an operator-norm API. -/
def RotationDisplacementStatement : Prop :=
  ∀ k : ℕ, 1 ≤ k → k ≤ 2 → ∀ v : Vec3, normSq v = 1 →
    normSq ((frameRotation ^ k).mulVec v - v) ≤ (40 / 101 : ℝ)^2

/-- `l:threeframes`, lines 386–396: equal-vertex comparison in each coordinate
family, and the displayed equality witness (0,1,phi)/r. -/
def SelfRotationStatement : Prop :=
  (∀ k : ℕ, 1 ≤ k → k ≤ 2 → ∀ a : IcoLetter,
    frameBound ≤ 1 - dot (icoVector a) ((frameRotation ^ k).mulVec (icoVector a))) ∧
  1 - dot (frameVector 0 (0, 0, 0)) (frameVector 1 (0, 0, 0)) = frameBound

/-- `l:threeframes`, lines 418–420: squared triangle/Cauchy inequality in
three coordinates. The strict input distance gives the strict 9/50 bound. -/
def DisplacedDistanceStatement : Prop :=
  ∀ u v w : Vec3, normSq u = 1 → normSq v = 1 → normSq w = 1 →
    1 < normSq (u - v) → normSq (w - v) ≤ (40 / 101 : ℝ)^2 →
      9 / 50 < 1 - dot u w

/-- `l:threeframes`, lines 382–384: cancel the common rotation; exchange the
two labels when the exponent difference is negative. The witness exponent
is a natural number in [1,2], so no truncated subtraction is used. -/
def RelativeRotationStatement : Prop :=
  ∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 ∧ ∃ u v : IcoLetter,
      dot (frameVector i a) (frameVector j b) =
        dot (icoVector u) ((frameRotation ^ k).mulVec (icoVector v))

theorem rotation : RotationStatement := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [frameRotation, Matrix.mul_apply, Fin.sum_univ_succ]
  · norm_num [frameRotation, Matrix.det_fin_three]

theorem rotationPowers : RotationPowersStatement := by
  intro j
  fin_cases j
  · simp
  · simpa using rotation.1
  · change (frameRotation ^ 2).transpose * frameRotation ^ 2 = 1
    rw [pow_two, Matrix.transpose_mul]
    calc
      _ = frameRotation.transpose * ((frameRotation.transpose * frameRotation) * frameRotation) := by
        simp only [mul_assoc]
      _ = 1 := by rw [rotation.1, one_mul, rotation.1]

theorem frameScalars : FrameScalarsStatement := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)
  have hn := Real.sqrt_nonneg (5 : ℝ)
  have hlt : Real.sqrt 5 < 5 := by nlinarith
  have hb : 0 < frameBound := by unfold frameBound; positivity
  have hbsmall : frameBound < 9 / 50 := by unfold frameBound; linarith
  have hb1 : frameBound < 1 := by linarith
  have hd : 0 < 2 - frameBound := by linarith
  have hr : 0 < frameRatio := div_pos hb hd
  have hr1 : frameRatio < 1 := by
    unfold frameRatio
    exact (div_lt_one hd).2 (by linarith)
  have he : 0 < frameEnergy := by unfold frameEnergy; positivity
  have he1 : frameEnergy ≤ 1 := by
    have hp : frameRatio ^ 4 ≤ 1 := pow_le_one₀ hr.le hr1.le
    unfold frameEnergy
    linarith
  exact ⟨hb, hb1, hbsmall, hr, hr1, he, he1⟩

end AKLT.Blueprint.Q
