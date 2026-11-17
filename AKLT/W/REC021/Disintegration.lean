module
public import AKLT.W.REC021.Fibers

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC021

theorem productFunctional_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : ι → Status) (f : (ι → Vec3) → ℝ) :
    productFunctional s f =
      ∑ n : ι → SpinLetter, (∏ x, spinWeight (s x) (n x)) * f (fun x => spinVector (n x)) := by
  classical
  unfold productFunctional
  congr 1
  ext n
  simp

theorem productFunctional_separated {ι : Type*} [Fintype ι] (s : ι → Status)
    (f : ι → Vec3 → ℝ) :
    productFunctional s (fun n => ∏ i, f i (n i)) = ∏ i, siteFunctional (s i) (f i) := by
  classical
  simp only [productFunctional, siteFunctional]
  simp_rw [← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i (j : SpinLetter) =>
    spinWeight (s i) j * f i (spinVector j))).symm

theorem productFunctional_add {ι : Type*} [Fintype ι] (s : ι → Status)
    (f g : (ι → Vec3) → ℝ) :
    productFunctional s (fun n => f n + g n) = productFunctional s f + productFunctional s g := by
  classical
  simp [productFunctional, mul_add, Finset.sum_add_distrib]

theorem productFunctional_sum {ι κ : Type*} [Fintype ι] [Fintype κ] (s : ι → Status)
    (f : κ → (ι → Vec3) → ℝ) :
    productFunctional s (fun n => ∑ k, f k n) = ∑ k, productFunctional s (f k) := by
  classical
  simp only [productFunctional, Finset.mul_sum]
  exact Finset.sum_comm

def CubicFiber.localFactor (F : CubicFiber) (i : Fin 3) (n : Vec3) : ℝ :=
  cubicWeight (F.field i 0) (F.field i 1) (F.field i 2) n

def CubicFiber.weight (F : CubicFiber) (σ : Fin 3 → SpinLetter) : ℝ :=
  F.coefficient * ((∏ i, spinWeight (F.status i) (σ i)) *
    ∏ i, F.localFactor i (spinVector (σ i)))

theorem CubicFiber.sum_weight (F : CubicFiber) : ∑ σ, F.weight σ = F.mass := by
  change (∑ σ, F.coefficient * _) = _
  rw [← Finset.mul_sum]
  have h := productFunctional_separated F.status F.localFactor
  rw [productFunctional_eq_sum] at h
  rw [h]
  simp [CubicFiber.mass, CubicFiber.A, cubicA, CubicFiber.localFactor, Fin.prod_univ_three]
  left
  rfl

theorem CubicFiber.sum_weight_pairs (F : CubicFiber) :
    (∑ σ, F.weight σ *
      (dot (spinVector (σ 0)) (spinVector (σ 1)) +
       dot (spinVector (σ 0)) (spinVector (σ 2)) +
       dot (spinVector (σ 1)) (spinVector (σ 2)))) = F.pairMass := by
  let W := F.localFactor
  let T (k : Fin 3) (n : Fin 3 → Vec3) : ℝ :=
    (∏ i : Fin 3, ![(fun v : Vec3 => W 0 v * v k),
      (fun v : Vec3 => W 1 v * v k), W 2] i (n i)) +
    (∏ i : Fin 3, ![(fun v : Vec3 => W 0 v * v k), W 1,
      (fun v : Vec3 => W 2 v * v k)] i (n i)) +
    (∏ i : Fin 3, ![W 0, (fun v : Vec3 => W 1 v * v k),
      (fun v : Vec3 => W 2 v * v k)] i (n i))
  have he (n : Fin 3 → Vec3) :
      (∏ i, W i (n i)) * (dot (n 0) (n 1) + dot (n 0) (n 2) + dot (n 1) (n 2)) =
        ∑ k, T k n := by
    simp [T, dot, Fin.sum_univ_three, Fin.prod_univ_three]
    ring
  calc
    _ = F.coefficient * productFunctional F.status (fun n =>
        (∏ i, W i (n i)) * (dot (n 0) (n 1) + dot (n 0) (n 2) + dot (n 1) (n 2))) := by
      simp only [CubicFiber.weight, productFunctional_eq_sum, Finset.mul_sum, W]
      apply Finset.sum_congr rfl
      intro σ _
      ring
    _ = F.coefficient * ∑ k, productFunctional F.status (T k) := by
      simp_rw [he]
      rw [productFunctional_sum]
    _ = F.pairMass := by
      simp_rw [T, productFunctional_add, productFunctional_separated]
      apply congrArg (fun v : ℝ => F.coefficient * v)
      simp [CubicFiber.pairMass, CubicFiber.B, CubicFiber.A, cubicB, cubicA,
        CubicFiber.localFactor, W, dot, Fin.prod_univ_three, Fin.sum_univ_three, mul_comm]
      simp only [show ∀ i : Fin 3, F.localFactor i =
        cubicWeight (F.field i 0) (F.field i 1) (F.field i 2) from fun _ => rfl]
      ring

/-- Resumming after replacing one coordinate multiplies a full sum by the
alphabet's cardinality. This proof permits zero weights. -/
theorem sum_update {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (x : ι) (f : (ι → Ω) → ℝ) :
    (∑ σ, ∑ j : Ω, f (Function.update σ x j)) = (Fintype.card Ω : ℝ) * ∑ σ, f σ := by
  let e : ((ι → Ω) × Ω) ≃ ((ι → Ω) × Ω) :=
    { toFun := fun p => (Function.update p.1 x p.2, p.1 x)
      invFun := fun p => (Function.update p.1 x p.2, p.1 x)
      left_inv := by intro p; ext i <;> simp [Function.update_apply]; split_ifs <;> simp_all
      right_inv := by intro p; ext i <;> simp [Function.update_apply]; split_ifs <;> simp_all }
  have h := Fintype.sum_equiv e
    (fun p => f (Function.update p.1 x p.2)) (fun p => f p.1) (fun _ => rfl)
  simpa [Fintype.sum_prod_type, ← Finset.mul_sum] using h

theorem sum_fin3_function {Ω : Type*} [Fintype Ω] (f : (Fin 3 → Ω) → ℝ) :
    (∑ j, f j) = ∑ a : Ω, ∑ b : Ω, ∑ c : Ω, f ![a, b, c] := by
  let e : (Fin 3 → Ω) ≃ Ω × Ω × Ω :=
    { toFun := fun j => (j 0, j 1, j 2)
      invFun := fun p => ![p.1, p.2.1, p.2.2]
      left_inv := by intro j; funext i; fin_cases i <;> rfl
      right_inv := by intro p; rfl }
  have h := Fintype.sum_equiv e f (fun p => f ![p.1, p.2.1, p.2.2])
    (by intro j; congr 1; funext i; fin_cases i <;> rfl)
  simpa [Fintype.sum_prod_type] using h

def blockUpdate {ι Ω : Type*} [DecidableEq ι] (x : Fin 3 → ι)
    (σ : ι → Ω) (j : Fin 3 → Ω) : ι → Ω :=
  Function.update (Function.update (Function.update σ (x 0) (j 0)) (x 1) (j 1)) (x 2) (j 2)

theorem sum_blockUpdate {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]
    (x : Fin 3 → ι) (f : (ι → Ω) → ℝ) :
    (∑ σ, ∑ j : Fin 3 → Ω, f (blockUpdate x σ j)) =
      (Fintype.card Ω : ℝ)^3 * ∑ σ, f σ := by
  simp_rw [sum_fin3_function]
  change (∑ σ, ∑ a : Ω, ∑ b : Ω, ∑ c : Ω,
    f (Function.update (Function.update (Function.update σ (x 0) a) (x 1) b) (x 2) c)) = _
  rw [sum_update (x 0) (fun σ => ∑ b : Ω, ∑ c : Ω,
    f (Function.update (Function.update σ (x 1) b) (x 2) c))]
  rw [sum_update (x 1) (fun σ => ∑ c : Ω, f (Function.update σ (x 2) c)),
    sum_update (x 2) f]
  ring

#print axioms productFunctional_separated
#print axioms productFunctional_eq_sum
#print axioms productFunctional_add
#print axioms productFunctional_sum
#print axioms CubicFiber.sum_weight
#print axioms CubicFiber.sum_weight_pairs
#print axioms sum_update
#print axioms sum_fin3_function
#print axioms sum_blockUpdate

end AKLT.W.REC021
