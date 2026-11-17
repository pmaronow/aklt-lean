module
public import AKLT.W.Q061.Product
public import AKLT.W.Q061.Projections

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.Q061

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {S : ι → Type*} [∀ x, Fintype (S x)]

omit [∀ x, Fintype (S x)] in
theorem constant_of_update_invariant (g : ((x : ι) → S x) → ℂ)
    (hg : ∀ x σ a, g (Function.update σ x a) = g σ)
    (σ τ : (x : ι) → S x) : g σ = g τ := by
  classical
  have patch (U : Finset ι) : g (fun y => if y ∈ U then τ y else σ y) = g σ := by
    induction U using Finset.induction_on with
    | empty => simp
    | @insert x U hx ih =>
      have he : (fun y => if y ∈ insert x U then τ y else σ y) =
          Function.update (fun y => if y ∈ U then τ y else σ y) x (τ x) := by
        ext y
        by_cases hy : y = x
        · subst y; simp
        · simp [hy, Function.update_of_ne]
      rw [he, hg, ih]
  simpa using (patch Finset.univ).symm

theorem mean_averageList (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) (l : List ι)
    (f : ((x : ι) → S x) → ℂ) :
    complexMean (productMass p) (averageList (siteAverage p) l f) =
      complexMean (productMass p) f := by
  induction l generalizing f with
  | nil => rfl
  | cons x l ih =>
    change complexMean (productMass p)
      (averageList (siteAverage p) l (siteAverage p x f)) = _
    rw [ih, mean_siteAverage p hp]

theorem averageList_univ (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) (f : ((x : ι) → S x) → ℂ) :
    averageList (siteAverage p) Finset.univ.toList f =
      fun _ => complexMean (productMass p) f := by
  classical
  let g := averageList (siteAverage p) Finset.univ.toList f
  have fixed (x : ι) : siteAverage p x g = g :=
    averageList_fixed (siteAverage p) (siteAverage_commute p) (siteAverage_idem p hp)
      x Finset.univ.toList (by simp) f
  have invariant (x : ι) (σ : (x : ι) → S x) (a : S x) :
      g (Function.update σ x a) = g σ := by
    calc
      _ = siteAverage p x g (Function.update σ x a) := congrFun (fixed x).symm _
      _ = siteAverage p x g σ := siteAverage_update p x g σ a
      _ = g σ := congrFun (fixed x) σ
  have constant := constant_of_update_invariant g invariant
  ext σ
  have hmean : complexMean (productMass p) g = g σ := by
    calc
      _ = complexMean (productMass p) (fun _ => g σ) := by
        congr 1
        ext τ
        exact constant τ σ
      _ = g σ := mean_const p hp _
  exact hmean.symm.trans (mean_averageList p hp Finset.univ.toList f)

/-- Complex finite-product Efron--Stein, with one term for each site. -/
theorem product_tensorization (p : (x : ι) → Weight (S x))
    (hp : ∀ x, PositiveProbability (p x)) (f : ((x : ι) → S x) → ℂ) :
    variance (productMass p) f ≤ ∑ x, energy p (f - siteAverage p x f) := by
  classical
  let c : ((x : ι) → S x) → ℂ := fun _ => complexMean (productMass p) f
  have centered : complexMean (productMass p) (f - c) = 0 := by
    rw [mean_sub, mean_const p hp]
    exact sub_self _
  have full : averageList (siteAverage p) Finset.univ.toList (f - c) = 0 := by
    rw [averageList_univ p hp, centered]
    rfl
  have diff (x : ι) : (f - c) - siteAverage p x (f - c) = f - siteAverage p x f := by
    rw [siteAverage_sub, siteAverage_const p hp]
    ext σ
    simp only [Pi.sub_apply]
    ring
  have h := projection_tensorization (siteAverage p) (energy p)
    (energy_nonneg p hp) (energy_split p hp) (siteAverage_commute p) (siteAverage_sub p)
    Finset.univ.toList (f - c)
  rw [full] at h
  simp_rw [diff] at h
  simpa [energy, variance, c] using h

end AKLT.W.Q061
