module
public import AKLT.W.REC082.PE.Moments
public import AKLT.W.REC082.PE.Factors

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC082.PE

private theorem product_enum (S : Finset Plane) (e : Fin (Fintype.card S) ≃ S)
    (f : Plane → ℝ) : (∏ i, f (e i).val) = ∏ x ∈ S, f x := by
  rw [Equiv.prod_comp e (fun x : S => f x.val)]
  exact Finset.prod_coe_sort S f

private theorem sum_enum (S : Finset Plane) (e : Fin (Fintype.card S) ≃ S)
    (f : Plane → ℝ) : (∑ i, f (e i).val) = ∑ x ∈ S, f x := by
  rw [Equiv.sum_comp e (fun x : S => f x.val)]
  exact Finset.sum_coe_sort S f

private theorem product_erase_enum (S : Finset Plane) (e : Fin (Fintype.card S) ≃ S)
    (f : Plane → ℝ) (i : Fin (Fintype.card S)) :
    (∏ j ∈ Finset.univ.erase i, f (e j).val) = ∏ x ∈ S.erase (e i).val, f x := by
  classical
  apply Finset.prod_bij (fun j _ => (e j).val)
  · intro j hj
    refine Finset.mem_erase.mpr ⟨?_, (e j).property⟩
    intro he
    exact (Finset.mem_erase.mp hj).1 (e.injective (Subtype.ext he))
  · intro j hj k hk he
    exact e.injective (Subtype.ext he)
  · intro x hx
    refine ⟨e.symm ⟨x, (Finset.mem_erase.mp hx).2⟩, ?_, ?_⟩
    · apply Finset.mem_erase.mpr
      refine ⟨?_, Finset.mem_univ _⟩
      intro he
      have hh := congrArg (fun j => (e j).val) he
      exact (Finset.mem_erase.mp hx).1 (by simpa using hh)
    · simp
  · intro j hj
    rfl

@[simp] theorem paddedSite_U (f : Vec3 → ℝ) :
    paddedSiteFunctional .U f = siteFunctional .U f := by
  simp [paddedSiteFunctional, paddedWeight, siteFunctional]

@[simp] theorem paddedSite_D (f : Vec3 → ℝ) :
    paddedSiteFunctional .D f = siteFunctional .D f := by
  simp [paddedSiteFunctional, paddedWeight, siteFunctional]

@[simp] theorem paddedSite_X (f : Vec3 → ℝ) : paddedSiteFunctional .X f = f 0 := by
  simp [paddedSiteFunctional, paddedWeight, Fintype.sum_option, spinVector]

/-- The local U expansion, reindexed by the actual present-neighbour finset. -/
theorem uMoment_finset (S : Finset Plane) (hS : S.card ≤ 3) (s : Plane → Vec3)
    (k : Fin 3) :
    paddedSiteFunctional .U (fun a => a k * ∏ o ∈ S, (1 + dot a (s o))) =
      (1 / 3 : ℝ) * ∑ o ∈ S, s o k *
        paddedSiteFunctional .D (fun a => ∏ p ∈ S.erase o, (1 + dot a (s p))) := by
  classical
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have hd (a : Vec3) : dot (Pi.single k 1) a = a k := by
    simp [dot, Pi.single_apply]
  have h := uStepMoment (Fintype.card S) (by simpa using hS)
    (Pi.single k 1) (fun i => s (e i).val)
  have hp (a : Vec3) := product_enum S e (fun o => 1 + dot a (s o))
  have he (a : Vec3) (i : Fin (Fintype.card S)) :=
    product_erase_enum S e (fun o => 1 + dot a (s o)) i
  simp_rw [hd, hp, he] at h
  rw [sum_enum S e (fun o => s o k *
    siteFunctional .D (fun a => ∏ p ∈ S.erase o, (1 + dot a (s p))))] at h
  simpa only [paddedSite_U, paddedSite_D] using h

/-- The D expansion, including an empty present-neighbour finset. -/
theorem dMoment_finset (S : Finset Plane) (hS : S.card ≤ 1) (s : Plane → Vec3)
    (k : Fin 3) :
    paddedSiteFunctional .D (fun a => a k * ∏ o ∈ S, (1 + dot a (s o))) =
      (1 / 5 : ℝ) * ∑ o ∈ S, s o k := by
  classical
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  have hd (a : Vec3) : dot (Pi.single k 1) a = a k := by
    simp [dot, Pi.single_apply]
  have h := dStepMoment (Fintype.card S) (by simpa using hS)
    (Pi.single k 1) (fun i => s (e i).val)
  have hp (a : Vec3) := product_enum S e (fun o => 1 + dot a (s o))
  simp_rw [hd, hp] at h
  rw [sum_enum S e (fun o => s o k)] at h
  simpa only [paddedSite_D] using h

/-- Pull a scalar independent of the integrated spin through its finite law. -/
theorem paddedSite_mul_const (s : Status) (f : Vec3 → ℝ) (c : ℝ) :
    paddedSiteFunctional s (fun a => f a * c) = paddedSiteFunctional s f * c := by
  simp only [paddedSiteFunctional, Finset.sum_mul, mul_assoc]

end AKLT.W.REC082.PE
