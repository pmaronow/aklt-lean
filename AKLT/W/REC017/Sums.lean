import AKLT.W.REC017.Quadrature

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC017

def letters {V : Finset Plane} (n : V → SpinLetter) (x : Plane) : SpinLetter :=
  if h : x ∈ V then n ⟨x, h⟩ else none

def field {V : Finset Plane} (n : V → SpinLetter) (x : Plane) : Vec3 :=
  spinVector (letters n x)

@[simp] theorem letters_mem {V : Finset Plane} (n : V → SpinLetter) (x : V) :
    letters n x = n x := by simp [letters]

@[simp] theorem field_mem {V : Finset Plane} (n : V → SpinLetter) (x : V) :
    field n x = spinVector (n x) := by simp [field]

def quadrature (V : Finset Plane) (s : Plane → Status)
    (F : (Plane → Vec3) → ℝ) : ℝ :=
  ∑ n : V → SpinLetter, (∏ x ∈ V, spinWeight (s x) (letters n x)) * F (field n)

def insertEquiv (V : Finset Plane) (y : Plane) (h : y ∉ V) :
    (↥(insert y V) → SpinLetter) ≃ SpinLetter × (V → SpinLetter) where
  toFun n := (n ⟨y, Finset.mem_insert_self _ _⟩,
    fun x => n ⟨x, Finset.mem_insert_of_mem x.property⟩)
  invFun p x := if hx : x.val = y then p.1 else
    p.2 ⟨x, Finset.mem_of_mem_insert_of_ne x.property hx⟩
  left_inv n := by
    funext x
    dsimp
    split_ifs with hx
    · congr 1
      exact Subtype.ext hx.symm
    · rfl
  right_inv p := by
    rcases p with ⟨a, n⟩
    apply Prod.ext
    · simp
    · funext x
      have hx : x.val ≠ y := fun he => h (he ▸ x.property)
      simp [hx]

theorem letters_insert (V : Finset Plane) (y : Plane) (h : y ∉ V)
    (a : SpinLetter) (n : V → SpinLetter) :
    letters ((insertEquiv V y h).symm (a, n)) = Function.update (letters n) y a := by
  funext x
  by_cases hx : x = y
  · subst x
    simp [letters, insertEquiv]
  · by_cases hv : x ∈ V <;> simp [letters, insertEquiv, hx, hv]

theorem field_insert (V : Finset Plane) (y : Plane) (h : y ∉ V)
    (a : SpinLetter) (n : V → SpinLetter) :
    field ((insertEquiv V y h).symm (a, n)) =
      Function.update (field n) y (spinVector a) := by
  funext x
  simp only [field, letters_insert]
  by_cases hx : x = y <;> simp [hx, field]

theorem quadrature_insert (V : Finset Plane) (y : Plane) (h : y ∉ V)
    (s : Plane → Status) (F : (Plane → Vec3) → ℝ) :
    quadrature (insert y V) s F =
      quadrature V s (fun n => siteFunctional (s y)
        (fun v => F (Function.update n y v))) := by
  classical
  unfold quadrature
  rw [← (insertEquiv V y h).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  rw [siteFunctional, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [field_insert, letters_insert, Finset.prod_insert h]
  simp only [Function.update_self]
  have hp : (∏ x ∈ V, spinWeight (s x) (Function.update (letters n) y a x)) =
      ∏ x ∈ V, spinWeight (s x) (letters n x) := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [Function.update_of_ne (show x ≠ y from fun he => h (he ▸ hx))]
  rw [hp]
  ring

theorem quadrature_status_congr (V : Finset Plane) (s t : Plane → Status)
    (h : ∀ x ∈ V, s x = t x) (F : (Plane → Vec3) → ℝ) :
    quadrature V s F = quadrature V t F := by
  unfold quadrature
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  exact Finset.prod_congr rfl fun x hx => by rw [h x hx]

end AKLT.W.REC017
