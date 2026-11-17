import AKLT.W.REC016.Free
import AKLT.W.REC016.Geometry

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC016

theorem bond_present {G : Finset Plane} {D : Network G} (e : D.bonds) :
    D.Present e.val.1 e.val.2 := (Finset.mem_filter.mp e.property).2

@[simp] theorem bond_left_active {G : Finset Plane} {D : Network G} (e : D.bonds) :
    e.val.1 ∈ D.active := (bond_present e).1

@[simp] theorem bond_right_active {G : Finset Plane} {D : Network G} (e : D.bonds) :
    e.val.2 ∈ D.active := (bond_present e).2.1

def bondLeft {G : Finset Plane} (D : Network G) (e : D.bonds) : D.active :=
  ⟨e.val.1, bond_left_active e⟩

def bondRight {G : Finset Plane} (D : Network G) (e : D.bonds) : D.active :=
  ⟨e.val.2, bond_right_active e⟩

theorem bond_positive {G : Finset Plane} {D : Network G} (e : D.bonds) :
    e.val.2.1 + e.val.2.2 = e.val.1.1 + e.val.1.2 + 1 := by
  have he := (Finset.mem_filter.mp e.property).1
  obtain ⟨x, _, hz⟩ := Finset.mem_biUnion.mp he
  obtain ⟨z, hz, heq⟩ := Finset.mem_image.mp hz
  have hpos := (Finset.mem_inter.mp hz).1
  rw [← heq]
  rcases Finset.mem_insert.mp hpos with h | h
  · rw [h]
    dsimp
    ring
  · have h := Finset.mem_singleton.mp h
    rw [h]
    dsimp
    ring

theorem bond_no_loop {G : Finset Plane} {D : Network G} (e : D.bonds) :
    bondLeft D e ≠ bondRight D e := by
  intro h
  have he := congrArg Subtype.val h
  have hp := bond_positive e
  change e.val.1 = e.val.2 at he
  rw [he] at hp
  omega

def dotPoly {α : Type*} (x y : α) : MvPolynomial (α × Fin 3) ℕ :=
  ∑ i, MvPolynomial.X (x, i) * MvPolynomial.X (y, i)

def freePoly {G : Finset Plane} (D : Network G) : MvPolynomial (D.active × Fin 3) ℕ :=
  ∏ e : D.bonds, (1 + dotPoly (bondLeft D e) (bondRight D e))

set_option maxHeartbeats 1200000 in
theorem free_pair_nonneg {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (x y : D.active) :
    0 ≤ D.partition τ false (fun v => dot (v x) (v y)) := by
  classical
  have h := polynomial_functional_nonneg (fun z : D.active => D.status z)
    (freePoly D * dotPoly x y)
  convert h using 1
  simp only [Network.partition, productFunctional, Bool.false_eq_true, false_and,
    ite_false, Finset.prod_const_one, mul_one]
  apply Finset.sum_congr (by ext; simp)
  intro σ _
  have he : ∀ e : D.bonds,
      D.spins σ e.val.1 = spinVector (σ (bondLeft D e)) ∧
      D.spins σ e.val.2 = spinVector (σ (bondRight D e)) := by
    intro e
    simp [Network.spins, bondLeft, bondRight]
  simp only [freePoly, dotPoly, MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod,
    MvPolynomial.eval₂_add, MvPolynomial.eval₂_one, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_X]
  have hp : (∏ e ∈ D.bonds, (1 + dot (D.spins σ e.1) (D.spins σ e.2))) =
      ∏ e : D.bonds, (1 + dot (spinVector (σ (bondLeft D e)))
        (spinVector (σ (bondRight D e)))) := by
    rw [← Finset.prod_coe_sort]
    apply Finset.prod_congr rfl
    intro e _
    rw [(he e).1, (he e).2]
  rw [hp]
  simp [Network.spins, x.property, y.property, dot, mul_comm, mul_left_comm, mul_assoc]

#print axioms free_pair_nonneg

end AKLT.W.REC016
