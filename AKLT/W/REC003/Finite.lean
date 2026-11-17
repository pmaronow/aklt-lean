module
public import AKLT.Defs.Domain

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC003

/-- Split a finite spin assignment into its value at one site and its restriction. -/
def splitSpins (V : Finset Plane) (y : Plane) (hy : y ∈ V) :
    (V → SpinLetter) ≃ SpinLetter × (V.erase y → SpinLetter) where
  toFun n := (n ⟨y, hy⟩, fun x => n ⟨x, Finset.mem_of_mem_erase x.property⟩)
  invFun p x := if h : x.val = y then p.1
    else p.2 ⟨x, Finset.mem_erase.mpr ⟨h, x.property⟩⟩
  left_inv n := by
    funext x
    dsimp
    split_ifs with h
    · congr 1
      exact Subtype.ext h.symm
    · rfl
  right_inv p := by
    rcases p with ⟨j, n⟩
    apply Prod.ext
    · simp
    · funext x
      simp [Finset.ne_of_mem_erase x.property]

def extendSpins (V : Finset Plane) (n : V → SpinLetter) (x : Plane) : Vec3 :=
  if h : x ∈ V then spinVector (n ⟨x, h⟩) else 0

theorem extend_split (V : Finset Plane) (y : Plane) (hy : y ∈ V)
    (j : SpinLetter) (n : V.erase y → SpinLetter) :
    extendSpins V ((splitSpins V y hy).symm (j, n)) =
      Function.update (extendSpins (V.erase y) n) y (spinVector j) := by
  funext x
  by_cases hxy : x = y
  · subst x
    simp [extendSpins, hy, splitSpins]
  · by_cases hx : x ∈ V
    · have hxe : x ∈ V.erase y := Finset.mem_erase.mpr ⟨hxy, hx⟩
      simp [extendSpins, hx, hxe, hxy, splitSpins, Function.update_of_ne]
    · have hxe : x ∉ V.erase y := fun h => hx (Finset.mem_of_mem_erase h)
      simp [extendSpins, hx, hxe, hxy, Function.update_of_ne]

theorem prod_split (V : Finset Plane) (y : Plane) (hy : y ∈ V)
    (s : Plane → Status) (j : SpinLetter) (n : V.erase y → SpinLetter) :
    (∏ x : V, spinWeight (s x) ((splitSpins V y hy).symm (j, n) x)) =
      spinWeight (s y) j * ∏ x : V.erase y, spinWeight (s x) (n x) := by
  classical
  rw [Fintype.prod_eq_mul_prod_compl ⟨y, hy⟩]
  simp only [splitSpins, Equiv.coe_fn_symm_mk, ↓reduceDIte]
  congr 1
  rw [← Finset.prod_attach]
  let e : ↥({⟨y, hy⟩}ᶜ : Finset V) ≃ ↥(V.erase y) :=
    { toFun := fun x => ⟨x.val.val, Finset.mem_erase.mpr
        ⟨by simpa [Subtype.ext_iff] using (Finset.mem_compl.mp x.property),
          x.val.property⟩⟩
      invFun := fun x => ⟨⟨x.val, Finset.mem_of_mem_erase x.property⟩,
        by simp [Subtype.ext_iff, Finset.ne_of_mem_erase x.property]⟩
      left_inv := by intro x; rfl
      right_inv := by intro x; rfl }
  apply Fintype.prod_equiv e
  intro x
  have hxy : x.val.val ≠ y := by
    simpa only [Finset.mem_singleton, Subtype.ext_iff] using
      (Finset.mem_compl.mp x.property)
  simp [hxy, e]

/-- Fubini at one active site, with no positivity premise and including empty complements. -/
theorem sum_site (V : Finset Plane) (y : Plane) (hy : y ∈ V)
    (s : Plane → Status) (H : (Plane → Vec3) → ℝ) :
    (∑ n : V → SpinLetter, (∏ x : V, spinWeight (s x) (n x)) * H (extendSpins V n)) =
      ∑ n : V.erase y → SpinLetter, (∏ x : V.erase y, spinWeight (s x) (n x)) *
        siteFunctional (s y) (fun v => H (Function.update (extendSpins (V.erase y) n) y v)) := by
  classical
  rw [← (splitSpins V y hy).symm.sum_comp]
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  simp only [prod_split, extend_split, siteFunctional, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

def spinIntegral (V : Finset Plane) (s : Plane → Status)
    (H : (Plane → Vec3) → ℝ) : ℝ :=
  ∑ n : V → SpinLetter, (∏ x : V, spinWeight (s x) (n x)) * H (extendSpins V n)

theorem spinIntegral_status (V : Finset Plane) (s t : Plane → Status)
    (hst : ∀ x ∈ V, s x = t x) (H : (Plane → Vec3) → ℝ) :
    spinIntegral V s H = spinIntegral V t H := by
  unfold spinIntegral
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  rw [hst x x.property]

theorem spinIntegral_site (V : Finset Plane) (y : Plane) (hy : y ∈ V)
    (s : Plane → Status) (H : (Plane → Vec3) → ℝ) :
    spinIntegral V s H = spinIntegral (V.erase y) s
      (fun m => siteFunctional (s y) (fun v => H (Function.update m y v))) :=
  sum_site V y hy s H

end AKLT.W.REC003
