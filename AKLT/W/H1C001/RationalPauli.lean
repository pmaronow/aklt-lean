module
public import AKLT.Cert.H1.Production.TopLeaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1C001

/-- Rationals obtained by casting integers. -/
def integerRationals : Subring ℚ := (Int.castRingHom ℚ).range

private def IntegralPair (x : ℚ × ℚ) : Prop :=
  x.1 ∈ integerRationals ∧ x.2 ∈ integerRationals

private lemma rationalPauli_integral (a : Fin 4) (i j : Fin 2) :
    IntegralPair (rationalPauli a i j) := by
  unfold rationalPauli IntegralPair
  split_ifs <;>
    constructor <;>
    first
    | exact integerRationals.zero_mem
    | exact integerRationals.one_mem
    | exact integerRationals.neg_mem integerRationals.one_mem

private lemma ratComplexMul_integral {x y : ℚ × ℚ}
    (hx : IntegralPair x) (hy : IntegralPair y) : IntegralPair (ratComplexMul x y) := by
  exact ⟨integerRationals.sub_mem (integerRationals.mul_mem hx.1 hy.1)
      (integerRationals.mul_mem hx.2 hy.2),
    integerRationals.add_mem (integerRationals.mul_mem hx.1 hy.2)
      (integerRationals.mul_mem hx.2 hy.1)⟩

private lemma ratComplexFold_integral (l : List (ℚ × ℚ)) (z : ℚ × ℚ)
    (hz : IntegralPair z) (hl : ∀ x ∈ l, IntegralPair x) :
    IntegralPair (l.foldl ratComplexMul z) := by
  induction l generalizing z with
  | nil => exact hz
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact ih _ (ratComplexMul_integral hz (hl x (List.mem_cons_self)))
        (fun y hy => hl y (List.mem_cons_of_mem x hy))

private lemma rationalPauliProduct_integral (J : Finset (Fin 20))
    (a : J → Fin 4) (σ τ : J → Fin 2) :
    (((Finset.univ : Finset J).toList.map fun j =>
      rationalPauli (a j) (σ j) (τ j)).foldl ratComplexMul (1, 0)).1 ∈ integerRationals := by
  apply (ratComplexFold_integral _ _
    ⟨integerRationals.one_mem, integerRationals.zero_mem⟩ ?_).1
  intro x hx
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hx
  exact rationalPauli_integral (a j) (σ j) (τ j)

private lemma rationalOperatorEntry_integral (J : Finset (Fin 20))
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ)
    (hp : ∀ m, p.coeff m ∈ integerRationals) (σ τ : J → Fin 2) :
    rationalOperatorEntry J p σ τ ∈ integerRationals := by
  unfold rationalOperatorEntry
  apply integerRationals.sum_mem
  intro a _
  exact integerRationals.mul_mem (hp _) (rationalPauliProduct_integral J a σ τ)

/-- Integer polynomial coefficients and integer basis coordinates give integer entries. -/
theorem rationalSectorEntry_integral (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p : MvPolynomial (Fin 20 × Fin 3) ℚ)
    (hp : ∀ m, p.coeff m ∈ integerRationals) (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε p a b ∈ integerRationals := by
  unfold rationalSectorEntry
  apply integerRationals.sum_mem
  intro σ _
  apply integerRationals.sum_mem
  intro τ _
  exact integerRationals.mul_mem
    (integerRationals.mul_mem (intCast_mem integerRationals _)
      (rationalOperatorEntry_integral _ p hp σ τ))
    (intCast_mem integerRationals _)

private def rationalConj (x : ℚ × ℚ) : ℚ × ℚ := (x.1, -x.2)

private lemma rationalConj_mul (x y : ℚ × ℚ) :
    rationalConj (ratComplexMul x y) = ratComplexMul (rationalConj x) (rationalConj y) := by
  apply Prod.ext <;> dsimp [rationalConj, ratComplexMul] <;> ring

private lemma rationalPauli_transpose (a : Fin 4) (i j : Fin 2) :
    rationalPauli a j i = rationalConj (rationalPauli a i j) := by
  fin_cases a <;> fin_cases i <;> fin_cases j <;>
    simp [rationalPauli, rationalConj]

private lemma rationalConj_fold (l : List (ℚ × ℚ)) (z : ℚ × ℚ) :
    rationalConj (l.foldl ratComplexMul z) =
      (l.map rationalConj).foldl ratComplexMul (rationalConj z) := by
  induction l generalizing z with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, ih, rationalConj_mul]

private lemma rationalPauliProduct_symm (J : Finset (Fin 20))
    (a : J → Fin 4) (σ τ : J → Fin 2) :
    (((Finset.univ : Finset J).toList.map fun j =>
      rationalPauli (a j) (σ j) (τ j)).foldl ratComplexMul (1, 0)).1 =
    (((Finset.univ : Finset J).toList.map fun j =>
      rationalPauli (a j) (τ j) (σ j)).foldl ratComplexMul (1, 0)).1 := by
  have hmap : ((Finset.univ : Finset J).toList.map fun j =>
      rationalPauli (a j) (τ j) (σ j)) =
    (((Finset.univ : Finset J).toList.map fun j =>
      rationalPauli (a j) (σ j) (τ j)).map rationalConj) := by
    rw [List.map_map]
    apply congrArg (fun f : J → ℚ × ℚ => (Finset.univ : Finset J).toList.map f)
    funext j
    exact rationalPauli_transpose (a j) (σ j) (τ j)
  rw [hmap]
  have h := congrArg Prod.fst (rationalConj_fold
    ((Finset.univ : Finset J).toList.map fun j =>
      rationalPauli (a j) (σ j) (τ j)) (1, 0))
  simpa only [rationalConj, Prod.fst, Prod.snd, neg_zero] using h

private lemma rationalOperatorEntry_symm (J : Finset (Fin 20))
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (σ τ : J → Fin 2) :
    rationalOperatorEntry J p σ τ = rationalOperatorEntry J p τ σ := by
  unfold rationalOperatorEntry
  apply Finset.sum_congr rfl
  intro a _
  rw [rationalPauliProduct_symm J a σ τ]

/-- Conjugate symmetry of rational Pauli entries makes their compressed real part symmetric. -/
theorem rationalSectorEntry_symm (π : PatternData) (r : Representation)
    (ε : ExchangeSigns π) (p : MvPolynomial (Fin 20 × Fin 3) ℚ)
    (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε p a b = rationalSectorEntry π r ε p b a := by
  unfold rationalSectorEntry
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro σ _
  rw [rationalOperatorEntry_symm _ p σ τ]
  ring

#print axioms rationalSectorEntry_integral
#print axioms rationalSectorEntry_symm

end AKLT.W.H1C001
