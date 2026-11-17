module
public import AKLT.Blueprint.H1.NodesV2Reduction

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M065

private def monomialTokenValue (m : (Fin 20 × Fin 3) →₀ ℕ)
    (u : Fin 20 → Vec3) (i : Fin 20) : ℝ :=
  ∏ k : Fin 3, u i k ^ m (i, k)

private theorem monomialSupportProduct_eq_tokenProduct
    (m : (Fin 20 × Fin 3) →₀ ℕ) (u : Fin 20 → Vec3) :
    (∏ v ∈ m.support, u v.1 v.2 ^ m v) = ∏ i : Fin 20, monomialTokenValue m u i := by
  change m.prod (fun v e => u v.1 v.2 ^ e) = _
  rw [Finsupp.prod_fintype]
  · rw [Fintype.prod_prod_type]
    rfl
  · intro v
    simp

private theorem monomialTokenValue_affine
    (m : (Fin 20 × Fin 3) →₀ ℕ) (j : Fin 20)
    (hm : (∑ k : Fin 3, m (j, k)) ≤ 1)
    (a b : Vec3) (t : ℝ) :
    monomialTokenValue m (fun _ => t • a + (1 - t) • b) j =
      t * monomialTokenValue m (fun _ => a) j +
        (1 - t) * monomialTokenValue m (fun _ => b) j := by
  have hsum : m (j, 0) + (m (j, 1) + m (j, 2)) ≤ 1 := by
    simpa [Fin.sum_univ_succ] using hm
  have h0 : m (j, 0) = 0 ∨ m (j, 0) = 1 := by omega
  have h1 : m (j, 1) = 0 ∨ m (j, 1) = 1 := by omega
  have h2 : m (j, 2) = 0 ∨ m (j, 2) = 1 := by omega
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;>
    rcases h2 with h2 | h2
  · simp [monomialTokenValue, Fin.prod_univ_three, h0, h1, h2]
  · simp [monomialTokenValue, Fin.prod_univ_three, h0, h1, h2]
  · simp [monomialTokenValue, Fin.prod_univ_three, h0, h1, h2]
  · have : False := by omega
    contradiction
  · simp [monomialTokenValue, Fin.prod_univ_three, h0, h1, h2]
  · have : False := by omega
    contradiction
  · have : False := by omega
    contradiction
  · have : False := by omega
    contradiction

private theorem monomialSupportProduct_affine
    (m : (Fin 20 × Fin 3) →₀ ℕ) (j : Fin 20)
    (hm : (∑ k : Fin 3, m (j, k)) ≤ 1)
    (u : Fin 20 → Vec3) (a b : Vec3) (t : ℝ) :
    (∏ v ∈ m.support,
        (Function.update u j (t • a + (1 - t) • b)) v.1 v.2 ^ m v) =
      t * (∏ v ∈ m.support, (Function.update u j a) v.1 v.2 ^ m v) +
        (1 - t) * (∏ v ∈ m.support, (Function.update u j b) v.1 v.2 ^ m v) := by
  rw [monomialSupportProduct_eq_tokenProduct, monomialSupportProduct_eq_tokenProduct,
    monomialSupportProduct_eq_tokenProduct]
  have hprod (x : Vec3) :
      (∏ i : Fin 20, monomialTokenValue m (Function.update u j x) i) =
        monomialTokenValue m (Function.update u j x) j *
          ∏ i ∈ ({j}ᶜ : Finset (Fin 20)), monomialTokenValue m (Function.update u j x) i := by
    simpa using (Fintype.prod_eq_mul_prod_compl j
      (fun i : Fin 20 => monomialTokenValue m (Function.update u j x) i))
  rw [hprod (t • a + (1 - t) • b), hprod a, hprod b]
  have hrest (x : Vec3) :
      (∏ i ∈ ({j}ᶜ : Finset (Fin 20)), monomialTokenValue m (Function.update u j x) i) =
        ∏ i ∈ ({j}ᶜ : Finset (Fin 20)), monomialTokenValue m u i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hij : i ≠ j := by simpa using hi
    simp [monomialTokenValue, hij]
  rw [hrest (t • a + (1 - t) • b), hrest a, hrest b]
  have hself (x : Vec3) :
      monomialTokenValue m (Function.update u j x) j = monomialTokenValue m (fun _ => x) j := by
    simp [monomialTokenValue]
  rw [hself, hself, hself, monomialTokenValue_affine m j hm a b t]
  ring

private theorem monomialTerm_affine
    (m : (Fin 20 × Fin 3) →₀ ℕ) (c : ℝ) (j : Fin 20)
    (hm : (∑ k : Fin 3, m (j, k)) ≤ 1)
    (u : Fin 20 → Vec3) (a b : Vec3) (t : ℝ) :
    c * (∏ v ∈ m.support,
        (Function.update u j (t • a + (1 - t) • b)) v.1 v.2 ^ m v) =
      t * (c * ∏ v ∈ m.support, (Function.update u j a) v.1 v.2 ^ m v) +
        (1 - t) * (c * ∏ v ∈ m.support, (Function.update u j b) v.1 v.2 ^ m v) := by
  rw [monomialSupportProduct_affine m j hm u a b t]
  ring

theorem main : AKLT.Blueprint.H1.AffineEvaluationStatementV2 := by
  intro p hp j u a b t
  simp only [evaluateRealPolynomial]
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, MvPolynomial.eval_eq]
  rw [Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  apply monomialTerm_affine
  exact hp m hm j

end AKLT.W.H1M065
