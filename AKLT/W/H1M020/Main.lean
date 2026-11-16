import AKLT.Blueprint.H1.NodesPauli

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.H1M020

private theorem invertPolynomial_monomial_support (I : Finset (Fin 20))
    (d : (Fin 20 × Fin 3) →₀ ℕ) (c : ℚ) :
    (invertPolynomial I (MvPolynomial.monomial d c)).support ⊆ {d} := by
  classical
  rw [invertPolynomial, MvPolynomial.eval₂Hom_monomial]
  simp only [Finsupp.prod]
  -- The variable part of the product is exactly the monomial with exponent `d`.
  have hvars :
      (∏ v ∈ d.support, (MvPolynomial.X v : MvPolynomial (Fin 20 × Fin 3) ℚ) ^ d v) =
        MvPolynomial.monomial d 1 := by
    simp
  have hsign : ∀ v : Fin 20 × Fin 3,
      (if v.1 ∈ I then (-1 : MvPolynomial (Fin 20 × Fin 3) ℚ) else 1) =
        MvPolynomial.C (if v.1 ∈ I then (-1 : ℚ) else 1) := by
    intro v
    split_ifs <;> simp
  simp_rw [hsign]
  -- Every transformed monomial is only rescaled, so its support is at `d`.
  rw [show (∏ v ∈ d.support,
      (MvPolynomial.C (if v.1 ∈ I then (-1 : ℚ) else 1) * MvPolynomial.X v) ^ d v) =
      (MvPolynomial.C (∏ v ∈ d.support, (if v.1 ∈ I then (-1 : ℚ) else 1) ^ d v)) *
        MvPolynomial.monomial d 1 by
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib, hvars]
        simp_rw [← map_pow]
        rw [← map_prod]
        ]
  simp only [MvPolynomial.C_mul']
  exact MvPolynomial.support_smul.trans
    (MvPolynomial.support_smul.trans MvPolynomial.support_monomial_subset)

private theorem invertPolynomial_support_subset (I : Finset (Fin 20))
    (p : AKLT.Blueprint.H1.VectorPolynomial) : (invertPolynomial I p).support ⊆ p.support := by
  classical
  have hinv : invertPolynomial I p =
      ∑ d ∈ p.support, invertPolynomial I (MvPolynomial.monomial d (p.coeff d)) := by
    calc
      invertPolynomial I p =
          MvPolynomial.eval₂Hom MvPolynomial.C
            (fun v => (if v.1 ∈ I then (-1 : MvPolynomial (Fin 20 × Fin 3) ℚ) else 1) *
              MvPolynomial.X v) p := rfl
      _ = MvPolynomial.eval₂Hom MvPolynomial.C
            (fun v => (if v.1 ∈ I then (-1 : MvPolynomial (Fin 20 × Fin 3) ℚ) else 1) *
              MvPolynomial.X v)
            (∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d)) :=
        congrArg _ p.as_sum
      _ = _ := by
        change MvPolynomial.eval₂Hom MvPolynomial.C
            (fun v => (if v.1 ∈ I then (-1 : MvPolynomial (Fin 20 × Fin 3) ℚ) else 1) *
              MvPolynomial.X v)
            (∑ d ∈ p.support, MvPolynomial.monomial d (p.coeff d)) =
          ∑ d ∈ p.support,
            MvPolynomial.eval₂Hom MvPolynomial.C
              (fun v => (if v.1 ∈ I then (-1 : MvPolynomial (Fin 20 × Fin 3) ℚ) else 1) *
                MvPolynomial.X v) (MvPolynomial.monomial d (p.coeff d))
        exact map_sum _ _ _
  rw [hinv]
  intro m hm
  have hm' : m ∈ p.support.biUnion fun d =>
      (invertPolynomial I (MvPolynomial.monomial d (p.coeff d))).support :=
    MvPolynomial.support_sum hm
  simp only [Finset.mem_biUnion] at hm'
  obtain ⟨d, hd, hm⟩ := hm'
  have heq : m = d := by
    simpa using (invertPolynomial_monomial_support I d (p.coeff d) hm)
  simpa [heq] using hd

theorem main : AKLT.Blueprint.H1.InversionPolynomialStatement := by
  classical
  intro J I p hp hs
  have hsup := invertPolynomial_support_subset I p
  refine ⟨?_, ?_, ?_⟩
  · intro m hm j
    exact hp m (hsup hm) j
  · intro m hm j hj k
    exact hs m (hsup hm) j hj k
  · intro u
    let ev : MvPolynomial (Fin 20 × Fin 3) ℚ →+* ℝ :=
      MvPolynomial.eval₂Hom (Rat.castHom ℝ)
        (fun v => AKLT.Defs.invertVectors I u v.1 v.2)
    have hcomp : ev.comp MvPolynomial.C = Rat.castHom ℝ := by
      ext q
      simp [ev]
    have hvar : ∀ v : Fin 20 × Fin 3,
        ev ((if v.1 ∈ I then (-1 : MvPolynomial (Fin 20 × Fin 3) ℚ) else 1) *
          MvPolynomial.X v) = u v.1 v.2 := by
      intro v
      by_cases h : v.1 ∈ I <;> simp [ev, AKLT.Defs.invertVectors, h]
    change ev (MvPolynomial.eval₂Hom MvPolynomial.C
      (fun v => (if v.1 ∈ I then (-1 : MvPolynomial (Fin 20 × Fin 3) ℚ) else 1) *
        MvPolynomial.X v) p) =
      MvPolynomial.eval₂Hom (Rat.castHom ℝ) (fun v => u v.1 v.2) p
    rw [MvPolynomial.map_eval₂Hom, hcomp]
    apply congrArg (fun f : (Fin 20 × Fin 3) → ℝ =>
      MvPolynomial.eval₂Hom (Rat.castHom ℝ) f p)
    exact funext hvar

end AKLT.W.H1M020
