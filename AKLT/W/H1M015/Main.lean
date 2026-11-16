import AKLT.Blueprint.H1.NodesPassage

noncomputable section
open AKLT.Blueprint.H1

namespace AKLT.W.H1M015

theorem main : AKLT.Blueprint.H1.ContractionSupportStatement := by
  intro V s p J hSupported
  classical
  intro a ha j hj k
  let projectExponent : (AKLT.Defs.LocalVariable →₀ ℕ) → (Fin 20 × Fin 3 →₀ ℕ) :=
    fun m => Finsupp.comapDomain Sum.inr m (by
      intro x _ y _ h
      exact Sum.inr.inj h)
  have hsum :
      (AKLT.Defs.contractSpins V s p).support ⊆
        p.support.biUnion (fun m =>
          (MvPolynomial.monomial (projectExponent m)
            (p.coeff m * ∏ x ∈ V,
              AKLT.Defs.rationalStatusMoment (s x)
                (fun k => m (.inl (x, k))))).support) := by
    unfold AKLT.Defs.contractSpins
    exact MvPolynomial.support_sum
  have ha' := hsum ha
  rcases Finset.mem_biUnion.mp ha' with ⟨m, hm, hterm⟩
  have hterm' : a ∈ {projectExponent m} :=
    MvPolynomial.support_monomial_subset hterm
  have hae : a = projectExponent m := by simpa using hterm'
  rw [hae]
  change m (Sum.inr (j, k)) = 0
  exact hSupported m hm j hj k

end AKLT.W.H1M015

#print axioms AKLT.W.H1M015.main
