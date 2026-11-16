import AKLT.Blueprint.H1.NodesPassage

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1M014

theorem main : AKLT.Blueprint.H1.ContractionAffineStatement := by
  intro V s p hp m hm j
  let f : (AKLT.Defs.LocalVariable →₀ ℕ) → AKLT.Blueprint.H1.VectorPolynomial :=
    fun a => MvPolynomial.monomial
      (Finsupp.comapDomain Sum.inr a (by
        intro x _ y _ h
        exact Sum.inr.inj h))
      (p.coeff a * ∏ x ∈ V,
        AKLT.Defs.rationalStatusMoment (s x)
          (fun k => a (.inl (x, k))))
  change m ∈ (∑ a ∈ p.support, f a).support at hm
  have hmem : m ∈ p.support.biUnion fun a => (f a).support := by
    exact Finset.mem_of_subset MvPolynomial.support_sum hm
  obtain ⟨a, ha, hma⟩ := Finset.mem_biUnion.mp hmem
  have hma' : m ∈ {Finsupp.comapDomain Sum.inr a (by
      intro x _ y _ h
      exact Sum.inr.inj h)} :=
    Finset.mem_of_subset MvPolynomial.support_monomial_subset hma
  have hdegree : (∑ k : Fin 3, m (j, k)) =
      ∑ k : Fin 3, a (.inr (j, k)) := by
    rw [Finset.mem_singleton] at hma'
    rw [hma']
    rfl
  rw [hdegree]
  exact hp a ha j

end AKLT.W.H1M014

#print axioms AKLT.W.H1M014.main
