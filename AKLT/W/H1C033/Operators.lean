module
public import AKLT.W.H1C033.Polynomial
public import AKLT.W.H1C033.Basis

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C033

/-- Rational complex multiplication can be folded in any order. -/
 theorem ratComplex_rightComm (a b c : ℚ × ℚ) :
    ratComplexMul (ratComplexMul a b) c = ratComplexMul (ratComplexMul a c) b := by
  apply Prod.ext <;> simp only [ratComplexMul, Prod.fst, Prod.snd] <;> ring

 theorem foldRat_reindex {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℚ × ℚ) :
    (((Finset.univ : Finset β).toList.map f).foldl ratComplexMul (1,0)) =
      (((Finset.univ : Finset α).toList.map (fun x => f (e x))).foldl ratComplexMul (1,0)) := by
  classical
  have hp : (Finset.univ : Finset β).toList.Perm
      ((Finset.univ : Finset α).toList.map e) := by
    apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _)
      ((Finset.nodup_toList _).map e.injective)).mpr
    intro y
    simp only [Finset.mem_toList, Finset.mem_univ, List.mem_map, true_and, true_iff]
    exact e.surjective y
  letI : RightCommutative ratComplexMul := ⟨ratComplex_rightComm⟩
  have hf := List.Perm.foldl_eq (f := ratComplexMul) (hp.map f) (1,0)
  simpa only [List.map_map, Function.comp_def] using hf

 theorem mirror_pauliExponent (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (a : reductionVectors π r → Fin 4) :
    pauliExponent (reductionVectors ρ r) (pushEquiv (vectorIndexEquiv π ρ h r) a) =
      (pauliExponent (reductionVectors π r) a).mapDomain vectorEquiv := by
  classical
  ext v
  obtain ⟨⟨j,k⟩,rfl⟩ := vectorEquiv.surjective v
  rw [Finsupp.mapDomain_apply_of_injective vectorEquiv.injective]
  simp only [pauliExponent, Finsupp.coe_equivFunOnFinite_symm, vectorEquiv_apply]
  by_cases hj : j ∈ reductionVectors π r
  · have ht := (mirror_vectors π ρ h r j).mpr hj
    simp only [hj, ht, dite_true]
    have hi : (⟨flipToken j,ht⟩ : reductionVectors ρ r) =
        vectorIndexEquiv π ρ h r ⟨j,hj⟩ := Subtype.ext rfl
    rw [hi, pushEquiv_apply]
  · have ht : flipToken j ∉ reductionVectors ρ r := by
      simpa only [mirror_vectors π ρ h r j] using hj
    simp only [hj, ht, dite_false]

 theorem mirror_operatorEntry (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (p : MvPolynomial (Fin 20 × Fin 3) ℚ)
    (σ τ : reductionVectors π r → Fin 2) :
    rationalOperatorEntry (reductionVectors ρ r) (MvPolynomial.rename vectorEquiv p)
      (pushEquiv (vectorIndexEquiv π ρ h r) σ) (pushEquiv (vectorIndexEquiv π ρ h r) τ) =
      rationalOperatorEntry (reductionVectors π r) p σ τ := by
  classical
  unfold rationalOperatorEntry
  symm
  apply Fintype.sum_equiv (pushEquiv (vectorIndexEquiv π ρ h r))
  intro a
  rw [mirror_pauliExponent, MvPolynomial.coeff_rename_mapDomain vectorEquiv vectorEquiv.injective]
  apply congrArg (fun z : ℚ × ℚ => p.coeff (pauliExponent (reductionVectors π r) a) * z.1)
  symm
  rw [foldRat_reindex (vectorIndexEquiv π ρ h r)]
  simp only [pushEquiv_apply]

 theorem mirror_sectorEntry (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π)
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ) (a b : CentralBasis π r ε) :
    rationalSectorEntry ρ r (mirroredSigns π ρ h ε) (MvPolynomial.rename vectorEquiv p)
      (centralEquiv π ρ h r ε a) (centralEquiv π ρ h r ε b) =
      rationalSectorEntry π r ε p a b := by
  classical
  unfold rationalSectorEntry
  symm
  apply Fintype.sum_equiv (pushEquiv (vectorIndexEquiv π ρ h r))
  intro σ
  apply Fintype.sum_equiv (pushEquiv (vectorIndexEquiv π ρ h r))
  intro τ
  rw [centralEquiv_val, centralEquiv_val, mirror_basisVector, mirror_basisVector,
    mirror_operatorEntry]

 theorem mirror_integerMatrix (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (I : Finset (Fin 20)) (D : ℕ)
    (next : Bool) (a b : CentralBasis π r ε) :
    integerSectorMatrix ρ r (mirroredSigns π ρ h ε) (I.image flipToken) D next
      (centralEquiv π ρ h r ε a) (centralEquiv π ρ h r ε b) =
      integerSectorMatrix π r ε I D next a b := by
  unfold integerSectorMatrix
  rw [← mirror_polynomial π ρ h r next, invert_rename, mirror_sectorEntry]

 theorem mirror_thresholdMatrix (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (ε : ExchangeSigns π) (I : Finset (Fin 20)) (D p q : ℕ)
    (a b : CentralBasis π r ε) :
    thresholdSectorMatrix ρ r (mirroredSigns π ρ h ε) (I.image flipToken) D p q
      (centralEquiv π ρ h r ε a) (centralEquiv π ρ h r ε b) =
      thresholdSectorMatrix π r ε I D p q a b := by
  change (5 * (q : ℤ)) * integerSectorMatrix ρ r _ _ D false _ _ -
    (3 * (p : ℤ)) * integerSectorMatrix ρ r _ _ D true _ _ =
    (5 * (q : ℤ)) * integerSectorMatrix π r ε I D false a b -
    (3 * (p : ℤ)) * integerSectorMatrix π r ε I D true a b
  rw [mirror_integerMatrix, mirror_integerMatrix]

end AKLT.W.H1C033
