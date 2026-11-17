module
public import AKLT.W.H1C033.Operators

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Reflection transport keeps the certificate's original `Fin t` order.
Only its equivalence with the central basis changes; its lower-triangular
factor and all residual row inequalities are reused verbatim. -/
noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

namespace AKLT.W.H1C033

 theorem mirror_sectorWitnesses (π ρ : PatternData) (h : MirrorEffectiveData π ρ)
    (r : Representation) (I : Finset (Fin 20)) (D p q : ℕ)
    (hw : H1SectorWitnesses π r I D p q) :
    H1SectorWitnesses ρ r (I.image flipToken) D p q := by
  intro ερ
  obtain ⟨ε,hε⟩ := (pushEquiv (groupEquiv π ρ h) : ExchangeSigns π ≃ ExchangeSigns ρ).surjective ερ
  change mirroredSigns π ρ h ε = ερ at hε
  subst ερ
  obtain ⟨t,index,g,d,S,L,hL,hrows⟩ := hw ε
  let index' : Fin t ≃ CentralBasis ρ r (mirroredSigns π ρ h ε) :=
    index.trans (centralEquiv π ρ h r ε)
  refine ⟨t,index',g,d,S,L,hL,?_⟩
  have hM : indexedSectorMatrix ρ r (mirroredSigns π ρ h ε) (I.image flipToken) D p q index' =
      indexedSectorMatrix π r ε I D p q index := by
    ext i j
    change thresholdSectorMatrix ρ r (mirroredSigns π ρ h ε) (I.image flipToken) D p q
      (centralEquiv π ρ h r ε (index i)) (centralEquiv π ρ h r ε (index j)) =
      thresholdSectorMatrix π r ε I D p q (index i) (index j)
    exact mirror_thresholdMatrix π ρ h r ε I D p q (index i) (index j)
  rw [hM]
  exact hrows

 theorem main : AKLT.Cert.H1.Production.Leaves.mirrorDataWitness := by
  intro π ρ _ _ h hw
  obtain ⟨r,I,hI,D,hD,hsectors⟩ := hw
  have hs := mirror_symm π ρ h
  refine ⟨r,I.image flipToken,mirror_inversion π ρ h r I hI,D,
    mirror_denominator ρ π hs r D hD,?_⟩
  rw [mirror_h1Numerator_eq π ρ h, mirror_h1Denominator_eq π ρ h]
  exact mirror_sectorWitnesses ρ π hs r I D (h1Numerator ρ) (h1Denominator ρ) hsectors

#print axioms flip_flip
#print axioms flip_zero
#print axioms flip_inj
#print axioms flip_tips
#print axioms flip_corners
#print axioms flip_sites
#print axioms flipEdge_flipEdge
#print axioms flipEdge_incident
#print axioms flipEdge_internal
#print axioms internal_not_reverse
#print axioms mem_bonds_iff
#print axioms mirror_edge
#print axioms mirror_degree
#print axioms mirror_groups
#print axioms mirror_single
#print axioms mirror_pair
#print axioms mirror_symm
#print axioms mirror_h1Numerator_eq
#print axioms mirror_h1Denominator_eq
#print axioms flipToken_flipToken
#print axioms flip_leader
#print axioms flip_second
#print axioms mirror_vectors
#print axioms mirror_inversion
#print axioms mirror_neighbour
#print axioms isolated_exponent
#print axioms mirror_bondedSpins
#print axioms trim_contract
#print axioms pointEquiv_apply
#print axioms tokenEquiv_apply
#print axioms vectorEquiv_apply
#print axioms localEquiv_inl
#print axioms localEquiv_inr
#print axioms rename_formalDot
#print axioms formalDot_comm
#print axioms positive_of_incident
#print axioms mirror_retained
#print axioms flip_pair_eq
#print axioms mirror_out_edge
#print axioms mirror_integrand
#print axioms externalExponent_rename
#print axioms contract_rename
#print axioms mirror_polynomial
#print axioms mirror_denominator
#print axioms invert_rename
#print axioms groupEquiv_val
#print axioms vectorIndexEquiv_val
#print axioms mirroredSigns_apply
#print axioms group_status
#print axioms mirror_basisSize
#print axioms groupBasisEquiv_val
#print axioms exchangeEquiv_val
#print axioms mirror_weight
#print axioms mirror_centralWeight
#print axioms centralEquiv_val
#print axioms pushEquiv_apply
#print axioms vectorIndexEquiv_leader
#print axioms vectorIndexEquiv_second
#print axioms mirror_basisVector
#print axioms ratComplex_rightComm
#print axioms foldRat_reindex
#print axioms mirror_pauliExponent
#print axioms mirror_operatorEntry
#print axioms mirror_sectorEntry
#print axioms mirror_integerMatrix
#print axioms mirror_thresholdMatrix
#print axioms mirror_sectorWitnesses
#print axioms main

#check (AKLT.W.H1C033.main : AKLT.Cert.H1.Production.Leaves.mirrorDataWitness)

end AKLT.W.H1C033
