module
public import AKLT.Cert.H1.Production.Leaves
public import AKLT.Cert.H1.Production.TopAssembly

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Only conditional assemblies. Every mathematical input is an exact closed
Prop in Leaves/TopLeaves and is assigned to a different cheaper first model. -/
namespace AKLT.Cert.H1.Production.Assembly
open AKLT.Defs AKLT.Gen.Gram
open scoped BigOperators ComplexOrder
noncomputable section

structure ConstructorPremises : Prop where
  covered : Leaves.inputCovered
  inversion : Leaves.compilerInversion
  geometry : Leaves.compilerGeometry
  denominator : Leaves.denominator
  lookup : Leaves.acceptedLookup
  parities : Leaves.parityCoverage
  basis : Leaves.basisIndexing
  acceptedDecode : Leaves.acceptedDecode
  expansion : Leaves.sectorPackingExpansion
  bound : Leaves.sectorCoefficientBound
  signed : Leaves.signedPacking
  packing : Leaves.packingDecode
  slice : Leaves.paritySlice
  moment : Leaves.momentPolynomial
  substitution : Leaves.tensorSubstitution
  linearity : Leaves.sectorLinearity
  entries : TopLeaves.integerEntries
  rows : Leaves.directRowsEntry
  metadata : Leaves.metadataFacts

theorem rationalCurrent_of_leaves (hm : Leaves.momentPolynomial)
    (hs : Leaves.tensorSubstitution) (hl : Leaves.sectorLinearity) : Leaves.rationalCurrent := by
  intro π hπ r I hI ss hg out ho ε a b next
  rw [hs π hπ r I hI ss hg out ho ε a b next,
    hm π hπ r I hI ss hg out ho next,
    hl π r ε a b]

theorem case_denominator (h : ConstructorPremises) {c : Case} (hm : c.MetadataAccepted) :
    ClearsDenominator (inputPattern c.input) (inputRepresentation c.input) c.denominator := by
  rcases hm with ⟨hi,hg,ht,hp,ho,hn,hd,hpar⟩
  have hgeom := h.geometry c.input hi c.network hg ht
  have hc := h.denominator _ (h.covered _ hi) _ _ (h.inversion _ hi) _ hgeom
  rw [← (h.metadata c ⟨hi,hg,ht,hp,ho,hn,hd,hpar⟩).2.1] at hc
  exact hc

theorem matrix_from_stages (h : ConstructorPremises) {c : Case} (hm : c.MetadataAccepted)
    {b : Bundle} (hb : b.LayoutAccepted c)
    (hr : SectorRowsAccepted b.sector c.out c.width c.p c.q b.mapped b.mapped b.block.M)
    (ε : ExchangeSigns (inputPattern c.input))
    (index : Fin b.block.M.length ≃ CentralBasis (inputPattern c.input) (inputRepresentation c.input) ε)
    (codes : ∀ i : Fin b.block.M.length, b.block.indices.getD i 0 =
      exchangeBasisCode (inputPattern c.input) (inputRepresentation c.input) ε (index i).val) :
    matrix b.block.M.length b.block.M = indexedSectorMatrix (inputPattern c.input)
      (inputRepresentation c.input) ε (inputInversion c.input) c.denominator c.p c.q index := by
  have hπ := h.covered c.input hm.1
  have hI := h.inversion c.input hm.1
  have hgeom := h.geometry c.input hm.1 c.network hm.2.1 hm.2.2.1
  have hD := case_denominator h hm
  have facts := h.metadata c hm
  have hM : b.block.M = directSectorRows b.sector c.out c.p c.q b.mapped :=
    (h.acceptedDecode c hm b hb hr).symm.trans
      (h.packing h.expansion h.bound h.signed c hm b hb)
  have hints (i j : Fin b.block.M.length) (next : Bool) :
      (directSectorCurrentNext b.sector c.out (b.mapped.getD i 0) (b.mapped.getD j 0) next).re =
        integerSectorMatrix (inputPattern c.input) (inputRepresentation c.input) ε
          (inputInversion c.input) c.denominator next (index i) (index j) := by
    have ht := rationalCurrent_of_leaves h.moment h.substitution h.linearity
      (inputPattern c.input) hπ (inputRepresentation c.input) (inputInversion c.input) hI
      c.network hgeom c.out facts.1 ε (index i) (index j) next
    have he := (h.entries (inputPattern c.input) hπ (inputRepresentation c.input)
      (inputInversion c.input) hI c.denominator hD ε next).2 (index i) (index j)
    rw [← facts.2.1] at ht
    rw [← codes i, ← codes j, ← h.slice c hm b hb i j next] at ht
    exact_mod_cast ht.trans he.symm
  ext i j
  calc
    matrix b.block.M.length b.block.M i j =
        matrix b.block.M.length (directSectorRows b.sector c.out c.p c.q b.mapped) i j :=
      congrArg (fun rows => matrix b.block.M.length rows i j) hM
    _ = (directSectorThreshold b.sector c.out c.p c.q (b.mapped.getD i 0) (b.mapped.getD j 0)).re :=
      h.rows b.sector c.out c.p c.q b.mapped b.block.M.length hb.2.2.2.2 i j
    _ = indexedSectorMatrix (inputPattern c.input) (inputRepresentation c.input) ε
        (inputInversion c.input) c.denominator c.p c.q index i j := by
      simp only [directSectorThreshold, Gaussian.add, Gaussian.scale]
      rw [hints i j false, hints i j true]
      simp only [indexedSectorMatrix, thresholdSectorMatrix, Matrix.submatrix_apply,
        Matrix.sub_apply, Matrix.smul_apply, zsmul_eq_mul, Int.cast_id]
      ring

theorem case_witness (h : ConstructorPremises) {c : Case} (hc : c.Accepted) :
    RawWitness (inputPattern c.input) := by
  obtain ⟨hm,hbs⟩ := hc
  refine ⟨inputRepresentation c.input, inputInversion c.input, h.inversion _ hm.1,
    c.denominator, case_denominator h hm, ?_⟩
  rcases hm with ⟨hi,hg,ht,hparams,ho,hp,hq,hpar⟩
  rw [← hp, ← hq]
  intro ε
  let hm' : c.MetadataAccepted := ⟨hi,hg,ht,hparams,ho,hp,hq,hpar⟩
  obtain ⟨b,hmem,hparity⟩ := h.parities c hm' ε
  obtain ⟨hl,hr,hcheck,htri⟩ := h.lookup c hbs b hmem
  obtain ⟨index,hcodes⟩ := h.basis c hm' b hl ε hparity
  have hM := matrix_from_stages h hm' hl hr ε index hcodes
  refine ⟨b.block.M.length,index,b.block.g,b.block.d,b.block.S,
    matrix b.block.M.length b.block.L, ?_, ?_⟩
  · exact fun i j hij => lowerTriangularCheck_sound htri _ i j hij
  · rw [← hM]
    exact gramResidualRows_of_checked hcheck

structure CoveragePremises : Prop where
  encoding : Leaves.rawEncoding
  enumeration : Leaves.enumerationSoundness
  lookup : Leaves.representativeLookup
  code : Leaves.representativeCode
  witnesses : Leaves.representativeWitnessLookup
  classification : Leaves.effectiveCodeClassification
  same : Leaves.sameDataWitness
  mirror : Leaves.mirrorDataWitness

theorem finiteData_of_checks (h : CoveragePremises) (t : Catalog) (rs : List Representative)
    (he : CoverageRowsAccepted t axialConfigurations)
    (hi : representativeCheck t rs = true) (hw : RepresentativesAccepted rs) :
    AKLT.Blueprint.Top.H1FiniteDataStatementV2 := by
  intro π hπ
  obtain ⟨axes,ha,corners,hcl,hcc,out,ho,heout,hkey⟩ := h.encoding π hπ
  obtain ⟨pid,hfind⟩ := h.enumeration t he axes ha corners hcl hcc out ho heout
  obtain ⟨r,hr,_hpid,hrkey⟩ := h.lookup t rs hi _ pid hfind
  obtain ⟨hin,hρ,hwρ⟩ := h.witnesses rs hw r hr
  have heq : effectivePatternCode π = effectivePatternCode (inputPattern r.input) :=
    hkey.trans (hrkey.symm.trans (h.code r.input hin).symm)
  rcases h.classification π (inputPattern r.input) hπ hρ heq with hs | hm
  · exact h.same π (inputPattern r.input) hπ hρ hs hwρ
  · exact h.mirror π (inputPattern r.input) hπ hρ hm hwρ

theorem certificateV2_of_checks (hc : TopLeaves.certificatePremises)
    (h : CoveragePremises) (t : Catalog) (rs : List Representative)
    (he : CoverageRowsAccepted t axialConfigurations)
    (hi : representativeCheck t rs = true) (hw : RepresentativesAccepted rs) :
    AKLT.Blueprint.Top.CertificateStatementV2 :=
  ⟨TopAssembly.certificate_of_leaves hc,finiteData_of_checks h t rs he hi hw⟩

#print axioms rationalCurrent_of_leaves
#print axioms case_denominator
#print axioms matrix_from_stages
#print axioms case_witness
#print axioms finiteData_of_checks
#print axioms certificateV2_of_checks
end
end AKLT.Cert.H1.Production.Assembly
