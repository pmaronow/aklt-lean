module
public import AKLT.Cert.H1.Production.TopLeaves
public import AKLT.Cert.H1.Production.Tensor

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Every declaration in this file is an exact closed Prop, with no proof.
The registry assigns each mathematical first attempt to a different cheaper
model. Assemblies combine these interfaces with finite check modules. -/
namespace AKLT.Cert.H1.Production.Leaves
open AKLT.Defs AKLT.Gen.Gram
open scoped BigOperators ComplexOrder
noncomputable section

def inputCovered : Prop := ∀ a : Input, inputCheck a = true → (inputPattern a).Covered

def compilerInversion : Prop := ∀ a : Input, inputCheck a = true →
  GroupInversion (inputPattern a) (inputRepresentation a) (inputInversion a)

def compilerGeometry : Prop := ∀ a : Input, inputCheck a = true →
  ∀ ss : List PackedSite, geometryCheck a ss = true → TablesAccepted ss →
    NetworkGeometry (inputPattern a) (inputRepresentation a) (inputInversion a) ss

def denominator : Prop := ∀ π : PatternData, π.Covered → ∀ r : Representation,
  ∀ I : Finset (Fin 20), GroupInversion π r I → ∀ ss : List PackedSite,
    NetworkGeometry π r I ss → ClearsDenominator π r ((ss.map (fun s => s.spec.totalDen)).prod)

def acceptedLookup : Prop := ∀ c : Case, BundlesAccepted c c.bundles →
  ∀ b ∈ c.bundles, b.Accepted c

def parityCoverage : Prop := ∀ c : Case, c.MetadataAccepted →
  ∀ ε : ExchangeSigns (inputPattern c.input), ∃ b ∈ c.bundles,
    b.block.parity = exchangeParity (inputPattern c.input) (inputRepresentation c.input) ε

def basisIndexing : Prop := ∀ c : Case, c.MetadataAccepted → ∀ b : Bundle,
  b.LayoutAccepted c → ∀ ε : ExchangeSigns (inputPattern c.input),
    b.block.parity = exchangeParity (inputPattern c.input) (inputRepresentation c.input) ε →
      b.Indexed c ε

/-- No mathematical reconstruction is hidden in this leaf: it only decodes the
accepted Gaussian integer and the bounded, distinct literal sparse digits. -/
def acceptedDecode : Prop := ∀ c : Case, c.MetadataAccepted → ∀ b : Bundle,
  b.LayoutAccepted c →
  SectorRowsAccepted b.sector c.out c.width c.p c.q b.mapped b.mapped b.block.M →
    constructedSectorRows b.sector c.out c.width
      ((b.sector.map (fun s => s.coordinates.length)).prod) c.p c.q b.mapped = b.block.M

/-- Expansion at disjoint mixed-radix positions; no signed-digit conclusion. -/
def sectorPackingExpansion : Prop := ∀ c : Case, c.MetadataAccepted → ∀ b : Bundle,
  b.LayoutAccepted c → ∀ row : Nat,
    packedSectorThresholdRow b.sector c.out row c.width c.p c.q =
      sumGaussian ((List.range ((b.sector.map (fun s => s.coordinates.length)).prod)).map
        (fun col => (directSectorThreshold b.sector c.out c.p c.q row col).scale
          ((2 : Nat)^(c.width*col) : Int)))

def sectorCoefficientBound : Prop := ∀ c : Case, c.MetadataAccepted → ∀ b : Bundle,
  b.LayoutAccepted c → ∀ row col : Nat,
    (directSectorThreshold b.sector c.out c.p c.q row col).re.natAbs +
      (directSectorThreshold b.sector c.out c.p c.q row col).im.natAbs < 2^(c.width-1)

def signedPacking : Prop := ∀ width n : Nat, 0 < width → ∀ f : Fin n → Int,
  (∀ i, -((2 : Nat)^(width-1) : Int) ≤ f i ∧ f i < ((2 : Nat)^(width-1) : Int)) →
  ∀ i : Fin n, signedDigit ((∑ j : Fin n, f j * ((2 : Nat)^(width*j.val) : Int)) +
    signedBias width n) width i = f i

/-- A small decoder-composition writer uses the preceding expansion, bound,
and signed-digit leaves, rather than reproving the network. -/
def packingDecode : Prop := sectorPackingExpansion → sectorCoefficientBound → signedPacking →
  ∀ c : Case, c.MetadataAccepted → ∀ b : Bundle, b.LayoutAccepted c →
    constructedSectorRows b.sector c.out c.width
      ((b.sector.map (fun s => s.coordinates.length)).prod) c.p c.q b.mapped =
        directSectorRows b.sector c.out c.p c.q b.mapped

/-- Pure coordinate slicing; the unsplit tensor is unchanged. -/
def paritySlice : Prop := ∀ c : Case, c.MetadataAccepted → ∀ b : Bundle,
  b.LayoutAccepted c → ∀ i j : Fin b.block.M.length, ∀ next : Bool,
    directSectorCurrentNext b.sector c.out (b.mapped.getD i 0) (b.mapped.getD j 0) next =
      directCurrentNext c.network c.out (b.block.indices.getD i 0) (b.block.indices.getD j 0) next

/-- Moment contraction and center integration, before any Pauli substitution. -/
def momentPolynomial : Prop := ∀ π : PatternData, π.Covered → ∀ r : Representation,
  ∀ I : Finset (Fin 20), GroupInversion π r I → ∀ ss : List PackedSite,
  NetworkGeometry π r I ss → ∀ out : Nat, ringSites.getD out (0,0) = π.outgoing.step →
  ∀ next : Bool, networkNumerator ss out next =
    MvPolynomial.C ((if next then 5 else 3) *
      (((ss.map (fun s => s.spec.totalDen)).prod : Nat) : ℚ)) *
        invertPolynomial I (reducedPolynomial π r next)

/-- Linear Pauli substitution and integer basis congruence; no spin contraction
or packed digits occur in this leaf. -/
def tensorSubstitution : Prop := ∀ π : PatternData, π.Covered → ∀ r : Representation,
  ∀ I : Finset (Fin 20), GroupInversion π r I → ∀ ss : List PackedSite,
  NetworkGeometry π r I ss → ∀ out : Nat, ringSites.getD out (0,0) = π.outgoing.step →
  ∀ ε : ExchangeSigns π, ∀ a b : CentralBasis π r ε, ∀ next : Bool,
    ((directCurrentNext ss out (exchangeBasisCode π r ε a.val)
      (exchangeBasisCode π r ε b.val) next).re : ℚ) =
      rationalSectorEntry π r ε (networkNumerator ss out next) a b

def sectorLinearity : Prop := ∀ π : PatternData, ∀ r : Representation,
  ∀ ε : ExchangeSigns π, ∀ a b : CentralBasis π r ε, ∀ k : ℚ, ∀ p : VectorPolynomial,
    rationalSectorEntry π r ε (MvPolynomial.C k * p) a b = k * rationalSectorEntry π r ε p a b

/-- The moment/Pauli tensor theorem, independent of packing and witness data.
It uses the exact raw polynomial and the actual unnormalized Defs basis. -/
def rationalCurrent : Prop := ∀ π : PatternData, π.Covered → ∀ r : Representation,
  ∀ I : Finset (Fin 20), GroupInversion π r I → ∀ ss : List PackedSite,
  NetworkGeometry π r I ss → ∀ out : Nat, ringSites.getD out (0,0) = π.outgoing.step →
  ∀ ε : ExchangeSigns π, ∀ a b : CentralBasis π r ε, ∀ next : Bool,
    ((directCurrentNext ss out (exchangeBasisCode π r ε a.val)
      (exchangeBasisCode π r ε b.val) next).re : ℚ) =
      (if next then 5 else 3) * (((ss.map (fun s => s.spec.totalDen)).prod : Nat) : ℚ) *
        rationalSectorEntry π r ε (invertPolynomial I (reducedPolynomial π r next)) a b

def directRowsEntry : Prop := ∀ ss : List SectorSite, ∀ out p q : Nat,
  ∀ indices : List Nat, ∀ n : Nat, indices.length = n → ∀ i j : Fin n,
    matrix n (directSectorRows ss out p q indices) i j =
      (directSectorThreshold ss out p q (indices.getD i 0) (indices.getD j 0)).re

/-- Arithmetic facts about the compiled record, not facts about an operator. -/
def metadataFacts : Prop := ∀ c : Case, c.MetadataAccepted →
  ringSites.getD c.out (0,0) = (inputPattern c.input).outgoing.step ∧
  c.denominator = (c.network.map (fun s => s.spec.totalDen)).prod ∧
  0 < c.width

def rawEncoding : Prop := ∀ π : PatternData, π.Covered →
  ∃ axes ∈ axialConfigurations, ∃ corners : List RawOption,
    corners.length = 4 ∧
    (corners.zipIdx.all (fun (x,i) => cornerOptions.contains x && cornerCompatible axes i x)) = true ∧
    ∃ out : Nat, out < 3 ∧ (rawEdges axes corners).getD out false = true ∧
      effectivePatternCode π = rawKey axes corners out

def enumerationSoundness : Prop := ∀ t : Catalog,
  CoverageRowsAccepted t axialConfigurations → ∀ axes ∈ axialConfigurations,
  ∀ corners : List RawOption, corners.length = 4 →
  (corners.zipIdx.all (fun (x,i) => cornerOptions.contains x && cornerCompatible axes i x)) = true →
  ∀ out : Nat, out < 3 → (rawEdges axes corners).getD out false = true →
    ∃ pid : Nat, t.find (rawKey axes corners out) = some pid

def representativeLookup : Prop := ∀ t : Catalog, ∀ rs : List Representative,
  representativeCheck t rs = true → ∀ key pid : Nat, t.find key = some pid →
    ∃ r ∈ rs, r.pid = pid ∧ r.key = key

def representativeCode : Prop := ∀ a : Input, inputCheck a = true →
  effectivePatternCode (inputPattern a) = rawKey a.axes a.corners a.outgoing

def representativeWitnessLookup : Prop := ∀ rs : List Representative,
  RepresentativesAccepted rs → ∀ r ∈ rs,
    inputCheck r.input = true ∧ (inputPattern r.input).Covered ∧ RawWitness (inputPattern r.input)

def representativesAppend : Prop := ∀ rs ss : List Representative,
  RepresentativesAccepted rs → RepresentativesAccepted ss → RepresentativesAccepted (rs ++ ss)

def effectiveCodeClassification : Prop := ∀ π ρ : PatternData, π.Covered → ρ.Covered →
  effectivePatternCode π = effectivePatternCode ρ → SameEffectiveData π ρ ∨ MirrorEffectiveData π ρ

def sameDataWitness : Prop := ∀ π ρ : PatternData, π.Covered → ρ.Covered →
  SameEffectiveData π ρ → RawWitness ρ → RawWitness π

def mirrorDataWitness : Prop := ∀ π ρ : PatternData, π.Covered → ρ.Covered →
  MirrorEffectiveData π ρ → RawWitness ρ → RawWitness π

end
end AKLT.Cert.H1.Production.Leaves
