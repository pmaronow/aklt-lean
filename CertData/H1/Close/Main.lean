import CertData.H1.Generated.Bridge.Targetassembly0000
import AKLT.W.H1C001.Main
import AKLT.W.H1C002.Main
import AKLT.W.H1C003.Main
import AKLT.W.H1C004.Main
import AKLT.W.H1C005.Main
import AKLT.W.H1C006.Main
import AKLT.W.H1C007.Main
import AKLT.W.H1C008.Main
import AKLT.W.H1C009.Main
import AKLT.W.H1C010.Main
import AKLT.W.H1C011.Main
import AKLT.W.H1C012.Main
import AKLT.W.H1C013.Main
import AKLT.W.H1C014.Main
import AKLT.W.H1C015.Main
import AKLT.W.H1C016.Main
import AKLT.W.H1C017.Main
import AKLT.W.H1C018.Main
import AKLT.W.H1C019.Main
import AKLT.W.H1C020.Main
import AKLT.W.H1C021.Main
import AKLT.W.H1C022.Main
import AKLT.W.H1C023.Main
import AKLT.W.H1C024.Main
import AKLT.W.H1C025.Main
import AKLT.W.H1C026.Main
import AKLT.W.H1C027.Main
import AKLT.W.H1C028.Main
import AKLT.W.H1C029.Main
import AKLT.W.H1C030.Main
import AKLT.W.H1C031.Main
import AKLT.W.H1C032.Main
import AKLT.W.H1C033.Main

/-! Closing assembly for the two H1 certificate contracts on main.
The numerical proofs are imported from the retained production artifacts.
All mathematical leaves below are supplied by merged writer theorems. -/

namespace CertData.H1.Close
open AKLT.Cert.H1.Production

-- These examples check every merged theorem against its exact closed leaf type.
example : AKLT.Cert.H1.Production.TopLeaves.integerEntries := AKLT.W.H1C001.main
example : AKLT.Cert.H1.Production.TopLeaves.thresholdScale := AKLT.W.H1C002.main
example : AKLT.Cert.H1.Production.TopLeaves.positiveScale := AKLT.W.H1C003.main
example : AKLT.Cert.H1.Production.TopLeaves.sylvester := AKLT.W.H1C004.main
example : AKLT.Cert.H1.Production.TopLeaves.bareiss := AKLT.W.H1C005.main
example : AKLT.Cert.H1.Production.TopLeaves.sectorPositiveImpliesBound := AKLT.W.H1C006.main
example : AKLT.Cert.H1.Production.Leaves.inputCovered := AKLT.W.H1C007.main
example : AKLT.Cert.H1.Production.Leaves.compilerInversion := AKLT.W.H1C008.main
example : AKLT.Cert.H1.Production.Leaves.compilerGeometry := AKLT.W.H1C009.main
example : AKLT.Cert.H1.Production.Leaves.denominator := AKLT.W.H1C010.main
example : AKLT.Cert.H1.Production.Leaves.acceptedLookup := AKLT.W.H1C011.main
example : AKLT.Cert.H1.Production.Leaves.parityCoverage := AKLT.W.H1C012.main
example : AKLT.Cert.H1.Production.Leaves.basisIndexing := AKLT.W.H1C013.main
example : AKLT.Cert.H1.Production.Leaves.acceptedDecode := AKLT.W.H1C014.main
example : AKLT.Cert.H1.Production.Leaves.sectorPackingExpansion := AKLT.W.H1C015.main
example : AKLT.Cert.H1.Production.Leaves.sectorCoefficientBound := AKLT.W.H1C016.main
example : AKLT.Cert.H1.Production.Leaves.signedPacking := AKLT.W.H1C017.main
example : AKLT.Cert.H1.Production.Leaves.packingDecode := AKLT.W.H1C018.main
example : AKLT.Cert.H1.Production.Leaves.paritySlice := AKLT.W.H1C019.main
example : AKLT.Cert.H1.Production.Leaves.momentPolynomial := AKLT.W.H1C020.main
example : AKLT.Cert.H1.Production.Leaves.tensorSubstitution := AKLT.W.H1C021.main
example : AKLT.Cert.H1.Production.Leaves.sectorLinearity := AKLT.W.H1C022.main
example : AKLT.Cert.H1.Production.Leaves.directRowsEntry := AKLT.W.H1C023.main
example : AKLT.Cert.H1.Production.Leaves.metadataFacts := AKLT.W.H1C024.main
example : AKLT.Cert.H1.Production.Leaves.rawEncoding := AKLT.W.H1C025.main
example : AKLT.Cert.H1.Production.Leaves.enumerationSoundness := AKLT.W.H1C026.main
example : AKLT.Cert.H1.Production.Leaves.representativeLookup := AKLT.W.H1C027.main
example : AKLT.Cert.H1.Production.Leaves.representativeCode := AKLT.W.H1C028.main
example : AKLT.Cert.H1.Production.Leaves.representativeWitnessLookup := AKLT.W.H1C029.main
example : AKLT.Cert.H1.Production.Leaves.representativesAppend := AKLT.W.H1C030.main
example : AKLT.Cert.H1.Production.Leaves.effectiveCodeClassification := AKLT.W.H1C031.main
example : AKLT.Cert.H1.Production.Leaves.sameDataWitness := AKLT.W.H1C032.main
example : AKLT.Cert.H1.Production.Leaves.mirrorDataWitness := AKLT.W.H1C033.main

private theorem constructorPremises : Assembly.ConstructorPremises :=
  {
    covered := AKLT.W.H1C007.main
    inversion := AKLT.W.H1C008.main
    geometry := AKLT.W.H1C009.main
    denominator := AKLT.W.H1C010.main
    lookup := AKLT.W.H1C011.main
    parities := AKLT.W.H1C012.main
    basis := AKLT.W.H1C013.main
    acceptedDecode := AKLT.W.H1C014.main
    expansion := AKLT.W.H1C015.main
    bound := AKLT.W.H1C016.main
    signed := AKLT.W.H1C017.main
    packing := AKLT.W.H1C018.main
    slice := AKLT.W.H1C019.main
    moment := AKLT.W.H1C020.main
    substitution := AKLT.W.H1C021.main
    linearity := AKLT.W.H1C022.main
    entries := AKLT.W.H1C001.main
    rows := AKLT.W.H1C023.main
    metadata := AKLT.W.H1C024.main
  }

private theorem coveragePremises : Assembly.CoveragePremises :=
  {
    encoding := AKLT.W.H1C025.main
    enumeration := AKLT.W.H1C026.main
    lookup := AKLT.W.H1C027.main
    code := AKLT.W.H1C028.main
    witnesses := AKLT.W.H1C029.main
    classification := AKLT.W.H1C031.main
    same := AKLT.W.H1C032.main
    mirror := AKLT.W.H1C033.main
  }

private theorem closedTargets :
    AKLT.Blueprint.Top.IntegerCheckStatement ∧ AKLT.Blueprint.Top.CertificateStatementV2 :=
  CertData.H1.Generated.Check.Targets.targets
    constructorPremises coveragePremises AKLT.W.H1C030.main
    ⟨AKLT.W.H1C001.main, AKLT.W.H1C006.main⟩
    ⟨AKLT.W.H1C001.main, AKLT.W.H1C002.main, AKLT.W.H1C003.main,
      AKLT.W.H1C004.main, AKLT.W.H1C005.main⟩

/-- The full finite H1 witness statement, with no certificate or leaf assumptions. -/
theorem finiteData : AKLT.Blueprint.Top.H1FiniteDataStatementV2 :=
  closedTargets.2.2

/-- The original H1 certificate soundness contract, with no remaining assumptions. -/
theorem certificate : AKLT.Blueprint.Top.CertificateStatement :=
  closedTargets.2.1

example : AKLT.Blueprint.Top.H1FiniteDataStatementV2 := finiteData
example : AKLT.Blueprint.Top.CertificateStatement := certificate

#print finiteData
#print certificate
#print axioms constructorPremises
#print axioms coveragePremises
#print axioms closedTargets
#print axioms finiteData
#print axioms certificate
#print axioms AKLT.W.H1C001.main
#print axioms AKLT.W.H1C002.main
#print axioms AKLT.W.H1C003.main
#print axioms AKLT.W.H1C004.main
#print axioms AKLT.W.H1C005.main
#print axioms AKLT.W.H1C006.main
#print axioms AKLT.W.H1C007.main
#print axioms AKLT.W.H1C008.main
#print axioms AKLT.W.H1C009.main
#print axioms AKLT.W.H1C010.main
#print axioms AKLT.W.H1C011.main
#print axioms AKLT.W.H1C012.main
#print axioms AKLT.W.H1C013.main
#print axioms AKLT.W.H1C014.main
#print axioms AKLT.W.H1C015.main
#print axioms AKLT.W.H1C016.main
#print axioms AKLT.W.H1C017.main
#print axioms AKLT.W.H1C018.main
#print axioms AKLT.W.H1C019.main
#print axioms AKLT.W.H1C020.main
#print axioms AKLT.W.H1C021.main
#print axioms AKLT.W.H1C022.main
#print axioms AKLT.W.H1C023.main
#print axioms AKLT.W.H1C024.main
#print axioms AKLT.W.H1C025.main
#print axioms AKLT.W.H1C026.main
#print axioms AKLT.W.H1C027.main
#print axioms AKLT.W.H1C028.main
#print axioms AKLT.W.H1C029.main
#print axioms AKLT.W.H1C030.main
#print axioms AKLT.W.H1C031.main
#print axioms AKLT.W.H1C032.main
#print axioms AKLT.W.H1C033.main

end CertData.H1.Close
