module
public import AKLT.W.H3C001.Main
public import AKLT.W.H3C002.Main
public import AKLT.W.H3C003.Main
public import AKLT.W.H3C004.Main
public import AKLT.W.H3C005.Main
public import AKLT.W.H3C006.Main
public import AKLT.W.H3C007.Main
public import AKLT.W.H3C008.Main
public import AKLT.W.H3C009.Main
public import AKLT.W.H3C010.Main
public import AKLT.W.H3C011.Main
public import AKLT.W.H3C012.Main
public import AKLT.W.H3C013.Main
public import AKLT.W.H3C014.Main
public import AKLT.W.H3C015.Main
public import AKLT.W.H3C016.Main
public import AKLT.W.H3C017.Main
public import AKLT.W.H3C018.Main
public import AKLT.W.H3C019.Main
public import AKLT.W.H3C020.Main
public import AKLT.W.H3C021.Main
public import AKLT.W.H3C022.Main
public import AKLT.W.H3C023.Main
public import AKLT.W.H3C024.Main
public import AKLT.W.H3C025.Main
public import AKLT.W.H3C026.Main
public import AKLT.W.H3C027.Main
public import AKLT.W.H3C028.Main
public import AKLT.W.H3C029.Main
public import AKLT.W.H3C030.Main
public import AKLT.W.H3C031.Main
public import AKLT.W.H3C032.Main
public import AKLT.W.H3C033.Main
public import AKLT.W.H3C034.Main
public import AKLT.W.H3C035.Main
public import AKLT.W.H3C036.Main
public import AKLT.W.H3C037.Main
public import AKLT.W.H3C038.Main
public import AKLT.W.H3C039.Main
public import AKLT.W.H3C040.Main
public import AKLT.W.H3C041.Main
public import AKLT.W.H3C042.Main
public import AKLT.W.H3C043.Main
public import AKLT.W.H3C044.Main
public import AKLT.W.H3C045.Main
public import AKLT.W.H3C046.Main
public import AKLT.W.H3C047.Main
public import AKLT.W.H3C048.Main
public import AKLT.W.H3C049.Main
public import AKLT.W.H3C050.Main
public import AKLT.W.H3C051.Main
public import AKLT.W.H3C052.Main
public import AKLT.W.H3C053.Main
public import AKLT.W.H3C054.Main
public import AKLT.W.H3C055.Main
public import AKLT.W.H3C056.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

set_option maxRecDepth 100000

/-! Close the hand-written H3 interfaces using the merged leaf theorems.
The examples check the complete 56-entry handoff in its original order. -/

namespace CertData.H3.Close

open CertData.H3.Bridge

example : CertData.H3.Bridge.CodeDecodeLeaf := AKLT.W.H3C001.main
example : CertData.H3.Bridge.CodeEncodeLeaf := AKLT.W.H3C002.main
example : CertData.H3.Bridge.LastWindowCodeLeaf := AKLT.W.H3C003.main
example : CertData.H3.Bridge.SuccessorCodeLeaf := AKLT.W.H3C004.main
example : CertData.H3.Bridge.RawReplaySoundLeaf := AKLT.W.H3C005.main
example : CertData.H3.Bridge.RawReplayCompleteLeaf := AKLT.W.H3C006.main
example : CertData.H3.Bridge.LegalDirectionLeaf := AKLT.W.H3C007.main
example : CertData.H3.Bridge.RevisitLeaf := AKLT.W.H3C008.main
example : CertData.H3.Bridge.RawRowSoundLeaf := AKLT.W.H3C009.main
example : CertData.H3.Bridge.RawTrieCoverageLeaf := AKLT.W.H3C010.main
example : CertData.H3.Bridge.RawTrieProjectionLeaf := AKLT.W.H3C011.main
example : CertData.H3.Bridge.RawTrieBoundsLeaf := AKLT.W.H3C012.main
example : CertData.H3.Bridge.RepresentativeBoundsLeaf := AKLT.W.H3C013.main
example : CertData.H3.Bridge.FieldCheckSoundLeaf := AKLT.W.H3C014.main
example : CertData.H3.Bridge.RawTrieCountLeaf := AKLT.W.H3C015.main
example : CertData.H3.Bridge.EdgeCountLeaf := AKLT.W.H3C016.main
example : CertData.H3.Bridge.IntervalCoverageLeaf := AKLT.W.H3C017.main
example : CertData.H3.Bridge.RectangleLeaf := AKLT.W.H3C018.main
example : CertData.H3.Bridge.EndpointBoxLeaf := AKLT.W.H3C019.main
example : CertData.H3.Bridge.PullLeaf := AKLT.W.H3C020.main
example : CertData.H3.Bridge.OrdinaryMaskLeaf := AKLT.W.H3C021.main
example : CertData.H3.Bridge.KnownMaskLeaf := AKLT.W.H3C022.main
example : CertData.H3.Bridge.DeadMaskLeaf := AKLT.W.H3C023.main
example : CertData.H3.Bridge.CenterZeroV2Leaf := AKLT.W.H3C024.main
example : CertData.H3.Bridge.TableBoundsLeaf := AKLT.W.H3C025.main
example : CertData.H3.Bridge.RowTermsV2Leaf := AKLT.W.H3C026.main
example : CertData.H3.Bridge.FreeRowLeaf := AKLT.W.H3C027.main
example : CertData.H3.Bridge.PlaneSoundLeaf := AKLT.W.H3C028.main
example : CertData.H3.Bridge.PrefixReplaySoundLeaf := AKLT.W.H3C029.main
example : CertData.H3.Bridge.PrefixReplayCompleteLeaf := AKLT.W.H3C030.main
example : CertData.H3.Bridge.PrefixStepLeaf := AKLT.W.H3C031.main
example : CertData.H3.Bridge.ShortComparatorLeaf := AKLT.W.H3C032.main
example : CertData.H3.Bridge.ShortValueLeaf := AKLT.W.H3C033.main
example : CertData.H3.Bridge.PrefixBatchSoundLeaf := AKLT.W.H3C034.main
example : CertData.H3.Bridge.EarlySoundLeaf := AKLT.W.H3C035.main
example : CertData.H3.Bridge.PrefixPartitionLeaf := AKLT.W.H3C036.main
example : CertData.H3.Bridge.NumericScaleLeaf := AKLT.W.H3C037.main
example : CertData.H3.Bridge.RationalCeilingLeaf := AKLT.W.H3C038.main
example : CertData.H3.Bridge.PlaneBatchSoundLeaf := AKLT.W.H3C039.main
example : CertData.H3.Bridge.RowCoverageLeaf := AKLT.W.H3C040.main
example : CertData.H3.Bridge.EndpointTableSoundLeaf := AKLT.W.H3C041.main
example : CertData.H3.Bridge.ResultAddLeaf := AKLT.W.H3C042.main
example : CertData.H3.Bridge.SemanticBatchSplitLeaf := AKLT.W.H3C043.main
example : CertData.H3.Bridge.PrefixResultsJoinLeaf := AKLT.W.H3C044.main
example : CertData.H3.Bridge.UniformRowCoverageLeaf := AKLT.W.H3C045.main
example : CertData.H3.Bridge.PrefixFamilyJoinLeaf := AKLT.W.H3C046.main
example : CertData.H3.Bridge.SpanDataLeaf := AKLT.W.H3C047.main
example : CertData.H3.Bridge.ClassDataLeaf := AKLT.W.H3C048.main
example : CertData.H3.Bridge.DecodeDataLeaf := AKLT.W.H3C049.main
example : CertData.H3.Bridge.QuotientDataLeaf := AKLT.W.H3C050.main
example : CertData.H3.Bridge.UnmaskedDataLeaf := AKLT.W.H3C051.main
example : CertData.H3.Bridge.FieldJoinLeaf := AKLT.W.H3C052.main
example : CertData.H3.Bridge.RawShardJoinLeaf := AKLT.W.H3C053.main
example : CertData.H3.Bridge.RepresentativeJoinLeaf := AKLT.W.H3C054.main
example : CertData.H3.Bridge.PassesEquivalenceLeaf := AKLT.W.H3C055.main
example : AKLT.Cert.H3.RowTermsAgreement := AKLT.W.H3C056.main

/-- The closed automaton interface consumed by the generated graph assembly. -/
theorem automatonLeaves : AutomatonBridgeLeaves :=
  ⟨AKLT.W.H3C047.main, AKLT.W.H3C048.main, AKLT.W.H3C049.main,
   AKLT.W.H3C050.main, AKLT.W.H3C053.main, AKLT.W.H3C054.main,
   AKLT.W.H3C010.main, AKLT.W.H3C011.main, AKLT.W.H3C015.main,
   AKLT.W.H3C016.main, AKLT.W.H3C051.main, AKLT.W.H3C052.main,
   AKLT.W.H3C012.main, AKLT.W.H3C013.main, AKLT.W.H3C014.main⟩

/-- Shared semantic facts for all five stationary cases. -/
theorem sharedCaseLeaves : SharedCaseLeaves :=
  ⟨AKLT.W.H3C025.main, AKLT.W.H3C028.main, AKLT.W.H3C034.main,
   AKLT.W.H3C035.main, AKLT.W.H3C036.main, AKLT.W.H3C038.main⟩

/-- The closed stationary interface consumed by the generated case assemblies. -/
theorem productionCaseLeaves : ProductionCaseLeaves :=
  ⟨sharedCaseLeaves, AKLT.W.H3C045.main, AKLT.W.H3C041.main, AKLT.W.H3C046.main⟩

#print axioms AKLT.W.H3C001.main
#print axioms AKLT.W.H3C002.main
#print axioms AKLT.W.H3C003.main
#print axioms AKLT.W.H3C004.main
#print axioms AKLT.W.H3C005.main
#print axioms AKLT.W.H3C006.main
#print axioms AKLT.W.H3C007.main
#print axioms AKLT.W.H3C008.main
#print axioms AKLT.W.H3C009.main
#print axioms AKLT.W.H3C010.main
#print axioms AKLT.W.H3C011.main
#print axioms AKLT.W.H3C012.main
#print axioms AKLT.W.H3C013.main
#print axioms AKLT.W.H3C014.main
#print axioms AKLT.W.H3C015.main
#print axioms AKLT.W.H3C016.main
#print axioms AKLT.W.H3C017.main
#print axioms AKLT.W.H3C018.main
#print axioms AKLT.W.H3C019.main
#print axioms AKLT.W.H3C020.main
#print axioms AKLT.W.H3C021.main
#print axioms AKLT.W.H3C022.main
#print axioms AKLT.W.H3C023.main
#print axioms AKLT.W.H3C024.main
#print axioms AKLT.W.H3C025.main
#print axioms AKLT.W.H3C026.main
#print axioms AKLT.W.H3C027.main
#print axioms AKLT.W.H3C028.main
#print axioms AKLT.W.H3C029.main
#print axioms AKLT.W.H3C030.main
#print axioms AKLT.W.H3C031.main
#print axioms AKLT.W.H3C032.main
#print axioms AKLT.W.H3C033.main
#print axioms AKLT.W.H3C034.main
#print axioms AKLT.W.H3C035.main
#print axioms AKLT.W.H3C036.main
#print axioms AKLT.W.H3C037.main
#print axioms AKLT.W.H3C038.main
#print axioms AKLT.W.H3C039.main
#print axioms AKLT.W.H3C040.main
#print axioms AKLT.W.H3C041.main
#print axioms AKLT.W.H3C042.main
#print axioms AKLT.W.H3C043.main
#print axioms AKLT.W.H3C044.main
#print axioms AKLT.W.H3C045.main
#print axioms AKLT.W.H3C046.main
#print axioms AKLT.W.H3C047.main
#print axioms AKLT.W.H3C048.main
#print axioms AKLT.W.H3C049.main
#print axioms AKLT.W.H3C050.main
#print axioms AKLT.W.H3C051.main
#print axioms AKLT.W.H3C052.main
#print axioms AKLT.W.H3C053.main
#print axioms AKLT.W.H3C054.main
#print axioms AKLT.W.H3C055.main
#print axioms AKLT.W.H3C056.main

#print axioms automatonLeaves
#print axioms sharedCaseLeaves
#print axioms productionCaseLeaves

end CertData.H3.Close

