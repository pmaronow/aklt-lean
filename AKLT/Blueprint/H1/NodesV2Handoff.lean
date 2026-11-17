module
public import AKLT.Blueprint.H1.NodesV2Structure
public import AKLT.Blueprint.Top.InputsV2

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs

namespace AKLT.Blueprint.H1

/-- Alias to the repaired SHARED witness predicate, not a new certificate model. -/
abbrev SharedSectorWitnessesV2 := AKLT.Defs.H1SectorWitnesses

/-- Alias to the repaired SHARED external data obligation. The old H1-local
declaration remains frozen for legacy users and is definitionally compatible. -/
abbrev SharedH1FiniteDataV2 : Prop := AKLT.Blueprint.Top.H1FiniteDataStatementV2

abbrev SharedCertificateV2 : Prop := AKLT.Blueprint.Top.CertificateStatementV2

/-- Canonical decomposition indices fix unused signs, as required by the referee.
The certificate premise still quantifies all signs; duplicate checks are harmless.
No orthogonality or normalization theorem is asserted here. -/
abbrev EffectiveSectorSignsV2 (π : PatternData) (r : Representation) :=
  {ε : ExchangeSigns π // AKLT.Defs.EffectiveExchangeSigns π r ε}

/-- The other lanes' closed inputs for the repaired global input package. This is
only packaging, not an additional leaf or a claim of completed H2/H3 data checks. -/
def OtherInputPartsV2 : Prop :=
  AKLT.Blueprint.Top.H2Statement ∧ AKLT.Blueprint.Top.H3Statement ∧
    certifiedRate < (2499 / 2500 : ℚ) ∧ (2499 / 2500 : ℚ) < 1 ∧
    AKLT.Blueprint.Top.Automaton10StatementV2 ∧ AKLT.Blueprint.Top.StationaryCheckStatementV2

end AKLT.Blueprint.H1
