module
public import AKLT.Blueprint.Top.ComputationV2
public import AKLT.Blueprint.Top.Operator

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.Blueprint.Top

/-- `t:inputs`: the original semantic numerical conclusions together with the
explicit H1 witness-coverage handoff and checks for the designated memory-ten
archive and corrected stationary operator. No data check is assumed by importing
this definition. Existing proved H2 and semantic input contracts are unchanged. -/
def InputsStatementV2 : Prop :=
  InputsStatement ∧ H1FiniteDataStatementV2 ∧ Automaton10StatementV2 ∧ StationaryCheckStatementV2

end AKLT.Blueprint.Top
