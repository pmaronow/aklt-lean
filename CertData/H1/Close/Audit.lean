import CertData.H1.Close.Main
import AKLT.Final.Conditional

/-! Import-only audit of the closed H1 proofs and their final-project interface. -/
namespace CertData.H1.Close.Audit

example : AKLT.Blueprint.Top.H1FiniteDataStatementV2 :=
  CertData.H1.Close.finiteData

example : AKLT.Blueprint.Top.CertificateStatement :=
  CertData.H1.Close.certificate

-- Applying the final project assembly discharges both H1 arguments.
-- Its two remaining arguments belong to the separate H3 lane.
example : AKLT.Blueprint.Top.Automaton10StatementV2 →
    AKLT.Blueprint.Top.StationaryCheckStatementV2 → AKLT.Challenge.MainStatementV2 :=
  AKLT.Final.main_of_certificates CertData.H1.Close.finiteData CertData.H1.Close.certificate

#print axioms CertData.H1.Close.finiteData
#print axioms CertData.H1.Close.certificate

end CertData.H1.Close.Audit
