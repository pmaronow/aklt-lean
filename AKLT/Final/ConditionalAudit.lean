import AKLT.Final.Conditional

/-! The exact certificate boundary, in the order of mainV2_of_open. -/

example : AKLT.Blueprint.Top.H1FiniteDataStatementV2 →
    AKLT.Blueprint.Top.CertificateStatement →
    AKLT.Blueprint.Top.Automaton10StatementV2 →
    AKLT.Blueprint.Top.StationaryCheckStatementV2 →
    AKLT.Challenge.MainStatementV2 := @AKLT.Final.main_of_certificates

#print axioms AKLT.Final.main_of_certificates

set_option pp.proofs true in
#print AKLT.Final.main_of_certificates
