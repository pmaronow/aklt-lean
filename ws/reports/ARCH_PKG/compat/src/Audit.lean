import Solution

-- These are all theorems exported by Solution, and the one new tree theorem.
#print axioms AKLT.Final.main_of_inputs
#print axioms AKLTPalomar.h1_iff
#print axioms AKLTPalomar.h3_iff
#print axioms AKLTPalomar.main_iff
#print axioms AKLTPalomar.aklt_gap_of_inputs

-- Exact signatures keep the premise count visible in the audit transcript.
#check (AKLT.Final.main_of_inputs : AKLT.Blueprint.Top.H1Statement →
  AKLT.Blueprint.Top.H3Statement → AKLT.Challenge.MainStatementV2)
#check (AKLTPalomar.aklt_gap_of_inputs : AKLTPalomar.H1 →
  AKLTPalomar.H3 → AKLTPalomar.Main)
