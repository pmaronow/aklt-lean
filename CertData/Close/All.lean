module
public import CertData.H1.Close.Main
public import CertData.H3.Close.Main
public import AKLT.Final.Conditional
public import AKLT.Blueprint.H1.Assembly
public import AKLT.Blueprint.H3.AssemblyV2
public import AKLT.Cert.H2.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

set_option maxRecDepth 100000

/-! Closed analytic inputs and headline, composed from the accepted certificate
proofs and the existing assemblies with their merged mathematical leaves. -/

namespace CertData.Close

/-- The analytic H1 input from the two closed H1 certificate contracts. -/
theorem h1 : AKLT.Blueprint.Top.H1Statement :=
  AKLT.Blueprint.H1.h1_of_theorem
    (AKLT.Blueprint.H1.h1Theorem_of_certificate
      CertData.H1.Close.certificate CertData.H1.Close.finiteData)

/-- The existing closed H2 input. -/
theorem h2 : AKLT.Blueprint.Top.H2Statement :=
  AKLT.Cert.H2.h2

/-- The analytic H3 input from all merged analytic leaves and both finite checks. -/
theorem h3 : AKLT.Blueprint.Top.H3Statement :=
  AKLT.Blueprint.H3.h3_of_leaves_and_checksV2
    ⟨AKLT.W.H3M001.main,
     AKLT.W.H3M002.main,
     AKLT.W.H3M003.main,
     AKLT.W.H3M004.main,
     AKLT.W.H3M005.main,
     AKLT.W.H3M006.main,
     AKLT.W.H3M007.main,
     AKLT.W.H3M008.main,
     AKLT.W.H3M009.main,
     AKLT.W.H3M010.main,
     AKLT.W.H3M011.main,
     AKLT.W.H3M012.main,
     AKLT.W.H3M013.main,
     AKLT.W.H3M014.main,
     AKLT.W.H3M015.main,
     AKLT.W.H3M016.main,
     AKLT.W.H3M017.main,
     AKLT.W.H3M018.main,
     AKLT.W.H3M019.main,
     AKLT.W.H3M020.main,
     AKLT.W.H3M021.main,
     AKLT.W.H3M022.main,
     AKLT.W.H3M023.main,
     AKLT.W.H3M024.main,
     AKLT.W.H3M025.main,
     AKLT.W.H3M026.main,
     AKLT.W.H3M027.main,
     AKLT.W.H3M028.main,
     AKLT.W.H3M029.main,
     AKLT.W.H3M030.main⟩
    ⟨AKLT.W.H3M031.main, AKLT.W.H3M032.main, AKLT.W.H3M033.main, AKLT.W.H3M034.main, AKLT.W.H3M035.main⟩
    CertData.H3.Close.automaton10 CertData.H3.Close.stationaryCheck

/-- The headline with all four finite certificate contracts discharged. -/
theorem main : AKLT.Challenge.MainStatementV2 :=
  AKLT.Final.main_of_certificates
    CertData.H1.Close.finiteData CertData.H1.Close.certificate
    CertData.H3.Close.automaton10 CertData.H3.Close.stationaryCheck

example : AKLT.Blueprint.Top.H1Statement := h1
example : AKLT.Blueprint.Top.H2Statement := h2
example : AKLT.Blueprint.Top.H3Statement := h3
example : AKLT.Challenge.MainStatementV2 := main

#print h1
#print h2
#print h3
#print main
#print axioms h1
#print axioms h2
#print axioms h3
#print axioms main

end CertData.Close

