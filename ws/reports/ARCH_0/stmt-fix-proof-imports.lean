import AKLT.Blueprint.Top.All
import AKLT.Cert.H2.Main
import AKLT.Uniq.Main

#check (AKLT.Cert.H2.h2 : AKLT.Blueprint.Top.H2Statement)
#check (AKLT.Cert.H2.alm : AKLT.Blueprint.Top.ALMStatement)
#check (AKLT.Cert.H2.h2Test : AKLT.Blueprint.Top.H2TestStatement)
#check (AKLT.Cert.H2.h2CV : AKLT.Blueprint.Top.H2CVStatement)
#check AKLT.Uniq.uniqueness
#print axioms AKLT.Cert.H2.h2
#print axioms AKLT.Uniq.uniqueness
