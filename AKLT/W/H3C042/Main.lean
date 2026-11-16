import CertData.H3.Bridge.Interface

namespace AKLT.W.H3C042

theorem main : CertData.H3.Bridge.ResultAddLeaf := by
  intro E r s
  simp only [CertData.H3.Bridge.resultValue, AKLT.Cert.H3.Production.PrefixResult.add]
  push_cast
  ring_nf

end AKLT.W.H3C042

#print axioms AKLT.W.H3C042.main
