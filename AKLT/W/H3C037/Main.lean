module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C037

open AKLT.Cert.H3.Production CertData.H3.Bridge

theorem main : CertData.H3.Bridge.NumericScaleLeaf := by
  intro E hden r
  unfold resultValue finalNumerator finalDenominator
  have hK : (E.denominator : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hden)
  push_cast
  field_simp [hK]

#print axioms main

end AKLT.W.H3C037
