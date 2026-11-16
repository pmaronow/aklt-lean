import AKLT.Gen.Gram.Random179.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Random179
theorem rows22_checked : checkRows lData 1 1 176 m22 l22 = true := by
  decide +kernel
#print axioms rows22_checked
end AKLT.Gen.Gram.Random179
