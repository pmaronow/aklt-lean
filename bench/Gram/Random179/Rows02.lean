import AKLT.Gen.Gram.Random179.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Random179
theorem rows2_checked : checkRows lData 1 1 16 m2 l2 = true := by
  decide +kernel
#print axioms rows2_checked
end AKLT.Gen.Gram.Random179
