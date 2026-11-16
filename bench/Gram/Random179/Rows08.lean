import AKLT.Gen.Gram.Random179.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Random179
theorem rows8_checked : checkRows lData 1 1 64 m8 l8 = true := by
  decide +kernel
#print axioms rows8_checked
end AKLT.Gen.Gram.Random179
