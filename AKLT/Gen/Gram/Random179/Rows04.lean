import AKLT.Gen.Gram.Random179.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Random179
theorem rows4_checked : checkRows lData 1 1 32 m4 l4 = true := by
  decide +kernel
#print axioms rows4_checked
end AKLT.Gen.Gram.Random179
