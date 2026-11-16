import AKLT.Gen.Gram.Random179.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Random179
theorem rows14_checked : checkRows lData 1 1 112 m14 l14 = true := by
  decide +kernel
#print axioms rows14_checked
end AKLT.Gen.Gram.Random179
