import AKLT.Gen.Gram.Random179.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Random179
theorem rows21_checked : checkRows lData 1 1 168 m21 l21 = true := by
  decide +kernel
#print axioms rows21_checked
end AKLT.Gen.Gram.Random179
