import AKLT.Gen.Gram.Random179.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Random179
theorem rows5_checked : checkRows lData 1 1 40 m5 l5 = true := by
  decide +kernel
#print axioms rows5_checked
end AKLT.Gen.Gram.Random179
