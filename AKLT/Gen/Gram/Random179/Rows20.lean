import AKLT.Gen.Gram.Random179.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Random179
theorem rows20_checked : checkRows lData 1 1 160 m20 l20 = true := by
  decide +kernel
#print axioms rows20_checked
end AKLT.Gen.Gram.Random179
