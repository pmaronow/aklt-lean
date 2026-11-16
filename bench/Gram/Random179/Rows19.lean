import AKLT.Gen.Gram.Random179.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Random179
theorem rows19_checked : checkRows lData 1 1 152 m19 l19 = true := by
  decide +kernel
#print axioms rows19_checked
end AKLT.Gen.Gram.Random179
