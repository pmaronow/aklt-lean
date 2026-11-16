import AKLT.Gen.Gram.Random179.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Random179
theorem rows18_checked : checkRows lData 1 1 144 m18 l18 = true := by
  decide +kernel
#print axioms rows18_checked
end AKLT.Gen.Gram.Random179
