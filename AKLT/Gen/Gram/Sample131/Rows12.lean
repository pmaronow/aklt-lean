import AKLT.Gen.Gram.Sample131.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Sample131
theorem rows12_checked : checkRows lData 1 1 96 m12 l12 = true := by
  decide +kernel
#print axioms rows12_checked
end AKLT.Gen.Gram.Sample131
