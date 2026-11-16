import AKLT.Gen.Gram.Sample131.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace AKLT.Gen.Gram.Sample131
theorem header_checked : header mData lData 1 1 1 = true := by decide +kernel
#print axioms header_checked
end AKLT.Gen.Gram.Sample131
