import AKLT.Gen.Packed.Bench.Scale1000000R1
namespace AKLT.Gen.Packed.Bench.Kernel1000000R100
set_option trace.profiler true in
set_option trace.profiler.threshold 0 in
 theorem checked : rowsCheck 79 12500 24 3 2 100 Scale1000000R1.A Scale1000000R1.B = true := by decide +kernel
#print axioms checked
end AKLT.Gen.Packed.Bench.Kernel1000000R100
