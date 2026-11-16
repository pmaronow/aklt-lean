import AKLT.Gen.Packed.Bench.Scale100000R1
namespace AKLT.Gen.Packed.Bench.Kernel100000R10
set_option trace.profiler true in
set_option trace.profiler.threshold 0 in
 theorem checked : rowsCheck 79 1250 24 3 2 10 Scale100000R1.A Scale100000R1.B = true := by decide +kernel
#print axioms checked
end AKLT.Gen.Packed.Bench.Kernel100000R10
