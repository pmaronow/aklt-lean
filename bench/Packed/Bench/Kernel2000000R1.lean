import AKLT.Gen.Packed.Bench.Scale2000000R1
namespace AKLT.Gen.Packed.Bench.Kernel2000000R1
set_option trace.profiler true in
set_option trace.profiler.threshold 0 in
 theorem checked : rowsCheck 79 25000 24 3 2 1 Scale2000000R1.A Scale2000000R1.B = true := by decide +kernel
#print axioms checked
end AKLT.Gen.Packed.Bench.Kernel2000000R1
