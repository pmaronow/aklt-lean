import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def modulus : Int := 18446744073709551457
def intLoop : Nat → Int → Int
  | 0, x => x
  | n+1, x => intLoop n (-((x*x + 17*x - 13) % modulus))
theorem checked : (intLoop 10000 (-9223372036854775821)).natAbs < modulus.natAbs := by decide +kernel
#print axioms checked
