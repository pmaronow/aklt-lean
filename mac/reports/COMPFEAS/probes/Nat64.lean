import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def modulus : Nat := 18446744073709551457
def natLoop : Nat → Nat → Nat
  | 0, x => x
  | n+1, x =>
    let y := (x*x + 17*x + 19) % modulus
    let g := Nat.gcd (y+1) (x+2)
    natLoop n ((y+g) % modulus)
theorem checked : natLoop 10000 9223372036854775821 < modulus := by decide +kernel
#print axioms checked
