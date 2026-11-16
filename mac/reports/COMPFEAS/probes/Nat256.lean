import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def modulus : Nat := 115792089237316195423570985008687907853269984665640564039457584007913129639777
def natLoop : Nat → Nat → Nat
  | 0, x => x
  | n+1, x =>
    let y := (x*x + 17*x + 19) % modulus
    let g := Nat.gcd (y+1) (x+2)
    natLoop n ((y+g) % modulus)
theorem checked : natLoop 10000 57896044618658097711785492504343953926634992332820282019728792003956564819981 < modulus := by decide +kernel
#print axioms checked
