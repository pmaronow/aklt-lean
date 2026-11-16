import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def zipSum : List Nat → List Nat → Nat
  | a::as, b::bs => a*b + zipSum as bs
  | _, _ => 0

def indexedSum (xs : List Nat) : List Nat → Nat
  | [] => 0
  | i::is => xs.getD i 0 + indexedSum xs is
theorem checked : zipSum (List.range 1000) (List.replicate 1000 1) = 499500 := by decide +kernel
#print axioms checked
