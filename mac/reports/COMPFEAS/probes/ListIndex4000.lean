import Mathlib
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

def zipSum : List Nat → List Nat → Nat
  | a::as, b::bs => a*b + zipSum as bs
  | _, _ => 0

def indexedSum (xs : List Nat) : List Nat → Nat
  | [] => 0
  | i::is => xs.getD i 0 + indexedSum xs is
theorem checked : indexedSum (List.range 4000) (List.range 4000) = 7998000 := by decide +kernel
#print axioms checked
