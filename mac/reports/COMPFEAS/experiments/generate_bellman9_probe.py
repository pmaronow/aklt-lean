from pathlib import Path
import random
root=Path(__file__).resolve().parents[1]
n=25921;b=84;B=1<<b;allmask=(1<<(n*b))-1;ones=allmask//(B-1);guard=ones*(1<<(b-1));upper=ones*((1<<30)-1)
rng=random.Random(76);v=sum(rng.randrange(1<<29,1<<30)<<(b*i) for i in range(n))
header='import Mathlib\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
for name,value in [('plane',v),('allMask',allmask),('guard',guard),('upper',upper)]:header+=f'def {name} : Nat := 0x{value:x}\n'
header+='''
def rotate (p : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftLeft p 84) allMask) (Nat.shiftRight p 2177280)
def rowOK (p : Nat) : Bool :=
  let lhs := p * 93824992236886 + rotate p * 93824992236886
  let rhs := upper * 281474976710656
  Nat.land (guard + rhs - lhs) guard == guard

def rows : Nat → Nat → Bool
  | 0, _ => true
  | n+1, p => rowOK p && rows n (rotate p)
'''
for k in [1,16]:
 (root/'probes'/f'Bellman9Guard{k}.lean').write_text(header+f'theorem checked : rows {k} plane = true := by decide +kernel\n#print axioms checked\n')
