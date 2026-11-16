from pathlib import Path
import json,random,sys
sys.set_int_max_str_digits(0)
root=Path(__file__).resolve().parents[1];out=root/'probes';out.mkdir(exist_ok=True)
head='import Mathlib\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n\n'
# This is a stand-alone finite check from the bond-trail definition, with a proposed integer vector.
H={r['code']:r['h'] for r in json.load(open(root/'data/h2_exact_m6k1_r5.json'))['rows']}
def encode(ds):return sum(d*4**i for i,d in enumerate(ds))
def canon(ds):return min(encode([(sg*d+r)%4 for d in ds]) for sg in [1,-1] for r in range(4))
dx=[1,0,-1,0];dy=[0,1,0,-1];vec={}
def gen(ds,x,y,used):
 if len(ds)==6:vec[encode(ds)]=H[canon(ds)];return
 for d in range(4):
  b=tuple(sorted(((x,y),(x+dx[d],y+dy[d]))))
  if b not in used:gen(ds+[d],x+dx[d],y+dy[d],used|{b})
gen([],0,0,set())
def tree(items):
 if not items:return '0'
 j=len(items)//2;c,h=items[j]
 return f'(if c < {c} then {tree(items[:j])} else if c == {c} then {h} else {tree(items[j+1:])})'
s=head+'''namespace CompfeasH2
abbrev Point := Int × Int
structure Walk where
  pos : Point
  dirs : List Nat
  edges : List (Point × Point)
  departed : List Point

def eqP (a b : Point) : Bool := a.1 == b.1 && a.2 == b.2

def move (p : Point) (d : Nat) : Point :=
  match d with
  | 0 => (p.1 + 1, p.2)
  | 1 => (p.1, p.2 + 1)
  | 2 => (p.1 - 1, p.2)
  | _ => (p.1, p.2 - 1)

def used (es : List (Point × Point)) (a b : Point) : Bool :=
  es.any (fun e => (eqP e.1 a && eqP e.2 b) || (eqP e.1 b && eqP e.2 a))

def extend (s : Walk) (d : Nat) : Walk :=
  { pos := move s.pos d, dirs := s.dirs ++ [d],
    edges := (s.pos, move s.pos d) :: s.edges, departed := s.pos :: s.departed }

def grow : Nat → Walk → List Walk
  | 0, s => [s]
  | n + 1, s => [0, 1, 2, 3].flatMap (fun d =>
      if used s.edges s.pos (move s.pos d) then [] else grow n (extend s d))

def encAux : List Nat → Nat → Nat → Nat
  | [], _, a => a
  | d :: ds, p, a => encAux ds (4*p) (a+d*p)
def enc (ds : List Nat) : Nat := encAux ds 1 0

def witness (c : Nat) : Nat :=
'''+tree(sorted(vec.items()))+'''

def rowOK (s : Walk) : Bool :=
  let hv := witness (enc s.dirs)
  let rev := s.departed.any (fun p => eqP p s.pos)
  let last := s.dirs.reverse.headD 0
  let total := [0, 1, 2, 3].foldl (fun acc d =>
    if used s.edges s.pos (move s.pos d) then acc else
      let num := if rev then 539121 else if d == last then 935000 else 961000
      acc + num * witness (enc (s.dirs.drop 1 ++ [d]))) 0
  Nat.ble 1 hv && Nat.ble (2500*total) (2499*2695605*hv)

def check : Bool :=
  let ws := grow 6 { pos := (0, 0), dirs := [], edges := [], departed := [] }
  (ws.length == 916) && ws.all rowOK

theorem checked : check = true := by decide +kernel
#print axioms checked
end CompfeasH2
'''
(out/'H2Small.lean').write_text(s)
for bits,n in [(64,10000),(256,10000),(4096,2000),(16384,200)]:
 P=2**bits-159
 s=head+f'def modulus : Nat := {P}\n'+'''def natLoop : Nat → Nat → Nat
  | 0, x => x
  | n+1, x =>
    let y := (x*x + 17*x + 19) % modulus
    let g := Nat.gcd (y+1) (x+2)
    natLoop n ((y+g) % modulus)
'''+f'theorem checked : natLoop {n} {2**(bits-1)+13} < modulus := by decide +kernel\n#print axioms checked\n'
 (out/f'Nat{bits}.lean').write_text(s)
for bits,n in [(64,10000),(4096,2000)]:
 s=head+f'def modulus : Int := {2**bits-159}\n'+'''def intLoop : Nat → Int → Int
  | 0, x => x
  | n+1, x => intLoop n (-((x*x + 17*x - 13) % modulus))
'''+f'theorem checked : (intLoop {n} (-{2**(bits-1)+13})).natAbs < modulus.natAbs := by decide +kernel\n#print axioms checked\n'
 (out/f'Int{bits}.lean').write_text(s)
for n in [1000,4000]:
 base=head+'''def zipSum : List Nat → List Nat → Nat
  | a::as, b::bs => a*b + zipSum as bs
  | _, _ => 0

def indexedSum (xs : List Nat) : List Nat → Nat
  | [] => 0
  | i::is => xs.getD i 0 + indexedSum xs is
'''
 (out/f'ListZip{n}.lean').write_text(base+f'theorem checked : zipSum (List.range {n}) (List.replicate {n} 1) = {n*(n-1)//2} := by decide +kernel\n#print axioms checked\n')
 (out/f'ListIndex{n}.lean').write_text(base+f'theorem checked : indexedSum (List.range {n}) (List.range {n}) = {n*(n-1)//2} := by decide +kernel\n#print axioms checked\n')
# Fixed point packing: the two incoming weighted planes have total coefficient one.
K=25;sites=2*K*K;w=160;sbits=48;B=1<<w;mask=(1<<(w*sites))-1;ones=mask//(B-1)
def fields(ids):return sum((B-1)<<(w*i) for i in ids)
consts=dict(allMask=mask,roundBias=ones*((1<<sbits)-1),lowMask=ones*((1<<(w-sbits))-1),highMask=ones*((B-1)^((1<<96)-1)),evenMask=fields(i for i in range(sites) if (i//K)%2==0),oddMask=fields(i for i in range(sites) if (i//K)%2==1),lastMask=fields(range(K-1,sites,K)),notLastMask=mask^fields(range(K-1,sites,K)))
rng=random.Random(20261115);packed=sum(rng.randrange(1<<62,1<<64)<<(w*i) for i in range(sites));consts['inputPlane']=packed
body=head+''.join(f'def {k} : Nat := 0x{v:x}\n' for k,v in consts.items())+'''
def east (p : Nat) : Nat :=
  let odd := Nat.land p oddMask
  let shifted := Nat.lor (Nat.shiftLeft (Nat.land odd notLastMask) 160)
      (Nat.shiftRight (Nat.land odd lastMask) 3840)
  let a := Nat.lor (Nat.land p evenMask) shifted
  Nat.lor (Nat.land (Nat.shiftLeft a 4000) allMask) (Nat.shiftRight a 196000)

def oneStep (p : Nat) : Nat :=
  let numerator := p * 140737488355328 + east p * 140737488355328
  Nat.land (Nat.shiftRight (numerator + roundBias) 48) lowMask

def packedLoop : Nat → Nat → Nat
  | 0, p => p
  | n+1, p => packedLoop n (oneStep p)
'''
for n in [1,16,128]:
 (out/f'Packed{n}.lean').write_text(body+f'theorem checked : Nat.land (packedLoop {n} inputPlane) highMask = 0 := by decide +kernel\n#print axioms checked\n')
# An actual dyadic Gram-residual certificate, supplied as data for timing only.
files=list((root/'data').glob('h1_chol_*_*.json'))
if files:
 r=json.load(open(max(files,key=lambda p:json.load(open(p))['n'])))
 def lst(x):return '['+', '.join(lst(v) if isinstance(v,list) else str(v) for v in x)+']'
 M=r['M'];L=[[int(x) for x in row[:i+1]] for i,row in enumerate(r['L'])]
 factor=r['shift_den']*(2**r['precision'])**2
 s=head+f'def mData : List (List Int) := {lst(M)}\ndef lData : List (List Int) := {lst(L)}\ndef factor : Int := {factor}\n'+'''
def dotI : List Int → List Int → Int
  | a::as, b::bs => a*b + dotI as bs
  | _, _ => 0

def offSum (diag : Nat) : Nat → List Int → Nat
  | _, [] => 0
  | j, x::xs => (if j == diag then 0 else x.natAbs) + offSum diag (j+1) xs

def checkRows (whole : List (List Int)) : Nat → List (List Int) → List (List Int) → Bool
  | _, [], [] => true
  | i, mr::ms, lr::ls =>
    let er := mr.zipWith (fun a l => a*factor-dotI lr l) whole
    let diagonal := er.getD i 0
    (mr.length == whole.length) && decide (0 < diagonal) &&
      Nat.ble (offSum i 0 er + 1) diagonal.natAbs && checkRows whole (i+1) ms ls
  | _, _, _ => false

def check : Bool := checkRows lData 0 mData lData

theorem checked : check = true := by decide +kernel
#print axioms checked
'''
 (out/'H1Gram.lean').write_text(s)
(out/'Baseline.lean').write_text('import Mathlib\n')
print('probe files',len(list(out.glob('*.lean'))),'H1 n',r['n'] if files else None)
