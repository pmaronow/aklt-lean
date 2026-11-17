#!/usr/bin/env python3
"""Generate one small frontier shard; all its mathematical claims are rechecked in Lean."""
from fractions import Fraction as F
import array, gzip, importlib.util, json, math, os, pathlib, struct, sys
HERE=pathlib.Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('exporter',HERE/'export.py')
ex=importlib.util.module_from_spec(spec);spec.loader.exec_module(ex)
dx=[1,0,-1,0];dy=[0,1,0,-1]
stem=[1,0,1,2,3,2,3,0,3,0]
xs,xt=F(1000,961),F(200,187)
alpha=[F(145217,10**6),F(150000,10**6)]
beta=[F(352782,10**6),F(357549,10**6)]
bp=[F(340008,10**6),F(344661,10**6)]
h=F(5404319552844595,4503599627370496)

def hp(a,b): return F(1) if dx[a]==dx[b] or dy[a]==dy[b] else h
def reward(ain,d,dead):
    other=[j for j in range(4) if j not in [(ain+2)%4,d]]
    live=[j for j in other if not dead[j]];ty=int(d!=ain)
    if not live:return F(0)
    if len(live)==1:return bp[ty]*hp(live[0],d)
    return alpha[ty]*hp(*live)+beta[ty]*(hp(live[0],d)+hp(live[1],d))

weights=[F(1,3),F(1,5),xs/3,xt/3]
for a in range(4):
    for d in range(4):
        if d==(a+2)%4:continue
        for mask in range(16):
            weights.append((xs if a==d else xt)*reward(a,d,[(mask>>j)&1 for j in range(4)])/3)
D=math.lcm(*(v.denominator for v in weights))

def code(ds):
    c=0
    for d in ds:c=c*4+d
    return c
def evaluate(ds):
    x,y=-1,0;ain=2;used=set();depart={};ph=[1,1,0,0];items=[];nr=0
    valid=True;hit=None
    for i,d in enumerate(ds):
        xx,yy=x+dx[d],y+dy[d]
        ed=tuple(sorted(((x,y),(xx,yy))))
        if ed in used or (i==0 and d==0) or (xx,yy)==(0,0):valid=False
        if (xx,yy)==(1,0) and hit is None:hit=i+1
        prior=depart.get((x,y),0)
        if prior:
            ph=[v*(D//5) for v in ph];nr+=1
        else:
            dead=[(x+dx[j],y+dy[j])==(0,0) or depart.get((x+dx[j],y+dy[j]),0)>=2 for j in range(4)]
            # Invalid reversals are never evaluated by the checked semantic branch.
            if d==(ain+2)%4: valid=False; k=F(0)
            else:k=reward(ain,d,dead)
            ty=int(d!=ain);xxf=xt if ty else xs;items.append((ty,k,i))
            w=int(xxf*k/3*D)
            PA,PB,QC,QD=ph
            if ty:ph=[PA*int(xt/3*D),PB*(D//3),QC*(D//3)+PA*w,QD*(D//3)]
            else:ph=[PA*int(xs/3*D),PB*int(xs/3*D),QC*int(xs/3*D),QD*(D//3)+PB*w]
        depart[x,y]=prior+1;used.add(ed);x,y=xx,yy;ain=d
    surviving=valid and hit is None
    closed=valid and hit==len(ds)
    short=F(0)
    if closed:
        # Same exact score and path-index tie break as kernelOrdering.
        items.sort(key=lambda e:(e[1]==0,(F(1)-1/(xt if e[0] else xs))/e[1] if e[1] else F(0),e[2]))
        pref=F(1)
        for ty,k,i in items:
            xx=xt if ty else xs;short+=pref*xx*k;pref*=xx
        short*=F(3,5)**nr/F(3)**len(ds)
    return dict(surviving=surviving,closed=closed,point=(x,y),ph=ph,short=short)

mapping,reps=ex.read_windows()
leaves=[evaluate(stem+[i//4,i%4]) for i in range(16)]
for i,r in enumerate(leaves):
    r['class']=mapping.get(code((stem+[i//4,i%4])[-10:]),0)
    r['site']=(r['point'][0]+70)*141+r['point'][1]+70
needed={(r['class'],r['site']) for r in leaves if r['surviving']}
vals={}
with gzip.open(ex.ARCHIVE/'stationary_B_m10_R70_d1_coarse.bin.gz','rb') as f:
    assert struct.unpack('<9q',f.read(72))==(10,12,70,3741,19881,1,0,16,1)
    f.read(16*3741)
    for p in range(4):
        for a in range(3741):
            raw=f.read(19881*4)
            for aa,s in needed:
                if aa==a: vals[p,a,s]=struct.unpack_from('<I',raw,s*4)[0]
    assert f.read(1)==b''
for r in leaves:
    r['values']=[vals.get((p,r['class'],r['site']),0) for p in range(4)]

survivalMask=sum(1<<i for i,r in enumerate(leaves) if r['surviving'])
phaseBits=max(v.bit_length() for r in leaves for v in r['ph'])
phaseBits=max(phaseBits,1)
numerator=sum(sum(a*b for a,b in zip(r['ph'],r['values'])) for r in leaves if r['surviving'])
denominator=D**12*65536
short=sum((r['short'] for r in leaves),F(0))
assert not any(evaluate(stem+[i])['closed'] for i in range(4))

s='module\n\npublic import CertData.H3.Kernel.Common\npublic import CertData.H3.Kernel.Literal\n'+ex.HEADER
s+='namespace AKLT.Cert.H3.Data.PrefixBN\nopen AKLT.Defs AKLT.Gen.Packed\n'
for name,n in [('stemCode',code(stem)),('stepDenominator',D),('survivalMask',survivalMask),
    ('phaseBits',phaseBits),('phaseNumerators',ex.pack_fields([v for r in leaves for v in r['ph']],phaseBits)),
    ('endpointClasses',ex.pack_fields([r['class'] for r in leaves],12)),
    ('endpointSites',ex.pack_fields([r['site'] for r in leaves],15)),
    ('endpointValues',ex.pack_fields([v for r in leaves for v in r['values']],32)),
    ('expectedNumerator',numerator),('shortNumerator',short.numerator),('shortDenominator',short.denominator)]:
    s+=f'def {name} : Nat := {ex.literal(n)}\n'
s+='''def word (e : Fin 16) : DirectionWord 12 := decodeWord 12 (stemCode*16+e.val)
def word11 (e : Fin 4) : DirectionWord 11 := decodeWord 11 (stemCode*4+e.val)
def survives (e : Fin 16) : Bool := survivalMask.testBit e.val
def endpointClass (e : Fin 16) : Fin 3741 := ⟨lane endpointClasses 12 e.val % 3741, Nat.mod_lt _ (by decide)⟩
def endpointSite (e : Fin 16) : Nat := lane endpointSites 15 e.val
def endpointValue (e : Fin 16) (φ : Phase) : Nat := lane endpointValues 32 (e.val*4+phaseCode φ)
def phaseNumerator (e : Fin 16) (φ : Phase) : Nat := lane phaseNumerators phaseBits (e.val*4+phaseCode φ)
def shardNumerator : Nat := ∑ e : Fin 16, if survives e then
  ∑ φ : Phase, phaseNumerator e φ * endpointValue e φ else 0
end AKLT.Cert.H3.Data.PrefixBN
'''
ex.write_source(ex.LEGACY_DATA/'PrefixBN.lean',s)
stats=dict(stem=stem,step_denominator=str(D),step_denominator_bits=D.bit_length(),phase_bits=phaseBits,
           surviving=[i for i,r in enumerate(leaves) if r['surviving']],closed=[i for i,r in enumerate(leaves) if r['closed']],
           tail_numerator=str(numerator),tail_denominator=str(denominator),short=str(short),shard_value=str(short+F(numerator,denominator)))
report=pathlib.Path(os.environ.get('H3_REPORT_DIR','/home/ubuntu/aklt/reports/REGEN_H3'))
report.mkdir(parents=True,exist_ok=True)
(report/'prefix_manifest.json').write_text(json.dumps(stats,indent=2)+'\n')
print(json.dumps(stats,indent=2))
