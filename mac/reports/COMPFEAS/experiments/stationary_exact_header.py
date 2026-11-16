from fractions import Fraction as F
from pathlib import Path
root=Path(__file__).resolve().parents[1]
S=2**48;h=F(5404319552844595,4503599627370496);xs=F(1000,961);xt=F(200,187)
ca=[F(145217,10**6),F(150000,10**6)];cb=[F(352782,10**6),F(357549,10**6)];bp=[F(340008,10**6),F(344661,10**6)]
dx=[1,0,-1,0];dy=[0,1,0,-1]
def ceil(q):return (q.numerator*S+q.denominator-1)//q.denominator
def resp(ain,d,dead):
 if d==(ain+2)%4:return 0
 f,g=[j for j in range(4) if j not in [(ain+2)%4,d]];ty=int(d!=ain)
 pair=lambda a,b: F(1) if dx[a]==dx[b] or dy[a]==dy[b] else h
 if dead==f:k=bp[ty]*pair(g,d)
 elif dead==g:k=bp[ty]*pair(f,d)
 else:k=ca[ty]*pair(f,g)+cb[ty]*(pair(f,d)+pair(g,d))
 return ceil((xs if d==ain else xt)*k/3)
s='#include <zlib.h>\n#define QSCALE (UINT64_C(1)<<48)\n'
s+=f'static const uint64_t qs={ceil(xs/3)},qt={ceil(xt/3)},q3={ceil(F(1,3))},q5={ceil(F(1,5))};\n'
s+='static const uint64_t qresp[4][4][5] = {\n'
for ain in range(4):s+='{'+','.join('{'+','.join(str(resp(ain,d,de)) for de in range(5))+'}' for d in range(4))+'},\n'
s+='};\n';(root/'experiments/stationary_weights.h').write_text(s)
