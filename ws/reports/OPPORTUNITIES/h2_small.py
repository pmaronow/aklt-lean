"""Independent exact rational checks of one-step H2 certificates."""
from fractions import Fraction as F
import json
from pathlib import Path
import time

OUT=Path(__file__).resolve().parent/'experiments'
DX=(1,0,-1,0); DY=(0,1,0,-1)

def windows(m):
    ans=[]
    def dfs(ds,x,y,edges):
        if len(ds)==m:
            ans.append(tuple(ds)); return
        for d in range(4):
            nx=x+DX[d]; ny=y+DY[d]
            e=tuple(sorted(((x,y),(nx,ny))))
            if e in edges: continue
            dfs(ds+[d],nx,ny,edges|{e})
    dfs([],0,0,set())
    return ans

def transitions(ws):
    ix={w:i for i,w in enumerate(ws)}; trs=[]
    for w in ws:
        pos=[(0,0)]
        for d in w: pos.append((pos[-1][0]+DX[d],pos[-1][1]+DY[d]))
        edges={tuple(sorted(e)) for e in zip(pos,pos[1:])}
        x,y=pos[-1]; row=[]
        for d in range(4):
            e=tuple(sorted(((x,y),(x+DX[d],y+DY[d]))))
            if e in edges: continue
            kind=2 if (x,y) in pos[:-1] else (0 if d==w[-1] else 1)
            row.append((ix[w[1:]+(d,)],kind))
        trs.append(row)
    return trs

def canonical(w):
    return min(tuple((sgn*d+r)%4 for d in w) for sgn in (-1,1) for r in range(4))

def test(m,q):
    start=time.monotonic(); ws=windows(m); trs=transitions(ws)
    weights=[F(1000,2883),F(200,561),F(1,5)]
    # Only the candidate search is floating point. The following check is exact.
    fw=list(map(float,weights)); h=[1.]*len(ws)
    for _ in range(4000):
        nh=[sum(fw[k]*h[j] for j,k in row) for row in trs]
        mx=max(nh); nh=[max(v/mx,0.01) for v in nh]
        if max(abs(a-b) for a,b in zip(nh,h))<1e-14: h=nh; break
        h=nh
    vals={canonical(w):max(1,round(h[i]*10**10)) for i,w in enumerate(ws)}
    hn=[vals[canonical(w)] for w in ws]
    ratios=[sum(weights[k]*hn[j] for j,k in row)/hn[i] for i,row in enumerate(trs)]
    lam=max(ratios); passed=lam<=q
    # Crude base W_n <= S^n for n<=m; no trail enumeration is necessary.
    S=weights[0]+2*weights[1]
    cv=F(max(hn),min(hn))*(S/q)**m
    cert=dict(m=m,q=str(q),weights=list(map(str,weights)),
              vector=[dict(directions=list(w),numerator=h) for w,h in sorted(vals.items())],
              denominator=10**10,convention='first reversal forbidden; no virtual incoming bond retained')
    (OUT/f'h2_m{m}_certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
    summary=dict(m=m,windows=len(ws),orbits=len(vals),transitions=sum(map(len,trs)),
                 exact_quotient=str(lam),quotient_float=float(lam),q=str(q),pass_exact=passed,
                 h_ratio=float(F(max(hn),min(hn))),Cv_upper=float(cv),Cv_exact=str(cv),wall=time.monotonic()-start)
    print(json.dumps(summary),flush=True)
    assert passed
    return summary

if __name__=='__main__':
    summaries=[test(6,F(2499,2500)),test(8,F(247,250))]
    (OUT/'h2_small_summary.json').write_text(json.dumps(summaries,indent=2)+'\n')
