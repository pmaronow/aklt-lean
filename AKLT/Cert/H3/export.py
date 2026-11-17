#!/usr/bin/env python3
"""Untrusted streaming exporter for the archived stationary certificates.

Only Python's standard library is required. Decimal/hex data emitted here are
candidate literals; their provenance hashes are not mathematical premises.
"""
import argparse, array, gzip, hashlib, json, os, pathlib, shutil, struct, sys

ROOT = pathlib.Path(__file__).resolve().parents[3]
HERE = pathlib.Path(__file__).resolve().parent
LEGACY_DATA = ROOT/'CertData/H3/Legacy/Data'
ARCHIVE = pathlib.Path(os.environ.get('H3_INPUT_DIR', '/home/ubuntu/aklt/compfeas/data'))
SS, NW, BITS = 19881, 3741, 80
HEADER = '\n@[expose] public section\nset_option backward.proofsInPublic true\nset_option maxHeartbeats 2000000000\nset_option maxRecDepth 1000000\n'

def disk_guard(additional_bytes=0):
    if shutil.disk_usage('/').free - additional_bytes < 100 * 1024**3:
        raise RuntimeError('ABORT: free disk on / below 100 GB')

def write_source(path, text):
    if not text.startswith('module\n') or len(text.splitlines()) > 10000:
        raise RuntimeError('Invalid generated module header or line count: ' + str(path))
    path.parent.mkdir(parents=True, exist_ok=True)
    disk_guard(len(text))
    path.write_text(text)

def literal(n): return 'h3_hex% "'+format(n,'x')+'"'
def pack_fields(vals,bits):
    # Byte conversion avoids a quadratic sequence of growing Python integers.
    if bits % 8 == 0:
        return int.from_bytes(b''.join(int(v).to_bytes(bits//8,'little') for v in vals),'little')
    vals=list(vals)
    def go(lo,hi):
        if hi-lo <= 32:
            return sum(vals[j] << (bits*(j-lo)) for j in range(lo,hi))
        mid=(lo+hi)//2
        return go(lo,mid) | (go(mid,hi) << (bits*(mid-lo)))
    return go(0,len(vals))

def read_windows():
    lines=(ARCHIVE/'windows_m10_min.txt').read_text().splitlines()
    nr,nq=map(int,lines[0].split()); assert (nr,nq)==(60092,NW)
    mapping=dict(map(int,l.split()) for l in lines[1:nr+1])
    reps=[list(map(int,l.split())) for l in lines[nr+1:]]
    assert len(reps)==NW
    return mapping,reps

def export_automaton():
    mapping,reps=read_windows()
    dense=[NW]*(4**10)
    for c,a in mapping.items(): dense[c]=a
    text='module\n\npublic import CertData.H3.Kernel.Common\npublic import CertData.H3.Kernel.Literal\n'+HEADER
    text+='namespace AKLT.Cert.H3.Data\nopen AKLT.Defs AKLT.Gen.Packed\n'
    for name,n in [('rawClass',pack_fields(dense,12)),('representatives',pack_fields((r[0] for r in reps),20)),
                   ('destinations',pack_fields((t+1 for r in reps for t in r[1:5]),12)),
                   ('edgeKinds',pack_fields((k if k>=0 else 3 for r in reps for k in r[5:9]),2))]:
        text+=f'def {name} : Nat := {literal(n)}\n'
    text+='''def projectCode (c : Nat) : Fin 3741 := ⟨lane rawClass 12 c % 3741, Nat.mod_lt _ (by decide)⟩
def representativeCode (a : Fin 3741) : Nat := lane representatives 20 a.val
def destination (a : Fin 3741) (d : Compass) : Nat := lane destinations 12 (a.val*4+directionCode d)
def quotient : MemoryQuotient 10 3741 where
  project w := projectCode (encodeWord w)
  representative a := decodeWord 10 (representativeCode a)
  allowed a d := destination a d != 0
  kind a d := stepKind (lane edgeKinds 2 (a.val*4+directionCode d))
  successor a d := ⟨(destination a d - 1) % 3741, Nat.mod_lt _ (by decide)⟩
  arrival a := direction (representativeCode a % 4)
end AKLT.Cert.H3.Data
'''
    out=LEGACY_DATA/'Automaton.lean'; write_source(out, text)
    return dict(source=str(out),raw_states=len(mapping),classes=NW)

def tree_expr(entries):
    if not entries: return 'PlaneTree.empty'
    if len(entries)==1:
        k,v=entries[0]; return f'(PlaneTree.leaf {k} {v})'
    j=len(entries)//2
    return f'(PlaneTree.branch {entries[j][0]} {tree_expr(entries[:j])} {tree_expr(entries[j:])})'

def export_case(name, selected, all_planes=False, group=64):
    disk_guard()
    source=ARCHIVE/(name+'.bin.gz')
    X=name.split('_')[1]; d0=int(name.split('_d')[1].split('_')[0]); tag=f'{X}{d0}'
    expected=(10,12,70,NW,SS,1 if X=='B' else 0,0 if X=='B' else 1,16,d0)
    groups={}; caps=None; maxima=0
    # A single pass validates header, length, uint32 endian format and gzip CRC.
    with gzip.open(source,'rb') as f:
        hdr=struct.unpack('<9q',f.read(72)); assert hdr==expected,(hdr,expected)
        capbytes=f.read(16*NW); assert len(capbytes)==16*NW
        caps=array.array('I');caps.frombytes(capbytes)
        if sys.byteorder!='little':caps.byteswap()
        for p in range(4):
            for a in range(NW):
                raw=f.read(SS*4); assert len(raw)==SS*4
                key=p*NW+a
                if all_planes or key in selected:
                    u=array.array('I');u.frombytes(raw)
                    if sys.byteorder!='little':u.byteswap()
                    maxima=max(maxima,max(u))
                    g=key//group if all_planes else 0
                    groups.setdefault(g,[]).append((key,pack_fields(u,BITS)))
        assert f.read(1)==b''
    modules=[]
    for g,entries in sorted(groups.items()):
        disk_guard()
        module=f'{tag}G{g:04d}' if all_planes else 'BNPrototype'
        text='module\n\npublic import CertData.H3.Legacy.Data.Automaton\npublic import CertData.H3.Kernel.Literal\n'+HEADER
        text+=f'namespace AKLT.Cert.H3.Data.{module}\nopen AKLT.Defs AKLT.Gen.Packed\n'
        text+=f'def caps : Nat := {literal(pack_fields(caps,32))}\n'
        for key,plane in entries: text+=f'def p{key} : Nat := {literal(plane)}\n'
        text+='def planes : PlaneTree := '+tree_expr([(k,f'p{k}') for k,_ in entries])+'\n'
        text+='''def cap (φ : Phase) (a : Fin 3741) : Nat := lane caps 32 (phaseCode φ * 3741 + a.val)
def plane (φ : Phase) (a : Fin 3741) : Nat := planes.get (phaseCode φ * 3741 + a.val)
def certificate : StationaryData 3741 where
  cap := cap
  value φ a x := lane (plane φ a) 80 (siteIndex x.val)
'''
        text+=f'end AKLT.Cert.H3.Data.{module}\n'
        out=LEGACY_DATA/f'{module}.lean';write_source(out,text);modules.append(str(out))
    sha=hashlib.file_digest(source.open('rb'),'sha256').hexdigest()
    return dict(name=name,sha256=sha,header=expected,modules=modules,exported_planes=sum(map(len,groups.values())),
                max_exported_u=maxima,max_cap=max(caps),selected_keys=sorted(selected))

def prototype_keys():
    mapping,reps=read_windows()
    windows=set(range(16))
    for r in reps[:16]: windows.update(t for t in r[1:5] if t>=0)
    # A true prefix with revisits; expand all sixteen two-step suffixes.
    stem=[1,0,1,2,3,2,3,0,3,0]
    for e in range(16):
        ds=stem+[e//4,e%4];code=0
        for d in ds[-10:]:code=code*4+d
        if code in mapping:windows.add(mapping[code])
    return {p*NW+a for p in range(4) for a in windows}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--all',action='store_true',help='Export every plane, grouped by 64 (large)')
    ap.add_argument('--case',default='stationary_B_m10_R70_d1_coarse')
    ap.add_argument('--group',type=int,default=64)
    args=ap.parse_args();assert 1<=args.group<=128
    if not args.all and args.case != 'stationary_B_m10_R70_d1_coarse':
        ap.error('The selected prototype is B/north; use --all to export another complete case.')
    disk_guard();auto=export_automaton()
    cert=export_case(args.case,prototype_keys(),args.all,args.group)
    report=pathlib.Path(os.environ.get('H3_REPORT_DIR','/home/ubuntu/aklt/reports/REGEN_H3'))
    report.mkdir(parents=True,exist_ok=True)
    (report/'export_manifest.json').write_text(json.dumps(dict(automaton=auto,certificate=cert),indent=2)+'\n')
    print(json.dumps({k:v for k,v in cert.items() if k!='selected_keys'}),flush=True)
if __name__=='__main__':main()
