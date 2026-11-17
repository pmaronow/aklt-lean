#!/usr/bin/env python3
"""Generate and kernel-check all stationary H3 certificates, outside AKLT/.

No native result is trusted as a proof. Expected integers, tables and scheduling
are untrusted inputs to ordinary Lean decide +kernel computations.
"""
from __future__ import annotations
import array, fractions, gzip, hashlib, json, math, os, pathlib, re, shutil
import struct, sys, time

ROOT=pathlib.Path(__file__).resolve().parents[3]
OUT=ROOT/'CertData/H3'
REPORT=pathlib.Path(os.environ.get('H3_REPORT_DIR',ROOT / 'verification/runs/H3'))
ARCHIVE=pathlib.Path(os.environ.get('H3_INPUT_DIR',ROOT / 'data/h3'))
SS,NQ,BITS=19881,3741,80
CASES={'B1':('B',1,351207554),'B2':('B',2,290599163),'C1':('C',1,527872005),'C2':('C',2,380754375),'C3':('C',3,273048088)}
HDR='set_option maxHeartbeats 2000000000\nset_option maxRecDepth 1000000\n'
F=fractions.Fraction
DX=[1,0,-1,0];DY=[0,1,0,-1]
LEGACY_HASHES={}
EQUIVALENCE={}

def guard(extra=0):
    if shutil.disk_usage('/').free-extra<100*1024**3:raise RuntimeError('ABORT: free disk below 100 GiB')

def write(path,text):
    if text.count('\n')>10000:raise RuntimeError('Generated source exceeds 10,000 lines: '+str(path))
    if not text.startswith('module\n'):raise RuntimeError('Missing module header: '+str(path))
    if path.exists() and path.read_text()==text:return
    path.parent.mkdir(parents=True,exist_ok=True);guard(max(0,len(text)-(path.stat().st_size if path.exists() else 0)))
    path.write_text(text)
def lit(n):return 'h3_hex% "'+format(int(n),'x')+'"'
def pack(vals,bits):
    vals=list(vals)
    if bits%8!=0:assert all(0<=int(v)<2**bits for v in vals), 'packed field overflow'
    if bits%8==0:return int.from_bytes(b''.join(int(v).to_bytes(bits//8,'little') for v in vals),'little')
    def go(lo,hi):
        if hi-lo<=32:return sum(vals[j]<<(bits*(j-lo)) for j in range(lo,hi))
        mid=(lo+hi)//2;return go(lo,mid)|(go(mid,hi)<<(bits*(mid-lo)))
    return go(0,len(vals))
def tree(es):
    if not es:return 'PlaneTree.empty'
    if len(es)==1:return f'(PlaneTree.leaf {es[0][0]} {es[0][1]})'
    m=len(es)//2;return f'(PlaneTree.branch {es[m][0]} {tree(es[:m])} {tree(es[m:])})'
def module(path):return str(path.relative_to(ROOT).with_suffix('')).replace('/','.')
def namespace(path):return module(path)
def source(path,imports,body,certificate=True):
    if 'CertData.H3.Kernel.Production.Model' not in imports:imports=['CertData.H3.Kernel.Production.Model']+list(imports)
    if module(path) in LEGACY_HASHES:
        legacy='\n'.join('import '+i for i in imports)+'\n'+('set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n' if certificate else '')+'namespace '+namespace(path)+'\nopen AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Defs AKLT.Gen.Packed\n'+body+'\nend '+namespace(path)+'\n'
        actual=hashlib.sha256(legacy.encode()).hexdigest()
        EQUIVALENCE[module(path)]=dict(legacy_template_sha256=actual,expected_sha256=LEGACY_HASHES[module(path)],equal=actual==LEGACY_HASHES[module(path)])
    # Audit all exported theorems, including glue omitted by the legacy template.
    lines=body.splitlines()
    printed={line.split()[2] for line in lines if line.startswith('#print axioms ')}
    theorems=[re.match(r'theorem (\w+)',line)[1] for line in lines if line.startswith('theorem ')]
    body+=''.join('\n#print axioms '+n+'\n' for n in theorems if n not in printed)
    # The unchanged structural sort calls this standard-library module's private
    # split helper. Import its body where kernel replay actually takes place.
    sort_import='\nimport all Init.Data.List.Sort.Basic' if 'earlyDFS' in body or 'prefixBatch' in body else ''
    return 'module\n\n'+'\n'.join('public import '+i for i in imports)+sort_import+'\n\n@[expose] public section\nset_option backward.proofsInPublic true\n'+(HDR if certificate else '')+'namespace '+namespace(path)+'\nopen AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Defs AKLT.Gen.Packed\n'+body+'\nend '+namespace(path)+'\n'
def load_windows():
    ls=(ARCHIVE/'windows_m10_min.txt').read_text().splitlines();nr,nq=map(int,ls[0].split());assert(nr,nq)==(60092,3741)
    raw=[tuple(map(int,l.split())) for l in ls[1:nr+1]]
    assert all(len(r)==2 and 0<=r[0]<4**10 and 0<=r[1]<3741 for r in raw)
    assert all(raw[i][0]<raw[i+1][0] for i in range(nr-1))
    mapping=dict(raw);assert len(mapping)==nr
    reps=[list(map(int,l.split())) for l in ls[nr+1:]]
    assert len(reps)==3741
    for a,r in enumerate(reps):
        assert len(r)==9 and 0<=r[0]<4**10 and mapping[r[0]]==a
        assert all(-1<=d<3741 for d in r[1:5]) and all(k in [-1,0,1,2] for k in r[5:9])
        assert all((d==-1)==(k==-1) for d,k in zip(r[1:5],r[5:9]))
    return mapping,reps
def manifest_path():return REPORT/'build_manifest.json'
def load_manifest():return json.loads(manifest_path().read_text()) if manifest_path().exists() else dict(schema=1,jobs=[],cases={})
def save_manifest(m):REPORT.mkdir(parents=True,exist_ok=True);manifest_path().write_text(json.dumps(m,indent=2)+'\n')
def job(path,kind,deps=(),**kw):return dict(module=module(path),source=str(path.relative_to(ROOT)),kind=kind,deps=list(deps),**kw)

def generate_graph(m):
    mapping,reps=load_windows();m['automaton_source_sha256']=hashlib.file_digest((ARCHIVE/'windows_m10_min.txt').open('rb'),'sha256').hexdigest();dense=[3741]*(4**10)
    for c,a in mapping.items():dense[c]=a
    p=OUT/'Graph.lean';body=''
    for i in range(256):body+=f'def b{i} : Nat := {lit(pack(dense[i*4096:(i+1)*4096],12))}\n'
    for name,value in [('denseClass',pack(dense,12)),('representatives',pack([r[0] for r in reps],20)),('destinations',pack([t+1 for r in reps for t in r[1:5]],12)),('kinds',pack([k if k>=0 else 3 for r in reps for k in r[5:9]],2))]:body+=f'def {name} : Nat := {lit(value)}\n'
    body+='def blocks : PlaneTree := '+tree([(i,f'b{i}') for i in range(256)])+'\n'
    body+="""def packed : CertData.H3.Bridge.PackedGraph := ⟨denseClass,blocks,representatives,destinations,kinds⟩
def graph : Graph := packed.toGraph
"""
    body+='def rebuilt : Nat := ['+','.join(f'b{i}' for i in range(256))+'].foldr (fun x rest => x+(rest <<< 49152)) 0\n'
    write(p,source(p,['CertData.H3.Kernel.Production.Model','CertData.H3.Kernel.Literal','CertData.H3.Bridge.GraphLayout'],body));jobs=[job(p,'graph',['CertData.H3.Bridge.GraphLayout'])]
    p=OUT/'Check/GraphTables.lean';body='theorem checked : CertData.H3.Graph.rebuilt = CertData.H3.Graph.denseClass := by decide +kernel\n#print axioms checked\n'
    write(p,source(p,['CertData.H3.Graph'],body));jobs.append(job(p,'graph_check',['CertData.H3.Graph']))
    counts=[0]*64
    for c in mapping:counts[(c//256)//64]+=1
    for i in range(64):
        p=OUT/f'Check/Raw/R{i:04d}.lean';body=f'def result : RawStats := rawBatch CertData.H3.Graph.graph {i*64} 64\ndef expected : RawStats := ⟨{counts[i]},true⟩\ntheorem checked : result = expected := by decide +kernel\n#print axioms checked\n'
        write(p,source(p,['CertData.H3.Graph'],body));jobs.append(job(p,'raw_check',['CertData.H3.Graph'],expected_count=counts[i]))
    for i in range(math.ceil(3741/64)):
        p=OUT/f'Check/Representatives/R{i:04d}.lean';body=f'theorem checked : representativeBatch CertData.H3.Graph.graph {64*i} {min(64,3741-64*i)} = true := by decide +kernel\n#print axioms checked\n'
        write(p,source(p,['CertData.H3.Graph'],body));jobs.append(job(p,'representative_check',['CertData.H3.Graph']))
    p=OUT/'Check/EdgeCounts.lean';body='theorem checked : edgeCounts CertData.H3.Graph.graph = (2516,5032,1872) := by decide +kernel\n#print axioms checked\n'
    write(p,source(p,['CertData.H3.Graph'],body));jobs.append(job(p,'edge_check',['CertData.H3.Graph']))
    m['graph_counts']=counts;m['jobs']=[j for j in m['jobs'] if j['kind'] not in {'graph','graph_check','raw_check','representative_check','edge_check'}]+jobs
    return mapping,reps

class Oracle:
    def __init__(self):
        self.xs,self.xt=F(1000,961),F(200,187);self.h=F(5404319552844595,4503599627370496)
        alpha=[F(145217,10**6),F(150000,10**6)];beta=[F(352782,10**6),F(357549,10**6)];bp=[F(340008,10**6),F(344661,10**6)]
        self.rewards={};self.responses={};weights=[F(1,3),F(1,5),self.xs/3,self.xt/3]
        hp=lambda a,b:F(1) if DX[a]==DX[b] or DY[a]==DY[b] else self.h
        for a in range(4):
            for d in range(4):
                for mask in range(16):
                    others=[j for j in range(4) if j not in [(a+2)%4,d] and not (mask>>j)&1]
                    ty=int(a!=d)
                    if d==(a+2)%4 or not others:k=F(0)
                    elif len(others)==1:k=bp[ty]*hp(others[0],d)
                    else:k=alpha[ty]*hp(*others)+beta[ty]*(hp(others[0],d)+hp(others[1],d))
                    self.rewards[a,d,mask]=k;self.responses[a,d,mask]=(self.xs if a==d else self.xt)*k/3
                    weights.extend([k,self.responses[a,d,mask]])
        self.K=math.lcm(*(w.denominator for w in weights));assert self.K==2427985134707609174016000000
        self.reward={key:int(v*self.K) for key,v in self.rewards.items()};self.response={key:int(v*self.K) for key,v in self.responses.items()}
        self.ns=int(self.xs/3*self.K);self.nt=int(self.xt/3*self.K);self.n3=self.K//3;self.n5=self.K//5
    def generate_exact(self,m):
        p=OUT/'Exact.lean';body=''
        for name,n in [('K',self.K),('ns',self.ns),('nt',self.nt),('n3',self.n3),('n5',self.n5),('rewards',pack([self.reward[a,d,mask] for a in range(4) for d in range(4) for mask in range(16)],96)),('responses',pack([self.response[a,d,mask] for a in range(4) for d in range(4) for mask in range(16)],96))]:body+=f'def {name} : Nat := {lit(n)}\n'
        body+='def exact : Exact := ⟨K,ns,nt,n3,n5,(fun a d mask => lane rewards 96 (64*a+16*d+mask)),(fun a d mask => lane responses 96 (64*a+16*d+mask))⟩\n'
        write(p,source(p,['CertData.H3.Kernel.Production.Replay','CertData.H3.Kernel.Literal'],body));m['jobs']=[j for j in m['jobs'] if j['kind']!='exact']+[job(p,'exact')]
    def start(self):return dict(x=-1,y=0,ain=2,used=frozenset(),depart=(),code=0,n=0,ph=(1,1,0,0),base=1,items=())
    def legal(self,s,d,d0):
        xx,yy=s['x']+DX[d],s['y']+DY[d];ed=tuple(sorted(((s['x'],s['y']),(xx,yy))))
        return (s['n']!=0 or d==d0) and (xx,yy)!=(0,0) and ed not in s['used']
    def step(self,s,d):
        x,y=s['x'],s['y'];xx,yy=x+DX[d],y+DY[d];ed=tuple(sorted(((x,y),(xx,yy))));A,B,C,D=s['ph'];items=s['items']
        if (x,y) in s['depart']:ph=tuple(p*self.n5 for p in s['ph']);base=s['base']*self.n5
        else:
            mask=sum(1<<j for j in range(4) if (x+DX[j],y+DY[j])==(0,0) or s['depart'].count((x+DX[j],y+DY[j]))>=2)
            r=self.response[s['ain'],d,mask];k=self.reward[s['ain'],d,mask];items=items+((d==s['ain'],k,s['n']),)
            ph=(A*self.ns,B*self.ns,C*self.ns,D*self.n3+B*r) if d==s['ain'] else (A*self.nt,B*self.n3,C*self.n3+A*r,D*self.n3)
            base=s['base']*self.n3
        return dict(x=xx,y=yy,ain=d,used=s['used']|{ed},depart=s['depart']+((x,y),),code=(s['code']*4+d)%1048576,n=s['n']+1,ph=ph,base=base,items=items)
    def short(self,s):
        def key(item):
            straight,k,t=item;x=self.ns*3 if straight else self.nt*3
            return (k==0,F((x-self.K),x*k) if k else F(0),t)
        its=sorted(s['items'],key=key);n=0
        for r in range(len(its)-1,-1,-1):
            straight,k,t=its[r];x=self.ns*3 if straight else self.nt*3;n=x*(k*self.K**(2*(len(its)-r-1))+self.K*n)
        return s['base']*n*self.K**(36-s['n']-2*len(its))

def result_zero():return dict(tail=0,short=0,leaves=0,closed=0,nodes=0,stems=0,ok=True)
def add(a,b):
    return {k:a[k] and b[k] if k=='ok' else a[k]+b[k] for k in a}
def result_term(r):return '⟨'+','.join(str(r[k]) for k in ['tail','short','leaves','closed','nodes','stems'])+','+str(r['ok']).lower()+'⟩'

def conjunction(props):return ' ∧\n  '.join(props+['True'])
def conjunction_proof(proofs):return '⟨'+','.join(proofs+['True.intro'])+'⟩'
def fin_cases_proof(proofs):
    p='(fun i => Fin.elim0 i)'
    for proof in reversed(proofs):p='Fin.cases '+proof+' ('+p+')'
    return p
def selector(name,values,typ,default):
    return f'def {name} : Nat → {typ}\n'+''.join(f'  | {i} => {v}\n' for i,v in enumerate(values))+f'  | _ => {default}\n'

def generate_case_bridges(m,extra):
    for tag,c in m['cases'].items():
        X,d0,ceiling=CASES[tag];compass={1:'.north',2:'.west',3:'.south'}[d0]
        base=f'CertData.H3.{tag}';ra=base+'.RowAssembly';pa=base+'.PrefixAssembly'
        p=OUT/f'Bridge/{tag}.lean';depth,group,batch=c['frontier_depth'],c['group'],c['prefix_batch']
        body=f'''abbrev G : Graph := CertData.H3.Graph.graph
abbrev T : Tables := {base}.Tables.tables
abbrev lookup : Tables := {base}.EndpointAll.tables
abbrev E : Exact := CertData.H3.Exact.exact
open CertData.H3.Bridge

theorem ceiling_value : ({ceiling} : ℚ)=stationaryPrefixCeiling .{X} {compass} := by decide +kernel
#print axioms ceiling_value

/-- Blueprint assembly from shared closed leaves and this case's computed checks. -/
theorem case_from_leaves (hQ : G.quotient=Automaton10Data.supplied)
    (hcorrect : G.quotient.Correct) (h : ProductionCaseLeaves) : CaseV2 .{X} {compass} := by
  rcases h with ⟨hs,hrow,hep,hprefix⟩
  have hrows := hrow G T .{X} {compass} {group} (by decide +kernel) {ra}.plane_checks
  have hendpoint := hep G T lookup .{X} {compass} hrows (fun _ _ => rfl)
  have hJ := hprefix hs.2.2.1 hs.2.2.2.1 hs.2.2.2.2.1 G T lookup E .{X}
    ⟨{d0},by decide +kernel⟩ {depth} {batch} {base}.Check.Early.expected {pa}.expectedAt
    CertData.H3.Check.ExactTable.checked hcorrect hendpoint
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    {base}.Check.Early.checked {pa}.batch_checks {pa}.expected_ok
  have hJ' := hJ.trans (congrArg (resultValue E) {pa}.expected_layout)
  exact caseV2_of_checks G T E .{X} {compass} {pa}.expectedTotal {ceiling}
    hQ hcorrect {base}.Check.Summary.case_allowed hrows hJ'
    CertData.H3.Check.ExactTable.checked {base}.Check.Summary.checked ceiling_value hs
#print axioms case_from_leaves
'''
        deps=[base+'.Pilot','CertData.H3.Check.ExactTable','CertData.H3.Bridge.Interface']
        write(p,source(p,deps,body));extra.append(job(p,'case_assembly',deps,case=tag))
    p=OUT/'Bridge/All.lean';cases=list(CASES)
    deps=['CertData.H3.Bridge.Production','CertData.H3.GraphAssembly','CertData.H3.Check.Shape']+[f'CertData.H3.Bridge.{c}' for c in cases]
    body='open CertData.H3.Bridge\n'
    body+='def Leaves : Prop := AutomatonBridgeLeaves ∧ ProductionCaseLeaves\n'
    body+='theorem stationary_from_leaves (h : Leaves) : AKLT.Blueprint.Top.StationaryCheckStatementV2 := by\n'
    body+='  rcases h with ⟨ha,hp⟩\n'
    body+='  have hQ := ha.2.2.2.1 CertData.H3.Graph.packed CertData.H3.Check.SuppliedTables.checked CertData.H3.Check.BlockLookup.checked\n'
    body+='  have hcorrect := graph_correct_from_leaves CertData.H3.Graph.packed ha CertData.H3.GraphAssembly.raw_receipt CertData.H3.GraphAssembly.representative_receipt\n'
    body+='  have hauto := automatonV2_from_leaves CertData.H3.Graph.packed ha CertData.H3.Check.SuppliedTables.checked CertData.H3.Check.BlockLookup.checked CertData.H3.GraphAssembly.raw_receipt CertData.H3.GraphAssembly.representative_receipt CertData.H3.GraphAssembly.field_receipt CertData.H3.Check.EdgeCounts.checked\n'
    body+='  exact stationaryV2_from_cases CertData.H3.Check.Shape.checked hauto\n'+''.join(f'    (CertData.H3.Bridge.{tag}.case_from_leaves hQ hcorrect hp)\n' for tag in cases)
    body+='#print axioms stationary_from_leaves\n'
    write(p,source(p,deps,body));extra.append(job(p,'all_case_assembly',deps,requires_cases=cases))
    extra.append(job(OUT/'Bridge/Production.lean','automaton_bridge',['CertData.H3.Bridge.GraphLayout','CertData.H3.Bridge.Interface']))

def generate_assemblies(m):
    graph='CertData.H3.Graph.graph';raw=[j for j in m['jobs'] if j['kind']=='raw_check'];reps=[j for j in m['jobs'] if j['kind']=='representative_check']
    p=OUT/'Check/SuppliedTables.lean';body="""theorem checked : CertData.H3.Graph.packed.Transcribed := by
  unfold CertData.H3.Bridge.PackedGraph.Transcribed
  decide +kernel
#print axioms checked
"""
    write(p,source(p,['CertData.H3.Graph','AKLT.Defs.Automaton10Data'],body))
    extra=[job(p,'supplied_binding',['CertData.H3.Graph'])]
    fields=[]
    for i in range(59):
        p=OUT/f'Check/Fields/F{i:04d}.lean'
        body=f'theorem checked : fieldBatch {graph} {64*i} {min(64,3741-64*i)} = true := by decide +kernel\n#print axioms checked\n'
        write(p,source(p,['CertData.H3.Graph'],body));fields.append(job(p,'field_check',['CertData.H3.Graph']))
    extra.extend(fields)
    p=OUT/'Check/Shape.lean';body='theorem checked : (square (0,0) certificateRadius).card = 19881 := by decide +kernel\n#print axioms checked\n'
    write(p,source(p,[],body));extra.append(job(p,'shape_check'))
    p=OUT/'Check/ExactTable.lean';body='''theorem checked : CertData.H3.Bridge.ExactValid CertData.H3.Exact.exact := by
  unfold CertData.H3.Bridge.ExactValid
  decide +kernel
#print axioms checked
'''
    write(p,source(p,['CertData.H3.Exact','CertData.H3.Bridge.Interface'],body));extra.append(job(p,'exact_check',['CertData.H3.Exact','CertData.H3.Bridge.Interface']))
    p=OUT/'Check/BlockLookup.lean';body="""def result : Bool := CertData.H3.Graph.packed.blockCheck
theorem checked : result = true := by decide +kernel
#print axioms checked
"""
    write(p,source(p,['CertData.H3.Graph'],body));extra.append(job(p,'block_lookup',['CertData.H3.Graph']))
    p=OUT/'GraphAssembly.lean';imports=[j['module'] for j in raw+reps+fields]+['CertData.H3.Check.EdgeCounts','CertData.H3.Check.GraphTables','CertData.H3.Check.SuppliedTables','CertData.H3.Check.BlockLookup']
    body='def RawChecks : Prop := '+conjunction([j['module']+'.result = '+j['module']+'.expected' for j in raw])+'\n'
    body+='theorem raw_checked : RawChecks := '+conjunction_proof([j['module']+'.checked' for j in raw])+'\n'
    body+=selector('rawAt',[j['module']+'.result' for j in raw],'RawStats','⟨0,false⟩')
    body+=selector('rawExpected',[j['module']+'.expected' for j in raw],'RawStats','⟨0,false⟩')
    body+='theorem all_raw_checked : ∀ i : Fin 64, rawAt i.val=rawExpected i.val := '+fin_cases_proof([j['module']+'.checked' for j in raw])+'\n'
    body+='def RepresentativeChecks : Prop := '+conjunction([f'representativeBatch {graph} {i*64} {min(64,3741-i*64)} = true' for i in range(len(reps))])+'\n'
    body+='theorem representatives_checked : RepresentativeChecks := '+conjunction_proof([j['module']+'.checked' for j in reps])+'\n'
    body+='def FieldChecks : Prop := '+conjunction([f'fieldBatch {graph} {i*64} {min(64,3741-i*64)} = true' for i in range(59)])+'\n'
    body+='theorem fields_checked : FieldChecks := '+conjunction_proof([j['module']+'.checked' for j in fields])+'\n#print axioms fields_checked\n'
    body+='def totalRaw : Nat := (['+','.join(j['module']+'.expected' for j in raw)+'] : List RawStats).foldl (fun n r => n+r.count) 0\n'
    body+='theorem count_checked : totalRaw = 60092 := by decide +kernel\n#print axioms all_raw_checked\n#print axioms raw_checked\n#print axioms representatives_checked\n#print axioms count_checked\n'
    body+=f'theorem raw_family : ∀ i : Fin 64, rawBatch {graph} (i.val*64) 64=rawExpected i.val := '+fin_cases_proof([j['module']+'.checked' for j in raw])+'\n#print axioms raw_family\n'
    body+='theorem raw_expected_ok : ∀ i : Fin 64, (rawExpected i.val).ok=true := by decide +kernel\n#print axioms raw_expected_ok\n'
    body+='theorem raw_expected_count : ((List.finRange 64).map fun i => (rawExpected i.val).count).sum=60092 := by decide +kernel\n#print axioms raw_expected_count\n'
    body+=f'theorem raw_receipt : CertData.H3.Bridge.RawReceipt {graph} := ⟨(fun i => rawExpected i.val),raw_family,raw_expected_ok,raw_expected_count⟩\n#print axioms raw_receipt\n'
    body+=f'theorem representative_receipt : CertData.H3.Bridge.RepresentativeReceipt {graph} := '+fin_cases_proof([j['module']+'.checked' for j in reps])+'\n#print axioms representative_receipt\n'
    body+=f'theorem field_receipt : CertData.H3.Bridge.FieldReceipt {graph} := '+fin_cases_proof([j['module']+'.checked' for j in fields])+'\n#print axioms field_receipt\n'
    write(p,source(p,imports,body));extra.append(job(p,'graph_assembly',imports))
    for tag,c in m['cases'].items():
        casejobs=[j for j in m['jobs'] if j.get('case')==tag];rows=[j for j in casejobs if j['kind']=='rows'];pref=[j for j in casejobs if j['kind']=='prefix'];early=next(j for j in casejobs if j['kind']=='early')
        p=OUT/tag/'RowAssembly.lean';imports=[j['module'] for j in rows]
        body='def Checks : Prop := '+conjunction([j['module']+'.result = true' for j in rows])+'\n'
        body+='theorem checked : Checks := '+conjunction_proof([j['module']+'.checked' for j in rows])+'\n#print axioms checked\n'
        body+=selector('atIndex',[j['module']+'.result' for j in rows],'Bool','false')
        body+=f'theorem all_checked : ∀ i : Fin {len(rows)}, atIndex i.val=true := '+fin_cases_proof([j['module']+'.checked' for j in rows])+'\n#print axioms all_checked\n'
        X,d0,ceiling=CASES[tag];compass={1:'.north',2:'.west',3:'.south'}[d0];group=c['group']
        body+=f'theorem plane_checks : ∀ i : Fin {len(rows)}, planeBatch {graph} CertData.H3.{tag}.Tables.tables .{X} {compass} (i.val*{group}) (min {group} (14964-i.val*{group}))=true := '+fin_cases_proof([j['module']+'.checked' for j in rows])+'\n#print axioms plane_checks\n'
        write(p,source(p,imports,body));extra.append(job(p,'row_assembly',imports,case=tag))
        p=OUT/tag/'PrefixAssembly.lean';parts=[early]+pref;imports=[j['module'] for j in parts]
        body='def Checks : Prop := '+conjunction([j['module']+'.result = '+j['module']+'.expected' for j in parts])+'\n'
        body+='theorem checked : Checks := '+conjunction_proof([j['module']+'.checked' for j in parts])+'\n'
        body+=selector('atIndex',[j['module']+'.result' for j in pref],'PrefixResult','zeroResult')
        body+=selector('expectedAt',[j['module']+'.expected' for j in pref],'PrefixResult','zeroResult')
        body+=f'theorem all_checked : ∀ i : Fin {len(pref)}, atIndex i.val=expectedAt i.val := '+fin_cases_proof([j['module']+'.checked' for j in pref])+'\n#print axioms all_checked\n'
        body+='def expectedTotal : PrefixResult := (['+','.join(j['module']+'.expected' for j in parts)+'] : List PrefixResult).foldl PrefixResult.add zeroResult\n'
        body+='def actualTotal : PrefixResult := (['+','.join(j['module']+'.result' for j in parts)+'] : List PrefixResult).foldl PrefixResult.add zeroResult\n'
        body+='theorem totals_equal : actualTotal = expectedTotal := congrArg (fun xs : List PrefixResult => xs.foldl PrefixResult.add zeroResult) ('
        eq='Eq.refl ([] : List PrefixResult)'
        for j in reversed(parts):eq='congrArg₂ List.cons '+j['module']+'.checked ('+eq+')'
        body+=eq+')\n#print axioms checked\n#print axioms totals_equal\n'
        depth,batch=c['frontier_depth'],c['prefix_batch'];earlymod=early['module']
        body+=f'theorem batch_checks : ∀ i : Fin {len(pref)}, prefixBatch {graph} CertData.H3.{tag}.EndpointAll.tables CertData.H3.Exact.exact .{X} {d0} {depth} (i.val*{batch}) (min {batch} (4^{depth}-i.val*{batch}))=expectedAt i.val := '+fin_cases_proof([j['module']+'.checked' for j in pref])+'\n#print axioms batch_checks\n'
        body+=f'theorem expected_ok : ∀ i : Fin {len(pref)}, (expectedAt i.val).ok=true := by decide +kernel\n#print axioms expected_ok\n'
        body+=f'theorem expected_layout : (({earlymod}.expected :: (List.finRange {len(pref)}).map (fun i => expectedAt i.val)).foldl PrefixResult.add zeroResult)=expectedTotal := by decide +kernel\n#print axioms expected_layout\n'
        write(p,source(p,imports,body));extra.append(job(p,'prefix_assembly',imports,case=tag))
        p=OUT/tag/'Check/Summary.lean';pa=f'CertData.H3.{tag}.PrefixAssembly';body=f'theorem checked : ceilingCheck CertData.H3.Exact.exact {pa}.expectedTotal {c["ceiling"]} = true := by decide +kernel\n'
        body+=f'theorem counts_checked : {pa}.expectedTotal.leaves = {c["expected_total"]["leaves"]} ∧ {pa}.expectedTotal.closed = {c["expected_total"]["closed"]} ∧ {pa}.expectedTotal.nodes-{pa}.expectedTotal.stems = {c["expected_total"]["nodes"]-c["expected_total"]["stems"]} := by decide +kernel\n'
        count=c['prefix_batch'];limit=4**c['frontier_depth']
        body+='def intervals : List (Nat × Nat) := ['+','.join(f'({start},{min(count,limit-start)})' for start in range(0,limit,count))+']\n'
        body+=f'theorem coverage_checked : intervalCheck intervals {limit} = true := by decide +kernel\n#print axioms checked\n#print axioms counts_checked\n#print axioms coverage_checked\n'
        X,d0,_=CASES[tag];compass={1:'.north',2:'.west',3:'.south'}[d0]
        body+=f'theorem case_allowed : (PairType.{X},Compass{compass}) ∈ stationaryCases := by decide +kernel\n#print axioms case_allowed\n'
        write(p,source(p,[pa,'CertData.H3.Kernel.Production.Batching'],body));extra.append(job(p,'summary',[pa],case=tag))
        p=OUT/tag/'Pilot.lean';ra=f'CertData.H3.{tag}.RowAssembly'
        body=f'def Checks : Prop := {ra}.Checks ∧ {pa}.Checks ∧ CertData.H3.GraphAssembly.RawChecks ∧ CertData.H3.GraphAssembly.RepresentativeChecks\ntheorem checked : Checks := ⟨{ra}.checked,{pa}.checked,CertData.H3.GraphAssembly.raw_checked,CertData.H3.GraphAssembly.representatives_checked⟩\n#print axioms checked\n'
        deps=[ra,pa,'CertData.H3.GraphAssembly',f'CertData.H3.{tag}.Check.Summary']
        write(p,source(p,deps,body));extra.append(job(p,'pilot',deps,case=tag))
    generate_case_bridges(m,extra)
    extra.append(job(OUT/'Bridge/LegacyTargets.lean','legacy_target_assembly',['CertData.H3.Bridge.Interface']))
    extra.append(job(OUT/'Bridge/FamilyAssembly.lean','family_assembly',['CertData.H3.Bridge.Interface']))
    kinds={j['kind'] for j in extra};m['jobs']=[j for j in m['jobs'] if j['kind'] not in kinds]+extra

def generate_case(tag,m,mapping,oracle,group=64,depth=8,batch=256):
    X,d0,ceiling=CASES[tag];target=(1,0) if X=='B' else (0,1);name=f'stationary_{X}_m10_R70_d{d0}_coarse';src=ARCHIVE/(name+'.bin.gz')
    jobs=[];endpoint_rows={};plane_refs=[];endpoint_refs=[]
    caps_path=OUT/tag/'Caps.lean';plane_groups=[];end_groups=[];ps=[];es=[];first=0
    def flush():
        nonlocal ps,es,first
        if not ps:return
        g=first//group;pp=OUT/tag/f'Plane/G{g:04d}.lean';ep=OUT/tag/f'Endpoint/G{g:04d}.lean'
        body=''.join(f'def p{k} : Nat := {lit(v)}\n' for k,v in ps);write(pp,source(pp,['CertData.H3.Kernel.Common','CertData.H3.Kernel.Literal'],body))
        body=''.join(f'def e{k} : Nat := {lit(v)}\n' for k,v in es);write(ep,source(ep,['CertData.H3.Kernel.Common','CertData.H3.Kernel.Literal'],body))
        plane_groups.append(module(pp));end_groups.append(module(ep));jobs.extend([job(pp,'plane_data',case=tag),job(ep,'endpoint_data',case=tag)])
        plane_refs.extend((k,module(pp)+f'.p{k}') for k,v in ps);endpoint_refs.extend((k,module(ep)+f'.e{k}') for k,v in es)
        ps=[];es=[]
    t=time.monotonic()
    with gzip.open(src,'rb') as f:
        header=struct.unpack('<9q',f.read(72));assert header==(10,12,70,3741,19881,*target,16,d0)
        capbytes=f.read(16*3741);caps=array.array('I');caps.frombytes(capbytes)
        if sys.byteorder!='little':caps.byteswap()
        for key in range(4*3741):
            raw=f.read(4*19881);assert len(raw)==4*19881
            u=array.array('I');u.frombytes(raw)
            if sys.byteorder!='little':u.byteswap()
            rect=[v for r in range(25) for v in u[(r+57)*141+58:(r+57)*141+83]]
            endpoint_rows[key]=rect
            if not ps:first=key
            ps.append((key,pack(u,80)));es.append((key,pack(rect,80)))
            if len(ps)==group:flush()
        flush();assert f.read(1)==b''
    body=f'def packedCaps : Nat := {lit(pack(caps,32))}\ndef cap (key : Nat) : Nat := lane packedCaps 32 key\n'
    write(caps_path,source(caps_path,['CertData.H3.Kernel.Common','CertData.H3.Kernel.Literal'],body));jobs.append(job(caps_path,'caps',case=tag))
    pp=OUT/tag/'PlaneAll.lean';write(pp,source(pp,plane_groups,'def index : PlaneTree := '+tree(plane_refs)+'\ndef plane (key : Nat) : Nat := index.get key\n'));jobs.append(job(pp,'plane_catalog',plane_groups,case=tag))
    ep=OUT/tag/'EndpointAll.lean';body='def index : PlaneTree := '+tree(endpoint_refs)+'\ndef endpoint (key : Nat) : Nat := index.get key\ndef tables : Tables := ⟨(fun _ => 0),CertData.H3.'+tag+'.Caps.cap,endpoint⟩\n'
    write(ep,source(ep,end_groups+[module(caps_path),'CertData.H3.Kernel.Production.Model'],body));jobs.append(job(ep,'endpoint_catalog',end_groups+[module(caps_path)],case=tag))
    tp=OUT/tag/'Tables.lean';body=f'def tables : Tables := ⟨CertData.H3.{tag}.PlaneAll.plane,CertData.H3.{tag}.Caps.cap,CertData.H3.{tag}.EndpointAll.endpoint⟩\ndef certificate : StationaryData 3741 := tables.data\n'
    write(tp,source(tp,[module(pp),module(ep)],body));jobs.append(job(tp,'tables',[module(pp),module(ep)],case=tag))
    compass={1:'.north',2:'.west',3:'.south'}[d0]
    for g in range(math.ceil(14964/group)):
        p=OUT/tag/f'Check/Rows/R{g:04d}.lean';body=f'def result : Bool := planeBatch CertData.H3.Graph.graph CertData.H3.{tag}.Tables.tables .{X} {compass} {g*group} {min(group,14964-g*group)}\ntheorem checked : result = true := by decide +kernel\n#print axioms checked\n'
        write(p,source(p,['CertData.H3.Graph',module(tp)],body));jobs.append(job(p,'rows',['CertData.H3.Graph',module(tp)],case=tag,first=g*group,count=min(group,14964-g*group)))
    def dfs(s,left,early=False):
        if (s['x'],s['y'])==target:return dict(tail=0,short=oracle.short(s),leaves=0,closed=1,nodes=1,stems=0,ok=True)
        if left==0:
            if early:r=result_zero();r['nodes']=1;return r
            a=mapping[s['code']];j=(s['x']+13)*25+s['y']+12;v=[endpoint_rows[p*3741+a][j] for p in range(4)]
            return dict(tail=sum(p*z for p,z in zip(s['ph'],v)),short=0,leaves=1,closed=0,nodes=1,stems=0,ok=True)
        r=result_zero()
        for d in range(4):
            if oracle.legal(s,d,d0):r=add(r,dfs(oracle.step(s,d),left-1,early))
        r['nodes']+=1;return r
    def stem(code):
        s=oracle.start()
        for n in range(depth):
            if (s['x'],s['y'])==target:return result_zero()
            d=code//4**(depth-1-n)%4
            if not oracle.legal(s,d,d0):return result_zero()
            s=oracle.step(s,d)
        if (s['x'],s['y'])==target:return result_zero()
        r=dfs(s,12-depth);r['stems']=1;return r
    early=dfs(oracle.start(),depth,True);results=[]
    for block in range(math.ceil(4**depth/batch)):
        r=result_zero()
        for code in range(block*batch,min((block+1)*batch,4**depth)):r=add(r,stem(code))
        results.append(r);p=OUT/tag/f'Check/Prefix/P{block:04d}.lean'
        body=f'def result : PrefixResult := prefixBatch CertData.H3.Graph.graph CertData.H3.{tag}.EndpointAll.tables CertData.H3.Exact.exact .{X} {d0} {depth} {block*batch} {min(batch,4**depth-block*batch)}\ndef expected : PrefixResult := {result_term(r)}\ntheorem checked : result = expected := by decide +kernel\n#print axioms checked\n'
        write(p,source(p,['CertData.H3.Graph','CertData.H3.Exact',module(ep)],body));jobs.append(job(p,'prefix',['CertData.H3.Graph','CertData.H3.Exact',module(ep)],case=tag,expected={k:v for k,v in r.items() if k not in ['tail','short']},block=block))
    p=OUT/tag/'Check/Early.lean';body=f'def result : PrefixResult := earlyDFS CertData.H3.Exact.exact .{X} {d0} {depth} initial\ndef expected : PrefixResult := {result_term(early)}\ntheorem checked : result = expected := by decide +kernel\n#print axioms checked\n'
    write(p,source(p,['CertData.H3.Exact'],body));jobs.append(job(p,'early',['CertData.H3.Exact'],case=tag))
    total=early
    for r in results:total=add(total,r)
    value=F(total['short'],oracle.K**36)+F(total['tail'],oracle.K**12*65536)
    log=json.loads(pathlib.Path(__file__).with_name('prefix-reference.json').read_text())[tag];assert value==F(log['exact_bound']),(value,log['exact_bound'])
    assert total['leaves']==log['leaves'] and total['closed']==log['closed']
    assert 10**9*value<=ceiling
    m['jobs']=[j for j in m['jobs'] if j.get('case')!=tag]+jobs
    m['cases'][tag]=dict(name=name,header=header,group=group,frontier_depth=depth,prefix_batch=batch,planes=14964,plane_modules=len(plane_groups),prefix_modules=len(results),expected_early=early,expected_prefix=results,expected_total=total,exact_bound=str(value),ceiling=ceiling,export_wall=time.monotonic()-t,source_sha256=hashlib.file_digest(src.open('rb'),'sha256').hexdigest())
    print(json.dumps(dict(case=tag,planes=14964,prefix_modules=len(results),leaves=total['leaves'],closed=total['closed'],export_wall=time.monotonic()-t)),flush=True)

def main():
    # The module-system runner owns input pins, freshness, resources, and receipts.
    from regen import main as run
    return run()

if __name__=='__main__':raise SystemExit(main())
