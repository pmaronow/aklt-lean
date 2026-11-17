#!/usr/bin/env python3
"""H1 production exporter: every parity, full complex packed rows, row batches.

All generated Lean lives below CertData/H1/Generated, never below AKLT/.
Only finite computation proofs and assemblies using existing library results
are generated. Mathematical soundness leaves are emitted separately.
"""
from __future__ import annotations
import argparse, hashlib, json, math, os, sys, time
from pathlib import Path
import export as old
from export_packed import tree
from packed import sites, packed_row, at
from production_build import guard as budget_guard
from module_source import module_source

ROOT=Path(os.environ.get('H1_REGEN_ROOT', str(Path(__file__).resolve().parents[4])))
OUT=ROOT/'CertData/H1/Generated'
NS='CertData.H1.Generated'
CORE='AKLT.Cert.H1'
REPORT=Path(os.environ.get('H1_REGEN_REPORT', '/home/ubuntu/aklt/reports/REGEN_H1'))

def module_path(module): return ROOT/(module.replace('.','/')+'.lean')

def write(module,text):
    text=module_source(text)
    path=module_path(module);path.parent.mkdir(parents=True,exist_ok=True)
    if not path.exists() or path.read_text()!=text: path.write_text(text)

def check_options():
    return ['set_option maxHeartbeats 0','set_option maxRecDepth 1000000']

def emit_pattern(r,ctor_batch=8,gram_rows=8,python_check=False,split=True):
    budget_guard()
    old.disk_guard(OUT)
    old.validate(r)
    old.NS=NS
    pid=r['pid'];tag=f'P{pid:04d}';ss=sites(r)
    D=math.prod(s['dim'] for s in ss);p,q=r['threshold']
    bound=math.prod(sum(abs(a)+abs(b) for a,b in s['table']) for s in ss)*(5*q*12+3*p*8)
    width=max(32,((bound.bit_length()+1+15)//16)*16)
    out=0 if r['pattern']['out']==[1,0] else 2
    jobs=[];blocks=[]
    def job(module,kind,deps=(),**kw):
        entry=dict(module=module,kind=kind,deps=list(deps),pid=pid,**kw)
        jobs.append(entry);return module
    pattern=job(f'{NS}.Data.{tag}','pattern_data')
    write(pattern,old.metadata(r))
    network=job(f'{NS}.Data.{tag}Network','network_data')
    dns=network
    data=[f'import {CORE}.Production.Basic',f'namespace {dns}',f'open {CORE}']
    for i,s in enumerate(ss):
        flag=lambda x:'true' if x else 'false'
        spec=f"⟨{s['dim']}, {flag(s['left'])}, {flag(s['right'])}, {flag(s['center'])}, {s['ns']}, {flag(s['kind']=='d')}, {flag(s['role']=='leaf')}, {flag(s['role']=='tip')}, {flag(s['inverted'])}, {s['stride']}⟩"
        data += [f'def spec{i} : SiteSpec := {spec}',f'def table{i} : Table := {tree(s["table"])}',
                 f'def site{i} : PackedSite := ⟨spec{i}, table{i}⟩']
    data += [f'def network : List PackedSite := {old.lean_list("site"+str(i) for i in range(8))}',
             f'def width : Nat := {width}',f'def lanes : Nat := {D}',f'def outgoing : Nat := {out}',
             f'def denominator : Nat := {r["representation"]["moment_denominator"]}',
             f'def thresholdP : Nat := {p}',f'def thresholdQ : Nat := {q}',f'end {dns}\n']
    write(network,'\n'.join(data))
    local=job(f'{NS}.Check.{tag}Local','local_parameters',[network,pattern])
    lines=[f'import {network}',f'import {pattern}',*check_options(),f'namespace {local}',
           f'open {CORE} {CORE}.Production {dns}']
    for i in range(8):
        lines += [f'theorem local{i} : tableCheck spec{i} table{i} = true := by decide +kernel',f'#print axioms local{i}']
    lines += ['theorem parameters : parametersCheck network outgoing width lanes denominator thresholdP thresholdQ = true := by decide +kernel',
              f'theorem parities : parityCoverCheck network {old.lean_list(b["exchange_parity"] for b in r["blocks"])} = true := by decide +kernel',
              '#print axioms parameters','#print axioms parities']
    for bi,b in enumerate(r['blocks']):
        lines += [f'theorem basis{bi:02d} : basisCheck network {b["exchange_parity"]} ({b["two_sz"]}) {old.lean_list(b["basis_indices"])} = true := by decide +kernel',f'#print axioms basis{bi:02d}']
    lines += [f'end {local}\n'];write(local,'\n'.join(lines))
    for bi,b in enumerate(r['blocks']):
        rec=old.export_block(OUT,r,bi,gram_rows,literal_namespace=CORE)
        # The reused exporter only supplies data and computation/Gram assemblies.
        paths=[module_path(rec['data_module']),module_path(rec['check_module'])]
        paths += [module_path(s['module']) for s in rec['shards']]
        for path in paths:
            text=path.read_text().replace(f'import {NS}.Literals',f'import {CORE}.Literals')
            if path.read_text()!=text:path.write_text(text)
        dm=job(rec['data_module'],'matrix_data',block=bi,n=b['n'])
        gram=[]
        for s in rec['shards']:
            gram.append(job(s['module'],'gram_rows',[dm],block=bi,n=b['n'],row_start=s['row_start'],row_end=s['row_end'],dot_products=s['dot_products']))
        positive=job(rec['check_module'],'positivity_assembly',[dm,*gram],block=bi,n=b['n'])
        inds=b['basis_indices'];mp=b['M_lt'];constructors=[];row_names=[]
        ctor_network=network;ss_expr='network';indices_expr=dm+'.basisIndices'
        ctor_inds=inds;row_check='packedRowCheck';rows_accepted='RowsAccepted';ctor_ss=ss
        layout=None;packed_lanes=D
        if split:
            coords=[]
            for si,s in enumerate(ss):
                following=sum(t['ns']!=0 for t in ss[si+1:])
                bit=(b['exchange_parity']//2**following)%2
                coords.append(([3] if bit else [0,1,2]) if s['ns']==2 and s['kind']=='d' else list(range(s['dim'])))
            # An exterior coordinate occurs only at an actual diluted pair.
            assert all(cs==[3] and s['ns']==2 and s['kind']=='d' or cs!=[3] for cs,s in zip(coords,ss))
            strides=[math.prod(len(c) for c in coords[i+1:]) for i in range(8)]
            def remap(index):
                code=0
                for s,cs in zip(ss,coords):code=code*len(cs)+cs.index(index//s['stride']%s['dim'])
                return code
            ctor_inds=[remap(i) for i in inds];packed_lanes=math.prod(map(len,coords))
            ctor_network=job(f'{NS}.Data.{tag}B{bi:02d}Sector','sector_network_data',[network],block=bi,n=b['n'])
            sector_lines=[f'import {network}',f'namespace {ctor_network}',f'open {CORE} {CORE}.Production']
            for si,(cs,stride) in enumerate(zip(coords,strides)):
                sector_lines += [f'def site{si} : SectorSite := ⟨{dns}.site{si}, {old.lean_list(cs)}, {stride}⟩']
            sector_lines += ['def sectorNetwork : List SectorSite := '+old.lean_list(f'site{i}' for i in range(8)),
                             f'def packedIndices : List Nat := {old.lean_list(ctor_inds)}',
                             f'def packedLanes : Nat := {packed_lanes}',f'end {ctor_network}\n']
            write(ctor_network,'\n'.join(sector_lines))
            ss_expr=ctor_network+'.sectorNetwork';indices_expr=ctor_network+'.packedIndices'
            row_check='packedSectorRowCheck';rows_accepted='SectorRowsAccepted'
            layout=job(f'{NS}.Check.{tag}B{bi:02d}Layout','sector_layout',[network,ctor_network,dm],block=bi,n=b['n'])
            write(layout,'\n'.join([f'import {ctor_network}',f'import {dm}',*check_options(),f'namespace {layout}',f'open {CORE}.Production',
                 f'theorem checked : sectorNetworkCheck {dns}.network {b["exchange_parity"]} {ss_expr} = true ∧ remapCheck {dns}.network {ss_expr} {dm}.basisIndices {indices_expr} = true := by decide +kernel',
                 '#print axioms checked',f'end {layout}\n']))
            if python_check:
                ctor_ss=[]
                for si,(s,cs,stride) in enumerate(zip(ss,coords,strides)):
                    table=[at(s,a,l,rr,v,bb) for a in cs for l in range(4) for rr in range(4) for v in range(4) for bb in cs]
                    ctor_ss.append(dict(s,dim=len(cs),stride=stride,table=table))
        for start in range(0,b['n'],ctor_batch):
            end=min(start+ctor_batch,b['n'])
            cm=job(f'{NS}.Check.{tag}B{bi:02d}Constructor{start:03d}','constructor_rows',list(dict.fromkeys([network,ctor_network,dm])),block=bi,n=b['n'],row_start=start,row_end=end)
            constructors.append(cm)
            text=[f'import {network}',f'import {ctor_network}',f'import {dm}',f'import {CORE}.Literals',*check_options(),
                  f'namespace {cm}',f'open {CORE} {CORE}.Production {dns}']
            for i in range(start,end):
                vals=[mp[max(i,j)*(max(i,j)+1)//2+min(i,j)] for j in range(b['n'])]
                if python_check:
                    got=packed_row(r,ctor_ss,ctor_inds[i],width)
                    expected=sum(x*(1<<(width*j)) for j,x in zip(ctor_inds,vals))
                    if got!=(expected,0): raise ValueError(('packed complete-row mismatch',pid,bi,i))
                text += [f'theorem row{i:03d} : {row_check} {ss_expr} outgoing width thresholdP thresholdQ {ctor_inds[i]} {indices_expr} ({dm}.mRows.getD {i} []) = true := by decide +kernel',
                         f'#print axioms row{i:03d}']
                row_names.append(f'{cm}.row{i:03d}')
            text += [f'end {cm}\n'];write(cm,'\n'.join(text))
        ca=job(f'{NS}.Check.{tag}B{bi:02d}Constructed','constructor_assembly',list(dict.fromkeys(constructors+[network,ctor_network,dm]+([layout] if layout else []))),block=bi,n=b['n'])
        proof='True.intro'
        for rn in reversed(row_names):proof=f'And.intro {rn} ({proof})'
        text=[*('import '+m for m in constructors),f'import {network}',f'import {dm}',*check_options(),
              f'namespace {ca}',f'open {CORE}.Production {dns}',
              f'theorem accepted : {rows_accepted} {ss_expr} outgoing width thresholdP thresholdQ {indices_expr} {indices_expr} {dm}.mRows := by',
              f'  exact {proof}', '#print axioms accepted',f'end {ca}\n']
        write(ca,'\n'.join(text))
        blocks.append(dict(pid=pid,block=bi,n=b['n'],parity=b['exchange_parity'],weight=b['two_sz'],data_module=dm,
                           positivity_module=positive,constructor_module=ca,constructor_rows=constructors,gram_rows=gram,
                           basis_theorem=f'{local}.basis{bi:02d}',row_theorems=row_names,
                           sector_network_module=ctor_network,layout_module=layout,packed_lanes=packed_lanes,split_before_packing=split))
    return dict(pid=pid,network_module=network,pattern_module=pattern,local_module=local,
                width=width,lanes=D,bound_bits=bound.bit_length(),blocks=blocks,jobs=jobs)

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--selection',type=Path)
    ap.add_argument('--pids',nargs='+',type=int)
    ap.add_argument('--all',action='store_true')
    ap.add_argument('--ctor-batch',type=int,default=8)
    ap.add_argument('--gram-rows',type=int,default=8)
    ap.add_argument('--python-check',action='store_true')
    ap.add_argument('--unsplit',action='store_true',help='retain full 4-dimensional D pair packing')
    ap.add_argument('--manifest',type=Path)
    args=ap.parse_args()
    if args.manifest is None:
        args.manifest=REPORT/('production-manifest.json' if args.all else 'pilot-manifest.json')
    if args.ctor_batch<1 or args.gram_rows<1:ap.error('batch sizes must be positive')
    selected=None if args.all else set(args.pids or json.loads(args.selection.read_text())['pids'] if args.selection else args.pids or [7237])
    begin=time.monotonic();patterns=[]
    for r in old.records(Path('/home/ubuntu/aklt/data/h1')):
        if selected is not None and r['pid'] not in selected:continue
        patterns.append(emit_pattern(r,args.ctor_batch,args.gram_rows,args.python_check,not args.unsplit))
    manifest=dict(format='h1-production-v2',data_root=str(OUT),namespace=NS,patterns=patterns,
                  jobs=[j for p in patterns for j in p['jobs']],
                  settings=dict(ctor_batch=args.ctor_batch,gram_rows=args.gram_rows),
                  generation_seconds=time.monotonic()-begin,mathematical_leaf_proofs_generated=0)
    args.manifest.parent.mkdir(parents=True,exist_ok=True)
    args.manifest.write_text(json.dumps(manifest,indent=2)+'\n')
    print(json.dumps(dict(patterns=len(patterns),blocks=sum(len(p['blocks']) for p in patterns),modules=len(manifest['jobs']),seconds=manifest['generation_seconds'],manifest=str(args.manifest))))

if __name__=='__main__':main()
