#!/usr/bin/env python3
"""Generate sharded representative indexes and the complete V2 target assembly."""
import argparse, json, re
from pathlib import Path
from production_export import NS, CORE, REPORT, write
from production_build import guard as budget_guard

def balanced(xs,combine):
    if len(xs)==1:return xs[0]
    mid=len(xs)//2
    return combine(balanced(xs[:mid],combine),balanced(xs[mid:],combine))

def append_expr(xs):return balanced(xs,lambda a,b:f'({a} ++ {b})')

def main():
    global NS
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('manifest',type=Path)
    ap.add_argument('--representatives',type=Path,default=REPORT/'representatives.json')
    ap.add_argument('--coverage',type=Path,default=REPORT/'coverage-manifest.json')
    ap.add_argument('--output',type=Path,default=REPORT/'production-final.json')
    ap.add_argument('--chunk',type=int,default=16)
    ap.add_argument('--partial',action='store_true',help='test witness aggregation only; no full coverage or Top target is asserted')
    ap.add_argument('--namespace',default=NS)
    args=ap.parse_args();plan=json.loads(args.manifest.read_text());items=json.loads(args.representatives.read_text())
    NS=args.namespace
    if not re.fullmatch(r'[A-Za-z][A-Za-z0-9]*(?:\.[A-Za-z][A-Za-z0-9]*)*',NS):ap.error('invalid namespace')
    if len(items)!=7962 and not args.partial:ap.error('the full target requires exactly 7962 representatives')
    coverage=json.loads(args.coverage.read_text());jobs=plan['jobs']+([] if args.partial else coverage['jobs']);chunks=[];keychecks=[];witnesses=[]
    for offset in range(0,len(items),args.chunk):
        budget_guard()
        i=offset//args.chunk;group=items[offset:offset+args.chunk]
        data=f'{NS}.Data.Representatives{i:03d}';check=f'{NS}.Check.Representatives{i:03d}Keys';witness=f'{NS}.Check.Representatives{i:03d}Witnesses'
        imports=[x[2] for x in group]
        lines=[*('import '+m for m in imports),f'import {CORE}.Production.Semantics',f'namespace {data}',f'open {CORE}.Production',
               'def representatives : List Representative := ['+', '.join(f'⟨{pid}, {inp}.input⟩' for k,pid,inp,cc in group)+']',
               'def keys : List (Nat × Nat) := ['+', '.join(f'({k}, {pid})' for k,pid,inp,cc in group)+']',f'end {data}\n']
        write(data,'\n'.join(lines));jobs.append(dict(module=data,kind='index_data',deps=imports))
        write(check,f'''import {data}
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace {check}
open {CORE}.Production {data}
theorem checked : representatives.map (fun r => (r.key,r.pid)) = keys := by decide +kernel
#print axioms checked
end {check}
''')
        jobs.append(dict(module=check,kind='index_keys',deps=[data],representatives=len(group)))
        proof='True.intro'
        for k,pid,inp,cc in reversed(group):
            hw=f'({cc}.representative h)'
            proof=f'And.intro {hw}.1 (And.intro {hw}.2.1 (And.intro {hw}.2.2 ({proof})))'
        write(witness,'\n'.join([f'import {data}',*('import '+x[3] for x in group),f'import {CORE}.Production.Assembly',
          'set_option maxHeartbeats 0','set_option maxRecDepth 1000000',f'namespace {witness}',f'open {CORE}.Production',
          f'theorem accepted (h : Assembly.ConstructorPremises) : RepresentativesAccepted {data}.representatives := by\n  exact {proof}',
          '#print axioms accepted',f'end {witness}\n']))
        jobs.append(dict(module=witness,kind='index_witness_assembly',deps=[data]+[x[3] for x in group]))
        chunks.append(data);keychecks.append(check);witnesses.append(witness)
    data=f'{NS}.Data.Representatives';coverage_data=f'{NS}.Data.Coverage'
    write(data,'\n'.join([*('import '+m for m in chunks),f'namespace {data}',f'open {CORE}.Production',
        'def representatives : List Representative := '+append_expr([m+'.representatives' for m in chunks]),
        'def keys : List (Nat × Nat) := '+append_expr([m+'.keys' for m in chunks]),f'end {data}\n']))
    jobs.append(dict(module=data,kind='index_all_data',deps=chunks))
    if args.partial:
        allw=f'{NS}.Check.AllWitnesses'
        proof=balanced([w+'.accepted h' for w in witnesses],lambda a,b:f'ha _ _ ({a}) ({b})')
        write(allw,'\n'.join([f'import {data}',*('import '+m for m in witnesses),f'import {CORE}.Production.Assembly',
           'set_option maxHeartbeats 0','set_option maxRecDepth 1000000',f'namespace {allw}',f'open {CORE}.Production',
           f'theorem accepted (h : Assembly.ConstructorPremises) (ha : Leaves.representativesAppend) : RepresentativesAccepted {data}.representatives := by\n  exact {proof}',
           '#print axioms accepted',f'end {allw}\n']))
        jobs.append(dict(module=allw,kind='all_witness_assembly',deps=[data,*witnesses],cap_gib=64))
        plan['jobs']=jobs;plan['index']=dict(representatives=len(items),chunks=len(chunks),scope='PARTIAL_WITNESS_AGGREGATION_ONLY')
        args.output.write_text(json.dumps(plan,indent=2)+'\n')
        print(json.dumps(dict(modules=len(jobs),representatives=len(items),manifest=str(args.output))))
        return
    header=f'{NS}.Check.RepresentativeIndex'
    proof=balanced([m+'.checked' for m in keychecks],lambda a,b:f'congrArg₂ List.append ({a}) ({b})')
    write(header,'\n'.join([f'import {data}',f'import {coverage_data}',*('import '+m for m in keychecks),
      'set_option maxHeartbeats 0','set_option maxRecDepth 1000000',f'namespace {header}',f'open {CORE}.Production {data}',
      f'theorem entries : keys = {coverage_data}.catalog.entries := by decide +kernel',
      'theorem keys_checked : representatives.map (fun r => (r.key,r.pid)) = keys := by',
      f'  unfold representatives keys\n  simp only [List.map_append]\n  exact {proof}',
      f'theorem checked : representativeCheck {coverage_data}.catalog representatives = true := by',
      '  simp only [representativeCheck, beq_iff_eq]',
      '  exact entries.symm.trans keys_checked.symm',
      '#print axioms entries','#print axioms keys_checked','#print axioms checked',f'end {header}\n']))
    jobs.append(dict(module=header,kind='index_assembly',deps=[data,coverage_data,*keychecks]))
    allw=f'{NS}.Check.AllWitnesses'
    proof=balanced([w+'.accepted h' for w in witnesses],lambda a,b:f'ha _ _ ({a}) ({b})')
    write(allw,'\n'.join([f'import {data}',*('import '+m for m in witnesses),f'import {CORE}.Production.Assembly',
       'set_option maxHeartbeats 0','set_option maxRecDepth 1000000',f'namespace {allw}',f'open {CORE}.Production',
       f'theorem accepted (h : Assembly.ConstructorPremises) (ha : Leaves.representativesAppend) : RepresentativesAccepted {data}.representatives := by\n  exact {proof}',
       '#print axioms accepted',f'end {allw}\n']))
    jobs.append(dict(module=allw,kind='all_witness_assembly',deps=[data,*witnesses],cap_gib=64))
    target=f'{NS}.Check.Targets';cov=f'{NS}.Check.CoverageComplete'
    write(target,f'''import {allw}
import {header}
import {cov}
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace {target}
open {CORE}.Production
theorem finiteData (h : Assembly.ConstructorPremises) (hc : Assembly.CoveragePremises)
    (ha : Leaves.representativesAppend) : AKLT.Blueprint.Top.H1FiniteDataStatementV2 :=
  Assembly.finiteData_of_checks hc {coverage_data}.catalog {data}.representatives
    {cov}.accepted {header}.checked ({allw}.accepted h ha)
theorem certificateV2 (h : Assembly.ConstructorPremises) (hc : Assembly.CoveragePremises)
    (ha : Leaves.representativesAppend) (hs : TopLeaves.certificatePremises) :
    AKLT.Blueprint.Top.CertificateStatementV2 :=
  ⟨TopAssembly.certificate_of_leaves hs,finiteData h hc ha⟩
theorem targets (h : Assembly.ConstructorPremises) (hc : Assembly.CoveragePremises)
    (ha : Leaves.representativesAppend) (hs : TopLeaves.certificatePremises)
    (hi : TopLeaves.integerCheckPremises) :
    AKLT.Blueprint.Top.IntegerCheckStatement ∧ AKLT.Blueprint.Top.CertificateStatementV2 :=
  ⟨TopAssembly.integerCheck_of_leaves hi,certificateV2 h hc ha hs⟩
#print axioms finiteData
#print axioms certificateV2
#print axioms targets
end {target}
''')
    jobs.append(dict(module=target,kind='target_assembly',deps=[allw,header,cov],cap_gib=64))
    plan['jobs']=jobs;plan['index']=dict(representatives=len(items),chunks=len(chunks),chunk_size=args.chunk,target_module=target)
    args.output.write_text(json.dumps(plan,indent=2)+'\n')
    print(json.dumps(dict(modules=len(jobs),representative_chunks=len(chunks),target=target,manifest=str(args.output))))

if __name__=='__main__':main()
