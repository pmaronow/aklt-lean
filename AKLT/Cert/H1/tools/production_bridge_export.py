#!/usr/bin/env python3
"""Compile raw inputs, check every geometry and emit conditional Defs bridges.

No mathematical proof module is generated. Per-pattern witness theorems apply
Production.Assembly.case_witness to numerical checks and named closed library theorems.
"""
import argparse, itertools, json, re
from pathlib import Path
from locations import INPUT_DIR
from export import records, raw_completion, RING, TIPS, lean_list
from coverage import AXIAL, CORNERS, key, bond
from production_export import ROOT, NS, CORE, REPORT, write
from production_build import guard as budget_guard

def input_literal(r):
    masks=raw_completion(r);kinds={tuple(s[:2]):s[2] for s in r['pattern']['sites']}
    def options(xs):return lean_list('⟨%d, %d⟩'%({'x':0,'u':1,'d':2}[kinds[x]],sum(1<<d for d in masks[x])) for x in xs)
    leaders={(1,1):0,(-1,1):2,(-1,-1):4,(1,-1):6,(2,0):8,(0,2):11,(-2,0):14,(0,-2):17}
    tokens=[];counts={}
    for x,y,role in r['representation']['slots']:
        pt=TIPS[x,y] if role=='tip' else (x,y)
        tokens.append(leaders[pt]+counts.get(pt,0));counts[pt]=counts.get(pt,0)+1
    inv=sorted(tokens[i] for i in r['representation']['inversion'])
    outgoing=1 if r['pattern']['out']==[0,1] else 0
    return f'⟨{options(AXIAL)}, {options(CORNERS)}, {outgoing}, {str(r["representation"]["leafred"]).lower()}, {lean_list(inv)}⟩'

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('manifest',type=Path)
    ap.add_argument('--output',type=Path)
    args=ap.parse_args();plan=json.loads(args.manifest.read_text());patterns={p['pid']:p for p in plan['patterns']}
    jobs=list(plan['jobs']);byid={j['module']:j for j in jobs};items=[]
    for r in records(INPUT_DIR):
        budget_guard()
        pid=r['pid']
        if pid not in patterns:continue
        pat=patterns[pid];tag=f'P{pid:04d}';network=pat['network_module'];local=pat['local_module']
        if any(not b.get('split_before_packing') for b in pat['blocks']):
            ap.error('the production Defs bridge requires the default split parity mode')
        inp=f'{NS}.Data.{tag}Input';geo=f'{NS}.Check.{tag}Geometry'
        write(inp,f'''import {CORE}.Production.Input
namespace {inp}
open {CORE}.Production
def input : Input := {input_literal(r)}
end {inp}
''')
        jobs.append(dict(module=inp,kind='input_data',deps=[],pid=pid))
        write(geo,f'''import {inp}
import {network}
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace {geo}
open {CORE}.Production
theorem input_checked : inputCheck {inp}.input = true := by decide +kernel
theorem geometry_checked : geometryCheck {inp}.input {network}.network = true := by decide +kernel
#print axioms input_checked
#print axioms geometry_checked
end {geo}
''')
        jobs.append(dict(module=geo,kind='input_geometry',deps=[inp,network],pid=pid))
        cd=f'{NS}.Data.{tag}Case';cc=f'{NS}.Check.{tag}Case'
        imports=[inp,network]+[m for b in pat['blocks'] for m in [b['data_module'],b['sector_network_module']]]
        lines=[*('import '+m for m in dict.fromkeys(imports)),f'import {CORE}.Production.Semantics',
               f'namespace {cd}',f'open {CORE}.Production']
        for bi,b in enumerate(pat['blocks']):
            dm=b['data_module'];sn=b['sector_network_module'];w=r['blocks'][bi]['witness']
            lines += [f'def bundle{bi:02d} : Bundle := ⟨⟨{dm}.mRows, {dm}.lRows, {w["g"]}, {w["d"]}, {w["S"]}, {dm}.exchangeParity, {dm}.twoSz, {dm}.basisIndices⟩, {sn}.sectorNetwork, {sn}.packedIndices⟩']
        bundles=lean_list(f'bundle{i:02d}' for i in range(len(pat['blocks'])))
        lines += [f'def caseData : Case := ⟨{inp}.input, {network}.network, {network}.outgoing, {network}.width, {network}.lanes, {network}.denominator, {network}.thresholdP, {network}.thresholdQ, {bundles}⟩',f'end {cd}\n']
        write(cd,'\n'.join(lines));jobs.append(dict(module=cd,kind='case_data',deps=list(dict.fromkeys(imports)),pid=pid))
        imports=[cd,geo,local]+[m for b in pat['blocks'] for m in [b['positivity_module'],b['constructor_module'],b['layout_module']]]
        lines=[*('import '+m for m in dict.fromkeys(imports)),f'import {CORE}.Production.Assembly',
               'set_option maxHeartbeats 0','set_option maxRecDepth 1000000',f'namespace {cc}',
               f'open {CORE} {CORE}.Production {cd}']
        tableproof='True.intro'
        for i in reversed(range(8)):tableproof=f'And.intro {local}.local{i} ({tableproof})'
        lines += ['theorem metadata : caseData.MetadataAccepted := by',
                  f'  exact ⟨{geo}.input_checked, {geo}.geometry_checked, {tableproof}, {local}.parameters, rfl, rfl, rfl, {local}.parities⟩',
                  '#print axioms metadata']
        for bi,b in enumerate(pat['blocks']):
            dm=b['data_module'];lay=b['layout_module'];ctor=b['constructor_module'];pos=b['positivity_module']
            lines += [f'theorem triangular{bi:02d} : lowerTriangularCheck {dm}.lRows = true := by decide +kernel',
                      f'theorem bundle{bi:02d}_accepted : Bundle.Accepted caseData bundle{bi:02d} := by',
                      f'  exact ⟨⟨{local}.basis{bi:02d}, {lay}.checked.1, {lay}.checked.2, rfl, rfl⟩, {ctor}.accepted, {pos}.checked, triangular{bi:02d}⟩',
                      f'#print axioms triangular{bi:02d}',f'#print axioms bundle{bi:02d}_accepted']
        proof='True.intro'
        for bi in reversed(range(len(pat['blocks']))):proof=f'And.intro bundle{bi:02d}_accepted ({proof})'
        lines += ['theorem accepted : caseData.Accepted := by',f'  exact ⟨metadata, {proof}⟩',
                  'theorem witness (h : Assembly.ConstructorPremises) : RawWitness (inputPattern caseData.input) :=',
                  '  Assembly.case_witness h accepted',
                  'theorem representative (h : Assembly.ConstructorPremises) :',
                  f'    inputCheck {inp}.input = true ∧ (inputPattern {inp}.input).Covered ∧ RawWitness (inputPattern {inp}.input) :=',
                  f'  ⟨{geo}.input_checked, h.covered _ {geo}.input_checked, witness h⟩',
                  '#print axioms accepted','#print axioms witness','#print axioms representative',f'end {cc}\n']
        write(cc,'\n'.join(lines));jobs.append(dict(module=cc,kind='case_assembly',deps=list(dict.fromkeys(imports)),pid=pid))
        pat['input_module']=inp;pat['geometry_module']=geo;pat['case_module']=cd;pat['case_check_module']=cc
        ks={tuple(s[:2]):s[2] for s in r['pattern']['sites']};bs={bond(tuple(a),tuple(b)) for a,b in r['pattern']['present']}
        items.append((key(ks,bs,tuple(r['pattern']['out'])),pid,inp,cc))
    plan['jobs']=jobs;plan['patterns']=list(patterns.values())
    plan['bridge']=dict(generated_mathematical_leaf_proofs=0,case_assemblies=len(items),input_compiler='AKLT.Cert.H1.Production.Input')
    output=args.output or REPORT/('pilot-complete.json' if len(items)<7962 else 'production-complete.json')
    output.write_text(json.dumps(plan,indent=2)+'\n')
    (REPORT/('pilot-representatives.json' if len(items)<7962 else 'representatives.json')).write_text(json.dumps(sorted(items),indent=2)+'\n')
    print(json.dumps(dict(patterns=len(items),modules=len(jobs),output=str(output))))

if __name__=='__main__':main()
