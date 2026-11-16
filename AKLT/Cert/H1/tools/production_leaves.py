#!/usr/bin/env python3
"""Exact closed generic leaves, replacing per-instance proof duplication.

This exporter writes no mathematical proof. The old registry is retained in
phase1/leaves.json, including attempt metadata and every exact old statement.
"""
import argparse, collections, hashlib, json, re
from pathlib import Path
from production_export import ROOT, REPORT
from production_build import guard as budget_guard, build_key, source_bytes

NS='AKLT.Cert.H1.Production'
PARENT=REPORT.parent

def props(path,namespace):
    text=path.read_text();matches=list(re.finditer(r'^def (\w+) : Prop :=\s*',text,re.M));out=[]
    for m in matches:
        end=re.search(r'\n(?=/--|/\*!|def |end\b)',text[m.end():])
        body=text[m.end():m.end()+end.start() if end else len(text)].strip()
        # Inter-declaration doc comments are not part of the proposition body.
        body=body.split('\n/--',1)[0].strip()
        out.append((namespace+'.'+m.group(1),body))
    return out

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--manifest',type=Path,default=REPORT/'production-ready.json')
    args=ap.parse_args()
    budget_guard()
    review=Path('/home/ubuntu/aklt/reports/ARCH_0/stmt-fix.md')
    oldpath=PARENT/'phase1/leaves.json';old=json.loads(oldpath.read_text())
    oldleaves={x['id']:x for x in old['proof_leaves']}
    prior=json.loads((PARENT/'leaves.json').read_text()) if (PARENT/'leaves.json').exists() else {}
    attempts={x['id']:x for x in prior.get('proof_leaves',[])}
    nodes=[]
    deps={
      'compilerGeometry':['inputCovered','compilerInversion'],
      'denominator':['momentPolynomial'],
      'basisIndexing':['compilerGeometry','parityCoverage'],
      'acceptedDecode':['signedPacking'],
      'sectorPackingExpansion':['compilerGeometry'],
      'sectorCoefficientBound':['compilerGeometry'],
      'packingDecode':['sectorPackingExpansion','sectorCoefficientBound','signedPacking'],
      'paritySlice':['compilerGeometry'],
      'momentPolynomial':['compilerGeometry'],
      'tensorSubstitution':['compilerGeometry'],
      'rawEncoding':[],
      'enumerationSoundness':[],
      'representativeCode':['inputCovered'],
      'sameDataWitness':['effectiveCodeClassification'],
      'mirrorDataWitness':['effectiveCodeClassification'],
    }
    for suffix in ['TopLeaves','Leaves']:
        path=ROOT/f'AKLT/Cert/H1/Production/{suffix}.lean';module=NS+'.'+suffix
        for name,body in props(path,module):
            short=name.rsplit('.',1)[1]
            status='OPEN'
            if short in ['integerCheckPremises','certificatePremises']:status='BUNDLE'
            if short=='rationalCurrent':status='DERIVED_AFTER_LEAVES'
            entry=dict(id=name,closed_prop=name,statement_lean=body,statement_module=module,
                statement_file=str(path.relative_to(ROOT)),statement_context=dict(namespace=module,open=['AKLT.Defs','AKLT.Gen.Gram'],scopes=['BigOperators','ComplexOrder'],section='noncomputable'),
                kind='proof' if status=='OPEN' else 'assembly_interface',status=status,
                dependencies=[NS+'.Leaves.'+d for d in deps.get(short,[])],
                statement_layer_dependencies=dict(repairs=[],rational_matrix_definitions_unchanged=True))
            if status=='OPEN':
                entry['first_attempt']=dict(required_route='different_cheaper_model',status='NOT_ATTEMPTED',root_may_prove=False)
                original='AKLT.Cert.H1.LeafStatements.'+short
                previous=attempts.get(name) or oldleaves.get(original)
                if previous and previous.get('statement_lean','').strip()==body:
                    for field in ['first_attempt','attempts','proof_file','writer','status','completion']:
                        if field in previous:entry[field]=previous[field]
                    entry['first_attempt']['required_route']='different_cheaper_model';entry['first_attempt']['root_may_prove']=False
                if suffix=='TopLeaves':entry['renamed_from']=original
            if short=='sectorPositiveImpliesBound':
                entry['statement_layer_dependencies']['repairs']=['F2','F3','F4']
                entry['statement_layer_dependencies']['note']='Exact rational target unchanged; generic analytic proofs should use Reduce/Inversion/OperatorStructure V2.'
                entry['suggested_lane']='BP_H1M'
            if short in ['basisIndexing','parityCoverage']:
                entry['statement_layer_dependencies']['repairs']=['A2']
                entry['statement_layer_dependencies']['note']='All ExchangeSigns remain quantified; ignored signs repeat a basis. No all-sign orthogonality premise.'
            if short in ['sameDataWitness','mirrorDataWitness','representativeWitnessLookup','representativesAppend']:
                entry['statement_layer_dependencies']['repairs']=['A1']
                entry['statement_layer_dependencies']['note']='RawWitness uses the new shared H1SectorWitnesses existence handoff.'
            if short=='rationalCurrent':
                entry['assembly']='AKLT.Cert.H1.Production.Assembly.rationalCurrent_of_leaves'
                entry['dependencies']=[NS+'.Leaves.'+d for d in ['momentPolynomial','tensorSubstitution','sectorLinearity']]
            nodes.append(entry)
    plan=json.loads(args.manifest.read_text());latest={}
    events=REPORT/'events.jsonl'
    if events.exists():
        for line in events.read_text().splitlines():
            try:x=json.loads(line)
            except json.JSONDecodeError:continue
            if x.get('exit')==0:latest[x['module']]=x
    modules=[]
    for j in plan['jobs']:
        path=ROOT/(j['module'].replace('.','/')+'.lean')
        rec={k:v for k,v in j.items() if k not in ['components','source_bytes']}
        rec['source_file']=str(path.relative_to(ROOT));rec['source_sha256']=hashlib.sha256(source_bytes(path)).hexdigest()
        if Path(str(path)+'.gz').exists():rec['source_archive_file']=str(Path(str(path)+'.gz').relative_to(ROOT))
        candidate=latest.get(j['module']);obj=path.with_suffix('.olean');checked=False
        if candidate and obj.exists():
            if all(d in latest for d in j['deps']):
                key,_=build_key(path,[latest[d] for d in j['deps']])
                checked=key==candidate.get('key') and hashlib.sha256(obj.read_bytes()).hexdigest()==candidate.get('artifact_sha256')
        rec['kernel_status']='KERNEL_CHECKED' if checked else 'NOT_RUN'
        rec['component_count']=len(j.get('components',[j['module']]))
        modules.append(rec)
    assembly_names=['rationalCurrent_of_leaves','case_denominator','matrix_from_stages','case_witness','finiteData_of_checks','certificateV2_of_checks']
    assemblies=[dict(theorem=NS+'.Assembly.'+n,status='PROVED_CONDITIONAL_ASSEMBLY',axioms=['propext','Classical.choice','Quot.sound']) for n in assembly_names]
    assemblies += [dict(theorem=NS+'.TopAssembly.'+n,status='PROVED_CONDITIONAL_ASSEMBLY',axioms=['propext','Classical.choice','Quot.sound']) for n in ['integerCheck_of_leaves','certificate_of_leaves','targets_of_leaves']]
    result=dict(format='cert-h1-production-leaves-v2',
      proof_policy=dict(root_new_mathematical_leaf_attempts=0,first_attempt_required='different_cheaper_model',allowed_root_work=['definitions','checkers','exporters','kernel computations','conditional assemblies']),
      statement_revision=dict(report=str(review),sha256=hashlib.sha256(review.read_bytes()).hexdigest(),finite_data_target='AKLT.Blueprint.Top.H1FiniteDataStatementV2',certificate_target='AKLT.Blueprint.Top.CertificateStatementV2',unchanged_targets=['AKLT.Blueprint.Top.IntegerCheckStatement','AKLT.Blueprint.Top.CertificateStatement']),
      proof_leaves=nodes,proof_leaf_counts=dict(collections.Counter(x['status'] for x in nodes)),
      assembly_nodes=assemblies,numerical_modules=modules,
      manifest=str(args.manifest),patterns=7962,blocks=12173,
      production_owner_map=plan['owner_modules'],
      legacy_registry=dict(path=str(oldpath),open_mathematical_statements=old['proof_leaf_counts']['OPEN'],status='PRESERVED_HISTORICAL_INTERFACES',replacement='Production generic compiler/packing/basis/coverage leaves and case assemblies; no old mathematical goal is claimed proved by this reorganization.',source_path_map=str(REPORT/'legacy-paths.json')),
      frozen_pre_rule_proofs=str(PARENT/'pre-rule-proofs.json'))
    result['pilot_manifest']=str(REPORT/'pilot-validation.json')
    result['preserved_legacy_audited_declarations']=321
    (PARENT/'leaves.json').write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
    compact=dict(format=result['format'],counts=result['proof_leaf_counts'],leaves=[{k:v for k,v in x.items() if k not in ['statement_lean','statement_context']} for x in nodes])
    (PARENT/'proof-leaf-index.json').write_text(json.dumps(compact,sort_keys=True,indent=2)+'\n')
    print(json.dumps(dict(counts=result['proof_leaf_counts'],numerical_modules=len(modules),conditional_assemblies=len(assemblies))))

if __name__=='__main__':main()
