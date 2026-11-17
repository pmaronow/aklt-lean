#!/usr/bin/env python3
"""Emit exact closed writer leaves, declaration/axiom audit and production inventory."""
from __future__ import annotations
import collections,hashlib,json,pathlib,re,time,os
ROOT=pathlib.Path(__file__).resolve().parents[3]
REPORT=pathlib.Path('/home/ubuntu/aklt/reports/CERT_H3')
PHASE=pathlib.Path(os.environ.get('H3_REPORT_DIR',str(REPORT/'phase2')))
BASE='CertData.H3.Bridge'

def decls(p):
    s=p.read_text();ns=re.search(r'^namespace ([\w.]+)',s,re.M)[1]
    starts=list(re.finditer(r'^(?:noncomputable )?(?:def|abbrev|theorem)\s+([\w]+)',s,re.M))
    for i,m in enumerate(starts):
        end=starts[i+1].start() if i+1<len(starts) else s.rfind('\nend ')
        text=s[m.start():end].strip();text=re.split(r'\n(?:#print|/--|/-!)',text)[0].rstrip()
        yield ns+'.'+m[1],text,s[:m.start()].count('\n')+1

def main():
    manifest=json.loads((PHASE/'build_manifest.json').read_text())
    measured={}
    for l in (PHASE/'measurements.jsonl').read_text().splitlines():
        r=json.loads(l)
        if not r.get('resumed'):measured[r['module']]=r
    handwritten=[ROOT/'CertData/H3/Bridge/Interface.lean',ROOT/'CertData/H3/Bridge/Production.lean',ROOT/'CertData/H3/Bridge/LegacyTargets.lean']
    cases=[ROOT/f'CertData/H3/Bridge/{tag}.lean' for tag in ['B1','B2','C1','C2','C3']]
    leaves=[]
    for p in handwritten+cases+[ROOT/'CertData/H3/Kernel/Rows.lean']:
        for name,body,line in decls(p):
            local=name.rsplit('.',1)[-1]
            if not (local.endswith('Leaf') or local=='RowTermsAgreement'):continue
            assert re.match(r'def \w+\s*:\s*Prop\s*:=',body),body[:100]
            mod=str(p.relative_to(ROOT).with_suffix('')).replace('/','.')
            dependencies=[]
            if local in {'PlaneSoundLeaf','RowTermsV2Leaf','CentreZeroV2Leaf','PassesEquivalenceLeaf'}:dependencies.append('F9')
            if p.name=='Production.lean' or local in {'RawTrieBoundsLeaf','RepresentativeBoundsLeaf','FieldCheckSoundLeaf'}:dependencies.append('F7')
            checked=p.with_suffix('.olean').exists() and p.with_suffix('.olean').stat().st_mtime_ns>=p.stat().st_mtime_ns
            leaves.append(dict(id=name,name=name,status='OPEN',role='mathematical_leaf',source=str(p.relative_to(ROOT)),line=line,
                imports=re.findall(r'^import (\S+)',p.read_text(),re.M),closed_lean_declaration=body,
                proof_statement=name,expected_proof_declaration='CertData.H3.Proofs.'+local+'.checked',proof_file='CertData/H3/Proofs/'+local+'.lean',closed=True,
                first_attempt='REQUIRED_FROM_A_DIFFERENT_CHEAPER_MODEL',attempted_here=False,
                declaration_module_kernel_checked=checked,statement_revision_dependencies=dependencies,
                dependencies=[],supporting_kernel_checks=[]))
    bylocal={x['name'].rsplit('.',1)[-1]:x for x in leaves if x['source'].endswith('/Interface.lean')}
    edges={
      'RawReplaySoundLeaf':['CodeDecodeLeaf','CodeEncodeLeaf'],
      'RawReplayCompleteLeaf':['CodeDecodeLeaf','CodeEncodeLeaf'],
      'LegalDirectionLeaf':['CodeEncodeLeaf'],
      'RawRowSoundLeaf':['LegalDirectionLeaf','RevisitLeaf','SuccessorCodeLeaf'],
      'RawTrieCoverageLeaf':['RawReplaySoundLeaf','RawReplayCompleteLeaf'],
      'RawTrieProjectionLeaf':['RawRowSoundLeaf','RawTrieCoverageLeaf','RawReplaySoundLeaf'],
      'RawTrieBoundsLeaf':['RawTrieCoverageLeaf'],
      'RawTrieCountLeaf':['RawReplaySoundLeaf','RawReplayCompleteLeaf','CodeEncodeLeaf'],
      'RowTermsV2Leaf':['OrdinaryMaskLeaf','KnownMaskLeaf','DeadMaskLeaf','PullLeaf','CentreZeroV2Leaf'],
      'PlaneSoundLeaf':['TableBoundsLeaf','FreeRowLeaf','RowTermsV2Leaf'],
      'RowCoverageLeaf':['PlaneBatchSoundLeaf','IntervalCoverageLeaf'],
      'EndpointTableSoundLeaf':['RectangleLeaf','TableBoundsLeaf'],
      'PrefixReplaySoundLeaf':['PrefixStepLeaf','CodeDecodeLeaf'],
      'PrefixReplayCompleteLeaf':['CodeEncodeLeaf','PrefixReplaySoundLeaf'],
      'ShortValueLeaf':['ShortComparatorLeaf'],
      'PrefixBatchSoundLeaf':['PrefixReplaySoundLeaf','PrefixReplayCompleteLeaf','PrefixStepLeaf','ShortValueLeaf','LastWindowCodeLeaf','EndpointBoxLeaf'],
      'EarlySoundLeaf':['PrefixStepLeaf','ShortValueLeaf'],
      'PrefixPartitionLeaf':['CodeEncodeLeaf','CodeDecodeLeaf'],
      'SemanticBatchSplitLeaf':['IntervalCoverageLeaf'],
      'PrefixResultsJoinLeaf':['ResultAddLeaf','SemanticBatchSplitLeaf'],
      'RationalCeilingLeaf':['NumericScaleLeaf'],
      'UniformRowCoverageLeaf':['PlaneBatchSoundLeaf','RowCoverageLeaf'],
      'PrefixFamilyJoinLeaf':['PrefixResultsJoinLeaf']}
    for local,deps in edges.items():
        if local in bylocal:bylocal[local]['dependencies']=[BASE+'.'+d for d in deps]
    for x in leaves:
        local=x['name'].rsplit('.',1)[-1]
        if local in {'SpanDataLeaf','ClassDataLeaf'}:x['supporting_kernel_checks']=['CertData.H3.Check.BlockLookup.checked','CertData.H3.Check.GraphTables.checked','CertData.H3.Check.SuppliedTables.checked']
        if local in {'QuotientDataLeaf','UnmaskedDataLeaf','DecodeDataLeaf'}:x['supporting_kernel_checks']=['CertData.H3.Check.SuppliedTables.checked']
        if local=='RawShardJoinLeaf':x['supporting_kernel_checks']=['CertData.H3.GraphAssembly.all_raw_checked','CertData.H3.GraphAssembly.count_checked']
        if local=='RepresentativeJoinLeaf':x['supporting_kernel_checks']=['CertData.H3.GraphAssembly.representatives_checked']
        if local=='FieldJoinLeaf':x['supporting_kernel_checks']=['CertData.H3.GraphAssembly.fields_checked']
        if local=='RowEnumerationLeaf':
            tag=pathlib.Path(x['source']).stem;x['dependencies']=[BASE+'.RowCoverageLeaf'];x['supporting_kernel_checks']=[f'CertData.H3.{tag}.RowAssembly.all_checked']
        if local=='EndpointLeaf':
            tag=pathlib.Path(x['source']).stem;x['dependencies']=[BASE+'.EndpointTableSoundLeaf',f'CertData.H3.Bridge.{tag}.RowEnumerationLeaf'];x['supporting_kernel_checks']=[f'CertData.H3.{tag}.RowAssembly.checked']
        if local=='PrefixJoinLeaf':
            tag=pathlib.Path(x['source']).stem;x['dependencies']=[BASE+'.PrefixResultsJoinLeaf'];x['supporting_kernel_checks']=[f'CertData.H3.{tag}.PrefixAssembly.all_checked',f'CertData.H3.{tag}.PrefixAssembly.totals_equal',f'CertData.H3.{tag}.Check.Summary.coverage_checked']
        x['writer_scope']='Prove precisely this closed Prop; reuse dependencies and checked computations. Do not re-run the full numerical certificate in a single reduction.'
    jobs=[];exports=[];axioms=[];failure=[]
    compact_path=PHASE/'compacted_sources.json'
    compacted=json.loads(compact_path.read_text()) if compact_path.exists() else {}
    for j in manifest['jobs']:
        r=measured.get(j['module'],{});p=ROOT/j['source'];checked=r.get('exit')==0 and p.with_suffix('.olean').exists() and (not p.exists() and j['module'] in compacted or p.exists() and p.with_suffix('.olean').stat().st_mtime_ns>=p.stat().st_mtime_ns)
        jj=dict(j,status='KERNEL_CHECKED' if checked else 'GENERATED_NOT_RUN')
        if checked:jj['measurement']={k:r[k] for k in ['wall','user_s','sys_s','rss_kib','olean_bytes'] if k in r}
        jobs.append(jj)
        if j['kind'] in {'plane_data','endpoint_data','caps','graph','exact','tables','plane_catalog','endpoint_catalog'}:continue
        for name,body,line in decls(p):
            if not body.startswith('theorem '):continue
            statement=body.split(':=',1)[0].strip()
            exports.append(dict(name=name,module=j['module'],source=j['source'],line=line,statement=statement,
                checked=checked,role='kernel_computation' if 'decide +kernel' in body else 'assembly'))
        if checked:
            log=pathlib.Path(r['log']).read_text()
            if re.search(r'error:|sorryAx',log):failure.append(j['module'])
            for name in re.findall(r"'([^']+)' does not depend on any axioms",log):axioms.append(dict(name=name,axioms=[]))
            for name,deps in re.findall(r"'([^']+)' depends on axioms: (\[[^\]]*\])",log,re.S):
                arr=[a.strip() for a in deps[1:-1].replace('\n','').split(',') if a.strip()]
                if not set(arr)<={'propext','Classical.choice','Quot.sound'}:failure.append([name,arr])
                axioms.append(dict(name=name,axioms=arr))
    # Generic interface's assemblies are bootstrapped rather than ordinary jobs.
    p=ROOT/'CertData/H3/Bridge/Interface.lean'
    for name,body,line in decls(p):
        if body.startswith('theorem '):exports.append(dict(name=name,module='CertData.H3.Bridge.Interface',source=str(p.relative_to(ROOT)),line=line,statement=body.split(':=',1)[0].strip(),checked=p.with_suffix('.olean').exists(),role='assembly'))
    log=PHASE/'bootstrap_Bridge_Interface.log' if (PHASE/'bootstrap_Bridge_Interface.log').exists() else PHASE/'bootstrap_Interface.log'
    if log.exists():
        for name,deps in re.findall(r"'([^']+)' depends on axioms: (\[[^\]]*\])",log.read_text(),re.S):
            arr=[a.strip() for a in deps[1:-1].replace('\n','').split(',') if a.strip()]
            if not set(arr)<={'propext','Classical.choice','Quot.sound'}:failure.append([name,arr])
            axioms.append(dict(name=name,axioms=arr))
    pre=json.loads((REPORT/'pre_rule_proofs.json').read_text());post=json.loads((REPORT/'post_rule_assemblies.json').read_text())
    out=dict(schema=3,task='CERT_H3_PHASE2',scope='Five stationary H3 certificates; B1 full production pilot',
      proof_policy='No new written mathematical leaf proof attempted here. Existing phase-1 proofs retained; new mathematical leaves require first attempt by a different cheaper model. Kernel computations and blueprint assemblies are permitted.',
      dependency_manifest='phase2/dependencies.json',statement_revision=dict(F7='Final supplied-data V2 contract, including unmasked field bounds and sentinels',F8='Phase expansion was restricted to closed trails; the numerical prefix definitions used here are unchanged; no expansion theorem is assumed',F9='The V2 center guard is handled by zero-center refinement leaves'),
      mathematical_leaves=leaves,mathematical_leaf_count=len(leaves),
      retained_pre_rule_proofs=pre,retained_phase1_assemblies=post,
      assemblies=[x for x in exports if x['role']=='assembly'],check_modules=jobs,
      generated_unexecuted_cases=['B2','C1','C2','C3'],
      legacy_leaf_manifest='phase1/leaves.json (superseded route, preserved for the grandfathered legacy assemblies)',
      full_family_assembly='CertData.H3.Bridge.stationaryV2_from_family_checks',
      final_concrete_composition='CertData.H3.Bridge.All.stationary_from_leaves (generated; imports the four not-yet-executed cases)',
      limitations=['No mathematical soundness leaf is proved here.','The four nonpilot cases are generated, not kernel executed.','H1 is outside the CERT_H3 namespace and is not claimed.'])
    (REPORT/'leaves.json').write_text(json.dumps(out,indent=2)+'\n')
    (PHASE/'exported_declarations.json').write_text(json.dumps(exports,indent=2)+'\n')
    (PHASE/'axioms.json').write_text(json.dumps(axioms,indent=2)+'\n')
    (PHASE/'check_status.json').write_text(json.dumps(jobs,indent=2)+'\n')
    (PHASE/'leaf_statements.txt').write_text('\n\n'.join('-- '+x['name']+'\n'+x['closed_lean_declaration'] for x in leaves)+'\n')
    checked_leaves=[x for x in leaves if x['declaration_module_kernel_checked']]
    imports=['CertData.H3.Bridge.Interface','CertData.H3.Bridge.Production','CertData.H3.Bridge.LegacyTargets','CertData.H3.Bridge.FamilyAssembly']
    for tag in ['B1','B2','C1','C2','C3','All']:
        p=ROOT/f'CertData/H3/Bridge/{tag}.lean'
        if p.with_suffix('.olean').exists() and p.with_suffix('.olean').stat().st_mtime_ns>=p.stat().st_mtime_ns:imports.append('CertData.H3.Bridge.'+tag)
    audit='\n'.join('import '+m for m in imports)+'\nset_option pp.universes true\n'
    audit+='\n'.join('#check ('+x['name']+' : Prop)\n#print '+x['name'] for x in checked_leaves)+'\n'
    # One check on each top assembly's exact statement and axioms.
    for x in exports:
        if x['role']=='assembly' and x['module'] in imports:
            audit+='#check '+x['name']+'\n#print axioms '+x['name']+'\n'
    ap=ROOT/'CertData/H3/Bridge/Audit.lean'
    if not ap.exists() or ap.read_text()!=audit:ap.write_text(audit)
    summary=dict(leaves=len(leaves),declaration_modules_checked=sum(x['declaration_module_kernel_checked'] for x in leaves),
      jobs=len(jobs),checked_jobs=sum(x['status']=='KERNEL_CHECKED' for x in jobs),exported_theorems=len(exports),axiom_audits=len(axioms),bad_axioms_or_logs=failure)
    (PHASE/'audit.json').write_text(json.dumps(summary,indent=2)+'\n');print(json.dumps(summary,indent=2))
    if failure:raise SystemExit(1)
if __name__=='__main__':main()
