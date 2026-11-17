from pathlib import Path
import json,re,hashlib
root=Path('/home/ubuntu/aklt/wt/BP_H1M'); report=Path('/home/ubuntu/aklt/reports/BP_H1M'); folder=root/'AKLT/Blueprint/H1'
baseline=json.loads((report/'adaptation-baseline-sha256.json').read_text())
for file,digest in baseline.items():assert hashlib.sha256((root/file).read_bytes()).hexdigest()==digest,file
old=json.loads((report/'leaves-before-adaptation.json').read_text())
replacements={
 'AffineEvaluationStatement':['AKLT.Blueprint.H1.AffineEvaluationStatementV2'],
 'PauliExpansionStatement':['AKLT.Blueprint.H1.PauliExpansionStatementV2'],
 'PauliProductTraceStatement':['AKLT.Blueprint.H1.PauliProductTraceStatementV2'],
 'ProductDensityPositiveStatement':['AKLT.Blueprint.H1.ProductDensityPositiveStatementV2'],
 'H1FiniteDataStatementV2':['AKLT.Blueprint.Top.H1FiniteDataStatementV2']}
for leaf in old:
 name=leaf['lean_name'].split('.')[-1];sup=name in replacements
 leaf['status']='superseded' if sup else 'kept'
 leaf['adaptation_status']=leaf['status']
 leaf['proof_status']='open historical statement; superseded in the active V2 blueprint' if sup else 'open'
 leaf['superseded_by']=replacements.get(name,[])
 leaf['adaptation_reason']='Wider real/arbitrary-finite contract or repaired shared handoff is used by V2 assemblies.' if sup else 'Statement is true unchanged and reused directly, or retained in the rational structural proof feeding real interpolation.'
 if name in ['InversionPolynomialStatement','DifferenceStructureStatement']:
  leaf['adaptation_reason']='Kept as a necessary rational prerequisite of the frozen operator-structure assembly. The wider real V2 counterpart is separate; no old statement is changed.'
# name | module | label | difficulty | estimated proof lines | definition/library inputs | proof route
rows='''
RationalEmbeddingStructureStatementV2|NodesV2Reduction|c:reduce|easy|20-80|AKLT.Defs.VectorAffine;AKLT.Defs.SupportedVectors;AKLT.Defs.VectorAffineReal;AKLT.Defs.SupportedVectorsReal;MvPolynomial.map|Use coefficient-map support inclusion. A coefficient embedding changes no monomial exponents, so vector degrees and absent-token exponents retain their bounds.
RationalEmbeddingEvaluationStatementV2|NodesV2Reduction|c:reduce|easy|5-30|AKLT.Defs.evaluateRealPolynomial;AKLT.Defs.evaluateReduced;MvPolynomial.map;MvPolynomial.eval₂|Commute polynomial evaluation with the rational-to-real coefficient map using the eval₂ composition identity. Keep this short fact open for the assigned first-attempt model.
DifferenceStructureStatementV2|NodesV2Reduction|c:reduce|medium|60-180|AKLT.Defs.VectorAffineReal;AKLT.Defs.SupportedVectorsReal;AKLT.Blueprint.H1.OrthogonalInvariantV2;MvPolynomial.C|Support of subtraction is contained in the union; multiplying by the real constant C c introduces no exponents. Ring-hom evaluation transfers the two covariance identities to the difference.
DifferenceEvaluationStatementV2|NodesV2Reduction|c:reduce|easy|10-50|AKLT.Defs.reducedDifferenceReal;AKLT.Defs.reducedPolynomialReal;AKLT.Defs.evaluateRealPolynomial;AKLT.Defs.evaluateReduced|Unfold the real difference and coefficient embedding, then use evaluation compatibility with map, subtraction, multiplication and constants. The threshold stays in R throughout.
AffineEvaluationStatementV2|NodesV2Reduction|c:reduce|medium|80-200|AKLT.Defs.VectorAffineReal;AKLT.Defs.evaluateRealPolynomial;AKLT.Blueprint.H1.SeparatelyAffine;Function.update|Expand real monomials. For each token the sum of the three coordinate exponents is at most one, so replacing that token by an affine combination distributes through every monomial.
PauliExpansionStatementV2|NodesV2Pauli|d:Pauli / l:inversion|medium|120-280|AKLT.Defs.RealVectorPolynomial;AKLT.Defs.VectorAffineReal;AKLT.Defs.SupportedVectorsReal;AKLT.Defs.pauliExponentReal;AKLT.Blueprint.H1.pauliCoordinate|Build the bijection between supported vector-affine monomials and J-to-Fin4 labels. Sum their evaluated coefficients. The empty active set is a singleton constant expansion.
PauliProductTraceStatementV2|NodesV2Pauli|l:inversion|medium|120-280|AKLT.Defs.pauliOperatorReal;AKLT.Defs.productDensityReal;AKLT.Defs.pauliExponentReal;Matrix.trace|Expand the matrix product and trace, interchange finite sums, factor the tensor-coordinate sums into products of one-slot traces, and apply the supplied scalar trace identity. Embed the real sum into C exactly.
InversionPolynomialStatementV2|NodesV2Pauli|l:inversion|medium|80-220|AKLT.Defs.invertPolynomialReal;AKLT.Defs.invertVectorsReal;AKLT.Defs.VectorAffineReal;AKLT.Defs.SupportedVectorsReal|Compute the coefficient signs on each monomial. Exponents are unchanged, and applying the sign substitution to both polynomial and vectors cancels every sign. No I-subset-J premise is needed for this stronger algebraic identity.
ProductDensityPositiveStatementV2|NodesV2Pauli|l:inversion|hard|150-350|AKLT.Defs.productDensityReal;AKLT.Defs.spinDensity;Matrix.PosSemidef.kronecker;Mathlib/Analysis/Matrix/Order.lean|Induct over the finite token set J, split the tensor function type at one coordinate, use PSD of the Kronecker product and transport across the explicit index equivalence. Handle the empty J as [1].
InversionBallStatementV2|NodesV2Pauli|l:inversion|easy|5-25|AKLT.Defs.invertVectorsReal;AKLT.Defs.normSq;AKLT.Defs.dot|Split membership in I and use invariance of the sum of coordinate squares under negation. This trivial fact remains an unproved leaf under the author's new rule.
RealDifferencePauliInterpolationStatementV2|NodesV2Structure|l:Ostruct|medium|60-180|AKLT.Defs.reducedDifferenceReal;AKLT.Defs.invertPolynomialReal;AKLT.Defs.pauliOperatorReal;AKLT.Defs.reducedDifference;AKLT.Defs.pauliOperator|Use coefficientwise real linearity of the Pauli map, inversion and rational coefficient embedding. The weights a=2-3c and b=3c-1 satisfy a+b=1 and a/3+2b/3=c. The exact Python prototype records these identities, not a Lean proof.
OperatorStructureLinearCombinationStatementV2|NodesV2Structure|l:Ostruct|medium|100-300|AKLT.Blueprint.H1.OperatorStructureAtV2;Matrix.toEuclideanLin;AKLT.Defs.symmetricPairProjection;Commute|Split the conjunction into Hermiticity, real entries, SU(2) commutators, the three End commutators, and pair properties. Every clause is real linear; distribute sums/scalars. No positivity or orthogonal-decomposition theorem is transferred.
'''.strip().splitlines()
metadata={}
for row in rows:
 name,module,label,difficulty,estimate,deps,route=row.split('|')
 metadata[name]={'module':module,'paper_label':label,'difficulty':difficulty,'estimated_proof_lines':[int(x) for x in estimate.split('-')],'dependencies':deps.split(';'),'suggested_proof_route':route}
checks={
'premises':'All required mathematical premises are explicit. The definition is a closed Prop and assumes no other blueprint leaf proposition.',
'vacuity_and_degenerate':'Finite empty sums/products use their usual conventions; vector and coefficient zeros are allowed.',
'coercions':'Exact Q-to-R and R-to-C ring embeddings only; no floating-point arithmetic or R-to-Q coercion.',
'finite_sums':'Use Finset support/site sums versus Fintype label/tensor sums exactly as typed, with explicit finite reindexing.',
'nat_subtraction':'No unguarded natural subtraction is introduced.',
'division_by_zero':'No variable denominator occurs. Fixed fractions 1/3 and 2/3 have positive nonzero denominators.',
'instances':'No ambient section variables; all finite token subtypes and function types retain their standard Fintype and DecidableEq instances.'}
overrides={
'RationalEmbeddingStructureStatementV2':{'premises':'Affineness and support of the rational polynomial are explicit; support inclusion suffices even if a coefficient map deletes terms.'},
'RationalEmbeddingEvaluationStatementV2':{'coercions':'Both evaluations take values in R. The rational coefficients are embedded once using Rat.castHom R; no change to vector coordinates.'},
'DifferenceStructureStatementV2':{'premises':'Affineness, invariance and support are supplied separately for both polynomials. c is arbitrary real, not restricted to rational thresholds.'},
'DifferenceEvaluationStatementV2':{'coercions':'c is a real scalar multiplying the rational-to-real evaluations; no c-as-rational term appears anywhere.'},
'AffineEvaluationStatementV2':{'premises':'Whole-vector degree <=1 is essential; coordinatewise multiaffineness alone would be insufficient. The output is the existing 20-token affine-function predicate needed for the unchanged convex-extension leaf.'},
'PauliExpansionStatementV2':{'vacuity_and_degenerate':'For n=0, necessarily J is empty and J->Fin4 has one member. The operator is scalar on C, not a zero-dimensional matrix. J empty is also allowed for positive n.', 'nat_subtraction':'The unchanged pauliCoordinate uses a.val-1 only after the a.val=0 guard; its index proof is retained in the frozen definition.'},
'PauliProductTraceStatementV2':{'premises':'The mathematical one-slot trace identity is explicit; affineness is unnecessary because both sides select the same Pauli exponents. Irrational real coefficients are permitted.'},
'InversionPolynomialStatementV2':{'premises':'Affineness/support are explicit; sign cancellation is valid even when I is not a subset of J. The public Top contract imposes I subset J when used.'},
'ProductDensityPositiveStatementV2':{'premises':'Every individual density on J is assumed PSD; no invertibility, positive definiteness, or trace normalization is needed by this tensor-positivity step.', 'vacuity_and_degenerate':'J empty yields the 1-by-1 matrix [1]. Arbitrary n and token counts above 20 are permitted.'},
'InversionBallStatementV2':{'vacuity_and_degenerate':'n=0 makes the j quantifier empty; for n>0 the equality also holds at the zero vector.'},
'RealDifferencePauliInterpolationStatementV2':{'premises':'The identity holds for arbitrary real c and any inversion; neither coveredness nor group inversion is needed for coefficientwise linearity.', 'vacuity_and_degenerate':'At c=1/3 or 2/3 one interpolation weight vanishes. Weights may be negative elsewhere; this is not interpolation of PSD/PD.', 'coercions':'The exact rational matrices at thresholds 1/3 and 2/3 are multiplied by real weights embedded in C. No rational approximation to c is used.'},
'OperatorStructureLinearCombinationStatementV2':{'premises':'Both input matrices satisfy the explicit mathematical predicate OperatorStructureAtV2. This predicate contains no positivity claim, so real coefficients of either sign are legitimate.', 'vacuity_and_degenerate':'Zero coefficients, the zero matrix, empty groups, and empty tensors are allowed. Fixed pair projections are shared by both input properties.'}}
new=[];newdefs=[]
for f in sorted(folder.glob('NodesV2*.lean')):
 text=f.read_text()
 for m in re.finditer(r'^def (\w*StatementV2) : Prop',text,re.M):
  name=m.group(1);end=text.find('\n\n',m.start());end=end if end>=0 else len(text);body=text[m.start():end];newdefs.append((name,body,f,m.start()))
  if name not in metadata:continue
  data=metadata[name];entry={'lean_name':'AKLT.Blueprint.H1.'+name,**data,'module':'AKLT.Blueprint.H1.'+data['module'],'status':'open','adaptation_status':'new','proof_status':'open','file':str(f),'line':text[:m.start()].count('\n')+1,'closed_statement':body,'paper_reference':{'report':'/home/ubuntu/aklt/reports/REF2_7/report.md','paper':'Appendix D; D.4 reduction, D.5-D.6 Pauli inversion, D.7 operator structure','repair_report':'/home/ubuntu/aklt/reports/ARCH_0/stmt-fix.md; F2/F3/F4'},'ownership':'H1 proof writer; first attempt must be a different, cheaper model','proof_policy':{'status':'open','first_attempt_required_from':'a different, cheaper model than the blueprint architect','blueprint_architect_may_prove':False,'applies_to_checker_soundness':True,'proof_attempts_by_architect_after_rule_update':0},'trap_check':{**checks,**overrides.get(name,{})},'reuse_pointers':['Frozen AKLT/Blueprint/H1 definitions and existing assembly implications','Pinned Mathlib polynomial, finite-sum and matrix libraries'],'supersedes':[]}
  for before,after in replacements.items():
   if entry['lean_name'] in after:entry['supersedes'].append('AKLT.Blueprint.H1.'+before)
  if name=='InversionPolynomialStatementV2':entry['adaptation_note']='Generalizes the old leaf for inversion; the old rational leaf stays kept for rational operator-structure prerequisites.'
  if name=='DifferenceStructureStatementV2':entry['adaptation_note']='Real-threshold extension; the rational old leaf stays kept inside the reused rational operator assembly.'
  new.append(entry)
assert {x['lean_name'].split('.')[-1] for x in new}==set(metadata)
# The repaired Top owns the data-existence obligation; the H1-local declaration is frozen and superseded.
f=root/'AKLT/Blueprint/Top/Operator.lean';text=f.read_text();name='H1FiniteDataStatementV2';start=text.index('def '+name+' : Prop');end=text.find('\n\n',start);body=text[start:end]
external=next(x.copy() for x in old if x['lean_name']=='AKLT.Blueprint.H1.H1FiniteDataStatementV2')
external.update(lean_name='AKLT.Blueprint.Top.H1FiniteDataStatementV2',module='AKLT.Blueprint.Top.Operator',file=str(f),line=text[:start].count('\n')+1,closed_statement=body,status='open',adaptation_status='new shared contract',proof_status='open',superseded_by=[],supersedes=['AKLT.Blueprint.H1.H1FiniteDataStatementV2'],ownership='external certificate-data owner; shared contract added by ARCH_0',adaptation_reason='ARCH_0 A1 adopted the missing finite-data handoff. H1 uses shared definitions via aliases and definitionally compatible old assemblies.')
external['dependencies']=['AKLT.Defs.H1SectorWitnesses','AKLT.Defs.h1Numerator','AKLT.Defs.h1Denominator','AKLT.Defs.GroupInversion','AKLT.Defs.ClearsDenominator','AKLT.Gen.Gram.checker_sound_complex']
external['suggested_proof_route']='External CERT_H1 owner must produce complete covered-pattern coverage and all regenerated sector witnesses for the shared Top proposition. Witness export/checking remains an independent obligation; no data are supplied by the H1 analytic assembly.'
external['proof_policy']['blueprint_architect_may_prove']=False
new.append(external)
manifest=old+new
assert len(old)==55 and len(new)==13 and sum(x['status']=='superseded' for x in manifest)==5
(report/'leaves.json').write_text(json.dumps(manifest,indent=2)+'\n')
(report/'leaves-v2-active.json').write_text(json.dumps([x for x in manifest if x['status']!='superseded'],indent=2)+'\n')
(report/'new-leaves-v2.json').write_text(json.dumps(new,indent=2)+'\n')
oldnodes=json.loads((report/'nodes.json').read_text())
for n in oldnodes:
 short=n['lean_name'].split('.')[-1];n['adaptation_status']='superseded' if short in replacements or short=='CertificateStatementV2' else 'kept'
(report/'nodes-adaptation.json').write_text(json.dumps(oldnodes,indent=2)+'\n')
# Exact statements of new open and assembled nodes, with new theorem signatures.
theorems=[];text=(folder/'AssemblyV2.lean').read_text()
for m in re.finditer(r'^theorem (\w+)',text,re.M):
 end=text.index(':=',m.start());theorems.append({'lean_name':'AKLT.Blueprint.H1.'+m.group(1),'signature':text[m.start():end].strip(),'file':str(folder/'AssemblyV2.lean'),'line':text[:m.start()].count('\n')+1,'classification':'proved assembly; no leaf proof'})
assert len(theorems)==15
exports=['# V2 exact declarations','','Namespace for H1-local declarations: `AKLT.Blueprint.H1`. Definitions and open leaves are not asserted as facts.','']
for name,body,f,start in newdefs:exports+=['```lean',body,'```','']
exports+=['```lean',external['closed_statement'],'```','']
for t in theorems:exports+=['```lean',t['signature'],'```','']
(report/'declarations-v2.md').write_text('\n'.join(exports))
traps=['# V2 per-leaf trap checks','','Old kept/superseded leaf checks are preserved in `leaves.json` and `trap-check.md`. All 13 new manifest entries are audited below.','']
for x in new:
 traps+=['## '+x['lean_name'],'']
 for k,v in x['trap_check'].items():traps+=['- **'+k+'**: '+v]
 traps+=['']
(report/'trap-check-v2.md').write_text('\n'.join(traps))
# Preserve baseline source bytes and inventory all newly proved assemblies.
verified={str(p):hashlib.sha256((root/p).read_bytes()).hexdigest()==d for p,d in baseline.items()};assert all(verified.values())
(report/'adaptation-preservation.json').write_text(json.dumps({'unchanged_pre_existing_files':verified,'frozen_leaf_files':[p for p in baseline if Path(p).name.startswith('Nodes')],'new_assembly_theorems':theorems,'new_leaf_proofs_written':0},indent=2)+'\n')
(report/'proof-ownership-adaptation.json').write_text(json.dumps({'rule':'No new leaf proofs by the blueprint architect; first attempt assigned to a different, cheaper model.','retained_inventory':'proof-ownership.json','new_declarations_proved':theorems,'all_new_proofs_are_assemblies':True,'new_leaf_proofs_written':0},indent=2)+'\n')
# Extract exact audit output without rerunning any Lean proof or check.
log=(report/'adaptation-build.log').read_text();lines=log.splitlines();at=None
for i,line in enumerate(lines):
 if line.startswith('{"module":') and json.loads(line)['module']=='AKLT.Blueprint.H1.AuditV2':at=i+1
assert at is not None
raw='\n'.join(lines[at:]).strip()+'\n';audit=[line for line in raw.splitlines() if "'AKLT.Blueprint.H1." in line and 'depends on axioms:' in line]
assert len(audit)==40
for line in audit:
 deps=re.search(r'\[([^]]*)\]',line).group(1)
 assert set(x.strip() for x in deps.split(',') if x.strip())<={'propext','Classical.choice','Quot.sound'}
(report/'axioms-v2.txt').write_text(raw)
state={'old_leaves':55,'old_kept':50,'old_superseded':5,'new_mathematical_leaves':12,'new_external_shared_data_contracts':1,'current_open':63,'manifest_records':68,'new_assemblies':15,'total_exported_theorem_audits':40,'new_closure_checks':18,'old_source_files_preserved':11,'new_source_files':7,'new_leaf_proofs':0}
(report/'adaptation-state.json').write_text(json.dumps(state,indent=2)+'\n')
print(json.dumps(state))
