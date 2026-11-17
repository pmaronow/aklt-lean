from pathlib import Path
import re,json
OUT=Path('/home/ubuntu/aklt/reports/VENDOR_1')
plan=Path('/home/ubuntu/aklt/reports/REV-PLAN/PLAN.md').read_text()
rows=re.findall(r'^### ([^\s]+) — (.+)$',plan,re.M)
P='AKLT.Vendor.'
D={}
def put(ids,names,relation):
 for i in ids.split():D[i]=([P+n for n in names],relation)
put('l:CE',['FiniteConditioning.condExp_on_fiber','FiniteConditioning.condExp_eq_of_fiber_integrals'], 'Fibre conditional-mean identification only. Orthogonal projection, total variance, complex values, and finite-product specialization remain a bridge; use the pinned Mathlib L2 conditional expectation API.')
put('l:finitecoupling',['FiniteChain.finiteTotalVariation','FiniteChain.finiteTotalVariation_contraction','FiniteChain.finiteTotalVariation_le_one'], 'Half-L1 TV and stochastic-kernel contraction. Marginalization needs its deterministic stochastic kernel; overlap, maximal coupling, completion and Hamming estimate are new finite lemmas. No donor supplies this entire statement.')
put('l:surgery',['FiniteConditioning.condExp_on_fiber','FiniteConditioning.condExp_eq_of_fiber_integrals'], 'Supports disintegration into fibres; pair-dependent kernel preservation and composition are new finite-sum identities.')
put('l:density',['FiniteChain.Cheeger.weightedVariance_le_center','FiniteChain.finiteDirichletForm'], 'Variational-centering ingredient and Dirichlet form only. Conditional-variance variational formula, product tensorization and the one-ratio density comparison are new.')
put('l:comparison',['FiniteChain.finiteDirichletForm_eq_neg_generator','FiniteConditioning.condExp_on_fiber'], 'Quadratic-form/generator and fibre ingredients; repeated-label conditional-variance summation and multiplicity estimate are new.')
put('l:contraction t:periodic',['QICLean.Matrix.IsHermitian.toEuclideanCLM_eigenvectorBasis','QICLean.OrthonormalBasis.re_inner_apply_eq_sum_of_eigen','QICLean.Matrix.IsHermitian.mul_norm_sq_le_re_inner_of_spectral_gap'], 'Finite self-adjoint spectral ingredients only. Conjugation from weighted reversible L2, Hamming Lipschitz contraction, singleton case, block counts and clock normalization remain to be proved. TV contraction is not Hamming contraction.')
put('d:poly',['Physlib.Sl2.StandardSl2Module'], 'Finite polynomial carrier model only; the chosen monomial norm and polynomial/sl2 identification are new.')
put('l:edge',['Physlib.Sl2.cgEquiv','Physlib.Sl2.cgEquiv_tensorE','Physlib.Sl2.cgEquiv_tensorF','Physlib.Sl2.cgEquiv_tensorH','Physlib.Sl2.cgProj_isTensorIntertwiner','Physlib.Sl2.IsTensorIntertwiner.eq_zero_of_forall_ne','Physlib.Sl2.IsTensorIntertwiner.exists_eq_smul_cgProj'], 'The complete tensor sl2 decomposition/intertwiner algebra is reusable (m=n=4). Polynomial multiplication, the determinant factor, Hermitian orthogonality and the specified normalization remain bridges; this does not by itself prove the edge-kernel equality.')
put('l:divisibility p:toruskernel',['Physlib.Sl2.IsTensorIntertwiner.eq_zero_of_forall_ne'], 'Edge-sector ingredient via l:edge only. UFD irreducibility/nonassociation, local divisibility, product degree and torus uniqueness are new, over Mathlib polynomial algebra.')
put('l:star',['Physlib.Sl2.cgEquiv_tensorH','QICLean.Matrix.IsHermitian.mul_norm_sq_le_re_inner_of_spectral_gap'], 'Finite sector/spectral tools only. The actual fixed-star operator and its comparison are new.')
put('d:frame l:tight',['QICLean.Matrix.IsIsometry','QICLean.Matrix.IsCoisometry','QICLean.Matrix.IsUnitaryBetween','QICLean.Matrix.IsIsometry.isUnitaryBetween_of_card_eq'], 'Finite coordinate isometry/coisometry algebra only. A rectangular frame uses the appropriate one-sided identity; equal-cardinality unitarity is not a tight-frame assertion for a 12x5 synthesis matrix. Spinors, fourth moments and the explicit resolution identity are new.')
put('l:quantumfibre t:QD',['QICLean.Matrix.conjTranspose_mul_mul_eq_conjTranspose_mul_iff_of_mul_eq_one','QICLean.Matrix.IsHermitian.mul_norm_sq_le_re_inner_of_spectral_gap'], 'Finite matrix cancellation and spectral quadratic-form tools only. The signed coherent transform, frame weights and fibre comparison require the campaign-specific construction.')
put('l:cut',['FiniteConditioning.condIndep_of_fiber_indep','FiniteConditioning.condExp_on_fiber'], 'Fibre independence/conditioning infrastructure; graph partition-factorization, strict common law and quantitative minorization are new.')
put('l:boundaryconn l:Xconn',['Balaban.LatticeGeom.exists_primitive_of_closed','Balaban.LatticeGeom.outerBoundary_mateConn','Balaban.LatticeGeom.outerBoundary_starConn','Balaban.LatticeGeom.exteriorBoundary_starConn'], 'Timar/cochain ingredients only. Donor assumes NN-connected sets (and uses the NN vertex boundary); the plan assumes star-connectivity and uses the full sup-distance-one boundary. A triangular/star-adjacency argument or proved reduction is required. No implication between these hypotheses is assumed.')
put('l:thicken',['Balaban.LatticeGeom.Conn','Balaban.LatticeGeom.StarNear','Balaban.LatticeGeom.StarConn'], 'Definitions and finite path infrastructure only; connected union of crosses and weighted distance/count estimate are new. Timar does not assert this bound.')
put('l:sector l:Ostruct',['Physlib.Sl2.tensorH_hwVec','Physlib.Sl2.tensorE_hwVec','Physlib.Sl2.tensorStringBasis','Physlib.Sl2.cgEquiv_tensorH','Physlib.Sl2.cgEquiv_tensorE','Physlib.Sl2.cgEquiv_tensorF'], 'Reusable finite ladder/tensor representation algebra. Identifying the actual Pauli/exchange representation, its adjoints, the central weight and eigenvalue detection for those matrices are new.')
put('l:log-mean-bounds',['LeanCert.Core.Dyadic.toRat_add','LeanCert.Core.Dyadic.toRat_mul','LeanCert.Core.Dyadic.toRat_shiftDown_le','LeanCert.Core.Dyadic.toRat_shiftUp_ge'], 'Exact dyadic arithmetic/directed rounding only; logarithmic-mean analytic inequalities and the stated rational table are new. No interval/log evaluator is imported.')
put('d:stationary-certificate p:stationary-check l:stationary-assembly l:integercheck p:certificate p:H2-test p:automaton10',['LeanCert.Core.Dyadic.toRat_add','LeanCert.Core.Dyadic.toRat_mul','LeanCert.Core.Dyadic.le_iff_toRat_le','LeanCert.Core.Dyadic.toRat_normalizeDown_le','LeanCert.Core.Dyadic.toRat_normalizeUp_ge'], 'Exact arithmetic soundness only; fixed-exponent dyadics can interpret integer-scaled data. No automaton, matrix reconstruction, Bellman checker, certificate data or large computation is supplied by this vendoring task.')
for key,_ in rows:
 if key not in D:
  if key.startswith(('d:','h:')):D[key]=([], 'Campaign-specific definition or contract. No donor theorem is claimed; implement the stated finite objects directly with Mathlib and the listed arithmetic/linear-algebra primitives.')
  elif key in ['l:moments','l:finitefacts','l:35','l:exact','l:threeframes','l:qmod']:
   D[key]=([], 'New finite moment/frame calculation. The continuous-sphere donors are excluded; derive the exact finite sums/algebra in the campaign definitions.')
  elif key in ['l:colour','l:planeenergy','l:boxlift','l:shellgeom','l:cutgeom','l:removal']:
   D[key]=([], 'New finite physical-site combinatorial/algebraic proof. No audited donor matches this statement; no cell/block or FK model theorem is substituted.')
  elif key in ['t:main','t:mainW','t:cutMOS','t:rec','t:H1','t:inputs']:
   D[key]=([], 'Campaign assembly/input theorem. Prove from the plan dependencies; vendoring does not certify its numerical, geometric or model-specific premises. The historical cutMOS label does not license an MO/MOS black-box import.')
  else:D[key]=([], 'New campaign-specific walk, coupling, topology or certificate proof. No audited donor declaration covers the full statement; use the plan dependency chain. General arithmetic/sl2 tools are mapped at their direct consumers above.')
# Reject typos in declaration references using the environment inventory.
exports={x['name'] for x in json.loads((OUT/'exported-declarations.json').read_text())}
for key,(names,_) in D.items():
 for n in names:assert n in exports,(key,n)
data=[dict(statement=key,title=title,declarations=D[key][0],scope=D[key][1]) for key,title in rows]
assert len(data)==len(set(x['statement'] for x in data))==105
(OUT/'reuse-map.json').write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
s='''# Reuse map for all 105 labelled REV-PLAN entries

Every row is accounted for. A declaration in this table is an imported proof ingredient,
unless the scope column says it proves the whole assertion. **No full manuscript assertion
is asserted to be proved solely by vendoring.** Definitions and computational contracts
are not theorems. Empty entries identify new work, rather than adding assumed facts.
The exact statements and quantifiers of every listed declaration are in [declarations.log](declarations.log).
All names below begin with `AKLT.Vendor.`; that common prefix is omitted for readability.

| Plan statement | Vendored declarations | Exact scope / remaining bridge |
|---|---|---|
'''
for x in data:
 names='<br>'.join('`'+n.removeprefix(P)+'`' for n in x['declarations']) or 'None'
 s+=f"| `{x['statement']}` — {x['title'].replace('|','/')} | {names} | {x['scope']} |\n"
(OUT/'reuse-map.md').write_text(s)
print('Wrote',len(data),'statement rows')
