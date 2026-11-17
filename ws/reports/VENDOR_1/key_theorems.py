from pathlib import Path
import subprocess,os,json,time
OUT=Path('/home/ubuntu/aklt/reports/VENDOR_1');ROOT=Path('/home/ubuntu/aklt/wt/VENDOR_1')
names=['FiniteConditioning.condExp_on_fiber','FiniteConditioning.condExp_eq_of_fiber_integrals','FiniteConditioning.condIndep_of_fiber_indep','FiniteChain.finiteTotalVariation_contraction','FiniteChain.Cheeger.weightedVariance_le_center','FiniteChain.finiteDirichletForm_eq_neg_generator','FiniteChain.finiteChainSemigroup_detailed_balance','QICLean.Matrix.IsIsometry.isUnitaryBetween_of_card_eq','QICLean.Matrix.IsHermitian.toEuclideanCLM_eigenvectorBasis','QICLean.Matrix.IsHermitian.mul_norm_sq_le_re_inner_of_spectral_gap','Physlib.Sl2.cgEquiv_tensorE','Physlib.Sl2.cgEquiv_tensorF','Physlib.Sl2.cgEquiv_tensorH','Physlib.Sl2.cgProj_isTensorIntertwiner','Physlib.Sl2.IsTensorIntertwiner.eq_zero_of_forall_ne','Physlib.Sl2.IsTensorIntertwiner.exists_eq_smul_cgProj','Balaban.LatticeGeom.exists_primitive_of_closed','Balaban.LatticeGeom.outerBoundary_starConn','Balaban.LatticeGeom.exteriorBoundary_starConn','LeanCert.Core.Dyadic.toRat_add','LeanCert.Core.Dyadic.toRat_mul','LeanCert.Core.Dyadic.toRat_shiftDown_le','LeanCert.Core.Dyadic.toRat_shiftUp_ge','LeanCert.Core.Dyadic.le_iff_toRat_le','LeanCert.Core.Dyadic.toRat_normalizeDown_le','LeanCert.Core.Dyadic.toRat_normalizeUp_ge']
names=['AKLT.Vendor.'+n for n in names]
known={x['name'] for x in json.loads((OUT/'exported-declarations.json').read_text())}
assert set(names)<=known,set(names)-known
(OUT/'KeyTheorems.lean').write_text('import AKLT.Vendor.All\n'+'\n'.join('#check @'+n+'\n#print axioms '+n for n in names)+'\n')
t=time.monotonic();p=subprocess.run(['lake','env','lean',str(OUT/'KeyTheorems.lean')],cwd=ROOT,env={**os.environ,'PATH':'/home/ubuntu/.elan/bin:'+os.environ['PATH']},text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(OUT/'key-theorems.log').write_text(p.stdout)
(OUT/'key-theorems.json').write_text(json.dumps(dict(names=names,seconds=time.monotonic()-t,returncode=p.returncode),indent=2)+'\n')
assert p.returncode==0,p.stdout
print('Key theorems:',len(names))
