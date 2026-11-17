from pathlib import Path
import re,json,hashlib
ROOT=Path('/home/ubuntu/aklt/wt/VENDOR_1')
p=ROOT/'AKLT/Vendor/QICLean/Algebra/MatrixUnitaryBetween.lean';s=p.read_text()
# Rewrite field syntax for predicates on Mathlib's Matrix, which is an abbreviation.
for pred in ['IsIsometry','IsCoisometry','IsUnitaryBetween']:
 for expr in ['(Matrix.reindex eₘ eₙ A)','(A * B)','Aᴴ','Bᴴ','A','B']:
  s=s.replace(expr+'.'+pred, '(AKLT.Vendor.QICLean.Matrix.'+pred+' '+expr+')')
# Proof methods on relocated predicates: make the first explicit argument visible.
start=s.index('namespace IsIsometry\n');mid=s.index('namespace IsCoisometry\n');end=s.index('namespace IsUnitaryBetween\n')
a=s[:start];b=s[start:mid];c=s[mid:end];d=s[end:]
b=b.replace('hA.rank_eq_card A','rank_eq_card A hA')
c=c.replace('hA.rank_eq_card A','rank_eq_card A hA').replace('hA.conjTranspose A','conjTranspose A hA').replace('h.isUnitaryBetween_of_card_eq Aᴴ hcard.symm','IsIsometry.isUnitaryBetween_of_card_eq Aᴴ h hcard.symm')
d=d.replace('hA.2.conjTranspose A','IsCoisometry.conjTranspose A hA.2').replace('hA.1.conjTranspose A','IsIsometry.conjTranspose A hA.1')
d=d.replace('hA.1.reindex A eₘ eₙ','IsIsometry.reindex A hA.1 eₘ eₙ').replace('hA.2.reindex A eₘ eₙ','IsCoisometry.reindex A hA.2 eₘ eₙ')
d=d.replace('hA.1.mul A B hB.1','IsIsometry.mul A B hA.1 hB.1').replace('hA.2.mul A B hB.2','IsCoisometry.mul A B hA.2 hB.2')
d=d.replace('hA.conjTranspose A','conjTranspose A hA').replace('hB.conjTranspose B','conjTranspose B hB')
d=d.replace('hAstar.mul Aᴴ (A * B) hAB','mul Aᴴ (A * B) hAstar hAB').replace('hAB.mul (A * B) Bᴴ hBstar','mul (A * B) Bᴴ hAB hBstar')
p.write_text(a+b+c+d)
p=ROOT/'AKLT/Vendor/QICLean/Analysis/LowEnergyPerturbation.lean';s=p.read_text()
for field in ['repr_apply_of_eigen','norm_sq_repr_symm','sub_smul_eq_repr_symm_of_eigen','re_inner_apply_eq_sum_of_eigen']:
 s=s.replace('b.'+field,'AKLT.Vendor.QICLean.OrthonormalBasis.'+field+' b')
p.write_text(s)
p=ROOT/'AKLT/Vendor/QICLean/Analysis/KernelSpectralGap.lean';s=p.read_text()
s=s.replace('hA.eigenvectorBasis.re_inner_apply_eq_sum_of_eigen','AKLT.Vendor.QICLean.OrthonormalBasis.re_inner_apply_eq_sum_of_eigen hA.eigenvectorBasis')
s=s.replace('hA.toEuclideanCLM_eigenvectorBasis','AKLT.Vendor.QICLean.Matrix.IsHermitian.toEuclideanCLM_eigenvectorBasis hA')
s=s.replace('      AKLT.Vendor.QICLean.Matrix.IsHermitian.toEuclideanCLM_eigenvectorBasis hA x]', '      (AKLT.Vendor.QICLean.Matrix.IsHermitian.toEuclideanCLM_eigenvectorBasis hA) x]')
p.write_text(s)
manifest=ROOT/'AKLT/Vendor/manifest.json';data=json.loads(manifest.read_text())
for item in data:
 p=ROOT/item['path'];item['vendored_sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
 if item['donor']=='QICLean':item['modifications'].append('Resolved Mathlib scopes/names explicitly; rewrote relocated extension field notation as qualified applications')
manifest.write_text(json.dumps(data,indent=2,ensure_ascii=False)+'\n')
