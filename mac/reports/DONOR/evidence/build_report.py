import json, pathlib, re, subprocess

ROOT = pathlib.Path('/Users/paronow/aklt-lean/reports/DONOR')
E = ROOT / 'evidence'
KEYS = {
 'M':'leanprover-community/mathlib4', 'P':'leanprover-community/physlib',
 'TN':'LionSR/TNLean', 'Q':'LionSR/QICLean', 'U':'TauCetiProject/TauCeti',
 'F':'pmaronow/fluctuations-palomar', 'A':'pmaronow/all-lean',
 'LL':'pmaronow/llm-audit-lean', 'SD':'pmaronow/spherical-dynamics-lean',
 'SE':'pmaronow/slowequilibration-palomar', 'ST':'StatLean/Stat-Lean',
 'S':'stat-lib/statlib', 'C':'Jiyuan-Tan/CausalSmith', 'E':'danlyng/Econlib',
 'EE':'eic/EpsilonEridani', 'AT':'facebookresearch/atlas-lean',
 'B':'scottnarmstrong/balaban-lean', 'PC':'zijie123123/PottsContinuity-lean',
 'PD':'zijie123123/PottsDiscontinuity-lean', 'RR':'PerAlexandersson/RealRooted',
 'H':'kim-em/hex-dev', 'LC':'alerad/leancert', 'GI':'girving/interval',
 'IB':'peti12352/lean-interval-bounds', 'L':'leanprover/lean4',
 'NT':'tejasvi/native-trust', 'C4':'tejasvi/lean4body-uniqueness',
 'Z7':'telaviv/zeta-irrationality', 'QEC':'Stavan-Jain/qec-lab',
 'CR':'Timeroot/ComputableReal', 'QI':'Timeroot/Lean-QuantumInfo',
 'D':'JD-Jones-ASES/finite-quantum-designs-lean', 'R':'dwrensha/Rupert.lean',
 'MS':'mrdouglasny/markov-semigroups', 'CMP':'leanprover/comparator',
 'VS':'validSDP/validsdp', 'IT':'affeldt-aist/infotheo',
 'TTO':'lopatto/tto-palomar', 'PL':'lopatto/plouffe-palomar-public',
}
CAT = {}
for p in (ROOT/'clones').iterdir():
 if not (p/'.git').exists() or p.name.endswith('-gitlab'): continue
 repo=p.name.replace('__','/',1)
 def get(f):
  try:return subprocess.check_output(['git','-C',str(p),'show','HEAD:'+f],text=True,stderr=subprocess.DEVNULL)
  except Exception:return ''
 sha=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
 paths=subprocess.check_output(['git','-C',str(p),'ls-tree','-r','--name-only','HEAD'],text=True).splitlines()
 tc=get('lean-toolchain').strip().replace('leanprover/lean4:','')
 try:ml=next(x for x in json.loads(get('lake-manifest.json'))['packages'] if x['name']=='mathlib')
 except Exception:ml=None
 lf=next((f for f in ['LICENSE','LICENSE.md','LICENSE.txt','LICENCE','COPYING'] if f in paths),None)
 license_text=get(lf) if lf else ''
 if repo=='facebookresearch/atlas-lean':lic='Apache-2.0 text **plus ML-use-intent preamble**; preserve complete text'
 elif 'Apache License' in license_text:lic='Apache-2.0'
 elif 'MIT License' in license_text:lic='MIT'
 elif 'GNU LESSER GENERAL PUBLIC LICENSE' in license_text:lic='LGPL-2.1 text'
 elif 'BSD' in license_text or 'Redistribution and use in source and binary forms' in license_text:lic='BSD-style text'
 else:lic='No standard root licence identified; inspect notices before copying'
 CAT[repo]=dict(repo=repo,commit=sha,toolchain=tc,mathlib=ml,paths=paths,license=lic,license_file=lf)

Q_PIN='603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac'
def link(repo,path,label=None,sha=None):
 d=CAT[repo];sha=sha or d['commit'];return f'[{label or path}](https://github.com/{repo}/blob/{sha}/{path})'
def ref(k,path,label=None):
 return link(KEYS[k],path,label, Q_PIN if k=='Q' else None)

table=['| Key | Repository and inspected commit | Lean; pinned Mathlib | Licence evidence |','|---|---|---|---|']
for k,repo in KEYS.items():
 d=CAT[repo];sha=Q_PIN if k=='Q' else d['commit'];tc=d['toolchain']
 pin=ref(k,'lean-toolchain',tc) if tc else 'non-Lean / toolchain not identified'
 if d['mathlib']:
  m=d['mathlib'];pin+='; Mathlib '+ref(k,'lake-manifest.json',m['rev'][:12])
 lic=d['license']+((' — '+ref(k,d['license_file'],'licence')) if d['license_file'] else '')
 table.append(f'| **{k}** | [{repo}](https://github.com/{repo}/tree/{sha}) `{sha}` | {pin} | {lic} |')

coverage=[
 ('Mathlib current and 4.34–4.36 era','M','Mathlib/Combinatorics/SetFamily/FourFunctions.lean','Searched representation, Hermitian/Rayleigh/PosDef, sphere measure, conditional-expectation, graph/trail, spectrum, echelon/Bareiss and tactics source. Direct FKG, spectral and combinatorial infrastructure; version comparisons are in §2.'),
 ('PhysLean / HepLean / Physlib','P','README.md','Resolved the current continuation to physlib; read physics and QuantumInfo trees, sl₂ construction/decomposition/coefficients, Pauli/Bloch and Ising files. Strong component-1 algebra; no direct spin-2 square-lattice AKLT theorem found.'),
 ('Lean-QuantumInfo','QI','README.md','Searched its finite quantum-information and StatMech tree; README records merger into Physlib in March 2026. Kept its older pin/licence distinct; prefer the current Physlib modules unless an old interface is specifically needed.'),
 ('TNLean','TN','TNLean/MPS/Examples/AKLT.lean','Searched all TNLean Lean sources for AKLT, valence bonds, Knabe, detectability, spin and parent Hamiltonians; inspected AKLT tensor/physical parent/sector and finite-range-gap files. Useful actual spin-chain donor.'),
 ('QICLean','Q','QICLean/Analysis/FiniteRangeKnabe.lean','Followed TNLean’s pinned dependency; inspected projections, kernel gaps, detectability, cyclic Knabe, coherent resolution and measure. Compared the three key blobs to the exact TNLean pin.'),
 ('TauCeti','U','TauCeti/Probability/Distributions/Uniform/Sphere/Basic.lean','Searched sphere, moments, Markov/coupling, min-max and matrix paths. Read normalized sphere/Gaussian bridges and Courant–Fischer. Its quantum-group Uq(sl₂) search hits are not automatically classical SU(2) results.'),
 ('Statlib','S','Statlib/Divergence/TotalVariation/Integral.lean','Searched full Lean tree for chain, Gibbs, coupling, conditional expectation, variance and TV. Useful TV and conditional expectation/divergence infrastructure; no MO/MOS or finite heat-bath gap theorem located.'),
 ('StatLean','ST','StatLean/Bayesian/MCMC/Gibbs.lean','Searched per-area source and read Gibbs/MCMC, conditional-L² and resampling-variance files. Stationarity and variance results found; their statements do not assert the requested mixing-to-gap theorem.'),
 ('CausalLean / Causalean','C','Causalean/Mathlib/Probability/FiniteMarkovPerturbation.lean','Resolved CausalForge to CausalSmith; searched Causalean coupling, kernels, conditioning, variance and Cholesky modules. Finite stochastic perturbations and Cholesky existence found. Causal-graph Markov equivalence is not Markov-chain mixing.'),
 ('llm-audit-lean','LL','NOTICE','Read README, verification/highlights guides, current NOTICE and relevant source, followed the historical highlights revision and enumerated cited repository URLs. Found finite-fibre conditioning; most statistical targets are peripheral to AKLT. Intentional Challenge holes are distinguished from implementation code.'),
 ('Econlib','E','Econlib/Probability/FinDist/Variance.lean','Followed audit citation; searched Markov, coupling, finite laws, conditioning and variance. Found finite total variance, stationary distributions and geometric convergence; useful adaptation substrate.'),
 ('EpsilonEridani','EE','EpsilonEridani/Mathematics/Calculus/Polynomial.lean','Followed audit citation and checked current polynomial integration/Legendre paths (now under EpsilonEridani/). Source includes Polynomial.integral_derivative_mul_derivative_mul_comm. No S² icosahedral-design theorem found in inspected sources; its DIS Martinelli citation is unrelated to dynamics.'),
 ('atlas-lean','AT','MathlibExt/Probability/TotalVariationCoupling.lean','Searched MathlibExt and PhyslibExt probability/Ising/random-cluster paths. Maximal coupling, path coupling and PF found. MarkovChainPoincare.variance_iterate_le merely iterates an assumed contraction. Licence preamble is recorded.'),
 ('balaban-lean','B','Balaban/LargeField/Geometry/Timar.lean','Located and read actual Timár/exterior-boundary and parity proofs. Important donor with a different adjacency direction from Appendix B.'),
 ('PottsContinuity-lean','PC','README.md','Registry-led search of planar duality/topology, finite/infinite FKG, comparison and domain Markov source. Read source interfaces and polygonal/Jordan donor paths; record concerns its declared theorem surface.'),
 ('PottsDiscontinuity-lean','PD','PottsDiscontinuity/Duality/RectangleDualCrossing.lean','Registry-led search; read rectangle cut labels, cell-boundary parity, dual crossing and planar alternatives. Concrete ℤ² topology donor.'),
 ('RealRooted','RR','RealRooted/Mathlib/LinearAlgebra/Matrix/PerronFrobenius/CollatzWielandt.lean','Read CollatzWielandt, Nonneg and spectral/irreducibility source. Reusable PF; checked that the named Collatz function is a minimum, not the needed maximum quotient.'),
 ('Hex development','H','HexPosDefTheory/README.md','Read positive-certificate definitions, soundness, scaling, congruence, quotation and tactic assembly, plus benchmark probes. Best located H1 checker; candidate computation separated from kernel acceptance.'),
 ('LeanCert','LC','README.md','Read current mode table and dyadic/interval/validity paths; searched native and kernel choices. Strict kernel mode exists; default native and automatic fallback are unsuitable unchanged.'),
 ('girving/interval','GI','README.md','Read software-floating representation and interval arithmetic paths; useful proved rounding semantics. Kernel performance for the proposed workload remains unmeasured.'),
 ('lean-interval-bounds','IB','README.md','Read Basic/Tactic/Approx interfaces and axiom-check examples. Useful isolated transcendental bounds; not a matrix or recurrence checker.'),
 ('ComputableReal','CR','README.md','Inspected examples and interface; advertised proofs use native_decide. Reference/potential adaptation only, not an approved proof path as shown.'),
 ('NativeTrust','NT','README.md','Read strict kernelization, staging/fuel replacement, conversion statistics and fallback settings. Useful migration/reflection techniques; convenience modes require care.'),
 ('lean4body-uniqueness','C4','README.md','Read exact checker/grid/certificate architecture and reported timings. Concrete large kernel-only interval computation example; not an AKLT proof donor.'),
 ('zeta-irrationality','Z7','README.md','Read certificate/chunk interfaces and reported time/memory; source under Z7/CertAK provides large arithmetic batching patterns.'),
 ('qec-lab','QEC','docs/lean-patterns.md','Read packed-Nat lookup and finite-walk kernel optimization account, including its contrasting large native-side sweeps. Only kernel-clean encoding techniques are recommended.'),
 ('Rupert icosahedron','R','Rupert/Icosahedron.lean','Read the explicit 12-vertex golden-ratio list and unrelated proof_wanted. No design-exactness theorem credited.'),
 ('Finite quantum designs','D','QuantumDesigns/WelchEquality.lean','Registry-led inspection of projective frames, Welch equality, SIC/MUB definitions, implementation and Challenge. Useful frame algebra, not an S² 4-design proof.'),
 ('markov-semigroups','MS','MarkovSemigroups/DobrushinZegarlinski/GlobalLSI.lean','Searched abstract Holley–Stroock and Dobrushin–Zegarlinski sources. Explicit global-LSI/covariance axioms block direct reuse under the required axiom policy.'),
 ('KTV swap-chain Comparator package',None,None,'Inspected guanyangwang/ktv-swap-lean-comparator@fd4dc985900b1fba59791067dcf3bf9341a94bda: ChallengeDefs.lean, Challenge.lean, Solution.lean, README.md. Finite rational Poincaré/Dirichlet spectral-gap statement and explicit state-space bridge; a pattern for theorem-surface design, not a Glauber theorem. '+link('guanyangwang/ktv-swap-lean-comparator','ChallengeDefs.lean')),
 ('Authors’ other Palomar packages','TTO','README.md','Listed all 16 lopatto repositories and inspected both Palomar-named packages. TTO dyadic geometry is unrelated to dyadic numerical interval checking; no selected AKLT donor. Also searched '+ref('PL','README.md','plouffe-palomar-public')+' and its Lean source; theta/zeta identities are peripheral.'),
 ('Comparator','CMP','README.md','Read permitted-axiom, fixed Challenge/Solution and transitive dependency checking rules. Used as the target acceptance design, not executed.'),
]
cov=['| Source | What was searched / result, with inspected source |','|---|---|']
for name,k,p,note in coverage:
 cov.append('| '+name+' | '+note+(' '+ref(k,p) if k else '')+' |')

rows=json.loads((E/'pmaronow-coverage.json').read_text());trees={x['repo']:x for x in json.loads((E/'pmaronow-trees.json').read_text())}
NOTES={
 'sk-mean-bias-palomar':'Finite-state Gibbs/continuity and Gaussian Poincaré hits; secondary to generic F chain code.',
 'llm-audit':'120 Lean files in validation material; statistics hits, no selected finite spin-dynamics theorem.',
 'llm-audit-lean':'Finite-fibre conditioning donor; third-party citations followed separately.',
 'self-audit-palomar':'Related audit/SAP and vendored Causalean/StatLean source; compare the public audit distribution.',
 'q-colorability-palomar':'Random graph threshold/finite probability; no selected AKLT/Glauber import.',
 'superfluidity-palomar':'Continuum Bose-gas Sobolev/Poincaré/operator source; patterns, not finite heat bath.',
 'maximal-dimensions':'PartIV Gibbs/coupling hits; no selected quantum-spin or finite heat-bath theorem.',
 'threshold-lean-temp':'ThLean predecessor; probability/graph hits, no selected new donor.',
 'superfluidity-lean-temp':'Same source families as superfluidity-palomar; prefer packaged snapshot.',
 'spherical-dynamics-lean':'Spherical diffusion/spectral/heat source; inspect assumptions; secondary, continuous-state.',
 'spherical-dynamics-temp':'Earlier spherical-diffusion source; prefer packaged snapshot.',
 'self-audit-backup':'Scanned archival Lean copies and current lean/ subtree; statistics/fibre material, no selected new dynamics donor.',
 'self-audit-lean':'Earlier audit source and supporting statistics; no selected extra dynamics donor.',
 'slowequilibration-palomar':'Spherical intrinsic forms and vendored SKGap finite-spin model definitions; useful patterns.',
 'ccv-temp':'Variance-estimation statistics; no selected donor for requested spin/chain results.',
 'ym3-lean-temp':'YM/field-theory source; incidental gap/variance hits, no selected AKLT import.',
 'fluctuations-palomar':'Primary public finite-chain, Dirichlet, heat-bath, Gibbs and TV donor.',
 'fluctuations-palomar-temp':'Same candidate families as packaged fluctuations source; no need to vendor both.',
 'fluctuations-temp':'Working and vendored finite-chain/SK source; prefer public packaged modules.',
 'slowequilibration-temp':'Working spherical/SK source and duplicate all-lean material; prefer packaged/generic APIs.',
 'all-lean':'Private consolidation; generic SKConstants chain/heat-bath source and interfaces inspected.',
 'sk-fluctuations':'Working spin-glass source and Glauber dependency-audit copies; prefer public package.',
 'ec567-palomar':'Elliptic-curve source; no relevant requested donor.',
 'ec567-temp':'Elliptic-curve source; no relevant requested donor.',
 'aging-palomar':'SphericalAging Gibbs generator/reversibility and variance source; continuous-state patterns.',
 'aging-temp':'Working aging source; no selected finite heat-bath replacement.',
 'arbitrary-rsb-palomar':'Gibbs cascade/mean-field source; finite probability patterns, not lattice mixing.',
 'temp-sk-repo':'Earlier mean-bias/cascade source; no additional selected chain donor.',
 'roughregime-palomar':'Functional estimation/statistics; no selected requested donor.',
 'ccv-palomar':'Variance estimation/statistics; no selected requested donor.',
 'frsb-palomar':'Parisi/RSB and Gaussian Poincaré; no selected finite lattice dynamics theorem.',
 'at-palomar':'RS/AT and Gaussian Poincaré; no selected finite lattice dynamics theorem.',
 'at-lean-old':'Older AT development; same search conclusion.',
 'design-based-lean':'Full tree plus README and two finite-coupling excerpts inspected; finite transportation compactness/minimizer donor. Large archive not retained.',
}
pt=['| Repository (default snapshot) | Scope / result |','|---|---|']
for d in rows:
 name=d['repo'];base=name.split('/')[1];tr=trees[name];paths=tr.get('paths',[])
 if d['status']=='empty':
  pt.append(f'| [{name}](https://github.com/{name}) — API inventory dated research snapshot | Empty/no default branch in returned inventory; no code searched. |');continue
 sha=d['commit'];sc=d.get('searches',{});n=d.get('materialized_lean',0)
 picks=[]
 for group in ['chain','other','gibbs','topology']:
  hits=sc.get(group,[])
  if hits:
   picks.append(hits[0]);break
 if base=='design-based-lean':picks=['lean/DesignBased/Vendor/OpenAI/FiniteCoupling.lean']
 if not picks:picks=[next((x for x in ['README.md','lean-toolchain','.gitkeep','index.html','source-note'] if x in paths),paths[0] if paths else '')]
 loc='; '.join(f'[{p}](https://github.com/{name}/blob/{sha}/{p})' for p in picks if p)
 note=NOTES.get(base, 'No Lean source in inspected tree/materialization; nothing relevant as a code donor.' if d.get('tracked_lean',0)==0 else 'Lean source searched; no additional selected donor.')
 scope=f'{n:,} Lean files searched' if n else 'tree/metadata search'
 if base=='design-based-lean':scope='tree + targeted source excerpts'
 pt.append(f'| {name} `{sha}`; {loc} | {scope}. {note} |')

infra={
 'leanprover-community/LeanSearchClient':'README.md',
 'leanprover-community/ProofWidgets4':'README.md',
 'leanprover-community/aesop':'README.md',
 'leanprover-community/batteries':'README.md',
 'leanprover-community/import-graph':'README.md',
 'leanprover-community/plausible':'README.md',
 'leanprover-community/quote4':'README.md',
 'leanprover/lean4-cli':'README.md',
 'leanprover/lean4export':'README.md',
 'YeWang1576/SpatialEffectPackage':'README.md',
}
it=['| Cited repository / exact inspected path | Search result |','|---|---|']
for repo,path in infra.items():
 result='README, tree and Lean source searched; generic search/UI/tactic/data/export tooling, no additional theorem donor for components 1–9.'
 if repo=='leanprover-community/batteries':result='README/tree/source searched; generic data structures/numerical support, already a Mathlib dependency; no located AKLT/chain theorem.'
 if repo=='leanprover-community/plausible':result='README/tree/source searched; property testing, not a kernel proof of an exhaustive certificate.'
 if repo=='YeWang1576/SpatialEffectPackage':result='README/tree searched; R spatial-effect estimation package, no Lean source or relevant requested code.'
 it.append('| '+link(repo,path,repo+' / '+path)+' | '+result+' |')

s=(E/'report-content.md').read_text()
s=s.replace('@@VERSION_TABLE@@','\n'.join(table)).replace('@@SOURCE_COVERAGE@@','\n'.join(cov)).replace('@@PMARONOW_COVERAGE@@','\n'.join(pt)).replace('@@INFRA_COVERAGE@@','\n'.join(it))
missing=[]
def expand(m):
 k,p=m.groups();repo=KEYS[k]
 if p not in CAT[repo]['paths']:missing.append((k,p))
 return ref(k,p)
s=re.sub(r'\[\[([A-Z0-9]+)\|([^\]]+)\]\]',expand,s)
if missing:print('MISSING PATHS:',missing)
(ROOT/'donors.md').write_text(s)
(E/'source-catalogue-final.json').write_text(json.dumps(CAT,indent=2))
print('Report:',len(s),'characters;',len(s.splitlines()),'lines;',len(s.split()),'words')
