#!/usr/bin/env python3
"""Render completed receipts into the final report. Does not run any checker."""
import json,re
from pathlib import Path
R=Path('/home/ubuntu/aklt/reports/PAL_FIT');G=1024**3

def read(p):return json.loads((R/p).read_text())
def measure(tag):return read('measurements/'+tag+'/result.json')
def fmt(x,n=2):return f'{x:,.{n}f}'
def mrow(label,tag,result):
 d=measure(tag);return f"| {label} | {fmt(d['wall_s'])} | {fmt(d['cpu_s'])} | {fmt(d['peak_rss_bytes']/G,3)} | {result} |"
def table(rows,header='| Stage | Wall s | CPU s | Peak RSS GiB | Result |'):
 return '\n'.join([header,'|---|---:|---:|---:|---|',*rows])
rows=['| Actual default-profile cgroup/setup | — | — | — | Blocked: systemd delegation unavailable |',
 mrow('Official source eligibility scanner','source-checks-final','Scanner completed; 1,104 missing module headers'),
 mrow('H1 final source-archive audit','h1-archive-sources','7,964 archives hash-match; 7,964 missing headers')]
for name,label,result in [('clean-build','Fresh broad source build, two workers','1,062 pass; 6 fail; 61 blocked'),('clean-resume','Continue fresh build, one worker','Cumulative 1,119 pass; H2.Check fails; 9 blocked')]:
 d=read(name+'/result.json');rows.append(f"| {label} | {fmt(d['wall_s'])} | {fmt(d['cpu_s'])} | {fmt(d['peak_worker_rss_sum_bytes']/G,3)} aggregate | {result} |")
rows += [mrow('Protected Challenge compile','canonical-challenge-compile','Fails: candidate-local AKLT import'),mrow('Strict headline + 416-leaf Audit','strict-audit','Pass, after disclosed warm H2 reuse'),mrow('Worktree conditional Solution','worktree-solution-build','Pass, disclosed warm dependencies'),mrow('Stock full Solution export','solution-export','Pass, 889,805,659 bytes'),mrow('Full Solution Lean replay','solution-lean-replay','Accept'),mrow('Full Solution NanoDa, four threads','solution-nanoda','Accept'),mrow('Full Solution con-ron, two workers','solution-conron','Allocation failure; censored AS cap')]
h=[]
for label,tag,res in [('H2 original source module','h2-source','Censored AS limit'),('H2 Lean replay','h2-lean-replay','Accept'),('H2 NanoDa','h2-nanoda','Accept'),('H2 con-ron','h2-conron','Allocation failure; censored'),('deadMask source module','deadmask-source','Accept'),('deadMask Lean replay','deadmask-lean-replay','Accept'),('deadMask NanoDa','deadmask-nanoda','Allocation failure; censored'),('deadMask con-ron','deadmask-conron','Allocation failure; censored')]:
 if tag in ['h2-source','deadmask-source']:
  module='AKLT.Cert.H2.Check' if tag=='h2-source' else 'AKLT.W.H3C026.DeadMask'
  d=next(x for x in map(json.loads,(R/'clean-resume/modules.jsonl').read_text().splitlines()) if x['module']==module)
  h.append(f"| {label} | {fmt(d['wall_s'])} | {fmt(d['cpu_s'])} | {fmt(d['peak_rss_bytes']/G,3)} | {res} |")
 else:h.append(mrow(label,tag,res))

pil=[]
for tag,label in [('pilot-Main','Challenge.Main'),('pilot-MainV2','Challenge.MainV2'),('pilot-Sanity','Challenge.Sanity'),('pilot-axioms','Challenge strict axiom audit')]:pil.append(mrow(label,tag,'Pass'))
for part in ['AKLT-Defs','AKLT-Gen-Gram']:
 d=read('pilot-'+part+'-result.json');assert not d['failed'] and d['audit']['exit_code']==0
 pil.append(f"| Complete {d['part']} part: {len(d['roots'])} files / {d['selected']} closure | {fmt(sum(x['wall_s'] for x in d['records']))} newly compiled | {fmt(sum(x['cpu_s'] for x in d['records']))} | {fmt(max(x['peak_rss_bytes'] for x in d['records'])/G,3)} max | Pass; {len(d['reused'])} prerequisites reused from successful pilot |")
 pil.append(mrow(d['part']+' strict public-theorem audit',d['audit']['name'],f"Pass; {len(d['audit_theorems'])} theorem prints"))
pil.append(mrow('H2.Check after module port','pilot-h2-AKLT.Cert.H2.Check','Allocation failure; not a successful H2 part port'))
pil.append(mrow('H2 successful public-theorem audit','pilot-h2-partial-axioms','Pass; successful H2 submodules only'))
d=read('pilot-h2-result.json')
pilot='The stronger successful pilots port the complete **AKLT/Defs (23 files, 24-module prerequisite closure)** and **AKLT/Gen/Gram (five files, five-module closure)** directories. Defs exercises private fixed-table helpers; Gram exercises the checker/soundness library. All compile without a proof-body repair. The Gram strict audit prints every public theorem, with statements in its existing CoreAudit output; axiom sets remain within the permitted three. Exact source manifests and results are [pilot-AKLT-Defs-result.json](pilot-AKLT-Defs-result.json) and [pilot-AKLT-Gen-Gram-result.json](pilot-AKLT-Gen-Gram-result.json).\n\n'+table(pil)+f"\n\nThe H2 attempt selected 34 modules: 29 pass (including reused Challenge.Main), one numerical module fails, and four dependents are blocked. Ported H2.Check is censored at 101.77 s / 101.69 CPU s / {fmt(measure('pilot-h2-AKLT.Cert.H2.Check')['peak_rss_bytes']/G,3)} GiB RSS and 31 GiB VMS. Its lower import memory is insufficient to finish the reduction. The {len(d['partial_audit_theorems'])} public theorems in successful H2 part modules pass their separate strict axiom audit. The open modules are exactly `AKLT.Cert.H2.Check`, `AKLT.Cert.H2.Finite`, `AKLT.Cert.H2.Main`, `AKLT.Cert.H2.All`, `AKLT.Cert.H2.Audit`; details in [pilot-h2-result.json](pilot-h2-result.json). In total 47 original sources were transformed across these overlapping pilots, under 5% of the tree. The compatibility fixture exports `AKLT.PALFit.VisibilityCompat.checked : AKLT.PALFit.VisibilityCompat.visible = 7`, whose axiom list is empty; the strict visibility fixture intentionally fails."

b=read('budget-model.json');p0,p1=b['profiles']
brows=[f"| Host CPU / RAM | 16 / 32 GiB | 32 / 64 GiB |",'| Host pressure / ceiling | 30.40 / 31.36 GiB | 60.80 / 62.72 GiB |','| Solo checker envelope after 1 GiB overhead | 30.36 GiB | 61.72 GiB |','| Redesigned build concurrency / ceiling envelope per process | 4 / 7.590 GiB | 8 / 7.715 GiB |','| Pressure-aware envelope per build process, same 1 GiB overhead | 7.350 GiB | 7.475 GiB |',f"| Residual ideal total CPU-hours, all work perfectly parallel | {fmt(p0['absolute_cpu_h_intercept'])} | {fmt(p1['absolute_cpu_h_intercept'])} |",f"| Reference new numerical K-hours, mandatory kernels, no literal cost | {fmt(p0['reference_K_h_intercept'],3)} | {fmt(p1['reference_K_h_intercept'],3)} |",'| Lean / NanoDa / con-ron check parallelism | 1 / ≤4 / ≤2 | 1 / ≤4 / ≤2 |','| All-three K-hours with rConron=2, 600-s repaired core con-ron | ≤0.333 | ≤0.333 |','| Byte-only export allowance | Not identifiable | Not identifiable |','| Conservative new-export design target, not an admission guarantee | 0.30 GB; total ≈1.19 GB | Same |']
btable='\n'.join(['| Budget item | Default 16×32 | Larger 32×64 |','|---|---:|---:|',*brows])
red=[]
for lane in ['H1','H3']:
 def band(p,key):
  vals=p['lanes'][lane][key];return f'{min(vals):.1f}–{max(vals):.1f}×'
 red.append(f"| {lane} mandatory build + Lean + NanoDa | {band(p0,'uniform_reduction_mandatory')} | {band(p1,'uniform_reduction_mandatory')} |")
 red.append(f"| {lane} complete con-ron within unchanged cap too | {band(p0,'uniform_reduction_all_three')} | {band(p1,'uniform_reduction_all_three')} |")
rtable='\n'.join(['| Separate-lane reduction scenario | Default | Larger |','|---|---:|---:|',*red])
text=(R/'tools/report-template.md').read_text()
for k,v in {'CORE_TABLE':table(rows),'HAZARD_TABLE':table(h),'PILOT_SECTION':pilot,'BUDGET_TABLE':btable,'REDUCTION_TABLE':rtable}.items():text=text.replace('{{'+k+'}}',v)
assert '{{' not in text
(R/'report.md').write_text(text)
print('report rendered',len(text.encode()),'bytes',len(text.splitlines()),'lines')
