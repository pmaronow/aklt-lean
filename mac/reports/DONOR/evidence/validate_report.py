import pathlib,json,re,subprocess,collections
root=pathlib.Path.cwd();s=(root/'donors.md').read_text();cat=json.loads((root/'evidence/source-catalogue-final.json').read_text());pm=json.loads((root/'evidence/pmaronow-trees.json').read_text());entries=list(cat.values())+pm
issues=[];checked=0
for u in re.findall(r'\]\((https://github\.com/[^)]+)\)',s):
 m=re.match(r'https://github\.com/([^/]+/[^/]+)/blob/([^/]+)/(.*)',u)
 if not m:continue
 repo,sha,path=m.groups();match=next((x for x in entries if x.get('repo')==repo and x.get('commit','').startswith(sha)),None)
 if repo=='LionSR/QICLean' and sha=='603fc408b9f4c2a50f2475e1e44843fdc0a9c0ac':match=cat[repo]
 if repo=='isabelle-prover/mirror-afp-devel':
  d=json.loads((root/'evidence/AFP-excerpts.json').read_text());match=d
 if match and path not in match.get('paths',[]):issues.append(('missing repo path',u))
 elif not match:issues.append(('unknown commit',u))
 checked+=1
for dest in re.findall(r'\]\((/[^)]+)\)',s):
 if not pathlib.Path(dest).exists():issues.append(('missing local path',dest))
if not s.startswith('STATUS: COMPLETE\n'):issues.append(('status','bad'))
if '@@' in s or '[[' in s:issues.append(('template','unexpanded'))
section=s.split('### All repositories returned for `pmaronow`',1)[1].split('### Every repository cited',1)[0]
coverage=sum(1 for line in section.splitlines() if line.startswith('| pmaronow/') or line.startswith('| [pmaronow/'))
if coverage!=53:issues.append(('pmaronow rows',coverage))
# Each Markdown table must have the same number of delimiters on every row.
block=[]
for i,line in enumerate(s.splitlines()+['']):
 if line.startswith('|'):block.append((i+1,line.count('|')))
 elif block:
  expected=block[0][1]
  issues.extend(('table delimiter mismatch',n,c,expected) for n,c in block if c!=expected)
  block=[]
result={'github_blob_links_checked':checked,'pmaronow_rows':coverage,'issues':issues,'report_bytes':len(s.encode()),'report_lines':len(s.splitlines())}
(root/'evidence/report-validation.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
