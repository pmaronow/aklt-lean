import subprocess,pathlib,json,concurrent.futures,sys
root=pathlib.Path('/Users/paronow/aklt-lean/reports/DONOR')
def one(name):
 p=root/'clones'/name.replace('/','__')
 try:
  if not p.exists(): subprocess.run(['git','clone','--quiet','--depth','1','--filter=blob:none','--no-checkout','https://github.com/'+name+'.git',str(p)],check=True,capture_output=True,text=True)
  sha=subprocess.check_output(['git','-C',str(p),'rev-parse','HEAD'],text=True).strip()
  paths=subprocess.check_output(['git','-C',str(p),'ls-tree','-r','--name-only','HEAD'],text=True).splitlines()
  subprocess.run(['git','-C',str(p),'sparse-checkout','set','--no-cone','*.lean','*.md','lean-toolchain','lake-manifest.json','lakefile.*','LICENSE*','COPYING*','formalization*','!/.lake/','!node_modules/','!vendor/'],check=True,capture_output=True,text=True)
  subprocess.run(['git','-C',str(p),'checkout','--quiet','HEAD'],check=True,capture_output=True,text=True)
  row=dict(repo=name,status='ok',commit=sha,paths=paths)
  (root/'evidence'/(name.replace('/','__')+'-tree.json')).write_text(json.dumps(row,indent=2))
  return name,sha,len(paths),sum(x.endswith('.lean') for x in paths)
 except Exception as e:return name,'ERROR',str(e)
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:
 for r in ex.map(one,sys.argv[1:]):print(*r,flush=True)
