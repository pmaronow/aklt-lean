import json,subprocess,pathlib,concurrent.futures
root=pathlib.Path.cwd(); rows=json.load(open('evidence/pmaronow-trees.json'))
patterns=['*.lean','/README*','/NOTICE*','LICENSE*','COPYING*','lean-toolchain','lake-manifest.json','lakefile.*','formalization.yaml','!/archive/','!/runs/','!/research/','!**/.lake/','!node_modules/']
def one(r):
 if r['status']!='cloned':return r['repo'],r['status']
 p=root/'clones'/r['repo'].replace('/','__')
 try:
  subprocess.run(['git','-C',str(p),'sparse-checkout','set','--no-cone',*patterns],check=True,capture_output=True,text=True)
  subprocess.run(['git','-C',str(p),'checkout','--quiet','HEAD'],check=True,capture_output=True,text=True)
  return r['repo'],'ok'
 except Exception as e:return r['repo'],str(e)
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex:
 for r in ex.map(one,rows):print(*r,flush=True)
