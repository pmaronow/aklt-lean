import json,os,fcntl
A=os.path.expanduser("~/aklt"); S=A+"/state/lw"
f=open(S+"/state.lock","w"); fcntl.flock(f,fcntl.LOCK_EX)
d=json.load(open(S+"/leaves.json"))
for k,x in d.items():
    if x["state"]=="exhausted" and x["stage"]=="sol": x["state"]="running"; print(k,"-> recheck with dependency detection")
json.dump(d,open(S+"/leaves.json.tmp","w"),indent=1); os.replace(S+"/leaves.json.tmp",S+"/leaves.json")
