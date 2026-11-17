import json,os,fcntl
A=os.path.expanduser("~/aklt"); S=A+"/state/lw"
f=open(S+"/state.lock","w"); fcntl.flock(f,fcntl.LOCK_EX)
d=json.load(open(S+"/leaves.json"))
x=d["REC082"]
if x["state"]=="exhausted": x["state"]="running"; print("REC082 -> recheck")
json.dump(d,open(S+"/leaves.json.tmp","w"),indent=1); os.replace(S+"/leaves.json.tmp",S+"/leaves.json")
