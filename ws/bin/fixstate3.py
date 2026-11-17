import json,os,fcntl
A=os.path.expanduser("~/aklt"); S=A+"/state/lw"
f=open(S+"/state.lock","w"); fcntl.flock(f,fcntl.LOCK_EX)
d=json.load(open(S+"/leaves.json"))
deps={"REC090":["REC089"],"REC094":["REC090"],"REC095":["REC090","REC094"],"REC080":["REC090"],"REC091":["REC089"]}
for k,a in deps.items():
    x=d[k]
    if x["state"]=="exhausted":
        x.update(stage="sol",state="pending",after=a,fail="the earlier attempt reduced the statement to other blueprint leaves ("+", ".join(d[q]["node"].split(".")[-1] for q in a)+") that are now proved and available as lemmas; any other residual it left must be proved here")
        print(k,"requeued after",a)
for k in ("REC019","REC082"):
    if d[k]["state"]=="exhausted": d[k].update(stage="opus",state="running"); print(k,"-> opus")
json.dump(d,open(S+"/leaves.json.tmp","w"),indent=1); os.replace(S+"/leaves.json.tmp",S+"/leaves.json")
