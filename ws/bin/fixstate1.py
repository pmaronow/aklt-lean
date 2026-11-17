import json,os,fcntl,subprocess
A=os.path.expanduser("~/aklt"); S=A+"/state/lw"
alive=set(l.split(":")[0][3:] for l in subprocess.run(["tmux","ls"],capture_output=True,text=True).stdout.splitlines() if l.startswith("LW_"))
f=open(S+"/state.lock","w"); fcntl.flock(f,fcntl.LOCK_EX)
d=json.load(open(S+"/leaves.json"))
for k,x in d.items():
    fl="%s/done/%s.%s"%(S,k,x["stage"])
    if k in alive and os.path.exists(fl):
        os.remove(fl); print("stale flag removed",k,x["state"])
    if k in alive and x["state"] in ("exhausted","pending"):
        x["state"]="running"; print("state->running",k)
    if x["state"]=="running" and x["stage"]!="opus" and k not in alive and not os.path.exists(fl): print("ORPHAN (running, no session, no flag)",k)
    if x["state"]=="exhausted": print("exhausted:",k,x["node"].split(".")[-1])
d["REC079"].update(stage="sol",state="pending",after=["REC077","REC083"],fail="earlier attempt reduced the statement to two residuals (ordered exposure; local envelope) that match the blueprint leaves TraceExposureStatement (REC077) and RemovalEnvelopeStatement (REC083), now available as lemmas")
json.dump(d,open(S+"/leaves.json.tmp","w"),indent=1); os.replace(S+"/leaves.json.tmp",S+"/leaves.json")
