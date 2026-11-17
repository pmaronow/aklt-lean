import pathlib,re,json,time
R=pathlib.Path('/home/ubuntu/aklt/reports/REL_FEAS')
for tag in ['h3-row-group','h3-row-group-shift']:
 p=R/'measurements'/tag/'export.ndjson';start=time.monotonic()
 counts={};maxdigits=0;lines=0;large=[]
 with p.open('rb') as f:
  for line in f:
   lines+=1
   q=line.find(b'"natVal":"')
   if q>=0:
    n=line.rfind(b'"')-q-10;maxdigits=max(maxdigits,n)
    bucket=str((n//100000)*100000)
    counts[bucket]=counts.get(bucket,0)+1
    if n>500000:large.append({'digits':n,'line':lines})
 d=dict(bytes=p.stat().st_size,records=lines,nat_literal_digit_buckets=counts,max_digits=maxdigits,over_500000_digits=large,scan_s=time.monotonic()-start)
 (R/'measurements'/tag/'histogram.json').write_text(json.dumps(d,indent=2));print(tag,d,flush=True)
