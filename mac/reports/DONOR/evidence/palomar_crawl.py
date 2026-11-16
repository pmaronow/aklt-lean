import urllib.request,urllib.parse,json,pathlib,time
base='https://data.palomar-registry.org/api/v1/results';url=base;entries=[];pages=[]
while url:
 req=urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'})
 d=json.load(urllib.request.urlopen(req));entries+=d['entries'];pages.append({'url':url,'revision':d['revision'],'count':len(d['entries'])})
 url=base+'?'+urllib.parse.urlencode({'cursor':d['next']}) if d.get('next') else None
 if len(pages)%10==0:print('pages',len(pages),'entries',len(entries),flush=True)
pathlib.Path('evidence/palomar-entire-index.json').write_text(json.dumps({'totals':d['totals'],'pages':pages,'entries':entries},indent=2))
print('COMPLETE',len(entries),d['totals'])
