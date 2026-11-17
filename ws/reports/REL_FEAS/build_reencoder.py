import pathlib,subprocess,os,resource
R=pathlib.Path('/home/ubuntu/aklt/reports/REL_FEAS');st=R/'scratch/lib';d=st/'RELFEAS'
src=(d/'FastExportV2.lean').read_text().replace('RELFEAS.FastExportV2','RELFEAS.ReencodeExport')
helper='''-- Prototype only: re-encode certificate data values; all types and proof bodies stay unchanged.
def shiftData : Nat → Nat → Expr
  | 0, n => mkNatLit n
  | fuel+1, n =>
    let bits := n.log2+1
    if bits ≤ 8192 then mkNatLit n else
      let cut := 8192 * (max 1 (((bits+8191)/8192)/2))
      mkApp2 (mkConst @Q@Nat.add)
        (shiftData fuel (Nat.land n (2^cut-1)))
        (mkApp2 (mkConst @Q@Nat.shiftLeft)
          (shiftData fuel (n >>> cut)) (mkNatLit cut))

'''.replace('@Q@',chr(96)*2)
src=src.replace('public structure Context',helper+'public structure Context')
lo=src.index('  | .defnInfo val => do');hi=src.index('  | .opaqueInfo val => do',lo)
part=src[lo:hi]
part=part.replace('    dumpDeps val.type','''    let value := if c.toString.startsWith "CertData.H3." then
      match val.value with
      | .lit (.natVal n) => shiftData 64 n
      | e => e
      else val.value
    dumpDeps val.type''')
part=part.replace('dumpDeps val.value','dumpDeps value').replace('dumpExpr val.value','dumpExpr value')
src=src[:lo]+part+src[hi:];(d/'ReencodeExport.lean').write_text(src)
(d/'ReencodeMain.lean').write_text((d/'FastMainV2.lean').read_text().replace('FastExportV2','ReencodeExport'))
tc=pathlib.Path.home()/'.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin'
env=os.environ.copy();env['PATH']=str(tc)+':'+env.get('PATH','');env['LEAN_PATH']=str(st)
def cap():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(16*1024**3,16*1024**3))
for cmd in [[tc/'lean','-o','RELFEAS/ReencodeExport.olean','-c','RELFEAS/ReencodeExport.c','RELFEAS/ReencodeExport.lean'],
 [tc/'lean','-c','RELFEAS/ReencodeMain.c','RELFEAS/ReencodeMain.lean'],
 [tc/'leanc','-O3','-o',R/'reencode-export','RELFEAS/ReencodeExport.c','RELFEAS/ReencodeMain.c']]:
 subprocess.run(list(map(str,cmd)),cwd=st,env=env,check=True,timeout=600,preexec_fn=cap)
