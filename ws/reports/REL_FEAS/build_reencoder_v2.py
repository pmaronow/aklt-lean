import pathlib,subprocess,os,resource
R=pathlib.Path('/home/ubuntu/aklt/reports/REL_FEAS');st=R/'scratch/lib';d=st/'RELFEAS'
src=(d/'FastExportV2.lean').read_text().replace('RELFEAS.FastExportV2','RELFEAS.ReencodeExportV2')
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
      val.value.replace fun e =>
        match e with
        | .lit (.natVal n) => if n.log2+1 > 8192 then some (shiftData 64 n) else none
        | _ => none
      else val.value
    dumpDeps val.type''')
part=part.replace('dumpDeps val.value','dumpDeps value').replace('dumpExpr val.value','dumpExpr value')
src=src[:lo]+part+src[hi:];(d/'ReencodeExportV2.lean').write_text(src)
(d/'ReencodeMainV2.lean').write_text((d/'FastMainV2.lean').read_text().replace('FastExportV2','ReencodeExportV2'))
tc=pathlib.Path.home()/'.elan/toolchains/leanprover--lean4---v4.35.0-rc2/bin'
env=os.environ.copy();env['PATH']=str(tc)+':'+env.get('PATH','');env['LEAN_PATH']=str(st)
def cap():
 resource.setrlimit(resource.RLIMIT_CORE,(0,0));resource.setrlimit(resource.RLIMIT_AS,(16*1024**3,16*1024**3))
for cmd in [[tc/'lean','-o','RELFEAS/ReencodeExportV2.olean','-c','RELFEAS/ReencodeExportV2.c','RELFEAS/ReencodeExportV2.lean'],
 [tc/'lean','-c','RELFEAS/ReencodeMainV2.c','RELFEAS/ReencodeMainV2.lean'],
 [tc/'leanc','-O3','-o',R/'reencode-export-v2','RELFEAS/ReencodeExportV2.c','RELFEAS/ReencodeMainV2.c']]:
 subprocess.run(list(map(str,cmd)),cwd=st,env=env,check=True,timeout=600,preexec_fn=cap)
