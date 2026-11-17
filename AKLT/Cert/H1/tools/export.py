#!/usr/bin/env python3
"""Export saved H1 witnesses as transparent Lean literals and Gram row checks.

No generated theorem claims that a supplied matrix equals the Defs constructor.
That independent obligation is recorded in leaves.json for every block.
Only the Python standard library is needed. This program never invokes Lean.
"""
from __future__ import annotations

import argparse
import gzip
import hashlib
import itertools
import json
from pathlib import Path
import shutil
from module_source import module_source

NS = "AKLT.Cert.H1"
RING = [(1, 0), (1, 1), (0, 1), (-1, 1), (-1, 0), (-1, -1), (0, -1), (1, -1)]
TIPS = {(1, 0): (2, 0), (0, 1): (0, 2), (-1, 0): (-2, 0), (0, -1): (0, -2)}
DIRS = [(1, 0), (0, 1), (-1, 0), (0, -1)]
DNAMES = ["east", "north", "west", "south"]


def require(p, detail):
    if not p:
        raise ValueError(detail)


def disk_guard(out: Path):
    require(shutil.disk_usage("/").free >= 100 * 10**9, "ABORT: / has less than 100 GB free")
    # The build runner separately checks source, compiled artifacts and reports
    # against 40 GB. This exporter checks free root space before every pattern.
    out.mkdir(parents=True, exist_ok=True)


def parse(s):
    def pairs(ps):
        d = {}
        for k, v in ps:
            require(k not in d, "duplicate JSON key: " + k)
            d[k] = v
        return d
    def no_float(v):
        raise ValueError("noninteger JSON number: " + v)
    return json.loads(s, object_pairs_hook=pairs, parse_float=no_float, parse_constant=no_float)


def records(base):
    ix = parse((base / "index.json").read_text())
    require(ix["format"] == "h1-gram-residual-v1", "wrong schema")
    pid = 0
    for c in ix["chunks"]:
        path = base / c["file"]
        require(hashlib.sha256(path.read_bytes()).hexdigest() == c["sha256"], "chunk hash")
        count = 0
        with gzip.open(path, "rt") as f:
            for line in f:
                r = parse(line)
                require(r["pid"] == pid, "pattern order")
                yield r
                pid += 1
                count += 1
        require(count == c["patterns"], "chunk length")
    require(pid == 7962, "pattern count")


def validate(r):
    pat, rep = r["pattern"], r["representation"]
    require(rep["model"] == "covered" and rep["refined"] is False, "unsupported model")
    require(rep["tip_radius"] == [3, 5], "tip radius")
    require([s[:2] for s in pat["sites"]] == [list(x) for x in RING], "site order")
    kinds = {tuple(s[:2]): s[2] for s in pat["sites"]}
    require(all(k in ("u", "d", "x") for k in kinds.values()), "status")
    bonds = {tuple(sorted((tuple(a), tuple(b)))) for a, b in pat["present"]}
    require(len(bonds) == len(pat["present"]), "duplicate bond")
    require(all(abs(a[0]-b[0])+abs(a[1]-b[1]) == 1 for a,b in bonds), "nonlocal bond")
    def kept(a,b):
        return tuple(sorted((a,b))) in bonds
    out = tuple(pat["out"])
    require(out in [(1,0),(0,1)] and kept((0,0),out), "outgoing")
    require(r["threshold"] == ([961,1000] if out == (0,1) else [187,200]), "threshold")
    slots, local, leaves = [], [], []
    for i,x in enumerate(RING):
        require((kinds[x] != "x") == any(x in b for b in bonds), "effective status")
        n = int(kept(x,TIPS[x])) if x in TIPS else (2 if kinds[x] != "x" else 0)
        role = "tip" if x in TIPS else "slot"
        if rep["leafred"] and x not in TIPS and n and int(kept(x,RING[i-1])) + int(kept(x,RING[(i+1)%8])) == 1:
            den = 2 if kinds[x] == "u" else 3
            leaves.append([*x,1,den]); n,role = 1,"leaf"
        group = list(range(len(slots),len(slots)+n))
        require(len({j in rep["inversion"] for j in group}) <= 1,"split pair inversion")
        slots.extend([[*x,role] for _ in range(n)])
        if n == 1:
            local.append([(1,0),(-1,0)])
        elif n == 2:
            local.append([(2,0),(0,0),(-2,0)] + ([(0,1)] if kinds[x] == "d" else []))
    require(rep["slots"] == slots and rep["nslots"] == len(slots),"slot order")
    require(rep["leaf_radii"] == leaves,"leaf radii")
    require(rep["inversion"] == sorted(set(rep["inversion"])) and
            all(type(i) is int and 0 <= i < len(slots) for i in rep["inversion"]),"inversion")
    sectors = {}
    for j,state in enumerate(itertools.product(*local)):
        par,sz = 0,0
        for spin,bit in state:
            sz += spin; par = 2*par+bit
        sectors.setdefault((par,sz),[]).append(j)
    selected = []
    for par in sorted({a for a,b in sectors}):
        sz = min((b for a,b in sectors if a == par),key=lambda t:(abs(t),-t))
        selected.append((par,sz,sectors[par,sz]))
    require(len(selected) == len(r["blocks"]),"exchange-sector coverage")
    for b,(par,sz,inds) in zip(r["blocks"],selected):
        require((b["exchange_parity"],b["two_sz"],b["basis_indices"]) == (par,sz,inds),"basis")
        n = b["n"]
        require(n == len(inds) and n > 0 and b["label"] == 1000*par+sz,"dimension/label")
        require(len(b["M_lt"]) == n*(n+1)//2,"M length")
        w = b["witness"]
        require(all(type(w[k]) is int and w[k] > 0 for k in ["g","d","S"]),"scales")
        require(len(w["L_lt"]) in [0,n*(n+1)//2],"L length")
        require(all(type(v) is int for v in b["M_lt"] + w["L_lt"]),"noninteger entry")


def lean_list(xs):
    return "[" + ", ".join(map(str,xs)) + "]"


def int_row(xs):
    return 'h1_row% "' + ",".join(map(str,xs)) + '"'


def raw_completion(r):
    """Choose a legal two-direction mask extending effective bonds.

    This is an export aid. Coverage of every *other* raw completion remains a
    Lean obligation, rather than being asserted by the Python program.
    """
    kinds = {tuple(s[:2]):s[2] for s in r["pattern"]["sites"]}
    bonds = {frozenset((tuple(a),tuple(b))) for a,b in r["pattern"]["present"]}
    live = {x for b in bonds for x in b}
    masks = {}
    for x in RING:
        k = kinds[x]
        if k == "x": masks[x] = []; continue
        if k == "u": masks[x] = [0,1,2,3]; continue
        choices = []
        for ds in itertools.combinations(range(4),2):
            if x == (0,-1) and 1 in ds: continue
            if x in [(1,0),(0,1),(-1,0)]:
                tv = next(i for i,d in enumerate(DIRS) if (x[0]+d[0],x[1]+d[1]) == (0,0))
                if tv not in ds: continue
            ok = True
            for i,d in enumerate(DIRS):
                y = (x[0]+d[0],x[1]+d[1])
                isbond = frozenset((x,y)) in bonds
                if (y in live or y in TIPS.values()) and ((i in ds) != isbond):
                    ok = False
            if ok: choices.append(list(ds))
        require(choices,"no raw completion")
        masks[x] = choices[0]
    return masks


def metadata(r):
    pid = r["pid"]; rep = r["representation"]
    masks = raw_completion(r)
    tips = set(TIPS.values())
    kinds = {tuple(s[:2]):s[2] for s in r["pattern"]["sites"]}
    status_cases = "\n".join(f"    else if x.val = ({x}, {y}) then .{'U' if k == 'u' else 'D'}"
                              for (x,y),k in kinds.items() if k != "x")
    kept_cases = "\n".join(f"    else if x.val = ({x}, {y}) then {{"+", ".join("."+DNAMES[i] for i in ds)+"}"
                            for (x,y),ds in masks.items() if ds)
    # Every original token is named by its Defs slot index, including a tip's
    # endpoint rather than the adjacent ring site used by the saved format.
    leaders = {(1,1):0,(-1,1):2,(-1,-1):4,(1,-1):6,(2,0):8,(0,2):11,(-2,0):14,(0,-2):17}
    tokens = []
    counts = {}
    for x,y,role in rep["slots"]:
        site = TIPS[(x,y)] if role == "tip" else (x,y)
        off = counts.get(site,0); counts[site] = off+1
        tokens.append(leaders[site]+off)
    inv = "{"+", ".join(str(tokens[i]) for i in rep["inversion"])+"}" if rep["inversion"] else "∅"
    p,q = r["threshold"]
    return f"""import AKLT.Defs.OperatorContracts

namespace {NS}.Data.P{pid:04d}
open AKLT.Defs
def pattern : PatternData where
  outgoing := .{'north' if r['pattern']['out'] == [0,1] else 'east'}
  status := fun x =>
    if x.val = (0, 0) ∨ x.val ∈ templateTips then .U
{status_cases}
    else .X
  kept := fun x =>
    if x.val = (0, 0) then {{.east, .north, .west}}
{kept_cases}
    else ∅
def representation : Representation := .{'reduced' if rep['leafred'] else 'unreduced'}
def inversion : Finset (Fin 20) := {inv}
def slotTokens : List Nat := {lean_list(tokens)}
def denominator : Nat := {rep['moment_denominator']}
def thresholdP : Nat := {p}
def thresholdQ : Nat := {q}
end {NS}.Data.P{pid:04d}
"""


def write(path,text):
    text = module_source(text)
    path.parent.mkdir(parents=True,exist_ok=True)
    if not path.exists() or path.read_text() != text:
        path.write_text(text)


def export_block(root,r,bi,rows,literal_namespace=None):
    pid=r["pid"]; b=r["blocks"][bi]; n=b["n"]; w=b["witness"]
    tag=f"P{pid:04d}B{bi:02d}"; dns=f"{NS}.Data.{tag}"; cns=f"{NS}.Check.{tag}"
    mp=b["M_lt"]; lp=w["L_lt"]
    M=[[mp[max(i,j)*(max(i,j)+1)//2+min(i,j)] for j in range(n)] for i in range(n)]
    L=[lp[i*(i+1)//2:(i+1)*(i+2)//2] if lp else [] for i in range(n)]
    shard_rows=rows if lp and n > 48 else n
    ranges=[(i,min(i+shard_rows,n)) for i in range(0,n,shard_rows)]
    data=[f"import {literal_namespace or NS}.Literals",f"import AKLT.Gen.Gram.Basic",f"\nnamespace {dns}","open AKLT.Gen.Gram",f"def dimension : Nat := {n}",
          f"def basisIndices : List Nat := {lean_list(b['basis_indices'])}",
          f"def exchangeParity : Nat := {b['exchange_parity']}",f"def twoSz : Int := {b['two_sz']}",
          f"def g : Int := {w['g']}",f"def d : Int := {w['d']}",f"def scale : Int := {w['S']}"]
    for k,(a,z) in enumerate(ranges):
        for name,rs in [("m",M),("l",L)]:
            data.append(f"def {name}{k:03d} : IntRows := ["+",\n  ".join(int_row(xs) for xs in rs[a:z])+"]")
    for name in ["m","l"]:
        data.append(f"def {name}Rows : IntRows := "+" ++ ".join(f"{name}{k:03d}" for k in range(len(ranges))))
    data.append(f"end {dns}\n")
    write(root/"Data"/(tag+".lean"),"\n".join(data))
    imports=[f"import {NS}.Data.{tag}"]
    shards=[]
    for k,(a,z) in enumerate(ranges):
        module=f"{NS}.Check.{tag}Rows{k:03d}"
        theorem=f"rows{k:03d}_checked"
        check=f"""{imports[0]}
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace {cns}
open AKLT.Gen.Gram {dns}
theorem {theorem} : checkRows lRows (d * scale ^ 2) g {a} m{k:03d} l{k:03d} = true := by
  decide +kernel
#print axioms {theorem}
end {cns}
"""
        write(root/"Check"/(tag+f"Rows{k:03d}.lean"),check)
        imports.append("import "+module)
        shards.append({"module":module,"theorem":cns+"."+theorem,"row_start":a,"row_end":z,
                       "dot_products":sum(sum(min(i+1,j+1) for j in range(n)) for i in range(a,z)) if lp else 0})
    # Structural assembly shares the proved checkRows_append_true lemma. The
    # last chunk needs no append; lengths are definitional literal equalities.
    assembly=f"rows{len(ranges)-1:03d}_checked"
    for k in range(len(ranges)-2,-1,-1):
        a,z=ranges[k]
        mt=" ++ ".join(f"m{j:03d}" for j in range(k+1,len(ranges)))
        lt=" ++ ".join(f"l{j:03d}" for j in range(k+1,len(ranges)))
        assembly=f"(@checkRows_append_true lRows m{k:03d} ({mt}) l{k:03d} ({lt}) (d * scale ^ 2) g {a} {z-a} rfl rfl rows{k:03d}_checked {assembly})"
    final="\n".join(imports)+f"""
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace {cns}
open AKLT.Gen.Gram {dns}
open scoped ComplexOrder
theorem header_checked : header mRows lRows g d scale = true := by
  decide +kernel
theorem rows_checked : checkRows lRows (d * scale ^ 2) g 0 mRows lRows = true := by
  exact {assembly}
theorem checked : checker mRows lRows g d scale = true := by
  simp only [checker, header_checked, rows_checked, Bool.and_self]
theorem positive_real : (toMatrix mRows).PosDef := checker_sound checked
theorem positive_complex :
    (castMatrix (matrix mRows.length mRows) : Matrix (Fin mRows.length) (Fin mRows.length) ℂ).PosDef :=
  checker_sound_complex checked
#print axioms header_checked
#print axioms rows_checked
#print axioms checked
#print axioms positive_real
#print axioms positive_complex
end {cns}
"""
    write(root/"Check"/(tag+".lean"),final)
    return {"pid":pid,"block":bi,"n":n,"label":b["label"],"threshold":r["threshold"],
            "data_module":dns,"pattern_module":f"{NS}.Data.P{pid:04d}",
            "check_module":cns,"positivity_theorems":[cns+".positive_real",cns+".positive_complex"],
            "matrix_entries":n*n,"factor_entries":len(lp),"shards":shards,
            "reconstruction":{"status":"OPEN","obligation":f"{NS}.Obligations.{tag}_fromDefs",
                              "meaning":"explicit Fin n equivalence and exact equality to indexedSectorMatrix"},
            "covered":{"status":"OPEN","obligation":f"{NS}.Check.P{pid:04d}_covered"},
            "kernel_status":"NOT_RUN"}



def main():
    from production_export import main as production_main
    production_main()


if __name__ == "__main__":
    main()
