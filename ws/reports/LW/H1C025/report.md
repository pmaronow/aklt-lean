STATUS: PROVED

The exact requested theorem is proved unconditionally:

```lean
theorem AKLT.W.H1C025.main : AKLT.Cert.H1.Production.Leaves.rawEncoding
```

Files:

- [Extraction.lean](/home/ubuntu/aklt/wt/LW_H1C025/AKLT/W/H1C025/Extraction.lean)
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_H1C025/AKLT/W/H1C025/Geometry.lean)
- [Compatibility.lean](/home/ubuntu/aklt/wt/LW_H1C025/AKLT/W/H1C025/Compatibility.lean)
- [Edges.lean](/home/ubuntu/aklt/wt/LW_H1C025/AKLT/W/H1C025/Edges.lean)
- [Encoding.lean](/home/ubuntu/aklt/wt/LW_H1C025/AKLT/W/H1C025/Encoding.lean)
- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C025/AKLT/W/H1C025/Main.lean)

All six Lean files are transitively imported by Main.lean. No frozen source was changed. No other blueprint leaf is used as a lemma; imports outside this directory are the original production definitions and their existing libraries.

The proof constructs axesOf π and cornersOf π directly from any covered PatternData. Removed sites get mask 0, U sites get mask 15, and D sites retain their actual kept directions. A bijection between the four encoded directions and keptAt proves the two-direction mask classification. The covered arrival and non-arrival rules then establish membership in axialConfigurations. Mutual consistency at nonremoved non-tip endpoints establishes every cornerCompatible condition.

The edge comparison proves that all sixteen raw edge bits equal presentBond on templateEdges. It treats covering tips using the tip exception, so their arbitrary kept flags have no effect. A separate degree-zero characterization proves that the raw liveness test deletes precisely the isolated sites used by reflectedPatternCode. Explicit equalities of the status and edge lists justify both reflection permutations. The two code equalities imply equality of the minimum keys. This handles arbitrary covered raw flags and does not assume the raw class is the 2,048,000 normalized configurations.

Axiom audit:

```text
'AKLT.W.H1C025.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every one of the 44 exported theorems has a #print axioms command in its source. All 44 report exactly the same permitted set above; the complete output is in [build.log](/home/ubuntu/aklt/reports/LW/H1C025/build.log).

Validation commands and wall times (PATH includes $HOME/.elan/bin):

| Check | Command | Result | Seconds |
|---|---|---|---:|
| Build all new modules | `lake build AKLT.W.H1C025.Main` | PASS | 53.68 |
| Exact type and axioms | `lake env lean /tmp/H1C025Exact.lean` | PASS | 6.47 |
| Export theorem and proof closure | `lake env leanexport AKLT.W.H1C025.Main -- AKLT.W.H1C025.main` | PASS | 7.80 |
| con-ron | `con-ron --verified --jobs=1 export.ndjson` | ACCEPT | 9.15 |
| NanoDa | `nanoda_bin nanoda.json` | ACCEPT | 3.16 |

The temporary exact check imported AKLT.W.H1C025.Main and checked:

```lean
example : AKLT.Cert.H1.Production.Leaves.rawEncoding := AKLT.W.H1C025.main
#check (AKLT.W.H1C025.main : AKLT.Cert.H1.Production.Leaves.rawEncoding)
#print axioms AKLT.W.H1C025.main
```

Its output is in [exact-check.log](/home/ubuntu/aklt/reports/LW/H1C025/exact-check.log).
The exporter and checker binaries are from the installed Lean 4.35.0-rc2 toolchain. Both checkers ran with one worker and a 180-second timeout. The NanoDa configuration rejects axioms outside the permitted three.

Independent checker receipts:

```text
con-ron: accepted 6700 declarations (--verified)
Checked 7459 declarations with no typechecker errors, 1 pretty printer errors: [
    "Unable to print axioms",
]
```

Both processes exited 0. NanoDa's reported pretty-printer issue concerns its axiom display; it reports no typechecker errors. The Lean axiom audit above separately succeeded.

The shared export is 33,641,922 bytes, SHA-256 `5ecef3175827ef836c04f137a02373dbd5b1ad23b00a46cee480d250aa5aa84c`.
Receipts and reproducible configuration are retained as [con-ron.log](/home/ubuntu/aklt/reports/LW/H1C025/con-ron.log), [nanoda.log](/home/ubuntu/aklt/reports/LW/H1C025/nanoda.log), [nanoda.json](/home/ubuntu/aklt/reports/LW/H1C025/nanoda.json), and [export-manifest.json](/home/ubuntu/aklt/reports/LW/H1C025/export-manifest.json). The corresponding .time files record resource use.

There are no open obligations or residual propositions. The earlier conditional assembly and its five residuals have been replaced by the unconditional proof. The previous report remains preserved in report.luna.md.

Exported declaration interfaces follow. All names are in namespace AKLT.W.H1C025; open namespaces are AKLT.Defs, AKLT.Cert.H1, and AKLT.Cert.H1.Production. Definition bodies and theorem proofs are in the linked source files. Two supporting instances provide LawfulBEq RawOption and Decidable (bondCondition π a b).

Extraction.lean:

```lean
def dirPoint (x : Plane) (d : Fin 4) : Plane

def keptDirs (π : PatternData) (x : Plane) : Finset (Fin 4)

def keptMask (π : PatternData) (x : Plane) : Nat

def rawOptionAt (π : PatternData) (x : Plane) : RawOption

def axesOf (π : PatternData) : List RawOption

def cornersOf (π : PatternData) : List RawOption

def compassIndex : Compass → Fin 4

theorem keptMask_hasDirection (π : PatternData) (x : Plane) (d : Fin 4) :
    hasDirection (keptMask π x) d.val = decide (d ∈ keptDirs π x)

theorem keptDirs_card (π : PatternData) (x : Plane)
    (hx : x ∈ templateSites) : (keptDirs π x).card = (π.keptAt x).card

def outgoingIndex (c : Compass) : Nat

theorem outgoingIndex_lt (π : PatternData) (hπ : π.Covered) :
    outgoingIndex π.outgoing < 3

theorem rawOption_status (π : PatternData) (x : Plane) :
    (rawOptionAt π x).status = statusDigit (π.statusAt x)

theorem rawOption_nonzero (π : PatternData) (x : Plane) :
    (rawOptionAt π x).status ≠ 0 ↔ π.statusAt x ≠ .X

theorem card_four (s : Finset (Fin 4)) :
    s.card = (if (0 : Fin 4) ∈ s then 1 else 0) +
      (if (1 : Fin 4) ∈ s then 1 else 0) +
      (if (2 : Fin 4) ∈ s then 1 else 0) +
      (if (3 : Fin 4) ∈ s then 1 else 0)

theorem keptMask_two (π : PatternData) (x : Plane) (hx : x ∈ templateSites)
    (hc : (π.keptAt x).card = 2) :
    keptMask π x ∈ ([3,5,9,6,10,12] : List Nat)

theorem dirPoint_neighbour (x : Plane) (d : Fin 4) :
    dirPoint x d ∈ neighbours x

theorem rawOption_direction (π : PatternData) (hπ : π.Covered) (x : Plane)
    (hx : x ∈ templateSites) (h0 : x ≠ (0,0)) (ht : x ∉ templateTips)
    (hs : π.statusAt x ≠ .X) (d : Fin 4) :
    hasDirection (rawOptionAt π x).mask d.val =
      decide (dirPoint x d ∈ π.keptAt x)

theorem rawOption_corner (π : PatternData) (hπ : π.Covered) (x : Plane)
    (hx : x ∈ templateCorners) (hxt : x ∈ templateSites) :
    rawOptionAt π x ∈ cornerOptions

theorem axial_X (i : Fin 4) : (⟨0,0⟩ : RawOption) ∈ axialOptions i.val

theorem axial_U (i : Fin 4) (hi : i.val < 3) :
    (⟨1,15⟩ : RawOption) ∈ axialOptions i.val

theorem axial_D (i : Fin 4) (m : Nat) (hm : m ∈ ([3,5,9,6,10,12] : List Nat))
    (hb : hasDirection m ((i.val+2)%4) = decide (i.val ≠ 3)) :
    (⟨2,m⟩ : RawOption) ∈ axialOptions i.val

theorem axis_mem (π : PatternData) (hπ : π.Covered) (i : Fin 4) :
    rawOptionAt π (compassAt i.val).step ∈ axialOptions i.val

theorem axes_mem (π : PatternData) (hπ : π.Covered) : axesOf π ∈ axialConfigurations
```

Geometry.lean:

```lean
theorem mem_internal (S : Finset Plane) (a b : Plane) :
    (a,b) ∈ internalBonds S ↔
      a ∈ S ∧ b ∈ S ∧ b ∈ positiveNeighbours a

theorem internal_template {a b : Plane} (he : (a,b) ∈ internalBonds templateSites) :
    (a,b) ∈ templateEdges ∨ (b,a) ∈ templateEdges

theorem template_internal (a b : Plane) (he : (a,b) ∈ templateEdges) :
    (a,b) ∈ internalBonds templateSites ∨ (b,a) ∈ internalBonds templateSites

def bondCondition (π : PatternData) (a b : Plane) : Prop

theorem presentBond_iff (π : PatternData) (a b : Plane)
    (he : (a,b) ∈ templateEdges) :
    presentBond π a b = true ↔ bondCondition π a b

theorem presentBond_symm (π : PatternData) (a b : Plane) :
    presentBond π a b = presentBond π b a

theorem presentBond_mem (π : PatternData) (a b : Plane) :
    presentBond π a b = true ↔ (a,b) ∈ π.bonds ∨ (b,a) ∈ π.bonds

theorem degree_zero (π : PatternData) (x : Plane) :
    patternDegree π x = 0 ↔ ∀ e ∈ templateEdges,
      (e.1 = x ∨ e.2 = x) → presentBond π e.1 e.2 = false

def semanticEdges (π : PatternData) : List Bool

def edgeLive (edges : List Bool) (i : Nat) : Bool

theorem ring_degree_zero (π : PatternData) (i : Fin 8) :
    patternDegree π (ringSites.getD i.val (0,0)) = 0 ↔
      edgeLive (semanticEdges π) i.val = false
```

Compatibility.lean:

```lean
def cornerPoint (i : Fin 4) : Plane

theorem cornerPoint_facts (i : Fin 4) :
    cornerPoint i ∈ templateCorners ∧ cornerPoint i ∈ templateSites

theorem compatible_pair (π : PatternData) (hπ : π.Covered) (x y : Plane)
    (d e : Nat) (hd : d < 4) (he : e < 4)
    (hx : x ∈ templateSites) (hy : y ∈ templateSites)
    (hx0 : x ≠ (0,0)) (hy0 : y ≠ (0,0))
    (hxt : x ∉ templateTips) (hyt : y ∉ templateTips)
    (hxy : dirPoint x ⟨d,hd⟩ = y) (hyx : dirPoint y ⟨e,he⟩ = x)
    (ha : Adjacent x y) :
    ((rawOptionAt π x).status = 0 ∨ (rawOptionAt π y).status = 0) ∨
      hasDirection (rawOptionAt π x).mask d =
        hasDirection (rawOptionAt π y).mask e

theorem corner_compatible (π : PatternData) (hπ : π.Covered) (i : Fin 4) :
    cornerCompatible (axesOf π) i.val (rawOptionAt π (cornerPoint i)) = true

theorem corners_valid (π : PatternData) (hπ : π.Covered) :
    (cornersOf π).zipIdx.all (fun (x,i) =>
      cornerOptions.contains x && cornerCompatible (axesOf π) i x) = true
```

Edges.lean:

```lean
def axisPoint (i : Fin 4) : Plane

def axisTip (i : Fin 4) : Plane

theorem axis_facts (i : Fin 4) :
    axisPoint i ∈ templateSites ∧ axisPoint i ≠ (0,0) ∧ axisPoint i ∉ templateTips

theorem axis_tip (i : Fin 4) : axisTip i ∈ templateTips

theorem center_edge (π : PatternData) (hπ : π.Covered) (i : Fin 4) :
    (i.val != 3 && (rawOptionAt π (axisPoint i)).status != 0 &&
      hasDirection (rawOptionAt π (axisPoint i)).mask ((i.val+2)%4)) =
        presentBond π (0,0) (axisPoint i)

theorem tip_edge (π : PatternData) (hπ : π.Covered) (i : Fin 4) :
    ((rawOptionAt π (axisPoint i)).status != 0 &&
      hasDirection (rawOptionAt π (axisPoint i)).mask i.val) =
        presentBond π (axisPoint i) (axisTip i)

theorem cycle_edge (π : PatternData) (hπ : π.Covered) (x y : Plane)
    (d e : Nat) (hd : d < 4) (he : e < 4)
    (hx : x ∈ templateSites) (hy : y ∈ templateSites)
    (hx0 : x ≠ (0,0)) (hy0 : y ≠ (0,0))
    (hxt : x ∉ templateTips) (hyt : y ∉ templateTips)
    (hxy : dirPoint x ⟨d,hd⟩ = y) (hyx : dirPoint y ⟨e,he⟩ = x)
    (hi : (x,y) ∈ templateEdges) :
    ((rawOptionAt π x).status != 0 && (rawOptionAt π y).status != 0 &&
      hasDirection (rawOptionAt π x).mask d &&
        hasDirection (rawOptionAt π y).mask e) = presentBond π x y

theorem rawEdges_explicit (e n w s ne nw sw se : RawOption) :
    rawEdges [e,n,w,s] [ne,nw,sw,se] =
      [e.status != 0 && hasDirection e.mask 2,
       n.status != 0 && hasDirection n.mask 3,
       w.status != 0 && hasDirection w.mask 0, false,
       e.status != 0 && ne.status != 0 && hasDirection e.mask 1 && hasDirection ne.mask 3,
       ne.status != 0 && n.status != 0 && hasDirection ne.mask 2 && hasDirection n.mask 0,
       n.status != 0 && nw.status != 0 && hasDirection n.mask 2 && hasDirection nw.mask 0,
       nw.status != 0 && w.status != 0 && hasDirection nw.mask 3 && hasDirection w.mask 1,
       w.status != 0 && sw.status != 0 && hasDirection w.mask 3 && hasDirection sw.mask 1,
       sw.status != 0 && s.status != 0 && hasDirection sw.mask 0 && hasDirection s.mask 2,
       s.status != 0 && se.status != 0 && hasDirection s.mask 0 && hasDirection se.mask 2,
       se.status != 0 && e.status != 0 && hasDirection se.mask 1 && hasDirection e.mask 3,
       e.status != 0 && hasDirection e.mask 0,
       n.status != 0 && hasDirection n.mask 1,
       w.status != 0 && hasDirection w.mask 2,
       s.status != 0 && hasDirection s.mask 3]

theorem edges_eq (π : PatternData) (hπ : π.Covered) :
    rawEdges (axesOf π) (cornersOf π) = semanticEdges π
```

Encoding.lean:

```lean
def semanticStatus (π : PatternData) : List Nat

theorem ring_options (π : PatternData) :
    ringOptions (axesOf π) (cornersOf π) = ringSites.map (rawOptionAt π)

theorem status_at (π : PatternData) (i : Fin 8) :
    (if edgeLive (semanticEdges π) i.val then
        (rawOptionAt π (ringSites.getD i.val (0,0))).status else 0) =
      (if patternDegree π (ringSites.getD i.val (0,0)) == 0 then 0
        else statusDigit (π.statusAt (ringSites.getD i.val (0,0))))

theorem statuses_eq (π : PatternData) :
    rawStatusDigits (axesOf π) (cornersOf π) (semanticEdges π) = semanticStatus π

theorem reflected_status (π : PatternData) :
    reflectSites.map (fun i => (semanticStatus π).getD i 0) =
      ringSites.map (fun x => if patternDegree π (reflectPoint true x) == 0 then 0
        else statusDigit (π.statusAt (reflectPoint true x)))

theorem reflected_edges (π : PatternData) :
    reflectEdges.map (fun i => (semanticEdges π).getD i false) =
      templateEdges.map (fun (a,b) =>
        presentBond π (reflectPoint true a) (reflectPoint true b))

theorem outgoing_code (π : PatternData) (hπ : π.Covered) (r : Bool) :
    (if r then
        if outgoingIndex π.outgoing == 0 then 2
        else if outgoingIndex π.outgoing == 2 then 0 else outgoingIndex π.outgoing
      else outgoingIndex π.outgoing) =
      (if π.outgoing == .north then 1
        else if (π.outgoing == .east) != r then 0 else 2)

theorem code_eq (π : PatternData) (hπ : π.Covered) (r : Bool) :
    rawCode (axesOf π) (cornersOf π) (outgoingIndex π.outgoing) r =
      reflectedPatternCode π r

theorem outgoing_present (π : PatternData) (hπ : π.Covered) :
    presentBond π (0,0) π.outgoing.step = true

theorem outgoing_edge (π : PatternData) (hπ : π.Covered) :
    (rawEdges (axesOf π) (cornersOf π)).getD (outgoingIndex π.outgoing) false = true
```

Main.lean:

```lean
theorem main : AKLT.Cert.H1.Production.Leaves.rawEncoding
```

## ORCH-SUMMARY

- Delivered AKLT/W/H1C025/Main.lean and five transitively imported helper modules.
- Exact theorem: AKLT.W.H1C025.main : AKLT.Cert.H1.Production.Leaves.rawEncoding.
- STATUS: PROVED; no dependency leaves or residual assumptions.
- Arbitrary covered raw flags are handled by normalization and proved bond preservation.
- Covered mutual consistency justifies corner pruning; actual degrees justify isolated-site removal.
- Both plain and reflected code comparisons are proved.
- All 44 theorem axiom audits: [propext, Classical.choice, Quot.sound].
- lake build AKLT.W.H1C025.Main passed in 53.68 seconds.
- Fresh exact-type check passed.
- con-ron accepted 6700 declarations (--verified); NanoDa checked 7459 with no typechecker errors.
- NanoDa also reports one axiom pretty-printer error; its checking exit status is 0.
- Open names: none. Limitations or deviations in theorem scope: none.
- Orchestrator can register the theorem and merge all six Lean files.
