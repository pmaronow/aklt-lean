STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C031/AKLT/W/H1C031/Main.lean) — fixed-width decoding, semantic recovery, and the requested theorem.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_H1C031/AKLT/W/H1C031/Geometry.lean) — template support, reflection, canonical bond orientation, and live-site support. Imported by Main.
- [build.log](/home/ubuntu/aklt/reports/LW/H1C031/build.log) — successful build, exact-type check, and all axiom audit output.

No files outside the task directory and report directory were edited. No other blueprint leaves were used as dependencies. The earlier attempt's arithmetic decoder and minimum-case reduction were reused and completed.

## Result

```lean
theorem AKLT.W.H1C031.main :
  AKLT.Cert.H1.Production.Leaves.effectiveCodeClassification
```

The proof decodes equal selected orientations of the minimum code into equal fixed-width status, edge, and outgoing digits. Every present bond lies on one of the sixteen template edges up to reversal; that support is invariant under reflection. Undirected equality recovers the original bond finset because its positive orientation excludes reversed bonds. A live site's status digit is nonzero, so equality with the target's effective digit forces the target to be live and recovers its status. Coveredness fixes the centre and tip statuses. Both formerly residual template-recovery statements are proved here; isolated-site statuses remain unrestricted.

## Exported declarations and statements

All names in the following signatures are in namespace `AKLT.W.H1C031`; the open namespaces are `AKLT.Defs`, `AKLT.Cert.H1`, and, in Main, `AKLT.Cert.H1.Production`. The two `Residual_...` definitions are retained as transparent interfaces from the earlier attempt, and are now discharged by `sameTemplateRecovery` and `crossTemplateRecovery`.

### Geometry.lean

```lean
theorem mem_internalBonds_iff {G : Finset Plane} {a b : Plane} :
    (a, b) ∈ internalBonds G ↔ a ∈ G ∧ b ∈ G ∧
      (b = (a.1 + 1, a.2) ∨ b = (a.1, a.2 + 1))

theorem internalBonds_no_reverse {G : Finset Plane} {a b : Plane}
    (h : (a, b) ∈ internalBonds G) : (b, a) ∉ internalBonds G

theorem mem_square_iff {x a : Plane} {u : Nat} :
    x ∈ square a u ↔
      (a.1 - (u : ℤ) ≤ x.1 ∧ x.1 ≤ a.1 + u) ∧
      (a.2 - (u : ℤ) ≤ x.2 ∧ x.2 ≤ a.2 + u)

theorem mem_templateSites_iff {x : Plane} :
    x ∈ templateSites ↔
      ((-2 ≤ x.1 ∧ x.1 ≤ 2) ∧ (-2 ≤ x.2 ∧ x.2 ≤ 2)) ∧
      latticeDist x (0, 0) ≤ 2

theorem templateSite_cases {x : Plane} (hx : x ∈ templateSites) :
    x = (0, 0) ∨ x ∈ ringSites ∨ x ∈ templateTips

theorem internalBond_templateEdge {a b : Plane}
    (h : (a, b) ∈ internalBonds templateSites) :
    (a, b) ∈ templateEdges ∨ (b, a) ∈ templateEdges

theorem reflectPoint_involution (f : Bool) (x : Plane) :
    reflectPoint f (reflectPoint f x) = x

theorem reflectPoint_false (x : Plane) : reflectPoint false x = x

theorem reflectPoint_true (x : Plane) : reflectPoint true x = (-x.1, x.2)

theorem reflectPoint_comm (f g : Bool) (x : Plane) :
    reflectPoint f (reflectPoint g x) = reflectPoint g (reflectPoint f x)

theorem reflect_ringSite (f : Bool) {x : Plane} (hx : x ∈ ringSites) :
    reflectPoint f x ∈ ringSites

theorem reflect_tip (f : Bool) {x : Plane} (hx : x ∈ templateTips) :
    reflectPoint f x ∈ templateTips

theorem reflect_templateEdge (f : Bool) {a b : Plane}
    (h : (a, b) ∈ templateEdges ∨ (b, a) ∈ templateEdges) :
    (reflectPoint f a, reflectPoint f b) ∈ templateEdges ∨
      (reflectPoint f b, reflectPoint f a) ∈ templateEdges

theorem presentBond_symm (π : PatternData) (a b : Plane) :
    presentBond π a b = presentBond π b a

theorem presentBond_templateEdge {π : PatternData} {a b : Plane}
    (h : presentBond π a b = true) :
    (a, b) ∈ templateEdges ∨ (b, a) ∈ templateEdges

theorem bonds_eq_of_presentBond_eq {π ρ : PatternData}
    (h : ∀ a b, presentBond π a b = presentBond ρ a b) : π.bonds = ρ.bonds

theorem positiveDegree_site_status {π : PatternData} {x : Plane}
    (hx : 0 < patternDegree π x) : x ∈ templateSites ∧ π.statusAt x ≠ .X
```

### Main.lean

```lean
def orientedStatusDigits (π : PatternData) (reflect : Bool) : List Nat :=
  ringSites.map fun x =>
    let y := reflectPoint reflect x
    if patternDegree π y == 0 then 0 else statusDigit (π.statusAt y)

def orientedEdgeDigits (π : PatternData) (reflect : Bool) : List Nat :=
  templateEdges.map fun (a,b) =>
    (presentBond π (reflectPoint reflect a) (reflectPoint reflect b)).toNat

def orientedOutgoingDigit (π : PatternData) (reflect : Bool) : Nat :=
  if π.outgoing == .north then 1
  else if (π.outgoing == .east) != reflect then 0 else 2

theorem orientedCode_formula (π : PatternData) (reflect : Bool) :
    reflectedPatternCode π reflect =
      (encodeDigits 3 (orientedStatusDigits π reflect) * 65536 +
        encodeDigits 2 (orientedEdgeDigits π reflect)) * 3 +
          orientedOutgoingDigit π reflect

theorem encodeDigits_lt_of_digits {base : Nat} (xs : List Nat)
    (h : ∀ a ∈ xs, a < base) : encodeDigits base xs < base ^ xs.length

theorem encodeDigits_inj_fixed {base : Nat} (hb : 0 < base)
    {xs ys : List Nat} (hlen : xs.length = ys.length)
    (hxs : ∀ a ∈ xs, a < base) (hys : ∀ a ∈ ys, a < base)
    (heq : encodeDigits base xs = encodeDigits base ys) : xs = ys

theorem statusDigits_bounded (π : PatternData) (f : Bool) :
    ∀ d ∈ orientedStatusDigits π f, d < 3

theorem edgeDigits_bounded (π : PatternData) (f : Bool) :
    ∀ d ∈ orientedEdgeDigits π f, d < 2

theorem statusDigit_getD {π : PatternData} {f : Bool} {i : Nat}
    (hi : i < ringSites.length) :
    (orientedStatusDigits π f).getD i 0 =
      (if patternDegree π (reflectPoint f (ringSites.getD i (0, 0))) == 0 then 0
        else statusDigit (π.statusAt (reflectPoint f (ringSites.getD i (0, 0)))))

theorem edgeDigit_getD {π : PatternData} {f : Bool} {i : Nat}
    (hi : i < templateEdges.length) :
    (orientedEdgeDigits π f).getD i 0 =
      (presentBond π
        (reflectPoint f (templateEdges.getD i ((0, 0), (0, 0))).1)
        (reflectPoint f (templateEdges.getD i ((0, 0), (0, 0))).2)).toNat

theorem orientedCode_eq_digits {π ρ : PatternData} {f g : Bool}
    (h : reflectedPatternCode π f = reflectedPatternCode ρ g) :
    orientedStatusDigits π f = orientedStatusDigits ρ g ∧
    orientedEdgeDigits π f = orientedEdgeDigits ρ g ∧
    orientedOutgoingDigit π f = orientedOutgoingDigit ρ g

theorem outgoing_of_orientedDigits {π ρ : PatternData}
    (hπ : π.Covered) (hρ : ρ.Covered) {f g : Bool}
    (h : orientedOutgoingDigit π f = orientedOutgoingDigit ρ g) :
    (if f = g then π.outgoing = ρ.outgoing
      else π.outgoing.step = reflectPoint true ρ.outgoing.step)

def Residual_sameTemplateRecovery : Prop :=
  ∀ π ρ : PatternData, π.Covered → ρ.Covered → ∀ f : Bool,
    orientedStatusDigits π f = orientedStatusDigits ρ f →
    orientedEdgeDigits π f = orientedEdgeDigits ρ f →
      π.bonds = ρ.bonds ∧
      ∀ x : Plane, 0 < patternDegree π x → π.statusAt x = ρ.statusAt x

def Residual_crossTemplateRecovery : Prop :=
  ∀ π ρ : PatternData, π.Covered → ρ.Covered → ∀ f g : Bool, f ≠ g →
    orientedStatusDigits π f = orientedStatusDigits ρ g →
    orientedEdgeDigits π f = orientedEdgeDigits ρ g →
      (∀ a b : Plane, presentBond π a b =
        presentBond ρ (reflectPoint true a) (reflectPoint true b)) ∧
      ∀ x : Plane, 0 < patternDegree π x →
        π.statusAt x = ρ.statusAt (reflectPoint true x)

theorem orientedEdgeDigits_eq_on {π ρ : PatternData} {f g : Bool}
    (h : orientedEdgeDigits π f = orientedEdgeDigits ρ g)
    {a b : Plane} (hab : (a, b) ∈ templateEdges) :
    presentBond π (reflectPoint f a) (reflectPoint f b) =
      presentBond ρ (reflectPoint g a) (reflectPoint g b)

theorem orientedPresentBond_eq {π ρ : PatternData} {f g : Bool}
    (h : orientedEdgeDigits π f = orientedEdgeDigits ρ g) (a b : Plane) :
    presentBond π (reflectPoint f a) (reflectPoint f b) =
      presentBond ρ (reflectPoint g a) (reflectPoint g b)

theorem statusDigit_injective : Function.Injective statusDigit

theorem orientedStatusDigits_eq_live {π ρ : PatternData} {f g : Bool}
    (h : orientedStatusDigits π f = orientedStatusDigits ρ g)
    {x : Plane} (hm : x ∈ ringSites) (hx : 0 < patternDegree π x) :
    π.statusAt x = ρ.statusAt (reflectPoint g (reflectPoint f x))

theorem sameTemplateRecovery : Residual_sameTemplateRecovery

theorem crossTemplateRecovery : Residual_crossTemplateRecovery

theorem main_from_residuals
    (hs : Residual_sameTemplateRecovery) (hc : Residual_crossTemplateRecovery) :
    AKLT.Cert.H1.Production.Leaves.effectiveCodeClassification

theorem main : AKLT.Cert.H1.Production.Leaves.effectiveCodeClassification
```

## Axiom audit

Every exported theorem has an explicit `#print axioms` command in its source. The successful build produced:

```text
'AKLT.W.H1C031.mem_internalBonds_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.internalBonds_no_reverse' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.mem_square_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.mem_templateSites_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.templateSite_cases' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.internalBond_templateEdge' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.reflectPoint_involution' depends on axioms: [propext]
'AKLT.W.H1C031.reflectPoint_false' depends on axioms: [propext]
'AKLT.W.H1C031.reflectPoint_true' depends on axioms: [propext]
'AKLT.W.H1C031.reflectPoint_comm' depends on axioms: [propext]
'AKLT.W.H1C031.reflect_ringSite' depends on axioms: [propext]
'AKLT.W.H1C031.reflect_tip' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.reflect_templateEdge' depends on axioms: [propext]
'AKLT.W.H1C031.presentBond_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.presentBond_templateEdge' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.bonds_eq_of_presentBond_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.positiveDegree_site_status' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.orientedCode_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.encodeDigits_lt_of_digits' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.encodeDigits_inj_fixed' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.statusDigits_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.edgeDigits_bounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.statusDigit_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.edgeDigit_getD' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.orientedCode_eq_digits' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.outgoing_of_orientedDigits' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.main_from_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.orientedEdgeDigits_eq_on' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.orientedPresentBond_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.statusDigit_injective' depends on axioms: [propext]
'AKLT.W.H1C031.orientedStatusDigits_eq_live' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.sameTemplateRecovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.crossTemplateRecovery' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C031.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the permitted axioms occur. The source scan found no forbidden declarations or proof shortcuts.

## Build and exact-type check

Command, with the timing wrapper omitted:

```sh
PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1C031.Main
```

Passed: **20.56 seconds** wall time, including dependency replay; Geometry took 8.5 seconds and Main 7.0 seconds. Both task modules compiled without warnings. Replayed dependencies emitted existing linter warnings.

The compiled Main file also contains:

```lean
#check (AKLT.W.H1C031.main : AKLT.Cert.H1.Production.Leaves.effectiveCodeClassification)
```

It reported the exact requested name and type. The final validation used Lean's kernel; con-ron and NanoDa were not run in this task. Geometric support is proved through symbolic membership lemmas and bounded coordinate cases, without deciding equality of large concrete Finsets or constructing finite equivalences.

## Open issues

None. No residual hypotheses, missing blueprint dependencies, or strengthened assumptions remain in `main`.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT.W.H1C031.main` with exactly the requested closed type.
- Main imports the only helper file, Geometry.
- Completed both residual template-recovery arguments from the earlier attempt.
- Canonical oriented bonds are recovered from undirected support.
- Status equality is required and proved only at positive-degree sites.
- No blueprint leaf dependencies or new assumptions.
- All 34 exported theorems audited; only permitted axioms occur.
- Requested Lake build passed in 20.56 seconds; exact-name/type check passed.
- No open mathematical obligations or deviations from the statement.
- Independent-kernel checks remain part of the downstream campaign validation.
- Orchestrator may accept and register this leaf.
