STATUS: PROVED

## Delivered files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C012/AKLT/W/H1C012/Main.lean): the required unconditional theorem.
- [Bridge.lean](/home/ubuntu/aklt/wt/LW_H1C012/AKLT/W/H1C012/Bridge.lean): semantic exchange parity belongs to the checked network parity list.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_H1C012/AKLT/W/H1C012/Geometry.lean): input slot counts, diluted flags, and accepted network specifications.
- [Parities.lean](/home/ubuntu/aklt/wt/LW_H1C012/AKLT/W/H1C012/Parities.lean): structural list induction for all admissible parity bits.

`Main.lean` transitively imports every Lean file in the task directory. No files outside the task directory were changed in the worktree. The earlier report remains in `report.luna.md`.

## Proof

The geometric proof first identifies the positively oriented edges incident to each corner or tip, then calculates its semantic degree from the raw edge flags. This proves that `groupSlots` agrees with `inputSlots`, including the reduced single-leaf case. At a corner, semantic status D agrees with the compiled diluted flag.

The parity proof is an induction on an arbitrary list. A fold appends a bit only at a nonempty group, and a true bit is permitted only for a two-slot diluted group. Its accumulated value occurs in `exchangeParities`. Applying this to the accepted network's indexed sites gives `input_parity_mem`. The checked `parityCoverCheck` equality then identifies this list with the bundle parities; `List.mem_map` supplies the required bundle.

Unused single/U signs never produce a true exterior bit. Their assignments may repeat a sector; no independent-summand or injectivity claim is used. No other blueprint leaf is imported as a proved dependency, and no residual proposition remains.

## Exported declarations

All names below are in `AKLT.W.H1C012`. Other helper declarations are private. These are their complete signatures, with the indicated namespace opens:

```lean
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

theorem main : AKLT.Cert.H1.Production.Leaves.parityCoverage

theorem input_group_slots (a : Input) (h : inputCheck a = true) (i : Fin 8) :
    groupSlots (inputPattern a) (inputRepresentation a) (groupPoint i.val) =
      inputSlots a i.val

theorem input_group_diluted (a : Input) (i : Fin 8) (hi : i.val % 2 ≠ 0) :
    (inputPattern a).statusAt (groupPoint i.val) = .D ↔
      ((ringOptions a.axes a.corners).getD i.val ⟨0,0⟩).status = 2

theorem geometry_specs (a : Input) (ss : List PackedSite)
    (h : geometryCheck a ss = true) :
    ss.length = 8 ∧ ∀ i (hi : i < ss.length), ss[i].spec = inputSpec a i

def parityStep {α : Type} (site : α → PackedSite) (bit : α → Bool)
    (par : Nat) (x : α) : Nat :=
  if (site x).spec.nslots == 0 then par else 2 * par + (bit x).toNat

theorem parity_fold_mem {α : Type} (site : α → PackedSite) (bit : α → Bool)
    (xs : List α)
    (hbit : ∀ x ∈ xs, (site x).spec.nslots ≠ 0 → bit x = true →
      (site x).spec.nslots = 2 ∧ (site x).spec.diluted = true) :
    xs.foldl (parityStep site bit) 0 ∈ exchangeParities (xs.map site)

theorem input_parity_mem (a : Input) (hi : inputCheck a = true)
    (ss : List PackedSite) (hg : geometryCheck a ss = true)
    (ε : ExchangeSigns (inputPattern a)) :
    exchangeParity (inputPattern a) (inputRepresentation a) ε ∈ exchangeParities ss
```

The target unfolds to exactly:

```lean
∀ c : Case, c.MetadataAccepted →
  ∀ ε : ExchangeSigns (inputPattern c.input), ∃ b ∈ c.bundles,
    b.block.parity = exchangeParity (inputPattern c.input) (inputRepresentation c.input) ε
```

## Axioms

Each exported theorem includes a `#print axioms` check in its defining file. A separate importing check produced:

```text
AKLT.W.H1C012.main : AKLT.Cert.H1.Production.Leaves.parityCoverage
'AKLT.W.H1C012.input_group_slots' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C012.input_group_diluted' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C012.geometry_specs' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C012.parityStep' does not depend on any axioms
'AKLT.W.H1C012.parity_fold_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C012.input_parity_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C012.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only the allowed axioms occur. The delivered Lean sources contain no prohibited declarations or tactics.

## Validation

- `lake build AKLT.W.H1C012.Main` — successful, 26.41 seconds wall time for the final rebuild of all four task modules. Lake reported Parities 3.2 s, Geometry 12 s, Bridge 3.4 s, Main 2.0 s. One harmless unused-simp-argument warning remains in Geometry; imported libraries replay their existing warnings.
- `lake env lean /tmp/H1C012_Check.lean` — successful, 3.51 seconds wall time. This imports `Main`, checks `(AKLT.W.H1C012.main : AKLT.Cert.H1.Production.Leaves.parityCoverage)`, proves an example of that exact type using `main`, and prints all exported declarations' axioms.
- Source review verified the import closure, task-only worktree changes, and absence of forbidden constructs.

Full evidence: [build.log](/home/ubuntu/aklt/reports/LW/H1C012/build.log), [build.time](/home/ubuntu/aklt/reports/LW/H1C012/build.time), [check.log](/home/ubuntu/aklt/reports/LW/H1C012/check.log), [check.time](/home/ubuntu/aklt/reports/LW/H1C012/check.time).

## Open issues

None in the mathematical proof or required deliverable. Secondary-kernel replay was not run locally and remains with the campaign checker.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C012/Main.lean` and its three imported helper modules.
- Required theorem: `AKLT.W.H1C012.main : AKLT.Cert.H1.Production.Leaves.parityCoverage`.
- Status: unconditional proof; no residuals and no dependence on other proved blueprint leaves.
- Reused the earlier checked-list-to-bundle extraction argument; proved the missing semantic membership bridge.
- Handles unused single/U signs by permitting exterior bits only at retained diluted pairs.
- Final module build and separate exact-type check both pass.
- Main axioms: `[propext, Classical.choice, Quot.sound]`.
- All exported theorem axioms checked; no prohibited constructs.
- Every task Lean file is transitively imported by Main.
- No mathematical limitations, missing premises, or requested-name deviations.
- One harmless unused-simp-argument warning remains; secondary kernels were not run locally.
- Orchestrator action: run the standard independent checker and register the leaf.
