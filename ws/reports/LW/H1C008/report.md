STATUS: PROVED

## Files

All proof files are under `AKLT/W/H1C008/`:

- `Main.lean`: the exact requested theorem.
- `InputFacts.lean`: checker fields, valid status digits, and inversion membership.
- `Geometry.lean`: symbolic bond and degree calculations at the eight original groups.
- `Slots.lean`: slot counts and original leader/second index identities.
- `Tokens.lean`: equality of the compiler token set with the active original tokens.

`Main.lean` transitively imports every helper file. No project source files outside the assigned proof directory were changed. The previous report remains in `report.luna.md`.

## Proof

The checker gives valid raw status digits. At each tip, its actual internal degree is the indicator of its one possible bond; at each corner it is the sum of its two possible bond indicators. These calculations identify `inputSlots` with the size of its retained single or pair group.

`inputTokens_active` proves

```lean
(inputTokens a).toFinset =
  (reductionVectors (inputPattern a) (inputRepresentation a)).image Fin.val
```

under `ValidStatuses a`, which follows from `inputCheck a = true`. Thus every inversion token is active. Every retained pair has `inputSlots a i = 2`, so the checker's equal-membership test gives precisely the required whole-pair equivalence. Leader and second index equalities are proved explicitly and used through `Fin.ext` and rewriting; all tokens are original `Fin 20` indices.

Both residual obligations from the earlier attempt are discharged. There are no residual assumptions and no dependencies on other blueprint leaf proofs.

## Exported declarations

All names below are in namespace `AKLT.W.H1C008`. The auxiliary definitions are:

- `ValidStatuses (a : Input) : Prop`: every axial and corner raw option obtained by `getD` has status at most 2.
- `compilerSite (i : Nat) : Plane`: the list `[ (2,0), (1,1), (0,2), (-1,1), (-2,0), (-1,-1), (0,-2), (1,-1) ]` at index `i`, defaulting to `(0,0)`.

The theorem signatures use `open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production`.

### InputFacts.lean

```lean
theorem validStatuses_of_check (a : Input) (h : inputCheck a = true) :
    ValidStatuses a

theorem inputInversion_mem (a : Input) (j : Fin 20) :
    j ∈ inputInversion a ↔ a.inversion.contains j.val = true

theorem inputTokens_mem (a : Input) (n : Nat) :
    n ∈ inputTokens a ↔ ∃ i < 8, ∃ k < inputSlots a i, n = ringLeader i + k

theorem inversion_supported (a : Input) (h : inputCheck a = true) :
    ∀ n ∈ a.inversion, n ∈ inputTokens a

theorem inversion_pairs (a : Input) (h : inputCheck a = true) (i : Nat) (hi : i < 8)
    (hslots : inputSlots a i = 2) :
    a.inversion.contains (ringLeader i) = a.inversion.contains (ringLeader i+1)
```

### Geometry.lean

```lean
theorem degree_compilerSite (a : Input) (hs : ValidStatuses a) (i : Nat) (hi : i < 8) :
    patternDegree (inputPattern a) (compilerSite i) =
      if i % 2 = 0 then ((rawEdges a.axes a.corners).getD (12+i/2) false).toNat
      else ((rawEdges a.axes a.corners).getD (4+i) false).toNat +
        ((rawEdges a.axes a.corners).getD (4+(i+7)%8) false).toNat
```

### Slots.lean

```lean
theorem compilerSite_mem (i : Nat) (hi : i < 8) :
    compilerSite i ∈ templateCorners ∪ templateTips

theorem compilerSite_exists (x : Plane) (hx : x ∈ templateCorners ∪ templateTips) :
    ∃ i < 8, compilerSite i = x

theorem compilerSite_leader (i : Nat) (hi : i < 8) :
    (groupLeader (compilerSite i)).val = ringLeader i

theorem compilerSite_second (i : Nat) (hi : i < 8) :
    (groupSecond (compilerSite i)).val = ringLeader i + 1

theorem inputSlots_eq (a : Input) (hs : ValidStatuses a) (i : Nat) (hi : i < 8) :
    inputSlots a i =
      if 0 < patternDegree (inputPattern a) (compilerSite i) then
        if groupIsPair (inputPattern a) (inputRepresentation a) (compilerSite i) then 2 else 1
      else 0

theorem inputSlots_pos (a : Input) (hs : ValidStatuses a) (i : Nat) (hi : i < 8) :
    0 < inputSlots a i ↔ compilerSite i ∈ reductionGroups (inputPattern a)

theorem inputSlots_two (a : Input) (hs : ValidStatuses a) (i : Nat) (hi : i < 8) :
    inputSlots a i = 2 ↔ compilerSite i ∈ reductionGroups (inputPattern a) ∧
      groupIsPair (inputPattern a) (inputRepresentation a) (compilerSite i) = true

theorem inputSlots_le_two (a : Input) (hs : ValidStatuses a) (i : Nat) (hi : i < 8) :
    inputSlots a i ≤ 2
```

### Tokens.lean

```lean
theorem inputTokens_mem_iff (a : Input) (hs : ValidStatuses a) (j : Fin 20) :
    j.val ∈ inputTokens a ↔
      j ∈ reductionVectors (inputPattern a) (inputRepresentation a)

theorem inputTokens_active (a : Input) (hs : ValidStatuses a) :
    (inputTokens a).toFinset =
      (reductionVectors (inputPattern a) (inputRepresentation a)).image Fin.val
```

### Main.lean

```lean
theorem main : AKLT.Cert.H1.Production.Leaves.compilerInversion
```

## Axioms

Each exported theorem has a `#print axioms` command in its source. Successful build output:

```text
'AKLT.W.H1C008.validStatuses_of_check' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.inputInversion_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.inputTokens_mem' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C008.inversion_supported' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C008.inversion_pairs' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C008.degree_compilerSite' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.compilerSite_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.compilerSite_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.compilerSite_leader' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.compilerSite_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.inputSlots_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.inputSlots_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.inputSlots_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.inputSlots_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.inputTokens_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.inputTokens_active' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C008.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Only `propext`, `Classical.choice`, and `Quot.sound` occur. A source audit found none of the forbidden proof escapes.

## Validation

- `lake build AKLT.W.H1C008.Geometry`: passed; target 13 seconds.
- `lake build AKLT.W.H1C008.Slots`: passed; target 7.7 seconds.
- `/usr/bin/time -f 'WALL_SECONDS=%e' lake build AKLT.W.H1C008.Main`: passed; 22.09 seconds wall time (Tokens 10 seconds, Main 6.3 seconds; earlier helpers cached).
- `lake env lean /tmp/H1C008-ExactCheck.lean`: passed; 6.15 seconds wall time. This file imports Main, checks an `example` of the exact requested type, runs `#check`, and prints axioms:

```text
AKLT.W.H1C008.main : AKLT.Cert.H1.Production.Leaves.compilerInversion
'AKLT.W.H1C008.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Open issues

After the interrupted turn, the unchanged target build passed again in 4.76 seconds, and the exact-type/axiom check passed again in 4.64 seconds.

None in the Lean proof. Independent campaign kernels were not invoked here; their recheck remains with the orchestrator.

## ORCH-SUMMARY

- Delivered exact theorem `AKLT.W.H1C008.main : AKLT.Cert.H1.Production.Leaves.compilerInversion`.
- Status: PROVED, without other blueprint leaf proof dependencies.
- Main transitively imports InputFacts, Geometry, Slots, and Tokens; no extra proof files remain.
- Proved exact active-token set equality and the whole-pair membership equivalence.
- Original `Fin 20` slot indices are preserved throughout.
- Previous residuals are fully discharged; no open residual statements or missing premises.
- Final target build passed in 22.09 seconds wall time; exact-type import check passed in 6.15 seconds.
- Axioms of main: `[propext, Classical.choice, Quot.sound]`.
- No forbidden constructs, sub-agents, or edits to existing library files.
- Independent kernel recheck is pending with the campaign infrastructure.
- Orchestrator can accept the proof and run its normal independent checks.
