STATUS: PROVED

## Files

- Proof: `/home/ubuntu/aklt/wt/LW_H1C019/AKLT/W/H1C019/Main.lean`.
- Separate import and exact-type check: `/home/ubuntu/aklt/reports/LW/H1C019/Check.lean`.
- Report: `/home/ubuntu/aklt/reports/LW/H1C019/report.md`.
- The earlier report remains preserved as `report.luna.md`.

The task directory contains only `Main.lean`. No statement, library, or other task file was modified.

## Exported declaration

```lean
theorem AKLT.W.H1C019.main : AKLT.Cert.H1.Production.Leaves.paritySlice
```

This proves the frozen statement unconditionally, from its own metadata and layout hypotheses. All auxiliary definitions and theorems are private. No other blueprint leaf is imported as a proved dependency.

## Proof

The earlier contraction proof is reused, and its coordinate residual is now fully proved:

1. A generic mixed-radix fold lemma recovers any bounded digit by dividing by the product of following radices and taking the current modulus.
2. The parity component of `sectorLabel` is such a fold, using radix one at sites without slots and radix two elsewhere. Its suffix product is exactly the power of two used in `sectorNetworkCheck`.
3. `basisCheck` gives each selected index its declared parity. Accepted dimension checks and the recovered parity bit show that each original digit belongs to its selected coordinate list. For a D pair, the exterior list is exactly `[3]`, and the symmetric list is exactly `[0,1,2]`.
4. `sectorNetworkCheck` identifies each base site, coordinate list, and sector stride. Applying the same mixed-radix lemma to `remapIndex`, then using `remapCheck`, proves both local coordinate identities.
5. These identities identify the local matrices. Structural induction carries them through the ring product, trace, center-code sums, and both choices of `next`.

The proof preserves coordinate `3`, the stored table entries, and the antisymmetric coefficient sign. It performs no normalization or coordinate permutation. Index and input equalities are established explicitly before rewriting their uses; no large concrete enumeration is evaluated by definitional equality.

## Axioms

`#print axioms AKLT.W.H1C019.main`:

```text
'AKLT.W.H1C019.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

No forbidden proof mechanisms occur in the delivered source.

## Validation

Commands ran from `/home/ubuntu/aklt/wt/LW_H1C019`, with `$HOME/.elan/bin` on `PATH`.

```text
lake build AKLT.W.H1C019.Main
Build completed successfully (8965 jobs).
```

Wall time: 12.00 seconds; the target module compiled in 6.8 seconds. Warnings were replayed from existing dependencies; the task module produced no warnings.

```text
lake env lean /home/ubuntu/aklt/reports/LW/H1C019/Check.lean
AKLT.W.H1C019.main : AKLT.Cert.H1.Production.Leaves.paritySlice
'AKLT.W.H1C019.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Exit status: zero. Wall time: 5.29 seconds. The separate check includes an `example` assigning `main` to the exact required closed type.

## Open issues

None. There are no residual statements or additional premises. The campaign's independent con-ron/NanoDa rechecks were not run locally.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C019/Main.lean`.
- Exported `AKLT.W.H1C019.main : AKLT.Cert.H1.Production.Leaves.paritySlice`.
- Status: PROVED, with no other blueprint-leaf dependencies.
- Completed the earlier coordinate residual using generic mixed-radix decoding and parity-bit extraction.
- D exterior coordinate `3` and the original antisymmetric sign are preserved exactly.
- Build passed: 12.00 seconds wall time, 6.8 seconds target compilation.
- Separate import and exact-type check passed: 5.29 seconds.
- Axioms: propext, Classical.choice, Quot.sound.
- Open declarations: none. Additional hypotheses: none. Scope deviations: none.
- Independent con-ron/NanoDa checks remain for the campaign checker.
- Orchestrator: accept the completed leaf and run the standard independent rechecks.
