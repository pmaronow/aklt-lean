STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M036/AKLT/W/H1M036/Main.lean): exports the requested theorem and prints the axioms for every public theorem in the deliverable.
- [Proof.lean](/home/ubuntu/aklt/wt/LW_H1M036/AKLT/W/H1M036/Proof.lean): contains the token matrix algebra and three public operator commutator lemmas.

## Exported declarations

- `AKLT.W.H1M036.endZP (J : Finset (Fin 20))`:
  `totalSpinZ J * totalSpinPlus J - totalSpinPlus J * totalSpinZ J = totalSpinPlus J`.
- `AKLT.W.H1M036.endZM (J : Finset (Fin 20))`:
  `totalSpinZ J * totalSpinMinus J - totalSpinMinus J * totalSpinZ J = -totalSpinMinus J`.
- `AKLT.W.H1M036.endPM (J : Finset (Fin 20))`:
  `totalSpinPlus J * totalSpinMinus J - totalSpinMinus J * totalSpinPlus J = (2 : ℂ) • totalSpinZ J`.
- `AKLT.W.H1M036.main`:
  `AKLT.Blueprint.H1.SpinCommutatorStatement`.

## Proof route

The scaled 2×2 Pauli matrices are checked directly against the three local commutator identities. For token lifts, same-token multiplication reduces to multiplication of the local matrices; distinct-token lifts commute because the off-token coordinate conditions determine the intermediate tensor index uniquely. Expanding the finite sums cancels the distinct-token terms, leaving the local commutators on each token. The resulting matrix identities are transported through `Matrix.toEuclideanLin` and applied to the arbitrary vector.

## Axioms

`#print axioms` output for each exported theorem (`endZP`, `endZM`, `endPM`, and `main`):

```text
[propext, Classical.choice, Quot.sound]
```

These are the allowed axioms listed in the brief.

## Build

Command: `lake build AKLT.W.H1M036.Main`

- Initial module compilation: `AKLT.W.H1M036.Proof` 7.8 s; `AKLT.W.H1M036.Main` 5.6 s.
- Final build after adding the axiom printouts: successful; `Proof` replayed and `Main` built in 3.9 s.

The final build emitted only benign Lean style warnings about deprecated `if_pos` / `if_neg` rewrite names and one redundant `change` tactic in the helper proof. There are no open proof obligations.

## ORCH-SUMMARY

- Delivered `Main.lean` with exact theorem `AKLT.W.H1M036.main : AKLT.Blueprint.H1.SpinCommutatorStatement` and helper module `Proof.lean`.
- The three single-token commutators are proved from the explicit Pauli matrices; distinct-token terms commute and cancel in the finite double sums.
- All exported theorem axiom outputs are `[propext, Classical.choice, Quot.sound]`.
- `lake build AKLT.W.H1M036.Main` succeeds.
- No deviations from the requested theorem or proof scope; no open issues beyond benign style warnings.
