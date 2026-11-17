STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C031/AKLT/W/H1C031/Main.lean)

No existing project files were changed. The requested exact declaration
`AKLT.W.H1C031.main : AKLT.Cert.H1.Production.Leaves.effectiveCodeClassification`
is not delivered.

## Delivered declarations

- `encodeDigits_lt_of_digits`: digits bounded by `base` give
  `encodeDigits base xs < base ^ xs.length`.
- `encodeDigits_inj_fixed`: for equal-length lists whose digits are below the
  base, equality of `encodeDigits` implies list equality.
- `statusDigit_getD` and `edgeDigit_getD`: read a decoded list at a valid
  template index as its named status or present-bond bit.
- `orientedCode_formula`: expands `reflectedPatternCode` into its status,
  edge, and outgoing components.
- `orientedCode_eq_digits`: equality of two oriented codes implies equality
  of all three components, including the fixed-width status and edge lists.
- `outgoing_of_orientedDigits`: for covered patterns, equal outgoing digits
  give equal outgoing directions when the flags agree, and horizontally
  reflected directions when they differ.
- `main_from_residuals`: proves the requested classification conditionally
  from `Residual_sameTemplateRecovery` and
  `Residual_crossTemplateRecovery`.

The residuals are closed propositions. The same-orientation residual asks
that equal oriented digit lists recover equal canonical bond finsets and
statuses at every positive-degree site. The cross-orientation residual asks
that such lists recover reflected undirected bond support and reflected
statuses at positive-degree sites. The cross residual preserves the brief's
allowance for arbitrary isolated-site statuses. Neither residual is proved.

## Axioms

`#print axioms` for every exported theorem in `Main.lean`, including
`encodeDigits_inj_fixed`, `orientedCode_eq_digits`,
`outgoing_of_orientedDigits`, and `main_from_residuals`, reported:

```text
[propext, Classical.choice, Quot.sound]
```

These are the standard allowed axioms. No `sorry`, `admit`, or custom axiom is
used.

## Build

Command:

```sh
PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1C031.Main
```

Result: passed. The measured wall time was 12.05 seconds including Lake's
dependency replay; the target module reported 6.7 seconds. Lean emitted only
non-fatal simp/linter warnings in the new file and pre-existing dependency
warnings.

## Open issues

- Prove `Residual_sameTemplateRecovery` from coveredness and the decoded lists.
- Prove `Residual_crossTemplateRecovery`, including recovery of canonical
  undirected template bonds under reflection.
- Then export the exact required declaration
  `AKLT.W.H1C031.main : AKLT.Cert.H1.Production.Leaves.effectiveCodeClassification`.

## ORCH-SUMMARY

- Delivered a compiled fixed-width code decoder and the min/reflection case
  reduction in `AKLT/W/H1C031/Main.lean`.
- `main_from_residuals` proves the leaf from two explicit closed residuals.
- Open: `Residual_sameTemplateRecovery` and
  `Residual_crossTemplateRecovery`.
- The exact requested `AKLT.W.H1C031.main` declaration is not present.
- Build passed with only linter warnings; no existing files were modified.
- Orchestrator decision: continue the finite template recovery proof or treat
  this as a partial submission.
