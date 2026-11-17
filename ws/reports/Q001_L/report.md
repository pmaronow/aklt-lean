STATUS: PROVED

## Files

- [OrthogonalFamilyStatement.lean](/home/ubuntu/aklt/wt/Q001_L/AKLT/W/Q001_L/OrthogonalFamilyStatement.lean)
- This report: `/home/ubuntu/aklt/reports/Q001_L/report.md`

## Exported declaration

`AKLT.W.Q001_L.OrthogonalFamilyStatement_holds` proves
`AKLT.Blueprint.Q.OrthogonalFamilyStatement`:

```lean
∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 →
  ∀ v : IcoLetter → Vec3, Function.Injective v →
    (∀ a, normSq (v a) = 1) → (∀ a, ∃ b, v b = -v a) →
      Function.Injective (fun a => R.mulVec (v a)) ∧
      (∀ a, normSq (R.mulVec (v a)) = 1) ∧
      ∀ a, ∃ b, R.mulVec (v b) = -R.mulVec (v a)
```

The proof uses `R.transpose * R = 1` as a left inverse to transfer injectivity, applies the matrix dot product identity to preserve squared norm, and maps the given antipodal witness through `R.mulVec_neg`.

## Axioms

`#print axioms AKLT.W.Q001_L.OrthogonalFamilyStatement_holds`:

```text
'AKLT.W.Q001_L.OrthogonalFamilyStatement_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.Blueprint.Q.NodesFrames` — succeeded in 7.1 s.
- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.Q001_L.OrthogonalFamilyStatement` — succeeded in 11.0 s; Lean reported the theorem's axiom list above.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.Q001_L.OrthogonalFamilyStatement_holds` in the assigned directory.
- The theorem proves the frozen target from its stated hypotheses.
- Build succeeded; only permitted foundational axioms are reported.
- No existing files were modified; no campaign-rule deviations or open issues.
