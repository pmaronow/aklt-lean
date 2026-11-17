STATUS: PROVED FROM DEPS

The requested theorem is proved with exactly its closed name and type:

```lean
theorem AKLT.W.H1C006.main :
    AKLT.Cert.H1.Production.TopLeaves.sectorPositiveImpliesBound
```

There are no residual assumptions. The earlier conditional entry point and both remaining residual definitions have been removed. The proof reuses the leaf modules listed in the supplied proved index, including `AKLT.W.H1C002.main : AKLT.Cert.H1.Production.TopLeaves.thresholdScale`.

Files:

| File | Contents |
| --- | --- |
| [Main.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Main.lean) | Exact requested theorem and axiom checks for every local exported theorem. |
| [Dependencies.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Dependencies.lean) | Assemblies from proved moment and H1 mathematical leaves, including common positive-factor reconstruction and repaired real interfaces. |
| [Central.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Central.lean) | Central-weight span identification and positivity of the ambient form from the sector matrix. |
| [Exchange.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Exchange.lean) | Tensor-coordinate exchange identities and common sign eigenvectors for commuting involutions. |
| [Coordinates.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Coordinates.lean) | New canonical coordinate representatives for single, symmetric-pair, and exterior-pair basis elements. |
| [Completeness.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Completeness.lean) | New proof that the explicit sector tensors span the prescribed joint exchange eigenspace. |
| [Supported.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Supported.lean) | Unconditional sector invariance and full-space positive semidefiniteness, allowing zero eigenvalues outside U support. |
| [Scaling.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/Scaling.lean) | Positive congruence scaling and transport from indexed integer matrices. |
| [RealBridge.lean](/home/ubuntu/aklt/wt/LW_H1C006/AKLT/W/H1C006/RealBridge.lean) | Rational-to-real embedding and application of repaired inversion/product-density positivity. |

All nine local Lean files are transitively imported by `Main.lean`. No source file outside `AKLT/W/H1C006/` was edited. The prior report remains in `report.luna.md`.

The 64 exported theorem signatures, with their exact statements and source files, are recorded in [declarations.lean.txt](/home/ubuntu/aklt/reports/LW/H1C006/declarations.lean.txt). In particular, the new completeness result is:

```lean
theorem AKLT.W.H1C006.exchange_complete
    (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (ψ : TensorSpace (reductionVectors π r))
    (hψ : ExchangeEigenvectors π r ε ψ) :
    ψ ∈ exchangeSpace π r ε
```

The supported positivity result has no completeness premise:

```lean
theorem AKLT.W.H1C006.posSemidef_of_supported_sectors
    (π : PatternData) (r : Representation)
    (M : Matrix (reductionVectors π r → Fin 2)
      (reductionVectors π r → Fin 2) ℂ)
    (hHerm : M.IsHermitian)
    (hPair : PairStructure π r (Matrix.toEuclideanLin M))
    (hPositive : ∀ ε : ExchangeSigns π,
      PositiveOn (exchangeSpace π r ε) (Matrix.toEuclideanLin M)) :
    M.PosSemidef
```

Proof:

1. Transport positive definiteness through the supplied indexing equivalences, then use the proved exact entry identity and the positive factor `15 * D₀ * q` to obtain positive central complex sector matrices.
2. Identify the central subspace with the span of its explicit central-weight vectors. Their matrix is precisely the ambient Hermitian form on those vectors. The proved spin-sector ladder chain promotes central positivity to positivity on each exchange sector.
3. Prove exchange completeness directly. Canonical configurations distinguish the explicit sector tensors. The exchange equations determine every other coordinate; equal spins at an exterior pair force a zero coordinate. Interpolation at the canonical configurations therefore reconstructs every vector with the prescribed exchange signs in the sector span.
4. A putative negative eigenvalue is nonzero. Commuting exchanges give a common sign eigenvector; U support forces its U signs to be positive, and completeness places it in a supported exchange sector. Sector positivity contradicts the negative eigenvalue. This establishes positive semidefiniteness on the full tensor space without requiring strict positivity on discarded U directions.
5. Embed the rational polynomial into the repaired real-scope inversion interface. Product-density positivity gives nonnegativity throughout the supported product of closed balls. Common reconstruction supplies the same positive factor and vector assignment for current and next, yielding the original pattern inequality at exactly `(p : ℝ) / q`.

Every imported leaf module was checked against the supplied index: all 79 are present. Their module list is [proved-dependencies.txt](/home/ubuntu/aklt/reports/LW/H1C006/proved-dependencies.txt). The main mathematical assemblies use the proved moment leaves, H1 reduction and reconstruction leaves, operator-structure leaves, repaired real Pauli/inversion leaves, and ladder-sector leaves. Positive scaling is proved locally from the now-proved `thresholdScale` leaf; the separate `H1C003` lemma is not required.

Axioms:

```text
#print axioms AKLT.W.H1C006.main
'AKLT.W.H1C006.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All 64 exported local theorems were checked with `#print axioms`; each reports exactly `[propext, Classical.choice, Quot.sound]`. Full output is in [axioms.txt](/home/ubuntu/aklt/reports/LW/H1C006/axioms.txt) and [build.log](/home/ubuntu/aklt/reports/LW/H1C006/build.log). Source audit found no forbidden proof construct or unproved placeholder.

Validation:

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build AKLT.W.H1C006.Main
# Build completed successfully (9108 jobs).
# 42.62 seconds elapsed; Main compiled in 5.0 seconds.
```

The build also compiled `Completeness.lean` in 6.7 seconds and the revised `Supported.lean` in 24 seconds. `Coordinates.lean` previously compiled in 6.6 seconds. Only local modules and missing proved-leaf artifacts were built; Mathlib was reused.

An additional import check verified the exact target with no arguments:

```lean
import AKLT.W.H1C006.Main
example : AKLT.Cert.H1.Production.TopLeaves.sectorPositiveImpliesBound :=
  AKLT.W.H1C006.main
#check AKLT.W.H1C006.main
#print axioms AKLT.W.H1C006.main
```

`lake env lean /tmp/H1C006-check.lean` passed in 4.78 seconds. The output is in [typecheck.log](/home/ubuntu/aklt/reports/LW/H1C006/typecheck.log).

Open issues: none for this statement. Validation used Lean's kernel; downstream con-ron/NanoDa checks have not been run here. No sub-agents were used.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1C006/Main.lean` and eight transitively imported local helper files.
- `AKLT.W.H1C006.main` has exactly the requested closed statement and no residual parameters.
- Status is PROVED FROM DEPS; all 79 imported leaf modules occur in the supplied proved index.
- Reused `AKLT.W.H1C002.main` for exact threshold scaling and proved positive scaling locally.
- Proved the remaining exchange-space completeness obligation here.
- The proof establishes full-space PSD and permits the discarded U-sector kernel.
- Uses the repaired real-scope inversion/product-density interfaces.
- All 64 exported theorem axiom checks report only `propext`, `Classical.choice`, `Quot.sound`.
- Required build passed in 42.62 seconds; exact-type import check passed in 4.78 seconds.
- Open mathematical leaves or residuals: none.
- No source edits outside the assigned directory; all local Lean files are imported by Main.
- No sub-agents, forbidden constructs, or new assumptions were used.
- Remaining downstream action: independent-kernel validation and integration of this proved leaf.
