STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_Q030/AKLT/W/Q030/Main.lean:56): the required closed theorem `AKLT.W.Q030.main`, with exactly the requested type.
- [Coordinates.lean](/home/ubuntu/aklt/wt/LW_Q030/AKLT/W/Q030/Coordinates.lean): an invertible binomial coordinate change and its intertwining identities for the frozen spin matrices.
- [Blocks.lean](/home/ubuntu/aklt/wt/LW_Q030/AKLT/W/Q030/Blocks.lean): the integer Casimir, nine weight parameters, and exact eigenvector construction and reconstruction.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_Q030/AKLT/W/Q030/Audit.lean): an exact-type example and axiom checks for all 20 exported theorems and both linear equivalences.
- [build.log](/home/ubuntu/aklt/reports/LW/Q030/build.log) and [audit.log](/home/ubuntu/aklt/reports/LW/Q030/audit.log): successful final validation output and timings.

The previous partial `Main.lean` has been replaced. Its residual declarations are no longer needed. The historical `report.luna.md` is preserved. All Lean source changes are confined to `AKLT/W/Q030/`.

## Proof

Multiply coordinate `(i,j)` by `sqrt(choose 4 i) * sqrt(choose 4 j)`. These factors are nonzero, so this defines a complex linear equivalence. The proved library lemmas `AKLT.Uniq.plus_normalization` and `AKLT.Uniq.minus_normalization` remove all radicals from the conjugated spin operators. Exact finite expansion then identifies the Casimir with `blockCasimir`.

The resulting integer operator preserves `i+j`, giving blocks of sizes `1,2,3,4,5,4,3,2,1`. For arbitrary `c : Fin 9 → ℂ`, the vector with entries

```text
choose(4,i) * choose(4,j) * c(i+j)
```

has eigenvalue 20. Conversely, explicit rational linear combinations of the first `n-1` eigenvector equations in every block of size `n` reconstruct all its coordinates from its first coordinate. The two constructions prove a linear equivalence

```lean
Module.End.eigenspace pairCasimir (20 : ℂ) ≃ₗ[ℂ] (Fin 9 → ℂ)
```

and therefore finrank nine. This establishes the dimension of the eigenspace itself. No eigenvalue multiplicity argument, numerical solver, residual assumption, or other blueprint leaf is used.

## Exported declarations and statements

All names below are in namespace `AKLT.W.Q030`; the displayed signatures use the same open namespaces as their source files. Definition bodies and theorem proofs are omitted here.

### Coordinates.lean

```lean
abbrev PairCoordinates := Fin 5 × Fin 5 → ℂ

def pairScale (p : Fin 5 × Fin 5) : ℂ

theorem pairScale_ne_zero (p : Fin 5 × Fin 5) : pairScale p ≠ 0

def coordinates : PairHilbert ≃ₗ[ℂ] PairCoordinates

theorem pairAt_zero_apply (A : Matrix (Fin 5) (Fin 5) ℂ)
    (v : PairHilbert) (i j : Fin 5) :
    pairAt A 0 v (i, j) = ∑ k : Fin 5, A i k * v (k, j)

theorem pairAt_one_apply (A : Matrix (Fin 5) (Fin 5) ℂ)
    (v : PairHilbert) (i j : Fin 5) :
    pairAt A 1 v (i, j) = ∑ k : Fin 5, A j k * v (i, k)

def integerPlus (i k : Fin 5) : ℂ

def integerMinus (i k : Fin 5) : ℂ

def coordZ (v : PairCoordinates) (p : Fin 5 × Fin 5) : ℂ

def coordPlus (v : PairCoordinates) (p : Fin 5 × Fin 5) : ℂ

def coordMinus (v : PairCoordinates) (p : Fin 5 × Fin 5) : ℂ

theorem scale_spinZ (i k : Fin 5) :
    AKLT.Uniq.singleScale i * spinZ i k =
      spinZ i k * AKLT.Uniq.singleScale k

theorem scale_spinPlus (i k : Fin 5) :
    AKLT.Uniq.singleScale i * spinPlus i k =
      integerPlus i k * AKLT.Uniq.singleScale k

theorem scale_spinMinus (i k : Fin 5) :
    AKLT.Uniq.singleScale i * spinMinus i k =
      integerMinus i k * AKLT.Uniq.singleScale k

theorem coordinates_pairAt_zero
    (A B : Matrix (Fin 5) (Fin 5) ℂ)
    (h : ∀ i k, AKLT.Uniq.singleScale i * A i k =
      B i k * AKLT.Uniq.singleScale k)
    (v : PairHilbert) (i j : Fin 5) :
    coordinates (pairAt A 0 v) (i, j) =
      ∑ k : Fin 5, B i k * coordinates v (k, j)

theorem coordinates_pairAt_one
    (A B : Matrix (Fin 5) (Fin 5) ℂ)
    (h : ∀ i k, AKLT.Uniq.singleScale i * A i k =
      B i k * AKLT.Uniq.singleScale k)
    (v : PairHilbert) (i j : Fin 5) :
    coordinates (pairAt A 1 v) (i, j) =
      ∑ k : Fin 5, B j k * coordinates v (i, k)

theorem coordinates_Z (v : PairHilbert) :
    coordinates ((pairAt spinZ 0 + pairAt spinZ 1) v) = coordZ (coordinates v)

theorem coordinates_plus (v : PairHilbert) :
    coordinates ((pairAt spinPlus 0 + pairAt spinPlus 1) v) =
      coordPlus (coordinates v)

theorem coordinates_minus (v : PairHilbert) :
    coordinates ((pairAt spinMinus 0 + pairAt spinMinus 1) v) =
      coordMinus (coordinates v)

def coordCasimir (v : PairCoordinates) : PairCoordinates

theorem coordinates_casimir (v : PairHilbert) :
    coordinates (pairCasimir v) = coordCasimir (coordinates v)
```

### Blocks.lean

```lean
def blockCasimir (v : PairCoordinates) : PairCoordinates

theorem coordCasimir_eq (v : PairCoordinates) : coordCasimir v = blockCasimir v

def parameters : PairCoordinates →ₗ[ℂ] (Fin 9 → ℂ)

def totalWeight (p : Fin 5 × Fin 5) : Fin 9

def topCoordinates : (Fin 9 → ℂ) →ₗ[ℂ] PairCoordinates

theorem parameters_topCoordinates (c : Fin 9 → ℂ) :
    parameters (topCoordinates c) = c

theorem blockCasimir_topCoordinates (c : Fin 9 → ℂ) :
    blockCasimir (topCoordinates c) = (20 : ℂ) • topCoordinates c

theorem reconstruct_eigenvector (v : PairCoordinates)
    (h : blockCasimir v = (20 : ℂ) • v) :
    topCoordinates (parameters v) = v
```

### Main.lean

```lean
theorem eigen_coordinates_iff (v : PairHilbert) :
    v ∈ Module.End.eigenspace pairCasimir (20 : ℂ) ↔
      blockCasimir (coordinates v) = (20 : ℂ) • coordinates v

def eigenspaceParameters :
    Module.End.eigenspace pairCasimir (20 : ℂ) →ₗ[ℂ] (Fin 9 → ℂ)

theorem eigenspaceParameters_injective : Function.Injective eigenspaceParameters

theorem eigenspaceParameters_surjective : Function.Surjective eigenspaceParameters

def eigenspaceEquiv :
    Module.End.eigenspace pairCasimir (20 : ℂ) ≃ₗ[ℂ] (Fin 9 → ℂ)

theorem main : AKLT.Blueprint.Q.PairTopDimensionStatement
```

## Axiom audit

The following is the output of `Audit.lean`, including the exact exported type. Every audited declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.

```text
AKLT.W.Q030.main : AKLT.Blueprint.Q.PairTopDimensionStatement
'AKLT.W.Q030.pairScale_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.pairAt_zero_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.pairAt_one_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.scale_spinZ' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.scale_spinPlus' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.scale_spinMinus' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.coordinates_pairAt_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.coordinates_pairAt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.coordinates_Z' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.coordinates_plus' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.coordinates_minus' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.coordinates_casimir' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.coordCasimir_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.parameters_topCoordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.blockCasimir_topCoordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.reconstruct_eigenvector' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.eigen_coordinates_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.eigenspaceParameters_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.eigenspaceParameters_surjective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.coordinates' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q030.eigenspaceEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Builds and checks

- `lake build AKLT.W.Q030.Coordinates` succeeded; module compilation took 5.4 seconds.
- Final `lake build AKLT.W.Q030.Main` succeeded without warnings: 67.92 seconds wall time, including 55 seconds for `Blocks` and 5.9 seconds for `Main`.
- `lake env lean AKLT/W/Q030/Audit.lean` succeeded: 5.68 seconds wall time. Its `example : AKLT.Blueprint.Q.PairTopDimensionStatement := AKLT.W.Q030.main` passed.
- A source scan found none of the prohibited proof placeholders, axioms, kernel bypasses, or execution mechanisms. The finite Casimir expansion uses a bounded `maxHeartbeats 1600000` and `maxRecDepth 3000`.
- `git status --short` reports only the task directory as untracked; no existing source outside the task directory was changed.

## Open issues

None. The requested statement is proved without additional hypotheses.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT.W.Q030.main : AKLT.Blueprint.Q.PairTopDimensionStatement` in `AKLT/W/Q030/Main.lean`.
- Helpers: `Coordinates.lean` and `Blocks.lean`; validation: `Audit.lean`.
- Proved an equivalence from the eigenvalue-20 eigenspace to `Fin 9 → ℂ`.
- Exact integer weight-block algebra; all nine blocks have one free parameter.
- Reuses proved scalar normalization lemmas from `AKLT.Uniq.SpinCoordinates`.
- No other blueprint leaf or transparent residual is assumed.
- All 20 exported theorem axiom checks contain only the three permitted axioms.
- Required build and exact-type audit succeeded; logs and timings are included.
- Open names: none. Limitations or deviations: none.
- No orchestrator decision is required.
