STATUS: PROVED

## Files

- [Coordinates.lean](/home/ubuntu/aklt/wt/LW_Q029/AKLT/W/Q029/Coordinates.lean): Weighted diagonal vectors and tensor-coordinate formulas; reuses the useful part of the earlier attempt.
- [Diagonal.lean](/home/ubuntu/aklt/wt/LW_Q029/AKLT/W/Q029/Diagonal.lean): Polynomial expansion in the nine weighted coefficient functionals and the kernel-complement span inclusion.
- [Ladder.lean](/home/ubuntu/aklt/wt/LW_Q029/AKLT/W/Q029/Ladder.lean): Finite raising/lowering calculations with the square-root binomial coefficients and boundary values.
- [Eigenvectors.lean](/home/ubuntu/aklt/wt/LW_Q029/AKLT/W/Q029/Eigenvectors.lean): Combines the spin-component actions into the eigenvalue-20 calculation for each vector.
- [Main.lean](/home/ubuntu/aklt/wt/LW_Q029/AKLT/W/Q029/Main.lean): Exports the exact closed theorem and prints axioms for every public theorem.

## Result and proof

The required declaration is proved without residual hypotheses:

```lean
theorem AKLT.W.Q029.main : AKLT.Blueprint.Q.PairTopInclusionStatement
```

Its unfolded conclusion is
`(LinearMap.ker pairDiagonal)ᗮ ≤ Module.End.eigenspace pairCasimir 20`.

Let `v_m = diagonalAdjointVector m`. Its `(j,k)` coordinate is
`√(choose 4 j) * √(choose 4 k)` when `j+k=m`, and zero otherwise.
The polynomial diagonal is the sum of the monomials `X₀^(8-m) X₁^m`
with coefficients `inner ℂ v_m ψ`. Therefore the orthogonal complement
of the span of these nine vectors lies in `ker pairDiagonal`.
Taking orthogonal complements proves `pairTopSpan` using finite-dimensional
orthogonal projection; no separate rank or dimension leaf is used.

The finite spin-matrix calculations establish
`Z v_m = (4-m) • v_m`, `U v_(m+1) = (8-m) • v_m`, and
`D v_m = (m+1) • v_(m+1)`, together with `U v_0 = 0` and `v_9 = 0`.
Substitution in `Z² + (UD+DU)/2` gives eigenvalue 20 for all nine vectors.
The eigenspace is a submodule, so it contains their span and hence the
kernel complement.

The two earlier residuals are fully discharged by `pairTopSpan` and
`diagonalAdjointVector_eigen`; their definitions and the conditional version
of `main` are no longer present.

## Exported declarations and statements

All names below are in namespace `AKLT.W.Q029`. The auxiliary definitions
are `Pair := PairHilbert`, `binomRoot`, `diagonalAdjointVector`, `pairZ`,
`pairU`, `pairD`, and `diagonalMonomial`, with the meanings described above.
The complete public theorem statements follow.

### Coordinates.lean

```lean
theorem pairAt_left_apply (A : Matrix (Fin 5) (Fin 5) ℂ) (v : Pair) (p : Fin 5 × Fin 5) :
    ((pairAt A 0 v).ofLp) p = ∑ i : Fin 5, A p.1 i * v (i,p.2)

lemma pairAt_right_apply (A : Matrix (Fin 5) (Fin 5) ℂ) (v : Pair) (p : Fin 5 × Fin 5) :
    ((pairAt A 1 v).ofLp) p = ∑ i : Fin 5, A p.2 i * v (p.1,i)

lemma sum_filter_left (j k : Fin 5) (m : ℕ) (f : Fin 5 → ℂ) :
    (∑ i : Fin 5, if i.val + k.val = m then if j = i then f i else 0 else 0) =
      if j.val + k.val = m then f j else 0

lemma sum_filter_right (j k : Fin 5) (m : ℕ) (f : Fin 5 → ℂ) :
    (∑ i : Fin 5, if j.val + i.val = m then if k = i then f i else 0 else 0) =
      if j.val + k.val = m then f k else 0

lemma pairZ_on_diag (m : Fin 9) : pairZ (diagonalAdjointVector m.val) =
    ((4 : ℂ) - (m.val : ℂ)) • diagonalAdjointVector m.val
```

### Diagonal.lean

```lean
theorem inner_diagonalAdjointVector (m : ℕ) (v : Pair) :
    inner ℂ (diagonalAdjointVector m) v =
      ∑ j : Fin 5, ∑ k : Fin 5,
        if j.val + k.val = m then v (j, k) * binomRoot j * binomRoot k else 0

theorem pairDiagonal_terms (v : Pair) : pairDiagonal v =
    ∑ j : Fin 5, ∑ k : Fin 5,
      MvPolynomial.C (v (j, k) * binomRoot j * binomRoot k) *
        diagonalMonomial (j.val + k.val)

theorem pairDiagonal_expansion (v : Pair) : pairDiagonal v =
    ∑ m : Fin 9, MvPolynomial.C (inner ℂ (diagonalAdjointVector m.val) v) *
      diagonalMonomial m.val

theorem pairTopSpan :
    (LinearMap.ker pairDiagonal)ᗮ ≤
      Submodule.span ℂ (Set.range (fun m : Fin 9 => diagonalAdjointVector m.val))
```

### Ladder.lean

```lean
theorem pairU_zero : pairU (diagonalAdjointVector 0) = 0

theorem pairU_succ (m : Fin 8) : pairU (diagonalAdjointVector (m.val + 1)) =
    ((8 - m.val : ℕ) : ℂ) • diagonalAdjointVector m.val

theorem pairD_on_diag (m : Fin 9) : pairD (diagonalAdjointVector m.val) =
    ((m.val + 1 : ℕ) : ℂ) • diagonalAdjointVector (m.val + 1)

theorem diagonalAdjointVector_nine : diagonalAdjointVector 9 = 0
```

### Eigenvectors.lean

```lean
theorem pairU_on_diag_nat (m : ℕ) (hm : m < 9) :
    pairU (diagonalAdjointVector m) =
      if m = 0 then 0 else ((9 - m : ℕ) : ℂ) • diagonalAdjointVector (m - 1)

theorem pairD_on_diag_nat (m : ℕ) (hm : m < 9) :
    pairD (diagonalAdjointVector m) =
      ((m + 1 : ℕ) : ℂ) • diagonalAdjointVector (m + 1)

theorem pairZ_on_diag_nat (m : ℕ) (hm : m < 9) :
    pairZ (diagonalAdjointVector m) =
      ((4 : ℂ) - (m : ℂ)) • diagonalAdjointVector m

theorem diagonalAdjointVector_eigen (m : Fin 9) :
    diagonalAdjointVector m.val ∈ Module.End.eigenspace pairCasimir 20
```

### Main.lean

```lean
theorem main : AKLT.Blueprint.Q.PairTopInclusionStatement
```

## Axiom audit

`Main.lean` runs `#print axioms` on all 18 public theorems. Output:

```text
'AKLT.W.Q029.pairAt_left_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.pairAt_right_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.sum_filter_left' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.sum_filter_right' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.pairZ_on_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.inner_diagonalAdjointVector' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.pairDiagonal_terms' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.pairDiagonal_expansion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.pairTopSpan' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.pairU_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.pairU_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.pairD_on_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.diagonalAdjointVector_nine' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.pairU_on_diag_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.pairD_on_diag_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.pairZ_on_diag_nat' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.diagonalAdjointVector_eigen' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.Q029.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All reported axioms are permitted: `propext`, `Classical.choice`, and
`Quot.sound`. No forbidden proof escapes or unproved assumptions occur in
the delivered files.

## Validation and timings

All commands used `PATH="$HOME/.elan/bin:$PATH"`.

- `lake build AKLT.W.Q029.Main` — passed; wall time **12.57 s** with the coordinate, diagonal, and ladder helpers already compiled. This run compiled `Eigenvectors` (4.5 s) and `Main` (3.4 s). Full output: [build.log](build.log); timing: [build.time](build.time).
- Earlier successful helper compilations reported: `Coordinates` 3.5 s, `Diagonal` 4.1 s, `Ladder` 91 s. The finite calculations have explicit, finite heartbeat limits.
- `lake env lean /tmp/AKLT_Q029_ExactType.lean` — passed; wall time **3.57 s**. The check contains the exact assignment below and prints the theorem and its axioms. Full output: [exact-type.log](exact-type.log); timing: [exact-type.time](exact-type.time).

```lean
import AKLT.W.Q029.Main
example : AKLT.Blueprint.Q.PairTopInclusionStatement := AKLT.W.Q029.main
#print AKLT.W.Q029.main
#print axioms AKLT.W.Q029.main
```

The printed declaration is closed and has exactly the requested name and
type. Source audit found none of the forbidden constructs. Only files
under `AKLT/W/Q029/` were changed or added in the worktree; the frozen
statement and existing libraries were untouched. No sub-agents were used.

## Open issues

None.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT/W/Q029/Main.lean` and four helper modules in the same directory.
- Exact export: `AKLT.W.Q029.main : AKLT.Blueprint.Q.PairTopInclusionStatement`.
- The square-root binomial weights are preserved throughout.
- Earlier residuals are discharged; `main` has no hypotheses.
- No other blueprint leaf or extra premise is used.
- Final target build and separate exact-type check both passed.
- All 18 public theorems use only `propext`, `Classical.choice`, `Quot.sound`.
- Open declarations: none. Limitations or deviations: none.
- Orchestrator action: accept the completed leaf and integrate these five modules.
