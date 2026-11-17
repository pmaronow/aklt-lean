STATUS: PROVED

Delivered the exact closed theorem:

```lean
theorem AKLT.W.WIN064.main : AKLT.Blueprint.Win.ComplementQuadratureStatement
```

## Files

- `AKLT/W/WIN064/Main.lean`: the requested theorem and the two partition-sum evaluation identities.
- `AKLT/W/WIN064/Geometry.lean`: the reused incidence argument, with simplifier cleanup.
- `AKLT/W/WIN064/Polynomial.lean`: the actual complementary partition polynomial, its separate degree bound, and evaluation identities.
- `AKLT/W/WIN064/Quadrature.lean`: tensorization of the supplied actual frame moment identities.
- Report artifacts: `ExactTypeCheck.lean`, `validation.log`, and `validation-timing.json` in this report directory.

## Proof

The polynomial has coordinates indexed by the retained sites `G \ Y`. It includes every internal bond of that set and exactly the original legs of `G` whose tails survive. Pins are fixed real coefficients. No leg into a removed site is introduced.

At each retained site, internal bonds and original exterior legs inject into disjoint subsets of the four physical neighbor directions. This bounds the sum of the coordinate exponents by four. Evaluation of the polynomial gives precisely the frame and reference partition integrands, including the uniform site weights.

Expanding into monomials factors each product quadrature into one-site monomial sums. `ThreeFramesStatement` supplies equality of those sums through degree four. This directly proves the needed tensor transfer, including the empty site set. Consequently the supplied `ExactStatement` hypothesis is not needed by the proof, but the exported theorem retains exactly the frozen statement's type.

No other blueprint leaf is imported or used as a theorem, and no residual assumptions remain.

## Exported declarations and statements

Independent `#check` output for every public definition, abbreviation, and theorem:

```text
AKLT.W.WIN064.ComplementPoly (D : Finset AKLT.Defs.Plane) : Type
AKLT.W.WIN064.coordinatePolynomial (D : Finset AKLT.Defs.Plane) (z : AKLT.Defs.Plane) (i : Fin 3) :
  AKLT.W.WIN064.ComplementPoly D
AKLT.W.WIN064.bondPolynomial (D : Finset AKLT.Defs.Plane) (e : AKLT.Defs.Plane × AKLT.Defs.Plane) :
  AKLT.W.WIN064.ComplementPoly D
AKLT.W.WIN064.originalPinPolynomial (G D : Finset AKLT.Defs.Plane) (τ : AKLT.Defs.PinAssignment G)
  (e : ↥(AKLT.Defs.originalLegs G)) : AKLT.W.WIN064.ComplementPoly D
AKLT.W.WIN064.complementPolynomial (G Y : Finset AKLT.Defs.Plane) (τ : AKLT.Defs.PinAssignment G) :
  AKLT.W.WIN064.ComplementPoly (G \ Y)
AKLT.W.WIN064.extendVectors {D : Finset AKLT.Defs.Plane} (a : ↥D → AKLT.Defs.Vec3) (z : AKLT.Defs.Plane) :
  AKLT.Defs.Vec3
AKLT.W.WIN064.quadrature.{u_1} {ι : Type u_1} [Fintype ι] (v : ι → AKLT.Defs.IcoLetter → AKLT.Defs.Vec3)
  (p : MvPolynomial (ι × Fin 3) ℝ) : ℝ
AKLT.W.WIN064.incidence_bound (G D : Finset AKLT.Defs.Plane) (hDG : D ⊆ G) (z : AKLT.Defs.Plane) (hz : z ∈ D) :
  {e ∈ AKLT.Defs.internalBonds D | e.1 = z ∨ e.2 = z}.card + {e ∈ AKLT.Defs.originalLegs G | e.1 = z}.card ≤ 4
AKLT.W.WIN064.quadrature_expand.{u_1} {ι : Type u_1} [Fintype ι] (v : ι → AKLT.Defs.IcoLetter → AKLT.Defs.Vec3)
  (p : MvPolynomial (ι × Fin 3) ℝ) :
  AKLT.W.WIN064.quadrature v p = ∑ m ∈ p.support, p.coeff m * ∏ x, 1 / 12 * ∑ a, ∏ i, v x a i ^ m (x, i)
AKLT.W.WIN064.frame_monomial (hThree : AKLT.Blueprint.Top.ThreeFramesStatement) (j : Fin 3) (m : Fin 3 → ℕ)
  (hm : ∑ i, m i ≤ 4) :
  1 / 12 * ∑ a, ∏ i, AKLT.Defs.frameVector j a i ^ m i = 1 / 12 * ∑ a, ∏ i, AKLT.Defs.icoVector a i ^ m i
AKLT.W.WIN064.frame_quadrature.{u_1} {ι : Type u_1} [Fintype ι] (hThree : AKLT.Blueprint.Top.ThreeFramesStatement)
  (κ : ι → Fin 3) (p : MvPolynomial (ι × Fin 3) ℝ) (hp : AKLT.Defs.SeparateDegreeFour p) :
  AKLT.W.WIN064.quadrature (fun x => AKLT.Defs.frameVector (κ x)) p =
    AKLT.W.WIN064.quadrature (fun x => AKLT.Defs.icoVector) p
AKLT.W.WIN064.complementPolynomial_degree (G Y : Finset AKLT.Defs.Plane) (τ : AKLT.Defs.PinAssignment G) :
  AKLT.Defs.SeparateDegreeFour (AKLT.W.WIN064.complementPolynomial G Y τ)
AKLT.W.WIN064.eval_coordinatePolynomial (D : Finset AKLT.Defs.Plane) (a : ↥D → AKLT.Defs.Vec3) (z : AKLT.Defs.Plane)
  (i : Fin 3) :
  (MvPolynomial.eval fun v => a v.1 v.2) (AKLT.W.WIN064.coordinatePolynomial D z i) = AKLT.W.WIN064.extendVectors a z i
AKLT.W.WIN064.eval_bondPolynomial (D : Finset AKLT.Defs.Plane) (a : ↥D → AKLT.Defs.Vec3)
  (e : AKLT.Defs.Plane × AKLT.Defs.Plane) :
  (MvPolynomial.eval fun v => a v.1 v.2) (AKLT.W.WIN064.bondPolynomial D e) =
    1 + AKLT.Defs.dot (AKLT.W.WIN064.extendVectors a e.1) (AKLT.W.WIN064.extendVectors a e.2)
AKLT.W.WIN064.eval_originalPinPolynomial (G D : Finset AKLT.Defs.Plane) (τ : AKLT.Defs.PinAssignment G)
  (a : ↥D → AKLT.Defs.Vec3) (e : ↥(AKLT.Defs.originalLegs G)) :
  (MvPolynomial.eval fun v => a v.1 v.2) (AKLT.W.WIN064.originalPinPolynomial G D τ e) =
    if (↑e).1 ∈ D then 1 + AKLT.Defs.dot (↑(τ e)) (AKLT.W.WIN064.extendVectors a (↑e).1) else 1
AKLT.W.WIN064.eval_complementPolynomial (G Y : Finset AKLT.Defs.Plane) (τ : AKLT.Defs.PinAssignment G)
  (a : ↥(G \ Y) → AKLT.Defs.Vec3) :
  (MvPolynomial.eval fun v => a v.1 v.2) (AKLT.W.WIN064.complementPolynomial G Y τ) =
    (∏ e ∈ AKLT.Defs.internalBonds (G \ Y),
        (1 + AKLT.Defs.dot (AKLT.W.WIN064.extendVectors a e.1) (AKLT.W.WIN064.extendVectors a e.2))) *
      ∏ e, if (↑e).1 ∈ G \ Y then 1 + AKLT.Defs.dot (↑(τ e)) (AKLT.W.WIN064.extendVectors a (↑e).1) else 1
AKLT.W.WIN064.framePinnedSum_eq_quadrature (κ : AKLT.Defs.Plane → Fin 3) (G Y : Finset AKLT.Defs.Plane)
  (τ : AKLT.Defs.PinAssignment G) :
  AKLT.Blueprint.Win.framePinnedSum κ G Y τ =
    AKLT.W.WIN064.quadrature (fun x => AKLT.Defs.frameVector (κ ↑x)) (AKLT.W.WIN064.complementPolynomial G Y τ)
AKLT.W.WIN064.pinnedSum_eq_quadrature (G Y : Finset AKLT.Defs.Plane) (τ : AKLT.Defs.PinAssignment G) :
  (AKLT.Defs.pinnedSum G Y τ fun x => 1) =
    AKLT.W.WIN064.quadrature (fun x => AKLT.Defs.icoVector) (AKLT.W.WIN064.complementPolynomial G Y τ)
AKLT.W.WIN064.main : AKLT.Blueprint.Win.ComplementQuadratureStatement
```

## Axiom audit

Independent `#print axioms` output for every exported theorem:

```text
'AKLT.W.WIN064.incidence_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN064.quadrature_expand' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN064.frame_monomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN064.frame_quadrature' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN064.complementPolynomial_degree' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN064.eval_coordinatePolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN064.eval_bondPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN064.eval_originalPinPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN064.eval_complementPolynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN064.framePinnedSum_eq_quadrature' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN064.pinnedSum_eq_quadrature' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.WIN064.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

All axioms are allowed: `propext`, `Classical.choice`, and `Quot.sound`.

## Validation

- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.WIN064.Main` — passed. Lake reported **7.4 seconds** for the final compilation of `Main`; all three local helper modules compiled successfully as well. The final build emitted no warnings.
- `PATH="$HOME/.elan/bin:$PATH" lake env lean /home/ubuntu/aklt/reports/LW/WIN064/ExactTypeCheck.lean` — passed, exit code 0, **11.167 seconds** wall time. This independently imports `Main` and checks `example : AKLT.Blueprint.Win.ComplementQuadratureStatement := AKLT.W.WIN064.main`.
- Source scan of all four delivered Lean files found none of the forbidden proof or execution constructs.
- All Lean source changes are confined to `AKLT/W/WIN064/`. The frozen statement and existing files elsewhere were not changed.

## Open issues

None. The requested theorem is present, compiled, and independently checked at its exact type.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT.W.WIN064.main : AKLT.Blueprint.Win.ComplementQuadratureStatement`.
- Main module: `AKLT.W.WIN064.Main`; three helpers are in the same task directory.
- Reused the earlier incidence proof and discharged the polynomial and quadrature work.
- Open leaves or residual statements: none.
- External proved-leaf dependencies: none.
- Axioms of every exported theorem: propext, Classical.choice, Quot.sound.
- Build and independent exact-type check pass; final build has no warnings.
- Route deviation: tensor transfer is proved directly from ThreeFramesStatement; ExactStatement is redundant.
- Mathematical limitations: none.
- Orchestrator action: accept and index WIN064 under the exact theorem and module above.
