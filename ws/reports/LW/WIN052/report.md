STATUS: PROVED

## Files

All Lean changes are confined to `AKLT/W/WIN052/`.

- `Main.lean`: the requested closed theorem and partition-sum reindexing.
- `Geometry.lean`: original-leg exclusion and the disjoint bond factorization.
- `Moments.lean`: linearity and contractions of the first four moment tensors.
- `Polynomial.lean`: the removal polynomial for every subset of the four neighbours.
- `Fiber.lean`: configuration equivalence, unchanged surviving spins, weight factorization, and the one-site sum identity.
- `Audit.lean`: exact-type ascription and axiom checks for all 31 exported theorems.

## Result

```lean
theorem AKLT.W.WIN052.main : AKLT.Blueprint.Win.RemovalIntegralStatement
```

This has exactly the requested name and type, with no residual parameter. Its only mathematical input is `MomentsStatement`, already an explicit hypothesis inside the frozen statement. No other blueprint leaf is assumed.

The proof reuses the earlier configuration equivalence and final finite-sum reindexing. It closes the missing calculation as follows. The original depth bound puts every neighbour of the removed site inside the original volume, so no original pin leg is attached to that site. Internal bonds split into the surviving bonds and exactly one bond for each surviving neighbour. Their weights factor, including the removed site's factor of `1/12`, while every original leg at other sites retains its weight. Summation over the removed spin then kills the odd terms, contracts pairs with coefficient `1/3`, and contracts the four-factor term with coefficient `1/15`. Sixteen finite neighbour-subset cases identify this expression with the frozen `pairSum` and `quartic` definitions. Summing the resulting fibre identity over the surviving configurations proves the statement for both pin choices.

## Exported declarations and statements

The following declarations are in namespace `AKLT.W.WIN052`, with `AKLT.Defs` and `AKLT.Blueprint.Win` open and `BigOperators` scoped. The private bookkeeping theorem in `Main.lean` is omitted.

### Geometry.lean

```lean
theorem dot_symm (a b : Vec3) : dot a b = dot b a

theorem neighbours_explicit (x : Plane) :
    neighbours x = {x + Compass.east.step, x + Compass.north.step,
      x + Compass.west.step, x + Compass.south.step}

theorem neighbour_ne (x : Plane) : x ∉ neighbours x

theorem neighbour_dist {x z : Plane} (hz : z ∈ neighbours x) : latticeDist x z = 1

theorem neighbours_in_volume {G : Finset Plane} {x : Plane}
    (hdepth : 3 ≤ boundaryDepth G x) : neighbours x ⊆ G

theorem leg_source_ne {G : Finset Plane} {x : Plane}
    (hdepth : 3 ≤ boundaryDepth G x) (e : originalLegs G) : e.val.1 ≠ x

theorem mem_bonds {D : Finset Plane} {a b : Plane} :
    (a, b) ∈ internalBonds D ↔ a ∈ D ∧ b ∈ D ∧ b ∈ positiveNeighbours a

theorem neighbour_orientation (x z : Plane) :
    z ∈ neighbours x ↔ z ∈ positiveNeighbours x ∨ x ∈ positiveNeighbours z

theorem orientation_exclusive (x z : Plane) :
    z ∈ positiveNeighbours x → x ∉ positiveNeighbours z

def edgeAt (x z : Plane) : Plane × Plane

theorem edgeAt_injective (x : Plane) : Function.Injective (edgeAt x)

theorem edgeAt_bond {E : Finset Plane} {x z : Plane}
    (hz : z ∈ neighbours x ∩ E) : edgeAt x z ∈ internalBonds (insert x E)

theorem bonds_insert {E : Finset Plane} {x : Plane} (_hx : x ∉ E) :
    internalBonds (insert x E) =
      internalBonds E ∪ (neighbours x ∩ E).image (edgeAt x)

theorem bonds_insert_disjoint {E : Finset Plane} {x : Plane} (hx : x ∉ E) :
    Disjoint (internalBonds E) ((neighbours x ∩ E).image (edgeAt x))

theorem bondProduct_insert {E : Finset Plane} {x : Plane} (hx : x ∉ E)
    (n : Plane → Vec3) :
    (∏ e ∈ internalBonds (insert x E), (1 + dot (n e.1) (n e.2))) =
      (∏ e ∈ internalBonds E, (1 + dot (n e.1) (n e.2))) *
      ∏ z ∈ neighbours x ∩ E, (1 + dot (n x) (n z))
```

### Moments.lean

```lean
theorem moment_sum {ι : Type} [Fintype ι] (f : ι → Vec3 → ℝ) :
    moment (fun v => ∑ i, f i v) = ∑ i, moment (f i)

theorem moment_scale (c : ℝ) (f : Vec3 → ℝ) :
    moment (fun v => c * f v) = c * moment f

theorem moment_add (f g : Vec3 → ℝ) :
    moment (fun v => f v + g v) = moment f + moment g

theorem moment_const (hM : AKLT.Blueprint.Top.MomentsStatement) (c : ℝ) :
    moment (fun _ => c) = c

theorem moment_dot (hM : AKLT.Blueprint.Top.MomentsStatement) (a : Vec3) :
    moment (fun v => dot v a) = 0

theorem pairMoment_of_moments (hM : AKLT.Blueprint.Top.MomentsStatement)
    (a b : Vec3) : moment (fun v => dot v a * dot v b) = (1 / 3 : ℝ) * dot a b

theorem tripleMoment (hM : AKLT.Blueprint.Top.MomentsStatement) (a b c : Vec3) :
    moment (fun v => dot v a * dot v b * dot v c) = 0

theorem fourthMoment (hM : AKLT.Blueprint.Top.MomentsStatement) (a b c d : Vec3) :
    moment (fun v => dot v a * dot v b * dot v c * dot v d) =
      (dot a b * dot c d + dot a c * dot b d + dot a d * dot b c) / 15

theorem fourFactors (hM : AKLT.Blueprint.Top.MomentsStatement) (a b c d : Vec3) :
    moment (fun v => (1 + dot v a) * (1 + dot v b) * (1 + dot v c) *
      (1 + dot v d)) =
    1 + (dot a b + dot a c + dot a d + dot b c + dot b d + dot c d) / 3 +
      (dot a b * dot c d + dot a c * dot b d + dot a d * dot b c) / 15

@[simp] theorem dot_zero (a : Vec3) : dot a 0 = 0

@[simp] theorem zero_dot (a : Vec3) : dot 0 a = 0
```

### Polynomial.lean

```lean
theorem neighbour_moment (hM : AKLT.Blueprint.Top.MomentsStatement)
    (x : Plane) (V : Finset Plane) (hV : V ⊆ neighbours x) (n : Plane → Vec3) :
    moment (fun v => ∏ z ∈ V, (1 + dot v (n z))) = removalPolynomial x V n
```

### Fiber.lean

```lean
def removalConfigEquiv (G Y : Finset Plane) (x : Plane)
    (hx : x ∈ G \ Y) :
    PlaneConfiguration (G \ Y) ≃
      PlaneConfiguration (G \ insert x Y) × IcoLetter

theorem spins_removed (G Y : Finset Plane) (x : Plane) (hx : x ∈ G \ Y)
    (r : PlaneConfiguration (G \ insert x Y)) (a : IcoLetter) :
    extendIcoSpins ((removalConfigEquiv G Y x hx).symm (r, a)) x = icoVector a

theorem spins_retained (G Y : Finset Plane) (x : Plane) (hx : x ∈ G \ Y)
    (r : PlaneConfiguration (G \ insert x Y)) (a : IcoLetter)
    (z : Plane) (hzx : z ≠ x) :
    extendIcoSpins ((removalConfigEquiv G Y x hx).symm (r, a)) z =
      extendIcoSpins r z

theorem weight_factor (G Y : Finset Plane) (τ : PinAssignment G) (x : Plane)
    (hstep : RemovalStep G Y x) (pinned : Bool)
    (r : PlaneConfiguration (G \ insert x Y)) (a : IcoLetter) :
    partWeight pinned G Y τ ((removalConfigEquiv G Y x hstep.2.1).symm (r, a)) =
      partWeight pinned G (insert x Y) τ r *
        ((1 / 12 : ℝ) * ∏ z ∈ survivors G Y x,
          (1 + dot (icoVector a) (extendIcoSpins r z)))

theorem siteFiber (hM : AKLT.Blueprint.Top.MomentsStatement)
    (G Y : Finset Plane) (τ : PinAssignment G) (x : Plane)
    (hstep : RemovalStep G Y x) (pinned : Bool)
    (r : PlaneConfiguration (G \ insert x Y)) :
    (∑ a : IcoLetter,
      partWeight pinned G Y τ ((removalConfigEquiv G Y x hstep.2.1).symm (r, a))) =
      partWeight pinned G (insert x Y) τ r *
        removalPolynomial x (survivors G Y x) (extendIcoSpins r)
```

### Main.lean

```lean
theorem main :
    AKLT.Blueprint.Win.RemovalIntegralStatement
```

## Axiom audit

`Audit.lean` first checks the exact ascription:

```text
AKLT.W.WIN052.main : AKLT.Blueprint.Win.RemovalIntegralStatement
```

Actual `#print axioms` output for every exported theorem follows. The full successful build output is also preserved in `audit.log`.

```text
AKLT/W/WIN052/Audit.lean:5:0: 'AKLT.W.WIN052.dot_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:6:0: 'AKLT.W.WIN052.neighbours_explicit' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:7:0: 'AKLT.W.WIN052.neighbour_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:8:0: 'AKLT.W.WIN052.neighbour_dist' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:9:0: 'AKLT.W.WIN052.neighbours_in_volume' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:10:0: 'AKLT.W.WIN052.leg_source_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:11:0: 'AKLT.W.WIN052.mem_bonds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:12:0: 'AKLT.W.WIN052.neighbour_orientation' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:13:0: 'AKLT.W.WIN052.orientation_exclusive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:14:0: 'AKLT.W.WIN052.edgeAt_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:15:0: 'AKLT.W.WIN052.edgeAt_bond' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:16:0: 'AKLT.W.WIN052.bonds_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:17:0: 'AKLT.W.WIN052.bonds_insert_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:18:0: 'AKLT.W.WIN052.bondProduct_insert' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:19:0: 'AKLT.W.WIN052.moment_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:20:0: 'AKLT.W.WIN052.moment_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:21:0: 'AKLT.W.WIN052.moment_add' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:22:0: 'AKLT.W.WIN052.moment_const' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:23:0: 'AKLT.W.WIN052.moment_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:24:0: 'AKLT.W.WIN052.pairMoment_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:25:0: 'AKLT.W.WIN052.tripleMoment' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:26:0: 'AKLT.W.WIN052.fourthMoment' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:27:0: 'AKLT.W.WIN052.fourFactors' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:28:0: 'AKLT.W.WIN052.dot_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:29:0: 'AKLT.W.WIN052.zero_dot' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:30:0: 'AKLT.W.WIN052.neighbour_moment' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:31:0: 'AKLT.W.WIN052.spins_removed' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:32:0: 'AKLT.W.WIN052.spins_retained' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:33:0: 'AKLT.W.WIN052.weight_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:34:0: 'AKLT.W.WIN052.siteFiber' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT/W/WIN052/Audit.lean:35:0: 'AKLT.W.WIN052.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Builds and timings

Successful commands, run from `/home/ubuntu/aklt/wt/LW_WIN052` with the prebuilt project dependencies:

```sh
PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -p lake build AKLT.W.WIN052.Main
PATH="$HOME/.elan/bin:$PATH" /usr/bin/time -p lake build AKLT.W.WIN052.Audit
```

- Main build: exit 0; 15.19 seconds elapsed. This incremental build compiled `Fiber.lean` in 3.5 seconds and `Main.lean` in 4.8 seconds; the geometry, moments, and polynomial helpers had already been compiled successfully.
- Audit build: exit 0; 8.58 seconds elapsed, including 3.6 seconds compiling the audit. It confirmed the exact type and that all exported theorem axioms are limited to `[propext, Classical.choice, Quot.sound]`.
- No placeholders, extra hypotheses, nonstandard axioms, or forbidden proof mechanisms remain.

## Open issues

None. The earlier `Residual_siteFiber` declaration and conditional `main` have been replaced by the proved `siteFiber` helper and the closed `main` theorem. No files outside the assigned Lean directory were changed in the worktree.

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT/W/WIN052/Main.lean` and five helper/audit modules in the same directory.
- Exact export: `AKLT.W.WIN052.main : AKLT.Blueprint.Win.RemovalIntegralStatement`.
- The earlier site-fibre residual is fully discharged; no residual declarations remain.
- Both the requested module build and the exact-type/axiom audit build pass.
- All 31 exported theorems use only propext, Classical.choice, and Quot.sound.
- Other blueprint leaves are not used as proof inputs.
- Open names: none. Limitations or deviations: none.
- Orchestrator action: accept the closed leaf proof and import `AKLT.W.WIN052.Main`.
