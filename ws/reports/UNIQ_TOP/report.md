STATUS: PROVED FROM DEPS

## Files

- [TorusKernel.lean](/home/ubuntu/aklt/wt/UNIQ_TOP/AKLT/W/UNIQ_TOP/TorusKernel.lean) proves the Top interface theorem, using `AKLT.Uniq.uniqueness` for nonvanishing and the exact Hamiltonian kernel.

## Exported declaration

- `AKLT.W.UNIQ_TOP.torusKernel : AKLT.Blueprint.Top.TorusKernelStatement`
- Expanded statement, for every `L N : AKLT.Challenge.Size`: every bond has two sites; `bondSites` is injective; every site has exactly four distinct torus neighbours and is not its own neighbour; `B L N ≠ 0`; `LinearMap.ker (H L N) = Submodule.span ℂ {B L N}`; and for every Boolean edge orientation choice `ε`, `Submodule.span ℂ {reorientedB L N ε} = Submodule.span ℂ {B L N}`.

The proof uses the proved torus size/injectivity lemmas and establishes the four-neighbour facts directly, including periods three. For the final conjunct it proves `reorientedB` is a nonzero scalar multiple of `B`, with scalar the product of the edge signs.

## Axiom audit

`#print axioms AKLT.W.UNIQ_TOP.torusKernel`:

```text
[propext, Classical.choice, Quot.sound]
```

These are the permitted Lean axioms. The theorem has no `sorryAx` dependency.

## Build

Command:

```text
PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.UNIQ_TOP.TorusKernel
```

Final build succeeded in 10.690 s wall time; the target module compiled in 3.7 s. Lake reported 8964 dependency jobs, with existing modules replayed and the target module built. The target's `#print axioms` output is included above.

## Open issues

None for `TorusKernelStatement`. The theorem module is built directly; no root aggregator or other namespace was edited, consistent with the assigned write scope.

## ORCH-SUMMARY

- Delivered `AKLT.W.UNIQ_TOP.torusKernel` in `AKLT/W/UNIQ_TOP/TorusKernel.lean`.
- The full Top torus-kernel interface is proved from `AKLT.Uniq.uniqueness` plus local geometry and orientation-sign arguments.
- Axiom audit: `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- Build: `lake build AKLT.W.UNIQ_TOP.TorusKernel` succeeded (10.690 s total; 3.7 s target compile).
- No open proof obligations. Root aggregator wiring was outside the assigned write scope and was not changed.
