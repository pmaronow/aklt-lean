STATUS: PROVED

`AKLT.W.H1C020.main : AKLT.Cert.H1.Production.Leaves.momentPolynomial` is proved with exactly this name and type and no hypotheses. Both residuals that Sol left open, `Residual_ringFubini` and `Residual_centerContraction`, are now theorems in their original form. Neither was restated.

## Final theorem (as it compiles)

```lean
theorem main : AKLT.Cert.H1.Production.Leaves.momentPolynomial :=
  main_of_residuals ringFubini_holds centerContraction_holds
```

`main_of_residuals` is Sol's earlier conditional composition under a new name. The two new theorems are:

- `AKLT.W.H1C020.ringFubini_holds : AKLT.W.H1C020.Residual_ringFubini`
- `AKLT.W.H1C020.centerContraction_holds : AKLT.W.H1C020.Residual_centerContraction`

## Axioms

I ran a scratch file outside the worktree and deleted it afterwards. It contained `theorem exactType : AKLT.Cert.H1.Production.Leaves.momentPolynomial := AKLT.W.H1C020.main` and `#print axioms`. The exact-type check passed and the output was:

```
'AKLT.W.H1C020.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.ringFubini_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.centerContraction_holds' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.H1C020.main : AKLT.Cert.H1.Production.Leaves.momentPolynomial
```

## Build

`cd /home/ubuntu/aklt/wt/LW_H1C020 && lake build AKLT.W.H1C020.Main` finished with `Build completed successfully (8994 jobs).` The log is `/home/ubuntu/aklt/reports/LW/H1C020/build.opus.log`. When modules change, each new module takes about 3–18 s to build. Only warnings remain, such as deprecated `if_pos`/`if_neg` and unused simp arguments.

## Files

All files are under `AKLT/W/H1C020/`. No file outside that directory was edited. Every `.lean` file in the directory is imported, directly or transitively, by `Main.lean`.

- **Changed:**
  - `Main.lean` now proves the closed `main`, and `main_of_residuals` is the old conditional composition. I removed the `#print axioms` that was in `Main.lean`.
- **New:**
  - `Contract.lean`: generic facts about `contractSpins`.
    - Variable support (`VarsIn`, which implies `InternallySupported`), list linearity, and pulling out `C a`.
    - A spin monomial times a renamed vector polynomial contracts to its moment weight times that polynomial.
    - Enlarging the contracted set by sites without variables changes nothing; status congruence; the diluted flag gives the same moments.
  - `Chain.lean`: the uncontracted transfer `openL`/`closedL`, built with the same recursion as `openTransfer`.
    - `contract_openL`: contracting the ring sites one at a time (finite Fubini, using Sol's `contractSpins_disjoint_mul`) turns it into `openTransfer`.
    - `closedL_factor`: if each local tensor factors as left edge times site times right edge, the trace is the site factors times the bond sums.
  - `Site.lean`: the uncontracted local tensor `gLoc = Lf * (Cf * Gf) * Rf`.
    - `contract_gLoc`: contracting its single internal spin gives exactly `rationalLocal`, in every branch (leaf, tip and absent-bond branches included).
  - `RingGeom.lean`: template geometry.
    - Which ring sites are retained.
    - Every bond at a corner is one of its two ring bonds, and every bond at a tip goes to its axial site.
    - The leaf neighbour of a tip; a replaced corner has exactly one of its two ring bonds, and its leaf neighbour is the other end of that bond.
  - `Split.lean`: `reducedIntegrand_split`, the identity `reducedIntegrand π r next = ringPart π r * centerPart π r next`.
    - `bonds_prod`: a product over `π.bonds` equals the product over the 16 fixed `templateEdges`, each present or not. Its proof uses `Finset.prod_bij_ne_one`, `H1C031.internalBond_templateEdge` and `internalBonds_no_reverse`, and the edge midpoints are distinct.
    - The group factors are reindexed by the 8 ring positions.
  - `CenterExp.lean`: `center_expand`, the integral of the passage spin against at most three passage bonds.
    - The first and third moments vanish, and the second moment is `δ_kl` times `1/3` (U) or `1/5` (D).
  - `Bonds.lean`: `SiteFlags`, read off `NetworkGeometry`, plus two identities.
    - The centre factor `Cf` equals `ringCoordinate`.
    - The group-slot factor `Gf` equals the group factor; for a tip it carries the radius 3/5 and for a pair corner both slots.
  - `BondId.lean`:
    - `bond_identity`: each bond sum is the ring bond times the leaf factor that bond carries (radius 1/2 or 1/3, at the leaf's unique neighbour).
    - `corner_identity`: around a corner, the two bonds and its slot factor give its group factor exactly once.
  - `RingFubini.lean`:
    - `closedL_eq`: the uncontracted transfer equals `ringPart * insertion codes`.
    - `ringIntegrand_eq`: `eraseCenterHom` fixes the ring part, through `MvPolynomial.hom_congr_vars`, and sends the passage part to 1.
    - Variable-support lemmas.
  - `ResidualRing.lean`: `ringFubini_holds`.
  - `ResidualCenter.lean`: `centerContraction_holds`.
    - Coveredness removes the south passage bond.
    - `centerPairs` is evaluated from the three axial centre flags.
    - The pair insertions are matched with the expansion, including the exclusion of `out` in next mode.
- **Unchanged from Sol:**
  - Audit, Fubini, Geometry, GroupTokens, Inversion, Local, Normalization, Reduction, Transfer.

## Dependencies

The proof imports helper lemmas from three leaves that are already proved and merged:

- `AKLT.W.H1M023.Geometry`: `bond_info`, `leaf_bond`, `group_single`, `group_pair_retained`, `group_single_neighbour_retained`, `positive_degree_active` and `pattern_tip_degree_bound`.
- `AKLT.W.H1C031.Geometry`: `mem_internalBonds_iff`, `mem_templateSites_iff`, `internalBond_templateEdge`, `internalBonds_no_reverse`, `templateSite_cases` and `presentBond_symm`.
- `AKLT.W.H1M006.Geometry`: `mem_active_iff` and `covered_incident_subset`.

No unproved blueprint leaf is used.

## Rule compliance

A source scan of the directory finds no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `unsafe`, `opaque`, `#eval`, IO, `run_cmd`, `initialize` or `macro_rules`. The only `maxHeartbeats` settings are Sol's existing bounded ones.

On the independent-checker rule:

- My files use `rfl` only on very small literals: `colorChoices 1`/`2`, which have 4 and 16 short lists, `templateEdges.length`, individual entries of `templateEdges`, and `Fin 3` coordinates of `vectorVariable`.
- `decide` appears only for single facts of the size of `0 < 1` and `U ≠ X`.
- I replaced a kernel `decide` (distinct midpoints of the 16 template edges) with `simp`/`norm_num`.
- Template case analysis is done with `interval_cases`, `omega` and `simp`.
- Some imported helper lemmas from H1M023 and H1C031 (not the specific ones listed above) use `decide +kernel` on the template inside the leaves that already passed review.

I did not run any independent con-ron or NanoDa checks.
