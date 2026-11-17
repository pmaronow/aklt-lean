STATUS: PROVED

## Files changed (worktree /home/ubuntu/aklt/wt/LW_H1C021)

- NEW `AKLT/W/H1C021/Dictionary.lean` (498 lines): proves `AKLT.W.H1C021.monomialCongruence : Residual_monomialCongruence`, the one residual left by the earlier attempts.
- EDITED `AKLT/W/H1C021/Main.lean`: added `import AKLT.W.H1C021.Dictionary` and the theorem `main`. Removed the two `#print axioms` lines at the end of the file.
- No other files changed. `git status` shows only `AKLT/W/H1C021/` as untracked. All 10 `.lean` files in the directory (Basic, Basis, Congruence, Dictionary, Expansion, Linearity, Main, Monomials, Radix, Rational) are imported transitively by `Main.lean`.

## Final theorem (as it compiles)

```lean
theorem AKLT.W.H1C021.main : AKLT.Cert.H1.Production.Leaves.tensorSubstitution :=
  main_of_monomialCongruence monomialCongruence
```

It has no hypotheses. A scratch check `example : AKLT.Cert.H1.Production.Leaves.tensorSubstitution := AKLT.W.H1C021.main` passes.

## #print axioms (scratch file /tmp/h1c021opus/ax.lean, run with `lake env lean`)

```
'AKLT.W.H1C021.main' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C021.monomialCongruence' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Build

`cd /home/ubuntu/aklt/wt/LW_H1C021 && lake build AKLT.W.H1C021.Main` reports "Build completed successfully (8991 jobs)": Dictionary took 9.7 s, Main 15 s, about 30 s wall time in total. There are no errors and no new warnings; the only warning in the H1C021 files is an old linter note in Radix.lean. The log is in /home/ubuntu/aklt/reports/LW/H1C021/build.opus.log.

Forbidden-term scan of AKLT/W/H1C021/*.lean: none of sorry, admit, axiom, native_decide, implemented_by, unsafe, opaque, extern, #eval, IO, run_cmd, initialize or macro_rules appears. The only heartbeat setting is the existing `maxHeartbeats 800000` in Basis.lean. The con-ron/NanoDa independent checks (bin/conron-check.sh) were not run, because that script writes temporary files at the worktree root.

## How the residual is closed (Dictionary.lean)

The residual says that for pure monomials (one color list per ring group), the real part of the form product equals the rational sector entry. The proof has these steps:

1. **Ring geometry.** `groupSite : Plane → Nat` inverts `groupPoint` on the eight template points. Lemmas:
   - `groupSite_groupPoint`, `groupPoint_mem_template` and `groupSite_spec` say it is a bijection between `range 8` and `templateCorners ∪ templateTips`.
   - `ringLeader_groupSite` gives `ringLeader (groupSite x) = groupLeader x`.
   - `groupSecond_val` gives `groupSecond x = groupLeader x + 1`, because every leader is at most 17.

   These are 8-case `decide` steps on small literals only. No operator, Fintype enumeration or large object is unfolded.

2. **Reindexing.**
   - `prod_sites_eq_prod_groups`: a product over the eight sites that is 1 off the reduction groups equals the product over `reductionGroups π`. It uses `Finset.prod_subset` and `Finset.prod_nbij'`.
   - `prod_tokens_eq_prod_groups`: a product over the tokens equals the product over groups and their slots, via `groupSlotEquiv`.
   - `formProduct_range` and `monomialProduct_range`: the list recursions written as products over `List.range`.

3. **The Pauli label.** `colourLabel π r css : reductionVectors π r → Fin 4` reads each token's color from its group's list, through `groupSlotEquiv.symm`. `colourLabel_token` evaluates it on `groupSlotToken x k`.

4. **Polynomial side.** `pauliExponent_eq_sum` and `pauliMonomial_eq_prod` show that `monomial (pauliExponent J d) 1` is the product of the token factors (`1` or `vectorVariable`). `vectorMonomial_group` matches each group's factor with `vectorMonomial`, for both singles and pairs. Together these give `monomialProduct 0 css = monomial (pauliExponent J (colourLabel π r css)) 1`.

5. **Form side.** `localForm_group` shows that each group's `gaussianValue (localForm …)` equals the local congruence sum produced by `rationalSectorEntry_pauliMonomial`:
   - singles use `pauliZ_value`;
   - pairs use `pairForm_value`, with `pairCoeff (groupDigit …)` shown equal to `localVector` (`pairCoeff_localVector`). This includes the exterior case, where the digit is 3.
   - The sums over the dependent slot types are handled by `slot_sum_one`/`slot_sum_two` and `slot_prod_one`/`slot_prod_two`. These are stated for a general `N` with `hN : N = 1` or `N = 2`, which avoids rewriting inside `GroupSlot`.

6. **Assembly.** `monomialCongruence` rewrites the monomial (step 4), applies the existing `rationalSectorEntry_pauliMonomial`, and matches the eight-site form product with the group product (steps 2 and 5).

The residual as stated was true, and no restatement was needed. No remaining residuals.
