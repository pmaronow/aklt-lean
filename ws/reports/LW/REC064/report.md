STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_REC064/AKLT/W/REC064/Main.lean)
- Report: `/home/ubuntu/aklt/reports/LW/REC064/report.md`

## Exported declarations

- `AKLT.W.REC064.main : AKLT.Blueprint.Rec.KernelRegroupStatement`
- `AKLT.W.REC064.latticeDist_triangle (x y z : Plane) : latticeDist x z ≤ latticeDist x y + latticeDist y z`
- `AKLT.W.REC064.latticeDist_symm (x y : Plane) : latticeDist x y = latticeDist y x`
- `AKLT.W.REC064.wordVertex_succ {n} (u : Plane) (w : DirectionWord n) (i : Fin n) : wordVertex u w (i.val + 1) = wordVertex u w i.val + (w i).step`
- `AKLT.W.REC064.neighbours_dist_one {x z : Plane} (hz : z ∈ neighbours x) : latticeDist z x = 1`
- `AKLT.W.REC064.wordVertex_latticeDist_start_le {n} (u : Plane) (w : DirectionWord n) (j : ℕ) : latticeDist u (wordVertex u w j) ≤ j`
- `AKLT.W.REC064.responsePair_shift_le {n} (X : PairType) (w : DirectionWord n) (i : Fin n) (p : Finset Plane) (hp : p ∈ responsePairs w i) : pairShift X p ≤ n + 1`
- `AKLT.W.REC064.exposureSum_zero_of_reward_zero {n} (w : DirectionWord n) (reward : Fin n → ℚ) (l : List (Fin n)) (h : ∀ i, reward i = 0) : exposureSum w reward l = 0`
- `AKLT.W.REC064.responseKappa_zero_of_shift_gt {n} (X Y : PairType) (s : ℕ) (w : DirectionWord n) (i : Fin n) (hs : n + 1 < s) : responseKappa X Y s w i = 0`
- `AKLT.W.REC064.kernelLengthCoefficient_zero_of_shift_gt (X Y : PairType) (s n : ℕ) (hs : n + 1 < s) : kernelLengthCoefficient X Y s n = 0`
- `AKLT.W.REC064.kernelLengthCoefficient_zero_at_zero (X Y : PairType) (s : ℕ) : kernelLengthCoefficient X Y s 0 = 0`

The helpers establish the geometric support cutoff. The main proof distributes each shift weight through its ENNReal length sum, exchanges the nonnegative sums with `ENNReal.tsum_comm`, then replaces each inner shift `tsum` by the finite range `0,…,n+1` using the support lemma. The positivity premise on `θ` is accepted as stated; no real-valued divergent `tsum` is used.

## Axiom checks

The file runs `#print axioms` on every exported theorem. The reported dependencies are:

- `main`, `wordVertex_succ`, `neighbours_dist_one`, `wordVertex_latticeDist_start_le`, `responsePair_shift_le`, `exposureSum_zero_of_reward_zero`, `responseKappa_zero_of_shift_gt`, `kernelLengthCoefficient_zero_of_shift_gt`, and `kernelLengthCoefficient_zero_at_zero`: `[propext, Classical.choice, Quot.sound]`.
- `latticeDist_triangle` and `latticeDist_symm`: `[propext, Quot.sound]`.

## Build

- `lake build AKLT.W.REC064.Main` — passed.
- Lake reported module build time 6.3 s; command wall time was 11.4 s.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT.W.REC064.main` at the exact requested type.
- Proved the response-site distance bound `pairShift ≤ n+1` directly from the path definitions.
- Regrouped the nonnegative ENNReal series with `ENNReal.tsum_comm` and finite support.
- Checked axioms on every exported theorem; only `propext`, `Classical.choice`, `Quot.sound` occur.
- Build passed with `lake build AKLT.W.REC064.Main`.
- No residual statements, deviations, or open issues.
