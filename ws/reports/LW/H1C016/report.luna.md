STATUS: PARTIAL

Files:

- `/home/ubuntu/aklt/wt/LW_H1C016/AKLT/W/H1C016/Main.lean`
- `/home/ubuntu/aklt/reports/LW/H1C016/report.md`

The requested unconditional declaration `AKLT.W.H1C016.main : AKLT.Cert.H1.Production.Leaves.sectorCoefficientBound` is not delivered. The compiled file proves the target from three explicit residual propositions and proves basic Gaussian L1 lemmas. The target statement is not asserted as an unconditional theorem.

Exported declarations:

- `gaussianL1 (z : Gaussian) : Nat := z.re.natAbs + z.im.natAbs`.
- `gaussianL1_add_le (a b : Gaussian) : gaussianL1 (a.add b) ≤ gaussianL1 a + gaussianL1 b`.
- `gaussianL1_scale (n : Int) (a : Gaussian) : gaussianL1 (a.scale n) = n.natAbs * gaussianL1 a`.
- `gaussianL1_sumGaussian_le (xs : List Gaussian) : gaussianL1 (sumGaussian xs) ≤ (xs.map gaussianL1).sum`.
- `Residual_sectorRingL1`: the checked local table shapes and sector-network check bound each un-packed closed ring coefficient by the product of sector table absolute sums.
- `Residual_centerCounts`: accepted input geometry gives at most three center pairs and at most one pair avoiding the outgoing site.
- `Residual_thresholdAssembly`: given the ring estimate, center counts, sector-network check, and parameters check, every direct threshold coefficient has L1 norm below `2^(width-1)`.
- `main_of_residuals (hRing : Residual_sectorRingL1) (hCenters : Residual_centerCounts) (hThreshold : Residual_thresholdAssembly) : AKLT.Cert.H1.Production.Leaves.sectorCoefficientBound`.

`#print axioms` output:

```text
gaussianL1_add_le: [propext, Quot.sound]
gaussianL1_scale: [propext]
gaussianL1_sumGaussian_le: [propext, Quot.sound]
main_of_residuals: [propext, Classical.choice, Quot.sound]
```

These are within the campaign's allowed axiom set.

Build: `lake build AKLT.W.H1C016.Main` succeeded. Total command time was about 10 seconds; Lean reported 4.9 seconds for the module. Existing dependency warnings were replayed. No tests were added or run.

Open issues:

- Prove `Residual_sectorRingL1`: control the L1 norm of each closed four-state contraction by the product of the local table absolute sums.
- Prove `Residual_centerCounts`: derive the center-pair bounds from `inputCheck`, `geometryCheck`, and the outgoing-site equation.
- Prove `Residual_thresholdAssembly`: combine the ring bound and center counts through Gaussian addition/scaling and extract the strict coefficient threshold from `parametersCheck`.
- Then replace `main_of_residuals` with the requested unconditional `AKLT.W.H1C016.main`.

ORCH-SUMMARY

- Delivered a compiled `Main.lean` with Gaussian L1 lemmas and `main_of_residuals`.
- The requested unconditional theorem is open.
- Open residuals: `Residual_sectorRingL1`, `Residual_centerCounts`, `Residual_thresholdAssembly`.
- No source files outside `AKLT/W/H1C016/` were changed; report is at the requested report path.
- Orchestrator must decide whether to continue proving the three residuals or route this leaf back as partial.
