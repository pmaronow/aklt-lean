STATUS: PARTIAL

## Files

- AKLT/W/WIN052/Main.lean

## Declarations

- AKLT.W.WIN052.pairMoment_of_moments (hM : AKLT.Blueprint.Top.MomentsStatement) (a b : Vec3) : moment (fun v => dot v a * dot v b) = (1 / 3 : ℝ) * dot a b
- AKLT.W.WIN052.Residual_siteFiber : Prop: for every removal instance and every fixed configuration off the removed site, summing the old partWeight over the removed site's IcoLetter gives the after-removal partWeight times removalPolynomial.
- AKLT.W.WIN052.main (hResidual : Residual_siteFiber) : AKLT.Blueprint.Win.RemovalIntegralStatement

main is conditional on the residual and therefore does **not** have the requested unconditional type. The fixed-rest fiber statement is smaller than the original statement because it handles one configuration of all surviving sites at a time; summing those identities is handled in main.

## Axioms

Output of #print axioms:

    'AKLT.W.WIN052.pairMoment_of_moments' depends on axioms: [propext, Classical.choice, Quot.sound]
    'AKLT.W.WIN052.main' depends on axioms: [propext, Classical.choice, Quot.sound]

The second theorem's listed axioms do not discharge Residual_siteFiber; it remains an explicit theorem parameter.

## Build

- Command: PATH="$HOME/.elan/bin:$PATH" time lake build AKLT.W.WIN052.Main
- Result: successful.
- Elapsed time: 8.33 seconds (Lean module reported 3.7 seconds).

## Open issue

Prove AKLT.W.WIN052.Residual_siteFiber. This is the uncompleted local network calculation: establish that the removed site has no original pin leg, factor the incident bond terms, then use the first through fourth moment tensors to obtain the pair and quartic terms. The current file proves the pair contraction and the configuration reindexing, but does not establish this fiber identity or the requested unconditional leaf.

## ORCH-SUMMARY

- Delivered AKLT/W/WIN052/Main.lean and this report.
- pairMoment_of_moments is proved.
- main proves the requested statement from explicit Residual_siteFiber.
- Unresolved: AKLT.W.WIN052.Residual_siteFiber, the fixed-rest one-site integration identity.
- The requested unconditional AKLT.W.WIN052.main : AKLT.Blueprint.Win.RemovalIntegralStatement is not delivered.
- Module build succeeds; axioms are only propext, Classical.choice, Quot.sound, with the residual still explicit.
- No existing files were modified.
