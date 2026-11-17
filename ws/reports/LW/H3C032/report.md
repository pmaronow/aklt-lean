STATUS: PROVED

## Files

- `AKLT/W/H3C032/Main.lean`: completes the earlier scalar reduction and exports the requested closed theorem.
- `AKLT/W/H3C032/Arithmetic.lean`: proves the normalized exposure-factor identities and exact score/cross-product comparison.
- `build.log` and `exact-type.log` in this report directory record successful verification.
- The supplied earlier report remains in `report.luna.md`.

## Exported declarations

All declarations below are in namespace `AKLT.W.H3C032`. The main deliverable is exactly:

```lean
theorem main : CertData.H3.Bridge.ShortComparatorLeaf
```

The arithmetic helper exports:

```lean
def scaledScore (K X A : Nat) : ℚ :=
  ((X : ℚ) / K - 1) / (((X : ℚ) / K) * ((A : ℚ) / K))

theorem scaledScore_comparison (K X Y A B : Nat) (hK : 0 < K)
    (hX : K ≤ X) (hY : K ≤ Y) (hA : 0 < A) (hB : 0 < B) :
    (scaledScore K X A < scaledScore K Y B ↔
      (X - K) * Y * B < (Y - K) * X * A) ∧
    (scaledScore K X A = scaledScore K Y B ↔
      (X - K) * Y * B = (Y - K) * X * A)

theorem exposureFactor_normalized (E : Exact)
    (hE : CertData.H3.Bridge.ExactValid E) (a : RewardItem) :
    (exposureFactor E a : ℚ) / E.denominator = passageFactor a.straight

theorem denominator_le_exposureFactor (E : Exact)
    (hE : CertData.H3.Bridge.ExactValid E) (a : RewardItem) :
    E.denominator ≤ exposureFactor E a
```

The earlier reduction is retained, and its residual is now proved:

```lean
def ResidualScaledComparator : Prop :=
  ∀ (E : Exact), CertData.H3.Bridge.ExactValid E →
    ∀ (n : Nat) (w : DirectionWord n) (a b : RewardItem) (i j : Fin n),
      i.val = a.time → j.val = b.time →
      a.straight = wordStraight kernelIncoming w i →
      b.straight = wordStraight kernelIncoming w j →
      (a.reward : ℚ) / E.denominator = witnessKappa w i →
      (b.reward : ℚ) / E.denominator = witnessKappa w j →
      itemLE E a b = shortOrderLE w i j

theorem scaledComparator : ResidualScaledComparator

theorem main_of_residual (hcore : ResidualScaledComparator) :
    CertData.H3.Bridge.ShortComparatorLeaf
```

## Proof

The proof reuses the supplied earlier attempt's extraction of item data from `PrefixRepresents`. `ExactValid` identifies each stored exposure numerator divided by the denominator with its passage factor. Both fixed passage factors are at least one, so natural subtraction of the denominator agrees with rational subtraction.

For positive rewards, each rational score equals `(X-K)*K/(X*A)`. Positive denominators permit cross-multiplication; cancellation of the common positive scale gives exactly the natural products used by `itemLE`. Strict comparison and equality are both proved, preserving chronological ties. Separate zero-reward branches preserve the specified infinity ordering, including chronological ordering when both rewards vanish.

No certificate is normalized or enumerated. No other blueprint leaf is used as a lemma. No additional model or sub-agent was invoked; this continuation completes the earlier attempt supplied with the task.

## Axiom audit

Successful build output from the six `#print axioms` commands:

```text
'AKLT.W.H3C032.scaledScore_comparison' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C032.exposureFactor_normalized' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C032.denominator_le_exposureFactor' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C032.scaledComparator' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C032.main_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H3C032.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The delivered Lean sources contain none of the forbidden declarations or tactics.

## Verification

With `$HOME/.elan/bin` added to `PATH`:

- `lake env lean AKLT/W/H3C032/Arithmetic.lean`: successful first helper check, 8.92 seconds wall time. An unnecessary trailing tactic warning was subsequently removed.
- The first full build exposed a dependent-rewrite issue under `decide`; replacing that rewrite with simplification resolved it.
- `lake build AKLT.W.H3C032.Main`: successful final build, 15.88 seconds wall time; Main compilation reported 6.6 seconds. The log includes replayed warnings from existing Packed modules, with no warnings from the delivered files.
- A separate `lake env lean --stdin` import check succeeded in 7.24 seconds, using:

```lean
import AKLT.W.H3C032.Main
example : CertData.H3.Bridge.ShortComparatorLeaf := AKLT.W.H3C032.main
#check AKLT.W.H3C032.main
#print axioms AKLT.W.H3C032.main
```

Its output confirms the exact name and type and only the three permitted axioms.

## Open issues

None. `ResidualScaledComparator` is fully discharged by `scaledComparator`; the requested theorem has no residual hypotheses. Changes are confined to the assigned task directory and report directory.

## ORCH-SUMMARY

- Delivered `AKLT.W.H3C032.main : CertData.H3.Bridge.ShortComparatorLeaf`.
- Main file: `AKLT/W/H3C032/Main.lean`; helper: `AKLT/W/H3C032/Arithmetic.lean`.
- Completed the supplied earlier reduction; its arithmetic residual is proved.
- Exact scaling, natural subtraction, zero-reward infinity, and chronological ties are covered.
- No certificate normalization, other blueprint-leaf dependency, or sub-agent.
- Every exported theorem uses only `propext`, `Classical.choice`, and `Quot.sound`.
- Required build passed in 15.88 seconds; separate exact-type import check passed in 7.24 seconds.
- Open leaves/residuals: none. No mathematical limitations or decisions remain.
