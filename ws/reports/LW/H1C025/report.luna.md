STATUS: PARTIAL

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C025/AKLT/W/H1C025/Main.lean)

## Delivered declarations

The exact theorem `AKLT.W.H1C025.main : AKLT.Cert.H1.Production.Leaves.rawEncoding` is not proved yet. `Main.lean` contains five closed residual propositions:

```lean
def Residual_axesShape : Prop :=
  ∀ π : PatternData, π.Covered → axesOf π ∈ axialConfigurations

def Residual_cornerShape : Prop :=
  ∀ π : PatternData, π.Covered →
    (cornersOf π).zipIdx.all (fun (x,i) =>
      cornerOptions.contains x && cornerCompatible (axesOf π) i x) = true

def Residual_outgoingEdge : Prop :=
  ∀ π : PatternData, π.Covered →
    (rawEdges (axesOf π) (cornersOf π)).getD (outgoingIndex π.outgoing) false = true

def Residual_plainCode : Prop :=
  ∀ π : PatternData, π.Covered →
    rawCode (axesOf π) (cornersOf π) (outgoingIndex π.outgoing) false =
      reflectedPatternCode π false

def Residual_reflectedCode : Prop :=
  ∀ π : PatternData, π.Covered →
    rawCode (axesOf π) (cornersOf π) (outgoingIndex π.outgoing) true =
      reflectedPatternCode π true
```

The compiled conditional assembly has this exact statement:

```lean
theorem main_of_residuals :
    Residual_axesShape → Residual_cornerShape → Residual_outgoingEdge →
      Residual_plainCode → Residual_reflectedCode →
        AKLT.Cert.H1.Production.Leaves.rawEncoding
```

It is a conditional assembly, not the requested unconditional theorem.

The extraction normalizes irrelevant flags at X sites to mask 0 and U sites to mask 15, while retaining the actual D masks. The proved private helper lemmas show that each mask bit records the corresponding kept compass direction and that the four encoded directions are in bijection with `keptAt` for a template site. This addresses the raw-versus-normalized-mask issue at the representation level; the option classification and code comparisons remain open.

## Axioms

`#print axioms AKLT.W.H1C025.main_of_residuals`:

```text
[propext, Classical.choice, Quot.sound]
```

These are within the allowed axiom set. No forbidden proof escape appears in the delivered file.

## Build

- `PATH="$HOME/.elan/bin:$PATH" lake env lean AKLT/W/H1C025/Main.lean` — compiled successfully (about 8 seconds).
- `PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1C025.Main` — succeeded; Lake reported 7.4 seconds for the target and about 13 seconds wall time for the command.

## Open issues

The five residuals above are the exact remaining obligations. `Residual_axesShape` needs the covered U/X/D case analysis, including the distinct arrival-site rule and classification of two-kept-direction masks. `Residual_cornerShape` needs the corresponding corner mask classification and the covered mutual-consistency condition. `Residual_outgoingEdge` needs the connection between the extracted direction bit and `presentBond`. The two code residuals need the raw edge/status digit correspondence, isolated-site pruning, and the reflected site/edge permutations. Until these are proved, the exact requested `main` theorem is absent.

## ORCH-SUMMARY

- Delivered one compiled file: `AKLT/W/H1C025/Main.lean`.
- `AKLT.W.H1C025.main_of_residuals` assembles `rawEncoding` from five explicit closed residual propositions.
- Mask extraction and direction/cardinality helper lemmas are proved privately.
- Exact `AKLT.W.H1C025.main : rawEncoding` remains open.
- Open declarations: `Residual_axesShape`, `Residual_cornerShape`, `Residual_outgoingEdge`, `Residual_plainCode`, `Residual_reflectedCode`.
- Raw covered configurations still require treatment beyond the 2,048,000 normalized mask configurations; this implementation normalizes only irrelevant X/U flags and retains D masks.
- Build succeeded with allowed axioms `[propext, Classical.choice, Quot.sound]` for the conditional assembly.
- Orchestrator should resume by proving the five residuals; no external decision is required.
