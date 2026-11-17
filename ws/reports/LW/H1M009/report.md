STATUS: PROVED

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M009/AKLT/W/H1M009/Main.lean): complete proof; all supporting declarations are private.
- [Check.lean](/home/ubuntu/aklt/wt/LW_H1M009/AKLT/W/H1M009/Check.lean): independent import and exact-type check.

## Exported declarations

```lean
theorem AKLT.W.H1M009.main :
    AKLT.Blueprint.H1.OriginalDegreeStatement
```

Equivalently, for every pattern `π`, coveredness implies that both original
integrands are internally admissible: each monomial has total degree at most
four at each internal site, and every omitted site's coordinate exponents vanish.

## Proof

Polynomial support inclusions under addition, multiplication, finite sums, and
finite products bound each monomial's degree by the number of incident factors.
Each formal dot product contributes at most one degree at each internal endpoint.

Two finite facts are proved using `decide +kernel`: every slot belongs to the
template, and the full template's incident bonds plus external slots number at
most four at every template site. Actual bonds form a subset of those bonds, and
retained slots contribute no more than the full slot count. Every actual bond
endpoint and retained slot site is active, so all incidence counts vanish at
omitted sites. These facts hold for arbitrary raw patterns; the required
coveredness hypothesis is therefore unnecessary for this degree bound.

No other blueprint leaf is used as a lemma, and no residual assumptions remain.

## Axioms

`#print axioms AKLT.W.H1M009.main` outputs:

```text
'AKLT.W.H1M009.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Validation

With `PATH="$HOME/.elan/bin:$PATH"`:

- `lake build AKLT.W.H1M009.Main` — passed; 21.20 seconds wall time, Lake module build time 10 seconds.
- `lake env lean AKLT/W/H1M009/Check.lean` — passed; 12.96 seconds wall time. The checker imports `Main`, assigns `main` to the exact requested proposition, and prints its type and axioms.
- Source scan found none of the forbidden proof shortcuts or declarations.

## Open issues

None.

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M009/Main.lean` with the exact requested theorem name and type.
- Delivered `AKLT/W/H1M009/Check.lean` with a passing independent exact-type check.
- Status: PROVED; no residual statements or dependencies on other blueprint leaves.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Both remaining claims from the earlier attempt are now proved.
- Existing statement and library files were not modified.
- Limitations, deviations, and open declarations: none.
- No orchestrator decision or follow-up proof is needed.
