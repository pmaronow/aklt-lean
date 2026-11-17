STATUS: PROVED FROM DEPS

# H1C001 — integer entries

The requested closed theorem is proved with exactly the required name and type:

```lean
theorem AKLT.W.H1C001.main :
    AKLT.Cert.H1.Production.TopLeaves.integerEntries
```

There are no residual assumptions. The earlier `Residual_integrality` and
`Residual_symmetry` declarations have been removed.

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C001/AKLT/W/H1C001/Main.lean) — closed target theorem, exact-type check, and axiom audit.
- [Arithmetic.lean](/home/ubuntu/aklt/wt/LW_H1C001/AKLT/W/H1C001/Arithmetic.lean) — coefficient inversion and denominator clearing.
- [RationalPauli.lean](/home/ubuntu/aklt/wt/LW_H1C001/AKLT/W/H1C001/RationalPauli.lean) — integral rational Pauli contractions and symmetry.

`Main.lean` transitively imports every Lean file in this directory. No existing
files outside `AKLT/W/H1C001/` were changed.

## Proof

Variable inversion multiplies each monomial coefficient by an integer product
of signs. Thus the supplied `ClearsDenominator` hypothesis also clears the
inverted coefficients at the exact current/next scales `3D₀` and `5D₀`.
Rational Pauli entries have integer real and imaginary coordinates; multiplication
preserves this property. Summing against the integer exchange-basis coordinates
therefore gives an integer scaled sector entry, so its floor is exact.

For symmetry, transposing each rational Pauli matrix conjugates its entry.
Conjugation commutes with the rational complex multiplication used by the list
fold. Taking real parts and interchanging the two finite basis sums proves
symmetry of `rationalSectorEntry` for every rational polynomial. Applying the
same scale and floor preserves symmetry.

The argument does not require coveredness or the restriction that inversion is
a union of groups. It proves the target while retaining its frozen hypotheses.
There is no division by the witness parameter `g`.

## Reused proved leaf

- Module: `AKLT.W.H1C022.Main`.
- Declaration: `AKLT.W.H1C022.main`.
- Statement: `AKLT.Cert.H1.Production.Leaves.sectorLinearity`.
- This dependency appears in `/home/ubuntu/aklt/state/lw/proved-index.tsv`.

It identifies multiplication of a polynomial by `MvPolynomial.C k` with
multiplication of its rational sector entry by `k`.

## Exported declarations

All declarations below are in namespace `AKLT.W.H1C001`. The notation and types
are those of `AKLT.Defs`.

```lean
def integerRationals : Subring ℚ := (Int.castRingHom ℚ).range

theorem rationalSectorEntry_integral
    (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ)
    (hp : ∀ m, p.coeff m ∈ integerRationals)
    (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε p a b ∈ integerRationals

theorem rationalSectorEntry_symm
    (π : PatternData) (r : Representation) (ε : ExchangeSigns π)
    (p : MvPolynomial (Fin 20 × Fin 3) ℚ)
    (a b : CentralBasis π r ε) :
    rationalSectorEntry π r ε p a b = rationalSectorEntry π r ε p b a

theorem invertPolynomial_coeff
    (I : Finset (Fin 20)) (p : MvPolynomial (Fin 20 × Fin 3) ℚ)
    (d : (Fin 20 × Fin 3) →₀ ℕ) :
    ∃ z : ℤ, (invertPolynomial I p).coeff d = p.coeff d * (z : ℚ)

theorem scaled_inverted_coeff_integral
    (π : PatternData) (r : Representation) (I : Finset (Fin 20))
    (D₀ : ℕ) (hD : ClearsDenominator π r D₀)
    (next : Bool) (d : (Fin 20 × Fin 3) →₀ ℕ) :
    (MvPolynomial.C ((if next then 5 else 3) * (D₀ : ℚ)) *
      invertPolynomial I (reducedPolynomial π r next)).coeff d ∈ integerRationals

theorem scaled_sector_integral
    (π : PatternData) (r : Representation) (I : Finset (Fin 20))
    (D₀ : ℕ) (hD : ClearsDenominator π r D₀)
    (ε : ExchangeSigns π) (next : Bool) (a b : CentralBasis π r ε) :
    ∃ z : ℤ, (if next then 5 else 3) * (D₀ : ℚ) * rationalSectorEntry π r ε
      (invertPolynomial I (reducedPolynomial π r next)) a b = z

theorem main : AKLT.Cert.H1.Production.TopLeaves.integerEntries
```

## Axioms

Each exported theorem has a corresponding `#print axioms` command in its source.
The output is:

```text
'AKLT.W.H1C001.rationalSectorEntry_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C001.rationalSectorEntry_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C001.invertPolynomial_coeff' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C001.scaled_inverted_coeff_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C001.scaled_sector_integral' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C001.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The delivered source contains no forbidden declarations, tactics, or options.

## Validation

- `/usr/bin/time -f 'ELAPSED=%e s' lake build AKLT.W.H1C001.Main` — passed in **22.48 s** after the final edits. The three task modules compiled in 5.6 s, 5.9 s, and 5.4 s. Existing imported modules emitted their pre-existing warnings; the task modules emitted none.
- `#check (AKLT.W.H1C001.main : AKLT.Cert.H1.Production.TopLeaves.integerEntries)` — passed as part of that build.
- `lake env leanexport AKLT.W.H1C001.Main -- AKLT.W.H1C001.main` — dependency-closure export passed in **19.68 s**.
- `con-ron --verified --jobs=4 --progress=1 export.ndjson` — passed in **26.30 s**: `con-ron: accepted 9388 declarations (--verified)`.
- `nanoda_bin nanoda.json` — passed in **3.29 s**: `Checked 10311 declarations with no typechecker errors`. Its configuration permits only the three allowed axioms and makes other axioms hard errors. NanoDa additionally reported one pretty-printer warning, `Unable to print axioms`; this was not a typechecker error.

Checker logs and timings: [con-ron.log](/home/ubuntu/aklt/reports/LW/H1C001/con-ron.log),
[con-ron.progress.log](/home/ubuntu/aklt/reports/LW/H1C001/con-ron.progress.log),
[nanoda.log](/home/ubuntu/aklt/reports/LW/H1C001/nanoda.log),
[nanoda.json](/home/ubuntu/aklt/reports/LW/H1C001/nanoda.json), and
[checker-results.json](/home/ubuntu/aklt/reports/LW/H1C001/checker-results.json).
The temporary 39 MB dependency export was removed after validation; it can be
regenerated with the recorded export command.

## Open issues

None. Both independent kernels accepted the proof. The NanoDa pretty-printer
warning recorded above is the only diagnostic from independent validation.

## ORCH-SUMMARY

- Delivered the closed `AKLT.W.H1C001.main` at the exact requested type.
- All earlier arithmetic and symmetry residuals are discharged.
- Files: `Main.lean`, `Arithmetic.lean`, `RationalPauli.lean`; all are imported.
- Reused indexed dependency: `AKLT.W.H1C022.main` (`Leaves.sectorLinearity`).
- Scales are exactly `3D₀` and `5D₀`; no witness-`g` division occurs.
- Build, exact-type check, and axiom audit passed.
- Allowed axioms only: `propext`, `Classical.choice`, `Quot.sound`.
- Open proof declarations: none.
- Con-ron accepted 9,388 declarations; NanoDa checked 10,311 without type errors.
- NanoDa emitted one reporting-only warning: `Unable to print axioms`.
- Orchestrator: register/merge H1C001 after the usual validation.
