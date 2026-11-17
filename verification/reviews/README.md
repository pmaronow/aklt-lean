# Independent statement reviews

These compressed reports are verbatim review snapshots. Their original paths,
line numbers, manuscript versions, and quoted identifier spellings are evidence
about the materials each reviewer received, not instructions for running this
repository. `manifest.json` pins their uncompressed bytes. Use `gzip -dc` to read
a report. No report is represented as a review of proof modules it did not see.

| Review | Scope | Verdict |
|---|---|---|
| FID_FABLE | Physical Challenge, selected H1/H2/H3 inputs, and the reduction against manuscript-v2 | FAITHFUL WITH REMARKS; no Fatal or Major finding |
| FID_ASTRA | The same selected statement and input layer, with exact finite checks | FAITHFUL WITH REMARKS; no Fatal or Major finding |
| FID_CH2 | Earlier all-parity target MainStatementV2 against the supplied target and earlier paper; headline only | PASS; zero blocking findings |

The third review predates the current paper and its corrected citations; it is
not another whole-tree proof audit. The two current-paper reviews agree on the
selected theorem. Their minor findings were resolved in the fidelity fix rounds:
correct paper locations, removal of the obsolete even-period statement, accurate
Iff.rfl documentation, exact Challenge generation, no root Challenge cache resets,
an explicit spin convention, proved sanity propositions, and input-layer notes.
See `docs/STATEMENT-NOTES.md`, `docs/FIDELITY.md`, and
`verification/fidelity-fix/` and `verification/fidelity-round2/` from the repository
root. Legacy/V2 operators and redundant raw sign indices are documented with
their precise domain restrictions; no unrestricted identification is claimed.
