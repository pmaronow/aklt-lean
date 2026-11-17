# Receipts of the final build

These files are the compact receipts behind the root `VERIFICATION.md`. They were
produced on sources with Lean source digest
`c875dff024d396b0b78f1fa955ea5d38e8f577e1d8bd69e970fd02bea906bee9`. `SHA256SUMS`
pins every file here except this note. Files ending in `.gz` are gzip-compressed
copies of the original logs. The complete report directory, including per-module
logs and axiom transcripts, is the release asset `verification-receipts.tar.zst`.

| Directory | Contents |
|---|---|
| `status/` | Time-stamped status lines of the three build drivers |
| `handwritten/` | Lake logs of the cold hand-written build and of the rebuild after comment-only edits |
| `H1/` | Input receipt, run record, verifier summary, per-kind totals, generated-source hashes, closing receipt, verifier logs |
| `H3/` | Summary, run records, environment, input pins, axiom and declaration lists, generated-source hashes, verifier logs |
| `closing/` | Input pins, closing-module and Audit transcripts, source and header checks, both statement comparisons |
| `regression/` | Independent-kernel replay of the two-input reduction: receipt and stage results |
| `archives/` | Comparison of the released source archives with the final build's generated sources; hashes of the release assets |

Absolute paths in these files are those of the build machine. Commit hashes in the
status files are development commits; they resolve on the `development` branch.
The status files also show two restarts: the H3 driver was restarted from an empty
state after comment-only edits to the Lean sources, and the H1 driver was restarted
without a preliminary step that named two modules that do not exist. The closing
driver first stopped at the input-pin check because the input directory had not
been prepared, and later at the source check because of the two author-metadata
findings; the remaining checks were then run and passed.
