**Target ("the fit").** The whole package — proof tree plus BOTH finite certificates (H1 and H3′) plus H2 — must
pass that verifier on the default profile. The certificates are kernel-checked three times there (clean build;
Lean's kernel replay of the export; NanoDa — measured at 0.1–5x Lean on certificate modules, see
`/home/ubuntu/aklt/reports/REL_FEAS/report.md`), with at most ~5 Lean processes in parallel during the build
(32 GiB) and with the Lean replay possibly serial (being measured). Design to two levels and say which you reach:
- Level A (safe even if the replays are serial): each certificate costs at most ~15 minutes of single-thread Lean
  kernel time in total, at most 4 GiB per process, at most ~200 MB of exported literal data, source files of at
  most 10,000 lines each and a few hundred MB of generated source in total.
- Level B (needs parallel replays or the larger 32 CPU / 64 GiB profile): at most ~3 CPU-hours of Lean kernel
  time per certificate, at most 6 GiB per process, at most ~2 GB of exported literals.
Today: H1 ≈ 115 CPU-hours, H3′ ≈ 20 CPU-hours. Rules that stay: no `native_decide`, no new axioms (only propext,
Classical.choice, Quot.sound), everything kernel-checked; the headline theorem is unchanged (existential
constants: ∃ c > 0, L₀ with every nonzero eigenvalue ≥ c for all L, N ≥ L₀), so ANY valid finite input that makes
the paper's argument go through is acceptable — weaker constants are fine as long as the final inequalities
still close.
