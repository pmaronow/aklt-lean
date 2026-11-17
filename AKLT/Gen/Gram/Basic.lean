module
public import AKLT.Gen.Gram.Theory
public import AKLT.Gen.Gram.Checker

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Reusable entry point for integer Gram/residual certificates. Benchmark data
and certificates are deliberately imported separately. -/
