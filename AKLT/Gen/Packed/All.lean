module
public import AKLT.Gen.Packed.Construction
public import AKLT.Gen.Packed.Check
public import AKLT.Gen.Packed.Grid

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Public entry point for packed-plane arithmetic and square-grid routing.
The worked literal certificate is in `AKLT.Gen.Packed.Example`.
-/
