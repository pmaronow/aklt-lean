module
public import AKLT.W.H1C025.Compatibility
public import AKLT.W.H1C025.Encoding

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Extract a normalized raw representative from every covered pattern.
Only irrelevant X and U flags are normalized. D flags are encoded from the
actual kept sets; mutual consistency proves the corner pruning condition.
The encoding comparison uses present bonds and the actual template degrees. -/
namespace AKLT.W.H1C025
open AKLT.Defs AKLT.Cert.H1.Production AKLT.Cert.H1

/-- Every covered pattern has an allowed raw representative with the same
plain and reflected effective data, hence the same canonical key. -/
theorem main : AKLT.Cert.H1.Production.Leaves.rawEncoding := by
  intro π hπ
  refine ⟨axesOf π, axes_mem π hπ, cornersOf π, by simp [cornersOf],
    corners_valid π hπ, outgoingIndex π.outgoing, outgoingIndex_lt π hπ,
    outgoing_edge π hπ, ?_⟩
  unfold effectivePatternCode rawKey
  exact congrArg₂ min (code_eq π hπ false).symm (code_eq π hπ true).symm

#print axioms main

end AKLT.W.H1C025
