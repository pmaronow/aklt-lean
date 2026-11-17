import AKLT.Blueprint.Q.NodesFrames
import AKLT.Blueprint.Q.NodesTight

open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Q

-- Inspection only: this module contains no theorem or proof.
#print OrthogonalFamilyStatement
#print OneSiteMomentEncodingStatement
#print IcoDistanceStatement
#print RotationDisplacementStatement
#print SelfRotationStatement
#print DisplacedDistanceStatement
#print RelativeRotationStatement
#print SpinorChoiceStatement

#print DegreeFour
#print SeparateDegreeFour
#print productFunctional
#print compatible
#print chosenSpinor
#print spinDensity

noncomputable def oneSiteEncodingCandidate (p : MvPolynomial (Fin 3) ℝ) :
    MvPolynomial (Fin 1 × Fin 3) ℝ :=
  MvPolynomial.rename (fun k : Fin 3 => ((0 : Fin 1), k)) p

#check MvPolynomial.eval_rename
#check MvPolynomial.totalDegree_rename_le
#check MvPolynomial.le_totalDegree
#check Matrix.mulVec_mulVec
#check Matrix.mulVec_neg
#check Matrix.dotProduct_transpose_mulVec
#check Equiv.piUnique
#synth Fintype IcoLetter
#synth Fintype (Fin 1 → SpinLetter)
#eval Fintype.card IcoLetter
#eval Fintype.card SpinLetter
#eval Fintype.card (Fin 1 → SpinLetter)

set_option pp.explicit true in
#print DisplacedDistanceStatement
