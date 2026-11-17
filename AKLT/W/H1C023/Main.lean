module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C023

open AKLT.Cert.H1.Production
open AKLT.Gen.Gram

theorem main : AKLT.Cert.H1.Production.Leaves.directRowsEntry := by
  intro ss out p q indices n hlen i j
  have hi : i.val < indices.length := by omega
  have hj : j.val < indices.length := by omega
  change
    ((indices.map (fun row =>
      indices.map (fun col => (directSectorThreshold ss out p q row col).re))).getD i.val []).getD
        j.val 0 =
      (directSectorThreshold ss out p q (indices.getD i.val 0) (indices.getD j.val 0)).re
  let rowValues : Nat → List ℤ := fun row =>
    indices.map (fun col => (directSectorThreshold ss out p q row col).re)
  have hiMap : i.val < (indices.map rowValues).length := by simpa using hi
  have hOuterDefault :
      (indices.map rowValues).getD i.val [] =
        (indices.map rowValues).getD i.val (rowValues 0) := by
    rw [List.getD_eq_getElem (indices.map rowValues) [] hiMap]
    rw [List.getD_eq_getElem (indices.map rowValues) (rowValues 0) hiMap]
  have hOuter := List.getD_map (l := indices) (d := 0) (n := i.val) rowValues
  have hInner :
      (rowValues (indices.getD i.val 0)).getD j.val 0 =
        (directSectorThreshold ss out p q (indices.getD i.val 0)
          (indices.getD j.val 0)).re := by
    dsimp [rowValues]
    have hjMap : j.val < (indices.map
        (fun col => (directSectorThreshold ss out p q (indices.getD i.val 0) col).re)).length := by
      simpa using hj
    have hDefault :
        (indices.map
          (fun col => (directSectorThreshold ss out p q (indices.getD i.val 0) col).re)).getD
            j.val 0 =
          (indices.map
            (fun col => (directSectorThreshold ss out p q (indices.getD i.val 0) col).re)).getD
            j.val ((directSectorThreshold ss out p q (indices.getD i.val 0) 0).re) := by
      rw [List.getD_eq_getElem _ _ hjMap]
      rw [List.getD_eq_getElem _ _ hjMap]
    rw [hDefault]
    exact List.getD_map (l := indices) (d := 0) (n := j.val)
      (fun col => (directSectorThreshold ss out p q (indices.getD i.val 0) col).re)
  rw [show (indices.map (fun row =>
      indices.map (fun col => (directSectorThreshold ss out p q row col).re)) : List (List ℤ)) =
      indices.map rowValues by rfl]
  rw [hOuterDefault, hOuter, hInner]

end AKLT.W.H1C023
