import AKLT.W.H1C009.Edges
import AKLT.W.H1C025.Encoding

/-! The input compiler and the raw encoder have the same bonds and effective
statuses.  The latter discard isolated sites before either reflection is encoded.
The imported helpers belong to the proved leaves H1C009 and H1C025. -/
namespace AKLT.W.H1C028
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

private theorem input_edges (a : Input) (ha : inputCheck a = true) :
    AKLT.W.H1C025.semanticEdges (inputPattern a) = rawEdges a.axes a.corners := by
  apply List.ext_getElem
  · simp [AKLT.W.H1C025.semanticEdges, templateEdges, rawEdges]
  · intro i hi hj
    have hi16 : i < 16 := by
      simpa [AKLT.W.H1C025.semanticEdges, templateEdges] using hi
    have ht : i < templateEdges.length := by simpa [templateEdges] using hi16
    have h := AKLT.W.H1C009.raw_edge a ha i hi16
    dsimp only at h
    rw [List.getD_eq_getElem _ _ ht, List.getD_eq_getElem _ _ hj] at h
    simpa only [AKLT.W.H1C025.semanticEdges, List.getElem_map] using h

private theorem input_status_digit (a : Input) (ha : inputCheck a = true)
    (i : Nat) (hi : i < 8) :
    statusDigit ((inputPattern a).statusAt (ringSites.getD i (0,0))) =
      ((ringOptions a.axes a.corners).getD i ⟨0,0⟩).status := by
  rw [AKLT.W.H1C009.statusAt_ring a i hi]
  rcases AKLT.W.H1C009.ring_status_range a ha i hi with hs | hs | hs <;>
    simp only [List.getD_eq_getElem?_getD] at hs ⊢ <;>
    simp [hs, statusDigit]

private theorem input_statuses (a : Input) (ha : inputCheck a = true) :
    rawStatusDigits a.axes a.corners (rawEdges a.axes a.corners) =
      AKLT.W.H1C025.semanticStatus (inputPattern a) := by
  apply List.ext_getElem
  · simp [rawStatusDigits, AKLT.W.H1C025.semanticStatus, ringOptions, ringSites]
  · intro i hi hj
    have hi8 : i < 8 := by simpa [rawStatusDigits, ringOptions] using hi
    have hr : i < (ringOptions a.axes a.corners).length := by
      simpa [ringOptions] using hi8
    have hx : i < ringSites.length := by simpa [ringSites] using hi8
    have hs := input_status_digit a ha i hi8
    have hz := AKLT.W.H1C025.ring_degree_zero (inputPattern a) ⟨i, hi8⟩
    rw [input_edges a ha] at hz
    rw [List.getD_eq_getElem _ _ hx] at hz hs
    rw [List.getD_eq_getElem _ _ hr] at hs
    simp only [rawStatusDigits, AKLT.W.H1C025.semanticStatus,
      List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
    change (if AKLT.W.H1C025.edgeLive (rawEdges a.axes a.corners) i then
        ((ringOptions a.axes a.corners)[i]).status else 0) =
      (if patternDegree (inputPattern a) (ringSites[i]) == 0 then 0
        else statusDigit ((inputPattern a).statusAt (ringSites[i])))
    by_cases hd : patternDegree (inputPattern a) (ringSites[i]) = 0
    · have he := hz.mp hd
      simp only [he, Bool.false_eq_true, ite_false, hd, beq_self_eq_true, ite_true]
    · have he : AKLT.W.H1C025.edgeLive (rawEdges a.axes a.corners) i = true := by
        cases hb : AKLT.W.H1C025.edgeLive (rawEdges a.axes a.corners) i with
        | false => exact (hd (hz.mpr hb)).elim
        | true => rfl
      simp only [he, ite_true, beq_iff_eq, hd, ite_false]
      exact hs.symm

private theorem input_code (a : Input) (ha : inputCheck a = true) (r : Bool) :
    rawCode a.axes a.corners a.outgoing r = reflectedPatternCode (inputPattern a) r := by
  have hout : a.outgoing < 3 := by
    have hh := ha
    simp only [inputCheck, Bool.and_eq_true, decide_eq_true_eq] at hh
    tauto
  have hO :
      (if r then if a.outgoing == 0 then 2 else if a.outgoing == 2 then 0 else a.outgoing
        else a.outgoing) =
      (if (inputPattern a).outgoing == .north then 1
        else if ((inputPattern a).outgoing == .east) != r then 0 else 2) := by
    rcases (show a.outgoing = 0 ∨ a.outgoing = 1 ∨ a.outgoing = 2 by omega)
      with ho | ho | ho <;> cases r <;> simp [inputPattern, compassAt, ho]
  simp only [rawCode]
  rw [input_statuses a ha, ← input_edges a ha, hO]
  cases r with
  | false =>
      simp [reflectedPatternCode, AKLT.W.H1C025.semanticStatus,
        AKLT.W.H1C025.semanticEdges, reflectPoint, Function.comp_def]
  | true =>
      rw [ite_eq_left rfl, ite_eq_left rfl, AKLT.W.H1C025.reflected_status,
        AKLT.W.H1C025.reflected_edges]
      simp only [reflectedPatternCode, List.map_map, Function.comp_def]

/-- Compilation preserves the canonical effective code, including isolated-site
removal and the east/west reflection of the outgoing direction. -/
theorem main : AKLT.Cert.H1.Production.Leaves.representativeCode := by
  intro a ha
  unfold effectivePatternCode rawKey
  exact congrArg₂ min (input_code a ha false).symm (input_code a ha true).symm

#print axioms AKLT.W.H1C028.main

end AKLT.W.H1C028
