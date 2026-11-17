module
public import AKLT.W.H1C025.Edges

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C025
open AKLT.Defs AKLT.Cert.H1.Production AKLT.Cert.H1

def semanticStatus (π : PatternData) : List Nat :=
  ringSites.map fun x => if patternDegree π x == 0 then 0 else statusDigit (π.statusAt x)

theorem ring_options (π : PatternData) :
    ringOptions (axesOf π) (cornersOf π) = ringSites.map (rawOptionAt π) := by
  simp [ringOptions, axesOf, cornersOf, ringSites, List.range_succ]

theorem status_at (π : PatternData) (i : Fin 8) :
    (if edgeLive (semanticEdges π) i.val then
        (rawOptionAt π (ringSites.getD i.val (0,0))).status else 0) =
      (if patternDegree π (ringSites.getD i.val (0,0)) == 0 then 0
        else statusDigit (π.statusAt (ringSites.getD i.val (0,0)))) := by
  cases he : edgeLive (semanticEdges π) i.val with
  | false =>
    have hz := (ring_degree_zero π i).mpr he
    simp only [Bool.false_eq_true, ite_false, hz, beq_self_eq_true, ite_true]
  | true =>
    have hz : patternDegree π (ringSites.getD i.val (0,0)) ≠ 0 := by
      intro hz
      have hf := (ring_degree_zero π i).mp hz
      rw [he] at hf
      contradiction
    simp only [ite_true, beq_iff_eq, hz, ite_false, rawOption_status]

theorem statuses_eq (π : PatternData) :
    rawStatusDigits (axesOf π) (cornersOf π) (semanticEdges π) = semanticStatus π := by
  apply List.ext_getElem
  · simp [rawStatusDigits, ring_options, semanticStatus]
  · intro j hj _
    have hj8 : j < 8 := by
      simpa [rawStatusDigits, ring_options, ringSites] using hj
    have h := status_at π ⟨j,hj8⟩
    interval_cases j <;>
      simpa [rawStatusDigits, ring_options, semanticStatus, ringSites,
        edgeLive, List.zipIdx_cons'] using h

theorem reflected_status (π : PatternData) :
    reflectSites.map (fun i => (semanticStatus π).getD i 0) =
      ringSites.map (fun x => if patternDegree π (reflectPoint true x) == 0 then 0
        else statusDigit (π.statusAt (reflectPoint true x))) := by
  simp [reflectSites, semanticStatus, ringSites, reflectPoint]

theorem reflected_edges (π : PatternData) :
    reflectEdges.map (fun i => (semanticEdges π).getD i false) =
      templateEdges.map (fun (a,b) =>
        presentBond π (reflectPoint true a) (reflectPoint true b)) := by
  simp [reflectEdges, semanticEdges, templateEdges, reflectPoint, presentBond_symm]

theorem outgoing_code (π : PatternData) (hπ : π.Covered) (r : Bool) :
    (if r then
        if outgoingIndex π.outgoing == 0 then 2
        else if outgoingIndex π.outgoing == 2 then 0 else outgoingIndex π.outgoing
      else outgoingIndex π.outgoing) =
      (if π.outgoing == .north then 1
        else if (π.outgoing == .east) != r then 0 else 2) := by
  have hs := hπ.1
  cases π.outgoing <;> cases r <;> simp [outgoingIndex] at hs ⊢

theorem code_eq (π : PatternData) (hπ : π.Covered) (r : Bool) :
    rawCode (axesOf π) (cornersOf π) (outgoingIndex π.outgoing) r =
      reflectedPatternCode π r := by
  simp only [rawCode, edges_eq π hπ, statuses_eq, outgoing_code π hπ]
  cases r with
  | false => simp [reflectedPatternCode, semanticStatus, semanticEdges, reflectPoint,
      Function.comp_def]
  | true =>
    rw [ite_eq_left rfl, ite_eq_left rfl, reflected_status, reflected_edges]
    simp only [reflectedPatternCode, List.map_map, Function.comp_def]

theorem outgoing_present (π : PatternData) (hπ : π.Covered) :
    presentBond π (0,0) π.outgoing.step = true := by
  have hxt : π.outgoing.step ∈ templateSites := by
    cases π.outgoing <;> norm_num [Compass.step, templateSites, square, latticeDist]
  have hxnt : π.outgoing.step ∉ templateTips := by
    cases π.outgoing <;> norm_num [Compass.step, templateTips]
  have hc : (0,0) ∈ templateSites \ templateTips := by
    norm_num [templateSites, square, latticeDist, templateTips]
  have hout := hπ.1
  have hk0 : π.outgoing.step ∈ π.keptAt (0,0) := by
    rw [hπ.2.2.1]
    cases ho : π.outgoing <;> simp [ho] at hout
    all_goals simp [Compass.step]
  have hsa : π.statusAt π.outgoing.step ≠ .X := hπ.2.2.2.2.2.1
  have hs0 : π.statusAt (0,0) ≠ .X := by simp [hπ.2.1]
  have ha : Adjacent (0,0) π.outgoing.step := by
    cases π.outgoing <;> norm_num [Compass.step, Adjacent, latticeDist]
  have hk := (hπ.2.2.2.2.2.2.2.2.2 (0,0) hc _
    (Finset.mem_sdiff.mpr ⟨hxt,hxnt⟩) hs0 hsa ha).mp hk0
  have hi : ((0,0),π.outgoing.step) ∈ templateEdges := by
    cases π.outgoing <;> simp [Compass.step, templateEdges]
  apply (presentBond_iff π _ _ hi).mpr
  exact ⟨hs0,hsa,Or.inr hk0,Or.inr hk⟩

theorem outgoing_edge (π : PatternData) (hπ : π.Covered) :
    (rawEdges (axesOf π) (cornersOf π)).getD (outgoingIndex π.outgoing) false = true := by
  rw [edges_eq π hπ]
  have hp := outgoing_present π hπ
  have hs := hπ.1
  cases ho : π.outgoing <;> simp [ho] at hs
  all_goals simpa [ho, outgoingIndex, semanticEdges, templateEdges, Compass.step] using hp

#print axioms ring_options
#print axioms status_at
#print axioms statuses_eq
#print axioms reflected_status
#print axioms reflected_edges
#print axioms outgoing_code
#print axioms code_eq
#print axioms outgoing_present
#print axioms outgoing_edge

end AKLT.W.H1C025
