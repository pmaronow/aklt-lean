import AKLT.W.H1C025.Extraction
import AKLT.W.H1C025.Geometry

namespace AKLT.W.H1C025
open AKLT.Defs AKLT.Cert.H1.Production AKLT.Cert.H1

def axisPoint (i : Fin 4) : Plane := (compassAt i.val).step
def axisTip (i : Fin 4) : Plane := axisPoint i + axisPoint i

theorem axis_facts (i : Fin 4) :
    axisPoint i ∈ templateSites ∧ axisPoint i ≠ (0,0) ∧ axisPoint i ∉ templateTips := by
  fin_cases i <;> norm_num [axisPoint, compassAt, Compass.step,
    templateSites, square, latticeDist, templateTips]

theorem axis_tip (i : Fin 4) : axisTip i ∈ templateTips := by
  fin_cases i <;> norm_num [axisTip, axisPoint, compassAt, Compass.step, templateTips,
    Prod.mk_add_mk]

theorem center_edge (π : PatternData) (hπ : π.Covered) (i : Fin 4) :
    (i.val != 3 && (rawOptionAt π (axisPoint i)).status != 0 &&
      hasDirection (rawOptionAt π (axisPoint i)).mask ((i.val+2)%4)) =
        presentBond π (0,0) (axisPoint i) := by
  have hi : ((0,0),axisPoint i) ∈ templateEdges := by
    fin_cases i <;> norm_num [axisPoint, compassAt, Compass.step, templateEdges]
  have hp : dirPoint (axisPoint i) ⟨(i.val+2)%4, Nat.mod_lt _ (by omega)⟩ = (0,0) := by
    fin_cases i <;> norm_num [axisPoint, dirPoint, compassAt, Compass.step, Prod.mk_add_mk]
  have hk : axisPoint i ∈ π.keptAt (0,0) ↔ i.val ≠ 3 := by
    rw [hπ.2.2.1]
    fin_cases i <;> norm_num [axisPoint, compassAt, Compass.step]
  apply Bool.eq_iff_iff.mpr
  rw [presentBond_iff π _ _ hi]
  by_cases hs : π.statusAt (axisPoint i) = .X
  · simp [bondCondition, rawOption_status, hs, statusDigit]
  have hb := rawOption_direction π hπ _ (axis_facts i).1 (axis_facts i).2.1
    (axis_facts i).2.2 hs ⟨(i.val+2)%4, Nat.mod_lt _ (by omega)⟩
  simp only [hp] at hb
  rw [hb]
  have h0t : (0,0) ∉ templateTips := by norm_num [templateTips]
  simp [bondCondition, Bool.and_eq_true, rawOption_nonzero, hπ.2.1,
    h0t, (axis_facts i).2.2, hk, hs, and_comm]

theorem tip_edge (π : PatternData) (hπ : π.Covered) (i : Fin 4) :
    ((rawOptionAt π (axisPoint i)).status != 0 &&
      hasDirection (rawOptionAt π (axisPoint i)).mask i.val) =
        presentBond π (axisPoint i) (axisTip i) := by
  have hi : (axisPoint i,axisTip i) ∈ templateEdges := by
    fin_cases i <;> norm_num [axisPoint, axisTip, compassAt, Compass.step,
      Prod.mk_add_mk, templateEdges]
  have hp : dirPoint (axisPoint i) i = axisTip i := rfl
  have ht := hπ.2.2.2.2.2.2.2.2.1 _ (axis_tip i)
  apply Bool.eq_iff_iff.mpr
  rw [presentBond_iff π _ _ hi]
  by_cases hs : π.statusAt (axisPoint i) = .X
  · simp [bondCondition, rawOption_status, hs, statusDigit]
  rw [rawOption_direction π hπ _ (axis_facts i).1 (axis_facts i).2.1
    (axis_facts i).2.2 hs i]
  simp [bondCondition, Bool.and_eq_true, rawOption_nonzero, ht,
    (axis_facts i).2.2, axis_tip, hp]

theorem cycle_edge (π : PatternData) (hπ : π.Covered) (x y : Plane)
    (d e : Nat) (hd : d < 4) (he : e < 4)
    (hx : x ∈ templateSites) (hy : y ∈ templateSites)
    (hx0 : x ≠ (0,0)) (hy0 : y ≠ (0,0))
    (hxt : x ∉ templateTips) (hyt : y ∉ templateTips)
    (hxy : dirPoint x ⟨d,hd⟩ = y) (hyx : dirPoint y ⟨e,he⟩ = x)
    (hi : (x,y) ∈ templateEdges) :
    ((rawOptionAt π x).status != 0 && (rawOptionAt π y).status != 0 &&
      hasDirection (rawOptionAt π x).mask d &&
        hasDirection (rawOptionAt π y).mask e) = presentBond π x y := by
  apply Bool.eq_iff_iff.mpr
  rw [presentBond_iff π _ _ hi]
  by_cases hsx : π.statusAt x = .X
  · simp [bondCondition, rawOption_status, hsx, statusDigit]
  by_cases hsy : π.statusAt y = .X
  · simp [bondCondition, rawOption_status, hsy, statusDigit]
  rw [rawOption_direction π hπ x hx hx0 hxt hsx ⟨d,hd⟩,
    rawOption_direction π hπ y hy hy0 hyt hsy ⟨e,he⟩]
  simp [bondCondition, Bool.and_eq_true, rawOption_nonzero, hsx, hsy,
    hxt, hyt, hxy, hyx]

theorem rawEdges_explicit (e n w s ne nw sw se : RawOption) :
    rawEdges [e,n,w,s] [ne,nw,sw,se] =
      [e.status != 0 && hasDirection e.mask 2,
       n.status != 0 && hasDirection n.mask 3,
       w.status != 0 && hasDirection w.mask 0, false,
       e.status != 0 && ne.status != 0 && hasDirection e.mask 1 && hasDirection ne.mask 3,
       ne.status != 0 && n.status != 0 && hasDirection ne.mask 2 && hasDirection n.mask 0,
       n.status != 0 && nw.status != 0 && hasDirection n.mask 2 && hasDirection nw.mask 0,
       nw.status != 0 && w.status != 0 && hasDirection nw.mask 3 && hasDirection w.mask 1,
       w.status != 0 && sw.status != 0 && hasDirection w.mask 3 && hasDirection sw.mask 1,
       sw.status != 0 && s.status != 0 && hasDirection sw.mask 0 && hasDirection s.mask 2,
       s.status != 0 && se.status != 0 && hasDirection s.mask 0 && hasDirection se.mask 2,
       se.status != 0 && e.status != 0 && hasDirection se.mask 1 && hasDirection e.mask 3,
       e.status != 0 && hasDirection e.mask 0,
       n.status != 0 && hasDirection n.mask 1,
       w.status != 0 && hasDirection w.mask 2,
       s.status != 0 && hasDirection s.mask 3] := by
  simp [rawEdges, ringOptions, edgeDirections, List.range_succ]

theorem edges_eq (π : PatternData) (hπ : π.Covered) :
    rawEdges (axesOf π) (cornersOf π) = semanticEdges π := by
  rw [axesOf, cornersOf, rawEdges_explicit]
  simp only [semanticEdges, templateEdges, List.map_cons, List.map_nil, List.cons.injEq,
    and_true]
  repeat' constructor
  · simpa [axisPoint, compassAt, Compass.step] using center_edge π hπ 0
  · simpa [axisPoint, compassAt, Compass.step] using center_edge π hπ 1
  · simpa [axisPoint, compassAt, Compass.step] using center_edge π hπ 2
  · simpa [axisPoint, compassAt, Compass.step] using center_edge π hπ 3
  all_goals first | apply cycle_edge π hπ | skip
  all_goals try norm_num [templateSites, square, latticeDist, templateTips, templateEdges,
    dirPoint, compassAt, Compass.step, Prod.mk_add_mk]
  · simpa [axisPoint, axisTip, compassAt, Compass.step, Prod.mk_add_mk] using tip_edge π hπ 0
  · simpa [axisPoint, axisTip, compassAt, Compass.step, Prod.mk_add_mk] using tip_edge π hπ 1
  · simpa [axisPoint, axisTip, compassAt, Compass.step, Prod.mk_add_mk] using tip_edge π hπ 2
  · simpa [axisPoint, axisTip, compassAt, Compass.step, Prod.mk_add_mk] using tip_edge π hπ 3

#print axioms axis_facts
#print axioms axis_tip
#print axioms center_edge
#print axioms tip_edge
#print axioms cycle_edge
#print axioms rawEdges_explicit
#print axioms edges_eq

end AKLT.W.H1C025
