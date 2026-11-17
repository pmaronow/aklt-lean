module
public import AKLT.W.H1C009.Fields

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C009
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

private theorem siteSpec_eq_of_beq {x y : SiteSpec} (h : (x == y) = true) : x = y := by
  change instBEqSiteSpec.beq x y = true at h
  cases x
  cases y
  simp_all [instBEqSiteSpec.beq]

private theorem geometry_specs {a : Input} {ss : List PackedSite}
    (hgeom : geometryCheck a ss = true) :
    ss.length = 8 ∧ ∀ si ∈ ss.zipIdx, si.1.spec = inputSpec a si.2 := by
  unfold geometryCheck at hgeom
  have hparts := hgeom
  simp only [Bool.and_eq_true] at hparts
  constructor
  · exact of_decide_eq_true hparts.1
  · intro si hsi
    exact siteSpec_eq_of_beq (List.all_eq_true.mp hparts.2 si hsi)

private theorem dimensions_map {a : Input} {ss : List PackedSite}
    (hgeom : geometryCheck a ss = true) :
    ss.map (fun t => t.spec.dim) = (List.range 8).map (inputDimension a) := by
  have hs := geometry_specs hgeom
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, hs.1]
  · intro j hj₁ hj₂
    rw [List.getElem_map, List.getElem_map]
    have hjss : j < ss.length := by simpa using hj₁
    have hjr : j < 8 := by simpa using hj₂
    have hspec := (List.forall_mem_zipIdx'.mp hs.2) j hjss
    have hdim := congrArg (fun z : SiteSpec => z.dim) hspec
    simpa only [inputSpec, List.getElem_range (by simpa using hjr)] using hdim

private theorem tablesAccepted_mem {ss : List PackedSite} {s : PackedSite}
    (h : TablesAccepted ss) (hs : s ∈ ss) : tableCheck s.spec s.table = true := by
  induction ss with
  | nil => simp at hs
  | cons t ts ih =>
      change tableCheck t.spec t.table = true ∧ TablesAccepted ts at h
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · exact h.1
      · exact ih h.2 hs

/-- Accepted compiler geometry agrees with the bond and reduction definitions. -/
theorem main : AKLT.Cert.H1.Production.Leaves.compilerGeometry := by
  intro a ha ss hgeom htables
  have hs := geometry_specs hgeom
  have hdimList := dimensions_map hgeom
  refine ⟨hs.1, ?_⟩
  intro si hsi
  rcases si with ⟨s,i⟩
  have hi : i < 8 := by
    have h := List.snd_lt_of_mem_zipIdx hsi
    simp only [Nat.add_zero, hs.1] at h
    exact h
  have hspec : s.spec = inputSpec a i := hs.2 (s,i) hsi
  have hstride : s.spec.stride = ((ss.drop (i+1)).map (fun t => t.spec.dim)).prod := by
    have hsuffix : (ss.drop (i+1)).map (fun t => t.spec.dim) =
        ((List.range 8).drop (i+1)).map (inputDimension a) := by
      calc
        _ = (ss.map (fun t => t.spec.dim)).drop (i+1) := List.map_drop
        _ = ((List.range 8).map (inputDimension a)).drop (i+1) := by rw [hdimList]
        _ = _ := List.map_drop.symm
    have h := congrArg SiteSpec.stride hspec
    simpa only [inputSpec, hsuffix] using h
  have htable : tableCheck s.spec s.table = true :=
    tablesAccepted_mem htables (List.fst_mem_of_mem_zipIdx hsi)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,hstride,htable⟩ <;> rw [hspec]
  · exact input_left a ha i hi
  · exact input_right a ha i hi
  · exact input_center a ha i hi
  · exact inputSlots_eq a ha i hi
  · exact input_dim a ha i hi
  · exact input_diluted a i hi
  · exact input_leaf a ha i hi
  · exact input_tip a ha i hi
  · exact input_inverted a i hi

#print axioms main

end AKLT.W.H1C009
