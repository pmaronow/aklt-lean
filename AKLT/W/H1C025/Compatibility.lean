module
public import AKLT.W.H1C025.Extraction

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C025
open AKLT.Defs AKLT.Cert.H1.Production AKLT.Cert.H1

def cornerPoint (i : Fin 4) : Plane :=
  ([(1,1),(-1,1),(-1,-1),(1,-1)] : List Plane).getD i.val (0,0)

theorem cornerPoint_facts (i : Fin 4) :
    cornerPoint i ∈ templateCorners ∧ cornerPoint i ∈ templateSites := by
  fin_cases i <;> norm_num [cornerPoint, templateCorners, templateSites, square, latticeDist]

theorem compatible_pair (π : PatternData) (hπ : π.Covered) (x y : Plane)
    (d e : Nat) (hd : d < 4) (he : e < 4)
    (hx : x ∈ templateSites) (hy : y ∈ templateSites)
    (hx0 : x ≠ (0,0)) (hy0 : y ≠ (0,0))
    (hxt : x ∉ templateTips) (hyt : y ∉ templateTips)
    (hxy : dirPoint x ⟨d,hd⟩ = y) (hyx : dirPoint y ⟨e,he⟩ = x)
    (ha : Adjacent x y) :
    ((rawOptionAt π x).status = 0 ∨ (rawOptionAt π y).status = 0) ∨
      hasDirection (rawOptionAt π x).mask d =
        hasDirection (rawOptionAt π y).mask e := by
  by_cases hsx : π.statusAt x = .X
  · simp [rawOption_status, hsx, statusDigit]
  by_cases hsy : π.statusAt y = .X
  · simp [rawOption_status, hsy, statusDigit]
  right
  rw [rawOption_direction π hπ x hx hx0 hxt hsx ⟨d,hd⟩,
    rawOption_direction π hπ y hy hy0 hyt hsy ⟨e,he⟩]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, hxy, hyx]
  exact hπ.2.2.2.2.2.2.2.2.2 x (Finset.mem_sdiff.mpr ⟨hx,hxt⟩)
    y (Finset.mem_sdiff.mpr ⟨hy,hyt⟩) hsx hsy ha

theorem corner_compatible (π : PatternData) (hπ : π.Covered) (i : Fin 4) :
    cornerCompatible (axesOf π) i.val (rawOptionAt π (cornerPoint i)) = true := by
  fin_cases i <;>
    norm_num [cornerCompatible, cornerAdjacency, axesOf, cornerPoint, Bool.and_eq_true]
  all_goals constructor
  all_goals apply compatible_pair π hπ
  all_goals norm_num [templateSites, square, latticeDist, templateTips, Adjacent,
    dirPoint, compassAt, Compass.step, Prod.mk_add_mk]

theorem corners_valid (π : PatternData) (hπ : π.Covered) :
    (cornersOf π).zipIdx.all (fun (x,i) =>
      cornerOptions.contains x && cornerCompatible (axesOf π) i x) = true := by
  have h0 := rawOption_corner π hπ _ (cornerPoint_facts 0).1 (cornerPoint_facts 0).2
  have h1 := rawOption_corner π hπ _ (cornerPoint_facts 1).1 (cornerPoint_facts 1).2
  have h2 := rawOption_corner π hπ _ (cornerPoint_facts 2).1 (cornerPoint_facts 2).2
  have h3 := rawOption_corner π hπ _ (cornerPoint_facts 3).1 (cornerPoint_facts 3).2
  have c0 := corner_compatible π hπ 0
  have c1 := corner_compatible π hπ 1
  have c2 := corner_compatible π hπ 2
  have c3 := corner_compatible π hπ 3
  simp only [cornerPoint] at h0 h1 h2 h3 c0 c1 c2 c3
  simpa [cornersOf, List.zipIdx_cons', List.contains_iff_mem] using
    And.intro (And.intro h0 c0) (And.intro (And.intro h1 c1)
      (And.intro (And.intro h2 c2) (And.intro h3 c3)))

#print axioms cornerPoint_facts
#print axioms compatible_pair
#print axioms corner_compatible
#print axioms corners_valid

end AKLT.W.H1C025
