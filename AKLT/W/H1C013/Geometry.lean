module
public import AKLT.W.H1C013.Digits

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators

namespace AKLT.W.H1C013
open AKLT.Defs AKLT.Cert.H1 AKLT.Cert.H1.Production

def zeroSite : PackedSite := ⟨⟨1,false,false,false,0,false,false,false,false,1⟩,.empty⟩
def siteAt (ss : List PackedSite) (i : Nat) : PackedSite := ss.getD i zeroSite

theorem list_sites (ss : List PackedSite) (hl : ss.length = 8) :
    ss = positions.map (siteAt ss) := by
  apply List.ext_getElem
  · simp [positions, hl]
  · intro i hi hi'
    simp only [List.getElem_map, positions, List.getElem_range]
    exact (List.getD_eq_getElem ss zeroSite hi).symm

/-- Only the coordinate fields used by the basis enumeration. -/
def CoordinateGeometry (π : PatternData) (r : Representation) (ss : List PackedSite) : Prop :=
  ss.length = 8 ∧ ∀ i : Nat, i < 8 →
    (siteAt ss i).spec.nslots = groupSlots π r (groupPoint i) ∧
    (siteAt ss i).spec.dim = groupDim π r (groupPoint i) ∧
    (siteAt ss i).spec.diluted = decide (π.statusAt (ringSites.getD i (0,0)) = .D) ∧
    (siteAt ss i).spec.stride = ((ss.drop (i+1)).map (fun s => s.spec.dim)).prod

theorem geometry_at (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss) (i : Nat) (hi : i < 8) :
    (siteAt ss i).spec.nslots = groupSlots π r (groupPoint i) ∧
    (siteAt ss i).spec.dim = groupDim π r (groupPoint i) ∧
    (siteAt ss i).spec.diluted = decide (π.statusAt (ringSites.getD i (0,0)) = .D) ∧
    (siteAt ss i).spec.stride = ((ss.drop (i+1)).map (fun s => s.spec.dim)).prod := hg.2 i hi

theorem paired_point (π : PatternData) (r : Representation) (i : Nat) (hi : i < 8)
    (hp : groupIsPair π r (groupPoint i) = true) :
    groupPoint i = ringSites.getD i (0,0) := by
  classical
  have hc : groupPoint i ∈ templateCorners := (of_decide_eq_true hp).1
  interval_cases i <;> first | rfl | norm_num [groupPoint, ringSites, templateCorners] at hc

theorem geometry_dims (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss) :
    ss.map (fun s => s.spec.dim) = positions.map (fun i => groupDim π r (groupPoint i)) := by
  rw [list_sites ss hg.1, List.map_map]
  apply List.map_congr_left
  intro i hi
  exact (geometry_at π r ss hg i (by simpa [positions] using hi)).2.1

theorem geometry_digit (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss)
    (f : Nat → Nat) (hf : ∀ i ∈ positions, f i < groupDim π r (groupPoint i))
    (i : Nat) (hi : i < 8) :
    radix positions (fun i => groupDim π r (groupPoint i)) f /
      (siteAt ss i).spec.stride % (siteAt ss i).spec.dim = f i := by
  obtain ⟨hn,hd,hdu,hst⟩ := geometry_at π r ss hg i hi
  rw [hd, hst, List.map_drop, geometry_dims π r ss hg, ← List.map_drop]
  have h := radix_digit positions (fun i => groupDim π r (groupPoint i)) f hf i
    (by simpa [positions] using hi)
  simpa only [positions, List.getElem_range] using h

theorem geometry_weight (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss)
    (f : Nat → Nat) (i : Nat) (hi : i < 8) :
    localWeight (siteAt ss i).spec (f i) = digitWeight π r f i := by
  obtain ⟨hn,hd,hdu,hst⟩ := geometry_at π r ss hg i hi
  rw [localWeight, hn]
  by_cases hx : groupPoint i ∈ reductionGroups π <;>
    cases hp : groupIsPair π r (groupPoint i) <;>
    simp [groupSlots, digitWeight, hx, hp]

theorem geometry_bit (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss)
    (f : Nat → Nat) (i : Nat) (hi : i < 8)
    (hx : groupPoint i ∈ reductionGroups π) :
    (if (siteAt ss i).spec.nslots == 2 && (siteAt ss i).spec.diluted && f i == 3
      then 1 else 0) = digitBit π r f i := by
  obtain ⟨hn,hd,hdu,hst⟩ := geometry_at π r ss hg i hi
  rw [hn]
  cases hp : groupIsPair π r (groupPoint i)
  · simp [groupSlots, hx, hp, digitBit]
  · have he := paired_point π r i hi hp
    rw [hdu, ← he]
    simp [groupSlots, hx, hp, digitBit, and_assoc]

theorem fold_label {α : Type*} (xs : List α) (active : α → Bool)
    (bit : α → Nat) (w : α → Int) (p : Nat) (z : Int) :
    xs.foldl (fun a x => (if active x then 2*a.1 + bit x else a.1, a.2+w x)) (p,z) =
      ((xs.filter active).foldl (fun a x => 2*a+bit x) p, z+(xs.map w).sum) := by
  induction xs generalizing p z with
  | nil => simp
  | cons x xs ih =>
    cases hx : active x <;> simp [hx, ih, add_assoc]

theorem geometry_label (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss)
    (f : Nat → Nat) (hf : ∀ i ∈ positions, f i < groupDim π r (groupPoint i)) :
    sectorLabel ss (radix positions (fun i => groupDim π r (groupPoint i)) f) =
      (radix (activePositions π) (fun _ => 2) (digitBit π r f),
        (positions.map (digitWeight π r f)).sum) := by
  classical
  unfold sectorLabel
  rw [list_sites ss hg.1, List.foldl_map]
  have he := foldl_congr_mem positions
    (fun a i =>
      let s := siteAt ss i
      let d := radix positions (fun i => groupDim π r (groupPoint i)) f / s.spec.stride % s.spec.dim
      (if s.spec.nslots == 0 then a.1 else
        2*a.1 + (if s.spec.nslots == 2 && s.spec.diluted && d == 3 then 1 else 0),
        a.2 + localWeight s.spec d))
    (fun a i =>
      (if groupPoint i ∈ reductionGroups π then 2*a.1 + digitBit π r f i else a.1,
        a.2 + digitWeight π r f i)) ?_ (0,0)
  · rw [he]
    simpa only [decide_eq_true_eq, zero_add, radix, activePositions, Nat.mul_comm] using
      fold_label positions (fun i => decide (groupPoint i ∈ reductionGroups π))
        (digitBit π r f) (digitWeight π r f) 0 0
  · intro a i hi
    have hi' : i < 8 := by simpa [positions] using hi
    dsimp only
    rw [geometry_digit π r ss hg f hf i hi', geometry_weight π r ss hg f i hi']
    obtain ⟨hn,hd,hdu,hst⟩ := geometry_at π r ss hg i hi'
    by_cases hx : groupPoint i ∈ reductionGroups π
    · rw [geometry_bit π r ss hg f i hi' hx, hn]
      cases hp : groupIsPair π r (groupPoint i) <;> simp [groupSlots, hx, hp]
    · rw [hn]
      simp [groupSlots, hx]

theorem geometry_centralWeight (π : PatternData) (r : Representation)
    (ss : List PackedSite) (hg : CoordinateGeometry π r ss) :
    (AKLT.Cert.H1.Production.centralWeight ss : ℚ) = 2 * AKLT.Defs.centralWeight π r := by
  classical
  have hn : (ss.filter (fun s => s.spec.nslots == 1)).length =
      (positions.filter (fun i => groupSlots π r (groupPoint i) == 1)).length := by
    rw [list_sites ss hg.1, List.filter_map, List.length_map]
    congr 1
    apply List.filter_congr
    intro i hi
    dsimp only [Function.comp_apply]
    rw [(geometry_at π r ss hg i (by simpa [positions] using hi)).1]
  unfold AKLT.Cert.H1.Production.centralWeight AKLT.Defs.centralWeight
  rw [hn, single_count]
  simp only [Nat.even_iff, beq_iff_eq]
  split_ifs <;> norm_num

end AKLT.W.H1C013
