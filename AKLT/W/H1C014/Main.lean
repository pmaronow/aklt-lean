import AKLT.W.H1C014.Sparse
import AKLT.W.H1C014.Layout
import AKLT.W.H1C024.Main

namespace AKLT.W.H1C014

open AKLT.Cert.H1.Production
open AKLT.Cert.H1.Production.Leaves
open AKLT.Cert.H1
open AKLT.Gen.Gram

private theorem gaussian_beq_eq {a b : Gaussian} (h : (a == b) = true) : a = b := by
  cases a with
  | mk ar ai =>
    cases b with
    | mk br bi =>
      change (ar == br && ai == bi) = true at h
      have hh := Bool.and_eq_true_iff.mp h
      have hr : ar = br := (beq_iff_eq).mp hh.1
      have hi : ai = bi := (beq_iff_eq).mp hh.2
      subst br
      subst bi
      rfl

private theorem packedSectorRowCheck_sound
    (ss : List SectorSite) (out width p q row : Nat)
    (indices : List Nat) (expected : List Int)
    (h : packedSectorRowCheck ss out width p q row indices expected = true) :
    indices.length = expected.length ∧
    (∀ a ∈ expected,
      -((2 : Nat)^(width-1) : Int) ≤ a ∧
        a < ((2 : Nat)^(width-1) : Int)) ∧
    packedSectorThresholdRow ss out row width p q =
      ⟨sparsePack width indices expected, 0⟩ := by
  unfold packedSectorRowCheck at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    decide_eq_true_eq] at h
  rcases h with ⟨⟨hlen, hbound⟩, hpacked⟩
  exact ⟨hlen, hbound, gaussian_beq_eq hpacked⟩

private theorem acceptedSectorRow_decode
    (ss : List SectorSite) (out width lanes p q row : Nat)
    (indices : List Nat) (expected : List Int)
    (hw : 0 < width) (hnd : indices.Nodup)
    (hpos : ∀ j ∈ indices, j < lanes)
    (h : packedSectorRowCheck ss out width p q row indices expected = true) :
    constructedSectorRow ss out width lanes p q row indices = expected := by
  obtain ⟨hlen, hbound, hpacked⟩ := packedSectorRowCheck_sound ss out width p q row indices expected h
  have hdigits := signedSparseDecode width lanes hw indices expected hlen hnd hpos hbound
  unfold constructedSectorRow
  have hre : (packedSectorThresholdRow ss out row width p q).re =
      sparsePack width indices expected := by
    exact congrArg Gaussian.re hpacked
  simp only [hre]
  exact hdigits

theorem rows_decode
    (ss : List SectorSite) (out width lanes p q : Nat)
    (columns positions : List Nat) (rows : IntRows)
    (hw : 0 < width) (hnd : columns.Nodup)
    (hpos : ∀ j ∈ columns, j < lanes)
    (hrows : SectorRowsAccepted ss out width p q columns positions rows) :
    positions.map (fun row => constructedSectorRow ss out width lanes p q row columns) = rows := by
  induction positions generalizing rows with
  | nil =>
      cases rows with
      | nil => rfl
      | cons row rows => simp [SectorRowsAccepted] at hrows
  | cons i is ih =>
      cases rows with
      | nil => simp [SectorRowsAccepted] at hrows
      | cons row rows =>
          simp only [SectorRowsAccepted] at hrows
          rcases hrows with ⟨hrow, htail⟩
          have hhead := acceptedSectorRow_decode ss out width lanes p q i
            columns row hw hnd hpos hrow
          have htailEq := ih rows htail
          simp only [List.map_cons]
          rw [hhead]
          rw [htailEq]

/-- Every accepted literal sector row is recovered by the production decoder. -/
theorem main : AKLT.Cert.H1.Production.Leaves.acceptedDecode := by
  unfold AKLT.Cert.H1.Production.Leaves.acceptedDecode
  intro c hc b hb hr
  obtain ⟨hnd, hrange⟩ := layoutIndexing c hc b hb
  have hw : 0 < c.width := (AKLT.W.H1C024.main c hc).2.2
  unfold constructedSectorRows
  have hresult := rows_decode b.sector c.out c.width
    ((b.sector.map (fun s => s.coordinates.length)).prod) c.p c.q
    b.mapped b.mapped b.block.M hw hnd hrange hr
  exact hresult

#print axioms rows_decode
#print axioms main

end AKLT.W.H1C014
