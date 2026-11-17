module
public import AKLT.Cert.H1.Production.Leaves
public import AKLT.Cert.H1.Production.Semantics

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C019

open AKLT.Cert.H1.Production
open AKLT.Cert.H1

private def dummySpec : AKLT.Cert.H1.SiteSpec :=
  ⟨0, false, false, false, 0, false, false, false, false, 0⟩

private def dummyPacked : AKLT.Cert.H1.PackedSite :=
  ⟨dummySpec, AKLT.Cert.H1.Table.empty⟩

private def dummySector : SectorSite := ⟨dummyPacked, [], 0⟩

private instance : Inhabited AKLT.Cert.H1.PackedSite := ⟨dummyPacked⟩
private instance : Inhabited SectorSite := ⟨dummySector⟩

private theorem siteSpec_eq_of_beq {a b : AKLT.Cert.H1.SiteSpec}
    (h : (a == b) = true) : a = b := by
  cases a with
  | mk ad al ar ac an adi alf atip ainv astride =>
    cases b with
    | mk bd bl br bc bn bdi blf btip binv bstride =>
      change AKLT.Cert.H1.instBEqSiteSpec.beq _ _ = true at h
      simp only [AKLT.Cert.H1.instBEqSiteSpec.beq, Bool.and_eq_true,
        beq_iff_eq] at h
      rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      rfl

private theorem gaussian_eq_of_beq {a b : Gaussian} (h : (a == b) = true) :
    a = b := by
  cases a with
  | mk ar ai =>
    cases b with
    | mk br bi =>
      change AKLT.Cert.H1.instBEqGaussian.beq _ _ = true at h
      simp only [AKLT.Cert.H1.instBEqGaussian.beq, Bool.and_eq_true,
        beq_iff_eq] at h
      rcases h with ⟨rfl, rfl⟩
      rfl

private theorem table_eq_of_beq : ∀ a b : Table, (a == b) = true → a = b := by
  intro a
  induction a with
  | empty =>
    intro b h
    cases b with
    | empty => rfl
    | leaf g => change false = true at h; cases h
    | node cut l r => change false = true at h; cases h
  | leaf x =>
    intro b h
    cases b with
    | empty => change false = true at h; cases h
    | leaf y =>
      change (x == y) = true at h
      exact congrArg Table.leaf (gaussian_eq_of_beq h)
    | node cut l r => change false = true at h; cases h
  | node cut l r ihl ihr =>
    intro b h
    cases b with
    | empty => change false = true at h; cases h
    | leaf y => change false = true at h; cases h
    | node cut' l' r' =>
      change ((cut == cut') && ((l == l') && (r == r'))) = true at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      rcases h with ⟨rfl, hl, hr⟩
      have hleft := ihl l' hl
      have hright := ihr r' hr
      cases hleft
      cases hright
      rfl

private def radixPack {α : Type} (radix digit : α → Nat) (xs : List α)
    (acc : Nat) : Nat :=
  xs.foldl (fun a x => a * radix x + digit x) acc

private theorem radixPack_affine {α : Type} (radix digit : α → Nat)
    (xs : List α) (acc : Nat) :
    radixPack radix digit xs acc =
      acc * (xs.map radix).prod + radixPack radix digit xs 0 := by
  induction xs generalizing acc with
  | nil => simp [radixPack]
  | cons x xs ih =>
      simp only [radixPack, List.foldl_cons, List.map_cons, List.prod_cons,
        Nat.zero_mul, Nat.zero_add] at *
      rw [ih (acc * radix x + digit x), ih (digit x)]
      ring

private theorem radixPack_lt {α : Type} (radix digit : α → Nat)
    (xs : List α) (hd : ∀ x ∈ xs, digit x < radix x) :
    radixPack radix digit xs 0 < (xs.map radix).prod := by
  induction xs with
  | nil => simp [radixPack]
  | cons x xs ih =>
      have hx := hd x (by simp)
      have ht := ih (fun y hy => hd y (by simp [hy]))
      have hp : 0 < (xs.map radix).prod := by omega
      change radixPack radix digit xs (0 * radix x + digit x) < _
      rw [Nat.zero_mul, Nat.zero_add, radixPack_affine]
      simp only [List.map_cons, List.prod_cons]
      have hmul := Nat.mul_le_mul_right (xs.map radix).prod (Nat.succ_le_of_lt hx)
      nlinarith

private theorem radixPack_digit {α : Type} (radix digit : α → Nat)
    (xs : List α) (acc : Nat) (hd : ∀ x ∈ xs, digit x < radix x)
    (k : Nat) (hk : k < xs.length) :
    radixPack radix digit xs acc / ((xs.drop (k+1)).map radix).prod % radix xs[k] =
      digit xs[k] := by
  induction xs generalizing acc k with
  | nil => simp at hk
  | cons x xs ih =>
      have ht : ∀ y ∈ xs, digit y < radix y := fun y hy => hd y (by simp [hy])
      cases k with
      | zero =>
          have hx := hd x (by simp)
          have hlt := radixPack_lt radix digit xs ht
          have hp : 0 < (xs.map radix).prod := by omega
          simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero]
          change radixPack radix digit xs (acc * radix x + digit x) /
            (xs.map radix).prod % radix x = digit x
          rw [radixPack_affine]
          have hdiv : ((acc * radix x + digit x) * (xs.map radix).prod +
              radixPack radix digit xs 0) / (xs.map radix).prod =
              acc * radix x + digit x := by
            apply Nat.div_eq_of_lt_le <;> nlinarith
          rw [hdiv]
          simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero,
            Nat.zero_mod, Nat.zero_add, Nat.mod_eq_of_lt hx]
      | succ k =>
          simpa only [radixPack, List.foldl_cons, List.drop_succ_cons,
            List.getElem_cons_succ] using
            ih (acc * radix x + digit x) ht k (by simpa using hk)

private def parityRadix (s : PackedSite) : Nat :=
  if s.spec.nslots == 0 then 1 else 2

private def parityDigit (index : Nat) (s : PackedSite) : Nat :=
  if s.spec.nslots == 0 then 0 else
    if s.spec.nslots == 2 && s.spec.diluted &&
        index / s.spec.stride % s.spec.dim == 3 then 1 else 0

private theorem parityDigit_lt (index : Nat) (s : PackedSite) :
    parityDigit index s < parityRadix s := by
  by_cases h : s.spec.nslots = 0
  · simp [parityDigit, parityRadix, h]
  · simp only [parityDigit, parityRadix, beq_iff_eq, h, ↓reduceIte]
    split <;> omega

private theorem sectorLabel_fst (ss : List PackedSite) (index : Nat) :
    (sectorLabel ss index).1 = radixPack parityRadix (parityDigit index) ss 0 := by
  unfold sectorLabel radixPack
  symm
  apply List.foldl_hom (Prod.fst : Nat × Int → Nat) (init := (0, 0)) (l := ss)
  intro a s
  by_cases h : s.spec.nslots = 0
  · simp [parityRadix, parityDigit, h]
  · simp [parityRadix, parityDigit, h, Nat.mul_comm]

private theorem parityRadix_prod (ss : List PackedSite) :
    (ss.map parityRadix).prod =
      2 ^ (ss.filter (fun t => t.spec.nslots != 0)).length := by
  induction ss with
  | nil => simp
  | cons s ss ih =>
      by_cases h : s.spec.nslots = 0
      · simp [parityRadix, h, ih]
      · simp [parityRadix, h, ih, pow_succ, Nat.mul_comm]

private theorem parityBit_eq {ss : List PackedSite} {index parity k : Nat}
    (hpar : (sectorLabel ss index).1 = parity) (hk : k < ss.length)
    (hactive : ss[k].spec.nslots ≠ 0) :
    parity / 2 ^ ((ss.drop (k+1)).filter (fun t => t.spec.nslots != 0)).length % 2 =
      parityDigit index ss[k] := by
  have h := radixPack_digit parityRadix (parityDigit index) ss 0
    (fun s _ => parityDigit_lt index s) k hk
  rw [← sectorLabel_fst, hpar, parityRadix_prod] at h
  simpa only [parityRadix, beq_iff_eq, hactive, ↓reduceIte] using h

private theorem sectorNetwork_length {base : List PackedSite} {parity : Nat}
    {ss : List SectorSite} (h : sectorNetworkCheck base parity ss = true) :
    ss.length = base.length := by
  simp only [sectorNetworkCheck, Bool.and_eq_true] at h
  exact (beq_iff_eq).mp h.1

private theorem sectorNetwork_site {base : List PackedSite} {parity : Nat}
    {ss : List SectorSite} (h : sectorNetworkCheck base parity ss = true)
    (k : Nat) (hk : k < base.length) (hs : k < ss.length) :
    ss[k].base = base[k] ∧
    ss[k].coordinates = sectorCoordinates base[k].spec
      (parity / 2 ^ ((base.drop (k+1)).filter (fun t => t.spec.nslots != 0)).length % 2) ∧
    ss[k].stride = ((ss.drop (k+1)).map (fun t => t.coordinates.length)).prod := by
  have hzip : k < (base.zip ss).length := by simp [hk, hs]
  have hmem : ((base[k], ss[k]), k) ∈ (base.zip ss).zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    rw [List.getElem?_eq_getElem hzip]
    simp only [List.getElem_zip]
  simp only [sectorNetworkCheck, Bool.and_eq_true, List.all_eq_true] at h
  rcases h.2 _ hmem with ⟨⟨⟨hSpec, hTable⟩, hCoords⟩, hStride⟩
  refine ⟨?_, (beq_iff_eq).mp hCoords, (beq_iff_eq).mp hStride⟩
  have hspec := siteSpec_eq_of_beq hSpec
  have htable := table_eq_of_beq _ _ hTable
  cases hl : ss[k].base with
  | mk ls lt =>
      cases hr : base[k] with
      | mk rs rt =>
          simp only [hl, hr] at hspec htable
          cases hspec
          cases htable
          rfl

private theorem metadata_dim {c : Case} (hc : c.MetadataAccepted)
    (k : Nat) (hk : k < c.network.length) :
    0 < c.network[k].spec.dim ∧
      (c.network[k].spec.nslots = 2 → c.network[k].spec.diluted = true →
        c.network[k].spec.dim = 4) := by
  have h := hc.2.2.2.1
  simp only [parametersCheck, Bool.and_eq_true, List.all_eq_true] at h
  have hm : (c.network[k], k) ∈ c.network.zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    exact List.getElem?_eq_getElem hk
  have hs := h.2 _ hm
  simp only [beq_iff_eq, decide_eq_true_eq] at hs
  refine ⟨hs.1.1.1.1, ?_⟩
  intro hn hd
  have heq := hs.1.1.2
  simpa [hn, hd] using heq

private theorem sectorLabel_of_basis {base : List PackedSite}
    {parity : Nat} {weight : Int} {indices : List Nat}
    (hb : basisCheck base parity weight indices = true)
    {index : Nat} (hi : index ∈ indices) :
    (sectorLabel base index).1 = parity := by
  simp only [basisCheck, Bool.and_eq_true, beq_iff_eq] at hb
  rw [hb.1.2] at hi
  have hfilter := (List.mem_filter.mp hi).2
  have heq : sectorLabel base index = (parity, weight) := (beq_iff_eq).mp hfilter
  exact congrArg Prod.fst heq

private theorem original_digit_mem {c : Case} (hc : c.MetadataAccepted)
    {parity index : Nat} (hpar : (sectorLabel c.network index).1 = parity)
    (k : Nat) (hk : k < c.network.length) :
    index / c.network[k].spec.stride % c.network[k].spec.dim ∈
      sectorCoordinates c.network[k].spec
        (parity / 2 ^ ((c.network.drop (k+1)).filter
          (fun t => t.spec.nslots != 0)).length % 2) := by
  have hdim := metadata_dim hc k hk
  have hbound := Nat.mod_lt (index / c.network[k].spec.stride) hdim.1
  by_cases hD : c.network[k].spec.nslots = 2 ∧ c.network[k].spec.diluted = true
  · have hbit := parityBit_eq hpar hk (by omega)
    have hfour := hdim.2 hD.1 hD.2
    by_cases hdigit : index / c.network[k].spec.stride % c.network[k].spec.dim = 3
    · simp [parityDigit, hD.1, hD.2, hdigit] at hbit
      simp [sectorCoordinates, hD.1, hD.2, hbit, hdigit]
    · simp [parityDigit, hD.1, hD.2, hdigit] at hbit
      simp [sectorCoordinates, hD.1, hD.2, hbit]
      omega
  · have hnot : (c.network[k].spec.nslots == 2 && c.network[k].spec.diluted) = false := by
      cases hd : c.network[k].spec.diluted <;> simp_all
    simp only [sectorCoordinates, hnot, Bool.false_eq_true, ↓reduceIte,
      List.mem_range]
    exact hbound

private theorem remap_coordinate {c : Case} (hc : c.MetadataAccepted)
    {b : Bundle} (hb : b.LayoutAccepted c) {index : Nat}
    (hi : index ∈ b.block.indices) (k : Nat) (hk : k < b.sector.length) :
    b.sector[k].coordinates.getD
        (remapIndex c.network b.sector index / b.sector[k].stride %
          b.sector[k].coordinates.length) 0 =
      index / (c.network.getD k default).spec.stride %
        (c.network.getD k default).spec.dim := by
  have hlen := sectorNetwork_length hb.2.1
  have hkbase : k < c.network.length := by omega
  have hpar := sectorLabel_of_basis hb.1 hi
  have hmem (t : Nat) (ht : t < c.network.length) (hts : t < b.sector.length) :
      index / c.network[t].spec.stride % c.network[t].spec.dim ∈
        b.sector[t].coordinates := by
    rw [(sectorNetwork_site hb.2.1 t ht hts).2.1]
    exact original_digit_mem hc hpar t ht
  let radix : PackedSite × SectorSite → Nat := fun p => p.2.coordinates.length
  let digit : PackedSite × SectorSite → Nat := fun p =>
    p.2.coordinates.idxOf (index / p.1.spec.stride % p.1.spec.dim)
  have hd : ∀ p ∈ c.network.zip b.sector, digit p < radix p := by
    intro p hp
    obtain ⟨t, ht, heq⟩ := List.getElem_of_mem hp
    rw [← heq, List.getElem_zip]
    exact List.idxOf_lt_length_of_mem
      (hmem t (List.lt_length_left_of_zip ht) (List.lt_length_right_of_zip ht))
  have hzip : k < (c.network.zip b.sector).length := by simp [hk, hkbase]
  have hdecode := radixPack_digit radix digit (c.network.zip b.sector) 0 hd k hzip
  have hmap : (c.network.zip b.sector).map Prod.snd = b.sector :=
    List.map_snd_zip (by omega)
  have hprod : (((c.network.zip b.sector).drop (k+1)).map radix).prod =
      ((b.sector.drop (k+1)).map (fun s => s.coordinates.length)).prod := by
    have hdrop := congrArg (fun xs : List SectorSite => xs.drop (k+1)) hmap
    rw [← List.map_drop] at hdrop
    have hm := congrArg (List.map (fun s : SectorSite => s.coordinates.length)) hdrop
    simp only [List.map_map, Function.comp_def] at hm
    exact congrArg List.prod hm
  change remapIndex c.network b.sector index /
    (((c.network.zip b.sector).drop (k+1)).map radix).prod %
      radix (c.network.zip b.sector)[k] = digit (c.network.zip b.sector)[k] at hdecode
  rw [hprod, List.getElem_zip] at hdecode
  dsimp only [radix, digit] at hdecode
  rw [← (sectorNetwork_site hb.2.1 k hkbase hk).2.2] at hdecode
  rw [hdecode, List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem
    (hmem k hkbase hk)), List.getElem_idxOf]
  rw [List.getD_eq_getElem _ _ hkbase]

/-- The remapped sector coordinates select the original local basis digit. -/
private def CoordinateDigits : Prop :=
  ∀ c : Case, c.MetadataAccepted → ∀ b : Bundle, b.LayoutAccepted c →
    ∀ i j : Fin b.block.M.length,
      ∀ k : Nat, k < b.sector.length →
        let s := b.sector.getD k default
        let base := c.network.getD k default
        s.coordinates.getD
            (b.mapped.getD i 0 / s.stride % s.coordinates.length) 0 =
          b.block.indices.getD i 0 / base.spec.stride % base.spec.dim ∧
        s.coordinates.getD
            (b.mapped.getD j 0 / s.stride % s.coordinates.length) 0 =
          b.block.indices.getD j 0 / base.spec.stride % base.spec.dim

private theorem coordinateDigits : CoordinateDigits := by
  intro c hc b hb i j k hk
  have hremap : b.block.indices.map (remapIndex c.network b.sector) = b.mapped := by
    exact (beq_iff_eq).mp hb.2.2.1
  have hcoord (t : Fin b.block.M.length) :
      (b.sector.getD k default).coordinates.getD
          (b.mapped.getD t 0 / (b.sector.getD k default).stride %
            (b.sector.getD k default).coordinates.length) 0 =
        b.block.indices.getD t 0 / (c.network.getD k default).spec.stride %
          (c.network.getD k default).spec.dim := by
    have ht : t.val < b.block.indices.length := by
      rw [hb.2.2.2.1]
      exact t.isLt
    have hi : b.block.indices.getD t 0 ∈ b.block.indices := by
      rw [List.getD_eq_getElem _ _ ht]
      exact List.getElem_mem ht
    have hmapped : b.mapped.getD t 0 =
        remapIndex c.network b.sector (b.block.indices.getD t 0) := by
      rw [← hremap, List.getD_eq_getElem _ _ (by simpa only [List.length_map] using ht),
        List.getElem_map, List.getD_eq_getElem _ _ ht]
    rw [List.getD_eq_getElem _ _ hk, hmapped]
    exact remap_coordinate hc hb hi k hk
  exact ⟨hcoord i, hcoord j⟩

private theorem sectorSiteMatrix_eq_of_coordinates {s : SectorSite}
    {base : PackedSite} {rowS colS rowB colB v : Nat}
    (hbase : s.base = base)
    (hrow : s.coordinates.getD (rowS / s.stride % s.coordinates.length) 0 =
      rowB / base.spec.stride % base.spec.dim)
    (hcol : s.coordinates.getD (colS / s.stride % s.coordinates.length) 0 =
      colB / base.spec.stride % base.spec.dim) :
    directSectorSiteMatrix s rowS colS v = directSiteMatrix base rowB colB v := by
  subst base
  unfold directSectorSiteMatrix directSiteMatrix
  rw [hrow, hcol]

private theorem baseProjection_of_sectorNetworkCheck {base : List PackedSite}
    {parity : Nat} {ss : List SectorSite}
    (hcheck : sectorNetworkCheck base parity ss = true) :
    ss.map SectorSite.base = base := by
  classical
  simp only [sectorNetworkCheck, Bool.and_eq_true, List.all_eq_true] at hcheck
  have hlen : ss.length = base.length := (beq_iff_eq).mp hcheck.1
  apply List.ext_getElem
  · simp [hlen]
  · intro k hmap hbase
    have hss : k < ss.length := by simpa using hmap
    have hzip : k < (base.zip ss).length := by simp [hbase, hss]
    have hp : ((base[k], ss[k]), k) ∈ (base.zip ss).zipIdx := by
      apply List.mem_zipIdx_iff_getElem?.mpr
      rw [List.getElem?_eq_getElem hzip]
      simp only [List.getElem_zip]
    have hs := hcheck.2 _ hp
    rcases hs with ⟨⟨⟨hSpec, hTable⟩, _hCoords⟩, _hStride⟩
    have hsite : ss[k].base = base[k] := by
      have hs := siteSpec_eq_of_beq hSpec
      have ht := table_eq_of_beq (ss[k].base.table) (base[k].table) hTable
      cases hleft : ss[k].base with
      | mk ls lt =>
        cases hright : base[k] with
        | mk rs rt =>
          simp only [hleft, hright] at hs ht
          cases hs
          cases ht
          rfl
    rw [List.getElem_map]
    exact hsite

private theorem sectorRingProduct_eq (ss : List SectorSite)
    (rowS colS rowB colB : Nat)
    (codes : List Nat)
    (hlocal : ∀ k : Nat, k < ss.length →
      directSectorSiteMatrix (ss.getD k default) rowS colS (codes.getD k 0) =
        directSiteMatrix ((ss.map SectorSite.base).getD k default) rowB colB
          (codes.getD k 0)) :
    directSectorRingProduct rowS colS ss codes =
      directRingProduct rowB colB (ss.map SectorSite.base) codes := by
  induction ss generalizing codes with
  | nil => rfl
  | cons s ss ih =>
      cases codes with
      | nil =>
          simp only [directSectorRingProduct, directRingProduct, List.headD,
            List.tail, List.map]
          have h0 := hlocal 0 (by simp)
          have htail : ∀ k : Nat, k < ss.length →
              directSectorSiteMatrix (ss.getD k default) rowS colS 0 =
                directSiteMatrix ((ss.map SectorSite.base).getD k default) rowB colB 0 := by
            intro k hk
            have := hlocal (k+1) (by simp; omega)
            simpa using this
          have hrec := ih (codes := []) htail
          have h0' : directSectorSiteMatrix s rowS colS 0 =
                directSiteMatrix s.base rowB colB 0 := by simpa using h0
          rw [h0', hrec]
      | cons code codes =>
          simp only [directSectorRingProduct, directRingProduct, List.headD,
            List.tail, List.map]
          have h0 := hlocal 0 (by simp)
          have htail : ∀ k : Nat, k < ss.length →
              directSectorSiteMatrix (ss.getD k default) rowS colS
                  ((code :: codes).getD (k+1) 0) =
                directSiteMatrix ((ss.map SectorSite.base).getD k default) rowB colB
                  ((code :: codes).getD (k+1) 0) := by
            intro k hk
            have := hlocal (k+1) (by simp; omega)
            simpa only [List.getD_cons_succ, List.map] using this
          have hrec := ih (codes := codes) htail
          have h0' : directSectorSiteMatrix s rowS colS code =
                directSiteMatrix s.base rowB colB code := by simpa using h0
          rw [h0', hrec]

private theorem sectorRingValue_eq (ss : List SectorSite)
    (rowS colS rowB colB : Nat)
    (codes : List Nat)
    (hlocal : ∀ k : Nat, k < ss.length →
      directSectorSiteMatrix (ss.getD k default) rowS colS (codes.getD k 0) =
        directSiteMatrix ((ss.map SectorSite.base).getD k default) rowB colB
          (codes.getD k 0)) :
    directSectorRingValue ss rowS colS codes =
      directRingValue (ss.map SectorSite.base) rowB colB codes := by
  unfold directSectorRingValue directRingValue
  rw [sectorRingProduct_eq ss rowS colS rowB colB codes hlocal]

private theorem sectorCurrentNext_eq (ss : List SectorSite) (out : Nat)
    (rowS colS rowB colB : Nat)
    (next : Bool)
    (hlocal : ∀ codes : List Nat, ∀ k : Nat, k < ss.length →
      directSectorSiteMatrix (ss.getD k default) rowS colS (codes.getD k 0) =
        directSiteMatrix ((ss.map SectorSite.base).getD k default) rowB colB
          (codes.getD k 0)) :
    directSectorCurrentNext ss out rowS colS next =
      directCurrentNext (ss.map SectorSite.base) out rowB colB next := by
  have hval (codes : List Nat) :
      directSectorRingValue ss rowS colS codes =
        directRingValue (ss.map SectorSite.base) rowB colB codes := by
    apply sectorRingValue_eq
    intro k hk
    exact hlocal codes k hk
  simp only [directSectorCurrentNext, directCurrentNext]
  simp_rw [hval]
  simp only [List.length_map]

/-- The contraction and all center-code summations preserve a pointwise local
matrix identity. -/
private theorem main_of_coordinateDigits (h : CoordinateDigits) :
    AKLT.Cert.H1.Production.Leaves.paritySlice := by
  intro c hc b hb i j next
  have hbase : b.sector.map SectorSite.base = c.network :=
    baseProjection_of_sectorNetworkCheck hb.2.1
  have hcoords := h c hc b hb i j
  have hlocal (codes : List Nat) (k : Nat) (hk : k < b.sector.length) :
      directSectorSiteMatrix (b.sector.getD k default)
          (b.mapped.getD i 0) (b.mapped.getD j 0) (codes.getD k 0) =
        directSiteMatrix ((b.sector.map SectorSite.base).getD k default)
          (b.block.indices.getD i 0) (b.block.indices.getD j 0) (codes.getD k 0) := by
    have hbaseSite : (b.sector.getD k default).base =
        (b.sector.map SectorSite.base).getD k default := by
      change SectorSite.base (b.sector.getD k (default : SectorSite)) =
        (b.sector.map SectorSite.base).getD k (SectorSite.base (default : SectorSite))
      exact (List.getD_map (l := b.sector) (d := (default : SectorSite))
        (n := k) SectorSite.base).symm
    have hc' := hcoords k hk
    rw [← hbase] at hc'
    exact sectorSiteMatrix_eq_of_coordinates hbaseSite hc'.1 hc'.2
  have hcur (next : Bool) :
      directSectorCurrentNext b.sector c.out (b.mapped.getD i 0)
          (b.mapped.getD j 0) next =
        directCurrentNext c.network c.out (b.block.indices.getD i 0)
          (b.block.indices.getD j 0) next := by
    rw [← hbase]
    apply sectorCurrentNext_eq b.sector c.out (b.mapped.getD i 0)
      (b.mapped.getD j 0) (b.block.indices.getD i 0) (b.block.indices.getD j 0) next
    intro codes k hk
    have hl := hlocal codes k hk
    simpa using hl
  exact hcur next

theorem main : AKLT.Cert.H1.Production.Leaves.paritySlice :=
  main_of_coordinateDigits coordinateDigits

#print axioms main

end AKLT.W.H1C019
