import AKLT.Cert.H1.Production.Leaves

namespace AKLT.W.H1C014

open AKLT.Cert.H1 AKLT.Cert.H1.Production

private def baseLanes (bs : List PackedSite) : Nat :=
  (bs.map (fun b => b.spec.dim)).prod

private def groups (bs : List PackedSite) : Nat :=
  (bs.filter (fun b => b.spec.nslots != 0)).length

private def digit (b : PackedSite) (index : Nat) : Nat :=
  index / b.spec.stride % b.spec.dim

private def BaseInfo : List PackedSite → Prop
  | [] => True
  | b :: bs => 0 < b.spec.dim ∧
      (b.spec.nslots = 2 → b.spec.diluted = true → b.spec.dim = 4) ∧
      b.spec.stride = baseLanes bs ∧ BaseInfo bs

private theorem baseInfo_of_indexed (bs : List PackedSite)
    (h : ∀ (i : Nat) (hi : i < bs.length),
      0 < bs[i].spec.dim ∧
      (bs[i].spec.nslots = 2 → bs[i].spec.diluted = true → bs[i].spec.dim = 4) ∧
      bs[i].spec.stride = baseLanes (bs.drop (i+1))) : BaseInfo bs := by
  induction bs with
  | nil => trivial
  | cons b bs ih =>
      have h0 := h 0 (by simp)
      simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero] at h0
      refine ⟨h0.1, h0.2.1, h0.2.2, ih ?_⟩
      intro i hi
      have ht := h (i+1) (by simpa using Nat.succ_lt_succ hi)
      simpa only [List.getElem_cons_succ, List.drop_succ_cons] using ht

private theorem baseInfo_of_parameters (bs : List PackedSite)
    (out width lanes den p q : Nat)
    (h : parametersCheck bs out width lanes den p q = true) : BaseInfo bs := by
  have hall := (Bool.and_eq_true_iff.mp h).2
  apply baseInfo_of_indexed
  intro i hi
  have hs := List.forall_mem_zipIdx'.mp (List.all_eq_true.mp hall) i hi
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hs
  refine ⟨hs.1.1.1.1, ?_, hs.1.2⟩
  intro hn hd
  have hdim := hs.1.1.2
  simpa [hn, hd] using hdim

private def CoordInfo : List PackedSite → List SectorSite → Nat → Prop
  | [], [], _ => True
  | b :: bs, s :: ss, parity =>
      s.coordinates = sectorCoordinates b.spec (parity / 2^groups bs % 2) ∧
        CoordInfo bs ss parity
  | _, _, _ => False

private theorem coordInfo_of_indexed (bs : List PackedSite) (ss : List SectorSite)
    (parity : Nat) (hlen : ss.length = bs.length)
    (h : ∀ (i : Nat) (hi : i < bs.length),
      (ss[i]'(by omega)).coordinates =
        sectorCoordinates bs[i].spec (parity / 2^groups (bs.drop (i+1)) % 2)) :
    CoordInfo bs ss parity := by
  induction bs generalizing ss with
  | nil =>
      cases ss with
      | nil => trivial
      | cons s ss => simp at hlen
  | cons b bs ih =>
      cases ss with
      | nil => simp at hlen
      | cons s ss =>
          have h0 := h 0 (by simp)
          simp only [List.getElem_cons_zero, List.drop_succ_cons, List.drop_zero] at h0
          refine ⟨h0, ih ss (by simpa using hlen) ?_⟩
          intro i hi
          have ht := h (i+1) (by simpa using Nat.succ_lt_succ hi)
          simpa only [List.getElem_cons_succ, List.drop_succ_cons] using ht

private theorem coordInfo_of_check (bs : List PackedSite) (ss : List SectorSite)
    (parity : Nat) (h : sectorNetworkCheck bs parity ss = true) : CoordInfo bs ss parity := by
  obtain ⟨hlen, hall⟩ := Bool.and_eq_true_iff.mp h
  have hlen' : ss.length = bs.length := by simpa using hlen
  apply coordInfo_of_indexed bs ss parity hlen'
  intro i hi
  have hz : i < (bs.zip ss).length := by
    simpa only [List.length_zip, hlen', Nat.min_self] using hi
  have hs := List.forall_mem_zipIdx'.mp (List.all_eq_true.mp hall) i hz
  simp only [List.getElem_zip, Bool.and_eq_true] at hs
  simpa only [beq_iff_eq, groups] using hs.1.2

private def sectorBit (b : PackedSite) (index : Nat) : Nat :=
  if b.spec.nslots == 2 && b.spec.diluted && digit b index == 3 then 1 else 0

private def parityStep (index par : Nat) (b : PackedSite) : Nat :=
  if b.spec.nslots == 0 then par else 2*par + sectorBit b index

private def parityFold (bs : List PackedSite) (index par : Nat) : Nat :=
  bs.foldl (parityStep index) par

private theorem sectorBit_lt (b : PackedSite) (index : Nat) : sectorBit b index < 2 := by
  unfold sectorBit
  split <;> omega

private theorem sectorLabel_parity (bs : List PackedSite) (index : Nat) :
    (sectorLabel bs index).1 = parityFold bs index 0 := by
  unfold sectorLabel parityFold
  symm
  apply List.foldl_hom Prod.fst (init := (0, (0 : Int)))
  intro x b
  cases x
  rfl

/-- Dropping all parity bits contributed by a suffix recovers its starting prefix. -/
private theorem parityFold_div (bs : List PackedSite) (index par : Nat) :
    parityFold bs index par / 2^groups bs = par := by
  induction bs generalizing par with
  | nil => simp [parityFold, groups]
  | cons b bs ih =>
      by_cases hn : b.spec.nslots = 0
      · simpa [parityFold, parityStep, groups, hn] using ih par
      · have hg : groups (b :: bs) = groups bs + 1 := by simp [groups, hn]
        change parityFold bs index (parityStep index par b) / 2^groups (b :: bs) = par
        rw [hg, pow_succ, ← Nat.div_div_eq_div_mul, ih]
        have hb := sectorBit_lt b index
        simp only [parityStep, beq_iff_eq, hn, ite_false]
        omega

private theorem parityFold_bit (b : PackedSite) (bs : List PackedSite)
    (index par : Nat) (hn : b.spec.nslots ≠ 0) :
    parityFold (b :: bs) index par / 2^groups bs % 2 = sectorBit b index := by
  change parityFold bs index (parityStep index par b) / 2^groups bs % 2 = _
  rw [parityFold_div]
  have hb := sectorBit_lt b index
  simp only [parityStep, beq_iff_eq, hn, ite_false]
  omega

private theorem coordinates_contain_digit (b : PackedSite) (index bit : Nat)
    (hpos : 0 < b.spec.dim)
    (hdim : b.spec.nslots = 2 → b.spec.diluted = true → b.spec.dim = 4)
    (hbit : b.spec.nslots ≠ 0 → bit = sectorBit b index) :
    digit b index ∈ sectorCoordinates b.spec bit := by
  have hlt : digit b index < b.spec.dim := Nat.mod_lt _ hpos
  by_cases hn : b.spec.nslots = 2
  · by_cases hd : b.spec.diluted = true
    · have hb := hbit (by omega)
      have hfour := hdim hn hd
      have hlt4 : digit b index < 4 := by omega
      by_cases he : digit b index = 3
      · have hb1 : bit = 1 := by simpa [sectorBit, hn, hd, he] using hb
        simp [sectorCoordinates, hn, hd, hb1, he]
      · have hb0 : bit = 0 := by simpa [sectorBit, hn, hd, he] using hb
        simp [sectorCoordinates, hn, hd, hb0]
        omega
    · simp [sectorCoordinates, hn, hd, List.mem_range, hlt]
  · simp [sectorCoordinates, hn, List.mem_range, hlt]

private theorem allowed_of_parity (bs : List PackedSite) (ss : List SectorSite)
    (index par parity : Nat) (hb : BaseInfo bs) (hc : CoordInfo bs ss parity)
    (hp : parityFold bs index par = parity) :
    ∀ t ∈ bs.zip ss, digit t.1 index ∈ t.2.coordinates := by
  induction bs generalizing ss par with
  | nil => simp
  | cons b bs ih =>
      cases ss with
      | nil => exact False.elim hc
      | cons s ss =>
          obtain ⟨hpos, hdim, hstride, hbt⟩ := hb
          obtain ⟨hcoords, hct⟩ := hc
          have hhead : digit b index ∈ s.coordinates := by
            rw [hcoords]
            apply coordinates_contain_digit b index _ hpos hdim
            intro hn
            rw [← hp]
            exact parityFold_bit b bs index par hn
          have ht := ih ss (parityStep index par b) hbt hct hp
          intro t hm
          simp only [List.zip_cons_cons, List.mem_cons] at hm
          rcases hm with rfl | hm
          · exact hhead
          · exact ht t hm

private def remapStep (index code : Nat) (t : PackedSite × SectorSite) : Nat :=
  code * t.2.coordinates.length + t.2.coordinates.idxOf (digit t.1 index)

private def remapFold (ts : List (PackedSite × SectorSite)) (index code : Nat) : Nat :=
  ts.foldl (remapStep index) code

private def coordProduct (ts : List (PackedSite × SectorSite)) : Nat :=
  (ts.map (fun t => t.2.coordinates.length)).prod

private theorem remapFold_lt (ts : List (PackedSite × SectorSite)) (index code : Nat)
    (h : ∀ t ∈ ts, digit t.1 index ∈ t.2.coordinates) :
    remapFold ts index code < (code+1) * coordProduct ts := by
  induction ts generalizing code with
  | nil => simp [remapFold, coordProduct]
  | cons t ts ih =>
      have hd := List.idxOf_lt_length_of_mem (h t (by simp))
      have ht := ih (remapStep index code t) (fun u hu => h u (by simp [hu]))
      have hle : remapStep index code t + 1 ≤ (code+1) * t.2.coordinates.length := by
        dsimp [remapStep]
        nlinarith
      calc
        remapFold (t :: ts) index code = remapFold ts index (remapStep index code t) := rfl
        _ < (remapStep index code t+1) * coordProduct ts := ht
        _ ≤ ((code+1) * t.2.coordinates.length) * coordProduct ts :=
          Nat.mul_le_mul_right _ hle
        _ = (code+1) * coordProduct (t :: ts) := by simp [coordProduct, Nat.mul_assoc]

private theorem radix_div (a r d : Nat) (hd : d < r) : (a*r+d)/r = a := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hd, Nat.zero_add]

/-- Equality of two remapped words determines every original coordinate. -/
private theorem remapFold_digits (ts : List (PackedSite × SectorSite))
    (x y a b : Nat)
    (hx : ∀ t ∈ ts, digit t.1 x ∈ t.2.coordinates)
    (hy : ∀ t ∈ ts, digit t.1 y ∈ t.2.coordinates)
    (he : remapFold ts x a = remapFold ts y b) :
    a = b ∧ ∀ t ∈ ts, digit t.1 x = digit t.1 y := by
  induction ts generalizing a b with
  | nil => exact ⟨he, by simp⟩
  | cons t ts ih =>
      have htx := hx t (by simp)
      have hty := hy t (by simp)
      have hix := List.idxOf_lt_length_of_mem htx
      have hiy := List.idxOf_lt_length_of_mem hty
      obtain ⟨hstep, htail⟩ := ih (remapStep x a t) (remapStep y b t)
        (fun u hu => hx u (by simp [hu])) (fun u hu => hy u (by simp [hu])) he
      have hab := congrArg (fun k => k / t.2.coordinates.length) hstep
      dsimp only [remapStep] at hab hstep
      rw [radix_div _ _ _ hix, radix_div _ _ _ hiy] at hab
      have hidx : t.2.coordinates.idxOf (digit t.1 x) =
          t.2.coordinates.idxOf (digit t.1 y) := by
        rw [hab] at hstep
        exact Nat.add_left_cancel hstep
      have hhead : digit t.1 x = digit t.1 y := (List.idxOf_inj htx).mp hidx
      refine ⟨hab, ?_⟩
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact hhead
      · exact htail u hu

private theorem same_digits_mod (bs : List PackedSite) (hb : BaseInfo bs) (x y : Nat)
    (h : ∀ b ∈ bs, digit b x = digit b y) : x % baseLanes bs = y % baseLanes bs := by
  induction bs with
  | nil => simp [baseLanes, Nat.mod_one]
  | cons b bs ih =>
      obtain ⟨_, _, hstride, hbt⟩ := hb
      have ht := ih hbt (fun t hm => h t (by simp [hm]))
      have hh := h b (by simp)
      change x / b.spec.stride % b.spec.dim = y / b.spec.stride % b.spec.dim at hh
      rw [hstride] at hh
      change x % (b.spec.dim * baseLanes bs) = y % (b.spec.dim * baseLanes bs)
      rw [Nat.mul_comm b.spec.dim, Nat.mod_mul, Nat.mod_mul, ht, hh]

private theorem coordProduct_zip (bs : List PackedSite) (ss : List SectorSite)
    (hlen : ss.length = bs.length) :
    coordProduct (bs.zip ss) = (ss.map (fun s => s.coordinates.length)).prod := by
  have he := List.map_snd_zip (l₁ := bs) (l₂ := ss) (by omega)
  have hp := congrArg (fun xs : List SectorSite => (xs.map (fun s => s.coordinates.length)).prod) he
  simpa only [List.map_map, Function.comp_def, coordProduct] using hp

private theorem zip_digits_left (bs : List PackedSite) (ss : List SectorSite)
    (hlen : ss.length = bs.length) (x y : Nat)
    (h : ∀ t ∈ bs.zip ss, digit t.1 x = digit t.1 y) :
    ∀ b ∈ bs, digit b x = digit b y := by
  intro b hb
  have hm : b ∈ (bs.zip ss).map Prod.fst := by
    rw [List.map_fst_zip (by omega)]
    exact hb
  obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
  simpa only [he] using h t ht

/-- The layout checks place the selected columns at distinct positions within
the sector's mixed-radix range. -/
theorem layoutIndexing (c : Case) (hc : c.MetadataAccepted) (b : Bundle)
    (hb : b.LayoutAccepted c) :
    b.mapped.Nodup ∧ ∀ j ∈ b.mapped,
      j < (b.sector.map (fun s => s.coordinates.length)).prod := by
  have hbase := baseInfo_of_parameters c.network c.out c.width c.lanes c.denominator c.p c.q
    hc.2.2.2.1
  have hcoord := coordInfo_of_check c.network b.sector b.block.parity hb.2.1
  have hlen : b.sector.length = c.network.length := by
    simpa only [beq_iff_eq] using (Bool.and_eq_true_iff.mp hb.2.1).1
  have hindices : b.block.indices = sectorIndices c.network b.block.parity b.block.weight := by
    have hcheck := hb.1
    simp only [basisCheck, Bool.and_eq_true, beq_iff_eq] at hcheck
    exact hcheck.1.2
  have hmapped : b.block.indices.map (remapIndex c.network b.sector) = b.mapped := by
    simpa only [remapCheck, beq_iff_eq] using hb.2.2.1
  have hindex : ∀ i ∈ b.block.indices,
      i < baseLanes c.network ∧
        ∀ t ∈ c.network.zip b.sector, digit t.1 i ∈ t.2.coordinates := by
    intro i hi
    rw [hindices] at hi
    simp only [sectorIndices, List.mem_filter, List.mem_range, beq_iff_eq] at hi
    have hp := congrArg Prod.fst hi.2
    change (sectorLabel c.network i).1 = b.block.parity at hp
    rw [sectorLabel_parity] at hp
    exact ⟨hi.1, allowed_of_parity c.network b.sector i 0 b.block.parity hbase hcoord hp⟩
  have hnd : b.block.indices.Nodup := by
    rw [hindices]
    exact List.nodup_range.filter _
  rw [← hmapped]
  constructor
  · apply (List.nodup_map_iff_inj_on hnd).mpr
    intro x hx y hy he
    have hdx := (hindex x hx).2
    have hdy := (hindex y hy).2
    change remapFold (c.network.zip b.sector) x 0 = remapFold (c.network.zip b.sector) y 0 at he
    have hd := (remapFold_digits _ x y 0 0 hdx hdy he).2
    have heq := same_digits_mod c.network hbase x y
      (zip_digits_left c.network b.sector hlen x y hd)
    simpa only [Nat.mod_eq_of_lt (hindex x hx).1, Nat.mod_eq_of_lt (hindex y hy).1] using heq
  · intro j hj
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hj
    have hlt := remapFold_lt (c.network.zip b.sector) i 0 (hindex i hi).2
    rw [coordProduct_zip c.network b.sector hlen] at hlt
    change remapFold (c.network.zip b.sector) i 0 < _
    simpa only [Nat.zero_add, Nat.one_mul] using hlt

#print axioms layoutIndexing

end AKLT.W.H1C014
