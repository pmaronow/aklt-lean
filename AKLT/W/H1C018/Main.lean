import AKLT.Cert.H1.Production.Leaves

namespace AKLT.W.H1C018

open AKLT.Cert.H1.Production
open AKLT.Cert.H1
open AKLT.Cert.H1.Production.Leaves
open scoped BigOperators

private theorem finRangeValue (n : Nat) : (List.finRange n).map Fin.val = List.range n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [List.finRange_succ, List.map_cons, List.map_map, List.range_succ_eq_map,
        Fin.val_zero, Function.comp_def, Fin.val_succ]
      rw [← ih, List.map_map]
      apply congrArg (fun l => 0 :: l)
      apply List.map_congr_left
      intro x hx
      exact Nat.add_one _

private theorem finRangeSum (n : Nat) (f : Fin n → Int) :
    ((List.finRange n).map f).sum = ∑ i : Fin n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.map_cons, List.map_map, List.sum_cons,
        Fin.sum_univ_succ]
      have ht := ih (fun i => f i.succ)
      simpa [Function.comp_def] using congrArg (fun z : Int => f 0 + z) ht

private theorem gaussianSumReal (xs : List Gaussian) :
    (sumGaussian xs).re = (xs.map Gaussian.re).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [sumGaussian, Gaussian.add, ih]

private def parityStep (index acc : Nat) (s : PackedSite) : Nat :=
  if s.spec.nslots == 0 then acc else
    2*acc + if s.spec.nslots == 2 && s.spec.diluted &&
      index / s.spec.stride % s.spec.dim == 3 then 1 else 0

private def parityBit (index : Nat) (s : PackedSite) : Nat :=
  if s.spec.nslots == 2 && s.spec.diluted &&
      index / s.spec.stride % s.spec.dim == 3 then 1 else 0

private def activeCount : List PackedSite → Nat
  | [] => 0
  | s :: ss => if s.spec.nslots = 0 then activeCount ss else activeCount ss + 1

private def parityTail (index : Nat) : List PackedSite → Nat
  | [] => 0
  | s :: ss =>
      if s.spec.nslots = 0 then parityTail index ss
      else parityBit index s * 2^(activeCount ss) + parityTail index ss

private theorem activeCount_eq_filterLength (ss : List PackedSite) :
    activeCount ss = (ss.filter (fun s => s.spec.nslots != 0)).length := by
  induction ss with
  | nil => rfl
  | cons s ss ih =>
      cases hn : s.spec.nslots with
      | zero => simp [activeCount, hn, ih]
      | succ k => simp [activeCount, hn, ih]

private theorem parityLabelFst (ss : List PackedSite) (index : Nat) (acc : Nat × Int) :
    (ss.foldl (fun z s =>
      (if s.spec.nslots == 0 then z.1 else
        2*z.1 + if s.spec.nslots == 2 && s.spec.diluted &&
          index / s.spec.stride % s.spec.dim == 3 then 1 else 0,
       z.2 + localWeight s.spec (index / s.spec.stride % s.spec.dim))) acc).1 =
      ss.foldl (parityStep index) acc.1 := by
  induction ss generalizing acc with
  | nil => rfl
  | cons s ss ih =>
      simpa [List.foldl_cons, parityStep] using
        ih (if s.spec.nslots == 0 then acc.1 else
          2*acc.1 + if s.spec.nslots == 2 && s.spec.diluted &&
            index / s.spec.stride % s.spec.dim == 3 then 1 else 0,
          acc.2 + localWeight s.spec (index / s.spec.stride % s.spec.dim))

private theorem sectorLabel_fst_eq_parityFold (ss : List PackedSite) (index : Nat) :
    (sectorLabel ss index).1 = ss.foldl (parityStep index) 0 := by
  simpa [sectorLabel] using parityLabelFst ss index (0, 0)

private theorem parityFold_formula (index acc : Nat) (ss : List PackedSite) :
    ss.foldl (parityStep index) acc = acc * 2^(activeCount ss) + parityTail index ss := by
  induction ss generalizing acc with
  | nil => simp [activeCount, parityTail]
  | cons s ss ih =>
      by_cases hz : s.spec.nslots = 0
      · simp [List.foldl_cons, parityStep, activeCount, parityTail, hz, ih]
      · by_cases hb : (s.spec.nslots == 2 && s.spec.diluted &&
            index / s.spec.stride % s.spec.dim == 3) = true
        · simp [List.foldl_cons, parityStep, activeCount, parityTail, parityBit, hz, hb, ih,
            Nat.pow_succ]
          ring
        · simp [List.foldl_cons, parityStep, activeCount, parityTail, parityBit, hz, hb, ih,
            Nat.pow_succ]
          ring

private theorem parityTail_lt (index : Nat) (ss : List PackedSite) :
    parityTail index ss < 2^(activeCount ss) := by
  induction ss with
  | nil => simp [parityTail, activeCount]
  | cons s ss ih =>
      by_cases hz : s.spec.nslots = 0
      · simp [parityTail, activeCount, hz, ih]
      · by_cases hb : (s.spec.nslots == 2 && s.spec.diluted &&
            index / s.spec.stride % s.spec.dim == 3) = true
        · simp [parityTail, activeCount, parityBit, hz, hb, Nat.pow_succ]
          omega
        · simp [parityTail, activeCount, parityBit, hz, hb, Nat.pow_succ]
          omega

private theorem parityBitAt (ss : List PackedSite) (index i : Nat) (hi : i < ss.length)
    (hspecial : (ss[i]).spec.nslots == 2 && (ss[i]).spec.diluted = true) :
    (sectorLabel ss index).1 /
      2^((ss.drop (i+1)).filter (fun s => s.spec.nslots != 0)).length % 2 =
      parityBit index ss[i] := by
  let pre := ss.take i
  let site := ss[i]
  let post := ss.drop (i+1)
  have hdrop : ss.drop i = site :: post := by
    simpa [site, post] using List.drop_eq_getElem_cons hi
  have hsplit : pre ++ site :: post = ss := by
    have ht := List.take_append_drop i ss
    rw [hdrop] at ht
    simpa [pre, site, post] using ht
  have hcount : (post.filter (fun s => s.spec.nslots != 0)).length = activeCount post :=
    (activeCount_eq_filterLength post).symm
  have hformula := parityFold_formula index
    (pre.foldl (parityStep index) 0) (site :: post)
  have hfull : (sectorLabel ss index).1 =
      (pre.foldl (parityStep index) 0) * 2^(activeCount (site :: post)) +
        parityTail index (site :: post) := by
    rw [sectorLabel_fst_eq_parityFold, ← hsplit, List.foldl_append]
    exact hformula
  have hspProp : site.spec.nslots = 2 ∧ site.spec.diluted = true := by
    simpa [site] using hspecial
  have hsactive : site.spec.nslots ≠ 0 := by omega
  have hcode : (sectorLabel ss index).1 =
      ((pre.foldl (parityStep index) 0)*2 + parityBit index site) * 2^(activeCount post) +
        parityTail index post := by
    rw [hfull]
    by_cases hb : index / site.spec.stride % site.spec.dim == 3
    · simp [activeCount, parityTail, parityStep, parityBit, hsactive, hspProp.1,
        hspProp.2, hb, Nat.pow_succ]
      ring
    · simp [activeCount, parityTail, parityStep, parityBit, hsactive, hspProp.1,
        hspProp.2, hb, Nat.pow_succ]
      ring
  have hbitlt : parityBit index site < 2 := by
    dsimp [parityBit]
    split <;> omega
  have htail : parityTail index post < 2^(activeCount post) := parityTail_lt index post
  have hdiv : (sectorLabel ss index).1 / 2^(activeCount post) =
      (pre.foldl (parityStep index) 0)*2 + parityBit index site := by
    apply Nat.div_eq_of_lt_le
    · rw [hcode]
      nlinarith
    · rw [hcode]
      nlinarith [htail]
  have hmod : ((pre.foldl (parityStep index) 0)*2 + parityBit index site) % 2 =
      parityBit index site := by omega
  calc
    (sectorLabel ss index).1 /
        2^((ss.drop (i+1)).filter (fun s => s.spec.nslots != 0)).length % 2 =
        (sectorLabel ss index).1 / 2^(activeCount post) % 2 := by
          rw [hcount]
    _ = parityBit index site := by rw [hdiv, hmod]

private def mixedCode (xs : List (Nat × Nat)) : Nat :=
  xs.foldl (fun acc x => acc*x.1+x.2) 0

private theorem mixedCode_lt (xs : List (Nat × Nat))
    (hd : ∀ x ∈ xs, x.2 < x.1) (acc : Nat) :
    xs.foldl (fun z x => z*x.1+x.2) acc < (acc+1) * (xs.map Prod.fst).prod := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
      have hx := hd x (by simp)
      have htail : ∀ y ∈ xs, y.2 < y.1 := by
        intro y hy
        exact hd y (by simp [hy])
      have hbase : acc*x.1 + x.2 + 1 ≤ (acc+1)*x.1 := by
        have hstep : x.2 + 1 ≤ x.1 := Nat.succ_le_of_lt hx
        calc
          acc*x.1 + x.2 + 1 ≤ acc*x.1 + x.1 := Nat.add_le_add_left hstep _
          _ = (acc+1)*x.1 := by ring
      calc
        (x :: xs).foldl (fun z y => z*y.1+y.2) acc =
            xs.foldl (fun z y => z*y.1+y.2) (acc*x.1+x.2) := rfl
        _ < ((acc*x.1+x.2)+1) * (xs.map Prod.fst).prod := ih htail _
        _ ≤ ((acc+1)*x.1) * (xs.map Prod.fst).prod := Nat.mul_le_mul_right _ hbase
        _ = (acc+1) * ((x :: xs).map Prod.fst).prod := by simp; ring

private theorem mapZipSnd_eq (xs : List PackedSite) (ys : List SectorSite)
    (h : ys.length ≤ xs.length) :
    (xs.zip ys).map Prod.snd = ys := List.map_snd_zip h

private theorem remapIndex_lt_of_digits (base : List PackedSite) (ss : List SectorSite)
    (index : Nat)
    (hd : ∀ z ∈ base.zip ss,
      (z.2.coordinates.idxOf (index / z.1.spec.stride % z.1.spec.dim)) < z.2.coordinates.length)
    (hlen : ss.length ≤ base.length) :
    remapIndex base ss index < (ss.map (fun s => s.coordinates.length)).prod := by
  let xs := (base.zip ss).map (fun z =>
    (z.2.coordinates.length, z.2.coordinates.idxOf (index / z.1.spec.stride % z.1.spec.dim)))
  have hcode : remapIndex base ss index = mixedCode xs := by
    simp [remapIndex, mixedCode, xs, List.foldl_map]
  have hdigits : ∀ x ∈ xs, x.2 < x.1 := by
    intro x hx
    rcases List.mem_map.mp hx with ⟨z,hz,rfl⟩
    exact hd z hz
  have hfst : xs.map Prod.fst = (base.zip ss).map (fun z => z.2.coordinates.length) := by
    simp [xs, List.map_map]
  have hprod : (xs.map Prod.fst).prod = (ss.map (fun s => s.coordinates.length)).prod := by
    rw [hfst]
    have hmapfst : (base.zip ss).map (fun z => z.2.coordinates.length) =
        ((base.zip ss).map Prod.snd).map (fun s => s.coordinates.length) := by
      simp [List.map_map]
    have hmap := congrArg (List.map (fun s : SectorSite => s.coordinates.length))
      (mapZipSnd_eq base ss hlen)
    exact congrArg List.prod (hmapfst.trans hmap)
  rw [hcode]
  have := mixedCode_lt xs hdigits 0
  rw [hprod] at this
  simpa [mixedCode] using this

private theorem decodeSectorRow {ss : List SectorSite} {out width n p q : Nat}
    (hpack : ∀ row : Nat, packedSectorThresholdRow ss out row width p q =
      sumGaussian ((List.range n).map (fun col =>
        (directSectorThreshold ss out p q row col).scale ((2 : Nat)^(width*col) : Int))))
    (hbound : ∀ row col : Nat,
      (directSectorThreshold ss out p q row col).re.natAbs +
        (directSectorThreshold ss out p q row col).im.natAbs < 2^(width-1))
    (hsigned : ∀ w n : Nat, 0 < w → ∀ f : Fin n → Int,
      (∀ i, -((2 : Nat)^(w-1) : Int) ≤ f i ∧ f i < ((2 : Nat)^(w-1) : Int)) →
      ∀ i : Fin n, signedDigit ((∑ j : Fin n, f j * ((2 : Nat)^(w*j.val) : Int)) +
        signedBias w n) w i = f i)
    (hwidth : 0 < width)
    (row : Nat) (indices : List Nat)
    (hindices : ∀ j ∈ indices, j < n) :
    constructedSectorRow ss out width n p q row indices =
      indices.map (fun col => (directSectorThreshold ss out p q row col).re) := by
  let f : Fin n → Int := fun i => (directSectorThreshold ss out p q row i.val).re
  have hmaps :
        (List.range n).map (fun col =>
          (directSectorThreshold ss out p q row col).re * ((2 : Nat)^(width*col) : Int)) =
        (List.finRange n).map (fun i => f i * ((2 : Nat)^(width*i.val) : Int)) := by
      rw [← finRangeValue n, List.map_map]
      apply List.map_congr_left
      intro i hi
      rfl
  have hreal : (packedSectorThresholdRow ss out row width p q).re =
      ∑ i : Fin n, f i * ((2 : Nat)^(width*i.val) : Int) := by
    calc
      _ = (sumGaussian ((List.range n).map (fun col =>
          (directSectorThreshold ss out p q row col).scale ((2 : Nat)^(width*col) : Int)))).re :=
        congrArg Gaussian.re (hpack row)
      _ = ((List.range n).map (fun col =>
          (directSectorThreshold ss out p q row col).re * ((2 : Nat)^(width*col) : Int))).sum := by
        rw [gaussianSumReal]
        simp only [List.map_map, Function.comp_apply]
        change ((List.range n).map (fun col =>
          (Gaussian.scale ((2 : Nat)^(width*col) : Int)
            (directSectorThreshold ss out p q row col)).re)).sum = _
        apply congrArg List.sum
        apply List.map_congr_left
        intro col hcol
        simp [Gaussian.scale]
        ring
      _ = ((List.finRange n).map (fun i => f i * ((2 : Nat)^(width*i.val) : Int))).sum := by
        rw [hmaps]
      _ = ∑ i : Fin n, f i * ((2 : Nat)^(width*i.val) : Int) := finRangeSum n _
  have hfb : ∀ i : Fin n, -((2 : Nat)^(width-1) : Int) ≤ f i ∧
      f i < ((2 : Nat)^(width-1) : Int) := by
    intro i
    have hb := hbound row i.val
    have hr : (f i).natAbs < 2^(width-1) := by
      have hle : (f i).natAbs ≤ (directSectorThreshold ss out p q row i.val).re.natAbs +
          (directSectorThreshold ss out p q row i.val).im.natAbs := by
        dsimp [f]
        omega
      exact Nat.lt_of_le_of_lt hle hb
    have habs : |f i| < ((2 : Nat)^(width-1) : Int) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hr
    rw [abs_lt] at habs
    exact ⟨by omega, habs.2⟩
  have hd := hsigned width n hwidth f hfb
  change indices.map (fun col => signedDigit
      ((packedSectorThresholdRow ss out row width p q).re + signedBias width n) width col) = _
  apply List.map_congr_left
  intro col hcol
  have hc := hd ⟨col, hindices col hcol⟩
  rw [← hreal] at hc
  simpa [f] using hc

 theorem main : AKLT.Cert.H1.Production.Leaves.packingDecode := by
  intro hexp hbound hs c hm b hb
  have hmAccepted := hm
  rcases hm with ⟨hi,hgeom,ht,hparams,ho,hp,hq,hpar⟩
  have hwidth : 0 < c.width := by
    simp [parametersCheck] at hparams
    omega
  let n := (b.sector.map (fun s => s.coordinates.length)).prod
  have hsectorFacts := hb.2.1
  simp [sectorNetworkCheck] at hsectorFacts
  have hparamsFacts := hparams
  simp [parametersCheck] at hparamsFacts
  have hbasisFacts := hb.1
  simp [basisCheck] at hbasisFacts
  have hindicesEq : b.block.indices = sectorIndices c.network b.block.parity b.block.weight :=
    hbasisFacts.1.2
  have hremap : b.block.indices.map (remapIndex c.network b.sector) = b.mapped := by
    simpa [remapCheck] using hb.2.2.1
  have hrange : ∀ col ∈ b.mapped, col < n := by
    intro col hcol
    have hcol' : col ∈ b.block.indices.map (remapIndex c.network b.sector) := by
      rw [hremap]
      exact hcol
    rcases List.mem_map.mp hcol' with ⟨idx,hidx,rfl⟩
    have hidxSec : idx ∈ sectorIndices c.network b.block.parity b.block.weight := by
      rw [← hindicesEq]
      exact hidx
    rcases List.mem_filter.mp hidxSec with ⟨_, htest⟩
    have hlabel : sectorLabel c.network idx = (b.block.parity,b.block.weight) := by
      simpa using htest
    have hdigits : ∀ z ∈ c.network.zip b.sector,
        (z.2.coordinates.idxOf (idx / z.1.spec.stride % z.1.spec.dim)) < z.2.coordinates.length := by
      intro z hz
      rcases z with ⟨site,ssite⟩
      rcases List.mem_iff_get.mp hz with ⟨i,hget⟩
      have hziplen : i.val < (c.network.zip b.sector).length := i.isLt
      have hiNet : i.val < c.network.length := by
        simp [List.length_zip] at hziplen
        omega
      have hiSec : i.val < b.sector.length := by
        simp [List.length_zip] at hziplen
        omega
      have hiAll : i.val < ((c.network.zip b.sector).zipIdx).length := by
        simp [List.length_zip]
        omega
      have hget' : (c.network.zip b.sector)[i.val] = (site,ssite) := by
        simpa using hget
      have hpairMem : ((site,ssite),i.val) ∈ (c.network.zip b.sector).zipIdx := by
        have hmem := List.getElem_mem (l := (c.network.zip b.sector).zipIdx) (n := i.val) hiAll
        simp only [List.getElem_zipIdx, Nat.zero_add] at hmem
        rw [hget'] at hmem
        exact hmem
      have hcoord := (hsectorFacts.2 site ssite i.val hpairMem).1.2
      have hsite : c.network[i.val] = site := by
        have := congrArg Prod.fst hget'
        simpa [List.getElem_zip] using this
      have hsiteMem : (site,i.val) ∈ c.network.zipIdx := by
        have hilen : i.val < c.network.zipIdx.length := by simp [hiNet]
        have hmem := List.getElem_mem (l := c.network.zipIdx) (n := i.val) hilen
        simp only [List.getElem_zipIdx, Nat.zero_add] at hmem
        rw [hsite] at hmem
        exact hmem
      have hsiteFacts := hparamsFacts.2 site i.val hsiteMem
      have hdim : 0 < site.spec.dim := hsiteFacts.1.1.1.1
      have hdimformula := hsiteFacts.1.1.2
      let digit := idx / site.spec.stride % site.spec.dim
      have hdigit : digit < site.spec.dim := Nat.mod_lt _ hdim
      change ssite.coordinates.idxOf digit < ssite.coordinates.length
      by_cases hsp : (site.spec.nslots == 2 && site.spec.diluted) = true
      · have hspProp : site.spec.nslots = 2 ∧ site.spec.diluted = true := by
          simpa using hsp
        have hbit := parityBitAt c.network idx i.val hiNet (by simpa [hsite] using hsp)
        rw [hsite] at hbit
        have hlabelpar := congrArg Prod.fst hlabel
        rw [hlabelpar] at hbit
        simp only [parityBit, hspProp.1, hspProp.2] at hbit
        by_cases hthree : digit == 3
        · have hparone : b.block.parity /
              2^((c.network.drop (i.val+1)).filter (fun t => t.spec.nslots != 0)).length % 2 = 1 := by
            simpa [parityBit, digit, hthree] using hbit
          have hdigitEq : digit = 3 := of_decide_eq_true hthree
          have hmem : digit ∈ ssite.coordinates := by
            rw [hcoord]
            simp [sectorCoordinates, hspProp.1, hspProp.2, hparone, hdigitEq]
          exact List.idxOf_lt_length_iff.mpr hmem
        · have hparzero : b.block.parity /
              2^((c.network.drop (i.val+1)).filter (fun t => t.spec.nslots != 0)).length % 2 = 0 := by
            simpa [parityBit, digit, hthree] using hbit
          have hdimEq : site.spec.dim = 4 := by
            simpa [hspProp.1, hspProp.2] using hdimformula
          have hdigit3 : digit < 3 := by
            have : digit < 4 := by simpa [hdimEq] using hdigit
            have hne : digit ≠ 3 := by
              intro heq
              apply hthree
              simpa [heq]
            omega
          have hmem : digit ∈ ssite.coordinates := by
            rw [hcoord]
            simp [sectorCoordinates, hspProp.1, hspProp.2, hparzero]
            interval_cases digit <;> simp_all
          exact List.idxOf_lt_length_iff.mpr hmem
      · have hcoords : ssite.coordinates = List.range site.spec.dim := by
          rw [hcoord]
          simp [sectorCoordinates, hsp]
        have hmem : digit ∈ List.range site.spec.dim := List.mem_range.mpr hdigit
        rw [hcoords]
        exact List.idxOf_lt_length_iff.mpr hmem
    have hsmall := remapIndex_lt_of_digits c.network b.sector idx hdigits
      (le_of_eq hsectorFacts.1)
    simpa [n] using hsmall
  change constructedSectorRows b.sector c.out c.width n c.p c.q b.mapped =
    directSectorRows b.sector c.out c.p c.q b.mapped
  change b.mapped.map (fun row => constructedSectorRow b.sector c.out c.width n c.p c.q row b.mapped) =
    b.mapped.map (fun row => b.mapped.map (fun col =>
      (directSectorThreshold b.sector c.out c.p c.q row col).re))
  apply List.map_congr_left
  intro row hrow
  exact decodeSectorRow (fun row => hexp c hmAccepted b hb row)
    (fun row col => hbound c hmAccepted b hb row col) hs hwidth row b.mapped hrange

end AKLT.W.H1C018
