module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C026

open AKLT.Cert.H1.Production

private instance : LawfulBEq RawOption where
  rfl := by
    intro a
    cases a with
    | mk s m =>
        change (s == s && m == m) = true
        simp only [beq_self_eq_true, Bool.and_self]
  eq_of_beq := by
    intro a b h
    cases a with
    | mk sa ma =>
        cases b with
        | mk sb mb =>
            change (sa == sb && ma == mb) = true at h
            have h' : (sa == sb) = true ∧ (ma == mb) = true := by
              simpa only [Bool.and_eq_true] using h
            rcases h' with ⟨hs, hm⟩
            have hs' : sa = sb := Nat.eq_of_beq_eq_true hs
            have hm' : ma = mb := Nat.eq_of_beq_eq_true hm
            subst sb
            subst mb
            rfl

private theorem all_mem {α : Type} {l : List α} {f : α → Bool}
    (hall : l.all f = true) {a : α} (ha : a ∈ l) : f a = true := by
  induction l with
  | nil => simp at ha
  | cons b bs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hall
      rcases List.mem_cons.mp ha with hab | ha
      · simpa [hab] using hall.1
      · exact ih hall.2 ha

private theorem coverage_at_mem (t : Catalog) {rows : List (List RawOption)}
    (hrows : CoverageRowsAccepted t rows) {axes : List RawOption}
    (haxes : axes ∈ rows) : CoverageAccepted t axes := by
  induction rows with
  | nil => simp at haxes
  | cons row rest ih =>
      simp only [CoverageRowsAccepted] at hrows
      rcases List.mem_cons.mp haxes with heq | hmem
      · subst axes
        exact hrows.1
      · exact ih hrows.2 hmem

private theorem shard_at (t : Catalog) (axes : List RawOption)
    (h : CoverageAccepted t axes) (i : Nat) (hi : i < cornerOptions.length) :
    coverageShard t axes i = true := by
  have h8 : i < 8 := by simpa [cornerOptions] using hi
  rcases h with ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩
  interval_cases i <;> simp_all

private theorem first_three_status_zero
    (axes : List RawOption)
    (h : (axes.take 3).all (fun a => a.status == 0) = true)
    (i : Nat) (hi : i < 3) : (axes.getD i ⟨0, 0⟩).status = 0 := by
  cases i with
  | zero =>
      cases axes with
      | nil => simp [List.getD]
      | cons a as =>
          have ha : (a.status == 0) = true := all_mem h (by simp)
          have ha' : a.status = 0 := of_decide_eq_true ha
          simpa only [List.getD_cons_zero] using ha'
  | succ i =>
      cases i with
      | zero =>
          cases axes with
          | nil => simp [List.getD]
          | cons a as =>
              cases as with
              | nil => simp [List.getD]
              | cons b bs =>
                  have hb : (b.status == 0) = true := all_mem h (by simp)
                  have hb' : b.status = 0 := of_decide_eq_true hb
                  simpa only [List.getD_cons_succ, List.getD_cons_zero] using hb'
      | succ i =>
          cases i with
          | zero =>
              cases axes with
              | nil => simp [List.getD]
              | cons a as =>
                  cases as with
                  | nil => simp [List.getD]
                  | cons b bs =>
                      cases bs with
                      | nil => simp [List.getD]
                      | cons c cs =>
                          have hc : (c.status == 0) = true := all_mem h (by simp)
                          have hc' : c.status = 0 := of_decide_eq_true hc
                          simpa only [List.getD_cons_succ, List.getD_cons_zero] using hc'
          | succ i =>
              have : False := by omega
              exact this.elim

private theorem raw_edge_false_of_first_three_X
    (axes corners : List RawOption)
    (hX : (axes.take 3).all (fun a => a.status == 0) = true)
    (out : Nat) (hout : out < 3) : (rawEdges axes corners).getD out false = false := by
  have hstatus := first_three_status_zero axes hX out hout
  let center : List Bool := (List.range 4).map (fun i =>
      i != 3 && (axes.getD i ⟨0, 0⟩).status != 0 &&
        hasDirection (axes.getD i ⟨0, 0⟩).mask ((i + 2) % 4))
  let cycle : List Bool := (List.range 8).map (fun i =>
      let a := (ringOptions axes corners).getD i ⟨0, 0⟩
      let b := (ringOptions axes corners).getD ((i + 1) % 8) ⟨0, 0⟩
      let d := edgeDirections.getD i 0
      a.status != 0 && b.status != 0 && hasDirection a.mask d && hasDirection b.mask ((d + 2) % 4))
  let tips : List Bool := (List.range 4).map (fun i =>
      let a := axes.getD i ⟨0, 0⟩
      a.status != 0 && hasDirection a.mask i)
  change ((center ++ cycle) ++ tips).getD out false = false
  have houter : out < (center ++ cycle).length := by
    simp [center, cycle]
    omega
  rw [List.getD_append _ _ _ _ houter]
  have hcenter : out < center.length := by simp [center]; omega
  rw [List.getD_append _ _ _ _ hcenter]
  rw [List.getD_eq_getElem _ _ hcenter, List.getElem_map, List.getElem_range]
  have hstatus' : (axes[out]?.getD ⟨0, 0⟩).status = 0 := by simpa using hstatus
  simp [center, hstatus', hout]

private theorem corners_shape (corners : List RawOption) (hlen : corners.length = 4) :
    ∃ c0 c1 c2 c3, corners = [c0, c1, c2, c3] := by
  cases corners with
  | nil => simp at hlen
  | cons c0 xs =>
      cases xs with
      | nil => simp at hlen
      | cons c1 xs =>
          cases xs with
          | nil => simp at hlen
          | cons c2 xs =>
              cases xs with
              | nil => simp at hlen
              | cons c3 xs =>
                  cases xs with
                  | nil => exact ⟨c0, c1, c2, c3, rfl⟩
                  | cons c4 xs => simp at hlen

private theorem lookup_of_coverage (t : Catalog) (axes : List RawOption)
    (hcoverage : CoverageAccepted t axes)
    (corners : List RawOption) (hlen : corners.length = 4)
    (hcorners : (corners.zipIdx.all
      (fun (x, i) => cornerOptions.contains x && cornerCompatible axes i x)) = true)
    (out : Nat) (hout : out < 3)
    (hlive : (rawEdges axes corners).getD out false = true) :
    ∃ pid : Nat, t.find (rawKey axes corners out) = some pid := by
  obtain ⟨c0, c1, c2, c3, rfl⟩ := corners_shape corners hlen
  have h0 := all_mem hcorners (a := (c0, 0)) (by simp)
  have h1 := all_mem hcorners (a := (c1, 1)) (by simp)
  have h2 := all_mem hcorners (a := (c2, 2)) (by simp)
  have h3 := all_mem hcorners (a := (c3, 3)) (by simp)
  simp only [Bool.and_eq_true] at h0 h1 h2 h3
  have hc0 : cornerOptions.contains c0 = true ∧ cornerCompatible axes 0 c0 = true := by
    simpa using h0
  have hc1 : cornerOptions.contains c1 = true ∧ cornerCompatible axes 1 c1 = true := by
    simpa using h1
  have hc2 : cornerOptions.contains c2 = true ∧ cornerCompatible axes 2 c2 = true := by
    simpa using h2
  have hc3 : cornerOptions.contains c3 = true ∧ cornerCompatible axes 3 c3 = true := by
    simpa using h3
  have hm0 : c0 ∈ cornerOptions := List.contains_iff_mem.mp hc0.1
  obtain ⟨first, hfirst, hget⟩ := List.mem_iff_getElem.mp hm0
  have hfirst_lt : first < cornerOptions.length := hfirst
  have hfirstD : cornerOptions.getD first ⟨0, 0⟩ = c0 := by
    rw [List.getD_eq_getElem _ _ hfirst]
    exact hget
  have hshard := shard_at t axes hcoverage first hfirst_lt
  have hnotX : (axes.take 3).all (fun a => a.status == 0) ≠ true := by
    intro hX
    have hfalse := raw_edge_false_of_first_three_X axes [c0, c1, c2, c3] hX out hout
    rw [hfalse] at hlive
    contradiction
  cases hX : (axes.take 3).all (fun a => a.status == 0) with
  | false =>
      have hshard' :
          (if cornerCompatible axes 0 (cornerOptions.getD first ⟨0, 0⟩) then
            (allowedCorners axes 1).all (fun c1 =>
              (allowedCorners axes 2).all (fun c2 =>
                (allowedCorners axes 3).all (fun c3 =>
                  markedCheck t axes [cornerOptions.getD first ⟨0, 0⟩, c1, c2, c3])))
           else true) = true := by
        simpa only [coverageShard, hX, Bool.false_eq_true, if_false] using hshard
      have hshard'' :
          (allowedCorners axes 1).all (fun x1 =>
            (allowedCorners axes 2).all (fun x2 =>
              (allowedCorners axes 3).all (fun x3 =>
                markedCheck t axes [c0, x1, x2, x3]))) = true := by
        simpa only [hfirstD, hc0.2, if_pos] using hshard'
      have hm1 : c1 ∈ allowedCorners axes 1 := by
        apply List.mem_filter.mpr
        exact ⟨List.contains_iff_mem.mp hc1.1, hc1.2⟩
      have hm2 : c2 ∈ allowedCorners axes 2 := by
        apply List.mem_filter.mpr
        exact ⟨List.contains_iff_mem.mp hc2.1, hc2.2⟩
      have hm3 : c3 ∈ allowedCorners axes 3 := by
        apply List.mem_filter.mpr
        exact ⟨List.contains_iff_mem.mp hc3.1, hc3.2⟩
      have hmarked : markedCheck t axes [c0, c1, c2, c3] = true := by
        have h1all := all_mem hshard'' hm1
        have h2all := all_mem h1all hm2
        exact all_mem h2all hm3
      have houtmarked := all_mem hmarked (List.mem_range.mpr hout)
      have hlive' : (rawEdges axes [c0, c1, c2, c3])[out]?.getD false = true := by
        simpa using hlive
      have hsome : (t.find (rawKey axes [c0, c1, c2, c3] out)).isSome = true := by
        simpa [markedCheck, rawKey, rawCode, hlive'] using houtmarked
      cases hfind : t.find (rawKey axes [c0, c1, c2, c3] out) with
      | none => simp [hfind] at hsome
      | some pid => exact ⟨pid, rfl⟩
  | true => exact (hnotX hX).elim

theorem main : AKLT.Cert.H1.Production.Leaves.enumerationSoundness := by
  intro t hrows axes haxes corners hlen hcorners out hout hlive
  exact lookup_of_coverage t axes (coverage_at_mem t hrows haxes)
    corners hlen hcorners out hout hlive

end AKLT.W.H1C026
