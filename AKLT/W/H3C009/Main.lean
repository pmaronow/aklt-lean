module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true
set_option maxRecDepth 100000

namespace AKLT.W.H3C009

open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Gen.Packed
open CertData.H3.Bridge

@[simp] private theorem directionCode_direction (n : Nat) :
    AKLT.Cert.H3.directionCode (AKLT.Cert.H3.direction (n % 4)) = n % 4 := by
  have hn : n % 4 < 4 := Nat.mod_lt _ (by decide)
  interval_cases h : n % 4 <;>
    simp [AKLT.Cert.H3.direction, AKLT.Cert.H3.directionCode]

private theorem encode_decode_ten (c : Nat) (hc : c < 1048576) :
    encodeWord (decodeWord 10 c) = c := by
  have hstep (k : Nat) :
      ((c / 4^k) % 4) * 4^k + (c / 4^(k+1)) * 4^(k+1) = (c / 4^k) * 4^k := by
    have hq : c / 4^k / 4 = c / 4^(k+1) := by
      rw [Nat.div_div_eq_div_mul]
      simp [pow_succ, Nat.mul_comm]
    have hp : 4^(k+1) = 4^k * 4 := by simp [pow_succ]
    have hm := congrArg (fun z => z * 4^k) (Nat.mod_add_div (c / 4^k) 4)
    calc
      ((c / 4^k) % 4) * 4^k + (c / 4^(k+1)) * 4^(k+1) =
          ((c / 4^k) % 4 + 4 * (c / 4^k / 4)) * 4^k := by
        rw [hq, hp]
        ring
      _ = (c / 4^k) * 4^k := hm
  have h0 := hstep 0
  have h1 := hstep 1
  have h2 := hstep 2
  have h3 := hstep 3
  have h4 := hstep 4
  have h5 := hstep 5
  have h6 := hstep 6
  have h7 := hstep 7
  have h8 := hstep 8
  have h9 := hstep 9
  have hquot : c / 1048576 = 0 := Nat.div_eq_of_lt (by simpa using hc)
  simp [encodeWord, decodeWord, directionCode_direction, List.finRange_succ_last]
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  linarith [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, hquot]

private theorem revisit_leaf_proved : RevisitLeaf := by
  intro n u incoming w s hrep
  rcases hrep with ⟨_, hpos, _, _, hdepart, _⟩
  rw [hdepart, hpos]
  simp [departureCount]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨i.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, hi⟩⟩
  · rintro ⟨j, hj⟩
    have hj' := List.mem_filter.mp hj
    exact ⟨⟨j, List.mem_range.mp hj'.1⟩, of_decide_eq_true hj'.2⟩

private theorem pair_eq_iff {a b c d : Point} :
    ({a, b} : Finset Point) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  constructor
  · intro h
    have ha : a = c ∨ a = d := by
      have hm : a ∈ ({c, d} : Finset Point) := by rw [← h]; simp
      simpa using hm
    have hb : b = c ∨ b = d := by
      have hm : b ∈ ({c, d} : Finset Point) := by rw [← h]; simp
      simpa using hm
    rcases ha with hac | had
    · rcases hb with hbc | hbd
      · have hdc : d = c := by
          have hm : d ∈ ({c, d} : Finset Point) := by simp
          rw [← h] at hm
          simpa [hac, hbc] using hm
        exact Or.inl ⟨hac, hbc.trans hdc.symm⟩
      · exact Or.inl ⟨hac, hbd⟩
    · rcases hb with hbc | hbd
      · exact Or.inr ⟨had, hbc⟩
      · have hcd : c = d := by
          have hm : c ∈ ({c, d} : Finset Point) := by simp
          rw [← h] at hm
          simpa [had, hbd] using hm
        exact Or.inl ⟨had.trans hcd.symm, hbd⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp [Finset.pair_comm]

private theorem bond_swap (x y : Point) : bond x y = bond y x := by
  by_cases he : x = y
  · subst y
    simp [bond]
  · have hcoords : ¬ (x.1 = y.1 ∧ x.2 = y.2) := by
      intro h
      exact he (Prod.ext h.1 h.2)
    by_cases hxy : x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
    · have hyx : ¬ (y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 ≤ x.2)) := by omega
      simp [bond, hxy, hyx]
    · have hyx : y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 ≤ x.2) := by omega
      simp [bond, hxy, hyx]

private theorem bond_pair (x y : Point) :
    ({(bond x y).1, (bond x y).2} : Finset Point) = {x, y} := by
  by_cases h : x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
  · simp [bond, h]
  · simp [bond, h, Finset.pair_comm]

private theorem bond_eq_iff_pair (x y z t : Point) :
    bond x y = bond z t ↔ ({x, y} : Finset Point) = {z, t} := by
  constructor
  · intro h
    calc
      ({x, y} : Finset Point) = {(bond x y).1, (bond x y).2} := (bond_pair x y).symm
      _ = {(bond z t).1, (bond z t).2} := by rw [h]
      _ = {z, t} := bond_pair z t
  · intro h
    rcases pair_eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact bond_swap _ _

private theorem rev_directionCode (d : Compass) :
    AKLT.Cert.H3.Production.rev (AKLT.Cert.H3.directionCode d) =
      AKLT.Cert.H3.directionCode d.reverse := by
  cases d <;> decide

private theorem legal_direction_leaf_proved : LegalDirectionLeaf := by
  intro w s hraw hrep d
  rcases hrep with ⟨_, hpos, hin, _, _, hused⟩
  have hin' : s.incoming = directionCode (windowArrival w) := by
    simpa using hin
  have hdir : directionCode (direction d.val) = d.val := by
    simpa [Nat.mod_eq_of_lt d.isLt] using directionCode_direction d.val
  have hdelta : delta d.val = (direction d.val).step := by
    fin_cases d <;> rfl
  have hlegal' : s.legal d.val = true ↔
      ∀ i : Fin 10, wordBond (0, 0) w i ≠
        {wordVertex (0, 0) w 10, wordVertex (0, 0) w 10 + delta d.val} := by
    simp [Walk.legal, hused, hpos, bond_eq_iff_pair,
      List.mem_reverse, List.mem_map, AKLT.Cert.H3.Production.advance, wordBond]
    rfl
  have hlegal : s.legal d.val = true ↔
      ∀ i : Fin 10, wordBond (0, 0) w i ≠
        {wordVertex (0, 0) w 10, wordVertex (0, 0) w 10 + (direction d.val).step} := by
    simpa [wordBond, hdelta] using hlegal'
  have hinv (e : Compass) : direction (directionCode e) = e := by
    cases e <;> rfl
  have hrev := rev_directionCode (windowArrival w)
  have hiff : d.val = directionCode (windowArrival w).reverse ↔
      direction d.val = (windowArrival w).reverse := by
    constructor
    · intro he
      exact (congrArg direction he).trans (hinv _)
    · intro he
      have := congrArg directionCode he
      simpa [hdir] using this
  have hneq := not_congr hiff
  rw [hin', hrev]
  simp [hlegal, WindowAdmissible, hneq]

private theorem successor_code_leaf_proved : SuccessorCodeLeaf := by
  intro c hc d
  let c' := (c * 4 + d.val) % 1048576
  have hc' : c' < 1048576 := by dsimp [c']; exact Nat.mod_lt _ (by decide)
  have hwindow : windowSuccessor (decodeWord 10 c) (direction d.val) = decodeWord 10 c' := by
    funext i
    fin_cases i <;> fin_cases d <;>
      simp [windowSuccessor, decodeWord, c'] <;>
      apply congrArg direction <;> omega
  rw [hwindow]
  exact encode_decode_ten c' hc'

private def rawRowLocal (G : Graph) (s : Walk) (d : Nat) : Bool :=
  let a := G.classAt s.code
  let revisit := s.departed.contains s.pos
  let allowed := (d != rev s.incoming) && s.legal d
  (G.allowed a d == allowed) &&
    (!allowed || (decide (G.dest a d ≤ 3741) &&
      (G.kind a d == if revisit then 2 else if d = s.incoming then 0 else 1) &&
      (G.next a d == G.classAt ((s.code * 4 + d) % 1048576)) &&
      (revisit || G.arrival a == s.incoming)))

private theorem rawRow_dir {G : Graph} {s : Walk} (hrow : rawRow G s = true)
    {j : Nat} (hj : j < 4) : rawRowLocal G s j = true := by
  have h := hrow
  change (decide (G.classAt s.code < 3741) && dirs.all (rawRowLocal G s)) = true at h
  rw [Bool.and_eq_true] at h
  rcases h with ⟨_, hall⟩
  have hm : j ∈ dirs := by simp [dirs]; omega
  exact (List.all_eq_true.mp hall) j hm

theorem main : RawRowSoundLeaf := by
  intro G c hc s hraw hrep hrow
  let w : DirectionWord 10 := decodeWord 10 c
  have hrep' : WalkRepresents (0, 0) 0 w s := by simpa [w] using hrep
  rcases hrep' with ⟨hdepth, hpos, hin, hcode, hdepart, hused⟩
  have henc : encodeWord w = c := encode_decode_ten c hc
  have hsc : s.code = c := by
    rw [hcode, henc, Nat.mod_eq_of_lt hc]
  have hclass : G.classAt s.code = G.classAt (encodeWord w) := by
    rw [hsc, henc]
  have htop := hrow
  change (decide (G.classAt s.code < 3741) && dirs.all (rawRowLocal G s)) = true at htop
  rw [Bool.and_eq_true] at htop
  have hbound : G.classAt s.code < 3741 := of_decide_eq_true htop.1
  let a : Fin 3741 := ⟨G.classAt s.code, hbound⟩
  have hproject : G.quotient.project w = a := by
    apply Fin.ext
    change G.classAt (encodeWord w) % 3741 = G.classAt s.code
    rw [← hclass]
    exact Nat.mod_eq_of_lt hbound
  refine ⟨hraw, ?_⟩
  intro e
  let j := directionCode e
  have hj : j < 4 := by cases e <;> decide
  have hdir : direction j = e := by cases e <;> rfl
  let allowed := (j != rev s.incoming) && s.legal j
  let revisit := s.departed.contains s.pos
  have hlocal := rawRow_dir hrow hj
  dsimp [rawRowLocal, allowed, revisit, a] at hlocal
  rw [Bool.and_eq_true] at hlocal
  have hallowedEq : G.allowed (G.classAt s.code) j = allowed := by
    simpa using hlocal.1
  have hAdmissible : allowed = true ↔ WindowAdmissible w e := by
    have h := legal_direction_leaf_proved w s hraw ⟨hdepth, hpos, hin, hcode, hdepart, hused⟩ ⟨j, hj⟩
    simpa [hdir, allowed] using h
  have hrowTail := hlocal.2
  have hQallowed : G.allowed (G.quotient.project w).val (directionCode e) = true ↔
      WindowAdmissible w e := by
    rw [hproject]
    change G.allowed (G.classAt s.code) j = true ↔ WindowAdmissible w e
    rw [hallowedEq]
    exact hAdmissible
  refine ⟨hQallowed, ?_⟩
  intro hadm
  have hallowTrue : allowed = true := hAdmissible.mpr hadm
  have hrowTail' := hrowTail
  simp at hrowTail'
  have hallowProp : j ≠ rev s.incoming ∧ s.legal j = true := by
    simpa [allowed] using hallowTrue
  have hgood : G.kind (G.classAt s.code) j =
      (if revisit then 2 else if j = s.incoming then 0 else 1) ∧
      G.next (G.classAt s.code) j = G.classAt ((s.code * 4 + j) % 1048576) ∧
      (s.pos ∈ s.departed ∨ G.arrival (G.classAt s.code) = s.incoming) := by
    rcases hrowTail' with hbad | hgood
    · rcases hbad with hrev | hlegal
      · exact (hallowProp.1 hrev).elim
      · simp [hlegal] at hallowProp
    · rcases hgood with ⟨hleft, harr⟩
      exact ⟨by simpa [revisit] using hleft.1.2, hleft.2, harr⟩
  have hin' : s.incoming = directionCode (windowArrival w) := by simpa using hin
  have hinv (d : Compass) : direction (directionCode d) = d := by cases d <;> rfl
  have hstraight : j = s.incoming ↔ e = windowArrival w := by
    have hcodes : directionCode e = directionCode (windowArrival w) ↔
        e = windowArrival w := by
      constructor
      · intro he
        calc
          e = direction (directionCode e) := (hinv e).symm
          _ = direction (directionCode (windowArrival w)) := congrArg direction he
          _ = windowArrival w := hinv _
      · rintro rfl
        rfl
    simpa [j, hin'] using hcodes
  have hRevisit : revisit = true ↔
      0 < departureCount (0, 0) w 10 (wordVertex (0, 0) w 10) := by
    dsimp [revisit]
    exact revisit_leaf_proved 10 (0, 0) 0 w s
      ⟨hdepth, hpos, hin, hcode, hdepart, hused⟩
  have hMemRevisit : revisit = true ↔ s.pos ∈ s.departed := by
    simp [revisit]
  have hkind : stepKind (G.kind (G.classAt s.code) j) = windowKind w e := by
    by_cases hvisit : 0 < departureCount (0, 0) w 10 (wordVertex (0, 0) w 10)
    · have hr : revisit = true := hRevisit.mpr hvisit
      have hm : s.pos ∈ s.departed := hMemRevisit.mp hr
      rw [hgood.1, hr]
      simp [stepKind, windowKind, hvisit]
    · have hr : revisit = false := by
        cases hv : revisit with
        | false => rfl
        | true => exact (hvisit (hRevisit.mp hv)).elim
      have hnm : s.pos ∉ s.departed := by
        intro hm
        exact hvisit (hRevisit.mp (hMemRevisit.mpr hm))
      by_cases hs : e = windowArrival w
      · have hst := hstraight.mpr hs
        rw [hgood.1, hr]
        simp [stepKind, windowKind, hvisit, hs, hst]
      · have hnt : j ≠ s.incoming := fun h => hs (hstraight.mp h)
        rw [hgood.1, hr]
        simp [stepKind, windowKind, hvisit, hs, hnt]
  have hsuccCode : encodeWord (windowSuccessor w e) = (c * 4 + j) % 1048576 := by
    have hs := successor_code_leaf_proved c hc ⟨j, hj⟩
    simpa [hdir] using hs
  have hnextQ : G.quotient.successor (G.quotient.project w) e =
      G.quotient.project (windowSuccessor w e) := by
    rw [hproject]
    change finState (G.next (G.classAt s.code) j) =
      finState (G.classAt (encodeWord (windowSuccessor w e)))
    rw [hgood.2.1, hsuccCode, hsc]
  refine ⟨?_, hnextQ, ?_⟩
  · rw [hproject]
    change stepKind (G.kind (G.classAt s.code) j) = windowKind w e
    exact hkind
  · intro hkindNot
    have hnotvisit : ¬ 0 < departureCount (0, 0) w 10 (wordVertex (0, 0) w 10) := by
      intro hvisit
      apply hkindNot
      simp [windowKind, w, hvisit]
    have hrv : revisit = false := by
      cases hv : revisit with
      | false => rfl
      | true => exact (hnotvisit (hRevisit.mp hv)).elim
    have hnm : s.pos ∉ s.departed := by
      intro hm
      exact hnotvisit (hRevisit.mp (hMemRevisit.mpr hm))
    have hArrival : G.arrival (G.classAt s.code) = s.incoming := by
      rcases hgood.2.2 with hm | har
      · exact (hnm hm).elim
      · exact har
    rw [hproject]
    change direction (G.arrival (G.classAt s.code)) = windowArrival w
    rw [hArrival, hin']
    exact hinv _

#print axioms main

end AKLT.W.H3C009
