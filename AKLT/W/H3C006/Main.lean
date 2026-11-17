module
public import CertData.H3.Bridge.Interface
public import AKLT.Cert.H2.Words

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

set_option maxRecDepth 100000

namespace AKLT.W.H3C006

open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production

private def pathBond {n : Nat} (p : Plane) (w : DirectionWord n) (i : Fin n) : Bond :=
  bond (wordVertex p w i.val) (wordVertex p w (i.val + 1))

private def SafePath {n : Nat} (s : Walk) (w : DirectionWord n) : Prop :=
  (∀ i, pathBond s.pos w i ∉ s.used) ∧ Function.Injective (pathBond s.pos w)

private theorem bond_edgeSet (x y : Plane) :
    ({x, y} : Finset Plane) = {(bond x y).1, (bond x y).2} := by
  unfold bond
  split_ifs <;> simp [Finset.pair_comm]

private theorem bond_eq_edgeSet {x y x' y' : Plane} (h : bond x y = bond x' y') :
    ({x, y} : Finset Plane) = {x', y'} := by
  calc
    ({x, y} : Finset Plane) = {(bond x y).1, (bond x y).2} := bond_edgeSet x y
    _ = {(bond x' y').1, (bond x' y').2} := by rw [h]
    _ = {x', y'} := (bond_edgeSet x' y').symm

private theorem rawWindow_safe {n : Nat} (w : DirectionWord n) (hw : RawWindow w) :
    SafePath rawInitial w := by
  constructor
  · intro i
    simp [rawInitial, pathBond]
  · intro i j hij
    apply hw
    have hset := bond_eq_edgeSet hij
    simpa [rawInitial, pathBond, wordBond] using hset

private theorem direction_delta (d : Nat) (hd : d < 4) : delta d = (direction d).step := by
  interval_cases d <;> rfl

private theorem pair_add_coords (p q : Plane) :
    p + q = (p.1 + q.1, p.2 + q.2) := by
  cases p with
  | mk x y => cases q with | mk a b => rfl

private theorem firstEdge_eq_pathBond {n : Nat} (p : Plane) (w : DirectionWord (n + 1))
    (d : Nat) (hhead : w ⟨0, by omega⟩ = direction d) (hd : d < 4) :
    pathBond p w ⟨0, by omega⟩ = bond p (advance p d) := by
  simp only [pathBond]
  rw [AKLT.Cert.H2.vertex_succ p w 0 (by omega), hhead]
  rw [AKLT.Cert.H2.vertex_zero]
  rw [advance, direction_delta d hd, pair_add_coords]

private theorem tailVertex_shift {n : Nat} (p : Plane) (w : DirectionWord (n + 1))
    (d : Compass) (hd : w ⟨0, by omega⟩ = d) (i : Nat) (hi : i ≤ n) :
    wordVertex (p + d.step) (AKLT.Cert.H2.slice w 1 n (by omega)) i =
      wordVertex p w (i + 1) := by
  have hs := AKLT.Cert.H2.slice_vertex p w 1 n (by omega) i hi
  rw [show 1 + i = i + 1 by omega] at hs
  rw [AKLT.Cert.H2.vertex_translate, hs]
  rw [AKLT.Cert.H2.vertex_succ p w 0 (by omega), hd]
  rw [AKLT.Cert.H2.vertex_zero]
  abel

private theorem tailBond_shift {n : Nat} (p : Plane) (w : DirectionWord (n + 1))
    (d : Compass) (hhead : w ⟨0, by omega⟩ = d) (i : Fin n) :
    pathBond (p + d.step) (AKLT.Cert.H2.slice w 1 n (by omega)) i = pathBond p w i.succ := by
  have h0 := tailVertex_shift p w d hhead i.val (by omega)
  have h1 := tailVertex_shift p w d hhead (i.val + 1) (by omega)
  simp only [pathBond]
  rw [h0, h1]
  simp [Fin.val_succ, Nat.add_assoc]

private theorem replayRaw_safe {n : Nat} (c : Nat) (s : Walk)
    (hsafe : SafePath s (decodeWord n c)) : (replayRaw n c s).isSome = true := by
  induction n generalizing c s with
  | zero => rfl
  | succ n ih =>
    let w : DirectionWord (n + 1) := decodeWord (n + 1) c
    let d : Nat := c / 4 ^ n % 4
    have hd : d < 4 := Nat.mod_lt _ (by decide)
    have hhead : w ⟨0, by omega⟩ = direction d := by
      simp [w, d, decodeWord]
    have htail : AKLT.Cert.H2.slice w 1 n (by omega) = decodeWord n c := by
      funext i
      change direction (c / 4 ^ ((n + 1) - 1 - (1 + i.val)) % 4) =
        direction (c / 4 ^ (n - 1 - i.val) % 4)
      have he : (n + 1) - 1 - (1 + i.val) = n - 1 - i.val := by omega
      rw [he]
    have hsafeTail : SafePath (s.step d) (decodeWord n c) := by
      rw [← htail]
      constructor
      · intro i
        have hvertex :
            wordVertex (s.pos + (direction d).step)
              (AKLT.Cert.H2.slice w 1 n (by omega)) i.val =
              wordVertex s.pos w (i.val + 1) :=
          tailVertex_shift s.pos w (direction d) hhead i.val (by omega)
        have hedge : pathBond (s.step d).pos (AKLT.Cert.H2.slice w 1 n (by omega)) i =
            pathBond s.pos w i.succ := by
          have hadv : advance s.pos d = s.pos + (direction d).step := by
            rw [advance, direction_delta d hd, pair_add_coords]
          change pathBond (advance s.pos d) (AKLT.Cert.H2.slice w 1 n (by omega)) i = _
          rw [hadv]
          exact tailBond_shift s.pos w (direction d) hhead i
        rw [hedge]
        change pathBond s.pos w i.succ ∉ (bond s.pos (advance s.pos d) :: s.used)
        have hused : pathBond s.pos w i.succ ∉ s.used := hsafe.1 i.succ
        have hnew : bond s.pos (advance s.pos d) ≠ pathBond s.pos w i.succ := by
          intro he
          have hfirst : pathBond s.pos w ⟨0, by omega⟩ = pathBond s.pos w i.succ := by
            exact (by
              have hf := firstEdge_eq_pathBond s.pos w d hhead hd
              exact hf.trans he)
          have hidx : (⟨0, by omega⟩ : Fin (n + 1)) ≠ i.succ := by
            intro hh
            have hv := congrArg Fin.val hh
            simp at hv
          exact hidx (hsafe.2 hfirst)
        simp only [List.mem_cons]
        exact fun hm => by
          rcases hm with hnew' | hused'
          · exact hnew (hnew'.symm)
          · exact hused hused'
      · intro i j hij
        have hedge : pathBond s.pos w i.succ = pathBond s.pos w j.succ := by
          have hadv : advance s.pos d = s.pos + (direction d).step := by
            rw [advance, direction_delta d hd, pair_add_coords]
          have hi := tailBond_shift s.pos w (direction d) hhead i
          have hj := tailBond_shift s.pos w (direction d) hhead j
          have hij' : pathBond (s.pos + (direction d).step)
              (AKLT.Cert.H2.slice w 1 n (by omega)) i =
              pathBond (s.pos + (direction d).step)
                (AKLT.Cert.H2.slice w 1 n (by omega)) j := by
            simpa [Walk.step, hadv] using hij
          exact hi.symm.trans (hij'.trans hj)
        have hinj := hsafe.2 hedge
        exact Fin.succ_injective _ hinj
    have hlegal : (s.legal d) = true := by
      have hfirst : pathBond s.pos w ⟨0, by omega⟩ = bond s.pos (advance s.pos d) :=
        firstEdge_eq_pathBond s.pos w d hhead hd
      have hfresh : bond s.pos (advance s.pos d) ∉ s.used := by
        have hsafeFirst := hsafe.1 (⟨0, by omega⟩ : Fin (n + 1))
        change pathBond s.pos w ⟨0, by omega⟩ ∉ s.used at hsafeFirst
        rw [← hfirst]
        exact hsafeFirst
      simpa [Walk.legal] using hfresh
    simpa [replayRaw, d, hlegal] using (ih c (s.step d) hsafeTail)

theorem main : CertData.H3.Bridge.RawReplayCompleteLeaf := by
  intro n c _ _ hraw
  exact replayRaw_safe c rawInitial (rawWindow_safe (decodeWord n c) hraw)

#print axioms main

end AKLT.W.H3C006
