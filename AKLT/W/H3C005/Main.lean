module
public import CertData.H3.Bridge.Interface

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H3C005
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production AKLT.Gen.Packed
open CertData.H3.Bridge

private theorem decode_succ_head (n c : Nat) :
    decodeWord (n+1) c ⟨0, by omega⟩ = direction ((c / 4^n) % 4) := by
  simp [decodeWord]

private theorem decode_succ_tail (n c : Nat) (i : Fin n) :
    decodeWord (n+1) c i.succ = decodeWord n c i := by
  simp only [decodeWord, Fin.val_succ]
  have h : n + 1 - 1 - (i.val + 1) = n - 1 - i.val := by omega
  rw [h]

private theorem directionCode_direction (x : Nat) (hx : x < 4) :
    directionCode (direction x) = x := by
  interval_cases x <;> simp [direction, directionCode] at *

private theorem encode_succ {n : Nat} (w : DirectionWord (n+1)) :
    encodeWord w = directionCode (w ⟨0, by omega⟩) * 4^n +
      encodeWord (fun i : Fin n => w i.succ) := by
  unfold encodeWord
  rw [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map]
  simp only [Fin.val_zero, Nat.sub_zero]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i hi
  simp only [Function.comp_apply, Fin.val_succ]
  congr 2
  omega

private theorem encode_decode_mod : ∀ n c : Nat,
    encodeWord (decodeWord n c) = c % 4^n := by
  intro n
  induction n with
  | zero => intro c; simp [encodeWord, decodeWord, Nat.mod_one]
  | succ n ih =>
    intro c
    rw [encode_succ]
    have ht : (fun i : Fin n => decodeWord (n+1) c i.succ) = decodeWord n c := by
      funext i
      exact decode_succ_tail n c i
    rw [ht, decode_succ_head]
    rw [directionCode_direction ((c / 4^n) % 4) (Nat.mod_lt _ (by omega)), ih]
    rw [show 4^(n+1) = 4^n * 4 by rw [pow_succ]]
    have hp : 0 < 4^n := by positivity
    have hmod : (c / 4^n % 4) * 4^n + c % 4^n = c % (4^n * 4) := by
      let p := 4^n
      have hp' : 0 < p := by dsimp [p]; positivity
      have hc : c % p + p * (c / p) = c := Nat.mod_add_div c p
      have hq : (c / p) % 4 + 4 * (c / p / 4) = c / p := Nat.mod_add_div (c / p) 4
      have hdiv : c / (p * 4) = c / p / 4 := by
        rw [Nat.div_div_eq_div_mul]
      have hrem : (c / p % 4) * p + c % p < p * 4 := by
        have hd : c / p % 4 < 4 := Nat.mod_lt _ (by omega)
        have hd3 : c / p % 4 ≤ 3 := by omega
        have hr : c % p < p := Nat.mod_lt _ hp'
        have hdp : (c / p % 4) * p ≤ 3 * p := Nat.mul_le_mul_right p hd3
        omega
      have hdecomp : c = (c / (p*4)) * (p*4) + ((c/p%4)*p + c%p) := by
        calc
          c = c % p + p * (c / p) := hc.symm
          _ = c % p + p * ((c/p)%4 + 4*(c/p/4)) := by rw [hq]
          _ = (c/p/4)*(p*4) + ((c/p%4)*p+c%p) := by ring
          _ = (c/(p*4))*(p*4) + ((c/p%4)*p+c%p) := by rw [← hdiv]
      have hmod' : c % (p*4) = (c/p%4)*p + c%p := by
        calc
          c % (p*4) = ((c/(p*4))*(p*4) + ((c/p%4)*p+c%p)) % (p*4) :=
            congrArg (fun x => x % (p*4)) hdecomp
          _ = ((p*4) * (c/(p*4)) + ((c/p%4)*p+c%p)) % (p*4) := by rw [Nat.mul_comm]
          _ = ((c/p%4)*p+c%p) % (p*4) := by rw [Nat.add_comm, Nat.add_mul_mod_self_left]
          _ = (c/p%4)*p+c%p := Nat.mod_eq_of_lt hrem
      exact hmod'.symm
    simpa using hmod
  
private theorem wordVertex_succ {n : Nat} (u : Plane) (w : DirectionWord n) (i : Fin n) :
    wordVertex u w (i.val + 1) = wordVertex u w i.val + (w i).step := by
  classical
  unfold wordVertex
  have hsum : ∀ k : Fin n,
      (if k.val < i.val + 1 then (w k).step else 0) =
        (if k.val < i.val then (w k).step else 0) +
          (if k = i then (w i).step else 0) := by
    intro k
    by_cases hk : k.val < i.val
    · have hki : k ≠ i := by intro h; subst k; omega
      have hlt : k.val < i.val + 1 := by omega
      simp [hk, hki, hlt]
    · by_cases hki : k = i
      · subst k
        simp
      · have hnot : ¬ k.val < i.val + 1 := by omega
        simp [hk, hki, hnot]
  simp_rw [hsum]
  rw [Finset.sum_add_distrib]
  simp
  abel

private theorem wordVertex_cons_at {n : Nat} (u : Plane) (w : DirectionWord (n+1))
    (j : Nat) (hj : j ≤ n) :
    wordVertex u w (j+1) =
      wordVertex (u + (w ⟨0, by omega⟩).step) (fun i : Fin n => w i.succ) j := by
  induction j with
  | zero =>
      simp [wordVertex]
  | succ j ih =>
      have hjn : j < n := by omega
      rw [wordVertex_succ u w ⟨j+1, by omega⟩,
        ih (by omega), wordVertex_succ (u + (w ⟨0, by omega⟩).step)
          (fun i : Fin n => w i.succ) ⟨j, hjn⟩]
      simp

private theorem wordVertex_zero {n : Nat} (u : Plane) (w : DirectionWord n) :
    wordVertex u w 0 = u := by simp [wordVertex]

private theorem departedList_cons {n : Nat} (u : Plane) (w : DirectionWord (n+1)) :
    (List.finRange (n+1)).reverse.map (fun i => wordVertex u w i.val) =
      ((List.finRange n).reverse.map (fun i =>
        wordVertex (u + (w ⟨0, by omega⟩).step) (fun i : Fin n => w i.succ) i.val)) ++ [u] := by
  rw [List.finRange_succ, List.reverse_cons, List.map_append, ← List.map_reverse, List.map_map]
  simp only [List.map_singleton, Fin.val_zero]
  rw [wordVertex_zero]
  change List.map (fun i : Fin n => wordVertex u w (i.val+1)) (List.finRange n).reverse ++ [u] = _
  apply congrArg (fun xs => xs ++ [u])
  apply List.map_congr_left
  intro i hi
  exact wordVertex_cons_at u w i.val (by omega)

private theorem usedList_cons {n : Nat} (u : Plane) (w : DirectionWord (n+1)) :
    (List.finRange (n+1)).reverse.map (fun i =>
      bond (wordVertex u w i.val) (wordVertex u w (i.val+1))) =
      ((List.finRange n).reverse.map (fun i =>
        bond (wordVertex (u + (w ⟨0, by omega⟩).step) (fun i : Fin n => w i.succ) i.val)
          (wordVertex (u + (w ⟨0, by omega⟩).step) (fun i : Fin n => w i.succ) (i.val+1)))) ++
        [bond u (u + (w ⟨0, by omega⟩).step)] := by
  rw [List.finRange_succ, List.reverse_cons, List.map_append, ← List.map_reverse, List.map_map]
  simp only [List.map_singleton, Fin.val_zero]
  rw [wordVertex_zero, wordVertex_cons_at u w 0 (by omega),
    wordVertex_zero (u := u + (w ⟨0, by omega⟩).step)
      (w := fun i : Fin n => w i.succ)]
  change List.map (fun i : Fin n => bond (wordVertex u w (i.val+1))
      (wordVertex u w (i.val+2))) (List.finRange n).reverse ++
      [bond u (u + (w ⟨0, by omega⟩).step)] = _
  apply congrArg (fun xs => xs ++ [bond u (u + (w ⟨0, by omega⟩).step)])
  apply List.map_congr_left
  intro i hi
  have h0 := wordVertex_cons_at u w i.val (by omega)
  have h1 := wordVertex_cons_at u w (i.val+1) (by omega)
  simpa [Fin.val_succ] using congrArg₂ bond h0 h1

private theorem windowArrival_decode_succ (n c : Nat) :
    windowArrival (decodeWord (n+1) c) =
      if n = 0 then direction ((c / 4^n) % 4) else windowArrival (decodeWord n c) := by
  cases n with
  | zero => simp [windowArrival, decodeWord]
  | succ n =>
      simp [windowArrival]
      exact decode_succ_tail (n+1) c ⟨n, by omega⟩


private def ReplayTrace (n c : Nat) (w s : Walk) : Prop :=
  s.depth = w.depth + n ∧
  s.pos = wordVertex w.pos (decodeWord n c) n ∧
  s.incoming = (if n = 0 then w.incoming else
    directionCode (windowArrival (decodeWord n c))) ∧
  s.departed = ((List.finRange n).reverse.map fun i =>
      wordVertex w.pos (decodeWord n c) i.val) ++ w.departed ∧
  s.used = ((List.finRange n).reverse.map fun i =>
      bond (wordVertex w.pos (decodeWord n c) i.val)
        (wordVertex w.pos (decodeWord n c) (i.val+1))) ++ w.used

private theorem replayRaw_trace : ∀ n c (w s : Walk),
    replayRaw n c w = some s → w.used.Nodup →
      ReplayTrace n c w s ∧ s.used.Nodup := by
  intro n
  induction n with
  | zero =>
      intro c w s h hnd
      simp only [replayRaw] at h
      injection h with hs
      subst s
      constructor
      · simp [ReplayTrace, wordVertex_zero]
      · exact hnd
  | succ n ih =>
      intro c w s h hnd
      dsimp only [replayRaw] at h
      let d := c / 4^n % 4
      by_cases hlegal : w.legal d
      · simp [d, hlegal] at h
        have hnot : bond w.pos (advance w.pos d) ∉ w.used := by
          have hc : w.used.contains (bond w.pos (advance w.pos d)) = false := by
            simpa [Walk.legal, d] using hlegal
          simpa using hc
        have hndStep : (w.step d).used.Nodup := by
          simpa [Walk.step] using List.nodup_cons.mpr ⟨hnot, hnd⟩
        have hr := ih c (w.step d) s h hndStep
        rcases hr with ⟨⟨hdepth,hpos,hinc,hdepart,hused⟩,hndOut⟩
        have hdlt : d < 4 := by dsimp [d]; exact Nat.mod_lt _ (by omega)
        have hadvance : advance w.pos d = w.pos + (direction d).step := by
          interval_cases d <;> simp [advance, direction, delta, Compass.step, Prod.add_def]
        have hstepPos : (w.step d).pos = w.pos + (direction d).step := by
          simp [Walk.step, hadvance]
        have hhead : decodeWord (n+1) c ⟨0, by omega⟩ = direction d := by
          simpa [d] using decode_succ_head n c
        have htail : (fun i : Fin n => decodeWord (n+1) c i.succ) = decodeWord n c := by
          funext i
          exact decode_succ_tail n c i
        constructor
        · refine ⟨?_, ?_, ?_, ?_, ?_⟩
          · dsimp [Walk.step] at hdepth
            omega
          · calc
              s.pos = wordVertex (w.step d).pos (decodeWord n c) n := hpos
              _ = wordVertex (w.pos + (direction d).step) (decodeWord n c) n := by
                    change wordVertex (advance w.pos d) (decodeWord n c) n = _
                    rw [hadvance]
              _ = wordVertex (w.pos + (decodeWord (n+1) c ⟨0, by omega⟩).step)
                    (fun i : Fin n => decodeWord (n+1) c i.succ) n := by rw [hhead, htail]
              _ = wordVertex w.pos (decodeWord (n+1) c) (n+1) := by
                    rw [wordVertex_cons_at w.pos (decodeWord (n+1) c) n (by omega)]
          · rw [hinc]
            by_cases hn : n = 0
            · subst n
              simp [Walk.step, d, windowArrival_decode_succ,
                directionCode_direction (c % 4) (Nat.mod_lt _ (by omega))]
            · simp [hn, windowArrival_decode_succ]
          · have hdepart' := hdepart
            simp only [Walk.step] at hdepart'
            rw [hdepart', departedList_cons]
            simp only [hadvance, hhead, htail]
            simp [List.append_assoc]
          · have hused' := hused
            simp only [Walk.step] at hused'
            rw [hused', usedList_cons]
            simp only [hadvance, hhead, htail]
            simp [List.append_assoc]
        · exact hndOut
      · simp [d, hlegal] at h

private theorem replayRaw_code : ∀ n c (w s : Walk),
    replayRaw n c w = some s → w.code < 1048576 →
      s.code = (w.code * 4^n + encodeWord (decodeWord n c)) % 1048576 := by
  intro n
  induction n with
  | zero =>
      intro c w s h hcode
      simp only [replayRaw] at h
      injection h with hs
      subst s
      simp [encodeWord, Nat.mod_eq_of_lt hcode]
  | succ n ih =>
      intro c w s h hcode
      dsimp only [replayRaw] at h
      let d := c / 4^n % 4
      by_cases hlegal : w.legal d
      · simp [d, hlegal] at h
        have hdlt : d < 4 := by dsimp [d]; exact Nat.mod_lt _ (by omega)
        have hstepcode : (w.step d).code < 1048576 := by
          simp [Walk.step]
          exact Nat.mod_lt _ (by omega)
        have hih := ih c (w.step d) s h hstepcode
        have hhead : directionCode ((decodeWord (n+1) c) ⟨0, by omega⟩) = d := by
          rw [decode_succ_head]
          exact directionCode_direction d hdlt
        have htail : (fun i : Fin n => decodeWord (n+1) c i.succ) = decodeWord n c := by
          funext i
          exact decode_succ_tail n c i
        rw [hih, encode_succ, hhead, htail]
        simp only [Walk.step]
        have hcong : Nat.ModEq 1048576
            (((w.code*4+d)%1048576)*4^n + encodeWord (decodeWord n c))
            ((w.code*4+d)*4^n + encodeWord (decodeWord n c)) := by
          exact Nat.ModEq.add
            (Nat.ModEq.mul_right (4^n) (Nat.mod_modEq (w.code*4+d) 1048576))
            (Nat.ModEq.rfl)
        change (((w.code*4+d)%1048576)*4^n + encodeWord (decodeWord n c)) % 1048576 =
          ((w.code*4+d)*4^n + encodeWord (decodeWord n c)) % 1048576 at hcong
        rw [hcong]
        rw [pow_succ]
        ring_nf
      · simp [d, hlegal] at h

private theorem bond_comm (x y : Point) : bond x y = bond y x := by
  unfold bond
  by_cases heq : x = y
  · subst y
    simp
  · by_cases hxy : x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
    · have hyx : ¬ (y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 ≤ x.2)) := by
        intro h
        apply heq
        apply Prod.ext <;> omega
      simp [hxy, hyx]
    · have hyx : y.1 < x.1 ∨ (y.1 = x.1 ∧ y.2 ≤ x.2) := by omega
      simp [hxy, hyx]

private theorem bond_eq_of_pairSet_eq (x y z t : Point)
    (h : ({x,y} : Finset Point) = {z,t}) : bond x y = bond z t := by
  have hm (a : Point) : (a=x ∨ a=y) ↔ (a=z ∨ a=t) := by
    have hh := congrArg (fun q : Finset Point => a ∈ q) h
    simpa using hh
  have hx : x=z ∨ x=t := (hm x).mp (Or.inl rfl)
  have hy : y=z ∨ y=t := (hm y).mp (Or.inr rfl)
  rcases hx with hx | hx
  · subst x
    rcases hy with hy | hy
    · subst y
      have ht := (hm t).mpr (Or.inr rfl)
      rcases ht with ht | ht <;> subst t <;> simp [bond]
    · subst y
      rfl
  · subst x
    rcases hy with hy | hy
    · subst y
      exact (bond_comm z t).symm
    · subst y
      have hz := (hm z).mpr (Or.inl rfl)
      rcases hz with hz | hz <;> subst z <;> simp [bond]

private theorem rawWindow_of_used_nodup {n : Nat} (w : DirectionWord n) (s : Walk)
    (hused : s.used = (List.finRange n).reverse.map (fun i =>
      bond (wordVertex (0,0) w i.val) (wordVertex (0,0) w (i.val+1))))
    (hnd : s.used.Nodup) : RawWindow w := by
  have hmap : ((List.finRange n).reverse.map (fun i =>
      bond (wordVertex (0,0) w i.val) (wordVertex (0,0) w (i.val+1)))).Nodup := by
    rw [← hused]
    exact hnd
  have hinjOn := (List.nodup_map_iff_inj_on
    (List.nodup_reverse.mpr (List.nodup_finRange n))).mp hmap
  intro i j hij
  apply hinjOn i (by simp) j (by simp)
  exact bond_eq_of_pairSet_eq _ _ _ _ hij

private theorem codeDecodeLeaf : CodeDecodeLeaf := by
  intro n c hc
  rw [encode_decode_mod]
  exact Nat.mod_eq_of_lt hc

theorem main : CertData.H3.Bridge.RawReplaySoundLeaf := by
  intro n c hn hc s hs
  have htrace := replayRaw_trace n c rawInitial s hs (by simp [rawInitial])
  rcases htrace with ⟨⟨hdepth,hpos,hinc,hdepart,hused⟩,hnd⟩
  have hcode := replayRaw_code n c rawInitial s hs (by simp [rawInitial])
  have hdecode : encodeWord (decodeWord n c) = c := codeDecodeLeaf n c hc
  have hcodeC : s.code = c % 1048576 := by
    simp [rawInitial, hdecode] at hcode
    exact hcode
  have hused' : s.used = (List.finRange n).reverse.map (fun i =>
      bond (wordVertex (0,0) (decodeWord n c) i.val)
        (wordVertex (0,0) (decodeWord n c) (i.val+1))) := by
    simpa [rawInitial] using hused
  have hwalk : WalkRepresents (0,0) 0 (decodeWord n c) s := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [rawInitial] using hdepth
    · exact hpos
    · exact hinc
    · exact hcodeC.trans (congrArg (fun x : Nat => x % 1048576) hdecode.symm)
    · simpa [rawInitial] using hdepart
    · exact hused'
  refine ⟨rawWindow_of_used_nodup (decodeWord n c) s hused' hnd, hwalk⟩

end AKLT.W.H3C005
