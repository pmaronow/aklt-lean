import AKLT.W.H3C034.Tree
import AKLT.W.H3C001.Main
import AKLT.W.H3C002.Main
import AKLT.W.H3C019.Main
import AKLT.Cert.H2.Words

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge
open AKLT.Cert.H2

namespace AKLT.W.H3C034

set_option maxHeartbeats 2000000

theorem decodeWord_mod (n c : Nat) : decodeWord n (c % 4^n) = decodeWord n c := by
  funext i
  unfold decodeWord
  congr 1
  let k := n-1-i.val
  have hk : k < n := by dsimp [k]; omega
  have hp : 4^n = 4^k * 4^(n-k) := by rw [← pow_add, Nat.add_sub_of_le (Nat.le_of_lt hk)]
  rw [hp, Nat.mod_mul_right_div_self]
  exact Nat.mod_mod_of_dvd _ (dvd_pow_self 4 (by omega : n-k ≠ 0))

theorem lastWindowCode : LastWindowCodeLeaf := by
  intro n hn w
  have hs : lastWindowWord 10 (decodeWord n (encodeWord w)) = decodeWord 10 (encodeWord w) := by
    funext i
    simp only [lastWindowWord, dite_eq_left (show n-10+i.val < n by omega), decodeWord]
    rw [show n-1-(n-10+i.val) = 10-1-i.val by omega]
  rw [(AKLT.W.H3C002.main n w).2] at hs
  rw [hs, ← decodeWord_mod]
  exact AKLT.W.H3C001.main 10 _ (Nat.mod_lt _ (by decide))

theorem decodeWord_snoc (n c d : Nat) (hd : d < 4) :
    decodeWord (n+1) (c*4+d) = snoc (decodeWord n c) (direction d) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [decodeWord, snoc, Nat.add_mod, Nat.mod_eq_of_lt hd]
  · simp only [snoc, Fin.snoc_castSucc]
    unfold decodeWord
    simp only [Fin.val_castSucc]
    have hk : n+1-1-j.val = (n-1-j.val)+1 := by omega
    rw [hk, pow_succ, Nat.mul_comm (4^(n-1-j.val)), ← Nat.div_div_eq_div_mul,
      Nat.mul_comm c 4, Nat.mul_add_div (by decide), Nat.div_eq_of_lt hd]
    simp

theorem decodeWord_last (n c : Nat) :
    decodeWord (n+1) c = snoc (decodeWord n (c/4)) (direction (c%4)) := by
  have h := decodeWord_snoc n (c/4) (c%4) (Nat.mod_lt _ (by decide))
  rw [Nat.mul_comm (c/4), Nat.div_add_mod] at h
  exact h

theorem runNode_snoc (E : Exact) (X : PairType) (d₀ n c d : Nat)
    (hd : d < 4) (s : PrefixState) :
    runNode E X d₀ (n+1) (c*4+d) s =
      (runNode E X d₀ n c s).bind (nextNode E X d₀ d) := by
  have h := runNode_split E X d₀ n 1 c d (by simpa using hd) s
  have heq : runNode E X d₀ 1 d = nextNode E X d₀ d := by
    funext t
    simp [runNode, Nat.mod_eq_of_lt hd]
  simpa only [pow_one, heq] using h

theorem runNode_last (E : Exact) (X : PairType) (d₀ n c : Nat) (s : PrefixState) :
    runNode E X d₀ (n+1) c s =
      (runNode E X d₀ n (c/4) s).bind (nextNode E X d₀ (c%4)) := by
  have h := runNode_snoc E X d₀ n (c/4) (c%4) (Nat.mod_lt _ (by decide)) s
  rw [Nat.mul_comm (c/4), Nat.div_add_mod] at h
  exact h

theorem append_one_eq_snoc {n : Nat} (w : DirectionWord n) (d : Compass) :
    appendWords w (fun _ : Fin 1 => d) = snoc w d := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [appendWords]
  · simp [appendWords, snoc, j.isLt]

theorem direction_step (d : Fin 4) : delta d.val = (direction d.val).step := by
  fin_cases d <;> rfl

theorem advance_eq (x : Point) (d : Fin 4) : advance x d.val = x + (direction d.val).step := by
  change x + delta d.val = _
  rw [direction_step]

theorem transition_walk (E : Exact) (s : PrefixState) (d : Nat) :
    (transition E s d).walk = s.walk.step d := by
  simp only [transition]
  split_ifs <;> rfl

theorem bond_symm (x y : Point) : bond x y = bond y x := by
  unfold bond
  split_ifs with hxy hyx hyx
  · have he : x=y := Prod.ext (by omega) (by omega)
    subst y
    rfl
  · rfl
  · rfl
  · omega

theorem bond_iff (x y z t : Point) :
    bond x y = bond z t ↔ ({x,y} : Finset Point) = {z,t} := by
  constructor
  · intro h
    have := congrArg (fun p : Point × Point => ({p.1,p.2} : Finset Point)) h
    unfold bond at this
    split_ifs at this <;> simpa [Finset.pair_comm] using this
  · intro h
    have hx : x=z ∨ x=t := by
      have hx : x ∈ ({z,t} : Finset Point) := h ▸ (by simp)
      simpa using hx
    have hy : y=z ∨ y=t := by
      have hy : y ∈ ({z,t} : Finset Point) := h ▸ (by simp)
      simpa using hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · subst x; subst y
      have hz : t=z := by
        have ht : t ∈ ({z,z} : Finset Point) := h.symm ▸ (by simp)
        simpa using ht
      subst t
      rfl
    · subst x; subst y; rfl
    · subst x; subst y; exact bond_symm _ _
    · subst x; subst y
      have hz : z=t := by
        have ht : z ∈ ({t,t} : Finset Point) := h.symm ▸ (by simp)
        simpa using ht
      subst z
      rfl

theorem legal_iff {n : Nat} (w : DirectionWord n) (s : PrefixState)
    (hrep : WalkRepresents kernelStart 2 w s.walk) (d : Fin 4) :
    s.walk.legal d.val = true ↔
      ∀ i : Fin n, wordBond kernelStart w i ≠
        {wordVertex kernelStart w n, wordVertex kernelStart w n + (direction d.val).step} := by
  rcases hrep with ⟨_, hp, _, _, _, hu⟩
  simp only [Walk.legal, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not]
  rw [hu]
  simp only [List.mem_map, List.mem_reverse, List.mem_finRange, true_and, not_exists]
  rw [hp, advance_eq]
  constructor
  · intro h i he
    exact h i ((bond_iff _ _ _ _).2 he)
  · intro h i he
    exact h i ((bond_iff _ _ _ _).1 he)

theorem trail_snoc_iff {n : Nat} (w : DirectionWord n) (d : Compass)
    (hn : 1 ≤ n) (hw : IsTrail kernelStart kernelIncoming w) :
    IsTrail kernelStart kernelIncoming (snoc w d) ↔
      ∀ i : Fin n, wordBond kernelStart w i ≠
        {wordVertex kernelStart w n, wordVertex kernelStart w n + d.step} := by
  constructor
  · exact fun h => snoc_fresh _ _ _ _ h
  · intro hf
    constructor
    · intro i j hij
      induction i using Fin.lastCases <;> induction j using Fin.lastCases
      · rfl
      · exact False.elim (hf _ (by simpa only [snoc_last_bond, snoc_bond] using hij.symm))
      · exact False.elim (hf _ (by simpa only [snoc_last_bond, snoc_bond] using hij))
      · exact congrArg Fin.castSucc (hw.1 (by simpa only [snoc_bond] using hij))
    · intro i hi
      have hil : i.val < n := by omega
      rw [snoc_apply_lt w d i.val hil]
      exact hw.2 _ hi

theorem goodStep_iff {n : Nat} (w : DirectionWord n) (s : PrefixState)
    (hrep : WalkRepresents kernelStart 2 w s.walk) (hn : 1 ≤ n)
    (hw : IsTrail kernelStart kernelIncoming w) (d₀ : Nat) (d : Fin 4) :
    goodStep d₀ s.walk d.val = true ↔
      IsTrail kernelStart kernelIncoming (snoc w (direction d.val)) ∧
        wordVertex kernelStart (snoc w (direction d.val)) (n+1) ≠ kernelCentre := by
  have hv : wordVertex kernelStart (snoc w (direction d.val)) (n+1) =
      advance s.walk.pos d.val := by
    rw [vertex_succ _ _ n (by omega), snoc_vertex _ _ _ n le_rfl, hrep.2.1,
      show (⟨n, by omega⟩ : Fin (n+1)) = Fin.last n by rfl, snoc_last, advance_eq]
  rw [goodStep, hrep.1]
  simp only [bne_iff_ne, ne_eq, Bool.or_eq_true, beq_iff_eq,
    show ¬ n=0 by omega, not_false_eq_true, true_or, Bool.and_eq_true, true_and]
  rw [legal_iff w s hrep d, ← trail_snoc_iff w _ hn hw, hv]
  rfl

theorem first_snoc_iff {n : Nat} (w : DirectionWord n) (d d₀ : Compass) (hn : 1 ≤ n) :
    FirstDirection (snoc w d) d₀ ↔ FirstDirection w d₀ := by
  constructor
  · rintro ⟨i, hi, hd⟩
    have hil : i.val < n := by omega
    exact ⟨⟨i.val, hil⟩, hi, by simpa only [snoc_apply_lt w d i.val hil] using hd⟩
  · rintro ⟨i, hi, hd⟩
    exact ⟨i.castSucc, hi, by simpa [snoc] using hd⟩

end AKLT.W.H3C034
