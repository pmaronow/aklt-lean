module
public import AKLT.Blueprint.Gap.NodesPeriodic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

open AKLT.Challenge AKLT.Blueprint.Gap AKLT.Defs

namespace AKLT.W.GAP032

private theorem cycleColor_lt_three (m i : ℕ) : cycleColor m i < 3 := by
  unfold cycleColor
  split <;> omega

private theorem cycleColor_adjacent (m i : ℕ) (hm : 3 ≤ m) (hi : i < m) :
    cycleColor m i ≠ cycleColor m ((i + 1) % m) := by
  by_cases hwrap : i + 1 = m
  · have hiEq : i = m - 1 := by omega
    subst i
    rw [hwrap, Nat.mod_self]
    have hlast : 0 ≠ m - 1 := by omega
    by_cases hodd : Odd m
    · rw [Nat.odd_iff] at hodd
      simp [cycleColor, Nat.odd_iff, hodd, hlast]
    · have heven : Even m := Nat.not_odd_iff_even.mp hodd
      rcases heven with ⟨k, hk⟩
      have hpar : (m - 1) % 2 = 1 := by omega
      simp [cycleColor, hodd, hlast, hpar]
  · have hlt : i + 1 < m := by omega
    have hnext : (i + 1) % m = i + 1 := Nat.mod_eq_of_lt hlt
    rw [hnext]
    by_cases hodd : Odd m
    · rw [Nat.odd_iff] at hodd
      by_cases hlast : i + 1 = m - 1
      · have hpar : i % 2 = 1 := by omega
        have hiLast : i ≠ m - 1 := by omega
        simp [cycleColor, Nat.odd_iff, hodd, hiLast, hlast, hpar]
      · have hiLast : i ≠ m - 1 := by omega
        have hne : i % 2 ≠ (i + 1) % 2 := by omega
        simpa [cycleColor, Nat.odd_iff, hodd, hiLast, hlast] using hne
    · have hne : i % 2 ≠ (i + 1) % 2 := by omega
      simpa [cycleColor, hodd] using hne

private theorem cycleColor_zmod_succ (m : ℕ) (hm : 3 ≤ m) (x : ZMod m) :
    cycleColor m x.val ≠ cycleColor m (x + 1).val := by
  haveI : NeZero m := ⟨by omega⟩
  have hval : (x + 1).val = (x.val + 1) % m := by
    rw [ZMod.val_add]
    have hm1 : 1 < m := by omega
    haveI : Fact (1 < m) := ⟨hm1⟩
    rw [ZMod.val_one]
  rw [hval]
  exact cycleColor_adjacent m x.val hm (ZMod.val_lt x)

private theorem addModThree_ne {a b c : ℕ} (ha : a < 3) (hb : b < 3)
    (hne : a ≠ b) : (a + c) % 3 ≠ (b + c) % 3 := by
  omega

theorem torusColor_proper (L N : Size) : ProperTorusColoring (torusColor L N) := by
  intro e
  rcases e with ⟨⟨x, y⟩, d⟩
  fin_cases d
  · have hcycle := cycleColor_zmod_succ L.val (by omega) x
    apply (Fin.ne_iff_vne _ _).2
    change (cycleColor L.val x.val + cycleColor N.val y.val) % 3 ≠
      (cycleColor L.val (x + 1).val + cycleColor N.val y.val) % 3
    exact addModThree_ne (cycleColor_lt_three _ _) (cycleColor_lt_three _ _) hcycle
  · have hcycle := cycleColor_zmod_succ N.val (by omega) y
    apply (Fin.ne_iff_vne _ _).2
    change (cycleColor L.val x.val + cycleColor N.val y.val) % 3 ≠
      (cycleColor L.val x.val + cycleColor N.val (y + 1).val) % 3
    have hne : cycleColor N.val y.val ≠ cycleColor N.val (y + 1).val := hcycle
    rw [Nat.add_comm (cycleColor L.val x.val) (cycleColor N.val y.val),
      Nat.add_comm (cycleColor L.val x.val) (cycleColor N.val (y + 1).val)]
    exact addModThree_ne (cycleColor_lt_three _ _) (cycleColor_lt_three _ _) hne

end AKLT.W.GAP032

theorem AKLT.W.GAP032.main : AKLT.Blueprint.Gap.TorusColorStatement := by
  intro L N
  exact AKLT.W.GAP032.torusColor_proper L N

#print axioms AKLT.W.GAP032.main
