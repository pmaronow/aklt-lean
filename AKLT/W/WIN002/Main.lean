import AKLT.Blueprint.Win.NodesShell

noncomputable section
open AKLT.Defs

namespace AKLT.W.WIN002

private theorem natAbs_lower_upper (a : ℤ) (u : ℕ) :
    ((a - (u : ℤ)) - (a + (u : ℤ))).natAbs = 2 * u := by
  have h : (a - (u : ℤ)) - (a + (u : ℤ)) = -((2 * u : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h, Int.natAbs_neg, Int.natAbs_natCast]

private theorem natAbs_upper_lower (a : ℤ) (u : ℕ) :
    ((a + (u : ℤ)) - (a - (u : ℤ))).natAbs = 2 * u := by
  have h : (a + (u : ℤ)) - (a - (u : ℤ)) = ((2 * u : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h, Int.natAbs_natCast]

private theorem close_endpoints_eq (a z : ℤ) (u : ℕ) (x y : ℤ)
    (hx : x = a - (u : ℤ) ∨ x = a + (u : ℤ))
    (hy : y = a - (u : ℤ) ∨ y = a + (u : ℤ))
    (hxz : (x - z).natAbs < u) (hyz : (y - z).natAbs < u) : x = y := by
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · rw [hx, hy]
  ·
    have htriangle : (x - y).natAbs ≤ (x - z).natAbs + (y - z).natAbs := by
      calc
        (x - y).natAbs = ((x - z) - (y - z)).natAbs := by congr 1; ring
        _ ≤ (x - z).natAbs + (y - z).natAbs := Int.natAbs_sub_le _ _
    have hsum : (x - z).natAbs + (y - z).natAbs < 2 * u := by omega
    have hdifference : (x - y).natAbs = 2 * u := by
      rw [hx, hy]
      exact natAbs_lower_upper a u
    have : False := by omega
    exact this.elim
  ·
    have htriangle : (x - y).natAbs ≤ (x - z).natAbs + (y - z).natAbs := by
      calc
        (x - y).natAbs = ((x - z) - (y - z)).natAbs := by congr 1; ring
        _ ≤ (x - z).natAbs + (y - z).natAbs := Int.natAbs_sub_le _ _
    have hsum : (x - z).natAbs + (y - z).natAbs < 2 * u := by omega
    have hdifference : (x - y).natAbs = 2 * u := by
      rw [hx, hy]
      exact natAbs_upper_lower a u
    have : False := by omega
    exact this.elim
  · rw [hx, hy]

theorem main : AKLT.Blueprint.Win.CloseCornerStatement := by
  intro a y u _
  classical
  rw [Finset.card_le_one]
  intro c hc d hd
  simp only [Finset.mem_filter] at hc hd
  rcases hc with ⟨hcMem, hcNear⟩
  rcases hd with ⟨hdMem, hdNear⟩
  change c ∈ ({a.1 - (u : ℤ), a.1 + (u : ℤ)} : Finset ℤ) ×ˢ
      ({a.2 - (u : ℤ), a.2 + (u : ℤ)} : Finset ℤ) at hcMem
  change d ∈ ({a.1 - (u : ℤ), a.1 + (u : ℤ)} : Finset ℤ) ×ˢ
      ({a.2 - (u : ℤ), a.2 + (u : ℤ)} : Finset ℤ) at hdMem
  rcases Finset.mem_product.mp hcMem with ⟨hc1, hc2⟩
  rcases Finset.mem_product.mp hdMem with ⟨hd1, hd2⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc1 hc2 hd1 hd2
  change max (c.1 - y.1).natAbs (c.2 - y.2).natAbs < u at hcNear
  change max (d.1 - y.1).natAbs (d.2 - y.2).natAbs < u at hdNear
  have hcX : (c.1 - y.1).natAbs < u :=
    lt_of_le_of_lt (Nat.le_max_left _ _) hcNear
  have hdX : (d.1 - y.1).natAbs < u :=
    lt_of_le_of_lt (Nat.le_max_left _ _) hdNear
  have hcY : (c.2 - y.2).natAbs < u :=
    lt_of_le_of_lt (Nat.le_max_right _ _) hcNear
  have hdY : (d.2 - y.2).natAbs < u :=
    lt_of_le_of_lt (Nat.le_max_right _ _) hdNear
  apply Prod.ext
  · exact close_endpoints_eq a.1 y.1 u c.1 d.1 hc1 hd1 hcX hdX
  · exact close_endpoints_eq a.2 y.2 u c.2 d.2 hc2 hd2 hcY hdY

end AKLT.W.WIN002

end
