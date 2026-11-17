import AKLT.Blueprint.Gap.NodesShell

noncomputable section
open AKLT.Defs AKLT.Blueprint.Gap
namespace AKLT.W.GAP047

 theorem main : AKLT.Blueprint.Gap.TrialCountStatement := by
  classical
  intro a y u h hh hE
  let E := AKLT.Defs.exceptionalIndices a y u
  let base : Finset (Fin h) := Finset.univ.filter fun j => j.val + 2 ≤ h
  let bad₁ : Finset (Fin h) := base.filter fun j => (j.val + 2 : ℤ) ∈ E
  let bad₂ : Finset (Fin h) := base.filter fun j => (j.val + 3 : ℤ) ∈ E
  have hbase : base.card = h - 1 := by
    have heq : base = Finset.univ.erase ⟨h - 1, by omega⟩ := by
      ext j
      simp only [base, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_erase, Finset.mem_univ, and_true]
      constructor
      · intro hj hlast
        have hv : j.val = h - 1 := by
          simpa using congrArg Fin.val hlast
        omega
      · intro hne
        have hv : j.val ≠ h - 1 := by
          intro hv
          apply hne
          exact Fin.ext (by simpa using hv)
        omega
    rw [heq, Finset.card_erase_of_mem]
    · simp
    · simp
  have htrial : AKLT.Blueprint.Gap.trialTimes a y u h = base \ (bad₁ ∪ bad₂) := by
    ext j
    simp [AKLT.Blueprint.Gap.trialTimes, base, bad₁, bad₂, E,
      Finset.mem_sdiff, Finset.mem_union]
    tauto
  have hbad₁ : bad₁.card ≤ E.card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin h => (j.val + 2 : ℤ))
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro x hx y hy hxy
      apply Fin.ext
      change (x.val : ℤ) + 2 = (y.val : ℤ) + 2 at hxy
      have hv : (x.val : ℤ) = (y.val : ℤ) := by omega
      exact_mod_cast hv
  have hbad₂ : bad₂.card ≤ E.card := by
    apply Finset.card_le_card_of_injOn (fun j : Fin h => (j.val + 3 : ℤ))
    · intro j hj
      exact (Finset.mem_filter.mp hj).2
    · intro x hx y hy hxy
      apply Fin.ext
      change (x.val : ℤ) + 3 = (y.val : ℤ) + 3 at hxy
      have hv : (x.val : ℤ) = (y.val : ℤ) := by omega
      exact_mod_cast hv
  have hsub : bad₁ ∪ bad₂ ⊆ base := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact (Finset.mem_filter.mp hj).1
    · exact (Finset.mem_filter.mp hj).1
  have hunion : (bad₁ ∪ bad₂).card ≤ 2 := by
    have hE' : E.card ≤ 1 := by simpa [E] using hE
    calc
      (bad₁ ∪ bad₂).card ≤ bad₁.card + bad₂.card := Finset.card_union_le _ _
      _ ≤ E.card + E.card := Nat.add_le_add hbad₁ hbad₂
      _ ≤ 2 := by omega
  rw [htrial, Finset.card_sdiff_of_subset hsub, hbase]
  omega

end AKLT.W.GAP047
end
