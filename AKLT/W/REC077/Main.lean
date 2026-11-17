module
public import AKLT.Blueprint.Rec.NodesRecursion
public import AKLT.W.REC010.Main
public import AKLT.W.REC011.Main
public import AKLT.W.REC039.Main
public import AKLT.W.REC041.Main
public import AKLT.W.REC046.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC077

/-- Telescope the trace ratios and expose the step products in the chosen order. -/
theorem main : AKLT.Blueprint.Rec.TraceExposureStatement := by
  classical
  intro G τ D hD u hu T n w hw σ x hx
  have hdyn := AKLT.W.REC039.main G D hD u hu T n w hw
  let a (i : Fin n) : Departure :=
    { G := G
      τ := τ
      D := prefixNetwork D u w i.val
      y := wordVertex u w i.val
      o := wordVertex u w (i.val + 1)
      auxiliary := hdyn.1 i.val (Nat.le_of_lt i.isLt)
      start := (hdyn.2 i).1
      present := by
        have hp := (hdyn.2 i).2
        exact Finset.mem_filter.mpr
          ⟨AKLT.W.REC039.adjacent_mem_neighbours hp.2.2.1, hp⟩ }
  let r (b : Bool) (i : Fin n) : ℝ :=
    stepRatio (prefixNetwork D u w i.val) τ b
      (wordVertex u w i.val) (wordVertex u w (i.val + 1))
  have hr (i : Fin n) :
      0 < r true i ∧ 0 < r false i ∧ r false i ≤ 1 ∧ r true i ≤ x i ∧ 1 ≤ x i :=
    ⟨AKLT.W.REC010.main (a i) true, AKLT.W.REC010.main (a i) false,
      AKLT.W.REC011.main (a i), (hx i).2, (hx i).1⟩
  have he := AKLT.W.REC046.main n (r true ∘ σ) (r false ∘ σ) (x ∘ σ)
    (fun i => hr (σ i))
  simp only [Function.comp_apply] at he
  rw [Equiv.prod_comp σ (r true), Equiv.prod_comp σ (r false)] at he
  rw [AKLT.W.REC041.main G τ D hD u hu T n w hw true,
    AKLT.W.REC041.main G τ D hD u hu T n w hw false]
  exact he

end AKLT.W.REC077
