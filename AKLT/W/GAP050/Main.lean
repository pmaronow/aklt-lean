module
public import AKLT.Blueprint.Gap.NodesShell

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap
attribute [local instance] Classical.propDecidable

namespace AKLT.W.GAP050

local instance (α : Type) : DecidableEq α := Classical.decEq α

private theorem sum_not_event_marginal
    {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (w : Weight Ω) (f : Ω → Ξ) (E : Ξ → Prop) :
    (∑ y, if E y then 0 else marginal w f y) =
      ∑ x, if E (f x) then 0 else w x := by
  classical
  unfold marginal
  calc
    (∑ y, if E y then 0 else ∑ x, if f x = y then w x else 0) =
        ∑ y, ∑ x, if E y then 0 else if f x = y then w x else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases he : E y <;> simp [he]
    _ = ∑ x, ∑ y, if E y then 0 else if f x = y then w x else 0 :=
      Finset.sum_comm
    _ = ∑ x, if E (f x) then 0 else w x := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_eq_single (f x)]
      · simp
      · intro y hy hne
        by_cases he : E y <;> simp [he, hne.symm]
      · simp

theorem main : AKLT.Blueprint.Gap.TraceDisagreementStatement := by
  classical
  intro ι _ _ S _ m w hw p q c hc U J E hsuccess
  let endpoint : PairTrace (Config S) m → Config S × Config S :=
    fun t => t (Fin.last m)
  let noSuccess : PairTrace (Config S) m → Prop :=
    fun t => ∀ j ∈ J, ¬ E j (t j.succ)
  have hpush :
      disagreement c U =
        ∑ t, if AgreeOn U (endpoint t).1 (endpoint t).2 then 0 else w t := by
    calc
      disagreement c U =
          ∑ z : Config S × Config S, if AgreeOn U z.1 z.2 then 0 else c.mass z.1 z.2 := by
        simp [disagreement, Fintype.sum_prod_type]
      _ = ∑ z, if AgreeOn U z.1 z.2 then 0 else marginal w endpoint z := by
        apply Finset.sum_congr rfl
        intro z hz
        exact congrArg (fun r => if AgreeOn U z.1 z.2 then 0 else r) (hc z.1 z.2)
      _ = ∑ t, if AgreeOn U (endpoint t).1 (endpoint t).2 then 0 else w t :=
        sum_not_event_marginal w endpoint (fun z => AgreeOn U z.1 z.2)
  have hterm : ∀ t,
      (if AgreeOn U (endpoint t).1 (endpoint t).2 then 0 else w t) ≤
        (if noSuccess t then w t else 0) := by
    intro t
    by_cases hwt : 0 < w t
    · by_cases hagree : AgreeOn U (endpoint t).1 (endpoint t).2
      · by_cases hn : noSuccess t
        · simpa [hagree, hn] using hw.1 t
        · simp [hagree, hn]
      · have hno : noSuccess t := by
          intro j hj he
          exact hagree (hsuccess t hwt ⟨j, hj, he⟩)
        simp [hagree, hno]
    · have hzero : w t = 0 := by
        apply le_antisymm
        · exact le_of_not_gt hwt
        · exact hw.1 t
      simp [hzero]
  calc
    disagreement c U = ∑ t, if AgreeOn U (endpoint t).1 (endpoint t).2 then 0 else w t := hpush
    _ ≤ ∑ t, if noSuccess t then w t else 0 := Finset.sum_le_sum fun t _ => hterm t
    _ = eventMass w noSuccess := by
      unfold eventMass
      apply Finset.sum_congr rfl
      intro t ht
      by_cases hn : ∀ j ∈ J, ¬ E j (t j.succ) <;> simp [noSuccess, hn]

end AKLT.W.GAP050

#print axioms AKLT.W.GAP050.main
