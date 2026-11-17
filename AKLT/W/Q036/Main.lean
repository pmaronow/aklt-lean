import AKLT.Blueprint.Q.NodesSplits
import AKLT.Challenge.Sanity

noncomputable section
open AKLT.Challenge

namespace AKLT.W.Q036

private theorem one_ne_zero (L : Size) : (1 : ZMod L.val) ≠ 0 := by
  simpa using AKLT.Challenge.small_natCast_ne_zero L 1 (by omega) (by have := L.property; omega)

private theorem self_ne_prev (L : Size) (a : ZMod L.val) : a ≠ a - 1 := by
  intro h
  apply one_ne_zero L
  calc
    (1 : ZMod L.val) = a - (a - 1) := by ring
    _ = 0 := sub_eq_zero.mpr h

private theorem prev_ne_self (L : Size) (a : ZMod L.val) : a - 1 ≠ a :=
  Ne.symm (self_ne_prev L a)

private theorem starEdge_injective {L N : Size} (x : Site L N) :
    Function.Injective (AKLT.Blueprint.Q.starEdge x) := by
  intro j k h
  fin_cases j <;> fin_cases k
  all_goals simp_all [AKLT.Blueprint.Q.starEdge]
  all_goals
    first
    | exact self_ne_prev L x.1 (by simpa using congrArg Prod.fst h)
    | exact prev_ne_self L x.1 (by simpa using congrArg Prod.fst h)
    | exact self_ne_prev N x.2 (by simpa using congrArg Prod.snd h)
    | exact prev_ne_self N x.2 (by simpa using congrArg Prod.snd h)

theorem main : AKLT.Blueprint.Q.StarEdgeEnumerationStatement := by
  intro L N x
  constructor
  · exact starEdge_injective x
  · classical
    apply Finset.ext
    intro e
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj⟩
      rw [← hj]
      fin_cases j <;> simp [AKLT.Blueprint.Q.starEdge, AKLT.Challenge.bondSites,
        AKLT.Challenge.nextSite]
    · intro he
      rcases e with ⟨y, d⟩
      fin_cases d
      · simp [AKLT.Challenge.bondSites, AKLT.Challenge.nextSite] at he
        rcases he with hxy | hxy
        · subst y
          exact ⟨0, by simp [AKLT.Blueprint.Q.starEdge]⟩
        · have hfst : y.1 + 1 = x.1 := by simpa using congrArg (fun p : Site L N => p.1) hxy.symm
          have hsnd : y.2 = x.2 := by simpa using congrArg (fun p : Site L N => p.2) hxy.symm
          have hy : y = (x.1 - 1, x.2) := by
            apply Prod.ext
            · calc
                y.1 = (y.1 + 1) - 1 := by ring
                _ = x.1 - 1 := congrArg (fun z : ZMod L.val => z - 1) hfst
            · exact hsnd
          subst y
          exact ⟨1, by simp [AKLT.Blueprint.Q.starEdge]⟩
      · simp [AKLT.Challenge.bondSites, AKLT.Challenge.nextSite] at he
        rcases he with hxy | hxy
        · subst y
          exact ⟨2, by simp [AKLT.Blueprint.Q.starEdge]⟩
        · have hfst : y.1 = x.1 := by simpa using congrArg (fun p : Site L N => p.1) hxy.symm
          have hsnd : y.2 + 1 = x.2 := by simpa using congrArg (fun p : Site L N => p.2) hxy.symm
          have hy : y = (x.1, x.2 - 1) := by
            apply Prod.ext
            · exact hfst
            · calc
                y.2 = (y.2 + 1) - 1 := by ring
                _ = x.2 - 1 := congrArg (fun z : ZMod N.val => z - 1) hsnd
          subst y
          exact ⟨3, by simp [AKLT.Blueprint.Q.starEdge]⟩

#print axioms main

end AKLT.W.Q036
