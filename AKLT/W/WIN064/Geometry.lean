import AKLT.Blueprint.Win.NodesCut

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN064

private def otherEnd (z : Plane) (e : Plane × Plane) : Plane :=
  if e.1 = z then e.2 else e.1

/-- At a retained site, each active internal bond and each original exterior leg
uses a different nearest-neighbor direction. Removed sites contribute no factor. -/
theorem incidence_bound (G D : Finset Plane) (hDG : D ⊆ G) (z : Plane)
    (hz : z ∈ D) :
    ((internalBonds D).filter fun e => e.1 = z ∨ e.2 = z).card +
      ((originalLegs G).filter fun e => e.1 = z).card ≤ 4 := by
  classical
  let A := (internalBonds D).filter fun e => e.1 = z ∨ e.2 = z
  let L := (originalLegs G).filter fun e => e.1 = z
  let N := neighbours z ∩ D
  let O := neighbours z \ G
  have hzG : z ∈ G := hDG hz
  have hAmap : ∀ e ∈ A, otherEnd z e ∈ N := by
    intro e he
    have he' : e ∈ internalBonds D := (Finset.mem_filter.mp he).1
    have hinc := (Finset.mem_filter.mp he).2
    simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image] at he'
    obtain ⟨x, hxD, y, hy, rfl⟩ := he'
    have hpos := (Finset.mem_inter.mp hy).1
    have hyD := (Finset.mem_inter.mp hy).2
    change x = z ∨ y = z at hinc
    change (if x = z then y else x) ∈ neighbours z ∩ D
    apply Finset.mem_inter.mpr
    constructor
    · by_cases hxz : x = z
      · subst x
        have hp : y = (z.1 + 1, z.2) ∨ y = (z.1, z.2 + 1) := by
          simpa [positiveNeighbours] using hpos
        rcases hp with hp | hp
        · subst y
          rw [neighbours]
          apply Finset.mem_image.mpr
          exact ⟨Compass.east, Finset.mem_univ _, by rcases z with ⟨a,b⟩; simp [Compass.step]⟩
        · subst y
          rw [neighbours]
          apply Finset.mem_image.mpr
          exact ⟨Compass.north, Finset.mem_univ _, by rcases z with ⟨a,b⟩; simp [Compass.step]⟩
      · have hyz : y = z := by
          rcases hinc with h | h
          · exact (hxz h).elim
          · exact h
        simp only [ite_eq_right hxz]
        have hp : z = (x.1 + 1, x.2) ∨ z = (x.1, x.2 + 1) := by
          have hp' : y = (x.1 + 1, x.2) ∨ y = (x.1, x.2 + 1) := by
            simpa [positiveNeighbours] using hpos
          simpa [hyz] using hp'
        rcases hp with hp | hp
        · have hfst := congrArg Prod.fst hp
          have hsnd := congrArg Prod.snd hp
          simp at hfst hsnd
          have hx : x = (z.1 - 1, z.2) := by apply Prod.ext <;> omega
          rw [hx]
          rw [neighbours]
          apply Finset.mem_image.mpr
          exact ⟨Compass.west, Finset.mem_univ _, by rcases z with ⟨a,b⟩; simp [Compass.step]; omega⟩
        · have hfst := congrArg Prod.fst hp
          have hsnd := congrArg Prod.snd hp
          simp at hfst hsnd
          have hx : x = (z.1, z.2 - 1) := by apply Prod.ext <;> omega
          rw [hx]
          rw [neighbours]
          apply Finset.mem_image.mpr
          exact ⟨Compass.south, Finset.mem_univ _, by rcases z with ⟨a,b⟩; simp [Compass.step]; omega⟩
    · by_cases hxz : x = z
      · subst x
        simpa using hyD
      · have hyz : y = z := by
          rcases hinc with h | h
          · exact (hxz h).elim
          · exact h
        subst y
        simp only [ite_eq_right hxz]
        exact hxD
  have hLmap : ∀ e ∈ L, e.2 ∈ O := by
    intro e he
    have he' : e ∈ originalLegs G := (Finset.mem_filter.mp he).1
    simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image] at he'
    obtain ⟨x, hxG, y, hy, rfl⟩ := he'
    have hneigh := (Finset.mem_sdiff.mp hy).1
    have hnotG := (Finset.mem_sdiff.mp hy).2
    have hxz : x = z := (Finset.mem_filter.mp he).2
    subst x
    exact Finset.mem_sdiff.mpr ⟨hneigh, hnotG⟩
  have hAinj : Set.InjOn (otherEnd z) (A : Set (Plane × Plane)) := by
    intro e₁ he₁ e₂ he₂ heq
    have h₁ : e₁ ∈ internalBonds D := (Finset.mem_filter.mp he₁).1
    have h₂ : e₂ ∈ internalBonds D := (Finset.mem_filter.mp he₂).1
    simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image] at h₁ h₂
    obtain ⟨x₁, hx₁, y₁, hy₁, heq₁⟩ := h₁
    obtain ⟨x₂, hx₂, y₂, hy₂, heq₂⟩ := h₂
    subst e₁ e₂
    have hi₁ := (Finset.mem_filter.mp he₁).2
    have hi₂ := (Finset.mem_filter.mp he₂).2
    change x₁ = z ∨ y₁ = z at hi₁
    change x₂ = z ∨ y₂ = z at hi₂
    have hp₁ : y₁ = (x₁.1 + 1, x₁.2) ∨ y₁ = (x₁.1, x₁.2 + 1) := by
      simpa [positiveNeighbours] using (Finset.mem_inter.mp hy₁).1
    have hp₂ : y₂ = (x₂.1 + 1, x₂.2) ∨ y₂ = (x₂.1, x₂.2 + 1) := by
      simpa [positiveNeighbours] using (Finset.mem_inter.mp hy₂).1
    have hnot₁ : x₁ ≠ y₁ := by
      intro he
      subst y₁
      rcases hp₁ with hp | hp
      · have hfst := congrArg Prod.fst hp
        simp at hfst
      · have hsnd := congrArg Prod.snd hp
        simp at hsnd
    have hnot₂ : x₂ ≠ y₂ := by
      intro he
      subst y₂
      rcases hp₂ with hp | hp
      · have hfst := congrArg Prod.fst hp
        simp at hfst
      · have hsnd := congrArg Prod.snd hp
        simp at hsnd
    rcases hi₁ with h₁ | h₁ <;> rcases hi₂ with h₂ | h₂
    · simp [otherEnd, h₁, h₂] at heq
      exact Prod.ext (h₁.trans h₂.symm) heq
    · simp [otherEnd, h₁, h₂] at heq
      rcases hp₁ with hp₁ | hp₁ <;> rcases hp₂ with hp₂ | hp₂
      all_goals
        have hx₂ : x₂ ≠ z := by intro h; exact hnot₂ (h.trans h₂.symm)
        simp [hx₂] at heq
        have h₁f := congrArg Prod.fst hp₁
        have h₁s := congrArg Prod.snd hp₁
        have h₂f := congrArg Prod.fst hp₂
        have h₂s := congrArg Prod.snd hp₂
        have hef := congrArg Prod.fst heq
        have hes := congrArg Prod.snd heq
        have h1f := congrArg Prod.fst h₁
        have h1s := congrArg Prod.snd h₁
        have h2f := congrArg Prod.fst h₂
        have h2s := congrArg Prod.snd h₂
        simp at h₁f h₁s h₂f h₂s hef hes h1f h1s h2f h2s
      all_goals exfalso; omega
    · simp [otherEnd, h₁, h₂] at heq
      rcases hp₁ with hp₁ | hp₁ <;> rcases hp₂ with hp₂ | hp₂
      all_goals
        have hx₁ : x₁ ≠ z := by intro h; exact hnot₁ (h.trans h₁.symm)
        simp [hx₁] at heq
        have h₁f := congrArg Prod.fst hp₁
        have h₁s := congrArg Prod.snd hp₁
        have h₂f := congrArg Prod.fst hp₂
        have h₂s := congrArg Prod.snd hp₂
        have hef := congrArg Prod.fst heq
        have hes := congrArg Prod.snd heq
        have h1f := congrArg Prod.fst h₁
        have h1s := congrArg Prod.snd h₁
        have h2f := congrArg Prod.fst h₂
        have h2s := congrArg Prod.snd h₂
        simp at h₁f h₁s h₂f h₂s hef hes h1f h1s h2f h2s
      all_goals exfalso; omega
    · simp [otherEnd, h₁, h₂] at heq
      have hxx₁ : x₁ ≠ z := by intro he; exact hnot₁ (he.trans h₁.symm)
      have hxx₂ : x₂ ≠ z := by intro he; exact hnot₂ (he.trans h₂.symm)
      simp [hxx₁, hxx₂] at heq
      exact Prod.ext heq (h₁.trans h₂.symm)
  have hLin : Set.InjOn Prod.snd (L : Set (Plane × Plane)) := by
    intro e₁ he₁ e₂ he₂ heq
    have hx₁ := (Finset.mem_filter.mp he₁).2
    have hx₂ := (Finset.mem_filter.mp he₂).2
    exact Prod.ext (hx₁.trans hx₂.symm) heq
  have hsum : N.card + O.card ≤ (neighbours z).card := by
    have hdis : Disjoint N O := by
      apply Finset.disjoint_left.mpr
      intro w hwN hwO
      have hwG : w ∈ G := hDG ((Finset.mem_inter.mp hwN).2)
      exact (Finset.mem_sdiff.mp hwO).2 hwG
    have hsub : N ∪ O ⊆ neighbours z := by
      intro w hw
      rcases Finset.mem_union.mp hw with h | h
      · exact (Finset.mem_inter.mp h).1
      · exact (Finset.mem_sdiff.mp h).1
    calc
      N.card + O.card = (N ∪ O).card := (Finset.card_union_of_disjoint hdis).symm
      _ ≤ (neighbours z).card := Finset.card_le_card hsub
  have hN : A.card ≤ N.card := Finset.card_le_card_of_injOn (otherEnd z) hAmap hAinj
  have hO : L.card ≤ O.card := Finset.card_le_card_of_injOn Prod.snd hLmap hLin
  have hn : (neighbours z).card = 4 := by
    change (Finset.univ.image (fun d : Compass => z + d.step)).card = 4
    have hinj : Set.InjOn (fun d : Compass => z + d.step)
        (↑(Finset.univ : Finset Compass) : Set Compass) := by
      intro a ha b hb hab
      cases a <;> cases b <;> simp [Compass.step] at hab ⊢
    rw [(Finset.card_image_iff).2 hinj]
    decide
  change A.card + L.card ≤ 4
  omega

end AKLT.W.WIN064
