import AKLT.Blueprint.H1.NodesReduction

noncomputable section

namespace AKLT.W.H1M030

theorem main : AKLT.Blueprint.H1.ProductBallNonnegativeStatement := by
  classical
  intro hChord F hAffine hUnitNonnegative u hu

  have hInduction :
      ∀ s : Finset (Fin 20),
        ∀ v : Fin 20 → AKLT.Defs.Vec3,
          (∀ j, j ∈ s → AKLT.Defs.normSq (v j) ≤ 1) →
          (∀ j, j ∉ s → AKLT.Defs.normSq (v j) = 1) →
          0 ≤ F v := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro v _ hOutside
        let w : Fin 20 → AKLT.Defs.UnitVector := fun j =>
          ⟨v j, hOutside j (by simp)⟩
        have hw : (fun j => (w j).val) = v := by
          funext j
          rfl
        rw [← hw]
        exact hUnitNonnegative w
    | @insert j s hj ih =>
        intro v hInside hOutside
        obtain ⟨a, b, t, ht0, ht1, hvj⟩ := hChord (v j) (hInside j (Finset.mem_insert_self j s))
        have hAInside : ∀ k, k ∈ s → AKLT.Defs.normSq ((Function.update v j a.val) k) ≤ 1 := by
          intro k hk
          have hbound := hInside k (Finset.mem_insert_of_mem hk)
          have hkj : k ≠ j := fun heq => hj (heq ▸ hk)
          simpa [Function.update, hkj] using hbound
        have hBInside : ∀ k, k ∈ s → AKLT.Defs.normSq ((Function.update v j b.val) k) ≤ 1 := by
          intro k hk
          have hbound := hInside k (Finset.mem_insert_of_mem hk)
          have hkj : k ≠ j := fun heq => hj (heq ▸ hk)
          simpa [Function.update, hkj] using hbound
        have hAOutside :
            ∀ k, k ∉ s → AKLT.Defs.normSq ((Function.update v j a.val) k) = 1 := by
          intro k hk
          by_cases hkj : k = j
          · subst k
            simpa [Function.update] using a.property
          · have hkInsert : k ∉ insert j s := by
              simp [hkj, hk]
            have hunit := hOutside k hkInsert
            simpa [Function.update, hkj] using hunit
        have hBOutside :
            ∀ k, k ∉ s → AKLT.Defs.normSq ((Function.update v j b.val) k) = 1 := by
          intro k hk
          by_cases hkj : k = j
          · subst k
            simpa [Function.update] using b.property
          · have hkInsert : k ∉ insert j s := by
              simp [hkj, hk]
            have hunit := hOutside k hkInsert
            simpa [Function.update, hkj] using hunit
        have hA := ih (Function.update v j a.val) hAInside hAOutside
        have hB := ih (Function.update v j b.val) hBInside hBOutside
        have ht1' : 0 ≤ 1 - t := by linarith
        have hCombination :
            0 ≤ t * F (Function.update v j a.val) +
              (1 - t) * F (Function.update v j b.val) := by
          exact add_nonneg (mul_nonneg ht0 hA) (mul_nonneg ht1' hB)
        have hRewrite :
            v = Function.update v j (t • a.val + (1 - t) • b.val) := by
          funext k
          by_cases hkj : k = j
          · subst k
            simp [Function.update, hvj]
          · simp [Function.update, hkj]
        rw [hRewrite]
        rw [hAffine j v a.val b.val t]
        exact hCombination

  exact hInduction Finset.univ u
    (by intro j _; exact hu j)
    (by intro j hj; exact (hj (Finset.mem_univ j)).elim)

end AKLT.W.H1M030
