module
public import AKLT.Blueprint.H3.NodesDomination

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.H3

namespace AKLT.W.H3M019

/-- Split a direction word into its first compass direction and remaining word. -/
private def headTailEquiv (r : ℕ) : Compass × DirectionWord r ≃ DirectionWord (r + 1) :=
  Fin.consEquiv (fun _ : Fin (r + 1) => Compass)

private theorem iterate_expansion (Q : MemoryQuotient 10 3741) (X : PairType)
    (d₀ : Compass) (r : ℕ) (φ : Phase) (a : Fin 3741) (x : Plane) :
    ((stationaryApply Q X d₀)^[r]) (stationaryReward X) φ a x =
      ∑ v : DirectionWord r,
        stationaryWordValue Q X d₀ (List.ofFn v) φ a x := by
  induction r generalizing φ a x with
  | zero =>
      simp [stationaryWordValue, stationaryReward]
  | succ r ih =>
      calc
        ((stationaryApply Q X d₀)^[r + 1]) (stationaryReward X) φ a x =
            ∑ d : Compass, ∑ ψ : Phase,
              stationaryCoefficient Q X d₀ φ a x d ψ *
                (∑ v : DirectionWord r,
                  stationaryWordValue Q X d₀ (List.ofFn v) ψ
                    (Q.successor a d) (x + d.step)) := by
          rw [Function.iterate_succ_apply']
          simp only [stationaryApply]
          simp_rw [ih]
        _ = ∑ d : Compass, ∑ v : DirectionWord r, ∑ ψ : Phase,
              stationaryCoefficient Q X d₀ φ a x d ψ *
                stationaryWordValue Q X d₀ (List.ofFn v) ψ
                  (Q.successor a d) (x + d.step) := by
          simp_rw [Finset.mul_sum]
          congr 1
          funext d
          exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
            (f := fun ψ v => stationaryCoefficient Q X d₀ φ a x d ψ *
              stationaryWordValue Q X d₀ (List.ofFn v) ψ (Q.successor a d) (x + d.step))
        _ = ∑ p : Compass × DirectionWord r,
              stationaryWordValue Q X d₀ (List.ofFn (headTailEquiv r p)) φ a x := by
          let pairVal : Compass × DirectionWord r → ℚ := fun p =>
            ∑ ψ : Phase,
              stationaryCoefficient Q X d₀ φ a x p.1 ψ *
                stationaryWordValue Q X d₀ (List.ofFn p.2) ψ
                  (Q.successor a p.1) (x + p.1.step)
          calc
            (∑ d : Compass, ∑ v : DirectionWord r, ∑ ψ : Phase,
                stationaryCoefficient Q X d₀ φ a x d ψ *
                  stationaryWordValue Q X d₀ (List.ofFn v) ψ
                    (Q.successor a d) (x + d.step)) = ∑ p, pairVal p := by
              simpa [pairVal] using (Fintype.sum_prod_type pairVal).symm
            _ = ∑ p : Compass × DirectionWord r,
                  stationaryWordValue Q X d₀ (List.ofFn (headTailEquiv r p)) φ a x := by
              apply Fintype.sum_congr
              intro p
              rcases p with ⟨d, v⟩
              simp [pairVal, stationaryWordValue, headTailEquiv, Fin.consEquiv]
        _ = ∑ v : DirectionWord (r + 1),
              stationaryWordValue Q X d₀ (List.ofFn v) φ a x := by
          exact Fintype.sum_equiv (headTailEquiv r) _ _ (by intro p; rfl)

theorem main : AKLT.Blueprint.H3.StationaryWordExpansionStatement := by
  intro Q X d₀ r φ a x
  exact iterate_expansion Q X d₀ r φ a x

#print axioms main

end AKLT.W.H3M019
