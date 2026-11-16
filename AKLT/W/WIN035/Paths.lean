import AKLT.W.WIN035.Geometry

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN035

/-! The complement escape argument is split into elementary coordinate paths.
The first lemmas record the local graph language used by those paths. -/

theorem joined_step {R : Plane → Plane → Prop} {S : Set Plane}
    {x y : Plane} (hx : x ∈ S) (hy : y ∈ S) (hxy : R x y) :
    JoinedIn R S x y := by
  exact Relation.ReflTransGen.single ⟨hx, hy, hxy⟩

def stepToward (x y : Plane) : Plane :=
  if x.1 < y.1 then (x.1 + 1, x.2)
  else if y.1 < x.1 then (x.1 - 1, x.2)
  else if x.2 < y.2 then (x.1, x.2 + 1)
  else if y.2 < x.2 then (x.1, x.2 - 1)
  else x

theorem stepToward_adj (x y : Plane) (h : x ≠ y) :
    Adjacent x (stepToward x y) := by
  unfold Adjacent latticeDist stepToward
  by_cases h₁ : x.1 < y.1
  · simp [h₁]
  · by_cases h₂ : y.1 < x.1
    · simp [h₁, h₂]
    · by_cases h₃ : x.2 < y.2
      · simp [h₁, h₂, h₃]
      · by_cases h₄ : y.2 < x.2
        · simp [h₁, h₂, h₃, h₄]
        · have hx1 : x.1 = y.1 := by omega
          have hx2 : x.2 = y.2 := by omega
          have hxy : x = y := Prod.ext hx1 hx2
          exact (h hxy).elim

theorem stepToward_dist_lt (x y : Plane) (h : x ≠ y) :
    latticeDist (stepToward x y) y < latticeDist x y := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  simp only [ne_eq, Prod.mk.injEq] at h
  unfold latticeDist stepToward
  split_ifs <;> omega

theorem stepToward_supDist_le (x y : Plane) :
    supDist (stepToward x y) y ≤ supDist x y := by
  unfold stepToward supDist
  split_ifs <;> omega

theorem joined_to_point {S : Set Plane} (y : Plane)
    (hclosed : ∀ x ∈ S, x ≠ y → stepToward x y ∈ S) :
    ∀ x ∈ S, JoinedIn Adjacent S x y := by
  intro x hx
  suffices h : ∀ n : ℕ, ∀ x : Plane, latticeDist x y = n → x ∈ S →
      JoinedIn Adjacent S x y by
    exact h (latticeDist x y) x rfl hx
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro x hdist hx
      by_cases hxy : x = y
      · subst x
        exact Relation.ReflTransGen.refl
      · let x' := stepToward x y
        have hx' : x' ∈ S := hclosed x hx hxy
        have hlt : latticeDist x' y < n := by
          rw [← hdist]
          exact stepToward_dist_lt x y hxy
        have htail : JoinedIn Adjacent S x' y := ih (latticeDist x' y) hlt x' rfl hx'
        exact Relation.ReflTransGen.trans
          (joined_step hx hx' (stepToward_adj x y hxy)) htail

theorem joined_mono {R : Plane → Plane → Prop} {S T : Set Plane}
    (hST : S ⊆ T) {x y : Plane} (h : JoinedIn R S x y) : JoinedIn R T x y := by
  exact Relation.ReflTransGen.mono (fun _ _ huv => ⟨hST huv.1, hST huv.2.1, huv.2.2⟩) x y h

/-- A strictly increasing natural potential cannot stay in a finite set forever. -/
theorem escape_of_increasing (F : Finset Plane) (S : Set Plane) (f : Plane → ℕ)
    (hstep : ∀ z ∈ F, z ∈ S → ∃ v ∈ S, Adjacent z v ∧ f z < f v) :
    ∀ z ∈ S, ∃ w, w ∉ F ∧ JoinedIn Adjacent S z w := by
  classical
  have go : ∀ n : ℕ, ∀ z ∈ S, F.sup f + 1 - f z = n →
      ∃ w, w ∉ F ∧ JoinedIn Adjacent S z w := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro z hz hn
      by_cases hzF : z ∈ F
      · obtain ⟨v, hv, hzv, hf⟩ := hstep z hzF hz
        have hbound : f z ≤ F.sup f := Finset.le_sup hzF
        have hlt : F.sup f + 1 - f v < n := by omega
        obtain ⟨w, hw, hvw⟩ := ih _ hlt v hv rfl
        exact ⟨w, hw, (joined_step hz hv hzv).trans hvw⟩
      · exact ⟨z, hzF, Relation.ReflTransGen.refl⟩
  intro z hz
  exact go _ z hz rfl

end AKLT.W.WIN035
