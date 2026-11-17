module
public import AKLT.Blueprint.Win.NodesTaper

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN034

private theorem adjacent_right (x y : ℤ) : Adjacent (x, y) (x + 1, y) := by
  simp [Adjacent, latticeDist]

private theorem adjacent_up (x y : ℤ) : Adjacent (x, y) (x, y + 1) := by
  simp [Adjacent, latticeDist]

private theorem joined_symm {S : Set Plane} {x y : Plane}
    (h : JoinedIn Adjacent S x y) : JoinedIn Adjacent S y x := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c hab hbc ih =>
      have hcb : c ∈ S ∧ b ∈ S ∧ Adjacent c b :=
        ⟨hbc.2.1, hbc.1, by
          have hs : Adjacent b c := hbc.2.2
          have hdist : latticeDist c b = latticeDist b c := by
            dsimp [latticeDist]
            rw [show c.1 - b.1 = -(b.1 - c.1) by omega, Int.natAbs_neg,
                show c.2 - b.2 = -(b.2 - c.2) by omega, Int.natAbs_neg]
          change latticeDist b c = 1 at hs
          change latticeDist c b = 1
          rw [hdist, hs]⟩
      change Relation.ReflTransGen (fun v w : Plane =>
        v ∈ S ∧ w ∈ S ∧ Adjacent v w) c _
      exact Relation.ReflTransGen.head (r := fun v w : Plane =>
        v ∈ S ∧ w ∈ S ∧ Adjacent v w) hcb ih

private theorem walkRight (S : Set Plane) (x y : ℤ) :
    ∀ n : ℕ, (∀ k : ℕ, k ≤ n → (x + (k : ℤ), y) ∈ S) →
      JoinedIn Adjacent S (x, y) (x + (n : ℤ), y) := by
  intro n
  induction n generalizing x y with
  | zero =>
      intro _
      change Relation.ReflTransGen (fun v w : Plane =>
        v ∈ S ∧ w ∈ S ∧ Adjacent v w) (x, y) (x + (0 : ℤ), y)
      simpa using (Relation.ReflTransGen.refl :
        Relation.ReflTransGen (fun v w : Plane =>
          v ∈ S ∧ w ∈ S ∧ Adjacent v w) (x, y) (x, y))
  | succ n ih =>
      intro h
      have h0 : (x, y) ∈ S := by simpa using h 0 (by omega)
      have h1 : (x + 1, y) ∈ S := by simpa using h 1 (by omega)
      have htail : ∀ k : ℕ, k ≤ n → (x + 1 + (k : ℤ), y) ∈ S := by
        intro k hk
        have ht := h (k + 1) (by omega)
        convert ht using 1 <;> congr 1 <;> push_cast <;> omega
      have tail := ih (x := x + 1) (y := y) htail
      have edge : (x, y) ∈ S ∧ (x + 1, y) ∈ S ∧ Adjacent (x, y) (x + 1, y) :=
        ⟨h0, h1, adjacent_right x y⟩
      have path := Relation.ReflTransGen.head (r := fun v w : Plane =>
        v ∈ S ∧ w ∈ S ∧ Adjacent v w) edge tail
      have hend : x + ((n + 1 : ℕ) : ℤ) = (x + 1) + (n : ℤ) := by
        push_cast
        omega
      rw [hend]
      exact path

private theorem walkUp (S : Set Plane) (x y : ℤ) :
    ∀ n : ℕ, (∀ k : ℕ, k ≤ n → (x, y + (k : ℤ)) ∈ S) →
      JoinedIn Adjacent S (x, y) (x, y + (n : ℤ)) := by
  intro n
  induction n generalizing x y with
  | zero =>
      intro _
      change Relation.ReflTransGen (fun v w : Plane =>
        v ∈ S ∧ w ∈ S ∧ Adjacent v w) (x, y) (x, y + (0 : ℤ))
      simpa using (Relation.ReflTransGen.refl :
        Relation.ReflTransGen (fun v w : Plane =>
          v ∈ S ∧ w ∈ S ∧ Adjacent v w) (x, y) (x, y))
  | succ n ih =>
      intro h
      have h0 : (x, y) ∈ S := by simpa using h 0 (by omega)
      have h1 : (x, y + 1) ∈ S := by simpa using h 1 (by omega)
      have htail : ∀ k : ℕ, k ≤ n → (x, y + 1 + (k : ℤ)) ∈ S := by
        intro k hk
        have ht := h (k + 1) (by omega)
        convert ht using 1 <;> congr 1 <;> push_cast <;> omega
      have tail := ih (x := x) (y := y + 1) htail
      have edge : (x, y) ∈ S ∧ (x, y + 1) ∈ S ∧ Adjacent (x, y) (x, y + 1) :=
        ⟨h0, h1, adjacent_up x y⟩
      have path := Relation.ReflTransGen.head (r := fun v w : Plane =>
        v ∈ S ∧ w ∈ S ∧ Adjacent v w) edge tail
      have hend : y + ((n + 1 : ℕ) : ℤ) = (y + 1) + (n : ℤ) := by
        push_cast
        omega
      rw [hend]
      exact path

private theorem connectX_le (S : Set Plane) (x x' y : ℤ) (hxx' : x ≤ x')
    (hseg : ∀ t : ℤ, min x x' ≤ t → t ≤ max x x' → (t, y) ∈ S) :
    JoinedIn Adjacent S (x, y) (x', y) := by
  let n : ℕ := (x' - x).toNat
  have hn : (n : ℤ) = x' - x := by
    dsimp [n]
    exact Int.toNat_of_nonneg (by omega)
  have hpath := walkRight S x y n (by
    intro k hk
    apply hseg (x + (k : ℤ))
    · rw [min_eq_left hxx']
      omega
    · rw [max_eq_right hxx']
      have hkZ : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hk
      omega)
  have hend : x + (n : ℤ) = x' := by rw [hn]; omega
  rw [hend] at hpath
  exact hpath

private theorem connectX (S : Set Plane) (x x' y : ℤ)
    (hseg : ∀ t : ℤ, min x x' ≤ t → t ≤ max x x' → (t, y) ∈ S) :
    JoinedIn Adjacent S (x, y) (x', y) := by
  by_cases hxx' : x ≤ x'
  · exact connectX_le S x x' y hxx' hseg
  · have hrev : JoinedIn Adjacent S (x', y) (x, y) := by
      apply connectX_le S x' x y (by omega)
      intro t hmin hmax
      have hmin' : min x x' ≤ t := by simpa [min_comm] using hmin
      have hmax' : t ≤ max x x' := by simpa [max_comm] using hmax
      exact hseg t hmin' hmax'
    exact joined_symm hrev

private theorem connectY_le (S : Set Plane) (x y y' : ℤ) (hyy' : y ≤ y')
    (hseg : ∀ t : ℤ, min y y' ≤ t → t ≤ max y y' → (x, t) ∈ S) :
    JoinedIn Adjacent S (x, y) (x, y') := by
  let n : ℕ := (y' - y).toNat
  have hn : (n : ℤ) = y' - y := by
    dsimp [n]
    exact Int.toNat_of_nonneg (by omega)
  have hpath := walkUp S x y n (by
    intro k hk
    apply hseg (y + (k : ℤ))
    · rw [min_eq_left hyy']
      omega
    · rw [max_eq_right hyy']
      have hkZ : (k : ℤ) ≤ (n : ℤ) := by exact_mod_cast hk
      omega)
  have hend : y + (n : ℤ) = y' := by rw [hn]; omega
  rw [hend] at hpath
  exact hpath

private theorem connectY (S : Set Plane) (x y y' : ℤ)
    (hseg : ∀ t : ℤ, min y y' ≤ t → t ≤ max y y' → (x, t) ∈ S) :
    JoinedIn Adjacent S (x, y) (x, y') := by
  by_cases hyy' : y ≤ y'
  · exact connectY_le S x y y' hyy' hseg
  · have hrev : JoinedIn Adjacent S (x, y') (x, y) := by
      apply connectY_le S x y' y (by omega)
      intro t hmin hmax
      have hmin' : min y y' ≤ t := by simpa [min_comm] using hmin
      have hmax' : t ≤ max y y' := by simpa [max_comm] using hmax
      exact hseg t hmin' hmax'
    exact joined_symm hrev

private theorem outside_of_x_gt (a z : Plane) (u : ℕ)
    (h : a.1 + (u : ℤ) < z.1) : z ∉ square a u := by
  intro hz
  have hp : z.1 ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + (u : ℤ)) ∧
      z.2 ∈ Finset.Icc (a.2 - (u : ℤ)) (a.2 + (u : ℤ)) :=
    Finset.mem_product.mp (by simpa [square] using hz)
  have hx := Finset.mem_Icc.mp hp.1
  omega

private theorem outside_of_x_lt (a z : Plane) (u : ℕ)
    (h : z.1 < a.1 - (u : ℤ)) : z ∉ square a u := by
  intro hz
  have hp : z.1 ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + (u : ℤ)) ∧
      z.2 ∈ Finset.Icc (a.2 - (u : ℤ)) (a.2 + (u : ℤ)) :=
    Finset.mem_product.mp (by simpa [square] using hz)
  have hx := Finset.mem_Icc.mp hp.1
  omega

private theorem outside_of_y_gt (a z : Plane) (u : ℕ)
    (h : a.2 + (u : ℤ) < z.2) : z ∉ square a u := by
  intro hz
  have hp : z.1 ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + (u : ℤ)) ∧
      z.2 ∈ Finset.Icc (a.2 - (u : ℤ)) (a.2 + (u : ℤ)) :=
    Finset.mem_product.mp (by simpa [square] using hz)
  have hy := Finset.mem_Icc.mp hp.2
  omega

private theorem outside_of_y_lt (a z : Plane) (u : ℕ)
    (h : z.2 < a.2 - (u : ℤ)) : z ∉ square a u := by
  intro hz
  have hp : z.1 ∈ Finset.Icc (a.1 - (u : ℤ)) (a.1 + (u : ℤ)) ∧
      z.2 ∈ Finset.Icc (a.2 - (u : ℤ)) (a.2 + (u : ℤ)) :=
    Finset.mem_product.mp (by simpa [square] using hz)
  have hy := Finset.mem_Icc.mp hp.2
  omega

private theorem toTopRow (a : Plane) (u : ℕ) (z : Plane)
    (hz : z ∉ square a u) :
    JoinedIn Adjacent {w | w ∉ square a u} z
      (z.1, a.2 + (u : ℤ) + 1) := by
  let S : Set Plane := {w | w ∉ square a u}
  let top : ℤ := a.2 + (u : ℤ) + 1
  let right : ℤ := a.1 + (u : ℤ) + 1
  change JoinedIn Adjacent S z (z.1, top)
  have htop : a.2 + (u : ℤ) < top := by dsimp [top]; omega
  have hright : a.1 + (u : ℤ) < right := by dsimp [right]; omega
  by_cases habove : a.2 + (u : ℤ) < z.2
  · apply connectY S z.1 z.2 top
    intro t hlo hhi
    have ht : a.2 + (u : ℤ) < t := by
      dsimp [top] at hhi
      omega
    exact outside_of_y_gt a (z.1, t) u ht
  · by_cases hrightZ : a.1 + (u : ℤ) < z.1
    · apply connectY S z.1 z.2 top
      intro t _ _
      exact outside_of_x_gt a (z.1, t) u hrightZ
    · by_cases hleftZ : z.1 < a.1 - (u : ℤ)
      · apply connectY S z.1 z.2 top
        intro t _ _
        exact outside_of_x_lt a (z.1, t) u hleftZ
      · have hbelow : z.2 < a.2 - (u : ℤ) := by
          by_contra hnot
          have hin : z ∈ square a u := by
            apply Finset.mem_product.mpr
            constructor
            · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          exact hz hin
        have hfirst : JoinedIn Adjacent S z (right, z.2) := by
          apply connectX S z.1 right z.2
          intro t _ _
          exact outside_of_y_lt a (t, z.2) u hbelow
        have hsecond : JoinedIn Adjacent S (right, z.2) (right, top) := by
          apply connectY S right z.2 top
          intro t _ _
          exact outside_of_x_gt a (right, t) u hright
        have hlast : JoinedIn Adjacent S (right, top) (z.1, top) := by
          apply connectX S right z.1 top
          intro t _ _
          exact outside_of_y_gt a (t, top) u htop
        have hjoin := hfirst.trans hsecond |>.trans hlast
        change JoinedIn Adjacent S z (z.1, top) at hjoin
        exact hjoin

theorem main : AKLT.Blueprint.Win.SquareExteriorStatement := by
  intro a u
  let S : Set Plane := {z | z ∉ square a u}
  have hnonempty : S.Nonempty := by
    refine ⟨(a.1 + (u : ℤ) + 1, a.2), ?_⟩
    exact outside_of_x_gt a _ u (by dsimp; omega)
  refine ⟨hnonempty, ?_⟩
  intro x hx y hy
  have hxTop := toTopRow a u x hx
  have hyTop := toTopRow a u y hy
  have hrow : JoinedIn Adjacent S
      (x.1, a.2 + (u : ℤ) + 1) (y.1, a.2 + (u : ℤ) + 1) := by
    apply connectX S x.1 y.1 (a.2 + (u : ℤ) + 1)
    intro t _ _
    exact outside_of_y_gt a (t, a.2 + (u : ℤ) + 1) u (by omega)
  have hpath := hxTop.trans hrow
  exact hpath.trans (joined_symm hyTop)

end AKLT.W.WIN034
