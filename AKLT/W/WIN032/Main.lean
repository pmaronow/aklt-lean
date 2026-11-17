module
public import AKLT.Blueprint.Win.NodesTaper

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs
namespace AKLT.W.WIN032

open AKLT.Blueprint.Win

private theorem joined_symm {S : Set Plane} {x y : Plane}
    (hxy : AKLT.Blueprint.Win.JoinedIn Adjacent S x y) :
    AKLT.Blueprint.Win.JoinedIn Adjacent S y x := by
  unfold AKLT.Blueprint.Win.JoinedIn at *
  apply Relation.ReflTransGen.mono
    (r := Function.swap (fun v w => v ∈ S ∧ w ∈ S ∧ Adjacent v w))
    (p := fun v w => v ∈ S ∧ w ∈ S ∧ Adjacent v w)
    (fun v w h => by
      rcases h with ⟨hw, hv, hadj⟩
      refine ⟨hv, hw, ?_⟩
      have hx : (v.1 - w.1).natAbs = (w.1 - v.1).natAbs := by
        rw [show v.1 - w.1 = -(w.1 - v.1) by omega, Int.natAbs_neg]
      have hy : (v.2 - w.2).natAbs = (w.2 - v.2).natAbs := by
        rw [show v.2 - w.2 = -(w.2 - v.2) by omega, Int.natAbs_neg]
      simpa [Adjacent, latticeDist, hx, hy, Nat.add_comm] using hadj)
  exact Relation.ReflTransGen.swap _ _ hxy

private theorem joined_horizontal_up {S : Set Plane} {x x' y : ℤ} (hxx : x ≤ x')
    (hmem : ∀ t : ℤ, min x x' ≤ t → t ≤ max x x' → (t, y) ∈ S) :
    AKLT.Blueprint.Win.JoinedIn Adjacent S (x, y) (x', y) := by
  have walk : ∀ n : ℕ, ∀ b : ℤ,
      (∀ t : ℤ, b ≤ t → t ≤ b + n → (t, y) ∈ S) →
      AKLT.Blueprint.Win.JoinedIn Adjacent S (b, y) (b + n, y) := by
    intro n
    induction n with
    | zero =>
        intro b hm
        have hEq : b + (0 : ℕ) = b := by simp
        rw [hEq]
        exact Relation.ReflTransGen.refl
    | succ n ih =>
        intro b hm
        have hprev : AKLT.Blueprint.Win.JoinedIn Adjacent S (b, y) (b + n, y) := by
          apply ih b
          intro t hbt htn
          apply hm t hbt
          omega
        have hstep : Adjacent (b + n, y) (b + (n + 1), y) := by
          simp [Adjacent, latticeDist]
        have hlast : AKLT.Blueprint.Win.JoinedIn Adjacent S (b + n, y) (b + (n + 1), y) :=
          Relation.ReflTransGen.single ⟨hm _ (by omega) (by omega),
            hm _ (by omega) (by omega), hstep⟩
        unfold AKLT.Blueprint.Win.JoinedIn at hprev hlast ⊢
        exact hprev.trans hlast
  let n : ℕ := (x' - x).toNat
  have hn : x' = x + n := by
    dsimp [n]
    omega
  rw [hn]
  apply walk n x
  intro t hxt htn
  apply hmem t
  · omega
  · omega

private theorem joined_horizontal {S : Set Plane} {x x' y : ℤ}
    (hmem : ∀ t : ℤ, min x x' ≤ t → t ≤ max x x' → (t, y) ∈ S) :
    AKLT.Blueprint.Win.JoinedIn Adjacent S (x, y) (x', y) := by
  by_cases hxy : x ≤ x'
  · exact joined_horizontal_up hxy hmem
  · have hyx : x' ≤ x := le_of_not_ge hxy
    have hrev : AKLT.Blueprint.Win.JoinedIn Adjacent S (x', y) (x, y) :=
      joined_horizontal_up hyx (fun t hlow hhigh => hmem t (by omega) (by omega))
    exact joined_symm hrev

private theorem joined_vertical_up {S : Set Plane} {x y y' : ℤ} (hyy : y ≤ y')
    (hmem : ∀ t : ℤ, min y y' ≤ t → t ≤ max y y' → (x, t) ∈ S) :
    AKLT.Blueprint.Win.JoinedIn Adjacent S (x, y) (x, y') := by
  have walk : ∀ n : ℕ, ∀ b : ℤ,
      (∀ t : ℤ, b ≤ t → t ≤ b + n → (x, t) ∈ S) →
      AKLT.Blueprint.Win.JoinedIn Adjacent S (x, b) (x, b + n) := by
    intro n
    induction n with
    | zero =>
        intro b hm
        have hEq : b + (0 : ℕ) = b := by simp
        rw [hEq]
        unfold AKLT.Blueprint.Win.JoinedIn
        exact Relation.ReflTransGen.refl
    | succ n ih =>
        intro b hm
        have hprev := ih b (fun t hbt htn => hm t hbt (by omega))
        have hstep : Adjacent (x, b + n) (x, b + (n + 1)) := by
          simp [Adjacent, latticeDist]
        have hlast : AKLT.Blueprint.Win.JoinedIn Adjacent S
            (x, b + n) (x, b + (n + 1)) :=
          Relation.ReflTransGen.single ⟨hm _ (by omega) (by omega),
            hm _ (by omega) (by omega), hstep⟩
        unfold AKLT.Blueprint.Win.JoinedIn at hprev hlast ⊢
        exact hprev.trans hlast
  let n : ℕ := (y' - y).toNat
  have hn : y' = y + n := by dsimp [n]; omega
  rw [hn]
  apply walk n y
  intro t hyt htn
  exact hmem t (by omega) (by omega)

private theorem joined_vertical {S : Set Plane} {x y y' : ℤ}
    (hmem : ∀ t : ℤ, min y y' ≤ t → t ≤ max y y' → (x, t) ∈ S) :
    AKLT.Blueprint.Win.JoinedIn Adjacent S (x, y) (x, y') := by
  by_cases hyy : y ≤ y'
  · exact joined_vertical_up hyy hmem
  · have hy'y : y' ≤ y := le_of_not_ge hyy
    have hrev : AKLT.Blueprint.Win.JoinedIn Adjacent S (x, y') (x, y) :=
      joined_vertical_up hy'y (fun t hlow hhigh => hmem t (by omega) (by omega))
    exact joined_symm hrev

theorem main : AKLT.Blueprint.Win.CoreConnectedStatement := by
  intro a y u i hsetup
  rcases hsetup with ⟨⟨hl, hu, hy⟩, hi, his, hne⟩
  have hs390 : (390 : ℝ) ≤ shellSpacing u := by
    unfold shellSpacing
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    apply (Real.le_sqrt (by positivity) (by positivity)).2
    have hu' : (390 : ℕ)^4 ≤ u := by
      have : geometryThreshold 64 ≤ u := hu
      unfold geometryThreshold at this
      norm_num at this ⊢
      exact this
    exact_mod_cast hu'
  have hspos : 0 < shellSpacing u := lt_of_lt_of_le (by norm_num) hs390
  have hs4 : shellSpacing u ^ 4 = (u : ℝ) := by
    unfold shellSpacing
    calc
      (Real.sqrt (Real.sqrt (u : ℝ))) ^ 4 =
          ((Real.sqrt (Real.sqrt (u : ℝ))) ^ 2) ^ 2 := by ring
      _ = (Real.sqrt (u : ℝ)) ^ 2 := by rw [Real.sq_sqrt (by positivity)]
      _ = (u : ℝ) := Real.sq_sqrt (by positivity)
  have hi' : (i : ℝ) ≤ shellSpacing u := his
  have hklo : (32 : ℤ) ≤ shellRadius u i := by
    unfold shellRadius
    have hi2 : (2 : ℝ) ≤ (i : ℝ) := by exact_mod_cast hi
    have hprod : (2 : ℝ) * 390 ≤ (i : ℝ) * shellSpacing u :=
      mul_le_mul hi2 hs390 (by norm_num) (by linarith)
    apply Int.le_floor.mpr
    exact_mod_cast (show (32 : ℝ) ≤ (i : ℝ) * shellSpacing u by nlinarith)
  have hkhi : (shellRadius u i : ℝ) ≤ (u : ℝ) - 31 := by
    unfold shellRadius
    calc
      (⌊(i : ℝ) * shellSpacing u⌋ : ℝ) ≤ (i : ℝ) * shellSpacing u := Int.floor_le _
      _ ≤ shellSpacing u ^ 2 := by
        have : 0 ≤ shellSpacing u := le_of_lt hspos
        nlinarith [mul_le_mul_of_nonneg_right hi' this]
      _ ≤ (u : ℝ) - 31 := by
        have hq : (1 : ℝ) ≤ shellSpacing u ^ 2 := by nlinarith
        have hmul : 0 ≤ shellSpacing u ^ 2 * (shellSpacing u ^ 2 - 2) :=
          mul_nonneg (by positivity) (by nlinarith)
        rw [← hs4]
        nlinarith
  have hkhi' : shellRadius u i ≤ (u : ℤ) - 31 := by exact_mod_cast hkhi
  have hklo' : (32 : ℤ) ≤ shellRadius u i := hklo
  have hybox :
      a.1 - (u : ℤ) - 1 ≤ y.1 ∧ y.1 ≤ a.1 + (u : ℤ) + 1 ∧
      a.2 - (u : ℤ) - 1 ≤ y.2 ∧ y.2 ≤ a.2 + (u : ℤ) + 1 := by
    have hupper (j : Fin 2) : (coord j y : ℤ) ≤ coord j a + (u : ℤ) + 1 := by
      by_contra hn
      have hy' : coord j a + (u : ℤ) + 2 ≤ coord j y := by omega
      have hbig : (2 : ℕ∞) ≤ setDistance supDist y (↑(square a u) : Set Plane) := by
        unfold setDistance
        apply le_iInf
        intro z
        have hzmem : z.val ∈ square a u := z.property
        have hcoord : coord j z.val ≤ coord j a + (u : ℤ) := by
          fin_cases j <;> simp [coord, square, Finset.mem_product, Finset.mem_Icc] at hzmem ⊢ <;> omega
        have hnat : 2 ≤ (coord j y - coord j z.val).natAbs := by omega
        have hdist : 2 ≤ supDist y z.val := by
          fin_cases j <;> simp [coord, supDist] at hnat ⊢ <;> omega
        exact_mod_cast hdist
      rw [hy] at hbig
      norm_num at hbig
    have hlower (j : Fin 2) : coord j a - (u : ℤ) - 1 ≤ coord j y := by
      by_contra hn
      have hy' : coord j y + 2 ≤ coord j a - (u : ℤ) := by omega
      have hbig : (2 : ℕ∞) ≤ setDistance supDist y (↑(square a u) : Set Plane) := by
        unfold setDistance
        apply le_iInf
        intro z
        have hzmem : z.val ∈ square a u := z.property
        have hcoord : coord j a - (u : ℤ) ≤ coord j z.val := by
          fin_cases j <;> simp [coord, square, Finset.mem_product, Finset.mem_Icc] at hzmem ⊢ <;> omega
        have hnat : 2 ≤ (coord j y - coord j z.val).natAbs := by omega
        have hdist : 2 ≤ supDist y z.val := by
          fin_cases j <;> simp [coord, supDist] at hnat ⊢ <;> omega
        exact_mod_cast hdist
      rw [hy] at hbig
      norm_num at hbig
    exact ⟨by simpa [coord] using hlower 0, by simpa [coord] using hupper 0,
      by simpa [coord] using hlower 1, by simpa [coord] using hupper 1⟩
  let m : ℤ := (u : ℤ) - 31
  let k : ℤ := shellRadius u i
  have hm : m = (u : ℤ) - 31 := rfl
  have hklo : 32 ≤ k := hklo'
  have hkhi : k ≤ m := by simpa [m, k] using hkhi'
  have hybox' :
      a.1 - m - 32 ≤ y.1 ∧ y.1 ≤ a.1 + m + 32 ∧
      a.2 - m - 32 ≤ y.2 ∧ y.2 ≤ a.2 + m + 32 := by
    rw [hm]
    rcases hybox with ⟨h₁, h₂, h₃, h₄⟩
    exact ⟨by omega, by omega, by omega, by omega⟩
  have hk0 : 0 ≤ k := by omega
  have hm0 : 0 ≤ m := by omega
  let K : Plane → Prop := fun z =>
    a.1 - m ≤ z.1 ∧ z.1 ≤ a.1 + m ∧
    a.2 - m ≤ z.2 ∧ z.2 ≤ a.2 + m ∧
    y.1 - k ≤ z.1 ∧ z.1 ≤ y.1 + k ∧
    y.2 - k ≤ z.2 ∧ z.2 ≤ y.2 + k ∧
    (z.1 = y.1 - k ∨ z.1 = y.1 + k ∨
      z.2 = y.2 - k ∨ z.2 = y.2 + k)
  have hchar (z : Plane) : z ∈ core a y u i ↔ K z := by
    constructor
    · intro hz
      change z ∈ (square a u).filter (fun w =>
        (supDist w y : ℤ) = k ∧ 32 ≤ squareDepth a u w) at hz
      rcases Finset.mem_filter.mp hz with ⟨_, ⟨hrad, hdepth⟩⟩
      have hsup : (supDist z a : ℤ) ≤ m := by
        change 32 ≤ max 0 ((u : ℤ) + 1 - (supDist z a : ℤ)) at hdepth
        rw [hm]
        omega
      have hcoordA₁ : |z.1 - a.1| ≤ m := by
        have hn : (z.1 - a.1).natAbs ≤ supDist z a := le_max_left _ _
        have hc : ((z.1 - a.1).natAbs : ℤ) ≤ (supDist z a : ℤ) := by exact_mod_cast hn
        rw [Int.abs_eq_natAbs]
        exact le_trans hc hsup
      have hcoordA₂ : |z.2 - a.2| ≤ m := by
        have hn : (z.2 - a.2).natAbs ≤ supDist z a := le_max_right _ _
        have hc : ((z.2 - a.2).natAbs : ℤ) ≤ (supDist z a : ℤ) := by exact_mod_cast hn
        rw [Int.abs_eq_natAbs]
        exact le_trans hc hsup
      have hinner₁ : a.1 - m ≤ z.1 ∧ z.1 ≤ a.1 + m := by
        rcases abs_le.mp hcoordA₁ with ⟨hlo, hhi⟩
        constructor <;> omega
      have hinner₂ : a.2 - m ≤ z.2 ∧ z.2 ≤ a.2 + m := by
        rcases abs_le.mp hcoordA₂ with ⟨hlo, hhi⟩
        constructor <;> omega
      have hradInt : max |z.1 - y.1| |z.2 - y.2| = k := by
        change (↑(max (z.1 - y.1).natAbs (z.2 - y.2).natAbs) : ℤ) = k at hrad
        rw [Nat.cast_max, ← Int.abs_eq_natAbs, ← Int.abs_eq_natAbs] at hrad
        exact hrad
      have hcoord₁ : y.1 - k ≤ z.1 ∧ z.1 ≤ y.1 + k := by
        have habs : |z.1 - y.1| ≤ k := by
          calc
            _ ≤ max |z.1 - y.1| |z.2 - y.2| := le_max_left _ _
            _ = k := hradInt
        rcases abs_le.mp habs with ⟨hlo, hhi⟩
        constructor <;> omega
      have hcoord₂ : y.2 - k ≤ z.2 ∧ z.2 ≤ y.2 + k := by
        have habs : |z.2 - y.2| ≤ k := by
          calc
            _ ≤ max |z.1 - y.1| |z.2 - y.2| := le_max_right _ _
            _ = k := hradInt
        rcases abs_le.mp habs with ⟨hlo, hhi⟩
        constructor <;> omega
      have hedge : z.1 = y.1 - k ∨ z.1 = y.1 + k ∨
          z.2 = y.2 - k ∨ z.2 = y.2 + k := by
        have hmax : |z.1 - y.1| = k ∨ |z.2 - y.2| = k := by
          by_cases h : |z.1 - y.1| ≤ |z.2 - y.2|
          · right
            rw [max_eq_right h] at hradInt
            exact hradInt
          · left
            rw [max_eq_left (le_of_not_ge h)] at hradInt
            exact hradInt
        rcases hmax with hmax | hmax
        · rcases (abs_eq (by omega : 0 ≤ k)).mp hmax with hp | hn <;> omega
        · rcases (abs_eq (by omega : 0 ≤ k)).mp hmax with hp | hn <;> omega
      exact ⟨hinner₁.1, hinner₁.2, hinner₂.1, hinner₂.2,
        hcoord₁.1, hcoord₁.2, hcoord₂.1, hcoord₂.2, hedge⟩
    · intro hz
      rcases hz with ⟨ha₁, ha₂, ha₃, ha₄, hy₁, hy₂, hy₃, hy₄, hedge⟩
      have hsup : (supDist z a : ℤ) ≤ m := by
        have h₁ : |z.1 - a.1| ≤ m := abs_le.mpr ⟨by omega, by omega⟩
        have h₂ : |z.2 - a.2| ≤ m := abs_le.mpr ⟨by omega, by omega⟩
        change (↑(max (z.1 - a.1).natAbs (z.2 - a.2).natAbs) : ℤ) ≤ m
        rw [Nat.cast_max, ← Int.abs_eq_natAbs, ← Int.abs_eq_natAbs]
        exact max_le_iff.mpr ⟨h₁, h₂⟩
      have hsq : z ∈ square a u := by
        have hmu : m ≤ (u : ℤ) := by rw [hm]; omega
        apply Finset.mem_product.mpr
        constructor
        · apply Finset.mem_Icc.mpr
          exact ⟨by omega, by omega⟩
        · apply Finset.mem_Icc.mpr
          exact ⟨by omega, by omega⟩
      have hdepth : 32 ≤ squareDepth a u z := by
        change 32 ≤ max 0 ((u : ℤ) + 1 - (supDist z a : ℤ))
        rw [hm] at hsup
        have hinner : 32 ≤ (u : ℤ) + 1 - (supDist z a : ℤ) := by omega
        exact le_trans hinner (le_max_right _ _)
      have hrad : (supDist z y : ℤ) = k := by
        have h₁ : |z.1 - y.1| ≤ k := abs_le.mpr ⟨by omega, by omega⟩
        have h₂ : |z.2 - y.2| ≤ k := abs_le.mpr ⟨by omega, by omega⟩
        have hedge' : |z.1 - y.1| = k ∨ |z.2 - y.2| = k := by
          rcases hedge with h | h | h | h
          · left; rw [h]; simp [abs_neg, abs_of_nonneg hk0]
          · left; rw [h]; simp [abs_of_nonneg hk0]
          · right; rw [h]; simp [abs_neg, abs_of_nonneg hk0]
          · right; rw [h]; simp [abs_of_nonneg hk0]
        have hmax : max |z.1 - y.1| |z.2 - y.2| = k := by
          rcases hedge' with h | h
          · rw [max_eq_left (le_trans h₂ (le_of_eq h.symm))]
            exact h
          · rw [max_eq_right (le_trans h₁ (le_of_eq h.symm))]
            exact h
        change (↑(max (z.1 - y.1).natAbs (z.2 - y.2).natAbs) : ℤ) = k
        rw [Nat.cast_max, ← Int.abs_eq_natAbs, ← Int.abs_eq_natAbs]
        exact hmax
      change z ∈ (square a u).filter (fun w =>
        (supDist w y : ℤ) = k ∧ 32 ≤ squareDepth a u w)
      exact Finset.mem_filter.mpr ⟨hsq, hrad, hdepth⟩
  have hxend : ∃ cx : ℤ, a.1 - m ≤ cx ∧ cx ≤ a.1 + m ∧
      y.1 - k ≤ cx ∧ cx ≤ y.1 + k ∧ (cx = y.1 - k ∨ cx = y.1 + k) := by
    by_cases h : a.1 ≤ y.1
    · refine ⟨y.1 - k, ?_, ?_, ?_, ?_, Or.inl rfl⟩ <;> omega
    · refine ⟨y.1 + k, ?_, ?_, ?_, ?_, Or.inr rfl⟩ <;> omega
  have hyend : ∃ cy : ℤ, a.2 - m ≤ cy ∧ cy ≤ a.2 + m ∧
      y.2 - k ≤ cy ∧ cy ≤ y.2 + k ∧ (cy = y.2 - k ∨ cy = y.2 + k) := by
    by_cases h : a.2 ≤ y.2
    · refine ⟨y.2 - k, ?_, ?_, ?_, ?_, Or.inl rfl⟩ <;> omega
    · refine ⟨y.2 + k, ?_, ?_, ?_, ?_, Or.inr rfl⟩ <;> omega
  rcases hxend with ⟨cx, hcxa₁, hcxa₂, hcxk₁, hcxk₂, hcxedge⟩
  rcases hyend with ⟨cy, hcya₁, hcya₂, hcyk₁, hcyk₂, hcyedge⟩
  have hcenter : K (cx, cy) := by
    refine ⟨hcxa₁, hcxa₂, hcya₁, hcya₂, hcxk₁, hcxk₂, hcyk₁, hcyk₂, ?_⟩
    rcases hcxedge with h | h
    · exact Or.inl h
    · rcases hcyedge with h' | h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inr (Or.inr h'))
  have hcenterCore : (cx, cy) ∈ core a y u i := (hchar _).2 hcenter
  have hcoreNonempty : (↑(core a y u i) : Set Plane).Nonempty := ⟨(cx, cy), hcenterCore⟩
  refine ⟨⟨hcoreNonempty, ?_⟩, ?_⟩
  · intro z hz w hw
    have hzK := (hchar z).1 hz
    have hwK := (hchar w).1 hw
    have joinToCenter : ∀ v : Plane, K v → AKLT.Blueprint.Win.JoinedIn Adjacent
        (↑(core a y u i) : Set Plane) v (cx, cy) := by
      intro v hv
      rcases hv with ⟨ha₁, ha₂, ha₃, ha₄, hy₁, hy₂, hy₃, hy₄, hedge⟩
      rcases hedge with hxl | hxu | hyl | hyu
      · have hfirst : AKLT.Blueprint.Win.JoinedIn Adjacent
            (↑(core a y u i) : Set Plane) (v.1, v.2) (v.1, cy) := by
          apply joined_vertical
          intro t hlo hhi
          apply (hchar (v.1, t)).2
          refine ⟨ha₁, ha₂, ?_, ?_, hy₁, hy₂, ?_, ?_, Or.inl hxl⟩
          · omega
          · omega
          · omega
          · omega
        have hsecond : AKLT.Blueprint.Win.JoinedIn Adjacent
            (↑(core a y u i) : Set Plane) (v.1, cy) (cx, cy) := by
          apply joined_horizontal
          intro t hlo hhi
          apply (hchar (t, cy)).2
          refine ⟨?_, ?_, hcya₁, hcya₂, ?_, ?_, hcyk₁, hcyk₂, ?_⟩
          · omega
          · omega
          · omega
          · omega
          · rcases hcyedge with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))
        unfold AKLT.Blueprint.Win.JoinedIn at hfirst hsecond
        exact hfirst.trans hsecond
      · have hfirst : AKLT.Blueprint.Win.JoinedIn Adjacent
            (↑(core a y u i) : Set Plane) (v.1, v.2) (v.1, cy) := by
          apply joined_vertical
          intro t hlo hhi
          apply (hchar (v.1, t)).2
          refine ⟨ha₁, ha₂, ?_, ?_, hy₁, hy₂, ?_, ?_, Or.inr (Or.inl hxu)⟩
          · omega
          · omega
          · omega
          · omega
        have hsecond : AKLT.Blueprint.Win.JoinedIn Adjacent
            (↑(core a y u i) : Set Plane) (v.1, cy) (cx, cy) := by
          apply joined_horizontal
          intro t hlo hhi
          apply (hchar (t, cy)).2
          refine ⟨?_, ?_, hcya₁, hcya₂, ?_, ?_, hcyk₁, hcyk₂, ?_⟩
          · omega
          · omega
          · omega
          · omega
          · rcases hcyedge with h | h
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h))
        unfold AKLT.Blueprint.Win.JoinedIn at hfirst hsecond
        exact hfirst.trans hsecond
      · have hfirst : AKLT.Blueprint.Win.JoinedIn Adjacent
            (↑(core a y u i) : Set Plane) (v.1, v.2) (cx, v.2) := by
          apply joined_horizontal
          intro t hlo hhi
          apply (hchar (t, v.2)).2
          refine ⟨?_, ?_, ha₃, ha₄, ?_, ?_, hy₃, hy₄, Or.inr (Or.inr (Or.inl hyl))⟩
          · omega
          · omega
          · omega
          · omega
        have hsecond : AKLT.Blueprint.Win.JoinedIn Adjacent
            (↑(core a y u i) : Set Plane) (cx, v.2) (cx, cy) := by
          apply joined_vertical
          intro t hlo hhi
          apply (hchar (cx, t)).2
          refine ⟨hcxa₁, hcxa₂, ?_, ?_, hcxk₁, hcxk₂, ?_, ?_, ?_⟩
          · omega
          · omega
          · omega
          · omega
          · rcases hcxedge with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
        unfold AKLT.Blueprint.Win.JoinedIn at hfirst hsecond
        exact hfirst.trans hsecond
      · have hfirst : AKLT.Blueprint.Win.JoinedIn Adjacent
            (↑(core a y u i) : Set Plane) (v.1, v.2) (cx, v.2) := by
          apply joined_horizontal
          intro t hlo hhi
          apply (hchar (t, v.2)).2
          refine ⟨?_, ?_, ha₃, ha₄, ?_, ?_, hy₃, hy₄, Or.inr (Or.inr (Or.inr hyu))⟩
          · omega
          · omega
          · omega
          · omega
        have hsecond : AKLT.Blueprint.Win.JoinedIn Adjacent
            (↑(core a y u i) : Set Plane) (cx, v.2) (cx, cy) := by
          apply joined_vertical
          intro t hlo hhi
          apply (hchar (cx, t)).2
          refine ⟨hcxa₁, hcxa₂, ?_, ?_, hcxk₁, hcxk₂, ?_, ?_, ?_⟩
          · omega
          · omega
          · omega
          · omega
          · rcases hcxedge with h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
        unfold AKLT.Blueprint.Win.JoinedIn at hfirst hsecond
        exact hfirst.trans hsecond
    have hzw := (joinToCenter z hzK).trans (joined_symm (joinToCenter w hwK))
    exact hzw
  · intro z hz
    have hzK := (hchar z).1 hz
    have hzcore := (hchar z).2 hzK
    change z ∈ (square a u).filter (fun w =>
      (supDist w y : ℤ) = k ∧ 32 ≤ squareDepth a u w) at hzcore
    rcases Finset.mem_filter.mp hzcore with ⟨hsq, ⟨hrad, hdepth⟩⟩
    have hoff : radialOffset y u i z = 0 := by
      unfold radialOffset
      rw [hrad]
      simp [k]
    change z ∈ (square a u).filter (fun w =>
      (radialOffset y u i w : ℝ) ≤ shellSpacing u / 12 ∧
      (radialOffset y u i w : ℤ) + 32 ≤ squareDepth a u w)
    refine Finset.mem_filter.mpr ⟨hsq, ?_⟩
    constructor
    · rw [hoff]
      norm_num
      positivity
    · rw [hoff]
      simpa using hdepth

end AKLT.W.WIN032
