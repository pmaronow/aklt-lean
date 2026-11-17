module
public import AKLT.Blueprint.Rec.NodesRecursion

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC083

private def removalDomain {G : Finset Plane} (Y : Finset Plane) : Network G where
  status := fun x => if x ∈ G \ Y then .U else .X
  kept := fun x => neighbours x ∩ G

private theorem removal_active {G : Finset Plane} (Y : Finset Plane)
    (_hYG : Y ⊆ G) : (removalDomain (G := G) Y).active = G \ Y := by
  ext x
  simp [Network.active, removalDomain]

private theorem protected_nonempty_of_nonempty (G : Finset Plane) (hG : G.Nonempty) :
    (protectedSites G).Nonempty := by
  classical
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image G (fun z => z.1) hG
  let z : Plane := (x.1 + 1, x.2)
  have hz : z ∉ G := by
    intro hz
    have hle := hmax z hz
    dsimp [z] at hle
    omega
  have hbd : boundaryDepth G x ≤ 1 := by
    unfold boundaryDepth setDistance
    apply iInf_le_of_le ⟨z, hz⟩
    norm_num [z, latticeDist]
  have hprot : x ∈ protectedSites G := by
    simp only [protectedSites, Finset.mem_filter]
    exact ⟨hx, le_trans hbd (by norm_num)⟩
  exact ⟨x, hprot⟩

private theorem finite_distance_to_nonempty (S : Finset Plane)
    (hS : S.Nonempty) (x : Plane) :
    setDistance latticeDist x (↑S : Set Plane) ≠ ⊤ := by
  obtain ⟨s, hs⟩ := hS
  have hle : setDistance latticeDist x (↑S : Set Plane) ≤ (latticeDist x s : ℕ∞) := by
    unfold setDistance
    exact iInf_le_of_le ⟨s, hs⟩ le_rfl
  intro htop
  rw [htop] at hle
  simp at hle

private theorem pair_type_of_distance (u v : Plane) (h : latticeDist u v = 2) :
    ∃ X : PairType, HasPairType X u v := by
  by_cases hx : u.1 = v.1
  · exact ⟨.B, h, Or.inl hx⟩
  · by_cases hy : u.2 = v.2
    · exact ⟨.B, h, Or.inr hy⟩
    · exact ⟨.C, h, ⟨hx, hy⟩⟩

private theorem neighbours_card (x : Plane) : (neighbours x).card = 4 := by
  rw [neighbours, Finset.card_image_of_injOn]
  · exact (by decide : Fintype.card Compass = 4)
  · intro a ha b hb hab
    have hstep : a.step = b.step := add_left_cancel hab
    cases a <;> cases b <;> simp [Compass.step] at hstep ⊢

private theorem removal_local (G Y : Finset Plane) (hYG : Y ⊆ G) :
    (removalDomain (G := G) Y).LocalRules := by
  classical
  let D := removalDomain (G := G) Y
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    change (if x ∈ G \ Y then Status.U else Status.X) = Status.X
    simp [Finset.mem_sdiff, hx]
  · intro x
    exact Finset.Subset.rfl
  · intro x hxG hs
    by_cases hy : x ∈ Y
    · simp [D, removalDomain, hxG, hy] at hs
    · simp [D, removalDomain, hxG, hy] at hs
  · intro x hxActive
    let P := D.presentNeighbours x
    let L := (originalLegs G).filter fun e => e.1 = x
    let T := L.image Prod.snd
    have hPsub : P ⊆ neighbours x := by
      intro z hz
      exact (Finset.mem_filter.mp hz).1
    have hTsub : T ⊆ neighbours x \ G := by
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨e, heL, rfl⟩
      rcases Finset.mem_filter.mp heL with ⟨he, hfst⟩
      unfold originalLegs at he
      rcases Finset.mem_biUnion.mp he with ⟨a, ha, he⟩
      rcases Finset.mem_image.mp he with ⟨z, hz, heq⟩
      have haz : a = x := by
        have hh := congrArg Prod.fst heq
        simpa [hfst] using hh
      subst a
      have hz' := Finset.mem_sdiff.mp hz
      have hsecond : e.2 = z := by
        have hh := congrArg Prod.snd heq
        exact hh.symm
      rw [hsecond]
      exact Finset.mem_sdiff.mpr hz'
    have hPsubG : P ⊆ G := by
      intro z hz
      rcases Finset.mem_filter.mp hz with ⟨_, hp⟩
      rcases hp with ⟨_, hzActive, _, _, _⟩
      exact (Finset.mem_filter.mp hzActive).1
    have hdisj : Disjoint P T := by
      apply Finset.disjoint_left.mpr
      intro z hzP hzT
      have hzG := hPsubG hzP
      have hznot := Finset.mem_sdiff.mp (hTsub hzT)
      exact hznot.2 hzG
    have hcardT : T.card = L.card := by
      apply Finset.card_image_of_injOn
      intro e he f hf hEq
      have hefst := (Finset.mem_filter.mp he).2
      have hffst := (Finset.mem_filter.mp hf).2
      exact Prod.ext (hefst.trans hffst.symm) hEq
    have hbound : P.card + L.card ≤ 4 := by
      calc
        P.card + L.card = P.card + T.card := by rw [hcardT]
        _ = (P ∪ T).card := (Finset.card_union_of_disjoint hdisj).symm
        _ ≤ (neighbours x).card := Finset.card_le_card (Finset.union_subset hPsub (Finset.Subset.trans hTsub Finset.sdiff_subset))
        _ = 4 := neighbours_card x
    simpa [D, P, L, Network.presentNeighbours] using hbound

private theorem neighbour_symm {x y : Plane} (h : y ∈ neighbours x) :
    x ∈ neighbours y := by
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and] at h ⊢
  rcases h with ⟨d, rfl⟩
  cases d with
  | east => exact ⟨Compass.west, by simp [Compass.step]; abel⟩
  | north => exact ⟨Compass.south, by simp [Compass.step]; abel⟩
  | west => exact ⟨Compass.east, by simp [Compass.step]; abel⟩
  | south => exact ⟨Compass.north, by simp [Compass.step]; abel⟩

private theorem removal_consistent (G Y : Finset Plane)
    (hY : Y ⊆ G \ protectedSites G) : (removalDomain (G := G) Y).Consistent := by
  classical
  let D := removalDomain (G := G) Y
  have hYG : Y ⊆ G := Finset.Subset.trans hY Finset.sdiff_subset
  have hlocal : D.LocalRules := removal_local G Y hYG
  refine ⟨⟨hlocal, ?_⟩, ?_, ?_, ?_⟩
  · intro x hx
    have hxG : x ∈ G := by
      have hx' : x ∈ protectedSites G := hx
      simpa [protectedSites] using (Finset.mem_filter.mp hx').1
    have hxY : x ∉ Y := by
      intro h
      exact (Finset.mem_sdiff.mp (hY h)).2 hx
    exact ⟨by simp [D, removalDomain, hxY, hxG], rfl⟩
  · intro x hx hs
    rfl
  · intro x hx hs
    by_cases hy : x ∈ Y
    · simp [D, removalDomain, hx, hy] at hs
    · simp [D, removalDomain, hx, hy] at hs
  · intro x hx y hy hxy
    have hxG : x ∈ G := (Finset.mem_filter.mp hx).1
    have hyG : y ∈ G := (Finset.mem_filter.mp hy).1
    have hxyN : y ∈ neighbours x ↔ x ∈ neighbours y :=
      ⟨neighbour_symm, neighbour_symm⟩
    simp [D, removalDomain, hxG, hyG, hxyN]

private def liftIco {V : Finset Plane} (a : (x : V) → IcoLetter) :
    (x : V) → SpinLetter := fun x => some (a x)

private theorem sum_spinletter_supported {V : Finset Plane}
    (F : ((x : V) → SpinLetter) → ℝ)
    (hzero : ∀ σ, (∃ x, σ x = none) → F σ = 0) :
    (∑ σ : (x : V) → SpinLetter, F σ) =
      ∑ a : (x : V) → IcoLetter, F (liftIco a) := by
  classical
  let good : Finset ((x : V) → SpinLetter) :=
    Finset.univ.filter fun σ => ∀ x, ∃ a, σ x = some a
  have hmem (σ : (x : V) → SpinLetter) :
      σ ∈ good ↔ ∃ a : (x : V) → IcoLetter, liftIco a = σ := by
    constructor
    · intro hσ
      have hall : ∀ x, ∃ a, σ x = some a := (Finset.mem_filter.mp hσ).2
      let a : (x : V) → IcoLetter := fun x => Classical.choose (hall x)
      refine ⟨a, ?_⟩
      funext x
      exact (Classical.choose_spec (hall x)).symm
    · rintro ⟨a, rfl⟩
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · intro x
        exact ⟨a x, rfl⟩
  have hgood : good = Finset.image liftIco Finset.univ := by
    ext σ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_univ, true_and]
    exact hmem σ
  have hinj : Set.InjOn (liftIco (V := V)) (↑(Finset.univ : Finset ((x : V) → IcoLetter))) := by
    intro a ha b hb hab
    funext x
    exact Option.some.inj (congrFun hab x)
  have hsumGood : (∑ σ ∈ good, F σ) = ∑ a : (x : V) → IcoLetter, F (liftIco a) := by
    rw [hgood]
    simpa using (Finset.sum_image hinj)
  have hbad : ∀ σ ∈ (Finset.univ : Finset ((x : V) → SpinLetter)),
      σ ∉ good → F σ = 0 := by
    intro σ hσ hnot
    have hnone : ∃ x, σ x = none := by
      by_contra hnone
      apply hnot
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_univ _
      · intro x
        cases hval : σ x with
        | none => exact False.elim (hnone ⟨x, hval⟩)
        | some a => exact ⟨a, rfl⟩
    exact hzero σ hnone
  calc
    ∑ σ : (x : V) → SpinLetter, F σ = ∑ σ ∈ good, F σ := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) hbad
    _ = ∑ a : (x : V) → IcoLetter, F (liftIco a) := hsumGood

@[simp] private theorem east_mem_neighbours (x : Plane) :
    (x.1 + 1, x.2) ∈ neighbours x := by
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨.east, by cases x with | mk a b => simp [Compass.step]⟩

@[simp] private theorem west_mem_neighbours (x : Plane) :
    x ∈ neighbours (x.1 + 1, x.2) := by
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨.west, by cases x with | mk a b => norm_num [Compass.step]⟩

@[simp] private theorem north_mem_neighbours (x : Plane) :
    (x.1, x.2 + 1) ∈ neighbours x := by
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨.north, by cases x with | mk a b => simp [Compass.step]⟩

@[simp] private theorem south_mem_neighbours (x : Plane) :
    x ∈ neighbours (x.1, x.2 + 1) := by
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨.south, by cases x with | mk a b => norm_num [Compass.step]⟩

@[simp] private theorem east_adjacent (x : Plane) : Adjacent x (x.1 + 1, x.2) := by
  norm_num [Adjacent, latticeDist]

@[simp] private theorem north_adjacent (x : Plane) : Adjacent x (x.1, x.2 + 1) := by
  norm_num [Adjacent, latticeDist]

private theorem removal_bonds (G Y : Finset Plane) (hYG : Y ⊆ G) :
    (removalDomain (G := G) Y).bonds = internalBonds (G \ Y) := by
  classical
  ext e
  rcases e with ⟨x, y⟩
  simp [Network.bonds, Network.Present, removalDomain, Network.active, internalBonds,
    positiveNeighbours, Finset.mem_sdiff]
  constructor
  · rintro ⟨⟨hxG, hpos, hyG⟩, ⟨_, hxY⟩, ⟨_, hyY⟩, _, _, _, _⟩
    exact ⟨⟨hxG, hxY⟩, hpos, hyG, hyY⟩
  · rintro ⟨⟨hxG, hxY⟩, hpos, hyG, hyY⟩
    rcases hpos with he | hn
    · subst y
      exact ⟨⟨hxG, Or.inl rfl, hyG⟩, ⟨hxG, hxY⟩, ⟨hyG, hyY⟩,
        east_adjacent x, ⟨east_mem_neighbours x, hyG⟩, west_mem_neighbours x, hxG⟩
    · subst y
      exact ⟨⟨hxG, Or.inr rfl, hyG⟩, ⟨hxG, hxY⟩, ⟨hyG, hyY⟩,
        north_adjacent x, ⟨north_mem_neighbours x, hyG⟩, south_mem_neighbours x, hxG⟩

private theorem ico_unit : ∀ j : IcoLetter, normSq (icoVector j) = 1 := by
  have hφ : goldenRatio ^ 2 = goldenRatio + 1 := by
    unfold goldenRatio
    nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  have hr : icoRadius ^ 2 = goldenRatio + 2 := by
    unfold icoRadius
    rw [Real.sq_sqrt (by unfold goldenRatio; positivity)]
  have hRpos : 0 < icoRadius := by
    unfold icoRadius
    apply Real.sqrt_pos.2
    unfold goldenRatio
    nlinarith [Real.sqrt_nonneg (5 : ℝ)]
  intro j
  rcases j with ⟨a,b,c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [normSq, dot, Fin.sum_univ_three, icoVector, signValue, Fin.ext_iff] <;>
    field_simp [ne_of_gt hRpos] <;> nlinarith [hφ, hr]

private theorem normSq_nonneg_local (a : Vec3) : 0 ≤ normSq a := by
  unfold normSq dot
  apply Finset.sum_nonneg
  intro i hi
  exact mul_self_nonneg (a i)

private theorem dot_bound_local (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    |dot a b| ≤ 1 := by
  have hna : 0 ≤ normSq a := normSq_nonneg_local a
  have hnb : 0 ≤ normSq b := normSq_nonneg_local b
  have hcs : dot a b ^ 2 ≤ normSq a * normSq b := by
    simpa [dot, normSq, mul_comm, pow_two] using
      (Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 3)) a b)
  have hp : normSq a * normSq b ≤ 1 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]
  apply abs_le.mpr
  constructor <;> nlinarith [sq_nonneg (dot a b - 1), sq_nonneg (dot a b + 1)]

private theorem ball_factor_local (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b ∧ 1 + dot a b ≤ 2 := by
  have h := dot_bound_local a b ha hb
  constructor <;> nlinarith [abs_le.mp h]

private theorem spin_norm_local (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => exact le_of_eq (ico_unit j)

private theorem network_spin_norm_local {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  classical
  by_cases hx : x ∈ D.active
  · simp [Network.spins, hx, spin_norm_local]
  · simp [Network.spins, hx, normSq, dot]

private def domainWeight {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (n : (x : D.active) → SpinLetter) : ℝ :=
  (∏ x : D.active, spinWeight (D.status x.val) (n x)) *
    (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
    ∏ e : originalLegs G,
      if b = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n e.val.1) else 1

private theorem domainWeight_nonneg {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (n : (x : D.active) → SpinLetter) :
    0 ≤ domainWeight D τ b n := by
  classical
  unfold domainWeight
  apply mul_nonneg
  · apply mul_nonneg
    · apply Finset.prod_nonneg
      intro x hx
      cases D.status x.val <;> cases n x <;> norm_num [spinWeight]
    · apply Finset.prod_nonneg
      intro e he
      exact (ball_factor_local _ _ (network_spin_norm_local D n e.1)
        (network_spin_norm_local D n e.2)).1
  · apply Finset.prod_nonneg
    intro e he
    by_cases hb : b = true ∧ e.val.1 ∈ D.active
    · simp [hb]
      exact (ball_factor_local _ _ (le_of_eq (τ e).property)
        (network_spin_norm_local D n e.val.1)).1
    · simp [hb]

private theorem partition_eq_weighted {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f = ∑ n : (x : D.active) → SpinLetter,
      domainWeight D τ b n * f (D.spins n) := by
  classical
  unfold Network.partition domainWeight
  apply Finset.sum_congr rfl
  intro n hn
  ring

private theorem expectation_abs_dot_le_one {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) (u v : Plane) :
    |D.expectation τ b (fun n => dot (n u) (n v))| ≤ 1 := by
  classical
  let W : ((x : D.active) → SpinLetter) → ℝ := domainWeight D τ b
  let f : ((x : D.active) → SpinLetter) → ℝ := fun n => dot (D.spins n u) (D.spins n v)
  have hW : ∀ n, 0 ≤ W n := fun n => domainWeight_nonneg D τ b n
  have hf : ∀ n, |f n| ≤ 1 := by
    intro n
    exact dot_bound_local _ _ (network_spin_norm_local D n u) (network_spin_norm_local D n v)
  have hlo : -D.partition τ b (fun _ => 1) ≤ D.partition τ b (fun n => dot (n u) (n v)) := by
    rw [partition_eq_weighted, partition_eq_weighted]
    simp only [mul_one]
    calc
      -(∑ n, domainWeight D τ b n) = ∑ n, -domainWeight D τ b n := by simp
      _ ≤ ∑ n, domainWeight D τ b n * dot (D.spins n u) (D.spins n v) :=
        Finset.sum_le_sum fun n hn => by
          have hfi := abs_le.mp (hf n)
          change -W n ≤ W n * f n
          have hm := mul_le_mul_of_nonneg_left hfi.1 (hW n)
          nlinarith
  have hhi : D.partition τ b (fun n => dot (n u) (n v)) ≤ D.partition τ b (fun _ => 1) := by
    rw [partition_eq_weighted, partition_eq_weighted]
    simp only [mul_one]
    exact Finset.sum_le_sum fun n hn => by
      have hfi := abs_le.mp (hf n)
      change W n * f n ≤ W n
      have hm := mul_le_mul_of_nonneg_left hfi.2 (hW n)
      nlinarith
  have hZ : 0 ≤ D.partition τ b (fun _ => 1) := by
    rw [partition_eq_weighted]
    simp only [mul_one]
    exact Finset.sum_nonneg fun n hn => hW n
  by_cases hz : D.partition τ b (fun _ => 1) = 0
  · have hN : D.partition τ b (fun n => dot (n u) (n v)) = 0 := by
      apply le_antisymm
      · simpa [hz] using hhi
      · simpa [hz] using hlo
    simp [Network.expectation, hz, hN]
  · have hzpos : 0 < D.partition τ b (fun _ => 1) := lt_of_le_of_ne hZ (Ne.symm hz)
    have habs : |D.partition τ b (fun n => dot (n u) (n v))| ≤ D.partition τ b (fun _ => 1) :=
      abs_le.mpr ⟨hlo, hhi⟩
    unfold Network.expectation
    rw [abs_div, abs_of_pos hzpos]
    exact (div_le_iff₀ hzpos).2 (by simpa using habs)

private theorem response_abs_le_two {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (u v : Plane) :
    |D.expectation τ true (fun n => dot (n u) (n v)) -
      D.expectation τ false (fun n => dot (n u) (n v))| ≤ 2 := by
  have ht := expectation_abs_dot_le_one D τ true u v
  have hf := expectation_abs_dot_le_one D τ false u v
  apply abs_le.mpr
  rcases abs_le.mp ht with ⟨htlo, hthi⟩
  rcases abs_le.mp hf with ⟨hflo, hfhi⟩
  constructor <;> linarith


private theorem removal_partition_free (G Y : Finset Plane) (τ : PinAssignment G)
    (hYG : Y ⊆ G) (f : (Plane → Vec3) → ℝ) :
    (removalDomain (G := G) Y).partition τ false f = freeSum G Y f := by
  classical
  let D := removalDomain (G := G) Y
  let V : Finset Plane := D.active
  have hV : V = G \ Y := by
    simpa [D, V] using removal_active (G := G) Y hYG
  have hbonds : D.bonds = internalBonds V := by
    rw [removal_bonds G Y hYG]
    rw [← hV]
  have hstatus : ∀ x : V, D.status x.val = Status.U := by
    intro x
    have hx := x.property
    simpa [D, V, Network.active, removalDomain, Finset.mem_sdiff] using hx
  rw [partition_eq_weighted]
  unfold freeSum
  rw [← hV]
  let summand (n : (x : V) → SpinLetter) : ℝ :=
    domainWeight D τ false n * f (D.spins n)
  have hzero : ∀ n : (x : V) → SpinLetter, (∃ x, n x = none) → summand n = 0 := by
    intro n hn
    obtain ⟨x, hx⟩ := hn
    have hsite : (∏ z : V, spinWeight Status.U (n z)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ x)
      simp [hx, spinWeight]
    unfold summand domainWeight
    simp_rw [hstatus]
    rw [hsite]
    simp
  rw [sum_spinletter_supported summand hzero]
  apply Finset.sum_congr rfl
  intro a ha
  have hsite : (∏ x : V, spinWeight Status.U (some (a x))) =
      (1 / 12 : ℝ) ^ V.card := by simp [spinWeight]
  have hspin : D.spins (liftIco a) = extendIcoSpins a := by
    funext x
    by_cases hx : x ∈ D.active
    · change x ∈ V at hx
      simp [D, V, Network.spins, removalDomain, extendIcoSpins, liftIco,
        spinVector, hx]
    · have hxV : x ∉ V := by simpa [V] using hx
      simp [D, V, Network.spins, removalDomain, extendIcoSpins, liftIco,
        spinVector, hx, hxV]
  have hsite' : (∏ x : V, spinWeight Status.U (liftIco a x)) =
      (1 / 12 : ℝ) ^ V.card := by simpa [liftIco] using hsite
  unfold summand domainWeight
  simp_rw [hstatus]
  rw [hsite', hbonds]
  simp_rw [hspin]
  simp [V]
  ring

private theorem removal_partition_pinned (G Y : Finset Plane) (τ : PinAssignment G)
    (hYG : Y ⊆ G) (f : (Plane → Vec3) → ℝ) :
    (removalDomain (G := G) Y).partition τ true f = pinnedSum G Y τ f := by
  classical
  let D := removalDomain (G := G) Y
  let V : Finset Plane := D.active
  have hV : V = G \ Y := by
    simpa [D, V] using removal_active (G := G) Y hYG
  have hbonds : D.bonds = internalBonds V := by
    rw [removal_bonds G Y hYG]
    rw [← hV]
  have hstatus : ∀ x : V, D.status x.val = Status.U := by
    intro x
    have hx := x.property
    simpa [D, V, Network.active, removalDomain, Finset.mem_sdiff] using hx
  rw [partition_eq_weighted]
  unfold pinnedSum
  rw [← hV]
  let summand (n : (x : V) → SpinLetter) : ℝ :=
    domainWeight D τ true n * f (D.spins n)
  have hzero : ∀ n : (x : V) → SpinLetter, (∃ x, n x = none) → summand n = 0 := by
    intro n hn
    obtain ⟨x, hx⟩ := hn
    have hsite : (∏ z : V, spinWeight Status.U (n z)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ x)
      simp [hx, spinWeight]
    unfold summand domainWeight
    simp_rw [hstatus]
    rw [hsite]
    simp
  rw [sum_spinletter_supported summand hzero]
  apply Finset.sum_congr rfl
  intro a ha
  have hsite : (∏ x : V, spinWeight Status.U (some (a x))) =
      (1 / 12 : ℝ) ^ V.card := by
    simp [spinWeight]
  have hspin : D.spins (liftIco a) = extendIcoSpins a := by
    funext x
    by_cases hx : x ∈ D.active
    · change x ∈ V at hx
      simp [D, V, Network.spins, removalDomain, extendIcoSpins, liftIco,
        spinVector, hx]
    · have hxV : x ∉ V := by simpa [V] using hx
      simp [D, V, Network.spins, removalDomain, extendIcoSpins, liftIco,
        spinVector, hx, hxV]
  have hsite' : (∏ x : V, spinWeight Status.U (liftIco a x)) =
      (1 / 12 : ℝ) ^ V.card := by simpa [liftIco] using hsite
  unfold summand domainWeight
  simp_rw [hstatus]
  rw [hsite', hbonds]
  simp_rw [hspin]
  simp [V]
  ring

private theorem removal_pinned_expectation (G Y : Finset Plane) (τ : PinAssignment G)
    (hYG : Y ⊆ G) (f : (Plane → Vec3) → ℝ) :
    (removalDomain (G := G) Y).expectation τ true f = pinnedExpectation G Y τ f := by
  unfold Network.expectation pinnedExpectation
  rw [removal_partition_pinned G Y τ hYG f,
    removal_partition_pinned G Y τ hYG (fun _ => 1)]

private theorem removal_free_expectation (G Y : Finset Plane) (τ : PinAssignment G)
    (hYG : Y ⊆ G) (f : (Plane → Vec3) → ℝ) :
    (removalDomain (G := G) Y).expectation τ false f = freeExpectation G Y f := by
  unfold Network.expectation freeExpectation
  rw [removal_partition_free G Y τ hYG f,
    removal_partition_free G Y τ hYG (fun _ => 1)]

private theorem responseEnvelope_bddAbove (X : PairType) (d : ℤ) :
    BddAbove ({0} ∪ {r : ℝ | ∃ G : Finset Plane, ∃ τ : PinAssignment G,
      ∃ D : Network G, ∃ u v c : Plane, D.ResponsePair X u v c ∧
      (d.toNat : ℕ∞) ≤ min (setDistance latticeDist u (↑(protectedSites G) : Set Plane))
        (setDistance latticeDist v (↑(protectedSites G) : Set Plane)) ∧
      r = |D.expectation τ true (fun n => dot (n u) (n v)) -
        D.expectation τ false (fun n => dot (n u) (n v))|}) := by
  refine ⟨2, ?_⟩
  intro r hr
  rcases (Set.mem_union r ({0} : Set ℝ) _).mp hr with hzero | hpair
  · simp only [Set.mem_singleton_iff] at hzero
    subst r
    norm_num
  · rcases hpair with ⟨G, τ, D, u, v, c, hpair, hdepth, rfl⟩
    exact response_abs_le_two D τ u v

theorem main : AKLT.Blueprint.Rec.RemovalEnvelopeStatement := by
  classical
  intro G τ Y hY u v hu hv huv hc
  have hYG : Y ⊆ G := Finset.Subset.trans hY Finset.sdiff_subset
  have huG : u ∈ G := (Finset.mem_sdiff.mp hu).1
  have hGne : G.Nonempty := ⟨u, huG⟩
  have hS : (protectedSites G).Nonempty := protected_nonempty_of_nonempty G hGne
  have hdu : setDistance latticeDist u (↑(protectedSites G) : Set Plane) ≠ ⊤ :=
    finite_distance_to_nonempty (protectedSites G) hS u
  have hdv : setDistance latticeDist v (↑(protectedSites G) : Set Plane) ≠ ⊤ :=
    finite_distance_to_nonempty (protectedSites G) hS v
  let depth := min (setDistance latticeDist u (↑(protectedSites G) : Set Plane))
    (setDistance latticeDist v (↑(protectedSites G) : Set Plane))
  have hdepthFinite : depth ≠ ⊤ := by
    intro htop
    exact hdu (min_eq_top.mp (by simpa [depth] using htop)).1
  let d : ℕ := depth.toNat
  have hdepthCast : (d : ℕ∞) = depth := ENat.coe_toNat hdepthFinite
  obtain ⟨X, hX⟩ := pair_type_of_distance u v huv
  obtain ⟨c, hcY, huc, hvc⟩ := hc
  let D := removalDomain (G := G) Y
  have hconsistent : D.Consistent := by
    simpa [D] using removal_consistent G Y hY
  have hact : D.active = G \ Y := by
    simpa [D] using removal_active (G := G) Y hYG
  have huActive : u ∈ D.active := by
    rw [hact]
    exact hu
  have hvActive : v ∈ D.active := by
    rw [hact]
    exact hv
  have hcG : c ∈ G := hYG hcY
  have hcX : D.status c = Status.X := by
    simp [D, removalDomain, Finset.mem_sdiff, hcY]
  have huU : D.status u = Status.U := by
    have hu' : u ∈ G ∧ u ∉ Y := Finset.mem_sdiff.mp hu
    simp [D, removalDomain, hu']
  have hvU : D.status v = Status.U := by
    have hv' : v ∈ G ∧ v ∉ Y := Finset.mem_sdiff.mp hv
    simp [D, removalDomain, hv']
  have hpair : D.ResponsePair X u v c := by
    refine ⟨hconsistent, huActive, hvActive, hcG, hcX, huc, hvc, hX, ?_, ?_⟩
    · exact Or.inl huU
    · exact Or.inl hvU
  have hval :
      |pinnedExpectation G Y τ (fun n => dot (n u) (n v)) -
        freeExpectation G Y (fun n => dot (n u) (n v))| =
      |D.expectation τ true (fun n => dot (n u) (n v)) -
        D.expectation τ false (fun n => dot (n u) (n v))| := by
    rw [removal_pinned_expectation G Y τ hYG, removal_free_expectation G Y τ hYG]
  have hmem :
      |D.expectation τ true (fun n => dot (n u) (n v)) -
        D.expectation τ false (fun n => dot (n u) (n v))| ∈
      ({0} ∪ {r : ℝ | ∃ G : Finset Plane, ∃ τ : PinAssignment G,
        ∃ E : Network G, ∃ a b z : Plane, E.ResponsePair X a b z ∧
        ((d : ℕ∞) ≤ min (setDistance latticeDist a (↑(protectedSites G) : Set Plane))
          (setDistance latticeDist b (↑(protectedSites G) : Set Plane)) ∧
          r = |E.expectation τ true (fun n => dot (n a) (n b)) -
            E.expectation τ false (fun n => dot (n a) (n b))|)}) := by
    apply Set.mem_union_right
    refine ⟨G, τ, D, u, v, c, hpair, ?_, rfl⟩
    simpa [d, depth] using hdepthCast.le
  have henv := le_csSup (responseEnvelope_bddAbove X (d : ℤ)) hmem
  rw [← hval] at henv
  refine ⟨X, d, ?_, henv⟩
  simpa [d, depth] using hdepthCast.symm

end AKLT.W.REC083
