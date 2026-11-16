import AKLT.Blueprint.Rec.NodesResponse

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC001

theorem icoVector_unit (j : IcoLetter) : normSq (icoVector j) = 1 := by
  rcases j with ⟨a, b, c⟩
  have hphi : goldenRatio ^ 2 = goldenRatio + 1 := by
    unfold goldenRatio
    have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    nlinarith
  have hr : icoRadius ^ 2 = goldenRatio + 2 := by
    unfold icoRadius
    have hp : 0 ≤ goldenRatio + 2 := by
      unfold goldenRatio
      positivity
    rw [Real.sq_sqrt hp]
  have hr0 : icoRadius ≠ 0 := by
    apply ne_of_gt
    unfold icoRadius
    exact Real.sqrt_pos.2 (by unfold goldenRatio; positivity)
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [icoVector, signValue, normSq, dot, Fin.sum_univ_succ] <;>
    field_simp [hr0] <;> nlinarith [hphi, hr]

theorem normSq_nonneg_local (a : Vec3) : 0 ≤ normSq a := by
  change 0 ≤ ∑ i, a i * a i
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg (a i))

theorem normSq_add_nonneg (a b : Vec3) : 0 ≤ normSq (fun i => a i + b i) :=
  normSq_nonneg_local _

theorem normSq_add (a b : Vec3) :
    normSq (fun i => a i + b i) = normSq a + 2 * dot a b + normSq b := by
  unfold normSq dot
  calc
    (∑ i, (a i + b i) * (a i + b i)) =
        ∑ i, (a i * a i + 2 * (a i * b i) + b i * b i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = (∑ i, a i * a i) + 2 * (∑ i, a i * b i) + (∑ i, b i * b i) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
          rw [Finset.mul_sum]

theorem vec_eq_neg_of_unit_dot (a b : Vec3) (ha : normSq a = 1) (hb : normSq b ≤ 1)
    (hab : dot a b = -1) : a = -b := by
  have hsum : normSq (fun i => a i + b i) = 0 := by
    have hn := normSq_add_nonneg a b
    rw [normSq_add, ha, hab] at hn
    have hEq : normSq b = 1 := le_antisymm hb (by linarith)
    rw [normSq_add, ha, hab, hEq]
    norm_num
  funext i
  have hz : (a i + b i) * (a i + b i) = 0 := by
    have hterms : ∑ q : Fin 3, (a q + b q) * (a q + b q) = 0 := by
      simpa [normSq, dot] using hsum
    have hsingle := Finset.single_le_sum (s := Finset.univ)
      (f := fun q : Fin 3 => (a q + b q) * (a q + b q))
      (fun q hq => mul_self_nonneg (a q + b q)) (Finset.mem_univ i)
    rw [hterms] at hsingle
    nlinarith [sq_nonneg (a i + b i)]
  have heq : a i + b i = 0 := mul_self_eq_zero.mp hz
  change a i = -b i
  linarith [heq]

set_option maxHeartbeats 6000000 in
theorem ico_forbid_unique (b : Vec3) (hb : normSq b ≤ 1) {j k : IcoLetter}
    (hj : 1 + dot (icoVector j) b = 0) (hk : 1 + dot (icoVector k) b = 0) : j = k := by
  have hdotj : dot (icoVector j) b = -1 := by linarith
  have hdotk : dot (icoVector k) b = -1 := by linarith
  have hvec : icoVector j = -b :=
    vec_eq_neg_of_unit_dot (icoVector j) b (icoVector_unit j) hb hdotj
  have hkvec : icoVector k = -b :=
    vec_eq_neg_of_unit_dot (icoVector k) b (icoVector_unit k) hb hdotk
  have hv : icoVector j = icoVector k := hvec.trans hkvec.symm
  -- The finite explicit coordinate realization is injective.
  have hinj : Function.Injective icoVector := by
    intro x y hxy
    rcases x with ⟨x, x₁, x₂⟩
    rcases y with ⟨y, y₁, y₂⟩
    have hnz : goldenRatio ≠ 0 := ne_of_gt (by
      unfold goldenRatio
      positivity)
    have hφsq : goldenRatio ^ 2 = goldenRatio + 1 := by
      unfold goldenRatio
      have hs : (Real.sqrt 5) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
      nlinarith
    have hr0 : icoRadius ≠ 0 := by
      apply ne_of_gt
      unfold icoRadius
      exact Real.sqrt_pos.2 (by unfold goldenRatio; positivity)
    fin_cases x <;> fin_cases y
    all_goals
      fin_cases x₁ <;> fin_cases x₂ <;> fin_cases y₁ <;> fin_cases y₂
      all_goals
        have h0 := congrFun hxy (0 : Fin 3)
        have h1 := congrFun hxy (1 : Fin 3)
        have h2 := congrFun hxy (2 : Fin 3)
        simp [icoVector, signValue] at h0 h1 h2
        try field_simp [hr0] at h0
        try field_simp [hr0] at h1
        try field_simp [hr0] at h2
        all_goals
          first
          | rfl
          | (rcases h2 with hbad | hbad
             · have hz : goldenRatio = 0 := by linarith
               exact (hnz hz).elim
             · have hz : icoRadius = 0 := by linarith
               exact (hr0 hz).elim)
          | nlinarith [hnz, hr0, hφsq]
  exact hinj hv

theorem dotFactor_nonneg (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have hn := normSq_nonneg_local (fun i => a i + b i)
  rw [normSq_add] at hn
  nlinarith

theorem ico_letter_avoidance (k : ℕ) (b : Fin k → Vec3)
    (hk : k ≤ 4) (hb : ∀ i, normSq (b i) ≤ 1) :
    ∃ j : IcoLetter, ∀ i, 0 < 1 + dot (icoVector j) (b i) := by
  classical
  by_contra h
  push_neg at h
  let badIndex : IcoLetter → Fin k := fun j => Classical.choose (h j)
  have badIndex_spec (j : IcoLetter) :
      1 + dot (icoVector j) (b (badIndex j)) ≤ 0 := Classical.choose_spec (h j)
  have badZero (j : IcoLetter) : 1 + dot (icoVector j) (b (badIndex j)) = 0 := by
    have hlo := dotFactor_nonneg (icoVector j) (b (badIndex j))
      (le_of_eq (icoVector_unit j))
      (hb (badIndex j))
    have hhi := badIndex_spec j
    linarith
  have hinj : Function.Injective badIndex := by
    intro j j' heq
    apply ico_forbid_unique (b (badIndex j)) (hb (badIndex j)) (badZero j)
    simpa [heq] using badZero j'
  have hcard := Fintype.card_le_of_injective badIndex hinj
  have hcard' : 12 ≤ k := by simpa [IcoLetter] using hcard
  omega

theorem adjacent_mem_neighbours {x y : Plane} (h : Adjacent x y) : y ∈ neighbours x := by
  rcases x with ⟨x₁, x₂⟩
  rcases y with ⟨y₁, y₂⟩
  change (x₁ - y₁).natAbs + (x₂ - y₂).natAbs = 1 at h
  have hc : ((x₁ - y₁).natAbs : ℤ) + ((x₂ - y₂).natAbs : ℤ) = 1 := by exact_mod_cast h
  have go (d : Compass) (heq : (x₁, x₂) + d.step = (y₁, y₂)) :
      (y₁, y₂) ∈ neighbours (x₁, x₂) := by
    apply Finset.mem_image.mpr
    exact ⟨d, Finset.mem_univ _, heq⟩
  by_cases h₁ : x₁ ≤ y₁ <;> by_cases h₂ : x₂ ≤ y₂
  · rw [Int.ofNat_natAbs_of_nonpos (sub_nonpos.mpr h₁),
      Int.ofNat_natAbs_of_nonpos (sub_nonpos.mpr h₂)] at hc
    have hdir : (y₁ = x₁ + 1 ∧ y₂ = x₂) ∨ (y₁ = x₁ ∧ y₂ = x₂ + 1) := by omega
    rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply go .east
      apply Prod.ext <;> simp [Compass.step] <;> omega
    · apply go .north
      apply Prod.ext <;> simp [Compass.step] <;> omega
  · rw [Int.ofNat_natAbs_of_nonpos (sub_nonpos.mpr h₁),
      Int.natAbs_of_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h₂)))] at hc
    have hdir : (y₁ = x₁ + 1 ∧ y₂ = x₂) ∨ (y₁ = x₁ ∧ y₂ + 1 = x₂) := by omega
    rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply go .east
      apply Prod.ext <;> simp [Compass.step] <;> omega
    · apply go .south
      apply Prod.ext <;> simp [Compass.step] <;> omega
  · rw [Int.natAbs_of_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h₁))),
      Int.ofNat_natAbs_of_nonpos (sub_nonpos.mpr h₂)] at hc
    have hdir : (y₁ + 1 = x₁ ∧ y₂ = x₂) ∨ (y₁ = x₁ ∧ y₂ = x₂ + 1) := by omega
    rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply go .west
      apply Prod.ext <;> simp [Compass.step] <;> omega
    · apply go .north
      apply Prod.ext <;> simp [Compass.step] <;> omega
  · rw [Int.natAbs_of_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h₁))),
      Int.natAbs_of_nonneg (sub_nonneg.mpr (le_of_lt (lt_of_not_ge h₂)))] at hc
    have hdir : (y₁ + 1 = x₁ ∧ y₂ = x₂) ∨ (y₁ = x₁ ∧ y₂ + 1 = x₂) := by omega
    rcases hdir with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · apply go .west
      apply Prod.ext <;> simp [Compass.step] <;> omega
    · apply go .south
      apply Prod.ext <;> simp [Compass.step] <;> omega

theorem present_symm {G : Finset Plane} (D : Network G) {x y : Plane}
    (h : D.Present x y) : D.Present y x := by
  have hdist : latticeDist y x = latticeDist x y := by
    simp only [latticeDist]
    rw [show y.1 - x.1 = -(x.1 - y.1) by ring,
      show y.2 - x.2 = -(x.2 - y.2) by ring, Int.natAbs_neg, Int.natAbs_neg]
  refine ⟨h.2.1, h.1, ?_, h.2.2.2.2, h.2.2.2.1⟩
  change latticeDist y x = 1
  rw [hdist]
  exact h.2.2.1

def partialGood {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (S : Finset Plane) (σ : Plane → IcoLetter) : Prop :=
  (∀ x ∈ S, x ∈ D.active) ∧
  (∀ e ∈ D.bonds, e.1 ∈ S → e.2 ∈ S →
    0 < 1 + dot (icoVector (σ e.1)) (icoVector (σ e.2))) ∧
  ∀ e : originalLegs G, e.val.1 ∈ S →
    0 < 1 + dot (τ e).val (icoVector (σ e.val.1))

set_option maxHeartbeats 3000000 in
theorem exists_partialGood {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (hD : D.Auxiliary) : ∀ S : Finset Plane, S ⊆ D.active →
      ∃ σ : Plane → IcoLetter, partialGood D τ S σ := by
  classical
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro h
      refine ⟨fun _ => default, ?_⟩
      simp [partialGood]
  | @insert x S hx ih =>
      intro hsub
      have hsubOld : S ⊆ D.active := by
        intro y hy
        exact hsub (Finset.mem_insert_of_mem hy)
      obtain ⟨σ, hσ⟩ := ih hsubOld
      have hxActive : x ∈ D.active := hsub (Finset.mem_insert_self x S)
      let N : Finset Plane := (D.presentNeighbours x).filter fun y => y ∈ S
      let L : Finset (Plane × Plane) := (originalLegs G).filter fun e => e.1 = x
      let C := {y : Plane // y ∈ N} ⊕ {e : Plane × Plane // e ∈ L}
      have hN : N.card ≤ (D.presentNeighbours x).card := by
        exact Finset.card_le_card (Finset.filter_subset _ _)
      have hL : L.card = ((originalLegs G).filter fun e => e.1 = x).card := rfl
      have hdegree := hD.1.2.2.2 x hxActive
      have hCcard : Fintype.card C ≤ 4 := by
        have hcard : Fintype.card C = N.card + L.card := by simp [C]
        rw [hcard, hL]
        omega
      let ec : C ≃ Fin (Fintype.card C) := Fintype.equivFin C
      let cv : C → Vec3 := fun c => match c with
        | Sum.inl y => icoVector (σ y.val)
        | Sum.inr e => (τ ⟨e.val, (Finset.mem_filter.mp e.property).1⟩).val
      have hcv : ∀ c, normSq (cv c) ≤ 1 := by
        intro c
        cases c with
        | inl y => exact le_of_eq (icoVector_unit (σ y.val))
        | inr e => exact le_of_eq (τ ⟨e.val, (Finset.mem_filter.mp e.property).1⟩).property
      obtain ⟨ell, hell⟩ := ico_letter_avoidance (Fintype.card C)
        (fun i => cv (ec.symm i)) hCcard (fun i => hcv (ec.symm i))
      have hpositive (c : C) : 0 < 1 + dot (icoVector ell) (cv c) := by
        simpa [cv] using hell (ec c)
      let σ' : Plane → IcoLetter := Function.update σ x ell
      have hgood : partialGood D τ (insert x S) σ' := by
        refine ⟨?_, ?_, ?_⟩
        · intro y hy
          rcases Finset.mem_insert.mp hy with hyx | hyold
          · simpa [hyx] using hxActive
          · exact hσ.1 y hyold
        · intro e he he₁ he₂
          have hPresent : D.Present e.1 e.2 := by
            unfold Network.bonds at he
            exact (Finset.mem_filter.mp he).2
          rcases Finset.mem_insert.mp he₁ with he₁x | he₁old
          · rcases Finset.mem_insert.mp he₂ with he₂x | he₂old
            · have hadj := hPresent.2.2.1
              rw [he₁x, he₂x] at hadj
              simp [Adjacent, latticeDist] at hadj
            · have hmemN : e.2 ∈ N := by
                apply Finset.mem_filter.mpr
                refine ⟨Finset.mem_filter.mpr ?_, he₂old⟩
                have hpresent : D.Present x e.2 := by
                  have ht := hPresent
                  rw [he₁x] at ht
                  exact ht
                exact ⟨adjacent_mem_neighbours hpresent.2.2.1, hpresent⟩
              have hp := hpositive (Sum.inl ⟨e.2, hmemN⟩)
              simpa [σ', cv, Function.update, he₁x,
                (ne_of_mem_of_not_mem he₂old hx), dot, mul_comm] using hp
          · rcases Finset.mem_insert.mp he₂ with he₂x | he₂old
            · have hmemN : e.1 ∈ N := by
                apply Finset.mem_filter.mpr
                refine ⟨Finset.mem_filter.mpr ?_, he₁old⟩
                have hpresent : D.Present e.1 x := by
                  have ht := hPresent
                  rw [he₂x] at ht
                  exact ht
                have hpresent' := present_symm D hpresent
                exact ⟨adjacent_mem_neighbours hpresent'.2.2.1, hpresent'⟩
              have hp := hpositive (Sum.inl ⟨e.1, hmemN⟩)
              simpa [σ', cv, Function.update, he₂x,
                (ne_of_mem_of_not_mem he₁old hx), dot, mul_comm] using hp
            · have hne₁ : e.1 ≠ x := by
                intro heq
                have hold : x ∈ S := by simpa [heq] using he₁old
                exact hx hold
              have hne₂ : e.2 ≠ x := by
                intro heq
                have hold : x ∈ S := by simpa [heq] using he₂old
                exact hx hold
              simpa [σ', Function.update, hne₁, hne₂] using
                hσ.2.1 e he he₁old he₂old
        · intro e heTail
          rcases Finset.mem_insert.mp heTail with hetailx | hetailold
          · have hmemL : e.val ∈ L := Finset.mem_filter.mpr ⟨e.property, hetailx⟩
            have hp := hpositive (Sum.inr ⟨e.val, hmemL⟩)
            simpa [σ', cv, Function.update, hetailx, dot, mul_comm] using hp
          · have hne : e.val.1 ≠ x := by
              intro heq
              have hold : x ∈ S := by simpa [heq] using hetailold
              exact hx hold
            simpa [σ', Function.update, hne] using hσ.2.2 e hetailold
      exact ⟨σ', hgood⟩

theorem exists_positive_assignment {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (hD : D.Auxiliary) : ∃ σ : Plane → IcoLetter, partialGood D τ D.active σ := by
  classical
  exact exists_partialGood D τ hD D.active (by intro x hx; exact hx)

private theorem spinVector_normSq_le_one (j : SpinLetter) : normSq (spinVector j) ≤ 1 := by
  cases j with
  | none => norm_num [spinVector, normSq, dot]
  | some j => rw [spinVector, icoVector_unit j]

private theorem dotFactor_nonneg_local (a b : Vec3) (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have hs := normSq_nonneg_local (fun i => a i + b i)
  rw [normSq_add] at hs
  nlinarith

private theorem status_of_active {G : Finset Plane} (D : Network G) (x : D.active) :
    D.status x.val = .U ∨ D.status x.val = .D := by
  have hx : D.status x.val ≠ .X := (Finset.mem_filter.mp x.property).2
  cases h : D.status x.val <;> simp_all [Status]

private theorem spinWeight_nonneg_local (s : Status) (hs : s = .U ∨ s = .D)
    (j : SpinLetter) : 0 ≤ spinWeight s j := by
  rcases hs with rfl | rfl <;> cases j <;> norm_num [spinWeight]

private theorem spinWeight_ico_pos_local (s : Status) (hs : s = .U ∨ s = .D)
    (j : IcoLetter) : 0 < spinWeight s (some j) := by
  rcases hs with rfl | rfl <;> norm_num [spinWeight]

private theorem networkSpins_normSq_le_one {G : Finset Plane} (D : Network G)
    (n : (x : D.active) → SpinLetter) (x : Plane) : normSq (D.spins n x) ≤ 1 := by
  by_cases hx : x ∈ D.active
  · simp only [Network.spins, dif_pos hx]
    exact spinVector_normSq_le_one (n ⟨x, hx⟩)
  · simp only [Network.spins, dif_neg hx]
    norm_num [normSq, dot]

theorem main : AKLT.Blueprint.Rec.NetworkPositiveStatement := by
  classical
  intro G τ D hD pinned
  obtain ⟨σ, hgood⟩ := exists_positive_assignment D τ hD
  let n₀ : (x : D.active) → SpinLetter := fun x => some (σ x.val)
  have hspin (x : D.active) : D.spins n₀ x.val = icoVector (σ x.val) := by
    simp [Network.spins, n₀, x.property, spinVector]
  have hsites_pos : 0 < ∏ x : D.active, spinWeight (D.status x.val) (n₀ x) := by
    apply Finset.prod_pos
    intro x hx
    exact spinWeight_ico_pos_local (D.status x.val) (status_of_active D x) (σ x.val)
  -- State the site and edge product bounds independently of the pin flag.
  have hsites_nn (n : (x : D.active) → SpinLetter) :
      0 ≤ ∏ x : D.active, spinWeight (D.status x.val) (n x) := by
    apply Finset.prod_nonneg
    intro x hx
    exact spinWeight_nonneg_local (D.status x.val) (status_of_active D x) (n x)
  have hbonds_nn (n : (x : D.active) → SpinLetter) :
      0 ≤ ∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2)) := by
    apply Finset.prod_nonneg
    intro e he
    exact dotFactor_nonneg_local _ _ (networkSpins_normSq_le_one D n e.1)
      (networkSpins_normSq_le_one D n e.2)
  have hlegs_nn (n : (x : D.active) → SpinLetter) :
      0 ≤ ∏ e : originalLegs G,
        if pinned = true ∧ e.val.1 ∈ D.active then
          1 + dot (τ e).val (D.spins n e.val.1) else 1 := by
    apply Finset.prod_nonneg
    intro e he
    by_cases hp : pinned = true ∧ e.val.1 ∈ D.active
    · simpa [hp] using dotFactor_nonneg_local _ _ (le_of_eq (τ e).property)
        (networkSpins_normSq_le_one D n e.val.1)
    · simp [hp]
  have hterm_nn (n : (x : D.active) → SpinLetter) :
      0 ≤ (∏ x : D.active, spinWeight (D.status x.val) (n x)) * 1 *
        (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
        ∏ e : originalLegs G,
          if pinned = true ∧ e.val.1 ∈ D.active then
            1 + dot (τ e).val (D.spins n e.val.1) else 1 := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (hsites_nn n) (by norm_num))
      (hbonds_nn n)) (hlegs_nn n)
  have hbonds_pos : 0 < ∏ e ∈ D.bonds,
      (1 + dot (D.spins n₀ e.1) (D.spins n₀ e.2)) := by
    apply Finset.prod_pos
    intro e he
    have hpresent : D.Present e.1 e.2 := (Finset.mem_filter.mp he).2
    have h := hgood.2.1 e he hpresent.1 hpresent.2.1
    have hleft : D.spins n₀ e.1 = icoVector (σ e.1) := hspin ⟨e.1, hpresent.1⟩
    have hright : D.spins n₀ e.2 = icoVector (σ e.2) := hspin ⟨e.2, hpresent.2.1⟩
    rw [hleft, hright]
    exact h
  have hlegs_pos : 0 < ∏ e : originalLegs G,
      if pinned = true ∧ e.val.1 ∈ D.active then
        1 + dot (τ e).val (D.spins n₀ e.val.1) else 1 := by
    apply Finset.prod_pos
    intro e he
    by_cases hp : pinned = true ∧ e.val.1 ∈ D.active
    · have h := hgood.2.2 e hp.2
      have hv : D.spins n₀ e.val.1 = icoVector (σ e.val.1) := hspin ⟨e.val.1, hp.2⟩
      rw [if_pos hp, hv]
      exact h
    · simp [hp]
  have hterm_pos : 0 < (∏ x : D.active, spinWeight (D.status x.val) (n₀ x)) * 1 *
      (∏ e ∈ D.bonds, (1 + dot (D.spins n₀ e.1) (D.spins n₀ e.2))) *
      ∏ e : originalLegs G,
        if pinned = true ∧ e.val.1 ∈ D.active then
          1 + dot (τ e).val (D.spins n₀ e.val.1) else 1 := by
    refine mul_pos (mul_pos (mul_pos hsites_pos (by norm_num)) hbonds_pos) hlegs_pos
  unfold Network.partition
  have hsum : 0 < ∑ n : (x : D.active) → SpinLetter,
      (∏ x : D.active, spinWeight (D.status x.val) (n x)) * 1 *
        (∏ e ∈ D.bonds, (1 + dot (D.spins n e.1) (D.spins n e.2))) *
        ∏ e : originalLegs G,
          if pinned = true ∧ e.val.1 ∈ D.active then
            1 + dot (τ e).val (D.spins n e.val.1) else 1 :=
    Finset.sum_pos' (fun n hn => hterm_nn n)
      ⟨n₀, Finset.mem_univ _, hterm_pos⟩
  simpa using hsum

end AKLT.W.REC001

#print axioms AKLT.W.REC001.icoVector_unit
#print axioms AKLT.W.REC001.normSq_nonneg_local
#print axioms AKLT.W.REC001.normSq_add_nonneg
#print axioms AKLT.W.REC001.normSq_add
#print axioms AKLT.W.REC001.vec_eq_neg_of_unit_dot
#print axioms AKLT.W.REC001.ico_forbid_unique
#print axioms AKLT.W.REC001.dotFactor_nonneg
#print axioms AKLT.W.REC001.ico_letter_avoidance
#print axioms AKLT.W.REC001.adjacent_mem_neighbours
#print axioms AKLT.W.REC001.present_symm
#print axioms AKLT.W.REC001.exists_partialGood
#print axioms AKLT.W.REC001.exists_positive_assignment
#print axioms AKLT.W.REC001.main
