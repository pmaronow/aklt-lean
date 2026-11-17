module
public import AKLT.W.REC021.Disintegration

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC021

theorem one_add_dot_nonneg {a b : Vec3} (ha : normSq a ≤ 1) (hb : normSq b ≤ 1) :
    0 ≤ 1 + dot a b := by
  have h := dot_cauchy a b
  have hp := mul_le_mul ha hb (normSq_nonneg b) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith [sq_nonneg (dot a b + 1)]

theorem spins_ball {G : Finset Plane} (D : Network G) (σ : D.active → SpinLetter)
    (x : Plane) : normSq (D.spins σ x) ≤ 1 := by
  by_cases h : x ∈ D.active
  · simp only [Network.spins, dif_pos h]
    rcases spin_norm (σ ⟨x, h⟩) with h | h <;> rw [h] <;> norm_num
  · simp [Network.spins, h, normSq, dot]

theorem mem_internalBonds {G : Finset Plane} {x y : Plane} :
    (x, y) ∈ internalBonds G ↔ x ∈ G ∧ y ∈ G ∧ y ∈ positiveNeighbours x := by
  simp [internalBonds, Finset.mem_biUnion, Finset.mem_image, Prod.mk.injEq,
    and_left_comm, and_assoc]

theorem positiveNeighbours_asymm {x y : Plane} (h : y ∈ positiveNeighbours x) :
    x ∉ positiveNeighbours y := by
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton,
    Prod.ext_iff] at *
  omega

theorem bond_orientation {G : Finset Plane} (D : Network G) (e : Plane × Plane)
    (he : e ∈ D.bonds) : e.2 ∈ positiveNeighbours e.1 :=
  (mem_internalBonds.mp (Finset.mem_filter.mp he).1).2.2

theorem bond_ne {G : Finset Plane} (D : Network G) (e : Plane × Plane)
    (he : e ∈ D.bonds) : e.1 ≠ e.2 := by
  have h := bond_orientation D e he
  simp only [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton,
    Prod.ext_iff] at h
  intro hh
  have h1 := congrArg Prod.fst hh
  have h2 := congrArg Prod.snd hh
  omega

def incidentBonds {G : Finset Plane} (D : Network G) (x : Plane) : Finset (Plane × Plane) :=
  D.bonds.filter fun e => e.1 = x ∨ e.2 = x

def otherEnd (x : Plane) (e : Plane × Plane) : Plane := if e.1 = x then e.2 else e.1

theorem incident_other_mem {G : Finset Plane} (D : Network G) (x : Plane)
    (e : Plane × Plane) (he : e ∈ incidentBonds D x) :
    otherEnd x e ∈ D.presentNeighbours x := by
  obtain ⟨he, hx⟩ := Finset.mem_filter.mp he
  have hp := (Finset.mem_filter.mp he).2
  rw [Network.presentNeighbours, Finset.mem_filter]
  rcases hx with hx | hx
  · have hpr : D.Present x e.2 := by simpa [hx] using hp
    simpa [otherEnd, hx] using
      (show e.2 ∈ neighbours x ∧ D.Present x e.2 from
        ⟨(mem_neighbours_iff _ _).mpr hpr.2.2.1, hpr⟩)
  · have hh : e.1 ≠ x := by
      intro hh
      exact bond_ne D e he (hh.trans hx.symm)
    have hpr : D.Present x e.1 := by simpa [hx] using present_symm D hp
    simpa [otherEnd, hh] using
      (show e.1 ∈ neighbours x ∧ D.Present x e.1 from
        ⟨(mem_neighbours_iff _ _).mpr hpr.2.2.1, hpr⟩)

theorem incident_other_injective {G : Finset Plane} (D : Network G) (x : Plane) :
    Set.InjOn (otherEnd x) (↑(incidentBonds D x) : Set (Plane × Plane)) := by
  intro e he e' he' hh
  obtain ⟨he, hx⟩ := Finset.mem_filter.mp he
  obtain ⟨he', hx'⟩ := Finset.mem_filter.mp he'
  have hn := bond_ne D e he
  have hn' := bond_ne D e' he'
  have ho := bond_orientation D e he
  have ho' := bond_orientation D e' he'
  rcases hx with hx | hx <;> rcases hx' with hx' | hx'
  · simp only [otherEnd, hx, hx', ite_true] at hh
    exact Prod.ext (hx.trans hx'.symm) hh
  · have hnx : e'.1 ≠ x := by intro h; exact hn' (h.trans hx'.symm)
    simp only [otherEnd, hx, hnx, ite_true, ite_false] at hh
    have hc := positiveNeighbours_asymm ho
    apply False.elim
    apply hc
    simpa [hx, hx', hh] using ho'
  · have hnx : e.1 ≠ x := by intro h; exact hn (h.trans hx.symm)
    simp only [otherEnd, hx', hnx, ite_true, ite_false] at hh
    have hc := positiveNeighbours_asymm ho
    apply False.elim
    apply hc
    simpa [hx, hx', hh] using ho'
  · have hnx : e.1 ≠ x := by intro h; exact hn (h.trans hx.symm)
    have hnx' : e'.1 ≠ x := by intro h; exact hn' (h.trans hx'.symm)
    simp only [otherEnd, hnx, hnx', ite_false] at hh
    exact Prod.ext hh (hx.trans hx'.symm)

theorem incident_card_le {G : Finset Plane} (D : Network G) (x : Plane) :
    (incidentBonds D x).card ≤ (D.presentNeighbours x).card := by
  exact Finset.card_le_card_of_injOn (otherEnd x)
    (fun e he => incident_other_mem D x e he) (incident_other_injective D x)

theorem three_fields {κ : Type*} (S : Finset κ) (v : κ → Vec3) (hcard : S.card ≤ 3)
    (hball : ∀ j ∈ S, normSq (v j) ≤ 1) :
    ∃ a : Fin 3 → Vec3, (∀ i, normSq (a i) ≤ 1) ∧
      ∀ n : Vec3, (∏ j ∈ S, (1 + dot n (v j))) = cubicWeight (a 0) (a 1) (a 2) n := by
  classical
  interval_cases hc : S.card
  · have hs : S = ∅ := Finset.card_eq_zero.mp hc
    subst S
    refine ⟨fun _ => 0, ?_, ?_⟩
    · intro i; simp [normSq, dot]
    · intro n; simp [cubicWeight, dot]
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp hc
    refine ⟨![v a, 0, 0], ?_, ?_⟩
    · intro i; fin_cases i <;> simp [normSq, dot] <;> exact hball a (by simp)
    · intro n; simp [cubicWeight, dot]
  · obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hc
    refine ⟨![v a, v b, 0], ?_, ?_⟩
    · intro i; fin_cases i
      · exact hball a (by simp)
      · exact hball b (by simp)
      · simp [normSq, dot]
    · intro n; simp [cubicWeight, hab, dot]
  · obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hc
    refine ⟨![v a, v b, v c], ?_, ?_⟩
    · intro i; fin_cases i
      · exact hball a (by simp)
      · exact hball b (by simp)
      · exact hball c (by simp)
    · intro n; simp [cubicWeight, hab, hac, hbc, mul_assoc]

theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  simp only [dot, Fin.sum_univ_three]
  ring

def localBondProduct {G : Finset Plane} (D : Network G) (n : Plane → Vec3)
    (x : Plane) (v : Vec3) : ℝ :=
  ∏ e ∈ incidentBonds D x, (1 + dot v (n (otherEnd x e)))

def outsideBondProduct {G : Finset Plane} (D : Network G) (n : Plane → Vec3)
    (x : Fin 3 → Plane) : ℝ :=
  ∏ e ∈ D.bonds,
    if (e.1 ≠ x 0 ∧ e.1 ≠ x 1 ∧ e.1 ≠ x 2) ∧
       (e.2 ≠ x 0 ∧ e.2 ≠ x 1 ∧ e.2 ≠ x 2)
    then 1 + dot (n e.1) (n e.2) else 1

theorem three_bond_factorization {G : Finset Plane} (D : Network G) (n : Plane → Vec3)
    (x : Fin 3 → Plane) (hinj : Function.Injective x)
    (hnobond : ∀ e ∈ D.bonds, ∀ i j, ¬ (e.1 = x i ∧ e.2 = x j))
    (v : Fin 3 → Vec3) :
    (∏ e ∈ D.bonds, (1 + dot (blockUpdate x n v e.1) (blockUpdate x n v e.2))) =
      outsideBondProduct D n x * localBondProduct D n (x 0) (v 0) *
        localBondProduct D n (x 1) (v 1) * localBondProduct D n (x 2) (v 2) := by
  have hx01 : x 0 ≠ x 1 := hinj.ne (by decide)
  have hx02 : x 0 ≠ x 2 := hinj.ne (by decide)
  have hx12 : x 1 ≠ x 2 := hinj.ne (by decide)
  have he (e : Plane × Plane) (he : e ∈ D.bonds) :
      1 + dot (blockUpdate x n v e.1) (blockUpdate x n v e.2) =
      (if (e.1 ≠ x 0 ∧ e.1 ≠ x 1 ∧ e.1 ≠ x 2) ∧
          (e.2 ≠ x 0 ∧ e.2 ≠ x 1 ∧ e.2 ≠ x 2)
        then 1 + dot (n e.1) (n e.2) else 1) *
      (if e.1 = x 0 ∨ e.2 = x 0 then 1 + dot (v 0) (n (otherEnd (x 0) e)) else 1) *
      (if e.1 = x 1 ∨ e.2 = x 1 then 1 + dot (v 1) (n (otherEnd (x 1) e)) else 1) *
      (if e.1 = x 2 ∨ e.2 = x 2 then 1 + dot (v 2) (n (otherEnd (x 2) e)) else 1) := by
    have hno := hnobond e he
    simp only [Fin.forall_fin_succ, Fin.forall_fin_zero] at hno
    by_cases ha0 : e.1 = x 0 <;> by_cases ha1 : e.1 = x 1 <;>
      by_cases ha2 : e.1 = x 2 <;> by_cases hb0 : e.2 = x 0 <;>
      by_cases hb1 : e.2 = x 1 <;> by_cases hb2 : e.2 = x 2 <;>
      simp_all [blockUpdate, Function.update_apply, otherEnd, dot_comm]
  calc
    _ = ∏ e ∈ D.bonds,
      ((if (e.1 ≠ x 0 ∧ e.1 ≠ x 1 ∧ e.1 ≠ x 2) ∧
          (e.2 ≠ x 0 ∧ e.2 ≠ x 1 ∧ e.2 ≠ x 2)
        then 1 + dot (n e.1) (n e.2) else 1) *
      (if e.1 = x 0 ∨ e.2 = x 0 then 1 + dot (v 0) (n (otherEnd (x 0) e)) else 1) *
      (if e.1 = x 1 ∨ e.2 = x 1 then 1 + dot (v 1) (n (otherEnd (x 1) e)) else 1) *
      (if e.1 = x 2 ∨ e.2 = x 2 then 1 + dot (v 2) (n (otherEnd (x 2) e)) else 1)) :=
        Finset.prod_congr rfl he
    _ = _ := by
      simp only [Finset.prod_mul_distrib, outsideBondProduct, localBondProduct,
        incidentBonds, Finset.prod_filter]

theorem three_site_factorization {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
    (w : ι → Ω → ℝ) (x : Fin 3 → ι) (hinj : Function.Injective x)
    (σ : ι → Ω) (j : Fin 3 → Ω) :
    (∏ u, w u (blockUpdate x σ j u)) =
      (∏ u, if u = x 0 ∨ u = x 1 ∨ u = x 2 then 1 else w u (σ u)) *
        w (x 0) (j 0) * w (x 1) (j 1) * w (x 2) (j 2) := by
  have hx01 : x 0 ≠ x 1 := hinj.ne (by decide)
  have hx02 : x 0 ≠ x 2 := hinj.ne (by decide)
  have hx12 : x 1 ≠ x 2 := hinj.ne (by decide)
  have he (u : ι) : w u (blockUpdate x σ j u) =
      (if u = x 0 ∨ u = x 1 ∨ u = x 2 then 1 else w u (σ u)) *
      (if u = x 0 then w u (j 0) else 1) *
      (if u = x 1 then w u (j 1) else 1) *
      (if u = x 2 then w u (j 2) else 1) := by
    by_cases h0 : u = x 0 <;> by_cases h1 : u = x 1 <;> by_cases h2 : u = x 2 <;>
      simp_all [blockUpdate, Function.update_apply]
  calc
    _ = ∏ u,
      ((if u = x 0 ∨ u = x 1 ∨ u = x 2 then 1 else w u (σ u)) *
      (if u = x 0 then w u (j 0) else 1) *
      (if u = x 1 then w u (j 1) else 1) *
      (if u = x 2 then w u (j 2) else 1)) := Finset.prod_congr rfl (fun u _ => he u)
    _ = _ := by simp only [Finset.prod_mul_distrib, Fintype.prod_ite_eq']

end AKLT.W.REC021
