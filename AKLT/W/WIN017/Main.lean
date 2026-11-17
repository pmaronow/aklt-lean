module
public import AKLT.Blueprint.Win.NodesTopology

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.WIN017

open AKLT.Blueprint.Win

private def vertical (c : EdgeChain) (i j : ℤ) : ZMod 2 := c s((i, j), (i, j + 1))

private def incidentEdges (x : Plane) : Finset LatticeEdge :=
  {s(x, (x.1 + 1, x.2)), s(x, (x.1 - 1, x.2)),
    s(x, (x.1, x.2 + 1)), s(x, (x.1, x.2 - 1))}

private lemma sym2_sameStart_ne {x y z : Plane} (hyz : y ≠ z) : s(x, y) ≠ s(x, z) := by
  intro he
  rcases Sym2.eq_iff.mp he with ⟨_, hyz'⟩ | ⟨hxz, hyx⟩
  · exact hyz hyz'
  · exact hyz (hyx.trans hxz)

private lemma zmod2_add_eq_zero {a b : ZMod 2} (h : a + b = 0) : a = b := by
  have h' := add_eq_zero_iff_eq_neg.mp h
  rw [CharTwo.neg_eq] at h'
  exact h'

private lemma sum_incidentEdges (c : EdgeChain) (x : Plane) :
    (∑ e ∈ incidentEdges x, c e) =
      c s(x, (x.1 + 1, x.2)) +
        (c s(x, (x.1 - 1, x.2)) +
          (c s(x, (x.1, x.2 + 1)) + c s(x, (x.1, x.2 - 1)))) := by
  classical
  let e1 := s(x, (x.1 + 1, x.2))
  let e2 := s(x, (x.1 - 1, x.2))
  let e3 := s(x, (x.1, x.2 + 1))
  let e4 := s(x, (x.1, x.2 - 1))
  have hd12 : e1 ≠ e2 := sym2_sameStart_ne (by
    intro h
    have := congrArg Prod.fst h
    omega)
  have hd13 : e1 ≠ e3 := sym2_sameStart_ne (by
    intro h
    have := congrArg Prod.fst h
    omega)
  have hd14 : e1 ≠ e4 := sym2_sameStart_ne (by
    intro h
    have := congrArg Prod.fst h
    omega)
  have hd23 : e2 ≠ e3 := sym2_sameStart_ne (by
    intro h
    have := congrArg Prod.fst h
    omega)
  have hd24 : e2 ≠ e4 := sym2_sameStart_ne (by
    intro h
    have := congrArg Prod.fst h
    omega)
  have hd34 : e3 ≠ e4 := sym2_sameStart_ne (by
    intro h
    have := congrArg Prod.snd h
    omega)
  have h1 : e1 ∉ ({e2, e3, e4} : Finset LatticeEdge) := by simp [Finset.mem_insert, hd12, hd13, hd14]
  have h2 : e2 ∉ ({e3, e4} : Finset LatticeEdge) := by simp [Finset.mem_insert, hd23, hd24]
  have h3 : e3 ∉ ({e4} : Finset LatticeEdge) := by simp [hd34]
  change (∑ e ∈ insert e1 (insert e2 (insert e3 {e4})), c e) = _
  rw [Finset.sum_insert h1, Finset.sum_insert h2, Finset.sum_insert h3,
    Finset.sum_singleton]

private lemma adjacent_four (x y : Plane) (h : Adjacent x y) :
    y = (x.1 + 1, x.2) ∨ y = (x.1 - 1, x.2) ∨
      y = (x.1, x.2 + 1) ∨ y = (x.1, x.2 - 1) := by
  rcases x with ⟨x1, x2⟩
  rcases y with ⟨y1, y2⟩
  simp only [Adjacent, latticeDist, Prod.mk.injEq] at h ⊢
  have hx : (x1 - y1).natAbs = 0 ∨ (x1 - y1).natAbs = 1 := by omega
  have hy : (x2 - y2).natAbs = 0 ∨ (x2 - y2).natAbs = 1 := by omega
  rcases hx with hx | hx <;> rcases hy with hy | hy
  · have hx' : x1 - y1 = 0 := (Int.natAbs_eq_zero).mp hx
    have hy' : x2 - y2 = 0 := (Int.natAbs_eq_zero).mp hy
    omega
  · have hx' : x1 - y1 = 0 := (Int.natAbs_eq_zero).mp hx
    rcases (Int.natAbs_eq_iff.mp hy) with hy' | hy'
    · omega
    · omega
  · rcases (Int.natAbs_eq_iff.mp hx) with hx' | hx'
    · have hy' : x2 - y2 = 0 := (Int.natAbs_eq_zero).mp hy
      omega
    · have hy' : x2 - y2 = 0 := (Int.natAbs_eq_zero).mp hy
      omega
  · have hx' : (x1 - y1).natAbs = 1 := hx
    have hy' : (x2 - y2).natAbs = 1 := hy
    omega

private lemma support_incident_mem (c : EdgeChain) (hNN : ChainNN c) (x : Plane)
    (e : LatticeEdge) (he : e ∈ c.support) (hx : x ∈ e) : e ∈ incidentEdges x := by
  obtain ⟨a, b, hab, hadj⟩ := hNN e he
  rw [hab] at hx
  rcases Sym2.mem_iff.mp hx with hxa | hxb
  · subst a
    rcases adjacent_four x b hadj with h | h | h | h <;> subst b <;>
      simp [incidentEdges, hab]
  · subst b
    have hadj' : Adjacent x a := metricFacts.2.2.1 a x hadj
    rcases adjacent_four x a hadj' with h | h | h | h <;> subst a <;>
      simp [incidentEdges, Sym2.eq_swap, hab]

private lemma coeff_zero_nonadjacent (c : EdgeChain) (hNN : ChainNN c)
    (x y : Plane) (h : ¬ Adjacent x y) : c s(x, y) = 0 := by
  by_contra hc
  have he : s(x, y) ∈ c.support := Finsupp.mem_support_iff.mpr hc
  obtain ⟨a, b, hab, hadj⟩ := hNN _ he
  have hab' : s(x, y) = s(a, b) := hab
  rcases Sym2.eq_iff.mp hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h hadj
  · exact h (metricFacts.2.2.1 _ _ hadj)

private lemma horizontal_zero_outside (c : EdgeChain) (R : ℤ)
    (hbox : ChainInBox c R) (i j : ℤ)
    (hj : j ∉ Finset.Icc (-R) R) : horizontal c i j = 0 := by
  unfold horizontal
  by_contra hc
  have he : s((i, j), (i + 1, j)) ∈ c.support := Finsupp.mem_support_iff.mpr hc
  have hb := hbox _ he (i, j) (Sym2.mem_iff.mpr (Or.inl rfl))
  have hb' := abs_le.mp hb.2
  have hji : j ∈ Finset.Icc (-R) R := by
    simp only [Finset.mem_Icc]
    omega
  exact hj hji

private lemma vertical_zero_outside (c : EdgeChain) (R : ℤ)
    (hbox : ChainInBox c R) (i j : ℤ)
    (hj : j < -R ∨ R ≤ j) : vertical c i j = 0 := by
  unfold vertical
  by_contra hc
  have he : s((i, j), (i, j + 1)) ∈ c.support := Finsupp.mem_support_iff.mpr hc
  have hb₁ := hbox _ he (i, j) (Sym2.mem_iff.mpr (Or.inl rfl))
  have hb₂ := hbox _ he (i, j + 1) (Sym2.mem_iff.mpr (Or.inr rfl))
  have hb₁' := abs_le.mp hb₁.2
  have hb₂' := abs_le.mp hb₂.2
  rcases hj with hj | hj <;> omega

private lemma even_local (c : EdgeChain) (hNN : ChainNN c) (hEven : ChainEven c)
    (i j : ℤ) :
    horizontal c (i - 1) j + horizontal c i j + vertical c i (j - 1) + vertical c i j = 0 := by
  classical
  let x : Plane := (i, j)
  let T : Finset LatticeEdge := c.support.filter fun e => x ∈ e
  have hTsub : T ⊆ incidentEdges x := by
    intro e he
    exact support_incident_mem c hNN x e (Finset.mem_filter.mp he).1 (Finset.mem_filter.mp he).2
  have hTzero : ∀ e ∈ incidentEdges x, e ∉ T → c e = 0 := by
    intro e he hnot
    have hx : x ∈ e := by
      simp only [incidentEdges, Finset.mem_insert, Finset.mem_singleton] at he
      rcases he with h | h | h | h <;> rw [h] <;>
        exact Sym2.mem_iff.mpr (Or.inl rfl)
    have hnotSupport : e ∉ c.support := by
      intro hs
      exact hnot (Finset.mem_filter.mpr ⟨hs, hx⟩)
    by_contra hc
    exact hnotSupport (Finsupp.mem_support_iff.mpr hc)
  have hevenx := hEven x
  rw [← Finset.sum_filter] at hevenx
  rw [Finset.sum_subset hTsub hTzero] at hevenx
  have hsum' :
      c s(x, (x.1 + 1, x.2)) +
        (c s(x, (x.1 - 1, x.2)) +
          (c s(x, (x.1, x.2 + 1)) + c s(x, (x.1, x.2 - 1)))) = 0 := by
    rw [sum_incidentEdges] at hevenx
    exact hevenx
  simp only [x] at hsum'
  simp only [horizontal, vertical, Sym2.eq_swap, Int.sub_add_cancel]
  linear_combination hsum'

private lemma plaquette_horizontal_coeff (i j p q : ℤ) :
    plaquette (p, q) s((i, j), (i + 1, j)) =
      (if (p, q) = (i, j) then 1 else 0) +
        (if (p, q) = (i, j - 1) then 1 else 0) := by
  simp_all [plaquette, edge, Finsupp.single_apply, Prod.mk.injEq]
  split_ifs <;> norm_num <;> omega

private lemma plaquette_vertical_coeff (i j p q : ℤ) :
    plaquette (p, q) s((i, j), (i, j + 1)) =
      (if (p, q) = (i - 1, j) then 1 else 0) +
        (if (p, q) = (i, j) then 1 else 0) := by
  simp_all [plaquette, edge, Finsupp.single_apply, Prod.mk.injEq]
  split_ifs <;> norm_num <;> omega


private lemma plaquette_horizontal_coeff_plane (i j : ℤ) (p : Plane) :
    plaquette p s((i, j), (i + 1, j)) =
      (if p = (i, j) then 1 else 0) +
        (if p = (i, j - 1) then 1 else 0) := by
  rcases p with ⟨p, q⟩
  exact plaquette_horizontal_coeff i j p q

private lemma plaquette_vertical_coeff_plane (i j : ℤ) (p : Plane) :
    plaquette p s((i, j), (i, j + 1)) =
      (if p = (i - 1, j) then 1 else 0) +
        (if p = (i, j) then 1 else 0) := by
  rcases p with ⟨p, q⟩
  exact plaquette_vertical_coeff i j p q

private lemma plaquetteSum_horizontal (c : EdgeChain) (R : ℤ) (P : Finset Plane)
    (hP : ∀ p : Plane, p ∉ P → tailCoefficient c R p.1 p.2 = 0) (i j : ℤ) :
    (∑ p ∈ P, tailCoefficient c R p.1 p.2 • plaquette p) s((i, j), (i + 1, j)) =
      tailCoefficient c R i j + tailCoefficient c R i (j - 1) := by
  classical
  change (Finsupp.lapply (s((i, j), (i + 1, j))) : EdgeChain →ₗ[ZMod 2] ZMod 2)
    (∑ p ∈ P, tailCoefficient c R p.1 p.2 • plaquette p) = _
  rw [map_sum]
  simp only [Finsupp.lapply_apply, Finsupp.smul_apply, plaquette_horizontal_coeff_plane, smul_eq_mul]
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  by_cases h₁ : (i, j) ∈ P
  · by_cases h₂ : (i, j - 1) ∈ P
    · simp [h₁, h₂]
    · have hz₂ : tailCoefficient c R i (j - 1) = 0 := hP (i, j - 1) h₂
      simp [h₁, h₂, hz₂]
  · have hz₁ : tailCoefficient c R i j = 0 := hP (i, j) h₁
    by_cases h₂ : (i, j - 1) ∈ P
    · simp [h₁, h₂, hz₁]
    · have hz₂ : tailCoefficient c R i (j - 1) = 0 := hP (i, j - 1) h₂
      simp [h₁, h₂, hz₁, hz₂]

private lemma plaquetteSum_vertical (c : EdgeChain) (R : ℤ) (P : Finset Plane)
    (hP : ∀ p : Plane, p ∉ P → tailCoefficient c R p.1 p.2 = 0) (i j : ℤ) :
    (∑ p ∈ P, tailCoefficient c R p.1 p.2 • plaquette p) s((i, j), (i, j + 1)) =
      tailCoefficient c R (i - 1) j + tailCoefficient c R i j := by
  classical
  change (Finsupp.lapply (s((i, j), (i, j + 1))) : EdgeChain →ₗ[ZMod 2] ZMod 2)
    (∑ p ∈ P, tailCoefficient c R p.1 p.2 • plaquette p) = _
  rw [map_sum]
  simp only [Finsupp.lapply_apply, Finsupp.smul_apply, plaquette_vertical_coeff_plane, smul_eq_mul]
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
  by_cases h₁ : (i - 1, j) ∈ P
  · by_cases h₂ : (i, j) ∈ P
    · simp [h₁, h₂]
    · have hz₂ : tailCoefficient c R i j = 0 := hP (i, j) h₂
      simp [h₁, h₂, hz₂]
  · have hz₁ : tailCoefficient c R (i - 1) j = 0 := hP (i - 1, j) h₁
    by_cases h₂ : (i, j) ∈ P
    · simp [h₁, h₂, hz₁]
    · have hz₂ : tailCoefficient c R i j = 0 := hP (i, j) h₂
      simp [h₁, h₂, hz₁, hz₂]

private lemma telescopeZ2 (v : ℤ → ZMod 2) (a : ℤ) (n : ℕ) :
    (∑ k ∈ Finset.range n,
      (v (a + (k : ℤ)) + v (a + (k : ℤ) + 1))) =
      v a + v (a + (n : ℤ)) := by
  induction n with
  | zero => simp [CharTwo.add_self_eq_zero]
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    norm_cast
    simp only [Nat.cast_succ]
    have ht : v (a + (n : ℤ)) + v (a + (n : ℤ)) = 0 := CharTwo.add_self_eq_zero _
    calc
      v a + v (a + (n : ℤ)) + (v (a + (n : ℤ)) + v (a + (n : ℤ) + 1))
          = v a + (v (a + (n : ℤ)) + v (a + (n : ℤ))) + v (a + (n : ℤ) + 1) := by ac_rfl
      _ = v a + 0 + v (a + (n : ℤ) + 1) := by rw [ht]
      _ = v a + v (a + (n : ℤ) + 1) := by simp
      _ = v a + v (a + (↑n + 1)) := by congr 2; ring

private lemma sumIccEqRange (a b : ℤ) (hab : a ≤ b) (f : ℤ → ZMod 2) :
    (∑ r ∈ Finset.Icc a b, f r) =
      ∑ k ∈ Finset.range (b - a + 1).toNat, f (a + (k : ℤ)) := by
  classical
  let n : ℕ := (b - a + 1).toNat
  have hn : (n : ℤ) = b - a + 1 := by
    dsimp [n]
    rw [Int.toNat_of_nonneg (by omega)]
  symm
  refine Finset.sum_bij (fun k hk => a + (k : ℤ)) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc, Finset.mem_range] at *
    constructor <;> omega
  · intro k hk k' hk' heq
    omega
  · intro r hr
    simp only [Finset.mem_Icc] at hr
    refine ⟨(r - a).toNat, ?_, ?_⟩
    · simp only [Finset.mem_range]
      exact (Int.toNat_lt_toNat (m := b - a + 1) (by omega)).2 (by omega)
    · have hcast : ((r - a).toNat : ℤ) = r - a := Int.toNat_of_nonneg (by omega)
      rw [hcast]
      omega
  · intro k hk
    rfl

private lemma tailHorizontalRecurrence (c : EdgeChain) (R : ℤ)
    (hbox : ChainInBox c R) (i j : ℤ) :
    tailCoefficient c R i j + tailCoefficient c R i (j - 1) = horizontal c i j := by
  unfold tailCoefficient
  rw [← Finset.sum_add_distrib]
  have hterm : ∀ r ∈ Finset.Icc (-R) R,
      (if j < r then horizontal c i r else 0) +
        (if j - 1 < r then horizontal c i r else 0) =
      if r = j then horizontal c i j else 0 := by
    intro r hr
    by_cases hjr : j < r
    · have hprev : j - 1 < r := by omega
      have hrj : r ≠ j := by omega
      simp [hjr, hprev, hrj, CharTwo.add_self_eq_zero]
    · by_cases hprev : j - 1 < r
      · have hrj : r = j := by omega
        subst r
        simp [hprev]
      · have hrj : r ≠ j := by omega
        simp [hjr, hprev, hrj]
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_ite_eq']
  by_cases hj : j ∈ Finset.Icc (-R) R
  · simp [hj]
  · simp [hj]
    exact (horizontal_zero_outside c R hbox i j hj).symm

private lemma tail_eq_Icc (c : EdgeChain) (R i j : ℤ) (hlo : -R ≤ j) :
    tailCoefficient c R i j =
      ∑ r ∈ Finset.Icc (j + 1) R, horizontal c i r := by
  classical
  unfold tailCoefficient
  have hsub : Finset.Icc (j + 1) R ⊆ Finset.Icc (-R) R := by
    intro r hr
    simp only [Finset.mem_Icc] at hr ⊢
    omega
  have hout : ∀ r ∈ Finset.Icc (-R) R, r ∉ Finset.Icc (j + 1) R →
      (if j < r then horizontal c i r else 0) = 0 := by
    intro r hr hnot
    simp only [Finset.mem_Icc] at hr
    by_cases hjr : j < r
    · have hmem : r ∈ Finset.Icc (j + 1) R := by
        simp only [Finset.mem_Icc]
        omega
      exact (hnot hmem).elim
    · simp [hjr]
  calc
    (∑ r ∈ Finset.Icc (-R) R, if j < r then horizontal c i r else 0) =
        ∑ r ∈ Finset.Icc (j + 1) R, if j < r then horizontal c i r else 0 :=
      (Finset.sum_subset hsub hout).symm
    _ = ∑ r ∈ Finset.Icc (j + 1) R, horizontal c i r := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_Icc] at hr
      have hlt : j < r := by omega
      simp [hlt]

private lemma tailVerticalRecurrence (c : EdgeChain) (R : ℤ)
    (hNN : ChainNN c) (hEven : ChainEven c) (hbox : ChainInBox c R)
    (hflux : ∀ i : ℤ, ∑ r ∈ Finset.Icc (-R) R, horizontal c i r = 0)
    (i j : ℤ) :
    tailCoefficient c R (i - 1) j + tailCoefficient c R i j = vertical c i j := by
  by_cases hlo : j < -R
  · have ht (k : ℤ) : tailCoefficient c R k j =
        ∑ r ∈ Finset.Icc (-R) R, horizontal c k r := by
      unfold tailCoefficient
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_Icc] at hr
      have hlt : j < r := by omega
      simp [hlt]
    have hv := vertical_zero_outside c R hbox i j (Or.inl hlo)
    rw [ht (i - 1), ht i, hflux (i - 1), hflux i, hv]
    simp
  · by_cases hhi : R ≤ j
    · have ht (k : ℤ) : tailCoefficient c R k j = 0 := by
        unfold tailCoefficient
        apply Finset.sum_eq_zero
        intro r hr
        simp only [Finset.mem_Icc] at hr
        have hnot : ¬ j < r := by omega
        simp [hnot]
      have hv := vertical_zero_outside c R hbox i j (Or.inr hhi)
      rw [ht (i - 1), ht i, hv]
      simp
    · have hlo' : -R ≤ j := by omega
      have hhi' : j < R := by omega
      have ht₁ := tail_eq_Icc c R (i - 1) j hlo'
      have ht₂ := tail_eq_Icc c R i j hlo'
      have hlen : R - (j + 1) + 1 = R - j := by omega
      have hend : j + ((R - j).toNat : ℤ) = R := by
        rw [Int.toNat_of_nonneg (by omega)]
        omega
      have htop : vertical c i R = 0 :=
        vertical_zero_outside c R hbox i R (Or.inr (show R ≤ R from le_rfl))
      calc
        tailCoefficient c R (i - 1) j + tailCoefficient c R i j =
            ∑ r ∈ Finset.Icc (j + 1) R,
              (horizontal c (i - 1) r + horizontal c i r) := by
                rw [ht₁, ht₂, ← Finset.sum_add_distrib]
        _ = ∑ k ∈ Finset.range (R - j).toNat,
              (horizontal c (i - 1) (j + 1 + (k : ℤ)) +
                horizontal c i (j + 1 + (k : ℤ))) := by
                rw [sumIccEqRange (j + 1) R (by omega)]
                rw [hlen]
        _ = ∑ k ∈ Finset.range (R - j).toNat,
              (vertical c i (j + (k : ℤ)) + vertical c i (j + (k : ℤ) + 1)) := by
                apply Finset.sum_congr rfl
                intro k hk
                have he := even_local c hNN hEven i (j + 1 + (k : ℤ))
                have hprev : (j + 1 + (k : ℤ)) - 1 = j + (k : ℤ) := by omega
                have hnext : j + 1 + (k : ℤ) = j + (k : ℤ) + 1 := by omega
                rw [hprev, hnext] at he
                rw [hnext]
                have hpair :
                    (horizontal c (i - 1) (j + (k : ℤ) + 1) +
                      horizontal c i (j + (k : ℤ) + 1)) +
                    (vertical c i (j + (k : ℤ)) + vertical c i (j + (k : ℤ) + 1)) = 0 := by
                  simpa [add_assoc] using he
                exact zmod2_add_eq_zero hpair
        _ = vertical c i j + vertical c i R := by
              rw [telescopeZ2, hend]
        _ = vertical c i j := by rw [htop]; simp

private lemma horizontalReconstructionAt (c : EdgeChain) (R : ℤ) (P : Finset Plane)
    (hbox : ChainInBox c R)
    (hP : ∀ p : Plane, p ∉ P → tailCoefficient c R p.1 p.2 = 0)
    (i j : ℤ) :
    c s((i, j), (i + 1, j)) =
      (∑ p ∈ P, tailCoefficient c R p.1 p.2 • plaquette p) s((i, j), (i + 1, j)) := by
  rw [plaquetteSum_horizontal c R P hP i j]
  exact (tailHorizontalRecurrence c R hbox i j).symm

private lemma verticalReconstructionAt (c : EdgeChain) (R : ℤ) (P : Finset Plane)
    (hNN : ChainNN c) (hEven : ChainEven c) (hbox : ChainInBox c R)
    (hflux : ∀ i : ℤ, ∑ r ∈ Finset.Icc (-R) R, horizontal c i r = 0)
    (hP : ∀ p : Plane, p ∉ P → tailCoefficient c R p.1 p.2 = 0)
    (i j : ℤ) :
    c s((i, j), (i, j + 1)) =
      (∑ p ∈ P, tailCoefficient c R p.1 p.2 • plaquette p) s((i, j), (i, j + 1)) := by
  rw [plaquetteSum_vertical c R P hP i j]
  exact (tailVerticalRecurrence c R hNN hEven hbox hflux i j).symm

private lemma adjacent_of_sym2_eq {x y a b : Plane} (he : s(x, y) = s(a, b))
    (hab : Adjacent a b) : Adjacent x y := by
  rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hab
  · exact metricFacts.2.2.1 _ _ hab

private lemma edgeCoeff_zero_nonadjacent (x y a b : Plane) (hn : ¬ Adjacent x y)
    (hab : Adjacent a b) : (edge a b) s(x, y) = 0 := by
  unfold edge
  rw [Finsupp.single_apply]
  split_ifs with he
  · exact (hn (adjacent_of_sym2_eq he.symm hab)).elim
  · rfl

private lemma plaquetteCoeff_zero_nonadjacent (p x y : Plane) (hn : ¬ Adjacent x y) :
    (plaquette p) s(x, y) = 0 := by
  have h₁ : Adjacent p (p + (1, 0)) := by
    simp [Adjacent, latticeDist]
  have h₂ : Adjacent (p + (1, 0)) (p + (1, 1)) := by
    simp [Adjacent, latticeDist]
  have h₃ : Adjacent (p + (1, 1)) (p + (0, 1)) := by
    simp [Adjacent, latticeDist]
  have h₄ : Adjacent (p + (0, 1)) p := by
    simp [Adjacent, latticeDist]
  unfold plaquette
  simp only [Finsupp.add_apply]
  rw [edgeCoeff_zero_nonadjacent x y p (p + (1, 0)) hn h₁,
      edgeCoeff_zero_nonadjacent x y (p + (1, 0)) (p + (1, 1)) hn h₂,
      edgeCoeff_zero_nonadjacent x y (p + (1, 1)) (p + (0, 1)) hn h₃,
      edgeCoeff_zero_nonadjacent x y (p + (0, 1)) p hn h₄]
  simp

theorem main : PlaquetteReconstructionStatement := by
  intro c hNN hEven R hR hbox hflux P hP
  apply Finsupp.ext
  intro e
  refine Sym2.inductionOn e ?_
  intro x y
  by_cases hadj : Adjacent x y
  · rcases adjacent_four x y hadj with he | hw | hn | hs
    · subst y
      exact horizontalReconstructionAt c R P hbox hP x.1 x.2
    · subst y
      have hs : s(x, (x.1 - 1, x.2)) = s((x.1 - 1, x.2), x) := Sym2.eq_swap
      rw [hs]
      simpa [Int.sub_add_cancel] using
        horizontalReconstructionAt c R P hbox hP (x.1 - 1) x.2
    · subst y
      exact verticalReconstructionAt c R P hNN hEven hbox hflux hP x.1 x.2
    · subst y
      have hs : s(x, (x.1, x.2 - 1)) = s((x.1, x.2 - 1), x) := Sym2.eq_swap
      rw [hs]
      simpa [Int.sub_add_cancel] using
        verticalReconstructionAt c R P hNN hEven hbox hflux hP x.1 (x.2 - 1)
  · have hc : c s(x, y) = 0 := coeff_zero_nonadjacent c hNN x y hadj
    have hp :
        (∑ p ∈ P, tailCoefficient c R p.1 p.2 • plaquette p) s(x, y) = 0 := by
      change (Finsupp.lapply (s(x, y)) : EdgeChain →ₗ[ZMod 2] ZMod 2)
        (∑ p ∈ P, tailCoefficient c R p.1 p.2 • plaquette p) = 0
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro p hp
      simp only [Finsupp.lapply_apply, Finsupp.smul_apply]
      rw [plaquetteCoeff_zero_nonadjacent p x y hadj]
      simp
    rw [hc, hp]

end AKLT.W.WIN017
