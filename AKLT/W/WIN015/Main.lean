module
public import AKLT.Blueprint.Win.NodesTopology

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
open AKLT.Blueprint.Win

namespace AKLT.W.WIN015

private def leftBox (R i : ℤ) : Finset Plane :=
  (Finset.Icc (-R) (min i R)).product (Finset.Icc (-R) R)

private lemma sum_pair_incidence (S : Finset Plane) (a b : Plane) (hne : a ≠ b)
    (q : ZMod 2) :
    (∑ x ∈ S, if x ∈ s(a, b) then q else 0) =
      (if a ∈ S then q else 0) + (if b ∈ S then q else 0) := by
  calc
    (∑ x ∈ S, if x ∈ s(a, b) then q else 0) =
        (∑ x ∈ S, ((if x = a then q else 0) + (if x = b then q else 0))) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Sym2.mem_iff]
      by_cases hxa : x = a
      · subst x
        simp [hne]
      · by_cases hxb : x = b
        · subst x
          simp [hne.symm]
        · simp [hxa, hxb]
    _ = (if a ∈ S then q else 0) + (if b ∈ S then q else 0) := by
      simp [Finset.sum_add_distrib]

private lemma horizontal_edges_unique (i r s : ℤ)
    (h : s((i, r), (i + 1, r)) = s((i, s), (i + 1, s))) : r = s := by
  rw [Sym2.eq_iff] at h
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact congrArg Prod.snd h₁
  · exfalso
    have : i = i + 1 := congrArg Prod.fst h₁
    omega

private lemma box_edge_sum (R i : ℤ) (c : EdgeChain) (hnn : ChainNN c)
    (hbox : ChainInBox c R) (e : LatticeEdge) (he : e ∈ c.support) :
    (∑ x ∈ leftBox R i, if x ∈ e then c e else 0) =
      ∑ r ∈ Finset.Icc (-R) R,
        if e = s((i, r), (i + 1, r)) then c e else 0 := by
  obtain ⟨a, b, rfl, hab⟩ := hnn e he
  have haBox := hbox (s(a, b)) he a (by simp)
  have hbBox := hbox (s(a, b)) he b (by simp)
  have ha1lo : -R ≤ a.1 := (abs_le.mp haBox.1).1
  have ha1hi : a.1 ≤ R := (abs_le.mp haBox.1).2
  have ha2lo : -R ≤ a.2 := (abs_le.mp haBox.2).1
  have ha2hi : a.2 ≤ R := (abs_le.mp haBox.2).2
  have hb1lo : -R ≤ b.1 := (abs_le.mp hbBox.1).1
  have hb1hi : b.1 ≤ R := (abs_le.mp hbBox.1).2
  have hb2lo : -R ≤ b.2 := (abs_le.mp hbBox.2).1
  have hb2hi : b.2 ≤ R := (abs_le.mp hbBox.2).2
  have haS : a ∈ leftBox R i ↔ a.1 ≤ i := by
    simp [leftBox, Finset.mem_product, Finset.mem_Icc]
    omega
  have hbS : b ∈ leftBox R i ↔ b.1 ≤ i := by
    simp [leftBox, Finset.mem_product, Finset.mem_Icc]
    omega
  have hne : a ≠ b := by
    intro h
    subst b
    simp [Adjacent, latticeDist] at hab
  have hstep :
      (a.1 = b.1 ∧ (a.2 + 1 = b.2 ∨ b.2 + 1 = a.2)) ∨
      (a.2 = b.2 ∧ (a.1 + 1 = b.1 ∨ b.1 + 1 = a.1)) := by
    unfold Adjacent latticeDist at hab
    omega
  rw [sum_pair_incidence (leftBox R i) a b hne (c s(a, b))]
  by_cases hai : a.1 ≤ i
  · by_cases hbi : b.1 ≤ i
    · have hnoCross : ∀ s : ℤ, s(a, b) ≠ s((i, s), (i + 1, s)) := by
        intro s hs
        rw [Sym2.eq_iff] at hs
        rcases hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> rcases h₁ with ⟨h₁a, h₁b⟩ <;>
          rcases h₂ with ⟨h₂a, h₂b⟩ <;> simp_all
      simp [haS, hbS, hai, hbi, hnoCross]
      exact CharTwo.add_self_eq_zero _
    · have hcross : (a.1 ≤ i) ≠ (b.1 ≤ i) := by simp [hai, hbi]
      have hcoords : a.2 = b.2 ∧ a.1 = i ∧ b.1 = i + 1 := by
        rcases hstep with hvert | hhor
        · omega
        · omega
      let r := a.2
      have hr : r ∈ Finset.Icc (-R) R := by
        simp [r, Finset.mem_Icc]
        exact ⟨ha2lo, ha2hi⟩
      have heq : s(a, b) = s((i, r), (i + 1, r)) := by
        rcases hcoords with ⟨h2, h1, h3⟩
        rw [show a = (i, r) by exact Prod.ext h1 (by rfl)]
        rw [show b = (i + 1, r) by exact Prod.ext h3 (by simpa [r] using h2.symm)]
      have huniq : ∀ s : ℤ,
          s((i, r), (i + 1, r)) = s((i, s), (i + 1, s)) ↔ s = r := by
        intro s
        constructor
        · intro heq
          exact (horizontal_edges_unique i r s heq).symm
        · intro hs
          subst s
          rfl
      simp [haS, hbS, hai, hbi, heq, huniq, hr]
  · by_cases hbi : b.1 ≤ i
    · have hcross : (a.1 ≤ i) ≠ (b.1 ≤ i) := by simp [hai, hbi]
      have hcoords : a.2 = b.2 ∧ a.1 = i + 1 ∧ b.1 = i := by
        rcases hstep with hvert | hhor
        · omega
        · omega
      let r := a.2
      have hr : r ∈ Finset.Icc (-R) R := by
        simp [r, Finset.mem_Icc]
        exact ⟨ha2lo, ha2hi⟩
      have heq : s(a, b) = s((i, r), (i + 1, r)) := by
        rcases hcoords with ⟨h2, h1, h3⟩
        rw [show a = (i + 1, r) by exact Prod.ext h1 (by rfl)]
        rw [show b = (i, r) by exact Prod.ext h3 (by simpa [r] using h2.symm)]
        exact Sym2.eq_swap
      have huniq : ∀ s : ℤ,
          s((i, r), (i + 1, r)) = s((i, s), (i + 1, s)) ↔ s = r := by
        intro s
        constructor
        · intro heq
          exact (horizontal_edges_unique i r s heq).symm
        · intro hs
          subst s
          rfl
      simp [haS, hbS, hai, hbi, heq, huniq, hr]
    · have hsame : (a.1 ≤ i) = (b.1 ≤ i) := by simp [hai, hbi]
      have hnoCross : ∀ s : ℤ, s(a, b) ≠ s((i, s), (i + 1, s)) := by
        intro s hs
        rw [Sym2.eq_iff] at hs
        rcases hs with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
          rcases h₁ with ⟨h₁a, h₁b⟩ <;> rcases h₂ with ⟨h₂a, h₂b⟩ <;>
          simp_all
      simp [haS, hbS, hai, hbi, hnoCross]

theorem main : AKLT.Blueprint.Win.ColumnFluxStatement := by
  classical
  intro c hnn heven R hR hbox i
  let S := leftBox R i
  have hsumzero :
      (∑ x ∈ S, ∑ e ∈ c.support, if x ∈ e then c e else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact heven x
  rw [Finset.sum_comm] at hsumzero
  have hformula :
      (∑ e ∈ c.support, ∑ x ∈ S, if x ∈ e then c e else 0) =
        ∑ e ∈ c.support,
          ∑ r ∈ Finset.Icc (-R) R,
            if e = s((i, r), (i + 1, r)) then c e else 0 := by
    apply Finset.sum_congr rfl
    intro e he
    simpa [S] using box_edge_sum R i c hnn hbox e he
  rw [hformula, Finset.sum_comm] at hsumzero
  have hinner : ∀ r : ℤ,
      (∑ e ∈ c.support,
        if e = s((i, r), (i + 1, r)) then c e else 0) =
          c s((i, r), (i + 1, r)) := by
    intro r
    by_cases hs : s((i, r), (i + 1, r)) ∈ c.support
    · simp [Finset.sum_ite_eq', hs]
    · have hc : c s((i, r), (i + 1, r)) = 0 := by
        by_contra hne
        exact hs (Finsupp.mem_support_iff.mpr hne)
      simp [Finset.sum_ite_eq', hs, hc]
  have hreduce :
      (∑ r ∈ Finset.Icc (-R) R,
        ∑ e ∈ c.support,
          if e = s((i, r), (i + 1, r)) then c e else 0) =
        ∑ r ∈ Finset.Icc (-R) R,
          c s((i, r), (i + 1, r)) := by
    apply Finset.sum_congr rfl
    intro r hr
    exact hinner r
  rw [hreduce] at hsumzero
  have htarget :
      (∑ r ∈ Finset.Icc (-R) R,
        c s((i, r), (i + 1, r))) = 0 := by
    simpa [horizontal] using hsumzero
  simpa [horizontal] using htarget

end AKLT.W.WIN015

#print axioms AKLT.W.WIN015.main
