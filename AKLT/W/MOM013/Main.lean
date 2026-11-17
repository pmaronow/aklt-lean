module
public import AKLT.Blueprint.Mom.NodesFinite

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open AKLT.Defs

namespace AKLT.W.MOM013

private def PreviousNeighbors {n : ℕ} (D : FiniteSpinNetwork n) (k : ℕ)
    (x : Fin n) :=
  {y : Fin n // y.val < k ∧ (y, x) ∈ D.bonds}

private def PrefixGood {α : Type} {n : ℕ} [Fintype α]
    (D : FiniteSpinNetwork n) (v : α → Vec3) (k : ℕ) (σ : Fin k → α) : Prop :=
  (∀ x : Fin n, ∀ hx : x.val < k, ∀ j : Fin (D.pinCount x),
    0 < 1 + dot ((D.pin x j).val) (v (σ ⟨x.val, hx⟩))) ∧
  (∀ e, ∀ he : e ∈ D.bonds, ∀ h₁ : e.1.val < k, ∀ h₂ : e.2.val < k,
    0 < 1 + dot (v (σ ⟨e.1.val, h₁⟩)) (v (σ ⟨e.2.val, h₂⟩)))

private theorem dot_comm (a b : Vec3) : dot a b = dot b a := by
  simp [AKLT.Defs.dot, mul_comm]

private theorem prefix_exists {α : Type} [Fintype α] (v : α → Vec3)
    (hball : ∀ a, normSq (v a) ≤ 1)
    (hlocal : ∀ k : ℕ, k ≤ 4 → ∀ b : Fin k → Vec3,
      (∀ i, normSq (b i) ≤ 1) → ∃ a, ∀ i, 0 < 1 + dot (v a) (b i))
    {n : ℕ} (D : FiniteSpinNetwork n) (hvalid : D.Valid) :
    ∀ k ≤ n, ∃ σ : Fin k → α, PrefixGood D v k σ := by
  classical
  intro k
  induction k with
  | zero =>
      intro hkn
      refine ⟨Fin.elim0, ?_⟩
      constructor
      · intro x hx j
        omega
      · intro e he h₁ h₂
        omega
  | succ k ih =>
      intro hkn
      obtain ⟨σ, hgood⟩ := ih (by omega)
      let x : Fin n := ⟨k, by omega⟩
      letI : Fintype (PreviousNeighbors D k x) :=
        Fintype.ofInjective (fun y : PreviousNeighbors D k x => y.1) Subtype.val_injective
      letI : Fintype (Fin (D.pinCount x) ⊕ PreviousNeighbors D k x) := inferInstance
      let Inc := {e : Fin n × Fin n // e ∈ D.bonds ∧ (e.1 = x ∨ e.2 = x)}
      letI : Fintype Inc := Fintype.ofInjective (fun e : Inc => e.1) Subtype.val_injective
      have hNInc : Fintype.card (PreviousNeighbors D k x) ≤ Fintype.card Inc := by
        apply Fintype.card_le_of_injective (fun y : PreviousNeighbors D k x =>
          (⟨(y.1, x), ⟨y.2.2, Or.inr rfl⟩⟩ : Inc))
        intro a b hab
        apply Subtype.ext
        have hfst := congrArg (fun e : Inc => e.val.1) hab
        exact Fin.ext (congrArg Fin.val hfst)
      have hIncCard : Fintype.card Inc =
          (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card := by
        let s := D.bonds.filter fun e => e.1 = x ∨ e.2 = x
        let equivInc : Inc ≃ {e // e ∈ s} := {
          toFun := fun e => ⟨e.1, Finset.mem_filter.mpr ⟨e.2.1, e.2.2⟩⟩
          invFun := fun e => ⟨e.1, Finset.mem_filter.mp e.2⟩
          left_inv := by intro e; apply Subtype.ext; rfl
          right_inv := by intro e; apply Subtype.ext; rfl }
        calc
          Fintype.card Inc = Fintype.card {e // e ∈ s} := Fintype.card_congr equivInc
          _ = s.card := Fintype.card_coe s
      rcases hvalid with ⟨_, horder, hdegree⟩
      have hQcard : Fintype.card (Fin (D.pinCount x) ⊕ PreviousNeighbors D k x) ≤ 4 := by
        rw [Fintype.card_sum, Fintype.card_fin]
        calc
          D.pinCount x + Fintype.card (PreviousNeighbors D k x) ≤
              D.pinCount x + Fintype.card Inc := Nat.add_le_add_left hNInc _
          _ = (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card + D.pinCount x := by
            rw [hIncCard]
            omega
          _ ≤ 4 := hdegree x
      let equiv : (Fin (D.pinCount x) ⊕ PreviousNeighbors D k x) ≃
          Fin (Fintype.card (Fin (D.pinCount x) ⊕ PreviousNeighbors D k x)) :=
        Fintype.equivFin _
      let b : Fin (Fintype.card (Fin (D.pinCount x) ⊕ PreviousNeighbors D k x)) → Vec3 := fun i =>
        match equiv.symm i with
        | Sum.inl j => (D.pin x j).val
        | Sum.inr y => v (σ ⟨y.1.val, y.2.1⟩)
      have hb : ∀ i, normSq (b i) ≤ 1 := by
        intro i
        cases hq : equiv.symm i with
        | inl j =>
            have hbvalue : b i = (D.pin x j).val := by simp [b, hq]
            rw [hbvalue]
            exact le_of_eq (D.pin x j).property
        | inr y =>
            have hbvalue : b i = v (σ ⟨y.1.val, y.2.1⟩) := by simp [b, hq]
            rw [hbvalue]
            exact hball _
      obtain ⟨a, ha⟩ := hlocal
        (Fintype.card (Fin (D.pinCount x) ⊕ PreviousNeighbors D k x)) hQcard b hb
      let σ' : Fin (k + 1) → α := fun z =>
        if hz : z.val < k then σ ⟨z.val, hz⟩ else a
      have hσold (y : Fin n) (hy : y.val < k) :
          σ' ⟨y.val, by omega⟩ = σ ⟨y.val, hy⟩ := by
        simp [σ', hy]
      have hσnew : σ' ⟨k, by omega⟩ = a := by
        simp [σ']
      refine ⟨σ', ?_⟩
      constructor
      · intro y hy j
        by_cases hlt : y.val < k
        · rw [hσold y hlt]
          exact hgood.1 y hlt j
        · have hyk : y.val = k := by omega
          have hyx : y = x := Fin.ext hyk
          subst y
          rw [hσnew]
          have hpos := ha (equiv (Sum.inl j))
          have hbvalue : b (equiv (Sum.inl j)) = (D.pin x j).val := by
            change (match equiv.symm (equiv (Sum.inl j)) with
              | Sum.inl q => (D.pin x q).val
              | Sum.inr y => v (σ ⟨y.1.val, y.2.1⟩)) = (D.pin x j).val
            rw [Equiv.symm_apply_apply]
          rw [hbvalue, dot_comm] at hpos
          exact hpos
      · intro e he h₁ h₂
        by_cases hprior : e.2.val < k
        · have hfirst : e.1.val < k := by
            have hlt := horder e he
            exact lt_trans hlt hprior
          rw [hσold e.1 hfirst, hσold e.2 hprior]
          exact hgood.2 e he hfirst hprior
        · have hsecond : e.2.val = k := by omega
          have hfirst : e.1.val < k := by
            have hlt := horder e he
            omega
          have heq : e.2 = x := Fin.ext hsecond
          have hpair : (e.1, x) = e := Prod.ext rfl heq.symm
          have hmem : (e.1, x) ∈ D.bonds := by
            rw [← hpair] at he
            exact he
          let y : PreviousNeighbors D k x := ⟨e.1, ⟨hfirst, hmem⟩⟩
          have hpos := ha (equiv (Sum.inr y))
          have hbvalue : b (equiv (Sum.inr y)) = v (σ ⟨e.1.val, hfirst⟩) := by
            change (match equiv.symm (equiv (Sum.inr y)) with
              | Sum.inl j => (D.pin x j).val
              | Sum.inr z => v (σ ⟨z.1.val, z.2.1⟩)) =
              v (σ ⟨e.1.val, hfirst⟩)
            rw [Equiv.symm_apply_apply]
          rw [hbvalue] at hpos
          rw [hσold e.1 hfirst]
          have hσedge : σ' ⟨e.2.val, h₂⟩ = a := by
            have hz : (⟨e.2.val, h₂⟩ : Fin (k + 1)) = ⟨k, by omega⟩ :=
              Fin.ext hsecond
            rw [hz]
            exact hσnew
          rw [hσedge, dot_comm]
          exact hpos

theorem main : AKLT.Blueprint.Mom.GreedyAssignmentStatement := by
  intro α inst v hball hlocal n D hvalid
  obtain ⟨σ, hgood⟩ := prefix_exists v hball hlocal D hvalid n (Nat.le_refl n)
  refine ⟨σ, ?_, ?_⟩
  · intro e he
    exact hgood.2 e he e.1.isLt e.2.isLt
  · intro x j
    exact hgood.1 x x.isLt j

end AKLT.W.MOM013
