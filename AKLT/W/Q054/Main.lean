module
public import AKLT.Blueprint.Q.NodesEnergy

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Q

namespace AKLT.W.Q054

local instance (priority := 100) (p : Prop) : Decidable p := Classical.propDecidable p

private abbrev Config (ι : Type*) (S : ι → Type*) := (x : ι) → S x

private def mass {ι : Type*} {S : ι → Type*} [Fintype ι] [DecidableEq ι]
    [∀ x, Fintype (S x)] (p : Weight (Config ι S)) (E : Config ι S → Prop)
    [DecidablePred E] : ℝ := by
  exact ∑ σ, if E σ then p σ else 0

private def fibreMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)]
    (p : Weight (Config ι S)) (x : ι) (σ : Config ι S)
    [DecidablePred (fun τ => fullFibreEvent x σ τ)] : ℝ := by
  exact ∑ τ, if fullFibreEvent x σ τ then p τ else 0

private def fibreLetterMass {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)]
    (p : Weight (Config ι S)) (x : ι) (σ : Config ι S) (a : S x)
    [DecidablePred (fun τ => fullFibreEvent x σ τ ∧ τ x = a)] : ℝ := by
  exact ∑ τ, if fullFibreEvent x σ τ ∧ τ x = a then p τ else 0

private def fibreEquiv {ι : Type*} [DecidableEq ι] {S : ι → Type*}
    (x : ι) [∀ y, Nonempty (S y)] (τ : Config ι S) :
    S x ≃ {σ : Config ι S // fullFibreEvent x σ τ} where
  toFun a := ⟨Function.update τ x a, by
    intro y hy
    simp [fullFibreEvent, hy]
  ⟩
  invFun σ := σ.1 x
  left_inv a := by simp
  right_inv σ := by
    apply Subtype.ext
    funext y
    by_cases hy : y = x
    · subst y
      simp
    · simpa [Function.update, hy] using (σ.2 y hy)

private lemma fibre_card {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (x : ι) (τ : Config ι S) :
    (Finset.univ.filter fun σ : Config ι S => fullFibreEvent x σ τ).card =
      Fintype.card (S x) := by
  have h := Fintype.card_congr (fibreEquiv x τ).symm
  let e : {σ : Config ι S // σ ∈ Finset.univ.filter
        (fun σ : Config ι S => fullFibreEvent x σ τ)} ≃
      {σ : Config ι S // fullFibreEvent x σ τ} := {
    toFun := fun σ => ⟨σ.1, (Finset.mem_filter.mp σ.2).2⟩
    invFun := fun σ => ⟨σ.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, σ.2⟩⟩
    left_inv := by intro σ; cases σ; rfl
    right_inv := by intro σ; cases σ; rfl
  }
  calc
    (Finset.univ.filter fun σ : Config ι S => fullFibreEvent x σ τ).card =
        Fintype.card ↥(Finset.univ.filter
          (fun σ : Config ι S => fullFibreEvent x σ τ)) := by
            exact (Fintype.card_coe _).symm
    _ = Fintype.card {σ : Config ι S // fullFibreEvent x σ τ} := by
      exact Fintype.card_congr e
    _ = Fintype.card (S x) := h

private lemma sum_fibre_indicator {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (x : ι) (τ : Config ι S) :
    (∑ σ, if fullFibreEvent x σ τ then (1 : ℝ) else 0) = Fintype.card (S x) := by
  calc
    (∑ σ, if fullFibreEvent x σ τ then (1 : ℝ) else 0) =
        ((Finset.univ.filter fun σ : Config ι S => fullFibreEvent x σ τ).card : ℝ) := by
          simp
    _ = Fintype.card (S x) := by exact_mod_cast fibre_card x τ

private lemma aggregate_fibres {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config ι S)) (x : ι)
    (P H : Config ι S → Prop) [DecidablePred P] [DecidablePred H]
    (hP : ∀ σ τ, fullFibreEvent x σ τ → (P σ ↔ P τ)) :
    (∑ σ, if P σ then ∑ τ, if fullFibreEvent x σ τ ∧ H τ then p τ else 0 else 0) =
      (Fintype.card (S x) : ℝ) * mass p (fun τ => P τ ∧ H τ) := by
  unfold mass
  rw [show (∑ σ, if P σ then ∑ τ,
      if fullFibreEvent x σ τ ∧ H τ then p τ else 0 else 0) =
    ∑ σ, ∑ τ, if P σ ∧ fullFibreEvent x σ τ ∧ H τ then p τ else 0 by
      apply Finset.sum_congr rfl
      intro σ hσ
      by_cases hp : P σ <;> simp [hp]]
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ hτ
  have hinner : (∑ σ, if P σ ∧ fullFibreEvent x σ τ ∧ H τ then p τ else 0) =
      (if P τ ∧ H τ then (Fintype.card (S x) : ℝ) * p τ else 0) := by
    by_cases hh : H τ
    · by_cases hp : P τ
      · have hcond : ∀ σ, (P σ ∧ fullFibreEvent x σ τ ∧ H τ) ↔
            fullFibreEvent x σ τ := by
          intro σ
          constructor
          · exact fun h => h.2.1
          · intro hf
            exact ⟨(hP σ τ hf).mpr hp, hf, hh⟩
        simp_rw [hcond]
        calc
          (∑ σ, if fullFibreEvent x σ τ then p τ else 0) =
              ∑ σ, (if fullFibreEvent x σ τ then (1 : ℝ) else 0) * p τ := by
                apply Finset.sum_congr rfl
                intro σ hσ
                by_cases hf : fullFibreEvent x σ τ <;> simp [hf]
          _ = (∑ σ, if fullFibreEvent x σ τ then (1 : ℝ) else 0) * p τ := by
                rw [Finset.sum_mul]
          _ = (Fintype.card (S x) : ℝ) * p τ := by rw [sum_fibre_indicator]
        simpa [hp, hh]
      · have hcond : ∀ σ, (P σ ∧ fullFibreEvent x σ τ ∧ H τ) ↔ False := by
          intro σ
          constructor
          · rintro ⟨hσ, hf, _⟩
            exact hp ((hP σ τ hf).mp hσ)
          · simp
        have hz : ∀ σ, ¬ (P σ ∧ fullFibreEvent x σ τ ∧ H τ) := by
          intro σ hσ
          exact (hcond σ).mp hσ
        calc
          (∑ σ, if P σ ∧ fullFibreEvent x σ τ ∧ H τ then p τ else 0) = 0 := by
            simp [hz]
          _ = if P τ ∧ H τ then (Fintype.card (S x) : ℝ) * p τ else 0 := by
            simp [hp]
    · simp [hh]
  rw [hinner]
  by_cases hp : P τ ∧ H τ <;> simp [hp]

private lemma fibre_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config ι S)) (hp : ∀ σ, 0 < p σ)
    (α : ℝ) (x : ι) (a : S x) (σ : Config ι S)
    (h : α ≤ conditionalProbability p (fullFibreEvent x σ) (fun τ => τ x = a)) :
    α * fibreMass p x σ ≤ fibreLetterMass p x σ a := by
  have hden : 0 < fibreMass p x σ := by
    unfold fibreMass
    have hterm : 0 < (if fullFibreEvent x σ σ then p σ else 0) := by
      simpa [fullFibreEvent] using hp σ
    have hsum := Finset.single_le_sum
      (s := Finset.univ)
      (f := fun τ => if fullFibreEvent x σ τ then p τ else 0)
      (fun τ _ => by
        by_cases hτ : fullFibreEvent x σ τ
        · simp [hτ, le_of_lt (hp τ)]
        · simp [hτ])
      (Finset.mem_univ σ)
    exact lt_of_lt_of_le hterm (by simpa using hsum)
  have hratio : α ≤ fibreLetterMass p x σ a / fibreMass p x σ := by
    have hraw : α ≤
        (∑ τ, if fullFibreEvent x σ τ ∧ τ x = a then p τ else 0) /
          fibreMass p x σ := by
      simpa [conditionalProbability, fibreMass] using h
    have hnum : (∑ τ, if fullFibreEvent x σ τ ∧ τ x = a then p τ else 0) =
        fibreLetterMass p x σ a := by
      unfold fibreLetterMass
      apply Finset.sum_congr rfl
      intro τ hτ
      by_cases hf : fullFibreEvent x σ τ <;> by_cases ha : τ x = a <;> simp [hf, ha]
    rw [hnum] at hraw
    exact hraw
  exact (le_div_iff₀ hden).mp hratio

private lemma aggregate_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config ι S)) (hp : ∀ σ, 0 < p σ)
    (α : ℝ) (x : ι) (a : S x) (P : Config ι S → Prop) [DecidablePred P]
    (hP : ∀ σ τ, fullFibreEvent x σ τ → (P σ ↔ P τ))
    (hlocal : ∀ σ, α * fibreMass p x σ ≤ fibreLetterMass p x σ a) :
    α * mass p P ≤ mass p (fun τ => P τ ∧ τ x = a) := by
  have hsum : (∑ σ, if P σ then α * fibreMass p x σ else 0) ≤
      (∑ σ, if P σ then fibreLetterMass p x σ a else 0) := by
    apply Finset.sum_le_sum
    intro σ hσ
    by_cases hPσ : P σ
    · simpa [hPσ] using hlocal σ
    · simp [hPσ]
  have hden := aggregate_fibres p x P (fun _ => True) hP
  have hnum := aggregate_fibres p x P (fun τ => τ x = a) hP
  have hsum' : α * (∑ σ, if P σ then fibreMass p x σ else 0) ≤
      (∑ σ, if P σ then fibreLetterMass p x σ a else 0) := by
    simpa [fibreMass, fibreLetterMass, mul_ite, Finset.mul_sum] using hsum
  have hden' : (∑ σ, if P σ then fibreMass p x σ else 0) =
      (Fintype.card (S x) : ℝ) * mass p P := by
    simpa [fibreMass] using hden
  have hnum' : (∑ σ, if P σ then fibreLetterMass p x σ a else 0) =
      (Fintype.card (S x) : ℝ) * mass p (fun τ => P τ ∧ τ x = a) := by
    simpa [fibreLetterMass] using hnum
  rw [hden', hnum'] at hsum'
  have hcard : 0 < (Fintype.card (S x) : ℝ) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (S x))
  have hmass : α * ((Fintype.card (S x) : ℝ) * mass p P) ≤
      (Fintype.card (S x) : ℝ) * mass p (fun τ => P τ ∧ τ x = a) := by
    simpa [mul_assoc] using hsum'
  nlinarith [hmass]

private lemma mass_partial_lower {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)] [∀ x, Nonempty (S x)]
    (p : Weight (Config ι S)) (hp : ∀ σ, 0 < p σ)
    (α : ℝ) (hα : 0 < α)
    (hlocal : ∀ x σ a, α ≤ conditionalProbability p (fullFibreEvent x σ)
      (fun τ => τ x = a))
    (J K : Finset ι) (hdis : Disjoint K J)
    (a b : Config ι S) :
    α ^ K.card * mass p (fun σ => ∀ x ∈ J, σ x = a x) ≤
      mass p (fun σ => (∀ x ∈ J, σ x = a x) ∧ (∀ x ∈ K, σ x = b x)) := by
  induction K using Finset.induction_on with
  | empty =>
      simp [mass]
  | @insert x K hx ih =>
      have hdisK : Disjoint K J := Finset.disjoint_of_subset_left
        (Finset.subset_insert x K) hdis
      have hxJ : x ∉ J := by
        intro hxJ
        exact (Finset.disjoint_left.mp hdis) (Finset.mem_insert_self x K) hxJ
      have hP : ∀ σ τ, fullFibreEvent x σ τ →
          ((∀ y ∈ J, σ y = a y) ∧ (∀ y ∈ K, σ y = b y) ↔
            (∀ y ∈ J, τ y = a y) ∧ (∀ y ∈ K, τ y = b y)) := by
        intro σ τ hf
        constructor
        · rintro ⟨hJ, hK⟩
          refine ⟨?_, ?_⟩
          · intro y hy
            have hyx : y ≠ x := by intro heq; subst y; exact hxJ hy
            calc
              τ y = σ y := hf y hyx
              _ = a y := hJ y hy
          · intro y hy
            have hyx : y ≠ x := by intro heq; subst y; exact hx hy
            calc
              τ y = σ y := hf y hyx
              _ = b y := hK y hy
        · rintro ⟨hJ, hK⟩
          refine ⟨?_, ?_⟩
          · intro y hy
            have hyx : y ≠ x := by intro heq; subst y; exact hxJ hy
            calc
              σ y = τ y := (hf y hyx).symm
              _ = a y := hJ y hy
          · intro y hy
            have hyx : y ≠ x := by intro heq; subst y; exact hx hy
            calc
              σ y = τ y := (hf y hyx).symm
              _ = b y := hK y hy
      have hstep := aggregate_lower p hp α x (b x)
        (fun σ => (∀ y ∈ J, σ y = a y) ∧ (∀ y ∈ K, σ y = b y)) hP
        (fun σ => fibre_lower p hp α x (b x) σ (hlocal x σ (b x)))
      have hmul := mul_le_mul_of_nonneg_left (ih hdisK) (le_of_lt hα)
      have hcombine : α * (α ^ K.card * mass p (fun σ => ∀ y ∈ J, σ y = a y)) ≤
          mass p (fun σ => (∀ y ∈ J, σ y = a y) ∧
            (∀ y ∈ K, σ y = b y) ∧ σ x = b x) := by
        have hstep' : α * mass p
            (fun σ => (∀ y ∈ J, σ y = a y) ∧ (∀ y ∈ K, σ y = b y)) ≤
            mass p (fun σ => ((∀ y ∈ J, σ y = a y) ∧ (∀ y ∈ K, σ y = b y)) ∧
              σ x = b x) := by
          simpa [mass] using hstep
        have hmul' : α * (α ^ K.card * mass p (fun σ => ∀ y ∈ J, σ y = a y)) ≤
            α * mass p (fun σ => (∀ y ∈ J, σ y = a y) ∧ (∀ y ∈ K, σ y = b y)) := by
          simpa [mul_assoc] using hmul
        have := le_trans hmul' hstep'
        simpa [mass, and_assoc] using this
      simpa [Finset.card_insert_of_notMem hx, pow_succ, mul_assoc, mul_left_comm,
        mul_comm, and_assoc, and_left_comm, and_comm, Finset.forall_mem_insert] using hcombine

private lemma mass_partial_event_pos {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : ι → Type*} [∀ x, Fintype (S x)]
    (p : Weight (Config ι S)) (hp : ∀ σ, 0 < p σ)
    (J : Finset ι) (a : Config ι S) :
    0 < mass p (fun σ => ∀ x ∈ J, σ x = a x) := by
  have hterm : 0 < (if (∀ x ∈ J, a x = a x) then p a else 0) := by
    simpa using hp a
  have hsum := Finset.single_le_sum
    (s := Finset.univ)
    (f := fun σ => if (∀ x ∈ J, σ x = a x) then p σ else 0)
    (fun σ _ => by
      by_cases hσ : (∀ x ∈ J, σ x = a x)
      · simpa only [if_pos hσ] using le_of_lt (hp σ)
      · simp [hσ])
    (Finset.mem_univ a)
  exact lt_of_lt_of_le hterm (by simpa [mass] using hsum)

theorem main : AKLT.Blueprint.Q.PartialAssignmentStatement := by
  intro ι hι hDec S hFin hNon p hp α hα hα1 hlocal U J hdis a b
  have hp' : ∀ σ : Config ι S, 0 < p σ := hp.1
  have hmass := mass_partial_lower p hp' α hα
    (fun x σ a => hlocal x σ a) J U hdis a b
  have hden := mass_partial_event_pos p hp' J a
  change α ^ U.card ≤ conditionalProbability p
    (fun σ => ∀ x ∈ J, σ x = a x) (fun σ => ∀ x ∈ U, σ x = b x)
  unfold conditionalProbability
  let E : Config ι S → Prop := fun σ => ∀ x ∈ J, σ x = a x
  let A : Config ι S → Prop := fun σ => ∀ x ∈ U, σ x = b x
  let denRaw : ℝ := ∑ σ, @ite ℝ (E σ) (Classical.propDecidable (E σ)) (p σ) 0
  let numRaw : ℝ := ∑ σ, if E σ ∧ A σ then p σ else 0
  have hdenEq : mass p E = denRaw := by
    unfold mass denRaw
    apply Finset.sum_congr rfl
    intro σ hσ
    by_cases he : E σ <;> simp [he]
  have hnumEq : mass p (fun σ => E σ ∧ A σ) = numRaw := by
    unfold mass numRaw
    apply Finset.sum_congr rfl
    intro σ hσ
    by_cases he : E σ ∧ A σ <;> simp [he]
  have hdenPos : 0 < denRaw := by
    rw [← hdenEq]
    exact hden
  have hnumLower : α ^ U.card * denRaw ≤ numRaw := by
    calc
      α ^ U.card * denRaw = α ^ U.card * mass p E := by rw [← hdenEq]
      _ ≤ mass p (fun σ => E σ ∧ A σ) := by simpa [E, A] using hmass
      _ = numRaw := hnumEq
  let numDecTarget : DecidablePred (fun σ : Config ι S => E σ ∧ A σ) := fun σ => by
    letI : Decidable (E σ) := Classical.propDecidable (E σ)
    letI : Decidable (A σ) := Classical.propDecidable (A σ)
    exact instDecidableAnd
  have hnumTarget : numRaw =
      (∑ σ, @ite ℝ (E σ ∧ A σ) (numDecTarget σ) (p σ) 0) := by
    unfold numRaw
    apply Finset.sum_congr rfl
    intro σ hσ
    by_cases he : E σ ∧ A σ <;> simp [E, A, he]
  apply (le_div_iff₀ hdenPos).2
  calc
    α ^ U.card * denRaw ≤ numRaw := hnumLower
    _ = (∑ σ, @ite ℝ
        ((fun σ : Config ι S => ∀ x ∈ J, σ x = a x) σ ∧
          (fun σ : Config ι S => ∀ x ∈ U, σ x = b x) σ)
        (numDecTarget σ) (p σ) 0) := hnumTarget

end AKLT.W.Q054
