import AKLT.Blueprint.Q.NodesStar

open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Q

noncomputable section

namespace AKLT.W.Q017

private def zeroConfig : Fin 5 → Fin 5 := fun _ => 0

private def basisVector (s : Fin 5 → Fin 5) : StarHilbert :=
  WithLp.toLp 2 (Pi.single s (1 : ℂ))

private def vacuum : StarHilbert := basisVector zeroConfig

private def oneExcitation (x : Fin 5) : Fin 5 → Fin 5 :=
  Function.update zeroConfig x 1

private lemma toEuclideanLin_single_apply {α β : Type*} [Fintype β] [DecidableEq β]
    (M : Matrix α β ℂ) (i : β) :
    (Matrix.toEuclideanLin M) (WithLp.toLp 2 (Pi.single i (1 : ℂ))) =
      WithLp.toLp 2 (fun j => M j i) := by
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_toLp, Matrix.toLin'_apply,
    Matrix.mulVec_single]
  congr 1
  ext j
  simp [Matrix.col]

private lemma starAtSite_basis (A : Matrix (Fin 5) (Fin 5) ℂ) (x : Fin 5)
    (s : Fin 5 → Fin 5) :
    starAtSite A x (basisVector s) =
      WithLp.toLp 2 (fun t =>
        if (∀ y, y ≠ x → t y = s y) then A (t x) (s x) else 0) := by
  let M : Matrix (Fin 5 → Fin 5) (Fin 5 → Fin 5) ℂ :=
    fun t r => if ∀ y, y ≠ x → t y = r y then A (t x) (r x) else 0
  change Matrix.toEuclideanLin M (WithLp.toLp 2 (Pi.single s (1 : ℂ))) = _
  rw [Matrix.toEuclideanLin, Matrix.toLpLin_toLp, Matrix.toLin'_apply,
    Matrix.mulVec_single]
  congr 1
  ext t
  simp [Matrix.col, Matrix.transpose, M]


private lemma starZ_vacuum (x : Fin 5) :
    starAtSite spinZ x vacuum = (2 : ℂ) • vacuum := by
  change starAtSite spinZ x (basisVector zeroConfig) = _
  rw [starAtSite_basis]
  ext t
  by_cases ht : t = zeroConfig
  · subst t
    simp [vacuum, basisVector, zeroConfig, spinZ]
  · simp only [vacuum, basisVector, zeroConfig, Pi.single_apply, smul_eq_mul]
    by_cases hr : ∀ y, ¬ y = x → t y = 0
    · have hx : t x ≠ 0 := by
        intro htx
        apply ht
        funext y
        by_cases hy : y = x
        · subst y
          exact htx
        · exact hr y hy
      simp [hr, spinZ, hx, ht]
    · simp [hr, ht]

private lemma starPlus_vacuum (x : Fin 5) :
    starAtSite spinPlus x vacuum = 0 := by
  change starAtSite spinPlus x (basisVector zeroConfig) = 0
  rw [starAtSite_basis]
  ext t
  simp [vacuum, basisVector, zeroConfig]
  by_cases hr : ∀ y, ¬ y = x → t y = 0
  · simp [hr, spinPlus]
  · simp [hr]

private lemma starMinus_vacuum (x : Fin 5) :
    starAtSite spinMinus x vacuum = (2 : ℂ) • basisVector (oneExcitation x) := by
  change starAtSite spinMinus x (basisVector zeroConfig) = _
  rw [starAtSite_basis]
  ext t
  by_cases ht : t = oneExcitation x
  · subst t
    simp [vacuum, basisVector, oneExcitation, zeroConfig, spinMinus, spinPlus,
      Matrix.conjTranspose_apply, Function.update_apply]
    norm_num
  · have hz : (if ∀ y, y ≠ x → t y = zeroConfig y then
        spinMinus (t x) (zeroConfig x) else 0) = 0 := by
      by_cases hr : ∀ y, y ≠ x → t y = zeroConfig y
      · rw [if_pos hr]
        have htx : t x ≠ 1 := by
          intro htx
          apply ht
          funext y
          by_cases hy : y = x
          · subst y
            have hone : oneExcitation x x = 1 := by simp [oneExcitation, Function.update_self]
            exact htx.trans hone.symm
          · have hty := hr y hy
            simpa [oneExcitation, zeroConfig, Function.update_apply, hy] using hty
        have hval : (t x).val ≠ 1 := by
          intro hv
          apply htx
          exact Fin.ext hv
        by_cases hh : 1 = (t x).val
        · exact False.elim (hval hh.symm)
        · simp [spinMinus, spinPlus, Matrix.conjTranspose_apply, zeroConfig, hh]
      · rw [if_neg hr]
    simp only [WithLp.ofLp_toLp]
    rw [hz]
    simp [vacuum, basisVector, oneExcitation, zeroConfig]
    exact ht


private lemma starPlus_oneExcitation (x y : Fin 5) :
    starAtSite spinPlus x (basisVector (oneExcitation y)) =
      if x = y then (2 : ℂ) • vacuum else 0 := by
  rw [starAtSite_basis]
  by_cases hxy : x = y
  · subst y
    ext t
    by_cases ht : t = zeroConfig
    · subst t
      simp [vacuum, basisVector, oneExcitation, zeroConfig, spinPlus,
        Function.update_apply]
      norm_num
    · have hz : (if ∀ z, z ≠ x → t z = oneExcitation x z then
          spinPlus (t x) (oneExcitation x x) else 0) = 0 := by
        by_cases hr : ∀ z, z ≠ x → t z = oneExcitation x z
        · rw [if_pos hr]
          have hx : t x ≠ 0 := by
            intro htx
            apply ht
            funext z
            by_cases hz : z = x
            · subst z
              exact htx
            · simpa [oneExcitation, Function.update_apply, hz] using hr z hz
          have hone : oneExcitation x x = 1 := by simp [oneExcitation, Function.update_self]
          rw [hone]
          simp [spinPlus, hx]
        · rw [if_neg hr]
      simp only [WithLp.ofLp_toLp]
      rw [hz]
      simp [vacuum, basisVector, oneExcitation, zeroConfig, ht]
  · have hinput : oneExcitation y x = 0 := by
      change Function.update zeroConfig y 1 x = 0
      rw [Function.update_of_ne hxy]
      rfl
    ext t
    simp only [basisVector, Pi.single_apply, Pi.zero_apply, smul_eq_mul]
    by_cases hr : ∀ z, z ≠ x → t z = oneExcitation y z
    · simp [hr, hinput, spinPlus, hxy]
    · simp [hr, hxy]

private def starLeaf (j : Fin 4) : Fin 5 := ⟨j.val + 1, by omega⟩

-- Compare both indices before lifting the formula to concrete star operators.
-- Even the frozen central zero has a different implicit NeZero proof.
private lemma starCasimir_formula (j : Fin 4) :
    starCasimir j =
      (starAtSite spinZ 0 + starAtSite spinZ (starLeaf j)) *
        (starAtSite spinZ 0 + starAtSite spinZ (starLeaf j)) +
      (1 / 2 : ℂ) •
        ((starAtSite spinPlus 0 + starAtSite spinPlus (starLeaf j)) *
          (starAtSite spinMinus 0 + starAtSite spinMinus (starLeaf j)) +
         (starAtSite spinMinus 0 + starAtSite spinMinus (starLeaf j)) *
          (starAtSite spinPlus 0 + starAtSite spinPlus (starLeaf j))) := by
  refine (starCasimir.eq_1 j).trans ?_
  exact congrArg₂ (fun z y : Fin 5 =>
    (starAtSite spinZ z + starAtSite spinZ y) *
      (starAtSite spinZ z + starAtSite spinZ y) +
    (1 / 2 : ℂ) •
      ((starAtSite spinPlus z + starAtSite spinPlus y) *
        (starAtSite spinMinus z + starAtSite spinMinus y) +
       (starAtSite spinMinus z + starAtSite spinMinus y) *
        (starAtSite spinPlus z + starAtSite spinPlus y))) (Fin.ext rfl) (Fin.ext rfl)

private lemma casimirFormula_apply (Z U D : Module.End ℂ StarHilbert) (v : StarHilbert) :
    (Z * Z + (1 / 2 : ℂ) • (U * D + D * U)) v =
      Z (Z v) + (1 / 2 : ℂ) • (U (D v) + D (U v)) := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Module.End.mul_apply]

private lemma starCasimir_vacuum (j : Fin 4) :
    starCasimir j vacuum = (20 : ℂ) • vacuum := by
  let y : Fin 5 := starLeaf j
  let Z := starAtSite spinZ 0 + starAtSite spinZ y
  let U := starAtSite spinPlus 0 + starAtSite spinPlus y
  let D := starAtSite spinMinus 0 + starAtSite spinMinus y
  have hy : y ≠ 0 := by
    intro h
    have : j.val + 1 = 0 := congrArg Fin.val h
    omega
  have hZ : Z vacuum = (4 : ℂ) • vacuum := by
    dsimp [Z]
    rw [starZ_vacuum, starZ_vacuum]
    module
  have hU : U vacuum = 0 := by
    dsimp [U]
    rw [starPlus_vacuum, starPlus_vacuum]
    simp
  have hD : D vacuum = (2 : ℂ) • basisVector (oneExcitation 0) +
      (2 : ℂ) • basisVector (oneExcitation y) := by
    dsimp [D]
    rw [starMinus_vacuum, starMinus_vacuum]
  have hU0 : U (basisVector (oneExcitation 0)) = (2 : ℂ) • vacuum := by
    dsimp [U]
    rw [starPlus_oneExcitation, starPlus_oneExcitation]
    simp [hy]
  have hUy : U (basisVector (oneExcitation y)) = (2 : ℂ) • vacuum := by
    dsimp [U]
    rw [starPlus_oneExcitation, starPlus_oneExcitation]
    simp [hy, Ne.symm hy]
  have hZZ : Z (Z vacuum) = (16 : ℂ) • vacuum := by
    rw [hZ, map_smul, hZ]
    module
  have hUD : U (D vacuum) = (8 : ℂ) • vacuum := by
    rw [hD, map_add, map_smul, map_smul, hU0, hUy]
    module
  have hDU : D (U vacuum) = 0 := by rw [hU]; simp
  have hCasimir : starCasimir j = Z * Z + (1 / 2 : ℂ) • (U * D + D * U) :=
    starCasimir_formula j
  rw [hCasimir, casimirFormula_apply, hZZ, hUD, hDU]
  module

private lemma projector_fixes_vacuum (j : Fin 4) :
    ((Module.End.eigenspace (starCasimir j) 20).starProjection) vacuum =
      vacuum := by
  apply (Submodule.starProjection_eq_self_iff).2
  change vacuum ∈ (starCasimir j).eigenspace 20
  rw [Module.End.mem_eigenspace_iff]
  exact starCasimir_vacuum j

private lemma starHamiltonian_vacuum :
    starHamiltonian vacuum = (4 : ℂ) • vacuum := by
  calc
    starHamiltonian vacuum = ∑ j : Fin 4, vacuum := by
      simp [starHamiltonian, projector_fixes_vacuum]
    _ = (4 : ℂ) • vacuum := by
      simp only [Finset.sum_const, Finset.card_fin]
      exact (Nat.cast_smul_eq_nsmul ℂ 4 vacuum).symm

private lemma vacuum_ne_zero : vacuum ≠ 0 := by
  intro h
  have h' := congrFun (congrArg WithLp.ofLp h) zeroConfig
  have h1 : (1 : ℂ) = 0 := by
    simpa [vacuum, basisVector, zeroConfig] using h'
  exact one_ne_zero h1

theorem main : AKLT.Blueprint.Q.StarWitnessStatement := by
  unfold AKLT.Blueprint.Q.StarWitnessStatement
  rw [Module.End.hasEigenvalue_iff, Submodule.ne_bot_iff]
  refine ⟨vacuum, ?_, vacuum_ne_zero⟩
  rw [Module.End.mem_eigenspace_iff]
  exact starHamiltonian_vacuum

end AKLT.W.Q017
