module
public import AKLT.Blueprint.Q.NodesSplits
public import AKLT.Uniq.SpinCoordinates

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Challenge AKLT.Defs AKLT.Blueprint.Q

namespace AKLT.W.Q037

variable {L N : Size}

def starSites (x : Site L N) : Fin 5 → Site L N := fun i =>
  if i = 0 then x else if i = 1 then (x.1 + 1, x.2) else
  if i = 2 then (x.1 - 1, x.2) else if i = 3 then (x.1, x.2 + 1) else
  (x.1, x.2 - 1)

def starPicked (x : Site L N) (y : Site L N) : Prop := ∃ i, starSites x i = y

def starSpectators (x : Site L N) := {y : Site L N // ¬ starPicked x y}
private noncomputable instance starSpectatorsFintype (x : Site L N) : Fintype (starSpectators x) := by
  classical
  letI : Fintype (Site L N) := inferInstance
  letI : Finite (starSpectators x) := Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _
private noncomputable instance starSpectatorsDecEq (x : Site L N) : DecidableEq (starSpectators x) :=
  Classical.decEq _

abbrev StarCoordinates := Fin 5 → Fin 5
abbrev StarLocal := EuclideanSpace ℂ StarCoordinates

private theorem zmod_two_ne_zero (m : Size) : (2 : ZMod m.val) ≠ 0 := by
  intro h
  have hmod : 2 % m.val = 0 % m.val :=
    (ZMod.natCast_eq_natCast_iff 2 0 m.val).mp (by simpa using h)
  have hlt : 2 < m.val := by have := m.property; omega
  rw [Nat.mod_eq_of_lt hlt, Nat.zero_mod] at hmod
  omega

private theorem zmod_one_ne_zero {m : Size} : (1 : ZMod m.val) ≠ 0 := by
  intro h
  have htwo : (2 : ZMod m.val) = 0 := by
    calc
      (2 : ZMod m.val) = 1 + 1 := by norm_num
      _ = 0 := by rw [h]; norm_num
  exact zmod_two_ne_zero m htwo

private theorem zmod_self_ne_add_one {m : Size} (z : ZMod m.val) : z ≠ z + 1 := by
  intro h
  have hx : z + 0 = z + 1 := by simpa using h
  have hc : (0 : ZMod m.val) = 1 := add_left_cancel hx
  exact zmod_one_ne_zero (m := m) hc.symm

private theorem zmod_self_ne_sub_one {m : Size} (z : ZMod m.val) : z ≠ z - 1 := by
  intro h
  have hh := congrArg (fun w : ZMod m.val => w + 1) h
  have hx : 1 + z = 0 + z := by simpa [add_comm] using hh
  have hc : (1 : ZMod m.val) = 0 := add_right_cancel hx
  exact zmod_one_ne_zero (m := m) hc

private theorem zmod_add_one_ne_sub_one {m : Size} (z : ZMod m.val) : z + 1 ≠ z - 1 := by
  intro h
  have hh := congrArg (fun w : ZMod m.val => w + 1) h
  have hh' := congrArg (fun w : ZMod m.val => w - z) hh
  have htwo : (2 : ZMod m.val) = 0 := by
    calc
      (2 : ZMod m.val) = (z + 1 + 1) - z := by ring
      _ = (z - 1 + 1) - z := hh'
      _ = 0 := by simp
  exact zmod_two_ne_zero m htwo

private theorem zmod_sub_one_ne_add_one {m : Size} (z : ZMod m.val) : z - 1 ≠ z + 1 :=
  Ne.symm (zmod_add_one_ne_sub_one z)

theorem starSites_injective (x : Site L N) : Function.Injective (starSites x) := by
  intro i j hij
  rcases x with ⟨a, b⟩
  fin_cases i <;> fin_cases j <;>
    simp_all [starSites, zmod_one_ne_zero, zmod_self_ne_sub_one,
      zmod_add_one_ne_sub_one, zmod_sub_one_ne_add_one]

private def starRangeEquiv (x : Site L N) : Fin 5 ≃ {y : Site L N // starPicked x y} :=
  Equiv.ofBijective (fun i => ⟨starSites x i, ⟨i, rfl⟩⟩) (by
    constructor
    · intro i j h
      exact starSites_injective x (congrArg Subtype.val h)
    · rintro ⟨y, i, rfl⟩
      exact ⟨i, rfl⟩)

private def starSiteEquiv (x : Site L N) : (Fin 5 ⊕ starSpectators x) ≃ Site L N := by
  classical
  exact (Equiv.sumCongr (starRangeEquiv x) (Equiv.refl _)).trans (Equiv.sumCompl (starPicked x))

private theorem starSiteEquiv_inl (x : Site L N) (i : Fin 5) :
    starSiteEquiv x (Sum.inl i) = starSites x i := by
  classical
  change (Equiv.sumCompl (starPicked x) (Sum.inl (starRangeEquiv x i))) = _
  rfl

private theorem starSiteEquiv_inr (x : Site L N) (y : starSpectators x) :
    starSiteEquiv x (Sum.inr y) = y.val := by
  classical
  change (Equiv.sumCompl (starPicked x) (Sum.inr y)) = _
  rfl

private def starConfigSplit (x : Site L N) : Configuration L N ≃
    StarCoordinates × (starSpectators x → Fin 5) := by
  classical
  exact (Equiv.piCongrLeft (fun _ : Site L N => Fin 5) (starSiteEquiv x)).symm.trans
    (Equiv.sumPiEquivProdPi (fun _ : Fin 5 ⊕ starSpectators x => Fin 5))

private theorem starConfigSplit_local (x : Site L N) (σ : Configuration L N) (i : Fin 5) :
    (starConfigSplit x σ).1 i = σ (starSites x i) := by
  classical
  change (Equiv.sumPiEquivProdPi (fun _ : Fin 5 ⊕ starSpectators x => Fin 5)
    ((Equiv.piCongrLeft (fun _ : Site L N => Fin 5) (starSiteEquiv x)).symm σ)).1 i = _
  simp [Equiv.sumPiEquivProdPi, starSiteEquiv_inl]

private theorem starConfigSplit_spectator (x : Site L N) (σ : Configuration L N)
    (y : starSpectators x) : (starConfigSplit x σ).2 y = σ y.val := by
  classical
  change (Equiv.sumPiEquivProdPi (fun _ : Fin 5 ⊕ starSpectators x => Fin 5)
    ((Equiv.piCongrLeft (fun _ : Site L N => Fin 5) (starSiteEquiv x)).symm σ)).2 y = _
  simp [Equiv.sumPiEquivProdPi, starSiteEquiv_inr]

private abbrev StarSpectatorAssignments (x : Site L N) := starSpectators x → Fin 5
private def starChartIndex (x : Site L N) : Configuration L N ≃
    Fin (Fintype.card (StarSpectatorAssignments x)) × StarCoordinates := by
  classical
  exact (starConfigSplit x).trans
    ((Equiv.prodCongr (Equiv.refl StarCoordinates) (Fintype.equivFin _)).trans
      (Equiv.prodComm _ _))

private def starChartIso (x : Site L N) :
    Hilbert L N ≃ₗᵢ[ℂ] EuclideanSpace ℂ
      (Fin (Fintype.card (StarSpectatorAssignments x)) × StarCoordinates) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (starChartIndex x)

private theorem starChartIso_apply (x : Site L N) (ψ : Hilbert L N)
    (r : Fin (Fintype.card (StarSpectatorAssignments x))) (s : StarCoordinates) :
    starChartIso x ψ (r, s) = ψ ((starChartIndex x).symm (r, s)) := by
  simp [starChartIso, LinearIsometryEquiv.piLpCongrLeft]

private theorem starChartIndex_local (x : Site L N) (σ : Configuration L N) (i : Fin 5) :
    (starChartIndex x σ).2 i = σ (starSites x i) := by
  classical
  simp [starChartIndex, Equiv.prodCongr_apply, Equiv.prodComm_apply,
    starConfigSplit_local]

private theorem starChartIndex_spectator (x : Site L N) (σ : Configuration L N)
    (y : starSpectators x) :
    (Fintype.equivFin (StarSpectatorAssignments x)).symm ((starChartIndex x σ).1) y =
      (starConfigSplit x σ).2 y := by
  classical
  simp [starChartIndex, Equiv.prodCongr_apply, Equiv.prodComm_apply]

private theorem starChartIndex_decode_local (x : Site L N)
    (r : Fin (Fintype.card (StarSpectatorAssignments x))) (s : StarCoordinates) (i : Fin 5) :
    (starChartIndex x).symm (r, s) (starSites x i) = s i := by
  have h := starChartIndex_local x ((starChartIndex x).symm (r, s)) i
  simpa using h.symm

private theorem starConfigSplit_update_local (x : Site L N) (σ : Configuration L N)
    (i : Fin 5) (k : Fin 5) :
    starConfigSplit x (Function.update σ (starSites x i) k) =
      (Function.update (starConfigSplit x σ).1 i k, (starConfigSplit x σ).2) := by
  apply Prod.ext
  · funext j
    by_cases h : i = j
    · subst j
      simp [starConfigSplit_local]
    · have hne : starSites x i ≠ starSites x j := fun heq => h (starSites_injective x heq)
      change Function.update σ (starSites x i) k (starSites x j) =
        Function.update (starConfigSplit x σ).1 i k j
      rw [Function.update_of_ne (Ne.symm h), starConfigSplit_local x σ j,
        Function.update_of_ne (Ne.symm hne)]
  · funext y
    have hne : starSites x i ≠ y.val := fun heq => y.property ⟨i, heq⟩
    change Function.update σ (starSites x i) k y.val = (starConfigSplit x σ).2 y
    rw [starConfigSplit_spectator x σ y, Function.update_of_ne (Ne.symm hne)]

private theorem starChartIndex_update_local (x : Site L N) (σ : Configuration L N)
    (i : Fin 5) (k : Fin 5) :
    starChartIndex x (Function.update σ (starSites x i) k) =
      ((starChartIndex x σ).1, Function.update (starChartIndex x σ).2 i k) := by
  classical
  simp [starChartIndex, starConfigSplit_update_local, Equiv.prodCongr_apply,
    Equiv.prodComm_apply]

private theorem starChartIndex_decode_update (x : Site L N)
    (r : Fin (Fintype.card (StarSpectatorAssignments x))) (s : StarCoordinates)
    (i : Fin 5) (k : Fin 5) :
    (starChartIndex x).symm (r, Function.update s i k) =
      Function.update ((starChartIndex x).symm (r, s)) (starSites x i) k := by
  apply (starChartIndex x).injective
  rw [starChartIndex_update_local]
  simp

private theorem starAtSite_apply (A : Matrix (Fin 5) (Fin 5) ℂ) (i : Fin 5)
    (v : StarLocal) (s : StarCoordinates) :
    starAtSite A i v s = ∑ k : Fin 5, A (s i) k * v (Function.update s i k) := by
  classical
  change (∑ t : StarCoordinates,
    (if ∀ y, y ≠ i → s y = t y then A (s i) (t i) else 0) * v t) = _
  symm
  apply Fintype.sum_of_injective (Function.update s i) (Function.update_injective s i)
  · intro t ht
    have hoff : ¬ ∀ y, y ≠ i → s y = t y := by
      intro h
      apply ht
      refine ⟨t i, ?_⟩
      funext y
      by_cases hy : y = i
      · subst y
        simp
      · simp [Function.update_of_ne hy, h y hy]
    rw [ite_eq_right hoff, zero_mul]
  · intro k
    have hoff : ∀ y, y ≠ i → s y = Function.update s i k y := by
      intro y hy
      simp [Function.update_of_ne hy]
    rw [ite_eq_left hoff, Function.update_self]

private theorem starChartIso_atSite (x : Site L N) (A : Matrix (Fin 5) (Fin 5) ℂ)
    (i : Fin 5) (ψ : Hilbert L N)
    (r : Fin (Fintype.card (StarSpectatorAssignments x))) (s : StarCoordinates) :
    starChartIso x (atSite A (starSites x i) ψ) (r, s) =
      starAtSite A i (WithLp.toLp 2 (fun t => starChartIso x ψ (r, t))) s := by
  rw [starChartIso_apply, AKLT.Uniq.atSite_apply, starChartIndex_decode_local]
  rw [starAtSite_apply]
  apply Finset.sum_congr rfl
  intro k hk
  rw [starChartIso_apply, starChartIndex_decode_update]


private def starLeaf (j : Fin 4) : Fin 5 := ⟨j.val + 1, by have := j.isLt; omega⟩

private theorem onBond_starEdge (A : Matrix (Fin 5) (Fin 5) ℂ) (x : Site L N) (j : Fin 4) :
    onBond A (starEdge x j) =
      atSite A (starSites x 0) + atSite A (starSites x (starLeaf (L := L) (N := N) j)) := by
  fin_cases j <;> simp [onBond, starEdge, starSites, starLeaf, nextSite, add_comm]

private abbrev StarMultiplicity (x : Site L N) := Fintype.card (StarSpectatorAssignments x)

private def chartSlice (x : Site L N) (ψ : Hilbert L N) (r : Fin (StarMultiplicity x)) : StarLocal :=
  WithLp.toLp 2 (fun s => starChartIso x ψ (r, s))

private def ChartTransports (x : Site L N) (T : Module.End ℂ (Hilbert L N))
    (S : Module.End ℂ StarLocal) : Prop :=
  ∀ ψ r s, starChartIso x (T ψ) (r, s) = S (chartSlice x ψ r) s

private theorem chartTransports_add (x : Site L N)
    {T₁ T₂ : Module.End ℂ (Hilbert L N)} {S₁ S₂ : Module.End ℂ StarLocal}
    (h₁ : ChartTransports x T₁ S₁) (h₂ : ChartTransports x T₂ S₂) :
    ChartTransports x (T₁ + T₂) (S₁ + S₂) := by
  intro ψ r s
  change starChartIso x (T₁ ψ + T₂ ψ) (r, s) =
    (S₁ (chartSlice x ψ r) + S₂ (chartSlice x ψ r)) s
  rw [map_add, PiLp.add_apply, h₁ ψ r s, h₂ ψ r s, PiLp.add_apply]

private theorem chartTransports_smul (x : Site L N) (c : ℂ)
    {T : Module.End ℂ (Hilbert L N)} {S : Module.End ℂ StarLocal}
    (h : ChartTransports x T S) : ChartTransports x (c • T) (c • S) := by
  intro ψ r s
  change starChartIso x (c • T ψ) (r, s) = (c • S) (chartSlice x ψ r) s
  rw [map_smul, PiLp.smul_apply, h ψ r s, LinearMap.smul_apply, PiLp.smul_apply]

private theorem chartTransports_mul (x : Site L N)
    {T₁ T₂ : Module.End ℂ (Hilbert L N)} {S₁ S₂ : Module.End ℂ StarLocal}
    (h₁ : ChartTransports x T₁ S₁) (h₂ : ChartTransports x T₂ S₂) :
    ChartTransports x (T₁ * T₂) (S₁ * S₂) := by
  intro ψ r s
  change starChartIso x (T₁ (T₂ ψ)) (r, s) = (S₁ * S₂) (chartSlice x ψ r) s
  rw [h₁]
  have hslice : chartSlice x (T₂ ψ) r = S₂ (chartSlice x ψ r) := by
    ext t
    exact h₂ ψ r t
  rw [hslice, Module.End.mul_apply]

private theorem chartTransports_onBond (x : Site L N) (j : Fin 4)
    (A : Matrix (Fin 5) (Fin 5) ℂ) :
    ChartTransports x (onBond A (starEdge x j))
      (starAtSite A 0 + starAtSite A (starLeaf (L := L) (N := N) j)) := by
  intro ψ r s
  rw [onBond_starEdge (L := L) (N := N) A x j]
  change starChartIso x
      (atSite A (starSites x 0) ψ + atSite A (starSites x (starLeaf (L := L) (N := N) j)) ψ)
      (r, s) = _
  rw [map_add, PiLp.add_apply, starChartIso_atSite, starChartIso_atSite,
    LinearMap.add_apply, PiLp.add_apply]
  rfl

private theorem starCasimir_formula (j : Fin 4) :
    starCasimir j =
      (starAtSite spinZ 0 + starAtSite spinZ (starLeaf (L := L) (N := N) j)) *
        (starAtSite spinZ 0 + starAtSite spinZ (starLeaf (L := L) (N := N) j)) +
      (1 / 2 : ℂ) •
        ((starAtSite spinPlus 0 + starAtSite spinPlus (starLeaf (L := L) (N := N) j)) *
          (starAtSite spinMinus 0 + starAtSite spinMinus (starLeaf (L := L) (N := N) j)) +
         (starAtSite spinMinus 0 + starAtSite spinMinus (starLeaf (L := L) (N := N) j)) *
          (starAtSite spinPlus 0 + starAtSite spinPlus (starLeaf (L := L) (N := N) j))) := by
  refine (starCasimir.eq_1 j).trans ?_
  exact congrArg₂ (fun z y : Fin 5 =>
    (starAtSite spinZ z + starAtSite spinZ y) *
      (starAtSite spinZ z + starAtSite spinZ y) +
    (1 / 2 : ℂ) •
      ((starAtSite spinPlus z + starAtSite spinPlus y) *
        (starAtSite spinMinus z + starAtSite spinMinus y) +
       (starAtSite spinMinus z + starAtSite spinMinus y) *
        (starAtSite spinPlus z + starAtSite spinPlus y))) (Fin.ext rfl) (Fin.ext rfl)


private theorem chartTransports_starCasimir (x : Site L N) (j : Fin 4) :
    ChartTransports x (bondCasimir (starEdge x j)) (starCasimir j) := by
  let Z : Module.End ℂ (Hilbert L N) := onBond spinZ (starEdge x j)
  let U : Module.End ℂ (Hilbert L N) := onBond spinPlus (starEdge x j)
  let D : Module.End ℂ (Hilbert L N) := onBond spinMinus (starEdge x j)
  let Z' : Module.End ℂ StarLocal := starAtSite spinZ 0 + starAtSite spinZ (starLeaf (L := L) (N := N) j)
  let U' : Module.End ℂ StarLocal := starAtSite spinPlus 0 + starAtSite spinPlus (starLeaf (L := L) (N := N) j)
  let D' : Module.End ℂ StarLocal := starAtSite spinMinus 0 + starAtSite spinMinus (starLeaf (L := L) (N := N) j)
  have hZ : ChartTransports x Z Z' := chartTransports_onBond x j spinZ
  have hU : ChartTransports x U U' := chartTransports_onBond x j spinPlus
  have hD : ChartTransports x D D' := chartTransports_onBond x j spinMinus
  have hZZ := chartTransports_mul x hZ hZ
  have hUD := chartTransports_mul x hU hD
  have hDU := chartTransports_mul x hD hU
  have hMix := chartTransports_add x hUD hDU
  have hScaled := chartTransports_smul x (1 / 2 : ℂ) hMix
  have hAll := chartTransports_add x hZZ hScaled
  -- Rewrite the operators before evaluating them on a slice.  Conversion
  -- underneath the concrete star Casimir would unfold a 3125-coordinate sum.
  have hBond : bondCasimir (starEdge x j) = Z * Z + (1 / 2 : ℂ) • (U * D + D * U) := rfl
  have hStar : starCasimir j = Z' * Z' + (1 / 2 : ℂ) • (U' * D' + D' * U') :=
    starCasimir_formula (L := L) (N := N) j
  rw [hBond, hStar]
  exact hAll

theorem main : AKLT.Blueprint.Q.StarCasimirChartStatement := by
  intro L N x
  let n := Fintype.card (StarSpectatorAssignments x)
  let U := starChartIso x
  refine ⟨n, U, ?_⟩
  intro j ψ r s
  have hSlice : chartSlice x ψ r = WithLp.toLp 2 (fun t => U ψ (r, t)) := rfl
  exact (chartTransports_starCasimir x j ψ r s).trans
    (congrArg (fun v : StarLocal => starCasimir j v s) hSlice)

#print axioms main

end AKLT.W.Q037
