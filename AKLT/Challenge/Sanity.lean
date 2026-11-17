module
public import AKLT.Challenge.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

/-! Sanity statements about the concrete definitions. Unproved statements below
are propositions, with no assumed inhabitants. These elementary checks do not
prove Theorem 1.2 (`t:main`, `sec1-result.tex`). Nonvanishing is proved separately
in `AKLT.Challenge.SanityProofs`; the rank sanity statement remains unproved. -/

noncomputable section

namespace AKLT.Challenge

/-- P_e is idempotent and symmetric for the complex Hilbert inner product. -/
def PIsOrthogonalProjection (L N : Size) : Prop :=
  ∀ e : Bond L N, (P e).IsSymmetricProjection

theorem p_isOrthogonalProjection (L N : Size) : PIsOrthogonalProjection L N := by
  intro e
  exact (spin4Space e).isSymmetricProjection_starProjection

/-- The projection has exactly the specified eigenvalue-20 range. -/
def PHasCorrectRange (L N : Size) : Prop :=
  ∀ e : Bond L N, LinearMap.range (P e) = spin4Space e

theorem p_hasCorrectRange (L N : Size) : PHasCorrectRange L N := by
  intro e
  exact (spin4Space e).range_starProjection

/-- Each bond projection is positive semidefinite, including symmetry. -/
def PPositive (L N : Size) : Prop := ∀ e : Bond L N, (P e).IsPositive

theorem p_positive (L N : Size) : PPositive L N := by
  intro e
  exact (p_isOrthogonalProjection L N e).isPositive

/-- H is positive semidefinite: symmetric and Re⟪Hψ,ψ⟫ ≥ 0. -/
def HPositive (L N : Size) : Prop := (H L N).IsPositive

theorem h_positive (L N : Size) : HPositive L N := by
  exact LinearMap.isPositive_sum Finset.univ fun e _ => p_positive L N e

/-- H is self-adjoint for the usual complex Hilbert inner product. -/
def HSelfAdjoint (L N : Size) : Prop :=
  IsSelfAdjoint (H L N)

theorem h_selfAdjoint (L N : Size) : HSelfAdjoint L N := by
  exact (h_positive L N).isSelfAdjoint

/-- Every complex eigenvalue is real, so the real eigenvalue quantifier in
`MainStatementV2` covers the whole spectrum. -/
def HEigenvaluesReal (L N : Size) : Prop :=
  ∀ μ : ℂ, (H L N).HasEigenvalue μ → starRingEnd ℂ μ = μ

theorem h_eigenvaluesReal (L N : Size) : HEigenvaluesReal L N := by
  intro μ hμ
  exact (h_positive L N).isSymmetric.conj_eigenvalue_eq_self hμ

/-- The site space has dimension five, over ℂ. -/
def SiteDimension : Prop := Module.finrank ℂ V = 5

theorem site_dimension : SiteDimension := by
  simp [SiteDimension, V]

/-- The torus has LN sites. -/
def SiteCount (L N : Size) : Prop := Fintype.card (Site L N) = L.val * N.val

theorem site_count (L N : Size) : SiteCount L N := by
  simp [SiteCount, Site, ZMod.card]

/-- There are exactly 2LN bond indices; absence of repetitions is checked
separately by `BondsAreDistinct`. -/
def BondCount (L N : Size) : Prop := Fintype.card (Bond L N) = 2 * L.val * N.val

theorem bond_count (L N : Size) : BondCount L N := by
  simp [BondCount, Bond, Direction, Site, ZMod.card, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc]

/-- The Hilbert space has dimension 5^(LN), over ℂ. -/
def HilbertDimension (L N : Size) : Prop :=
  Module.finrank ℂ (Hilbert L N) = 5 ^ (L.val * N.val)

theorem hilbert_dimension (L N : Size) : HilbertDimension L N := by
  simp [HilbertDimension, Hilbert, Configuration, Site, ZMod.card]

/-- No bond is a loop (§1 assumes L,N ≥ 3). -/
def BondsHaveTwoSites (L N : Size) : Prop :=
  ∀ e : Bond L N, (bondSites e).card = 2

/-- The small positive integers used to detect loops and reversed duplicates
do not vanish modulo a permitted side length. -/
theorem small_natCast_ne_zero (L : Size) (k : ℕ) (hk : 0 < k) (hL : k < L.val) :
    (k : ZMod L.val) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt hk hL

theorem nextSite_ne {L N : Size} (x : Site L N) (d : Direction) :
    nextSite x d ≠ x := by
  have hL := small_natCast_ne_zero L 1 (by omega) (by have := L.property; omega)
  have hN := small_natCast_ne_zero N 1 (by omega) (by have := N.property; omega)
  intro h
  by_cases hd : d = 0
  · apply hL
    simpa [nextSite, hd] using congrArg Prod.fst h
  · apply hN
    simpa [nextSite, hd] using congrArg Prod.snd h

theorem bonds_haveTwoSites (L N : Size) : BondsHaveTwoSites L N := by
  intro e
  exact Finset.card_pair (Ne.symm (nextSite_ne e.1 e.2))

/-- No two oriented indices denote the same unoriented bond. -/
def BondsAreDistinct (L N : Size) : Prop := Function.Injective (@bondSites L N)

theorem bonds_areDistinct (L N : Size) : BondsAreDistinct L N := by
  have hL1 := small_natCast_ne_zero L 1 (by omega) (by have := L.property; omega)
  have hL2 := small_natCast_ne_zero L 2 (by omega) (by have := L.property; omega)
  have hN2 := small_natCast_ne_zero N 2 (by omega) (by have := N.property; omega)
  intro ⟨x, d⟩ ⟨y, f⟩ h
  have hp : ({x, nextSite x d} : Set (Site L N)) = {y, nextSite y f} := by
    simpa [bondSites] using
      congrArg (fun s : Finset (Site L N) => (s : Set (Site L N))) h
  rcases Set.pair_eq_pair_iff.mp hp with ⟨hxy, hn⟩ | ⟨hxy, hn⟩
  · subst y
    have hd : d = f := by
      fin_cases d <;> fin_cases f
      · rfl
      · exact (hL1 (by simpa [nextSite] using congrArg Prod.fst hn)).elim
      · exact (hL1 (by simpa [nextSite] using (congrArg Prod.fst hn).symm)).elim
      · rfl
    cases hd
    rfl
  · have hb : nextSite (nextSite x d) f = x := by rw [hn]; exact hxy.symm
    fin_cases d <;> fin_cases f
    · apply (hL2 _).elim
      simpa [nextSite, add_assoc, one_add_one_eq_two] using congrArg Prod.fst hb
    · exact (hL1 (by simpa [nextSite] using congrArg Prod.fst hb)).elim
    · exact (hL1 (by simpa [nextSite] using congrArg Prod.fst hb)).elim
    · apply (hN2 _).elim
      simpa [nextSite, add_assoc, one_add_one_eq_two] using congrArg Prod.snd hb

/-- The coordinate conversion in (`d:poly`, `sec3-quantum-frames.tex`) never divides by zero. -/
def BasisNormalizationNonzero (L N : Size) : Prop :=
  ∀ σ : Configuration L N,
    (∏ x : Site L N, (Real.sqrt (Nat.choose 4 (σ x).val : ℝ) : ℂ)) ≠ 0

theorem basis_normalization_nonzero (L N : Size) : BasisNormalizationNonzero L N := by
  intro σ
  apply Finset.prod_ne_zero_iff.mpr
  intro x _
  apply Complex.ofReal_ne_zero.mpr
  apply Real.sqrt_ne_zero'.mpr
  have hp : 0 < Nat.choose 4 (σ x).val := Nat.choose_pos (by have := (σ x).isLt; omega)
  exact_mod_cast hp

/-- Nonvanishing of B in Theorem 1.2 (`t:main`, `sec1-result.tex`).
Proved as `b_nonzero` in `AKLT.Challenge.SanityProofs` from the existing
polynomial integral-domain argument and its coordinate conversion. -/
def BNonzero (L N : Size) : Prop := B L N ≠ 0

/-- Unproved sanity statement: the spin-4 projector has the expected rank.
No theorem or certificate assumes this proposition. A proof still needs the
25-dimensional Casimir multiplicity and its transfer to all spectator factors. -/
def BondRank (L N : Size) : Prop :=
  ∀ e : Bond L N, Module.finrank ℂ (LinearMap.range (P e)) =
    9 * 5 ^ (L.val * N.val - 2)

/-- An auxiliary arithmetic check: even permitted sizes are unbounded.
Theorem 1.2 itself allows every parity. -/
def EvenSizesUnbounded : Prop :=
  ∀ K : ℕ, ∃ L : Size, Even L.val ∧ K ≤ L.val

theorem even_sizes_unbounded : EvenSizesUnbounded := by
  intro K
  refine ⟨⟨2 * (K + 3), by omega⟩, ?_, ?_⟩
  · change Even (2 * (K + 3))
    exact ⟨K + 3, by omega⟩
  · dsimp
    omega

/-- The smallest even torus in the paper's domain. -/
def four : Size := ⟨4, by decide⟩

/-- A concrete non-degeneracy check: 16 sites, 32 bonds, dimension 5^16. -/
def FourByFourSizes : Prop :=
  Fintype.card (Site four four) = 16 ∧
  Fintype.card (Bond four four) = 32 ∧
  Module.finrank ℂ (Hilbert four four) = 5 ^ 16

theorem four_by_four_sizes : FourByFourSizes := by
  exact ⟨site_count four four, bond_count four four, hilbert_dimension four four⟩

/-- Unproved combined sanity statement, assumed by no theorem or certificate.
The bond checks and B ≠ 0 are proved; the rank assertion remains open. -/
def FourByFourNondegenerate : Prop :=
  BondsHaveTwoSites four four ∧ BondsAreDistinct four four ∧
    BNonzero four four ∧
    ∀ e : Bond four four, Module.finrank ℂ (LinearMap.range (P e)) = 9 * 5 ^ 14

#print axioms p_isOrthogonalProjection
#print axioms p_hasCorrectRange
#print axioms p_positive
#print axioms h_positive
#print axioms h_selfAdjoint
#print axioms h_eigenvaluesReal
#print axioms site_dimension
#print axioms site_count
#print axioms bond_count
#print axioms hilbert_dimension
#print axioms small_natCast_ne_zero
#print axioms nextSite_ne
#print axioms bonds_haveTwoSites
#print axioms bonds_areDistinct
#print axioms basis_normalization_nonzero
#print axioms even_sizes_unbounded
#print axioms four_by_four_sizes

end AKLT.Challenge
