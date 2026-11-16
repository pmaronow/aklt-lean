import AKLT.Blueprint.Gap.NodesPeriodic

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000
open AKLT.Defs AKLT.Challenge
namespace AKLT.W.GAP038
open AKLT.Blueprint.Gap

private lemma square_shift_mem (M : ℕ) (z : Plane) (dx dy : ℤ)
    (hz : z ∈ square (0, 0) M)
    (hdx : -1 ≤ dx ∧ dx ≤ 1) (hdy : -1 ≤ dy ∧ dy ≤ 1) :
    (z.1 + dx, z.2 + dy) ∈ square (0, 0) (M + 1) := by
  have hz' : z.1 ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) ∧
      z.2 ∈ Finset.Icc (-(M : ℤ)) (M : ℤ) := by
    simpa [square] using (Finset.mem_product.mp hz)
  have h1 := Finset.mem_Icc.mp hz'.1
  have h2 := Finset.mem_Icc.mp hz'.2
  apply Finset.mem_product.mpr
  constructor
  · apply Finset.mem_Icc.mpr
    constructor <;> omega
  · apply Finset.mem_Icc.mpr
    constructor <;> omega

private lemma torusSquare_shift_mem {L N : Size} (M : ℕ) (a x : Site L N)
    (dx dy : ℤ) (hx : x ∈ torusSquare L N M a)
    (hdx : -1 ≤ dx ∧ dx ≤ 1) (hdy : -1 ≤ dy ∧ dy ≤ 1) :
    (x.1 + (dx : ZMod L.val), x.2 + (dy : ZMod N.val)) ∈
      torusSquare L N (M + 1) a := by
  classical
  simp only [torusSquare, Finset.mem_image] at hx ⊢
  rcases hx with ⟨z, hz, rfl⟩
  refine ⟨(z.1 + dx, z.2 + dy), square_shift_mem M z dx dy hz hdx hdy, ?_⟩
  ext <;> simp [reduction, add_assoc]

private lemma torusSquare_east_mem_halo {L N : Size} (M : ℕ) (a : Site L N)
    {x : Site L N} (hx : x ∈ torusSquare L N M a) :
    (x.1 + 1, x.2) ∈ torusSquare L N (M+1) a := by
  simpa using torusSquare_shift_mem M a x 1 0 hx (by norm_num) (by norm_num)

private lemma torusSquare_west_mem_halo {L N : Size} (M : ℕ) (a : Site L N)
    {x : Site L N} (hx : x ∈ torusSquare L N M a) :
    (x.1 - 1, x.2) ∈ torusSquare L N (M+1) a := by
  simpa [sub_eq_add_neg] using torusSquare_shift_mem M a x (-1) 0 hx (by norm_num) (by norm_num)

private lemma torusSquare_north_mem_halo {L N : Size} (M : ℕ) (a : Site L N)
    {x : Site L N} (hx : x ∈ torusSquare L N M a) :
    (x.1, x.2 + 1) ∈ torusSquare L N (M+1) a := by
  simpa using torusSquare_shift_mem M a x 0 1 hx (by norm_num) (by norm_num)

private lemma torusSquare_south_mem_halo {L N : Size} (M : ℕ) (a : Site L N)
    {x : Site L N} (hx : x ∈ torusSquare L N M a) :
    (x.1, x.2 - 1) ∈ torusSquare L N (M+1) a := by
  simpa [sub_eq_add_neg] using torusSquare_shift_mem M a x 0 (-1) hx (by norm_num) (by norm_num)


private lemma local_agree_of_halo_agree {L N : Size} (M : ℕ) (a : Site L N)
    (σ τ : TorusConfiguration L N)
    (hagree : AgreeOn (torusHalo L N M a \ torusSquare L N M a) σ τ) :
    ∀ z ∈ ((torusSquare L N M a).biUnion torusNeighbours) \ torusSquare L N M a,
      σ z = τ z := by
  intro z hz
  rcases Finset.mem_sdiff.mp hz with ⟨hzNeighbors, hzOutside⟩
  rcases Finset.mem_biUnion.mp hzNeighbors with ⟨x, hx, hzx⟩
  have hzHalo : z ∈ torusSquare L N (M + 1) a := by
    simp only [torusNeighbours, Finset.mem_insert, Finset.mem_singleton] at hzx
    rcases hzx with h | h | h | h
    · rw [h]
      exact torusSquare_east_mem_halo M a hx
    · rw [h]
      exact torusSquare_west_mem_halo M a hx
    · rw [h]
      exact torusSquare_north_mem_halo M a hx
    · rw [h]
      exact torusSquare_south_mem_halo M a hx
  have hzHalo' : z ∈ torusHalo L N M a := by
    change z ∈ torusSquare L N (M + 1) a
    exact hzHalo
  exact hagree z (Finset.mem_sdiff.mpr ⟨hzHalo', hzOutside⟩)

private lemma marginal_decEq_irrel {Ω Ξ : Type} [Fintype Ω]
    (p : Weight Ω) (f : Ω → Ξ) (d₁ d₂ : DecidableEq Ξ) :
    @marginal Ω Ξ ‹Fintype Ω› d₁ p f = @marginal Ω Ξ ‹Fintype Ω› d₂ p f := by
  funext z
  unfold marginal
  apply Finset.sum_congr rfl
  intro x hx
  by_cases h : f x = z <;> simp [h]

private lemma blockLaw_eq_conditionalTorusLaw {L N : Size} (κ : Site L N → Fin 3)
    (U : Finset (Site L N)) (σ : TorusConfiguration L N) :
    blockLaw (torusLaw L N κ) U σ = AKLT.Defs.conditionalTorusLaw L N κ U σ := by
  classical
  unfold blockLaw fibre restrict AKLT.Defs.conditionalTorusLaw
  apply marginal_decEq_irrel

theorem main : AKLT.Blueprint.Gap.TorusRangeTransferStatement := by
  unfold AKLT.Blueprint.Gap.TorusRangeTransferStatement
  intro L N κ hlocal M _hM
  change ∀ a σ τ, AgreeOn (torusHalo L N M a \ torusSquare L N M a) σ τ →
    blockLaw (torusLaw L N κ) (torusSquare L N M a) σ =
      blockLaw (torusLaw L N κ) (torusSquare L N M a) τ
  intro a σ τ hagree
  let U := torusSquare L N M a
  have hlocalAgree := local_agree_of_halo_agree M a σ τ hagree
  have hconditional := hlocal U σ τ hlocalAgree
  rw [blockLaw_eq_conditionalTorusLaw κ U σ,
    blockLaw_eq_conditionalTorusLaw κ U τ]
  exact hconditional

end AKLT.W.GAP038
