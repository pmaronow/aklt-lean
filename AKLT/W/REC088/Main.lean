module
public import AKLT.Blueprint.Rec.NodesRenewal

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators Topology

namespace AKLT.W.REC088

theorem main : AKLT.Blueprint.Rec.RenewalScalarLimitStatement := by
  intro x a b ρ ha hb hρ₀ hρ₁ hbound
  let L : ℝ := b / (1 - ρ)
  have hρne : ρ ≠ 1 := ne_of_lt hρ₁
  have hden : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρne)
  have hgeom (k : ℕ) :
      (∑ j ∈ Finset.range k, ρ ^ j) = (1 - ρ ^ k) / (1 - ρ) := by
    rw [geom_sum_eq hρne k]
    field_simp [hden]; ring
  have hform (k : ℕ) :
      a * ρ ^ k + b * (∑ j ∈ Finset.range k, ρ ^ j) =
        L + ρ ^ k * (a - L) := by
    rw [hgeom k]
    dsimp [L]
    field_simp [hden]; ring
  have hpow : Filter.Tendsto (fun k : ℕ => ρ ^ k) Filter.atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ₀.le hρ₁
  have hlim : Filter.Tendsto (fun k : ℕ => L + ρ ^ k * (a - L)) Filter.atTop (𝓝 L) := by
    simpa using (hpow.mul_const (a - L)).const_add L
  refine le_of_tendsto_of_tendsto' tendsto_const_nhds hlim ?_
  intro k
  rw [← hform k]
  exact hbound k

end AKLT.W.REC088
