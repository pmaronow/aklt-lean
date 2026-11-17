module
public import AKLT.W.WIN052.Moments

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN052

/-- The tensor calculation on any subset of the four physical neighbours. -/
theorem neighbour_moment (hM : AKLT.Blueprint.Top.MomentsStatement)
    (x : Plane) (V : Finset Plane) (hV : V ⊆ neighbours x) (n : Plane → Vec3) :
    moment (fun v => ∏ z ∈ V, (1 + dot v (n z))) = removalPolynomial x V n := by
  classical
  have hfilter : V = (neighbours x).filter (fun z => z ∈ V) := by
    ext z
    simp only [Finset.mem_filter]
    exact ⟨fun hz => ⟨hV hz, hz⟩, And.right⟩
  have hm := fourFactors hM
    (if x + Compass.east.step ∈ V then n (x + Compass.east.step) else 0)
    (if x + Compass.west.step ∈ V then n (x + Compass.west.step) else 0)
    (if x + Compass.south.step ∈ V then n (x + Compass.south.step) else 0)
    (if x + Compass.north.step ∈ V then n (x + Compass.north.step) else 0)
  by_cases he : x + Compass.east.step ∈ V <;>
    by_cases hw : x + Compass.west.step ∈ V <;>
    by_cases hs : x + Compass.south.step ∈ V <;>
    by_cases hn : x + Compass.north.step ∈ V
  all_goals
    simp only [neighbours_explicit, Finset.filter_insert, Finset.filter_singleton,
      he, hw, hs, hn, ite_true, ite_false] at hfilter
    simp only [he, hw, hs, hn, ite_true, ite_false, dot_zero, zero_dot,
      zero_add, add_zero, zero_mul, mul_zero, one_mul, mul_one] at hm
    rw [hfilter]
    convert hm using 1
    · congr 1 <;> funext v
      all_goals simp [Compass.step, Prod.ext_iff] <;> ring
    · simp [removalPolynomial, pairSum, quartic, Compass.step, Prod.ext_iff, dot_symm]
      <;> ring

end AKLT.W.WIN052
