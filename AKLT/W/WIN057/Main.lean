module
public import AKLT.Blueprint.Win.NodesRemoval

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Blueprint.Win

namespace AKLT.W.WIN057

private theorem latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  unfold latticeDist
  have hx : (x.1 - z.1).natAbs ≤ (x.1 - y.1).natAbs + (y.1 - z.1).natAbs := by
    calc
      (x.1 - z.1).natAbs = ((x.1 - y.1) + (y.1 - z.1)).natAbs := by congr 1; ring
      _ ≤ (x.1 - y.1).natAbs + (y.1 - z.1).natAbs := Int.natAbs_add_le _ _
  have hy : (x.2 - z.2).natAbs ≤ (x.2 - y.2).natAbs + (y.2 - z.2).natAbs := by
    calc
      (x.2 - z.2).natAbs = ((x.2 - y.2) + (y.2 - z.2)).natAbs := by congr 1; ring
      _ ≤ (x.2 - y.2).natAbs + (y.2 - z.2).natAbs := Int.natAbs_add_le _ _
  omega

private theorem adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x := by
  have h₁ : (y.1 - x.1).natAbs = (x.1 - y.1).natAbs := by
    rw [show y.1 - x.1 = -(x.1 - y.1) by ring, Int.natAbs_neg]
  have h₂ : (y.2 - x.2).natAbs = (x.2 - y.2).natAbs := by
    rw [show y.2 - x.2 = -(x.2 - y.2) by ring, Int.natAbs_neg]
  unfold Adjacent latticeDist at *
  rw [h₁, h₂]
  exact h

private theorem adjacent_of_mem_neighbours {x z : Plane} (h : z ∈ neighbours x) :
    Adjacent x z := by
  rcases Finset.mem_image.mp h with ⟨d, -, rfl⟩
  cases d <;> simp [Adjacent, latticeDist, Compass.step]

private theorem neighbours_pair_dist_two {x z w : Plane}
    (hz : z ∈ neighbours x) (hw : w ∈ neighbours x) (hne : z ≠ w) :
    latticeDist z w = 2 := by
  rcases Finset.mem_image.mp hz with ⟨d, -, rfl⟩
  rcases Finset.mem_image.mp hw with ⟨e, -, rfl⟩
  cases d <;> cases e <;> simp_all [neighbours, latticeDist, Compass.step]

private theorem boundaryDepth_le_dist_add (G : Finset Plane) (x s : Plane) :
    boundaryDepth G x ≤ (latticeDist x s : ℕ∞) + boundaryDepth G s := by
  unfold boundaryDepth setDistance
  rw [ENat.add_iInf]
  apply le_iInf
  intro y
  calc
    (⨅ y : {y : Plane // y ∉ G}, (latticeDist x y.val : ℕ∞)) ≤
        (latticeDist x y.val : ℕ∞) := iInf_le _ y
    _ ≤ (latticeDist x s : ℕ∞) + (latticeDist s y.val : ℕ∞) := by
      exact_mod_cast latticeDist_triangle x s y.val

private theorem protected_distance_lower (G : Finset Plane) (x z : Plane)
    (hxz : Adjacent x z) :
    ∀ s ∈ protectedSites G, depthShift G x ≤ latticeDist z s := by
  intro s hs
  have hbs : boundaryDepth G s ≤ (2 : ℕ∞) := by
    simpa [protectedSites] using (Finset.mem_filter.mp hs).2
  have hbsTop : boundaryDepth G s < ⊤ := lt_of_le_of_lt hbs (ENat.natCast_lt_top 2)
  have hdepth := boundaryDepth_le_dist_add G x s
  have hsumTop : (latticeDist x s : ℕ∞) + boundaryDepth G s < ⊤ :=
    ENat.add_lt_top.mpr ⟨ENat.natCast_lt_top _, hbsTop⟩
  have hn := ENat.toNat_le_toNat hdepth (ne_of_lt hsumTop)
  have hn' : (boundaryDepth G x).toNat ≤ latticeDist x s + (boundaryDepth G s).toNat := by
    simpa [ENat.toNat_add (ENat.natCast_ne_top _) (ne_of_lt hbsTop)] using hn
  have hbsNat : (boundaryDepth G s).toNat ≤ 2 := by
    have hh := ENat.toNat_le_toNat hbs (ENat.natCast_ne_top 2)
    simpa using hh
  have hxz' : latticeDist x z = 1 := hxz
  have hdist := latticeDist_triangle x z s
  rw [hxz'] at hdist
  unfold depthShift
  omega

private theorem depthShift_le_protected_setDistance (G : Finset Plane) (x z : Plane)
    (hxz : Adjacent x z) :
    (depthShift G x : ℕ∞) ≤
      setDistance latticeDist z (↑(protectedSites G) : Set Plane) := by
  unfold setDistance
  apply le_iInf
  intro s
  exact_mod_cast protected_distance_lower G x z hxz s.1 s.2

private theorem decay_distance_le (A θ : ℝ) (hA : 0 ≤ A) (hθ₀ : 0 < θ)
    (hθ₁ : θ < 1) (k : ℕ) (r : ℕ∞) (hkr : (k : ℕ∞) ≤ r) :
    A * decay θ r ≤ A * θ ^ k := by
  by_cases htop : r = ⊤
  · simp [decay, htop]
    positivity
  · have hk : k ≤ r.toNat := by
      have hh := ENat.toNat_le_toNat hkr htop
      simpa using hh
    have hpow : θ ^ r.toNat ≤ θ ^ k :=
      pow_le_pow_of_le_one (le_of_lt hθ₀) (le_of_lt hθ₁) hk
    simp only [decay, htop, ↓reduceIte]
    exact mul_le_mul_of_nonneg_left hpow hA

end AKLT.W.WIN057

open AKLT.W.WIN057

theorem AKLT.W.WIN057.main : AKLT.Blueprint.Win.RemovedPairResponseStatement := by
  intro A θ hP G Y τ x hstep z hz w hw hne
  rcases hstep with ⟨hY, hxGY, hdepth⟩
  have hxnot : x ∉ protectedSites G := by
    intro hp
    have hbd : boundaryDepth G x ≤ (2 : ℕ∞) := by
      simpa [protectedSites] using (Finset.mem_filter.mp hp).2
    have hgreater : (2 : ℕ∞) < boundaryDepth G x :=
      lt_of_lt_of_le (by exact_mod_cast (by norm_num : 2 < 3)) hdepth
    exact (not_le_of_gt hgreater) hbd
  have hremove : insert x Y ⊆ G \ protectedSites G := by
    intro q hq
    rcases Finset.mem_insert.mp hq with hq | hq
    · subst q
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxGY).1, hxnot⟩
    · exact hY hq
  have hz' : z ∈ survivors G Y x := hz
  have hw' : w ∈ survivors G Y x := hw
  simp only [survivors, Finset.mem_inter] at hz' hw'
  have hzx : Adjacent z x := adjacent_symm (adjacent_of_mem_neighbours hz'.1)
  have hwx : Adjacent w x := adjacent_symm (adjacent_of_mem_neighbours hw'.1)
  have hdistzw : latticeDist z w = 2 := neighbours_pair_dist_two hz'.1 hw'.1 hne
  have hresp := hP.2.2.2 G τ (insert x Y) hremove z w hz'.2 hw'.2 hdistzw
    ⟨x, Finset.mem_insert_self x Y, hzx, hwx⟩
  have hdz := depthShift_le_protected_setDistance G x z (adjacent_symm hzx)
  have hdw := depthShift_le_protected_setDistance G x w (adjacent_symm hwx)
  have hmin : (depthShift G x : ℕ∞) ≤
      min (setDistance latticeDist z (↑(protectedSites G) : Set Plane))
        (setDistance latticeDist w (↑(protectedSites G) : Set Plane)) := le_min hdz hdw
  have hdecay := decay_distance_le A θ (by linarith [hP.1]) hP.2.1 hP.2.2.1
    (depthShift G x) _ hmin
  have hresp' :
      |partMean true G (insert x Y) τ (fun n => dot (n z) (n w)) -
        partMean false G (insert x Y) τ (fun n => dot (n z) (n w))| ≤
        A * decay θ (min (setDistance latticeDist z (↑(protectedSites G) : Set Plane))
          (setDistance latticeDist w (↑(protectedSites G) : Set Plane))) := by
    simpa [partMean, partSum, pinnedExpectation, freeExpectation] using hresp
  exact hresp'.trans hdecay

#print axioms AKLT.W.WIN057.main

