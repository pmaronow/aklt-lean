module
public import AKLT.Blueprint.Rec.NodesRecursion

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC081

theorem setDistance_le_of_mem (x y : Plane) (S : Set Plane) (hy : y ∈ S) :
    setDistance latticeDist x S ≤ (latticeDist x y : ℕ∞) :=
  iInf_le (fun z : S => (latticeDist x z.val : ℕ∞)) ⟨y, hy⟩

/-- A rightmost point of a finite nonempty volume is in its original protected layer. -/
theorem protectedSites_nonempty (G : Finset Plane) (hG : G.Nonempty) :
    (protectedSites G).Nonempty := by
  classical
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image G Prod.fst hG
  have hout : (x.1 + 1, x.2) ∉ G := by
    intro hy
    have := hmax _ hy
    simp only at this
    omega
  refine ⟨x, Finset.mem_filter.mpr ⟨hx, ?_⟩⟩
  have hdist := setDistance_le_of_mem x (x.1 + 1, x.2) {z | z ∉ G} hout
  have hone : latticeDist x (x.1 + 1, x.2) = 1 := by
    simp [latticeDist]
  exact hdist.trans (by simp [hone])

theorem protectedDistance_finite (G : Finset Plane) (hG : G.Nonempty) (x : Plane) :
    setDistance latticeDist x (↑(protectedSites G) : Set Plane) ≠ ⊤ := by
  obtain ⟨y, hy⟩ := protectedSites_nonempty G hG
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) (setDistance_le_of_mem x y _ hy)

theorem pair_volume_nonempty (p : PairData) : p.G.Nonempty :=
  ⟨p.u, (Finset.mem_filter.mp p.pair.2.1).1⟩

/-- Both distances are finite; taking `toNat` therefore retains the lower bound. -/
theorem protectedDepthProjection (p : PairData) (d : ℕ) (hdepth : (d : ℕ∞) ≤ p.depth) :
    d ≤ protectedDistance p.G p.u ∧ d ≤ protectedDistance p.G p.v := by
  have hG := pair_volume_nonempty p
  constructor
  · exact ENat.toNat_le_toNat (le_trans hdepth (min_le_left _ _))
      (protectedDistance_finite p.G hG p.u)
  · exact ENat.toNat_le_toNat (le_trans hdepth (min_le_right _ _))
      (protectedDistance_finite p.G hG p.v)

theorem pair_interior (p : PairData) (d : ℕ) (hd : 1 ≤ d)
    (hdepth : (d : ℕ∞) ≤ p.depth) :
    p.u ∉ protectedSites p.G ∧ p.v ∉ protectedSites p.G := by
  have hpos : (0 : ℕ∞) < d := by exact_mod_cast (by omega : 0 < d)
  constructor
  · intro hu
    have hdist := setDistance_le_of_mem p.u p.u (↑(protectedSites p.G) : Set Plane) hu
    have : (d : ℕ∞) ≤ 0 := (hdepth.trans (min_le_left _ _)).trans (by
      simpa [latticeDist] using hdist)
    exact (not_le_of_gt hpos) this
  · intro hv
    have hdist := setDistance_le_of_mem p.v p.v (↑(protectedSites p.G) : Set Plane) hv
    have : (d : ℕ∞) ≤ 0 := (hdepth.trans (min_le_right _ _)).trans (by
      simpa [latticeDist] using hdist)
    exact (not_le_of_gt hpos) this

theorem latticeDist_triangle (x y z : Plane) :
    latticeDist x z ≤ latticeDist x y + latticeDist y z := by
  have h₁ := Int.natAbs_add_le (x.1 - y.1) (y.1 - z.1)
  have h₂ := Int.natAbs_add_le (x.2 - y.2) (y.2 - z.2)
  simp only [sub_add_sub_cancel] at h₁ h₂
  unfold latticeDist
  omega

theorem wordVertex_zero {n : ℕ} (u : Plane) (w : DirectionWord n) :
    wordVertex u w 0 = u := by simp [wordVertex]

theorem wordVertex_step {n : ℕ} (u : Plane) (w : DirectionWord n) (j : Fin n) :
    wordVertex u w (j.val + 1) = wordVertex u w j.val + (w j).step := by
  classical
  unfold wordVertex
  have hsum : (∑ i : Fin n, if i.val < j.val + 1 then (w i).step else 0) =
      (∑ i : Fin n, if i.val < j.val then (w i).step else 0) + (w j).step := by
    calc
      _ = ∑ i : Fin n, ((if i.val < j.val then (w i).step else 0) +
          if i = j then (w j).step else 0) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hij : i = j
        · subst i; simp
        · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
          by_cases hlt : i.val < j.val
          · have hsucc : i.val < j.val + 1 := by omega
            simp only [ite_eq_left hlt, ite_eq_left hsucc, ite_eq_right hij, add_zero]
          · have hsucc : ¬ i.val < j.val + 1 := by omega
            simp only [ite_eq_right hlt, ite_eq_right hsucc, ite_eq_right hij, add_zero]
      _ = _ := by simp [Finset.sum_add_distrib]
  rw [hsum, add_assoc]

theorem wordVertex_distance_le {n : ℕ} (u : Plane) (w : DirectionWord n) :
    ∀ j ≤ n, latticeDist u (wordVertex u w j) ≤ j := by
  intro j hj
  induction j with
  | zero => simp [wordVertex_zero, latticeDist]
  | succ j ih =>
    have hstep := wordVertex_step u w (⟨j, by omega⟩ : Fin n)
    have hone : latticeDist (wordVertex u w j) (wordVertex u w (j + 1)) = 1 := by
      rw [hstep]
      cases hw : w ⟨j, by omega⟩ <;> simp [latticeDist, Compass.step]
    have := latticeDist_triangle u (wordVertex u w j) (wordVertex u w (j + 1))
    have := ih (by omega)
    omega

theorem stopped_length_ge_distance {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (w : DirectionWord n) (hw : StoppedNetworkTrail D u (protectedSites G) w) :
    protectedDistance G u ≤ n := by
  apply ENat.toNat_le_of_le_natCast
  exact (setDistance_le_of_mem u (wordVertex u w n) _ hw.2.2.2).trans
    (by exact_mod_cast wordVertex_distance_le u w n le_rfl)

theorem adjacent_compass (u c : Plane) (h : Adjacent u c) :
    ∃ incoming : Compass, u = c + incoming.step := by
  have hcoords :
      (u.1 = c.1 + 1 ∧ u.2 = c.2) ∨ (u.1 = c.1 ∧ u.2 = c.2 + 1) ∨
      (u.1 = c.1 - 1 ∧ u.2 = c.2) ∨ (u.1 = c.1 ∧ u.2 = c.2 - 1) := by
    unfold Adjacent latticeDist at h
    omega
  rcases hcoords with h | h | h | h
  · refine ⟨.east, ?_⟩; ext <;> simp [Compass.step] <;> omega
  · refine ⟨.north, ?_⟩; ext <;> simp [Compass.step] <;> omega
  · refine ⟨.west, ?_⟩; ext <;> simp [Compass.step] <;> omega
  · refine ⟨.south, ?_⟩; ext <;> simp [Compass.step] <;> omega

theorem present_symm {G : Finset Plane} (D : Network G) (x y : Plane)
    (h : D.Present x y) : D.Present y x := by
  refine ⟨h.2.1, h.1, ?_, h.2.2.2.2, h.2.2.2.1⟩
  have h₁ : (y.1 - x.1).natAbs = (x.1 - y.1).natAbs := by omega
  have h₂ : (y.2 - x.2).natAbs = (x.2 - y.2).natAbs := by omega
  simpa [Adjacent, latticeDist, h₁, h₂] using h.2.2.1

theorem stopped_isTrail {G : Finset Plane} {n : ℕ} (D : Network G)
    (u : Plane) (incoming : Compass) (T : Finset Plane) (w : DirectionWord n)
    (habs : ¬ D.Present (u - incoming.step) u) (hw : StoppedNetworkTrail D u T w) :
    IsTrail u incoming w := by
  refine ⟨hw.1, ?_⟩
  intro i hi heq
  have hv : wordVertex u w i.val = u := by simp [hi, wordVertex_zero]
  have he : wordVertex u w (i.val + 1) = u - incoming.step := by
    rw [wordVertex_step, hv, heq]
    cases incoming <;> ext <;> simp [Compass.reverse, Compass.step] <;> omega
  have hp := hw.2.1 i
  rw [hv, he] at hp
  exact habs (present_symm D _ _ hp)

theorem normalized_incoming_absent (p : PairData) (incoming : Compass)
    (hin : p.u = p.c + incoming.step) :
    ¬ p.normalized.Present (p.u - incoming.step) p.u := by
  have heq : p.u - incoming.step = p.c := by rw [hin, add_sub_cancel_right]
  intro h
  have hc := (Finset.mem_filter.mp h.1).2
  change p.D.status (p.u - incoming.step) ≠ .X at hc
  rw [heq] at hc
  exact hc p.pair.2.2.2.2.1

end AKLT.W.REC081
