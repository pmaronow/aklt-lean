module
public import AKLT.Blueprint.Rec.NodesClosure

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC054

private theorem neighbors_card_le (x : Plane) : (neighbors x).card ≤ 4 := by
  calc
    (neighbors x).card ≤ (Finset.univ : Finset Compass).card := Finset.card_image_le
    _ = 4 := by decide

private theorem kept_card_le {G : Finset Plane} {D : Network G}
    (hD : D.LocalRules) (x : Plane) : (D.kept x).card ≤ 4 :=
  (Finset.card_le_card ((hD.2.1 x).trans Finset.inter_subset_left)).trans
    (neighbors_card_le x)

private theorem presentNeighbors_subset_kept {G : Finset Plane} (D : Network G)
    (x : Plane) : D.presentNeighbors x ⊆ D.kept x := by
  intro z hz
  exact (Finset.mem_filter.mp hz).2.2.2.2.1

private theorem presentNeighbors_mono {G : Finset Plane} {D E : Network G}
    (ha : E.active ⊆ D.active) (hk : ∀ x, E.kept x ⊆ D.kept x) (x : Plane) :
    E.presentNeighbors x ⊆ D.presentNeighbors x := by
  intro z hz
  rcases Finset.mem_filter.mp hz with ⟨hz, hx, hz', hadj, hkx, hkz⟩
  exact Finset.mem_filter.mpr ⟨hz, ha hx, ha hz', hadj, hk x hkx, hk z hkz⟩

private theorem localRules_kept_subset {G : Finset Plane} {D E : Network G}
    (hD : D.LocalRules) (hs : E.status = D.status)
    (hk : ∀ x, E.kept x ⊆ D.kept x) : E.LocalRules := by
  have ha : E.active = D.active := by simp [Network.active, hs]
  have hn (x : Plane) : (E.presentNeighbors x).card ≤ (D.presentNeighbors x).card :=
    Finset.card_le_card (presentNeighbors_mono (by rw [ha]) hk x)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hs]
    exact hD.1 x hx
  · intro x
    exact (hk x).trans (hD.2.1 x)
  · intro x hx hsx
    exact (hn x).trans (hD.2.2.1 x hx (by simpa [hs] using hsx))
  · intro x hx
    exact (Nat.add_le_add_right (hn x) _).trans (hD.2.2.2 x (by simpa [ha] using hx))

private theorem traceStep_kept_subset {G : Finset Plane} (D : Network G)
    (y o x : Plane) : (traceStep D y o).kept x ⊆ D.kept x := by
  simp only [traceStep]
  split_ifs <;> first | exact Finset.erase_subset _ _ | exact Finset.Subset.refl _

private theorem traceStep_active_subset {G : Finset Plane} (D : Network G)
    (y o : Plane) : (traceStep D y o).active ⊆ D.active := by
  intro x hx
  rcases Finset.mem_filter.mp hx with ⟨hxG, hx⟩
  refine Finset.mem_filter.mpr ⟨hxG, ?_⟩
  by_cases hxy : x = y
  · subst x
    by_cases hy : D.status y = .U
    · simp [hy]
    · simp [traceStep, hy] at hx
  · simpa [traceStep, hxy] using hx

private theorem traceStep_localRules {G : Finset Plane} {D : Network G}
    (hD : D.LocalRules) (y o : Plane)
    (hy : D.status y = .U → (D.kept y).card ≤ 3) (ho : o ∈ D.kept y) :
    (traceStep D y o).LocalRules := by
  have hn (x : Plane) :
      ((traceStep D y o).presentNeighbors x).card ≤ (D.presentNeighbors x).card :=
    Finset.card_le_card (presentNeighbors_mono (traceStep_active_subset D y o)
      (traceStep_kept_subset D y o) x)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    by_cases hxy : x = y
    · subst x
      simp [traceStep, hD.1 y hx]
    · simpa [traceStep, hxy] using hD.1 x hx
  · intro x
    exact (traceStep_kept_subset D y o x).trans (hD.2.1 x)
  · intro x hx hs
    by_cases hxy : x = y
    · subst x
      have hU : D.status y = .U := by
        by_contra h
        simp [traceStep, h] at hs
      have hc : ((D.kept y).erase o).card ≤ 2 := by
        have := Finset.card_erase_add_one ho
        have := hy hU
        omega
      exact (Finset.card_le_card (presentNeighbors_subset_kept (traceStep D y o) y)).trans
        (by simpa [traceStep] using hc)
    · have hs' : D.status x = .D := by simpa [traceStep, hxy] using hs
      exact (hn x).trans (hD.2.2.1 x hx hs')
  · intro x hx
    exact (Nat.add_le_add_right (hn x) _).trans
      (hD.2.2.2 x (traceStep_active_subset D y o hx))

private theorem traceStep_arrival_card {G : Finset Plane} {D : Network G}
    (hD : D.LocalRules) {y o : Plane} (hne : y ≠ o) (hy : y ∈ D.kept o) :
    ((traceStep D y o).kept o).card ≤ 3 := by
  have hcard := kept_card_le hD o
  have herase := Finset.card_erase_add_one hy
  have : ((D.kept o).erase y).card ≤ 3 := by omega
  simpa [traceStep, Ne.symm hne] using this

private theorem traceStep_keeps_fresh_flag {G : Finset Plane} (D : Network G)
    (y o x z : Plane) (hz : z ∈ D.kept x)
    (hfresh : ({x, z} : Finset Plane) ≠ {y, o}) :
    z ∈ (traceStep D y o).kept x := by
  by_cases hxy : x = y
  · subst x
    have hzo : z ≠ o := by
      intro h
      exact hfresh (by rw [h])
    simpa [traceStep] using Finset.mem_erase.mpr ⟨hzo, hz⟩
  · by_cases hxo : x = o
    · subst x
      have hzy : z ≠ y := by
        intro h
        exact hfresh (by simp [h, Finset.pair_comm])
      simpa [traceStep, hxy] using Finset.mem_erase.mpr ⟨hzy, hz⟩
    · simpa [traceStep, hxy, hxo] using hz

private theorem traceNetwork_snoc {G : Finset Plane} (D : Network G)
    (xs : List Plane) (y o : Plane) :
    traceNetwork D (xs ++ [y, o]) = traceStep (traceNetwork D (xs ++ [y])) y o := by
  induction xs generalizing D with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil => rfl
    | cons b bs =>
      change traceNetwork (traceStep D a b) ((b :: bs) ++ [y, o]) =
        traceStep (traceNetwork (traceStep D a b) ((b :: bs) ++ [y])) y o
      exact ih (traceStep D a b)

private def pathPrefix {G : Finset Plane} (D : Network G) (f : ℕ → Plane)
    (j : ℕ) : Network G := traceNetwork D ((List.range (j + 1)).map f)

private theorem pathPrefix_succ {G : Finset Plane} (D : Network G)
    (f : ℕ → Plane) (j : ℕ) :
    pathPrefix D f (j + 1) = traceStep (pathPrefix D f j) (f j) (f (j + 1)) := by
  have hlist : (List.range (j + 1 + 1)).map f =
      (List.range j).map f ++ [f j, f (j + 1)] := by
    simp [List.range_succ, List.append_assoc]
  unfold pathPrefix
  rw [hlist, traceNetwork_snoc]
  simp only [List.range_succ, List.map_append, List.map_singleton]

/-- Only the next unused kept flags are needed to preserve the local degree rules.
The vertices may repeat, and no assertion about their evolving status is assumed. -/
theorem trace_localRules_of_fresh_bonds {G : Finset Plane} (D : Network G)
    (f : ℕ → Plane) (n : ℕ) (hD : D.LocalRules)
    (hstart : D.status (f 0) = .U → (D.kept (f 0)).card ≤ 3)
    (hne : ∀ i < n, f i ≠ f (i + 1))
    (hflags : ∀ i < n, f (i + 1) ∈ D.kept (f i) ∧ f i ∈ D.kept (f (i + 1)))
    (hinj : ∀ i < n, ∀ k < n,
      ({f i, f (i + 1)} : Finset Plane) = {f k, f (k + 1)} → i = k) :
    (traceNetwork D ((List.range (n + 1)).map f)).LocalRules := by
  have hinvariant (j : ℕ) (hj : j ≤ n) :
      (pathPrefix D f j).LocalRules ∧
      ((pathPrefix D f j).status (f j) = .U → ((pathPrefix D f j).kept (f j)).card ≤ 3) ∧
      (∀ i, j ≤ i → i < n →
        f (i + 1) ∈ (pathPrefix D f j).kept (f i) ∧
          f i ∈ (pathPrefix D f j).kept (f (i + 1))) := by
    induction j with
    | zero =>
      refine ⟨hD, hstart, ?_⟩
      intro i _ hi
      exact hflags i hi
    | succ j ih =>
      have hjn : j < n := by omega
      obtain ⟨hl, hu, hf⟩ := ih (by omega)
      have hcurrent := hf j (by omega) hjn
      rw [pathPrefix_succ]
      refine ⟨traceStep_localRules hl (f j) (f (j + 1)) hu hcurrent.1,
        fun _ => traceStep_arrival_card hl (hne j hjn) hcurrent.2, ?_⟩
      intro i hji hi
      have hprev := hf i (by omega) hi
      have hfresh : ({f i, f (i + 1)} : Finset Plane) ≠ {f j, f (j + 1)} := by
        intro heq
        have := hinj i hi j hjn heq
        omega
      exact ⟨traceStep_keeps_fresh_flag _ _ _ _ _ hprev.1 hfresh,
        traceStep_keeps_fresh_flag _ _ _ _ _ hprev.2 (by
          simpa only [Finset.pair_comm (f (i + 1)) (f i)] using hfresh)⟩
  exact (hinvariant n le_rfl).1

private theorem normalized_localRules (p : PairSetup) : p.normalized.LocalRules := by
  apply localRules_kept_subset (D := p.D) (E := p.normalized) p.pair.1.1.1 rfl
  intro x
  change (if x = p.u ∧ p.D.status p.u = .U then (p.D.kept x).erase p.c
    else p.D.kept x) ⊆ p.D.kept x
  split_ifs <;> first | exact Finset.erase_subset _ _ | exact Finset.Subset.refl _

private theorem normalized_start_card (p : PairSetup) (hs : p.normalized.status p.u = .U) :
    (p.normalized.kept p.u).card ≤ 3 := by
  have huG : p.u ∈ p.G := (Finset.mem_filter.mp p.pair.2.1).1
  have hfull := p.pair.1.2.1 p.u huG hs
  have hcu : p.c ∈ neighbors p.u := by
    apply Finset.mem_image.mpr
    refine ⟨p.incoming.reverse, Finset.mem_univ _, ?_⟩
    rw [p.incoming_eq]
    cases p.incoming <;> ext <;> simp [Compass.reverse, Compass.step, add_assoc]
  have hc : p.c ∈ p.D.kept p.u := by
    rw [hfull]
    exact Finset.mem_inter.mpr ⟨hcu, p.pair.2.2.2.1⟩
  have hcard := kept_card_le p.pair.1.1.1 p.u
  have herase := Finset.card_erase_add_one hc
  have : ((p.D.kept p.u).erase p.c).card ≤ 3 := by omega
  simpa [PairData.normalized, normalizeStart, show p.D.status p.u = .U from hs] using this

/-- The traced network satisfies the local rules, without any residual premise. -/
theorem terminal_localRules (p : PairSetup) {n : ℕ} (w : DirectionWord n)
    (htrail : StoppedNetworkTrail p.normalized p.u (protectedSites p.G) w) :
    (traceNetwork p.normalized (wordVertices p.u w)).LocalRules := by
  apply trace_localRules_of_fresh_bonds p.normalized (wordVertex p.u w) n
    (normalized_localRules p)
  · simpa [wordVertex] using normalized_start_card p
  · intro i hi heq
    have hadj := (htrail.2.1 ⟨i, hi⟩).2.2.1
    rw [heq] at hadj
    simp [Adjacent, latticeDist] at hadj
  · intro i hi
    exact ⟨(htrail.2.1 ⟨i, hi⟩).2.2.2.1, (htrail.2.1 ⟨i, hi⟩).2.2.2.2⟩
  · intro i hi k hk heq
    exact congrArg Fin.val (htrail.1 (show wordBond p.u w ⟨i, hi⟩ =
      wordBond p.u w ⟨k, hk⟩ from heq))

end AKLT.W.REC054
