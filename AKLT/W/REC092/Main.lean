import AKLT.Blueprint.Rec.NodesV2Local

noncomputable section
open AKLT.Defs

namespace AKLT.W.REC092

private lemma normalizeRotation_injective (a : Compass) :
    Function.Injective (normalizeRotation a) := by
  intro p q h
  cases a <;> cases p with
  | mk px py =>
    cases q with
    | mk qx qy =>
      simp [normalizeRotation] at h ⊢ <;> omega

private lemma chart_injective (y : Plane) (a : Compass) :
    Function.Injective (fun z : Plane => y + normalizeRotation a z) := by
  intro z t h
  apply normalizeRotation_injective a
  exact add_left_cancel h

private lemma normalizeRotation_adj_iff (a : Compass) (z t : Plane) :
    Adjacent (normalizeRotation a z) (normalizeRotation a t) ↔ Adjacent z t := by
  cases a <;> cases z with
  | mk zx zy =>
    cases t with
    | mk tx ty =>
      simp [Adjacent, latticeDist, normalizeRotation] <;> omega

private lemma adjacent_coordinate_cases {z t : Plane} (h : Adjacent z t) :
    (z.1 + 1 = t.1 ∧ z.2 = t.2) ∨
    (z.1 = t.1 ∧ z.2 + 1 = t.2) ∨
    (t.1 + 1 = z.1 ∧ t.2 = z.2) ∨
    (t.1 = z.1 ∧ t.2 + 1 = z.2) := by
  have hdist := h
  simp only [Adjacent, latticeDist] at hdist
  have hparts :
      ((z.1 - t.1).natAbs = 1 ∧ (z.2 - t.2).natAbs = 0) ∨
      ((z.1 - t.1).natAbs = 0 ∧ (z.2 - t.2).natAbs = 1) := by omega
  have hzero (x : ℤ) (hx : x.natAbs = 0) : x = 0 := by
    rcases Int.natAbs_eq x with h | h <;> rw [hx] at h <;> norm_num at h <;> assumption
  have hone (x : ℤ) (hx : x.natAbs = 1) : x = 1 ∨ x = -1 := by
    rcases Int.natAbs_eq x with h | h
    · rw [hx] at h
      norm_num at h
      exact Or.inl h
    · rw [hx] at h
      norm_num at h
      exact Or.inr h
  rcases hparts with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · have hy0 := hzero _ hy
    rcases hone _ hx with hx1 | hxneg
    · right
      right
      left
      omega
    · left
      omega
  · have hx0 := hzero _ hx
    rcases hone _ hy with hy1 | hyneg
    · right
      right
      right
      omega
    · right
      left
      omega

private lemma chart_adj_iff (y : Plane) (a : Compass) (z t : Plane) :
    Adjacent (y + normalizeRotation a z) (y + normalizeRotation a t) ↔
      Adjacent z t := by
  have htrans (u v : Plane) : Adjacent (y + u) (y + v) ↔ Adjacent u v := by
    cases y with
    | mk yx yy =>
      cases u with
      | mk ux uy =>
        cases v with
        | mk vx vy => simp [Adjacent, latticeDist] <;> omega
  exact (htrans _ _).trans (normalizeRotation_adj_iff a z t)

private lemma internalBonds_adj {S : Finset Plane} {z t : Plane}
    (h : (z, t) ∈ internalBonds S) : Adjacent z t := by
  rcases Finset.mem_biUnion.mp h with ⟨x, _, hx⟩
  rcases Finset.mem_image.mp hx with ⟨u, hu, heq⟩
  have heq' : (x, u) = (z, t) := heq
  have hxz : x = z := congrArg Prod.fst heq'
  have hut : u = t := congrArg Prod.snd heq'
  subst x
  subst u
  have hu' := (Finset.mem_inter.mp hu).1
  simp [positiveNeighbours] at hu'
  rcases hu' with hright | hup
  · subst t
    simp [Adjacent, latticeDist]
  · subst t
    simp [Adjacent, latticeDist]

private lemma adjacent_symm {z t : Plane} (h : Adjacent z t) : Adjacent t z := by
  rcases adjacent_coordinate_cases h with hE | hN | hW | hS
  · have hx : t.1 - z.1 = 1 := by omega
    have hy : t.2 - z.2 = 0 := by omega
    simp [Adjacent, latticeDist, hx, hy]
  · have hx : t.1 - z.1 = 0 := by omega
    have hy : t.2 - z.2 = 1 := by omega
    simp [Adjacent, latticeDist, hx, hy]
  · have hx : t.1 - z.1 = -1 := by omega
    have hy : t.2 - z.2 = 0 := by omega
    simp [Adjacent, latticeDist, hx, hy]
  · have hx : t.1 - z.1 = 0 := by omega
    have hy : t.2 - z.2 = -1 := by omega
    simp [Adjacent, latticeDist, hx, hy]

private lemma internal_of_bond {π : PatternData} {z t : Plane}
    (h : (z, t) ∈ π.bonds) : (z, t) ∈ internalBonds templateSites := by
  have hb : (z, t) ∈ internalBonds templateSites ∧
      (π.statusAt z ≠ .X ∧ π.statusAt t ≠ .X ∧
        (z ∈ templateTips ∨ t ∈ π.keptAt z) ∧
        (t ∈ templateTips ∨ z ∈ π.keptAt t)) := by
    simpa only [PatternData.bonds, Finset.mem_filter] using h
  exact hb.1

private lemma bond_of_data {π : PatternData} {z t : Plane}
    (hedge : (z, t) ∈ internalBonds templateSites)
    (hz : π.statusAt z ≠ .X) (ht : π.statusAt t ≠ .X)
    (hzt : z ∈ templateTips ∨ t ∈ π.keptAt z)
    (htz : t ∈ templateTips ∨ z ∈ π.keptAt t) :
    (z, t) ∈ π.bonds := by
  simp only [PatternData.bonds, Finset.mem_filter]
  exact ⟨hedge, ⟨hz, ht, hzt, htz⟩⟩

private lemma internalBonds_or {S : Finset Plane} {z t : Plane}
    (hz : z ∈ S) (ht : t ∈ S) (hadj : Adjacent z t) :
    (z, t) ∈ internalBonds S ∨ (t, z) ∈ internalBonds S := by
  have hor : (z.1 + 1 = t.1 ∧ z.2 = t.2) ∨
      (z.1 = t.1 ∧ z.2 + 1 = t.2) ∨
      (t.1 + 1 = z.1 ∧ t.2 = z.2) ∨
      (t.1 = z.1 ∧ t.2 + 1 = z.2) := by
    exact adjacent_coordinate_cases hadj
  rcases hor with he | hn | hw | hs
  · left
    simp [internalBonds, positiveNeighbours, Finset.mem_biUnion,
      Finset.mem_image, hz, ht, he]
  · left
    simp [internalBonds, positiveNeighbours, Finset.mem_biUnion,
      Finset.mem_image, hz, ht, hn]
  · right
    simp [internalBonds, positiveNeighbours, Finset.mem_biUnion,
      Finset.mem_image, hz, ht, hw]
  · right
    simp [internalBonds, positiveNeighbours, Finset.mem_biUnion,
      Finset.mem_image, hz, ht, hs]

private lemma bond_mem_kept {π : PatternData} {z t : Plane}
    (hzTip : z ∉ templateTips) (htTip : t ∉ templateTips)
    (h : (z, t) ∈ π.bonds) :
    π.statusAt z ≠ .X ∧ π.statusAt t ≠ .X ∧
      t ∈ π.keptAt z ∧ z ∈ π.keptAt t := by
  simp only [PatternData.bonds, Finset.mem_filter] at h
  rcases h with ⟨_, ⟨hs, ht, hzt, htz⟩⟩
  exact ⟨hs, ht, (hzt.resolve_left hzTip), (htz.resolve_left htTip)⟩

private lemma internalPresent_kept {π : PatternData} {z t : Plane}
    (hzTip : z ∉ templateTips) (htTip : t ∉ templateTips)
    (h : π.InternalPresent z t) :
    π.statusAt z ≠ .X ∧ π.statusAt t ≠ .X ∧
      t ∈ π.keptAt z ∧ z ∈ π.keptAt t := by
  rcases h with hzt | htz
  · exact bond_mem_kept hzTip htTip hzt
  · have h' := bond_mem_kept htTip hzTip htz
    exact ⟨h'.2.1, h'.1, h'.2.2.2, h'.2.2.1⟩

theorem main : AKLT.Blueprint.Rec.LegacyCoverComparisonStatementV2 := by
  intro G D haux y incoming outgoing hlegacy
  rcases hlegacy with ⟨π, hcovered, horient, hmatch⟩
  have hcoveredOrig := hcovered
  rcases hcovered with ⟨_, _, _, _, _, _, _, _, htip, _⟩
  rcases haux with ⟨hrules, _⟩
  have houtside := hrules.1
  let chart : Plane → Plane := fun z => y + normalizeRotation incoming z
  refine ⟨π, hcoveredOrig, horient, ?_, ?_⟩
  · intro z hz
    exact (hmatch z hz).1
  · intro z hz t ht
    have hzTip : z ∉ templateTips := (Finset.mem_sdiff.mp hz).2
    by_cases htTip : t ∈ templateTips
    · simp only [if_pos htTip]
      change D.Present (chart z) (chart t) → π.InternalPresent z t
      intro hpresent
      have hzStatus : π.statusAt z = D.status (chart z) := (hmatch z hz).1
      have hzActive : chart z ∈ D.active := hpresent.1
      have htActive : chart t ∈ D.active := hpresent.2.1
      have hzG : chart z ∈ G := (Finset.mem_filter.mp hzActive).1
      have htG : chart t ∈ G := (Finset.mem_filter.mp htActive).1
      have hzNonX : π.statusAt z ≠ .X := by
        rw [hzStatus]
        exact (Finset.mem_filter.mp hzActive).2
      have hkeptEq := (hmatch z hz).2 hzNonX
      have hflag : t ∈ π.keptAt z := by
        have hin : chart t ∈ ((π.keptAt z).image chart ∩ G) := by
          rw [hkeptEq]
          exact hpresent.2.2.2.1
        rcases Finset.mem_inter.mp hin with ⟨him, _⟩
        rcases Finset.mem_image.mp him with ⟨q, hq, hqeq⟩
        have : q = t := chart_injective y incoming hqeq
        simpa [this] using hq
      have hadj : Adjacent z t := (chart_adj_iff y incoming z t).mp hpresent.2.2.1
      have hedge := internalBonds_or (Finset.mem_sdiff.mp hz).1 ht hadj
      have htNonX : π.statusAt t ≠ .X := by
        rw [htip t htTip]
        decide
      have hpatternBond : (z, t) ∈ π.bonds ∨ (t, z) ∈ π.bonds := by
        rcases hedge with he | he
        · left
          exact bond_of_data he hzNonX htNonX
            (Or.inr hflag) (Or.inl htTip)
        · right
          exact bond_of_data he htNonX hzNonX
            (Or.inl htTip) (Or.inr hflag)
      change (z, t) ∈ π.bonds ∨ (t, z) ∈ π.bonds
      exact hpatternBond
    · simp only [if_neg htTip]
      change π.InternalPresent z t ↔ D.Present (chart z) (chart t)
      constructor
      · intro hpresent
        have hfacts := internalPresent_kept hzTip htTip hpresent
        have hzStatus : π.statusAt z = D.status (chart z) := (hmatch z hz).1
        have htStatus : π.statusAt t = D.status (chart t) := (hmatch t (Finset.mem_sdiff.mpr ⟨ht, htTip⟩)).1
        have hzG : chart z ∈ G := by
          by_contra hnot
          apply hfacts.1
          rw [hzStatus, houtside (chart z) hnot]
        have htG : chart t ∈ G := by
          by_contra hnot
          apply hfacts.2.1
          rw [htStatus, houtside (chart t) hnot]
        have hzKeptEq := (hmatch z hz).2 hfacts.1
        have htKeptEq := (hmatch t (Finset.mem_sdiff.mpr ⟨ht, htTip⟩)).2 hfacts.2.1
        have hzKept : chart t ∈ D.kept (chart z) := by
          rw [← hzKeptEq]
          exact Finset.mem_inter.mpr
            ⟨Finset.mem_image.mpr ⟨t, hfacts.2.2.1, rfl⟩, htG⟩
        have htKept : chart z ∈ D.kept (chart t) := by
          rw [← htKeptEq]
          exact Finset.mem_inter.mpr
            ⟨Finset.mem_image.mpr ⟨z, hfacts.2.2.2, rfl⟩, hzG⟩
        have hadjTemplate : Adjacent z t := by
          rcases hpresent with hp | hp
          · exact internalBonds_adj (internal_of_bond hp)
          · exact adjacent_symm (internalBonds_adj (internal_of_bond hp))
        have hadj : Adjacent (chart z) (chart t) :=
          (chart_adj_iff y incoming z t).mpr hadjTemplate
        have hzActive : chart z ∈ D.active :=
          Finset.mem_filter.mpr ⟨hzG, by rw [← hzStatus]; exact hfacts.1⟩
        have htActive : chart t ∈ D.active :=
          Finset.mem_filter.mpr ⟨htG, by rw [← htStatus]; exact hfacts.2.1⟩
        exact ⟨hzActive, htActive, hadj, hzKept, htKept⟩
      · intro hpresent
        have hzStatus : π.statusAt z = D.status (chart z) := (hmatch z hz).1
        have htStatus : π.statusAt t = D.status (chart t) := (hmatch t (Finset.mem_sdiff.mpr ⟨ht, htTip⟩)).1
        have hzActive : chart z ∈ D.active := hpresent.1
        have htActive : chart t ∈ D.active := hpresent.2.1
        have hzG : chart z ∈ G := (Finset.mem_filter.mp hzActive).1
        have htG : chart t ∈ G := (Finset.mem_filter.mp htActive).1
        have hzNonX : π.statusAt z ≠ .X := by rw [hzStatus]; exact (Finset.mem_filter.mp hzActive).2
        have htNonX : π.statusAt t ≠ .X := by rw [htStatus]; exact (Finset.mem_filter.mp htActive).2
        have hzKeptEq := (hmatch z hz).2 hzNonX
        have htKeptEq := (hmatch t (Finset.mem_sdiff.mpr ⟨ht, htTip⟩)).2 htNonX
        have hzFlag : t ∈ π.keptAt z := by
          have hin : chart t ∈ ((π.keptAt z).image chart ∩ G) := by
            rw [hzKeptEq]
            exact hpresent.2.2.2.1
          rcases Finset.mem_image.mp (Finset.mem_inter.mp hin).1 with ⟨q, hq, heq⟩
          have hqt : q = t := chart_injective y incoming heq
          simpa [hqt] using hq
        have htFlag : z ∈ π.keptAt t := by
          have hin : chart z ∈ ((π.keptAt t).image chart ∩ G) := by
            rw [htKeptEq]
            exact hpresent.2.2.2.2
          rcases Finset.mem_image.mp (Finset.mem_inter.mp hin).1 with ⟨q, hq, heq⟩
          have hqz : q = z := chart_injective y incoming heq
          simpa [hqz] using hq
        have hedge : (z, t) ∈ internalBonds templateSites ∨
            (t, z) ∈ internalBonds templateSites :=
          internalBonds_or (Finset.mem_sdiff.mp hz).1 ht
            ((chart_adj_iff y incoming z t).mp hpresent.2.2.1)
        have hzTip : z ∉ templateTips := (Finset.mem_sdiff.mp hz).2
        have htNonTip : t ∉ templateTips := htTip
        rcases hedge with he | he
        · exact Or.inl (bond_of_data he hzNonX htNonX (Or.inr hzFlag) (Or.inr htFlag))
        · exact Or.inr (bond_of_data he htNonX hzNonX (Or.inr htFlag) (Or.inr hzFlag))

end AKLT.W.REC092
