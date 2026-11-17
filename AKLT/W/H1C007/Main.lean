module
public import AKLT.Cert.H1.Production.Leaves

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.W.H1C007

open AKLT.Cert.H1.Production
open AKLT.Defs

private instance : ReflBEq RawOption where
  rfl := by
    intro a
    cases a with
    | mk status mask =>
      change ((status == status) && (mask == mask)) = true
      rw [Bool.and_eq_true]
      exact ⟨beq_self_eq_true _, beq_self_eq_true _⟩

private instance : LawfulBEq RawOption where
  eq_of_beq := by
    intro a b h
    cases a with
    | mk sa ma =>
      cases b with
      | mk sb mb =>
        change ((sa == sb) && (ma == mb)) = true at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        rcases h with ⟨rfl, rfl⟩
        rfl

private theorem list_eq_four_of_length {α : Type} (l : List α) (h : l.length = 4) :
    ∃ a b c d, l = [a, b, c, d] := by
  cases l with
  | nil => simp at h
  | cons a l =>
    have h₁ : l.length = 3 := by simpa using h
    cases l with
    | nil => simp at h₁
    | cons b l =>
      have h₂ : l.length = 2 := by simpa using h₁
      cases l with
      | nil => simp at h₂
      | cons c l =>
        have h₃ : l.length = 1 := by simpa using h₂
        cases l with
        | nil => simp at h₃
        | cons d l =>
          have h₄ : l.length = 0 := by simpa using h₃
          cases l with
          | nil => exact ⟨a, b, c, d, rfl⟩
          | cons e rest => simp at h₄

private theorem templateSites_cases (x : Plane) (hx : x ∈ templateSites) :
    x = (0, 0) ∨ x = (1, 0) ∨ x = (0, 1) ∨ x = (-1, 0) ∨
    x = (0, -1) ∨ x = (1, 1) ∨ x = (-1, 1) ∨ x = (-1, -1) ∨
    x = (1, -1) ∨ x = (2, 0) ∨ x = (0, 2) ∨ x = (-2, 0) ∨ x = (0, -2) := by
  rcases x with ⟨x₁, x₂⟩
  simp [templateSites, square, latticeDist] at hx
  rcases hx with ⟨⟨⟨hxl, hxu⟩, hyl, hyu⟩, hdist⟩
  have hcase₁ : x₁ = -2 ∨ x₁ = -1 ∨ x₁ = 0 ∨ x₁ = 1 ∨ x₁ = 2 := by omega
  rcases hcase₁ with hcase₁ | hcase₁ | hcase₁ | hcase₁ | hcase₁ <;> subst x₁
  all_goals
    have hcase₂ : x₂ = -2 ∨ x₂ = -1 ∨ x₂ = 0 ∨ x₂ = 1 ∨ x₂ = 2 := by omega
    rcases hcase₂ with hcase₂ | hcase₂ | hcase₂ | hcase₂ | hcase₂ <;> subst x₂ <;>
      simp_all [templateSites, square, latticeDist]

private def decodedStatus (o : RawOption) : Status :=
  if o.status == 1 then .U else if o.status == 2 then .D else .X

private theorem decodedStatus_eq_U_iff (o : RawOption) :
    decodedStatus o = .U ↔ o.status = 1 := by
  by_cases hs : o.status = 1
  · simp [decodedStatus, hs]
  · by_cases ht : o.status = 2 <;> simp [decodedStatus, hs, ht]

private def decodedKeptAt (x : Plane) (o : RawOption) : Finset Plane :=
  Finset.image (fun d => x + d.step)
    (((List.range 4).filter (fun d => hasDirection o.mask d)).map compassAt).toFinset

private theorem decodedKeptAt_step (x : Plane) (o : RawOption) (d : Nat)
    (hd : d < 4) :
    x + (compassAt d).step ∈ decodedKeptAt x o ↔ hasDirection o.mask d = true := by
  have hdCases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hdCases with rfl | rfl | rfl | rfl
  all_goals
    constructor
    · intro h
      rcases Finset.mem_image.mp h with ⟨c, hc, heq⟩
      rcases List.mem_toFinset.mp hc with hc
      rcases List.mem_map.mp hc with ⟨a, ha, hac⟩
      rcases List.mem_filter.mp ha with ⟨hr, hbit⟩
      have hcEq : c = compassAt a := hac.symm
      subst c
      have haCases : a = 0 ∨ a = 1 ∨ a = 2 ∨ a = 3 := by
        simp at hr
        omega
      rcases haCases with rfl | rfl | rfl | rfl <;>
        simp_all [compassAt, Compass.step]
    · intro hbit
      apply Finset.mem_image.mpr
      refine ⟨compassAt _, ?_, rfl⟩
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      refine ⟨_, ?_, rfl⟩
      apply List.mem_filter.mpr
      exact ⟨by simp [List.range, List.range.loop], hbit⟩

private theorem reverseStepPoint (x : Plane) (d : Nat) (hd : d < 4) :
    x = (x + (compassAt d).step) + (compassAt ((d+2)%4)).step := by
  have hdCases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hdCases with rfl | rfl | rfl | rfl <;>
    ext <;> simp [compassAt, Compass.step] <;> omega

private theorem decodedKeptAt_reverseStep (x : Plane) (o : RawOption) (d : Nat)
    (hd : d < 4) :
    x ∈ decodedKeptAt (x + (compassAt d).step) o ↔
      hasDirection o.mask ((d+2)%4) = true := by
  have hdir : (d+2)%4 < 4 := Nat.mod_lt _ (by decide)
  have h := decodedKeptAt_step (x + (compassAt d).step) o ((d+2)%4) hdir
  rw [← reverseStepPoint x d hd] at h
  exact h

private def axisSite (i : Nat) : Plane := AKLT.Cert.H1.ringSites.getD (2*i) (0,0)

private theorem axialCovered {i : Nat} (hi : i < 3) (o : RawOption)
    (ho : o ∈ axialOptions i) :
    decodedStatus o = .U ∨ decodedStatus o = .X ∨
      (decodedStatus o = .D ∧ (decodedKeptAt (axisSite i) o).card = 2 ∧
        (0,0) ∈ decodedKeptAt (axisSite i) o) := by
  interval_cases i
  · simp [axialOptions] at ho
    rcases ho with rfl | rfl | ⟨d, ⟨hd, hne⟩, rfl⟩
    · simp [decodedStatus]
    · simp [decodedStatus]
    · interval_cases d <;>
        simp_all [decodedStatus, decodedKeptAt, axisSite, AKLT.Cert.H1.ringSites,
          List.range, List.range.loop, hasDirection, compassAt, Compass.step]
  · simp [axialOptions] at ho
    rcases ho with rfl | rfl | ⟨d, ⟨hd, hne⟩, rfl⟩
    · simp [decodedStatus]
    · simp [decodedStatus]
    · interval_cases d <;>
        simp_all [decodedStatus, decodedKeptAt, axisSite, AKLT.Cert.H1.ringSites,
          List.range, List.range.loop, hasDirection, compassAt, Compass.step]
  · simp [axialOptions] at ho
    rcases ho with rfl | rfl | ⟨d, ⟨hd, hne⟩, rfl⟩
    · simp [decodedStatus]
    · simp [decodedStatus]
    · interval_cases d <;>
        simp_all [decodedStatus, decodedKeptAt, axisSite, AKLT.Cert.H1.ringSites,
          List.range, List.range.loop, hasDirection, compassAt, Compass.step]

private theorem axialNonzeroStatus {i : Nat} (hi : i < 3) (o : RawOption)
    (ho : o ∈ axialOptions i) (hnz : o.status != 0) : decodedStatus o ≠ .X := by
  interval_cases i
  · simp [axialOptions] at ho
    rcases ho with rfl | rfl | ⟨d, ⟨hd, hne⟩, rfl⟩ <;> simp_all [decodedStatus]
  · simp [axialOptions] at ho
    rcases ho with rfl | rfl | ⟨d, ⟨hd, hne⟩, rfl⟩ <;> simp_all [decodedStatus]
  · simp [axialOptions] at ho
    rcases ho with rfl | rfl | ⟨d, ⟨hd, hne⟩, rfl⟩ <;> simp_all [decodedStatus]

private theorem cornerCoveredAt (x : Plane) (o : RawOption) (ho : o ∈ cornerOptions) :
    decodedStatus o = .U ∨ decodedStatus o = .X ∨
      (decodedStatus o = .D ∧ (decodedKeptAt x o).card = 2) := by
  simp [cornerOptions] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [decodedStatus, decodedKeptAt, hasDirection, compassAt,
    Compass.step, List.range, List.range.loop]

private theorem axialUMask {i : Nat} (hi : i < 4) (o : RawOption)
    (ho : o ∈ axialOptions i) (hs : o.status = 1) : o.mask = 15 := by
  interval_cases i <;> simp [axialOptions] at ho ⊢ <;>
    rcases ho with rfl | rfl | ⟨d, hd, rfl⟩ <;> simp_all

private theorem cornerUMask (o : RawOption) (ho : o ∈ cornerOptions)
    (hs : o.status = 1) : o.mask = 15 := by
  simp [cornerOptions] at ho
  rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all

private theorem decodedKeptFull (x : Plane) :
    decodedKeptAt x ⟨1, 15⟩ = neighbours x := by
  ext y
  simp [decodedKeptAt, hasDirection, compassAt, Compass.step, neighbours,
    List.range, List.range.loop]
  constructor
  · rintro (h | h | h | h)
    · exact ⟨.east, h.symm⟩
    · exact ⟨.north, h.symm⟩
    · exact ⟨.west, h.symm⟩
    · exact ⟨.south, h.symm⟩
  · rintro ⟨d, h⟩
    cases d <;> simp_all [Compass.step]

private theorem inputStatusAtRing (a : Input) (x : Plane)
    (hx : x ∈ templateSites) (hc : x ≠ (0,0)) (ht : x ∉ templateTips) :
    (inputPattern a).statusAt x = decodedStatus (a.optionAt x) := by
  simp_all [inputPattern, PatternData.statusAt, hx, hc, ht, templateTips, decodedStatus]

private theorem inputKeptAtFull (a : Input) (x : Plane)
    (hx : x ∈ templateSites) (hc : x ≠ (0,0))
    (hm : (a.optionAt x).mask = 15) :
    (inputPattern a).keptAt x = neighbours x := by
  calc
    (inputPattern a).keptAt x = decodedKeptAt x (a.optionAt x) := by
      simp [inputPattern, PatternData.keptAt, hx, hc, decodedKeptAt]
    _ = decodedKeptAt x ⟨1, 15⟩ := by simp [decodedKeptAt, hm]
    _ = neighbours x := decodedKeptFull x

private theorem inputKeptAtEqDecoded (a : Input) (x : Plane)
    (hx : x ∈ templateSites) (hc : x ≠ (0,0)) :
    (inputPattern a).keptAt x = decodedKeptAt x (a.optionAt x) := by
  simp [inputPattern, PatternData.keptAt, decodedKeptAt, hx, hc]

private theorem optionAt_ringIndex (a : Input) (i : Nat) (hi : i < 8) :
    a.optionAt (AKLT.Cert.H1.ringSites.getD i (0,0)) =
      (ringOptions a.axes a.corners).getD i ⟨0,0⟩ := by
  let sites := AKLT.Cert.H1.ringSites
  let opts := ringOptions a.axes a.corners
  let entries := sites.zip opts
  let target := sites.getD i (0,0)
  let value := opts.getD i ⟨0,0⟩
  have hsites : sites.length = 8 := by simp [sites, AKLT.Cert.H1.ringSites]
  have hopts : opts.length = 8 := by
    simp [opts, ringOptions, List.range, List.range.loop]
  have hsitesNodup : sites.Nodup := by simp [sites, AKLT.Cert.H1.ringSites]
  have hiSites : i < sites.length := by omega
  have hiOpts : i < opts.length := by omega
  have hiEntries : i < entries.length := by
    change i < min sites.length opts.length
    exact Nat.lt_min.mpr ⟨hiSites, hiOpts⟩
  have hget : entries[i] = (target, value) := by
    calc
      entries[i] = (sites[i], opts[i]) := List.getElem_zip
      _ = (target, value) := by
        congr 1
        · exact List.getElem_eq_getD (0,0)
        · exact List.getElem_eq_getD (⟨0,0⟩ : RawOption)
  have hp : (fun p : Plane × RawOption => p.1 == target) (target, value) = true := by
    simp
  have hprev : ∀ j, ∀ hj : j < i,
      (!((fun p : Plane × RawOption => p.1 == target)
        (entries[j]'(show j < entries.length from by
          change j < min sites.length opts.length
          exact Nat.lt_min.mpr ⟨lt_trans hj hiSites, lt_trans hj hiOpts⟩)))) = true := by
    intro j hj
    have hjSites : j < sites.length := lt_trans hj hiSites
    have hjOpts : j < opts.length := lt_trans hj hiOpts
    have hjEntries : j < entries.length := by
      change j < min sites.length opts.length
      exact Nat.lt_min.mpr ⟨hjSites, hjOpts⟩
    have hpair := List.getElem_zip (l := sites) (l' := opts) (i := j) (h := hjEntries)
    have hfirst : (entries[j]'hjEntries).1 = sites[j]'hjSites := congrArg Prod.fst hpair
    have hne : sites[j]'hjSites ≠ target := by
      change sites[j]'hjSites ≠ sites.getD i (0,0)
      rw [List.getD_eq_getElem sites (0,0) hiSites]
      intro heq
      have hji : j = i := (hsitesNodup.getElem_inj).mp heq
      exact (Nat.ne_of_lt hj) hji
    have hbool : (sites[j]'hjSites == target) = false := by
      cases h : (sites[j]'hjSites == target) with
      | false => rfl
      | true =>
          have ht : sites[j]'hjSites = target := (beq_iff_eq).mp h
          exact False.elim (hne ht)
    simp [hfirst, hbool]
  have hfind : entries.find? (fun p => p.1 == target) = some (target, value) := by
    apply List.find?_eq_some_iff_getElem.mpr
    exact ⟨hp, ⟨i, hiEntries, hget, hprev⟩⟩
  change (((entries.find? (fun p => p.1 == target)).map Prod.snd).getD ⟨0,0⟩) = value
  rw [hfind]
  rfl

private theorem inputKeptAt_ringIndex (a : Input) (i : Nat) (hi : i < 8) :
    (inputPattern a).keptAt (AKLT.Cert.H1.ringSites.getD i (0,0)) =
      decodedKeptAt (AKLT.Cert.H1.ringSites.getD i (0,0))
        ((ringOptions a.axes a.corners).getD i ⟨0,0⟩) := by
  let x := AKLT.Cert.H1.ringSites.getD i (0,0)
  have hx : x ∈ templateSites := by
    dsimp [x]
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
        i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hcases with h | h | h | h | h | h | h | h <;> subst i <;>
      simp [AKLT.Cert.H1.ringSites, templateSites, square, latticeDist]
  have hc : x ≠ (0,0) := by
    dsimp [x]
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
        i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hcases with h | h | h | h | h | h | h | h <;> subst i <;>
      decide
  change (inputPattern a).keptAt x = decodedKeptAt x
    ((ringOptions a.axes a.corners).getD i ⟨0,0⟩)
  rw [inputKeptAtEqDecoded a x hx hc, optionAt_ringIndex a i hi]

private theorem inputStatusAt_ringIndex (a : Input) (i : Nat) (hi : i < 8) :
    (inputPattern a).statusAt (AKLT.Cert.H1.ringSites.getD i (0,0)) =
      decodedStatus ((ringOptions a.axes a.corners).getD i ⟨0,0⟩) := by
  let x := AKLT.Cert.H1.ringSites.getD i (0,0)
  have hx : x ∈ templateSites := by
    dsimp [x]
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
        i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hcases with h | h | h | h | h | h | h | h <;> subst i <;>
      simp [AKLT.Cert.H1.ringSites, templateSites, square, latticeDist]
  have hc : x ≠ (0,0) := by
    dsimp [x]
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
        i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hcases with h | h | h | h | h | h | h | h <;> subst i <;>
      decide
  have ht : x ∉ templateTips := by
    dsimp [x]
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨
        i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases hcases with h | h | h | h | h | h | h | h <;> subst i <;>
      simp [AKLT.Cert.H1.ringSites, templateTips]
  change (inputPattern a).statusAt x =
    decodedStatus ((ringOptions a.axes a.corners).getD i ⟨0,0⟩)
  rw [inputStatusAtRing a x hx hc ht, optionAt_ringIndex a i hi]

private theorem decodedStatus_ne_X_status_ne_zero (o : RawOption)
    (h : decodedStatus o ≠ .X) : o.status ≠ 0 := by
  cases o with
  | mk s m =>
    cases s with
    | zero => exact False.elim (h (by simp [decodedStatus]))
    | succ n => exact Nat.succ_ne_zero _

private theorem inputCenterKept (a : Input) :
    (inputPattern a).keptAt (0,0) = {(1,0), (0,1), (-1,0)} := by
  simp [inputPattern, PatternData.keptAt, templateSites, square, latticeDist,
    Compass.step]

private theorem inputCenterStatus (a : Input) :
    (inputPattern a).statusAt (0,0) = .U := by
  simp [inputPattern, PatternData.statusAt, templateSites, square, latticeDist]

private theorem inputKeptAtE (a : Input) :
    (inputPattern a).keptAt (1,0) = decodedKeptAt (1,0) (a.axes.getD 0 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputKeptAt_ringIndex a 0 (by decide)

private theorem inputKeptAtNE (a : Input) :
    (inputPattern a).keptAt (1,1) = decodedKeptAt (1,1) (a.corners.getD 0 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputKeptAt_ringIndex a 1 (by decide)

private theorem inputKeptAtN (a : Input) :
    (inputPattern a).keptAt (0,1) = decodedKeptAt (0,1) (a.axes.getD 1 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputKeptAt_ringIndex a 2 (by decide)

private theorem inputKeptAtNW (a : Input) :
    (inputPattern a).keptAt (-1,1) = decodedKeptAt (-1,1) (a.corners.getD 1 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputKeptAt_ringIndex a 3 (by decide)

private theorem inputKeptAtW (a : Input) :
    (inputPattern a).keptAt (-1,0) = decodedKeptAt (-1,0) (a.axes.getD 2 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputKeptAt_ringIndex a 4 (by decide)

private theorem inputKeptAtSW (a : Input) :
    (inputPattern a).keptAt (-1,-1) = decodedKeptAt (-1,-1) (a.corners.getD 2 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputKeptAt_ringIndex a 5 (by decide)

private theorem inputKeptAtS (a : Input) :
    (inputPattern a).keptAt (0,-1) = decodedKeptAt (0,-1) (a.axes.getD 3 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputKeptAt_ringIndex a 6 (by decide)

private theorem inputKeptAtSE (a : Input) :
    (inputPattern a).keptAt (1,-1) = decodedKeptAt (1,-1) (a.corners.getD 3 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputKeptAt_ringIndex a 7 (by decide)

private theorem inputStatusAtE (a : Input) :
    (inputPattern a).statusAt (1,0) = decodedStatus (a.axes.getD 0 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputStatusAt_ringIndex a 0 (by decide)

private theorem inputStatusAtNE (a : Input) :
    (inputPattern a).statusAt (1,1) = decodedStatus (a.corners.getD 0 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputStatusAt_ringIndex a 1 (by decide)

private theorem inputStatusAtN (a : Input) :
    (inputPattern a).statusAt (0,1) = decodedStatus (a.axes.getD 1 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputStatusAt_ringIndex a 2 (by decide)

private theorem inputStatusAtNW (a : Input) :
    (inputPattern a).statusAt (-1,1) = decodedStatus (a.corners.getD 1 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputStatusAt_ringIndex a 3 (by decide)

private theorem inputStatusAtW (a : Input) :
    (inputPattern a).statusAt (-1,0) = decodedStatus (a.axes.getD 2 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputStatusAt_ringIndex a 4 (by decide)

private theorem inputStatusAtSW (a : Input) :
    (inputPattern a).statusAt (-1,-1) = decodedStatus (a.corners.getD 2 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputStatusAt_ringIndex a 5 (by decide)

private theorem inputStatusAtS (a : Input) :
    (inputPattern a).statusAt (0,-1) = decodedStatus (a.axes.getD 3 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputStatusAt_ringIndex a 6 (by decide)

private theorem inputStatusAtSE (a : Input) :
    (inputPattern a).statusAt (1,-1) = decodedStatus (a.corners.getD 3 ⟨0,0⟩) := by
  simpa [AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop] using
    inputStatusAt_ringIndex a 7 (by decide)

private theorem memCenterFromE (o : RawOption) :
    (0,0) ∈ decodedKeptAt (1,0) o ↔ hasDirection o.mask 2 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_reverseStep (0,0) o 0 (by decide)

private theorem memCenterFromN (o : RawOption) :
    (0,0) ∈ decodedKeptAt (0,1) o ↔ hasDirection o.mask 3 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_reverseStep (0,0) o 1 (by decide)

private theorem memCenterFromW (o : RawOption) :
    (0,0) ∈ decodedKeptAt (-1,0) o ↔ hasDirection o.mask 0 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_reverseStep (0,0) o 2 (by decide)

private theorem memCenterFromS (o : RawOption) :
    (0,0) ∈ decodedKeptAt (0,-1) o ↔ hasDirection o.mask 1 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_reverseStep (0,0) o 3 (by decide)

private theorem memNEfromE (o : RawOption) :
    (1,1) ∈ decodedKeptAt (1,0) o ↔ hasDirection o.mask 1 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_step (1,0) o 1 (by decide)

private theorem memEfromNE (o : RawOption) :
    (1,0) ∈ decodedKeptAt (1,1) o ↔ hasDirection o.mask 3 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_reverseStep (1,0) o 1 (by decide)

private theorem memNfromNE (o : RawOption) :
    (0,1) ∈ decodedKeptAt (1,1) o ↔ hasDirection o.mask 2 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_reverseStep (0,1) o 0 (by decide)

private theorem memNEfromN (o : RawOption) :
    (1,1) ∈ decodedKeptAt (0,1) o ↔ hasDirection o.mask 0 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_step (0,1) o 0 (by decide)

private theorem memNWfromN (o : RawOption) :
    (-1,1) ∈ decodedKeptAt (0,1) o ↔ hasDirection o.mask 2 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_step (0,1) o 2 (by decide)

private theorem memNfromNW (o : RawOption) :
    (0,1) ∈ decodedKeptAt (-1,1) o ↔ hasDirection o.mask 0 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_reverseStep (0,1) o 2 (by decide)

private theorem memWfromNW (o : RawOption) :
    (-1,0) ∈ decodedKeptAt (-1,1) o ↔ hasDirection o.mask 3 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_reverseStep (-1,0) o 1 (by decide)

private theorem memNWfromW (o : RawOption) :
    (-1,1) ∈ decodedKeptAt (-1,0) o ↔ hasDirection o.mask 1 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_step (-1,0) o 1 (by decide)

private theorem memSWfromW (o : RawOption) :
    (-1,-1) ∈ decodedKeptAt (-1,0) o ↔ hasDirection o.mask 3 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_step (-1,0) o 3 (by decide)

private theorem memWfromSW (o : RawOption) :
    (-1,0) ∈ decodedKeptAt (-1,-1) o ↔ hasDirection o.mask 1 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_reverseStep (-1,0) o 3 (by decide)

private theorem memSfromSW (o : RawOption) :
    (0,-1) ∈ decodedKeptAt (-1,-1) o ↔ hasDirection o.mask 0 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_reverseStep (0,-1) o 2 (by decide)

private theorem memSWfromS (o : RawOption) :
    (-1,-1) ∈ decodedKeptAt (0,-1) o ↔ hasDirection o.mask 2 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_step (0,-1) o 2 (by decide)

private theorem memSEfromS (o : RawOption) :
    (1,-1) ∈ decodedKeptAt (0,-1) o ↔ hasDirection o.mask 0 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_step (0,-1) o 0 (by decide)

private theorem memSfromSE (o : RawOption) :
    (0,-1) ∈ decodedKeptAt (1,-1) o ↔ hasDirection o.mask 2 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_reverseStep (0,-1) o 0 (by decide)

private theorem memEfromSE (o : RawOption) :
    (1,0) ∈ decodedKeptAt (1,-1) o ↔ hasDirection o.mask 1 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_reverseStep (1,0) o 3 (by decide)

private theorem memSEfromE (o : RawOption) :
    (1,-1) ∈ decodedKeptAt (1,0) o ↔ hasDirection o.mask 3 = true := by
  simpa [compassAt, Compass.step] using decodedKeptAt_step (1,0) o 3 (by decide)

private theorem axialCenterBond {i : Nat} (hi : i < 4) (o : RawOption)
    (ho : o ∈ axialOptions i) (hnx : decodedStatus o ≠ .X) :
    hasDirection o.mask ((i+2)%4) = decide (i < 3) := by
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases hcases with h | h | h | h <;> subst i
  · rcases axialCovered (i := 0) (by decide) o ho with hU | hX | ⟨hD, hcard, hcenter⟩
    · have hmask := axialUMask (i := 0) (by decide) o ho
        ((decodedStatus_eq_U_iff o).mp hU)
      simp [hmask, hasDirection]
    · exact False.elim (hnx hX)
    · have hcenter' : (0,0) ∈ decodedKeptAt (1,0) o := by
        simpa [axisSite, AKLT.Cert.H1.ringSites] using hcenter
      simpa using (memCenterFromE o).mp hcenter'
  · rcases axialCovered (i := 1) (by decide) o ho with hU | hX | ⟨hD, hcard, hcenter⟩
    · have hmask := axialUMask (i := 1) (by decide) o ho
        ((decodedStatus_eq_U_iff o).mp hU)
      simp [hmask, hasDirection]
    · exact False.elim (hnx hX)
    · have hcenter' : (0,0) ∈ decodedKeptAt (0,1) o := by
        simpa [axisSite, AKLT.Cert.H1.ringSites] using hcenter
      simpa using (memCenterFromN o).mp hcenter'
  · rcases axialCovered (i := 2) (by decide) o ho with hU | hX | ⟨hD, hcard, hcenter⟩
    · have hmask := axialUMask (i := 2) (by decide) o ho
        ((decodedStatus_eq_U_iff o).mp hU)
      simp [hmask, hasDirection]
    · exact False.elim (hnx hX)
    · have hcenter' : (0,0) ∈ decodedKeptAt (-1,0) o := by
        simpa [axisSite, AKLT.Cert.H1.ringSites] using hcenter
      simpa using (memCenterFromW o).mp hcenter'
  · simp [axialOptions] at ho
    rcases ho with rfl | rfl | rfl | rfl
    · exact False.elim (hnx (by simp [decodedStatus]))
    · simp [hasDirection]
    · simp [hasDirection]
    · simp [hasDirection]

private theorem cornerCompatibleBit (axes : List RawOption) (i : Nat)
    (c : RawOption) (ai d : Nat)
    (hcomp : cornerCompatible axes i c = true)
    (haxis : decodedStatus (axes.getD ai ⟨0,0⟩) ≠ .X)
    (hcorner : decodedStatus c ≠ .X)
    (hpair : (ai,d) ∈ cornerAdjacency i) :
    hasDirection c.mask d =
      hasDirection (axes.getD ai ⟨0,0⟩).mask ((d+2)%4) := by
  have haxisNZ := decodedStatus_ne_X_status_ne_zero (axes.getD ai ⟨0,0⟩) haxis
  have hcornerNZ := decodedStatus_ne_X_status_ne_zero c hcorner
  unfold cornerCompatible at hcomp
  have hcornerZero : (c.status == 0) = false := by
    cases hz : (c.status == 0) with
    | false => rfl
    | true => exact False.elim (hcornerNZ (beq_iff_eq.mp hz))
  have haxisZero : ((axes.getD ai ⟨0,0⟩).status == 0) = false := by
    cases hz : ((axes.getD ai ⟨0,0⟩).status == 0) with
    | false => rfl
    | true => exact False.elim (haxisNZ (beq_iff_eq.mp hz))
  have hbits := (List.all_eq_true.mp hcomp) (ai,d) hpair
  change (c.status == 0 || (axes.getD ai ⟨0,0⟩).status == 0 ||
    hasDirection c.mask d == hasDirection (axes.getD ai ⟨0,0⟩).mask ((d+2)%4)) = true at hbits
  rw [hcornerZero, haxisZero] at hbits
  simpa using beq_iff_eq.mp hbits

private theorem nonTipSites_cases (x : Plane) (hx : x ∈ templateSites \ templateTips) :
    x = (0,0) ∨ x = (1,0) ∨ x = (0,1) ∨ x = (-1,0) ∨ x = (0,-1) ∨
    x = (1,1) ∨ x = (-1,1) ∨ x = (-1,-1) ∨ x = (1,-1) := by
  rcases Finset.mem_sdiff.mp hx with ⟨hsite, hnot⟩
  rcases templateSites_cases x hsite with h0 | he | hn | hw | hs |
    hc0 | hc1 | hc2 | hc3 | ht0 | ht1 | ht2 | ht3
  all_goals simp_all [templateTips]

theorem main : AKLT.Cert.H1.Production.Leaves.inputCovered := by
  intro a h
  cases a with
  | mk axes corners outgoing leafReduced inversion =>
    simp only [inputCheck, Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨⟨⟨⟨⟨⟨haxesLen, hcornersLen⟩, hout⟩, haxesAll⟩,
      hcornersAll⟩, hedges⟩, hstrict⟩, htokens⟩, hslots⟩
    have haxesLen' : axes.length = 4 := by simpa using haxesLen
    have hcornersLen' : corners.length = 4 := by simpa using hcornersLen
    obtain ⟨e, n, w, s, rfl⟩ := list_eq_four_of_length axes haxesLen'
    obtain ⟨c₀, c₁, c₂, c₃, rfl⟩ := list_eq_four_of_length corners hcornersLen'
    let inp : Input := ⟨[e, n, w, s], [c₀, c₁, c₂, c₃], outgoing, leafReduced, inversion⟩
    have he : e ∈ axialOptions 0 := by
      have hh := (List.all_eq_true.mp haxesAll) (e, 0) (by simp)
      exact List.contains_iff_mem.mp (by simpa using hh)
    have hn : n ∈ axialOptions 1 := by
      have hh := (List.all_eq_true.mp haxesAll) (n, 1) (by simp)
      exact List.contains_iff_mem.mp (by simpa using hh)
    have hw : w ∈ axialOptions 2 := by
      have hh := (List.all_eq_true.mp haxesAll) (w, 2) (by simp)
      exact List.contains_iff_mem.mp (by simpa using hh)
    have hs : s ∈ axialOptions 3 := by
      have hh := (List.all_eq_true.mp haxesAll) (s, 3) (by simp)
      exact List.contains_iff_mem.mp (by simpa using hh)
    have hc₀ : c₀ ∈ cornerOptions ∧ cornerCompatible [e, n, w, s] 0 c₀ = true := by
      have hh := (List.all_eq_true.mp hcornersAll) (c₀, 0) (by simp)
      have hb : cornerOptions.contains c₀ = true ∧
          cornerCompatible [e, n, w, s] 0 c₀ = true := by
        simpa only [Bool.and_eq_true] using hh
      exact ⟨List.contains_iff_mem.mp hb.1, hb.2⟩
    have hc₁ : c₁ ∈ cornerOptions ∧ cornerCompatible [e, n, w, s] 1 c₁ = true := by
      have hh := (List.all_eq_true.mp hcornersAll) (c₁, 1) (by simp)
      have hb : cornerOptions.contains c₁ = true ∧
          cornerCompatible [e, n, w, s] 1 c₁ = true := by
        simpa only [Bool.and_eq_true] using hh
      exact ⟨List.contains_iff_mem.mp hb.1, hb.2⟩
    have hc₂ : c₂ ∈ cornerOptions ∧ cornerCompatible [e, n, w, s] 2 c₂ = true := by
      have hh := (List.all_eq_true.mp hcornersAll) (c₂, 2) (by simp)
      have hb : cornerOptions.contains c₂ = true ∧
          cornerCompatible [e, n, w, s] 2 c₂ = true := by
        simpa only [Bool.and_eq_true] using hh
      exact ⟨List.contains_iff_mem.mp hb.1, hb.2⟩
    have hc₃ : c₃ ∈ cornerOptions ∧ cornerCompatible [e, n, w, s] 3 c₃ = true := by
      have hh := (List.all_eq_true.mp hcornersAll) (c₃, 3) (by simp)
      have hb : cornerOptions.contains c₃ = true ∧
          cornerCompatible [e, n, w, s] 3 c₃ = true := by
        simpa only [Bool.and_eq_true] using hh
      exact ⟨List.contains_iff_mem.mp hb.1, hb.2⟩
    clear hstrict htokens hslots
    simp only [AKLT.Defs.PatternData.Covered]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hout' : outgoing < 3 := of_decide_eq_true hout
      interval_cases outgoing <;> simp [inputPattern, compassAt]
    · simp [inputPattern, PatternData.statusAt, templateSites, square, latticeDist,
        templateTips, compassAt]
    · simp [inputPattern, PatternData.keptAt, templateSites, square, latticeDist,
        Compass.step, compassAt]
    · simp [axialOptions] at hs
      rcases hs with hs | hs | hs | hs
      · subst s
        simp [inputPattern, PatternData.statusAt, PatternData.keptAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop, templateSites, square, latticeDist,
          hasDirection, compassAt, Compass.step]
      · subst s
        simp [inputPattern, PatternData.statusAt, PatternData.keptAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop, templateSites, square, latticeDist,
          hasDirection, compassAt, Compass.step]
      · subst s
        simp [inputPattern, PatternData.statusAt, PatternData.keptAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop, templateSites, square, latticeDist,
          hasDirection, compassAt, Compass.step]
      · subst s
        simp [inputPattern, PatternData.statusAt, PatternData.keptAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop, templateSites, square, latticeDist,
          hasDirection, compassAt, Compass.step]
    · intro d hd
      cases d <;> simp at hd
      · have hcov := axialCovered (i := 0) (by decide) e he
        simpa [inputPattern, PatternData.statusAt, PatternData.keptAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop, templateSites,
          square, latticeDist, decodedStatus, decodedKeptAt, axisSite, hasDirection,
          compassAt, Compass.step] using hcov
      · have hcov := axialCovered (i := 1) (by decide) n hn
        simpa [inputPattern, PatternData.statusAt, PatternData.keptAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop, templateSites,
          square, latticeDist, decodedStatus, decodedKeptAt, axisSite, hasDirection,
          compassAt, Compass.step] using hcov
      · have hcov := axialCovered (i := 2) (by decide) w hw
        simpa [inputPattern, PatternData.statusAt, PatternData.keptAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop, templateSites,
          square, latticeDist, decodedStatus, decodedKeptAt, axisSite, hasDirection,
          compassAt, Compass.step] using hcov
    · have hout' : outgoing < 3 := of_decide_eq_true hout
      interval_cases outgoing
      · have hraw : (rawEdges [e, n, w, s] [c₀, c₁, c₂, c₃]).getD 0 false = true := by
          simpa using hedges
        have hbits : e.status != 0 ∧ hasDirection e.mask 2 = true := by
          simpa [rawEdges, ringOptions, List.range, List.range.loop] using hraw
        have hnonzero := axialNonzeroStatus (i := 0) (by decide) e he hbits.1
        simpa [inputPattern, PatternData.statusAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop,
          templateSites, square, latticeDist, decodedStatus, compassAt, Compass.step] using hnonzero
      · have hraw : (rawEdges [e, n, w, s] [c₀, c₁, c₂, c₃]).getD 1 false = true := by
          simpa using hedges
        have hbits : n.status != 0 ∧ hasDirection n.mask 3 = true := by
          simpa [rawEdges, ringOptions, List.range, List.range.loop] using hraw
        have hnonzero := axialNonzeroStatus (i := 1) (by decide) n hn hbits.1
        simpa [inputPattern, PatternData.statusAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop,
          templateSites, square, latticeDist, decodedStatus, compassAt, Compass.step] using hnonzero
      · have hraw : (rawEdges [e, n, w, s] [c₀, c₁, c₂, c₃]).getD 2 false = true := by
          simpa using hedges
        have hbits : w.status != 0 ∧ hasDirection w.mask 0 = true := by
          simpa [rawEdges, ringOptions, List.range, List.range.loop] using hraw
        have hnonzero := axialNonzeroStatus (i := 2) (by decide) w hw hbits.1
        simpa [inputPattern, PatternData.statusAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop,
          templateSites, square, latticeDist, decodedStatus, compassAt, Compass.step] using hnonzero
    · intro x hx
      simp [templateCorners] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · have hcov := cornerCoveredAt (1,1) c₀ hc₀.1
        simpa [inputPattern, PatternData.statusAt, PatternData.keptAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop, templateSites,
          square, latticeDist, decodedStatus, decodedKeptAt, hasDirection, compassAt,
          Compass.step] using hcov
      · have hcov := cornerCoveredAt (-1,1) c₁ hc₁.1
        simpa [inputPattern, PatternData.statusAt, PatternData.keptAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop, templateSites,
          square, latticeDist, decodedStatus, decodedKeptAt, hasDirection, compassAt,
          Compass.step] using hcov
      · have hcov := cornerCoveredAt (-1,-1) c₂ hc₂.1
        simpa [inputPattern, PatternData.statusAt, PatternData.keptAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop, templateSites,
          square, latticeDist, decodedStatus, decodedKeptAt, hasDirection, compassAt,
          Compass.step] using hcov
      · have hcov := cornerCoveredAt (1,-1) c₃ hc₃.1
        simpa [inputPattern, PatternData.statusAt, PatternData.keptAt, Input.optionAt,
          AKLT.Cert.H1.ringSites, ringOptions, List.range, List.range.loop, templateSites,
          square, latticeDist, decodedStatus, decodedKeptAt, hasDirection, compassAt,
          Compass.step] using hcov
    · intro x hx hxcenter hxtip hxU
      have hsites := templateSites_cases x hx
      rcases hsites with h0 | heq | hnq | hwq | hsq | hc0q | hc1q | hc2q | hc3q |
        ht0q | ht1q | ht2q | ht3q
      · subst x
        exact (hxcenter rfl).elim
      · subst x
        have hmem : ((1,0) : Plane) ∈ templateSites := by simp [templateSites, square, latticeDist]
        have hnc : ((1,0) : Plane) ≠ (0,0) := by decide
        have hnt : ((1,0) : Plane) ∉ templateTips := by simp [templateTips]
        have hs := inputStatusAtRing inp (1,0) hmem hnc hnt
        have hU' : (inputPattern inp).statusAt (1,0) = .U := by simpa [inp] using hxU
        rw [hs] at hU'
        have hdecode : decodedStatus e = .U := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hU'
        have hsrc := (decodedStatus_eq_U_iff e).mp hdecode
        have hmask := axialUMask (i := 0) (by decide) e he hsrc
        have hm : (inp.optionAt (1,0)).mask = 15 := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hmask
        have hkeep := inputKeptAtFull inp (1,0) hmem hnc hm
        simpa [inp] using hkeep
      · subst x
        have hmem : ((0,1) : Plane) ∈ templateSites := by simp [templateSites, square, latticeDist]
        have hnc : ((0,1) : Plane) ≠ (0,0) := by decide
        have hnt : ((0,1) : Plane) ∉ templateTips := by simp [templateTips]
        have hs := inputStatusAtRing inp (0,1) hmem hnc hnt
        have hU' : (inputPattern inp).statusAt (0,1) = .U := by simpa [inp] using hxU
        rw [hs] at hU'
        have hdecode : decodedStatus n = .U := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hU'
        have hsrc := (decodedStatus_eq_U_iff n).mp hdecode
        have hmask := axialUMask (i := 1) (by decide) n hn hsrc
        have hm : (inp.optionAt (0,1)).mask = 15 := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hmask
        have hkeep := inputKeptAtFull inp (0,1) hmem hnc hm
        simpa [inp] using hkeep
      · subst x
        have hmem : ((-1,0) : Plane) ∈ templateSites := by simp [templateSites, square, latticeDist]
        have hnc : ((-1,0) : Plane) ≠ (0,0) := by decide
        have hnt : ((-1,0) : Plane) ∉ templateTips := by simp [templateTips]
        have hs := inputStatusAtRing inp (-1,0) hmem hnc hnt
        have hU' : (inputPattern inp).statusAt (-1,0) = .U := by simpa [inp] using hxU
        rw [hs] at hU'
        have hdecode : decodedStatus w = .U := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hU'
        have hsrc := (decodedStatus_eq_U_iff w).mp hdecode
        have hmask := axialUMask (i := 2) (by decide) w hw hsrc
        have hm : (inp.optionAt (-1,0)).mask = 15 := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hmask
        have hkeep := inputKeptAtFull inp (-1,0) hmem hnc hm
        simpa [inp] using hkeep
      · subst x
        have hmem : ((0,-1) : Plane) ∈ templateSites := by simp [templateSites, square, latticeDist]
        have hnc : ((0,-1) : Plane) ≠ (0,0) := by decide
        have hnt : ((0,-1) : Plane) ∉ templateTips := by simp [templateTips]
        have hs' := inputStatusAtRing inp (0,-1) hmem hnc hnt
        have hU' : (inputPattern inp).statusAt (0,-1) = .U := by simpa [inp] using hxU
        rw [hs'] at hU'
        have hdecode : decodedStatus s = .U := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hU'
        have hsrc := (decodedStatus_eq_U_iff s).mp hdecode
        simp [axialOptions] at hs
        rcases hs with rfl | rfl | rfl | rfl <;> simp_all
      · subst x
        have hmem : ((1,1) : Plane) ∈ templateSites := by simp [templateSites, square, latticeDist]
        have hnc : ((1,1) : Plane) ≠ (0,0) := by decide
        have hnt : ((1,1) : Plane) ∉ templateTips := by simp [templateTips]
        have hs := inputStatusAtRing inp (1,1) hmem hnc hnt
        have hU' : (inputPattern inp).statusAt (1,1) = .U := by simpa [inp] using hxU
        rw [hs] at hU'
        have hdecode : decodedStatus c₀ = .U := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hU'
        have hsrc := (decodedStatus_eq_U_iff c₀).mp hdecode
        have hmask := cornerUMask c₀ hc₀.1 hsrc
        have hm : (inp.optionAt (1,1)).mask = 15 := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hmask
        have hkeep := inputKeptAtFull inp (1,1) hmem hnc hm
        simpa [inp] using hkeep
      · subst x
        have hmem : ((-1,1) : Plane) ∈ templateSites := by simp [templateSites, square, latticeDist]
        have hnc : ((-1,1) : Plane) ≠ (0,0) := by decide
        have hnt : ((-1,1) : Plane) ∉ templateTips := by simp [templateTips]
        have hs := inputStatusAtRing inp (-1,1) hmem hnc hnt
        have hU' : (inputPattern inp).statusAt (-1,1) = .U := by simpa [inp] using hxU
        rw [hs] at hU'
        have hdecode : decodedStatus c₁ = .U := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hU'
        have hsrc := (decodedStatus_eq_U_iff c₁).mp hdecode
        have hmask := cornerUMask c₁ hc₁.1 hsrc
        have hm : (inp.optionAt (-1,1)).mask = 15 := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hmask
        have hkeep := inputKeptAtFull inp (-1,1) hmem hnc hm
        simpa [inp] using hkeep
      · subst x
        have hmem : ((-1,-1) : Plane) ∈ templateSites := by simp [templateSites, square, latticeDist]
        have hnc : ((-1,-1) : Plane) ≠ (0,0) := by decide
        have hnt : ((-1,-1) : Plane) ∉ templateTips := by simp [templateTips]
        have hs := inputStatusAtRing inp (-1,-1) hmem hnc hnt
        have hU' : (inputPattern inp).statusAt (-1,-1) = .U := by simpa [inp] using hxU
        rw [hs] at hU'
        have hdecode : decodedStatus c₂ = .U := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hU'
        have hsrc := (decodedStatus_eq_U_iff c₂).mp hdecode
        have hmask := cornerUMask c₂ hc₂.1 hsrc
        have hm : (inp.optionAt (-1,-1)).mask = 15 := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hmask
        have hkeep := inputKeptAtFull inp (-1,-1) hmem hnc hm
        simpa [inp] using hkeep
      · subst x
        have hmem : ((1,-1) : Plane) ∈ templateSites := by simp [templateSites, square, latticeDist]
        have hnc : ((1,-1) : Plane) ≠ (0,0) := by decide
        have hnt : ((1,-1) : Plane) ∉ templateTips := by simp [templateTips]
        have hs := inputStatusAtRing inp (1,-1) hmem hnc hnt
        have hU' : (inputPattern inp).statusAt (1,-1) = .U := by simpa [inp] using hxU
        rw [hs] at hU'
        have hdecode : decodedStatus c₃ = .U := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hU'
        have hsrc := (decodedStatus_eq_U_iff c₃).mp hdecode
        have hmask := cornerUMask c₃ hc₃.1 hsrc
        have hm : (inp.optionAt (1,-1)).mask = 15 := by
          simpa [inp, Input.optionAt, AKLT.Cert.H1.ringSites, ringOptions,
            List.range, List.range.loop] using hmask
        have hkeep := inputKeptAtFull inp (1,-1) hmem hnc hm
        simpa [inp] using hkeep
      · subst x
        exact (hxtip (by simp [templateTips])).elim
      · subst x
        exact (hxtip (by simp [templateTips])).elim
      · subst x
        exact (hxtip (by simp [templateTips])).elim
      · subst x
        exact (hxtip (by simp [templateTips])).elim
    · intro x hx
      simp [templateTips] at hx
      rcases hx with rfl | rfl | rfl | rfl
      all_goals
        simp [inputPattern, PatternData.statusAt, templateSites, square, latticeDist,
          Compass.step, compassAt]
    · intro x hx y hy hxNX hyNX hadj
      rcases nonTipSites_cases x hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals
        rcases nonTipSites_cases y hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [Adjacent, latticeDist] at hadj
      all_goals
        simp [inputCenterStatus, inputStatusAtE, inputStatusAtNE, inputStatusAtN,
          inputStatusAtNW, inputStatusAtW, inputStatusAtSW, inputStatusAtS,
          inputStatusAtSE] at hxNX hyNX
        simp [inputCenterKept, inputKeptAtE, inputKeptAtNE, inputKeptAtN,
          inputKeptAtNW, inputKeptAtW, inputKeptAtSW, inputKeptAtS,
          inputKeptAtSE, memCenterFromE, memCenterFromN, memCenterFromW,
          memCenterFromS, memNEfromE, memEfromNE, memNfromNE, memNEfromN,
          memNWfromN, memNfromNW, memWfromNW, memNWfromW, memSWfromW,
          memWfromSW, memSfromSW, memSWfromS, memSEfromS, memSfromSE,
          memEfromSE, memSEfromE] at ⊢
      all_goals
        first
        | exact axialCenterBond (i := 0) (by decide) e he hxNX
        | exact axialCenterBond (i := 0) (by decide) e he hyNX
        | exact axialCenterBond (i := 1) (by decide) n hn hxNX
        | exact axialCenterBond (i := 1) (by decide) n hn hyNX
        | exact axialCenterBond (i := 2) (by decide) w hw hxNX
        | exact axialCenterBond (i := 2) (by decide) w hw hyNX
        | exact axialCenterBond (i := 3) (by decide) s hs hxNX
        | exact axialCenterBond (i := 3) (by decide) s hs hyNX
        | skip
      all_goals
        first
        | (guard_target = hasDirection c₀.mask 3 = hasDirection e.mask 1; exact
            cornerCompatibleBit [e,n,w,s] 0 c₀ 0 3 hc₀.2 hyNX hxNX (by simp [cornerAdjacency]))
        | (guard_target = hasDirection e.mask 1 = hasDirection c₀.mask 3; exact
            (cornerCompatibleBit [e,n,w,s] 0 c₀ 0 3 hc₀.2 hxNX hyNX (by simp [cornerAdjacency])).symm)
        | (guard_target = hasDirection c₀.mask 2 = hasDirection n.mask 0; exact
            cornerCompatibleBit [e,n,w,s] 0 c₀ 1 2 hc₀.2 hyNX hxNX (by simp [cornerAdjacency]))
        | (guard_target = hasDirection n.mask 0 = hasDirection c₀.mask 2; exact
            (cornerCompatibleBit [e,n,w,s] 0 c₀ 1 2 hc₀.2 hxNX hyNX (by simp [cornerAdjacency])).symm)
        | (guard_target = hasDirection c₁.mask 0 = hasDirection n.mask 2; exact
            cornerCompatibleBit [e,n,w,s] 1 c₁ 1 0 hc₁.2 hyNX hxNX (by simp [cornerAdjacency]))
        | (guard_target = hasDirection n.mask 2 = hasDirection c₁.mask 0; exact
            (cornerCompatibleBit [e,n,w,s] 1 c₁ 1 0 hc₁.2 hxNX hyNX (by simp [cornerAdjacency])).symm)
        | (guard_target = hasDirection c₁.mask 3 = hasDirection w.mask 1; exact
            cornerCompatibleBit [e,n,w,s] 1 c₁ 2 3 hc₁.2 hyNX hxNX (by simp [cornerAdjacency]))
        | (guard_target = hasDirection w.mask 1 = hasDirection c₁.mask 3; exact
            (cornerCompatibleBit [e,n,w,s] 1 c₁ 2 3 hc₁.2 hxNX hyNX (by simp [cornerAdjacency])).symm)
        | (guard_target = hasDirection c₂.mask 1 = hasDirection w.mask 3; exact
            cornerCompatibleBit [e,n,w,s] 2 c₂ 2 1 hc₂.2 hyNX hxNX (by simp [cornerAdjacency]))
        | (guard_target = hasDirection w.mask 3 = hasDirection c₂.mask 1; exact
            (cornerCompatibleBit [e,n,w,s] 2 c₂ 2 1 hc₂.2 hxNX hyNX (by simp [cornerAdjacency])).symm)
        | (guard_target = hasDirection c₂.mask 0 = hasDirection s.mask 2; exact
            cornerCompatibleBit [e,n,w,s] 2 c₂ 3 0 hc₂.2 hyNX hxNX (by simp [cornerAdjacency]))
        | (guard_target = hasDirection s.mask 2 = hasDirection c₂.mask 0; exact
            (cornerCompatibleBit [e,n,w,s] 2 c₂ 3 0 hc₂.2 hxNX hyNX (by simp [cornerAdjacency])).symm)
        | (guard_target = hasDirection c₃.mask 2 = hasDirection s.mask 0; exact
            cornerCompatibleBit [e,n,w,s] 3 c₃ 3 2 hc₃.2 hyNX hxNX (by simp [cornerAdjacency]))
        | (guard_target = hasDirection s.mask 0 = hasDirection c₃.mask 2; exact
            (cornerCompatibleBit [e,n,w,s] 3 c₃ 3 2 hc₃.2 hxNX hyNX (by simp [cornerAdjacency])).symm)
        | (guard_target = hasDirection c₃.mask 1 = hasDirection e.mask 3; exact
            cornerCompatibleBit [e,n,w,s] 3 c₃ 0 1 hc₃.2 hyNX hxNX (by simp [cornerAdjacency]))
        | (guard_target = hasDirection e.mask 3 = hasDirection c₃.mask 1; exact
            (cornerCompatibleBit [e,n,w,s] 3 c₃ 0 1 hc₃.2 hxNX hyNX (by simp [cornerAdjacency])).symm)
        | skip

end AKLT.W.H1C007
