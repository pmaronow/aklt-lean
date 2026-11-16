import AKLT.Blueprint.Q.NodesEnergy

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Q

namespace AKLT.W.Q052

lemma sum_fullFibre {W : Finset Plane} (x : W) (σ : PlaneConfiguration W)
    (f : PlaneConfiguration W → ℝ) :
    (by classical exact (∑ τ, if fullFibreEvent x σ τ then f τ else 0) =
      ∑ a : IcoLetter, f (Function.update σ x a)) := by
  classical
  symm
  apply Fintype.sum_of_injective (fun a : IcoLetter => Function.update σ x a)
    (Function.update_injective σ x)
    (fun a => f (Function.update σ x a))
    (fun τ => if fullFibreEvent x σ τ then f τ else 0)
  · intro τ hτ
    change ¬ ∃ a, Function.update σ x a = τ at hτ
    have hnot : ¬ fullFibreEvent x σ τ := by
      intro he
      apply hτ
      refine ⟨τ x, ?_⟩
      funext y
      by_cases hy : y = x
      · subst y
        simp
      · simp [Function.update_of_ne hy, he y hy]
    simp [hnot]
  · intro a
    have he : fullFibreEvent x σ (Function.update σ x a) := by
      intro y hy
      simp [Function.update_of_ne hy]
    simp [he]

lemma internal_adj {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds W) : Adjacent e.1 e.2 := by
  classical
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image] at he
  rcases he with ⟨u, hu, v, hv, huv⟩
  cases huv
  rcases Finset.mem_inter.mp hv with ⟨hpos, _⟩
  simp [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hpos
  rcases hpos with hpos | hpos
  · have h1 : u.1 + 1 = v.1 := by simpa using (congrArg Prod.fst hpos).symm
    have h2 : u.2 = v.2 := by simpa using (congrArg Prod.snd hpos).symm
    have hfst : u.1 - v.1 = -1 := by omega
    have hsnd : u.2 - v.2 = 0 := by omega
    norm_num [Adjacent, latticeDist, hfst, hsnd]
  · have h1 : u.1 = v.1 := by simpa using (congrArg Prod.fst hpos).symm
    have h2 : u.2 + 1 = v.2 := by simpa using (congrArg Prod.snd hpos).symm
    have hfst : u.1 - v.1 = 0 := by omega
    have hsnd : u.2 - v.2 = -1 := by omega
    norm_num [Adjacent, latticeDist, hfst, hsnd]

lemma internal_orientation {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds W) :
    e.2 = e.1 + (1, 0) ∨ e.2 = e.1 + (0, 1) := by
  classical
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image] at he
  rcases he with ⟨u, hu, v, hv, huv⟩
  cases huv
  rcases Finset.mem_inter.mp hv with ⟨hpos, _⟩
  simp [positiveNeighbours, Finset.mem_insert, Finset.mem_singleton] at hpos
  rcases hpos with hpos | hpos
  · left
    apply Prod.ext
    · simpa [Prod.fst_add, Prod.snd_add] using (congrArg Prod.fst hpos)
    · simpa [Prod.fst_add, Prod.snd_add] using (congrArg Prod.snd hpos)
  · right
    apply Prod.ext
    · simpa [Prod.fst_add, Prod.snd_add] using (congrArg Prod.fst hpos)
    · simpa [Prod.fst_add, Prod.snd_add] using (congrArg Prod.snd hpos)

lemma internal_no_reverse {W : Finset Plane} {u v : Plane}
    (h : (u, v) ∈ internalBonds W) (h' : (v, u) ∈ internalBonds W) : False := by
  rcases internal_orientation h with h | h
  · rcases internal_orientation h' with h' | h'
    · have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.fst h'
      simp [Prod.fst_add, Prod.snd_add] at h1 h2
      omega
    · have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.fst h'
      simp [Prod.fst_add, Prod.snd_add] at h1 h2
      omega
  · rcases internal_orientation h' with h' | h'
    · have h1 := congrArg Prod.snd h
      have h2 := congrArg Prod.snd h'
      simp [Prod.fst_add, Prod.snd_add] at h1 h2
      omega
    · have h1 := congrArg Prod.snd h
      have h2 := congrArg Prod.snd h'
      simp [Prod.fst_add, Prod.snd_add] at h1 h2
      omega

lemma internal_no_self {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds W) : e.1 ≠ e.2 := by
  rcases e with ⟨u, v⟩
  intro h
  have ha := internal_adj he
  change Adjacent u v at ha
  change u = v at h
  subst v
  simp [Adjacent, latticeDist] at ha

lemma internal_endpoints_mem {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ internalBonds W) : e.1 ∈ W ∧ e.2 ∈ W := by
  classical
  simp only [internalBonds, Finset.mem_biUnion, Finset.mem_image] at he
  rcases he with ⟨u, hu, v, hv, huv⟩
  cases huv
  exact ⟨hu, (Finset.mem_inter.mp hv).2⟩

lemma leg_target_not_mem {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs W) : e.2 ∉ W := by
  classical
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image] at he
  rcases he with ⟨u, hu, v, hv, huv⟩
  cases huv
  exact (Finset.mem_sdiff.mp hv).2

lemma leg_adj {W : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs W) : Adjacent e.1 e.2 := by
  classical
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image] at he
  rcases he with ⟨u, hu, v, hv, huv⟩
  cases huv
  change latticeDist u v = 1
  have hv' : v ∈ neighbours u := (Finset.mem_sdiff.mp hv).1
  simp only [neighbours, Finset.mem_image, Finset.mem_univ, true_and] at hv'
  rcases hv' with ⟨d, hd⟩
  cases d <;> simp [Compass.step] at hd
  · have hx : u.1 + 1 = v.1 := by simpa using congrArg Prod.fst hd
    have hy : u.2 = v.2 := by simpa using congrArg Prod.snd hd
    have h1 : u.1 - v.1 = -1 := by omega
    have h2 : u.2 - v.2 = 0 := by omega
    norm_num [latticeDist, h1, h2]
  · have hx : u.1 = v.1 := by simpa using congrArg Prod.fst hd
    have hy : u.2 + 1 = v.2 := by simpa using congrArg Prod.snd hd
    have h1 : u.1 - v.1 = 0 := by omega
    have h2 : u.2 - v.2 = -1 := by omega
    norm_num [latticeDist, h1, h2]
  · have hx : u.1 + -1 = v.1 := by simpa using congrArg Prod.fst hd
    have hy : u.2 = v.2 := by simpa using congrArg Prod.snd hd
    have h1 : u.1 - v.1 = 1 := by omega
    have h2 : u.2 - v.2 = 0 := by omega
    norm_num [latticeDist, h1, h2]
  · have hx : u.1 = v.1 := by simpa using congrArg Prod.fst hd
    have hy : u.2 + -1 = v.2 := by simpa using congrArg Prod.snd hd
    have h1 : u.1 - v.1 = 0 := by omega
    have h2 : u.2 - v.2 = 1 := by omega
    norm_num [latticeDist, h1, h2]

lemma adjacent_mem_neighbours {x y : Plane} (h : Adjacent x y) : y ∈ neighbours x := by
  classical
  have hsum : (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = 1 := h
  have hcases :
      ((x.1 - y.1).natAbs = 1 ∧ (x.2 - y.2).natAbs = 0) ∨
      ((x.1 - y.1).natAbs = 0 ∧ (x.2 - y.2).natAbs = 1) := by omega
  rcases hcases with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · rcases Int.natAbs_eq_iff.mp hx with hx | hx
    · have hy' : x.2 - y.2 = 0 := Int.natAbs_eq_zero.mp hy
      have hp : y = x + Compass.west.step := by
        apply Prod.ext <;> simp [Compass.step] <;> omega
      apply Finset.mem_image.mpr
      exact ⟨Compass.west, Finset.mem_univ _, hp.symm⟩
    · have hy' : x.2 - y.2 = 0 := Int.natAbs_eq_zero.mp hy
      have hp : y = x + Compass.east.step := by
        apply Prod.ext <;> simp [Compass.step] <;> omega
      apply Finset.mem_image.mpr
      exact ⟨Compass.east, Finset.mem_univ _, hp.symm⟩
  · have hx' : x.1 - y.1 = 0 := Int.natAbs_eq_zero.mp hx
    rcases Int.natAbs_eq_iff.mp hy with hy | hy
    · have hp : y = x + Compass.south.step := by
        apply Prod.ext <;> simp [Compass.step] <;> omega
      apply Finset.mem_image.mpr
      exact ⟨Compass.south, Finset.mem_univ _, hp.symm⟩
    · have hp : y = x + Compass.north.step := by
        apply Prod.ext <;> simp [Compass.step] <;> omega
      apply Finset.mem_image.mpr
      exact ⟨Compass.north, Finset.mem_univ _, hp.symm⟩

def internalAt (W : Finset Plane) (x : W) : Finset (Plane × Plane) :=
  (internalBonds W).filter fun e => e.1 = x.val ∨ e.2 = x.val

def legsAt (W : Finset Plane) (x : W) : Finset (Plane × Plane) :=
  (originalLegs W).filter fun e => e.1 = x.val

def internalAway (W : Finset Plane) (x : W) : Finset (Plane × Plane) :=
  (internalBonds W).filter fun e => e.1 ≠ x.val ∧ e.2 ≠ x.val

def legsAway (W : Finset Plane) (x : W) : Finset (Plane × Plane) :=
  (originalLegs W).filter fun e => e.1 ≠ x.val

def internalFactor {W : Finset Plane} (κ : Plane → Fin 3)
    (σ : PlaneConfiguration W) (e : Plane × Plane) : ℝ :=
  1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
    (frameVector (κ e.2) (extendLetters σ e.2))

def legFactor {W : Finset Plane} (κ : Plane → Fin 3) (η : FrameBoundary W)
    (σ : PlaneConfiguration W) (e : Plane × Plane) : ℝ :=
  1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
    (frameVector (κ e.2) (extendBoundary η e.2))

lemma extendLetters_update_ne {W : Finset Plane} (x : W) (σ : PlaneConfiguration W)
    (a : IcoLetter) {z : Plane} (hz : z ≠ x.val) :
    extendLetters (Function.update σ x a) z = extendLetters σ z := by
  classical
  unfold extendLetters
  by_cases hzw : z ∈ W
  · have hzx : (⟨z, hzw⟩ : W) ≠ x := by
      intro he
      exact hz (congrArg Subtype.val he)
    simp [hzw, Function.update_of_ne hzx]
  · simp [hzw]

def localWeight {W : Finset Plane} (κ : Plane → Fin 3) (η : FrameBoundary W)
    (σ : PlaneConfiguration W) (x : W) : ℝ :=
  (∏ e ∈ internalAt W x, internalFactor κ σ e) *
    ∏ e ∈ legsAt W x, legFactor κ η σ e

def fixedWeight {W : Finset Plane} (κ : Plane → Fin 3) (η : FrameBoundary W)
    (σ : PlaneConfiguration W) (x : W) : ℝ :=
  (1 / 12 : ℝ) ^ W.card *
    ((∏ e ∈ internalAway W x, internalFactor κ σ e) *
      ∏ e ∈ legsAway W x, legFactor κ η σ e)

def localIndex (W : Finset Plane) (x : W) : Finset (Bool × (Plane × Plane)) :=
  Finset.image (fun e => (false, e)) (internalAt W x) ∪
    Finset.image (fun e => (true, e)) (legsAt W x)

def indexNeighbour {W : Finset Plane} (x : W) (q : Bool × (Plane × Plane)) : Plane :=
  if q.1 = false then if q.2.1 = x.val then q.2.2 else q.2.1 else q.2.2

lemma localIndex_card {W : Finset Plane} (x : W) :
    (localIndex W x).card = (internalAt W x).card + (legsAt W x).card := by
  classical
  unfold localIndex
  have hi_card : (Finset.image (fun e => (false, e)) (internalAt W x)).card =
      (internalAt W x).card := Finset.card_image_iff.mpr (by
    intro e he f hf h
    exact congrArg Prod.snd h)
  have hl_card : (Finset.image (fun e => (true, e)) (legsAt W x)).card =
      (legsAt W x).card := Finset.card_image_iff.mpr (by
    intro e he f hf h
    exact congrArg Prod.snd h)
  have hd : Disjoint (Finset.image (fun e => (false, e)) (internalAt W x))
      (Finset.image (fun e => (true, e)) (legsAt W x)) := by
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
    rcases Finset.mem_image.mp hq' with ⟨f, hf, hEq⟩
    cases hEq
  calc
    (Finset.image (fun e => (false, e)) (internalAt W x) ∪
      Finset.image (fun e => (true, e)) (legsAt W x)).card =
        (Finset.image (fun e => (false, e)) (internalAt W x)).card +
          (Finset.image (fun e => (true, e)) (legsAt W x)).card := Finset.card_union_of_disjoint hd
    _ = (internalAt W x).card + (legsAt W x).card := by
      rw [hi_card, hl_card]

lemma neighbours_card_le_four (x : Plane) : (neighbours x).card ≤ 4 := by
  classical
  unfold neighbours
  calc
    (Finset.univ.image (fun d : Compass => x + d.step)).card ≤ Finset.univ.card :=
      Finset.card_image_le
    _ = 4 := by decide

lemma adjacent_symm {u v : Plane} (h : Adjacent u v) : Adjacent v u := by
  have h1 : v.1 - u.1 = -(u.1 - v.1) := by ring
  have h2 : v.2 - u.2 = -(u.2 - v.2) := by ring
  rw [Adjacent, latticeDist] at h ⊢
  rw [h1, h2, Int.natAbs_neg, Int.natAbs_neg]
  simpa [Nat.add_comm] using h

lemma indexNeighbour_maps {W : Finset Plane} (x : W)
    {q : Bool × (Plane × Plane)} (hq : q ∈ localIndex W x) :
    indexNeighbour x q ∈ neighbours x := by
  classical
  unfold localIndex at hq
  rcases Finset.mem_union.mp hq with hq | hq
  · rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
    have hI := (Finset.mem_filter.mp he).1
    rcases (Finset.mem_filter.mp he).2 with hs | ht
    · have ha : Adjacent x.val e.2 := by simpa [hs] using internal_adj hI
      simpa [indexNeighbour, hs] using adjacent_mem_neighbours ha
    · have ha : Adjacent x.val e.1 := by
        exact adjacent_symm (by simpa [ht] using internal_adj hI)
      have hne : e.1 ≠ x.val := by
        intro heq
        exact internal_no_self hI (heq.trans ht.symm)
      simpa [indexNeighbour, hne] using adjacent_mem_neighbours ha
  · rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
    have hL := (Finset.mem_filter.mp he).1
    have hs := (Finset.mem_filter.mp he).2
    have ha : Adjacent x.val e.2 := by simpa [hs] using leg_adj hL
    simpa [indexNeighbour, hs] using adjacent_mem_neighbours ha

lemma indexNeighbour_injOn {W : Finset Plane} (x : W) :
    Set.InjOn (indexNeighbour x) (↑(localIndex W x) : Set (Bool × (Plane × Plane))) := by
  classical
  intro q hq r hr hEq
  unfold localIndex at hq hr
  rcases Finset.mem_union.mp hq with hq | hq
  · rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
    rcases Finset.mem_union.mp hr with hr | hr
    · rcases Finset.mem_image.mp hr with ⟨f, hf, rfl⟩
      have hI := (Finset.mem_filter.mp he).1
      have hJ := (Finset.mem_filter.mp hf).1
      rcases (Finset.mem_filter.mp he).2 with hs | ht
      · rcases (Finset.mem_filter.mp hf).2 with hs' | ht'
        · have htar : e.2 = f.2 := by simpa [indexNeighbour, hs, hs'] using hEq
          have hsrc : e.1 = f.1 := hs.trans hs'.symm
          have hef : e = f := Prod.ext hsrc htar
          subst f
          rfl
        · have hne : f.1 ≠ x.val := by
            intro hf1
            exact internal_no_self hJ (hf1.trans ht'.symm)
          have htar : e.2 = f.1 := by simpa [indexNeighbour, hs, hne] using hEq
          have hrev : f = (e.2, e.1) := by
            apply Prod.ext
            · exact htar.symm
            · exact ht'.trans hs.symm
          rw [hrev] at hJ
          exact False.elim (internal_no_reverse hI hJ)
      · rcases (Finset.mem_filter.mp hf).2 with hs' | ht'
        · have hne : e.1 ≠ x.val := by
            intro he1
            exact internal_no_self hI (he1.trans ht.symm)
          have htar : e.1 = f.2 := by simpa [indexNeighbour, hne, hs'] using hEq
          have hrev : f = (e.2, e.1) := by
            apply Prod.ext
            · exact hs'.trans ht.symm
            · exact htar.symm
          rw [hrev] at hJ
          exact False.elim (internal_no_reverse hI hJ)
        · have hne : e.1 ≠ x.val := by
            intro he1
            exact internal_no_self hI (he1.trans ht.symm)
          have hne' : f.1 ≠ x.val := by
            intro hf1
            exact internal_no_self hJ (hf1.trans ht'.symm)
          have htar : e.1 = f.1 := by simpa [indexNeighbour, hne, hne'] using hEq
          have hsrc : e.2 = f.2 := ht.trans ht'.symm
          have hef : e = f := Prod.ext htar hsrc
          subst f
          rfl
    · rcases Finset.mem_image.mp hr with ⟨f, hf, rfl⟩
      have hI := (Finset.mem_filter.mp he).1
      have hL := (Finset.mem_filter.mp hf).1
      have htouch := (Finset.mem_filter.mp he).2
      have hta : indexNeighbour x (false, e) = f.2 := by
        rcases htouch with hs | ht
        · simpa [indexNeighbour, hs] using hEq
        · have hne : e.1 ≠ x.val := by
            intro he1
            exact internal_no_self hI (he1.trans ht.symm)
          simpa [indexNeighbour, hne] using hEq
      have hmem : indexNeighbour x (false, e) ∈ W := by
        rcases internal_endpoints_mem hI with ⟨h1, h2⟩
        rcases htouch with hs | ht
        · simpa [indexNeighbour, hs] using h2
        · have hne : e.1 ≠ x.val := by
            intro he1
            exact internal_no_self hI (he1.trans ht.symm)
          simpa [indexNeighbour, hne] using h1
      have hfW : f.2 ∈ W := by rw [← hta]; exact hmem
      exact False.elim (leg_target_not_mem hL hfW)
  · rcases Finset.mem_image.mp hq with ⟨e, he, rfl⟩
    rcases Finset.mem_union.mp hr with hr | hr
    · rcases Finset.mem_image.mp hr with ⟨f, hf, rfl⟩
      have hI := (Finset.mem_filter.mp hf).1
      have hL := (Finset.mem_filter.mp he).1
      have htouch := (Finset.mem_filter.mp hf).2
      have hta : e.2 = indexNeighbour x (false, f) := by
        rcases htouch with hs | ht
        · simpa [indexNeighbour, hs] using hEq
        · have hne : f.1 ≠ x.val := by
            intro hf1
            exact internal_no_self hI (hf1.trans ht.symm)
          simpa [indexNeighbour, hne] using hEq
      have hmem : indexNeighbour x (false, f) ∈ W := by
        rcases internal_endpoints_mem hI with ⟨h1, h2⟩
        rcases htouch with hs | ht
        · simpa [indexNeighbour, hs] using h2
        · have hne : f.1 ≠ x.val := by
            intro hf1
            exact internal_no_self hI (hf1.trans ht.symm)
          simpa [indexNeighbour, hne] using h1
      have heW : e.2 ∈ W := by rw [hta]; exact hmem
      exact False.elim (leg_target_not_mem hL heW)
    · rcases Finset.mem_image.mp hr with ⟨f, hf, rfl⟩
      have hL := (Finset.mem_filter.mp he).1
      have hL' := (Finset.mem_filter.mp hf).1
      have hs := (Finset.mem_filter.mp he).2
      have hs' := (Finset.mem_filter.mp hf).2
      have htar : e.2 = f.2 := by simpa [indexNeighbour, hs, hs'] using hEq
      have hsrc : e.1 = f.1 := hs.trans hs'.symm
      have hef : e = f := Prod.ext hsrc htar
      subst f
      rfl

lemma incident_card_le_four {W : Finset Plane} (x : W) :
    (internalAt W x).card + (legsAt W x).card ≤ 4 := by
  classical
  have hc : (localIndex W x).card ≤ (neighbours x.val).card :=
    Finset.card_le_card_of_injOn (indexNeighbour x)
      (by intro q hq; exact indexNeighbour_maps x hq)
      (indexNeighbour_injOn x)
  rw [localIndex_card] at hc
  exact hc.trans (neighbours_card_le_four x.val)

lemma planeWeight_split {W : Finset Plane} (κ : Plane → Fin 3)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) (x : W) :
    planeWeight κ W η σ =
      (1 / 12 : ℝ) ^ W.card *
        ((∏ e ∈ internalAt W x, internalFactor κ σ e) *
          (∏ e ∈ internalAway W x, internalFactor κ σ e)) *
        ((∏ e ∈ legsAt W x, legFactor κ η σ e) *
          (∏ e ∈ legsAway W x, legFactor κ η σ e)) := by
  classical
  unfold planeWeight internalAt internalAway legsAt legsAway internalFactor legFactor
  have hi := Finset.prod_filter_mul_prod_filter_not (internalBonds W)
    (fun e => e.1 = x.val ∨ e.2 = x.val)
    (fun e => 1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
      (frameVector (κ e.2) (extendLetters σ e.2)))
  have hl := Finset.prod_filter_mul_prod_filter_not (originalLegs W)
    (fun e => e.1 = x.val)
    (fun e => 1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
      (frameVector (κ e.2) (extendBoundary η e.2)))
  rw [hi.symm, hl.symm]
  simp only [not_or]

lemma internalAway_update {W : Finset Plane} (κ : Plane → Fin 3)
    (σ : PlaneConfiguration W) (x : W) (a : IcoLetter) :
    (∏ e ∈ internalAway W x, internalFactor κ (Function.update σ x a) e) =
      ∏ e ∈ internalAway W x, internalFactor κ σ e := by
  classical
  apply Finset.prod_congr rfl
  intro e he
  have hh := (Finset.mem_filter.mp he).2
  simp [internalFactor, extendLetters_update_ne x σ a hh.1,
    extendLetters_update_ne x σ a hh.2]

lemma legsAway_update {W : Finset Plane} (κ : Plane → Fin 3)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) (x : W) (a : IcoLetter) :
    (∏ e ∈ legsAway W x, legFactor κ η (Function.update σ x a) e) =
      ∏ e ∈ legsAway W x, legFactor κ η σ e := by
  classical
  apply Finset.prod_congr rfl
  intro e he
  have hh := (Finset.mem_filter.mp he).2
  simp [legFactor, extendLetters_update_ne x σ a hh]

lemma planeWeight_local {W : Finset Plane} (κ : Plane → Fin 3)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) (x : W) (a : IcoLetter) :
    planeWeight κ W η (Function.update σ x a) =
      fixedWeight κ η σ x * localWeight κ η (Function.update σ x a) x := by
  rw [planeWeight_split, internalAway_update, legsAway_update]
  unfold fixedWeight localWeight
  ring

lemma frameBound_pos_lt_one : 0 < frameBound ∧ frameBound < 1 := by
  have hs0 : 0 ≤ Real.sqrt (5 : ℝ) := Real.sqrt_nonneg _
  have hs : (Real.sqrt (5 : ℝ)) ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  unfold frameBound
  constructor <;> nlinarith

lemma plus_bounds {κ : Plane → Fin 3} (hb : interactionBounds)
    (hp : ProperPlaneColouring κ) {u v : Plane} (hadj : Adjacent u v)
    (a b : IcoLetter) :
    frameBound ≤ 1 + dot (frameVector (κ u) a) (frameVector (κ v) b) ∧
    1 + dot (frameVector (κ u) a) (frameVector (κ v) b) ≤ 2 - frameBound := by
  have hc : κ u ≠ κ v := hp u v hadj
  exact ⟨(hb (κ u) (κ v) hc a b).1,
    (hb (κ u) (κ v) hc a b).2.1⟩

lemma planeWeight_pos {W : Finset Plane} (κ : Plane → Fin 3)
    (hp : ProperPlaneColouring κ) (hb : interactionBounds)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) : 0 < planeWeight κ W η σ := by
  classical
  have hbpos := frameBound_pos_lt_one.1
  unfold planeWeight
  have hI : 0 < ∏ e ∈ internalBonds W,
      (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
        (frameVector (κ e.2) (extendLetters σ e.2))) := by
    apply Finset.prod_pos
    intro e he
    exact lt_of_lt_of_le hbpos (plus_bounds hb hp (internal_adj he)
      (extendLetters σ e.1) (extendLetters σ e.2)).1
  have hL : 0 < ∏ e ∈ originalLegs W,
      (1 + dot (frameVector (κ e.1) (extendLetters σ e.1))
        (frameVector (κ e.2) (extendBoundary η e.2))) := by
    apply Finset.prod_pos
    intro e he
    exact lt_of_lt_of_le hbpos (plus_bounds hb hp (leg_adj he)
      (extendLetters σ e.1) (extendBoundary η e.2)).1
  exact mul_pos (mul_pos (pow_pos (by norm_num) _) hI) hL

lemma internal_local_bounds {W : Finset Plane} (κ : Plane → Fin 3)
    (hp : ProperPlaneColouring κ) (hb : interactionBounds)
    (σ : PlaneConfiguration W) (x : W) {e : Plane × Plane}
    (he : e ∈ internalAt W x) :
    frameBound ≤ internalFactor κ σ e ∧ internalFactor κ σ e ≤ 2 - frameBound := by
  have hmem := (Finset.mem_filter.mp he).1
  have h := plus_bounds hb hp (internal_adj hmem)
    (extendLetters σ e.1) (extendLetters σ e.2)
  simpa [internalFactor] using h

lemma leg_local_bounds {W : Finset Plane} (κ : Plane → Fin 3)
    (hp : ProperPlaneColouring κ) (hb : interactionBounds)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) (x : W)
    {e : Plane × Plane} (he : e ∈ legsAt W x) :
    frameBound ≤ legFactor κ η σ e ∧ legFactor κ η σ e ≤ 2 - frameBound := by
  have hmem := (Finset.mem_filter.mp he).1
  have h := plus_bounds hb hp (leg_adj hmem)
    (extendLetters σ e.1) (extendBoundary η e.2)
  simpa [legFactor] using h

lemma prod_lower_pow {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) (b : ℝ) (hb : 0 ≤ b)
    (h : ∀ i ∈ s, b ≤ f i) : b ^ s.card ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.card_insert_of_notMem ha, pow_succ]
    have hfa := h a (Finset.mem_insert_self a s)
    have htail : b ^ s.card ≤ ∏ i ∈ s, f i := ih (by
      intro i hi
      exact h i (Finset.mem_insert_of_mem hi))
    have htail0 : 0 ≤ ∏ i ∈ s, f i :=
      Finset.prod_nonneg (by
        intro i hi
        exact le_trans hb (h i (Finset.mem_insert_of_mem hi)))
    calc
      b ^ s.card * b = b * b ^ s.card := by ring
      _ ≤ f a * ∏ i ∈ s, f i :=
        mul_le_mul hfa htail (pow_nonneg hb _) (le_trans hb hfa)
      _ = ∏ i ∈ insert a s, f i := by simp [ha]

lemma prod_upper_pow {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h0 : ∀ i ∈ s, 0 ≤ f i)
    (h : ∀ i ∈ s, f i ≤ c) : ∏ i ∈ s, f i ≤ c ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.card_insert_of_notMem ha]
    have hfa := h a (Finset.mem_insert_self a s)
    have hfa0 := h0 a (Finset.mem_insert_self a s)
    have htail : ∏ i ∈ s, f i ≤ c ^ s.card := ih
      (by intro i hi; exact h0 i (Finset.mem_insert_of_mem hi))
      (by intro i hi; exact h i (Finset.mem_insert_of_mem hi))
    have htail0 : 0 ≤ ∏ i ∈ s, f i := Finset.prod_nonneg (by
      intro i hi
      exact h0 i (Finset.mem_insert_of_mem hi))
    calc
      ∏ i ∈ insert a s, f i = f a * ∏ i ∈ s, f i := by simp [ha]
      _ ≤ c * c ^ s.card := mul_le_mul hfa htail htail0 hc
      _ = c ^ (s.card + 1) := by rw [pow_succ]; ring

lemma localWeight_estimate {W : Finset Plane} (κ : Plane → Fin 3)
    (hp : ProperPlaneColouring κ) (hb : interactionBounds)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) (x : W) :
    0 < localWeight κ η σ x ∧
      frameBound ^ ((internalAt W x).card + (legsAt W x).card) ≤ localWeight κ η σ x ∧
      localWeight κ η σ x ≤ (2 - frameBound) ^ ((internalAt W x).card + (legsAt W x).card) := by
  classical
  let I := internalAt W x
  let L := legsAt W x
  let n := I.card
  let m := L.card
  have hbpos := frameBound_pos_lt_one.1
  have hcpos : 0 < 2 - frameBound := by linarith [frameBound_pos_lt_one.2]
  have hIpos : 0 < ∏ e ∈ I, internalFactor κ σ e := by
    apply Finset.prod_pos
    intro e he
    exact lt_of_lt_of_le hbpos (internal_local_bounds κ hp hb σ x he).1
  have hLpos : 0 < ∏ e ∈ L, legFactor κ η σ e := by
    apply Finset.prod_pos
    intro e he
    exact lt_of_lt_of_le hbpos (leg_local_bounds κ hp hb η σ x he).1
  have hIlow : frameBound ^ n ≤ ∏ e ∈ I, internalFactor κ σ e :=
    prod_lower_pow I (fun e => internalFactor κ σ e) frameBound (le_of_lt hbpos)
      (by intro e he; exact (internal_local_bounds κ hp hb σ x he).1)
  have hLlow : frameBound ^ m ≤ ∏ e ∈ L, legFactor κ η σ e :=
    prod_lower_pow L (fun e => legFactor κ η σ e) frameBound (le_of_lt hbpos)
      (by intro e he; exact (leg_local_bounds κ hp hb η σ x he).1)
  have hIup : (∏ e ∈ I, internalFactor κ σ e) ≤ (2 - frameBound) ^ n :=
    prod_upper_pow I (fun e => internalFactor κ σ e) (2 - frameBound) (le_of_lt hcpos)
      (by intro e he; exact le_of_lt (lt_of_lt_of_le hbpos (internal_local_bounds κ hp hb σ x he).1))
      (by intro e he; exact (internal_local_bounds κ hp hb σ x he).2)
  have hLup : (∏ e ∈ L, legFactor κ η σ e) ≤ (2 - frameBound) ^ m :=
    prod_upper_pow L (fun e => legFactor κ η σ e) (2 - frameBound) (le_of_lt hcpos)
      (by intro e he; exact le_of_lt (lt_of_lt_of_le hbpos (leg_local_bounds κ hp hb η σ x he).1))
      (by intro e he; exact (leg_local_bounds κ hp hb η σ x he).2)
  have hlow : frameBound ^ (n + m) ≤
      (∏ e ∈ I, internalFactor κ σ e) * (∏ e ∈ L, legFactor κ η σ e) := by
    rw [pow_add]
    exact mul_le_mul hIlow hLlow (pow_nonneg (le_of_lt hbpos) m) (le_of_lt hIpos)
  have hup : (∏ e ∈ I, internalFactor κ σ e) * (∏ e ∈ L, legFactor κ η σ e) ≤
      (2 - frameBound) ^ (n + m) := by
    rw [pow_add]
    exact mul_le_mul hIup hLup (le_of_lt hLpos) (pow_nonneg (le_of_lt hcpos) n)
  have hpos : 0 <
      (∏ e ∈ I, internalFactor κ σ e) * (∏ e ∈ L, legFactor κ η σ e) := mul_pos hIpos hLpos
  have hcard : n + m ≤ 4 := by
    dsimp [n, m, I, L]
    exact incident_card_le_four x
  simpa [localWeight, I, L, n, m] using And.intro hpos (And.intro hlow hup)

lemma pow_ratio_degree {k : ℕ} (hk : k ≤ 4) : frameRatio ^ 4 ≤ frameRatio ^ k := by
  have hb := frameBound_pos_lt_one
  have hr0 : 0 ≤ frameRatio := le_of_lt (div_pos hb.1 (by linarith [hb.2]))
  have hr1 : frameRatio ≤ 1 := by
    unfold frameRatio
    apply (div_le_iff₀ (by linarith [hb.2])).2
    linarith [hb.2]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le hk
  rw [hm, pow_add]
  calc
    frameRatio ^ k * frameRatio ^ m ≤ frameRatio ^ k * 1 :=
      mul_le_mul_of_nonneg_left (pow_le_one₀ hr0 hr1) (pow_nonneg hr0 _)
    _ = frameRatio ^ k := by ring

lemma localWeight_ratio_bound {W : Finset Plane} (κ : Plane → Fin 3)
    (hp : ProperPlaneColouring κ) (hb : interactionBounds)
    (η : FrameBoundary W) (σ : PlaneConfiguration W) (x : W) (a : IcoLetter) :
    frameEnergy ≤
      localWeight κ η (Function.update σ x a) x /
        ∑ b : IcoLetter, localWeight κ η (Function.update σ x b) x := by
  classical
  let k := (internalAt W x).card + (legsAt W x).card
  have hk : k ≤ 4 := by dsimp [k]; exact incident_card_le_four x
  have hbpos := frameBound_pos_lt_one.1
  have hcpos : 0 < 2 - frameBound := by linarith [frameBound_pos_lt_one.2]
  have ha := localWeight_estimate κ hp hb η (Function.update σ x a) x
  have hnum : frameBound ^ k ≤ localWeight κ η (Function.update σ x a) x := by
    simpa [k] using ha.2.1
  have hdenpos : 0 < ∑ b : IcoLetter, localWeight κ η (Function.update σ x b) x := by
    apply Finset.sum_pos
    · intro b _
      exact (localWeight_estimate κ hp hb η (Function.update σ x b) x).1
    · exact ⟨default, Finset.mem_univ _⟩
  have hdenup :
      (∑ b : IcoLetter, localWeight κ η (Function.update σ x b) x) ≤
        12 * (2 - frameBound) ^ k := by
    calc
      (∑ b : IcoLetter, localWeight κ η (Function.update σ x b) x) ≤
          ∑ _b : IcoLetter, (2 - frameBound) ^ k :=
        Finset.sum_le_sum (by
          intro b _
          simpa [k] using (localWeight_estimate κ hp hb η (Function.update σ x b) x).2.2)
      _ = 12 * (2 - frameBound) ^ k := by norm_num [IcoLetter]
  have hdiv :
      frameBound ^ k / (12 * (2 - frameBound) ^ k) ≤
        localWeight κ η (Function.update σ x a) x /
          ∑ b : IcoLetter, localWeight κ η (Function.update σ x b) x := by
    apply div_le_div₀ (le_trans (pow_nonneg (le_of_lt hbpos) _) hnum) hnum hdenpos hdenup
  have hcne : 2 - frameBound ≠ 0 := ne_of_gt hcpos
  have hid : frameBound ^ k / (12 * (2 - frameBound) ^ k) =
      (1 / 12 : ℝ) * frameRatio ^ k := by
    unfold frameRatio
    field_simp [hcne]
    have hpow : (2 - frameBound)⁻¹ ^ k * (2 - frameBound) ^ k = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hcne, one_pow]
    calc
      frameBound ^ k = frameBound ^ k * 1 := by ring
      _ = frameBound ^ k * ((2 - frameBound)⁻¹ ^ k * (2 - frameBound) ^ k) := by rw [hpow]
      _ = frameBound ^ k * (2 - frameBound)⁻¹ ^ k * (2 - frameBound) ^ k := by ring
    ring
  calc
    frameEnergy = (1 / 12 : ℝ) * frameRatio ^ 4 := rfl
    _ ≤ (1 / 12 : ℝ) * frameRatio ^ k := by
      exact mul_le_mul_of_nonneg_left (pow_ratio_degree hk) (by norm_num)
    _ = frameBound ^ k / (12 * (2 - frameBound) ^ k) := hid.symm
    _ ≤ _ := hdiv

lemma planePartition_pos {W : Finset Plane} (κ : Plane → Fin 3)
    (hp : ProperPlaneColouring κ) (hb : interactionBounds) (η : FrameBoundary W) :
    0 < ∑ σ : PlaneConfiguration W, planeWeight κ W η σ := by
  classical
  apply Finset.sum_pos
  · intro σ _
    exact planeWeight_pos κ hp hb η σ
  · exact ⟨(fun _ : W => default), Finset.mem_univ _⟩

lemma conditionalProbability_local {W : Finset Plane} (κ : Plane → Fin 3)
    (hp : ProperPlaneColouring κ) (hb : interactionBounds) (η : FrameBoundary W)
    (x : W) (σ : PlaneConfiguration W) (a : IcoLetter) :
    conditionalProbability (planeLaw κ W η) (fullFibreEvent x σ) (fun τ => τ x = a) =
      localWeight κ η (Function.update σ x a) x /
        ∑ b : IcoLetter, localWeight κ η (Function.update σ x b) x := by
  classical
  let Z := ∑ τ : PlaneConfiguration W, planeWeight κ W η τ
  have hZ : 0 < Z := by dsimp [Z]; exact planePartition_pos κ hp hb η
  letI : DecidablePred (fun τ : PlaneConfiguration W => τ x = a) :=
    fun τ => Classical.propDecidable _
  have hN :
      (∑ τ, if fullFibreEvent x σ τ ∧ τ x = a then planeLaw κ W η τ else 0) =
        planeLaw κ W η (Function.update σ x a) := by
    have hs := sum_fullFibre x σ
      (fun τ => if τ x = a then planeLaw κ W η τ else 0)
    simpa [← ite_and, Function.update_self] using hs
  have hD :
      (∑ τ, if fullFibreEvent x σ τ then planeLaw κ W η τ else 0) =
        ∑ b : IcoLetter, planeLaw κ W η (Function.update σ x b) := by
    simpa using sum_fullFibre x σ (planeLaw κ W η)
  have hfixed :
      0 < fixedWeight κ η σ x := by
    have hloc := (localWeight_estimate κ hp hb η (Function.update σ x a) x).1
    have hw := planeWeight_pos κ hp hb η (Function.update σ x a)
    have hprod : 0 < fixedWeight κ η σ x *
        localWeight κ η (Function.update σ x a) x := by
      simpa [planeWeight_local] using hw
    exact (mul_pos_iff_of_pos_right hloc).mp hprod
  have hnum :
      (planeWeight κ W η (Function.update σ x a) / Z) =
        (fixedWeight κ η σ x / Z) * localWeight κ η (Function.update σ x a) x := by
    rw [planeWeight_local]
    dsimp [Z]
    ring
  have hsum :
      (∑ b : IcoLetter,
        planeWeight κ W η (Function.update σ x b) / Z) =
        (fixedWeight κ η σ x / Z) *
          ∑ b : IcoLetter, localWeight κ η (Function.update σ x b) x := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [planeWeight_local]
    dsimp [Z]
    ring
  have hlocden : 0 < ∑ b : IcoLetter, localWeight κ η (Function.update σ x b) x := by
    apply Finset.sum_pos
    · intro b _
      exact (localWeight_estimate κ hp hb η (Function.update σ x b) x).1
    · exact ⟨default, Finset.mem_univ _⟩
  have hcancel : fixedWeight κ η σ x / Z ≠ 0 :=
    div_ne_zero (ne_of_gt hfixed) (ne_of_gt hZ)
  have hratio := congrArg₂ (fun n d : ℝ => n / d) hN hD
  calc
    conditionalProbability (planeLaw κ W η) (fullFibreEvent x σ) (fun τ => τ x = a) =
        planeLaw κ W η (Function.update σ x a) /
          ∑ b : IcoLetter, planeLaw κ W η (Function.update σ x b) := by
      unfold conditionalProbability
      dsimp only
      exact hratio
    _ = localWeight κ η (Function.update σ x a) x /
          ∑ b : IcoLetter, localWeight κ η (Function.update σ x b) x := by
      simp only [planeLaw, AKLT.Defs.normalize]
      change (planeWeight κ W η (Function.update σ x a) / Z) /
          (∑ b : IcoLetter, planeWeight κ W η (Function.update σ x b) / Z) = _
      rw [hnum, hsum]
      field_simp [hcancel, ne_of_gt hlocden]

theorem main : AKLT.Blueprint.Q.PlaneOneSiteEnergyStatement := by
  intro hb κ hp W η x σ a
  rw [conditionalProbability_local κ hp hb η x σ a]
  exact localWeight_ratio_bound κ hp hb η σ x a

end AKLT.W.Q052

#print axioms AKLT.W.Q052.main
