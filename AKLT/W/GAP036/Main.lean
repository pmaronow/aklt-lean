module
public import AKLT.Blueprint.Gap.NodesPeriodic

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section

open scoped BigOperators
open AKLT.Defs AKLT.Challenge AKLT.Blueprint.Gap

namespace AKLT.W.GAP036

local instance (α : Type) : DecidableEq α := Classical.decEq α

private lemma square_mem_iff (c z : Plane) (M : ℕ) :
    z ∈ square c M ↔
      c.1 - (M : ℤ) ≤ z.1 ∧ z.1 ≤ c.1 + M ∧
      c.2 - (M : ℤ) ≤ z.2 ∧ z.2 ≤ c.2 + M := by
  simp [square, Finset.mem_product, Finset.mem_Icc, and_assoc]

private lemma square_translate (c : Plane) (M : ℕ) :
    square c M = (square (0, 0) M).image (fun z => c + z) := by
  ext z
  simp only [square_mem_iff, Finset.mem_image]
  constructor
  · rintro ⟨hx₁, hx₂, hy₁, hy₂⟩
    refine ⟨(z.1 - c.1, z.2 - c.2), ?_, ?_⟩
    · omega
    · ext <;> simp <;> omega
  · rintro ⟨w, hw, rfl⟩
    rcases hw with ⟨hx₁, hx₂, hy₁, hy₂⟩
    exact ⟨by simpa using (show c.1 - (M : ℤ) ≤ c.1 + w.1 by omega),
      by simpa using (show c.1 + w.1 ≤ c.1 + M by omega),
      by simpa using (show c.2 - (M : ℤ) ≤ c.2 + w.2 by omega),
      by simpa using (show c.2 + w.2 ≤ c.2 + M by omega)⟩

private lemma reduction_add (L N : Size) (x y : Plane) :
    reduction L N (x + y) = reduction L N x + reduction L N y := by
  simp [reduction]

private lemma lifted_square_image (L N : Size) (a : Site L N) (c : Plane)
    (hc : reduction L N c = a) (M : ℕ) :
    (square c M).image (reduction L N) = torusSquare L N M a := by
  calc
    (square c M).image (reduction L N)
        = ((square (0, 0) M).image (fun z => c + z)).image (reduction L N) := by
            rw [square_translate]
    _ = (square (0, 0) M).image (fun z => reduction L N (c + z)) := Finset.image_image
    _ = (square (0, 0) M).image (fun z => a + reduction L N z) := by
          congr 1
          funext z
          simp [reduction_add, hc]
    _ = torusSquare L N M a := rfl

private noncomputable def antipodalLetter
    (hanti : ∀ j : Fin 3, Function.Injective (frameVector j) ∧
      ∀ a, ∃ b, frameVector j b = -frameVector j a)
    (j : Fin 3) (a : IcoLetter) : IcoLetter := Classical.choose ((hanti j).2 a)

private lemma antipodalLetter_spec
    (hanti : ∀ j : Fin 3, Function.Injective (frameVector j) ∧
      ∀ a, ∃ b, frameVector j b = -frameVector j a)
    (j : Fin 3) (a : IcoLetter) :
    frameVector j (antipodalLetter hanti j a) = -frameVector j a :=
  Classical.choose_spec ((hanti j).2 a)

private lemma antipodalLetter_involutive
    (hanti : ∀ j : Fin 3, Function.Injective (frameVector j) ∧
      ∀ a, ∃ b, frameVector j b = -frameVector j a)
    (j : Fin 3) : Function.Involutive (antipodalLetter hanti j) := by
  intro a
  apply (hanti j).1
  calc
    frameVector j (antipodalLetter hanti j (antipodalLetter hanti j a)) =
        -frameVector j (antipodalLetter hanti j a) := antipodalLetter_spec hanti j _
    _ = -(-frameVector j a) := by rw [antipodalLetter_spec]
    _ = frameVector j a := by simp

private def parityLetter
    (hanti : ∀ j : Fin 3, Function.Injective (frameVector j) ∧
      ∀ a, ∃ b, frameVector j b = -frameVector j a)
    (j : Fin 3) (z : Plane) (a : IcoLetter) : IcoLetter :=
  if Even (z.1 + z.2) then a else antipodalLetter hanti j a

private lemma parityLetter_involutive
    (hanti : ∀ j : Fin 3, Function.Injective (frameVector j) ∧
      ∀ a, ∃ b, frameVector j b = -frameVector j a)
    (j : Fin 3) (z : Plane) : Function.Involutive (parityLetter hanti j z) := by
  intro a
  by_cases he : Even (z.1 + z.2)
  · simp [parityLetter, he]
  · simpa [parityLetter, he] using antipodalLetter_involutive hanti j a

private lemma parityLetter_vector
    (hanti : ∀ j : Fin 3, Function.Injective (frameVector j) ∧
      ∀ a, ∃ b, frameVector j b = -frameVector j a)
    (j : Fin 3) (z : Plane) (a : IcoLetter) :
    frameVector j (parityLetter hanti j z a) = paritySign z • frameVector j a := by
  by_cases he : Even (z.1 + z.2)
  · simp [parityLetter, paritySign, he]
  · simp [parityLetter, paritySign, he, antipodalLetter_spec]

private lemma supDist_eq_zero_iff (x y : Plane) :
    supDist x y = 0 ↔ x = y := by
  simp [supDist, Int.natAbs_eq_zero, Prod.ext_iff, sub_eq_zero]

private lemma adjacent_coordinate_bounds {x y : Plane} (h : Adjacent x y) :
    -1 ≤ y.1 - x.1 ∧ y.1 - x.1 ≤ 1 ∧
    -1 ≤ y.2 - x.2 ∧ y.2 - x.2 ≤ 1 := by
  have hsum : (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = 1 := h
  have hx : (x.1 - y.1).natAbs ≤ 1 := by omega
  have hy : (x.2 - y.2).natAbs ≤ 1 := by omega
  have hx' := Int.natAbs_eq (x.1 - y.1)
  have hy' := Int.natAbs_eq (x.2 - y.2)
  rcases hx' with hx' | hx' <;> rcases hy' with hy' | hy' <;> omega

private def clampCoord (c : ℤ) (M : ℕ) (t : ℤ) : ℤ :=
  if t < c - (M : ℤ) then c - (M : ℤ)
  else if c + M < t then c + M
  else t

private def clampPoint (c z : Plane) (M : ℕ) : Plane :=
  (clampCoord c.1 M z.1, clampCoord c.2 M z.2)

private lemma clampCoord_bounds (c : ℤ) (M : ℕ) (t : ℤ)
    (ht₁ : c - (M : ℤ) - 1 ≤ t) (ht₂ : t ≤ c + M + 1) :
    c - (M : ℤ) ≤ clampCoord c M t ∧ clampCoord c M t ≤ c + M ∧
    -1 ≤ t - clampCoord c M t ∧ t - clampCoord c M t ≤ 1 := by
  unfold clampCoord
  split_ifs with hlo hhi
  · constructor <;> [omega; constructor <;> omega]
  · constructor <;> [omega; constructor <;> omega]
  · constructor <;> [omega; constructor <;> omega]

private lemma clampCoord_eq_boundary_of_lt (c : ℤ) (M : ℕ) (t : ℤ)
    (h : t < c - (M : ℤ)) :
    clampCoord c M t = c - (M : ℤ) := by
  simp [clampCoord, h]

private lemma clampCoord_eq_boundary_of_gt (c : ℤ) (M : ℕ) (t : ℤ)
    (h : c + M < t) : clampCoord c M t = c + M := by
  unfold clampCoord
  by_cases hlo : t < c - (M : ℤ)
  · omega
  · simp [hlo, h]

private lemma ring_has_nearest (c z : Plane) (M : ℕ)
    (hz : z ∈ square c (M + 1)) (hout : z ∉ square c M) :
    ∃ x, x ∈ square c M ∧ supDist z x = 1 := by
  let x := clampPoint c z M
  have hz' := (square_mem_iff c z (M + 1)).mp hz
  have hb₁ := clampCoord_bounds c.1 M z.1 (by omega) (by omega)
  have hb₂ := clampCoord_bounds c.2 M z.2 (by omega) (by omega)
  have hxmem : x ∈ square c M := by
    dsimp [x, clampPoint]
    rw [square_mem_iff]
    exact ⟨hb₁.1, hb₁.2.1, hb₂.1, hb₂.2.1⟩
  rw [square_mem_iff c z M] at hout
  simp only [not_and_or] at hout
  have houter := hout
  rcases houter with hleft | hright | hbottom | htop
  · have hleft' : z.1 < c.1 - (M : ℤ) := by omega
    have hclamp₁ := clampCoord_eq_boundary_of_lt c.1 M z.1 hleft'
    have heq₁ : (z.1 - x.1).natAbs = 1 := by
      dsimp [x, clampPoint]
      rw [hclamp₁]
      have : z.1 = c.1 - (M : ℤ) - 1 := by omega
      rw [this]
      simp
    have hle₂ : (z.2 - x.2).natAbs ≤ 1 := by
      have h : -1 ≤ z.2 - x.2 ∧ z.2 - x.2 ≤ 1 := by simpa [x, clampPoint] using hb₂.2.2
      have hc := Int.natAbs_eq (z.2 - x.2)
      rcases hc with hc | hc <;> omega
    refine ⟨x, hxmem, ?_⟩
    simp [supDist, heq₁, Nat.max_eq_left (by omega)]
  · have hright' : c.1 + M < z.1 := by omega
    have hclamp₁ := clampCoord_eq_boundary_of_gt c.1 M z.1 hright'
    have heq₁ : (z.1 - x.1).natAbs = 1 := by
      dsimp [x, clampPoint]
      rw [hclamp₁]
      have : z.1 = c.1 + M + 1 := by omega
      rw [this]
      simp
    have hle₂ : (z.2 - x.2).natAbs ≤ 1 := by
      have h : -1 ≤ z.2 - x.2 ∧ z.2 - x.2 ≤ 1 := by simpa [x, clampPoint] using hb₂.2.2
      have hc := Int.natAbs_eq (z.2 - x.2)
      rcases hc with hc | hc <;> omega
    refine ⟨x, hxmem, ?_⟩
    simp [supDist, heq₁, Nat.max_eq_left (by omega)]
  · have hbottom' : z.2 < c.2 - (M : ℤ) := by omega
    have hclamp₂ := clampCoord_eq_boundary_of_lt c.2 M z.2 hbottom'
    have heq₂ : (z.2 - x.2).natAbs = 1 := by
      dsimp [x, clampPoint]
      rw [hclamp₂]
      have : z.2 = c.2 - (M : ℤ) - 1 := by omega
      rw [this]
      simp
    have hle₁ : (z.1 - x.1).natAbs ≤ 1 := by
      have h : -1 ≤ z.1 - x.1 ∧ z.1 - x.1 ≤ 1 := by simpa [x, clampPoint] using hb₁.2.2
      have hc := Int.natAbs_eq (z.1 - x.1)
      rcases hc with hc | hc <;> omega
    refine ⟨x, hxmem, ?_⟩
    simp [supDist, heq₂, Nat.max_eq_right (by omega)]
  · have htop' : c.2 + M < z.2 := by omega
    have hclamp₂ := clampCoord_eq_boundary_of_gt c.2 M z.2 htop'
    have heq₂ : (z.2 - x.2).natAbs = 1 := by
      dsimp [x, clampPoint]
      rw [hclamp₂]
      have : z.2 = c.2 + M + 1 := by omega
      rw [this]
      simp
    have hle₁ : (z.1 - x.1).natAbs ≤ 1 := by
      have h : -1 ≤ z.1 - x.1 ∧ z.1 - x.1 ≤ 1 := by simpa [x, clampPoint] using hb₁.2.2
      have hc := Int.natAbs_eq (z.1 - x.1)
      rcases hc with hc | hc <;> omega
    refine ⟨x, hxmem, ?_⟩
    simp [supDist, heq₂, Nat.max_eq_right (by omega)]

private lemma setDistance_ring_eq_one (c z : Plane) (M : ℕ)
    (hz : z ∈ square c (M + 1)) (hout : z ∉ square c M) :
    setDistance supDist z (↑(square c M) : Set Plane) = 1 := by
  have hnear := ring_has_nearest c z M hz hout
  rcases hnear with ⟨x, hx, hdist⟩
  unfold setDistance
  apply le_antisymm
  · calc
      (⨅ y : {y : Plane // y ∈ (↑(square c M) : Set Plane)},
          (supDist z y.val : ℕ∞)) ≤ (supDist z x : ℕ∞) :=
            iInf_le _ (⟨x, by simpa using hx⟩ :
              {y : Plane // y ∈ (↑(square c M) : Set Plane)})
      _ = 1 := by exact_mod_cast hdist
  · apply le_iInf
    intro y
    have hymem : y.val ∈ square c M := by simpa using y.property
    have hnotzero : supDist z y.val ≠ 0 := by
      intro hzero
      have heq := (supDist_eq_zero_iff z y.val).mp hzero
      exact hout (heq ▸ hymem)
    have hpos : 1 ≤ supDist z y.val := Nat.one_le_iff_ne_zero.mpr hnotzero
    exact_mod_cast hpos

private lemma adjacent_of_neighbors {x z : Plane} (hz : z ∈ neighbors x) :
    Adjacent x z := by
  rcases Finset.mem_image.mp hz with ⟨d, -, rfl⟩
  cases d <;> norm_num [neighbors, Compass.step, Adjacent, latticeDist]

private lemma exteriorSites_ring (c : Plane) (M : ℕ) (z : Plane)
    (hz : z ∈ exteriorSites (square c M)) :
    z ∈ square c (M + 1) \ square c M := by
  unfold exteriorSites at hz
  rcases Finset.mem_image.mp hz with ⟨e, he, rfl⟩
  unfold originalLegs at he
  rcases Finset.mem_biUnion.mp he with ⟨u, hu, he⟩
  rcases Finset.mem_image.mp he with ⟨v, hv, rfl⟩
  have hv' : v ∈ neighbors u \ square c M := by simpa using hv
  rcases Finset.mem_sdiff.mp hv' with ⟨hv, hvout⟩
  have hadj : Adjacent u v := adjacent_of_neighbors hv
  have hcoords := adjacent_coordinate_bounds hadj
  have humem := (square_mem_iff c u M).mp hu
  have hvbig : v ∈ square c (M + 1) := by
    rw [square_mem_iff]
    rcases humem with ⟨hu₁, hu₂, hu₃, hu₄⟩
    exact ⟨by omega, by omega, by omega, by omega⟩
  exact Finset.mem_sdiff.mpr ⟨hvbig, hvout⟩

private lemma square_subset_succ (c : Plane) (M : ℕ) (z : Plane)
    (hz : z ∈ square c M) : z ∈ square c (M + 1) := by
  rw [square_mem_iff] at hz ⊢
  rcases hz with ⟨h₁, h₂, h₃, h₄⟩
  exact ⟨by omega, by omega, by omega, by omega⟩

private lemma liftSite_exists (L N : Size) (a : Site L N) (c : Plane) (M : ℕ)
    (himage : (square c M).image (reduction L N) = torusSquare L N M a)
    (x : torusSquare L N M a) : ∃ z : square c M, reduction L N z.val = x.val := by
  have hx : x.val ∈ (square c M).image (reduction L N) := by
    simpa only [himage] using x.property
  rcases Finset.mem_image.mp hx with ⟨z, hz, hred⟩
  exact ⟨⟨z, hz⟩, hred⟩

private noncomputable def liftSite (L N : Size) (a : Site L N) (c : Plane) (M : ℕ)
    (himage : (square c M).image (reduction L N) = torusSquare L N M a)
    (x : torusSquare L N M a) : square c M :=
  Classical.choose (liftSite_exists L N a c M himage x)

private lemma liftSite_reduces (L N : Size) (a : Site L N) (c : Plane) (M : ℕ)
    (himage : (square c M).image (reduction L N) = torusSquare L N M a)
    (x : torusSquare L N M a) :
    reduction L N (liftSite L N a c M himage x).val = x.val :=
  Classical.choose_spec (liftSite_exists L N a c M himage x)

private noncomputable def liftEquiv (L N : Size) (a : Site L N) (c : Plane) (M : ℕ)
    (himage : (square c M).image (reduction L N) = torusSquare L N M a)
    (hinj : Set.InjOn (reduction L N) (↑(square c (M + 1)) : Set Plane)) :
    (torusSquare L N M a) ≃ (square c M) := by
  apply Equiv.ofBijective (liftSite L N a c M himage)
  constructor
  · intro x y hxy
    apply Subtype.ext
    have hred := congrArg (fun z : square c M => reduction L N z.val) hxy
    rw [liftSite_reduces, liftSite_reduces] at hred
    exact hred
  · intro z
    refine ⟨⟨reduction L N z.val, ?_⟩, ?_⟩
    · rw [← himage]
      exact Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩
    · apply Subtype.ext
      apply hinj
      · exact square_subset_succ c M _ (liftSite L N a c M himage ⟨reduction L N z.val, by
          rw [← himage]
          exact Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩⟩).property
      · exact square_subset_succ c M z.val z.property
      · exact liftSite_reduces L N a c M himage ⟨reduction L N z.val, by
          rw [← himage]
          exact Finset.mem_image.mpr ⟨z.val, z.property, rfl⟩⟩

theorem main : AKLT.Blueprint.Gap.BoxCoordinatesStatement := by
  intro hanti L N M _hM _hL _hN hInject κ a
  let c : Plane := (a.1.val, a.2.val)
  have hc : reduction L N c = a := by
    ext <;> simp [c, reduction, ZMod.natCast_zmod_val]
  have hinj := hInject c
  have himage := lifted_square_image L N a c hc M
  let e := liftEquiv L N a c M himage hinj
  let flip (x : torusSquare L N M a) : IcoLetter → IcoLetter :=
    parityLetter hanti (κ x.val) (e x).val
  let confEquiv :
      ((x : torusSquare L N M a) → IcoLetter) ≃
        ((z : square c M) → IcoLetter) :=
    { toFun := fun ω z => flip (e.symm z) (ω (e.symm z))
      invFun := fun ν x => flip x (ν (e x))
      left_inv := by
        intro ω
        funext x
        change flip x (flip (e.symm (e x)) (ω (e.symm (e x)))) = ω x
        rw [e.symm_apply_apply]
        exact parityLetter_involutive hanti (κ x.val) (e x).val (ω x)
      right_inv := by
        intro ν
        funext z
        change flip (e.symm z) (flip (e.symm z) (ν (e (e.symm z)))) = ν z
        rw [e.apply_symm_apply]
        exact parityLetter_involutive hanti (κ (e.symm z).val) (e (e.symm z)).val (ν z) }
  let coordChange : ProductChange
      (fun _ : torusSquare L N M a => IcoLetter)
      (fun _ : square c M => IcoLetter) :=
    { sites := e
      configurations := confEquiv
      coordinate_eq := by
        intro σ τ x
        change σ x = τ x ↔
          flip (e.symm (e x)) (σ (e.symm (e x))) =
            flip (e.symm (e x)) (τ (e.symm (e x)))
        rw [e.symm_apply_apply]
        constructor
        · intro h
          rw [h]
        · intro h
          calc
            σ x = flip x (flip x (σ x)) :=
              (parityLetter_involutive hanti (κ x.val) (e x).val (σ x)).symm
            _ = flip x (flip x (τ x)) := congrArg (flip x) h
            _ = τ x := parityLetter_involutive hanti (κ x.val) (e x).val (τ x) }
  let bdy : TorusConfiguration L N → Config (fun _ : Plane => IcoLetter) :=
    fun σ w =>
      if hw : w ∈ square c (M + 1) \ square c M then
        parityLetter hanti (κ (reduction L N w)) w (σ (reduction L N w))
      else (0, 0, 0)
  refine ⟨c, hc, coordChange, ?_, ?_, bdy, ?_, ?_⟩
  · intro x
    exact liftSite_reduces L N a c M himage x
  · intro ω x
    change frameVector (κ x.val)
        (flip (e.symm (e x)) (ω (e.symm (e x)))) =
          paritySign (e x).val • frameVector (κ x.val) (ω x)
    rw [e.symm_apply_apply]
    exact parityLetter_vector hanti (κ x.val) (e x).val (ω x)
  · intro σ z hz
    have hzring := exteriorSites_ring c M z hz
    change frameVector (κ (reduction L N z)) (bdy σ z) = _
    simp only [bdy, dif_pos hzring]
    exact parityLetter_vector hanti (κ (reduction L N z)) z (σ (reduction L N z))
  · intro y hy σ τ hagree
    rcases Finset.mem_sdiff.mp hy with ⟨hyHalo, hyOutside⟩
    have hyOuter : y ∈ torusSquare L N (M + 1) a := by
      simpa [torusHalo] using hyHalo
    have himageOuter := lifted_square_image L N a c hc (M + 1)
    have hyImage : y ∈ (square c (M + 1)).image (reduction L N) := by
      rw [himageOuter]
      exact hyOuter
    rcases Finset.mem_image.mp hyImage with ⟨z, hz, hred⟩
    have hzOutside : z ∉ square c M := by
      intro hzInner
      apply hyOutside
      rw [← himage]
      exact Finset.mem_image.mpr ⟨z, hzInner, hred⟩
    have hzring : z ∈ square c (M + 1) \ square c M :=
      Finset.mem_sdiff.mpr ⟨hz, hzOutside⟩
    have hdist := setDistance_ring_eq_one c z M hz hzOutside
    refine ⟨z, hzOutside, hdist, ?_⟩
    intro w hne
    by_cases hwring : w ∈ square c (M + 1) \ square c M
    · have hredne : reduction L N w ≠ y := by
        intro hwy
        have hwouter : w ∈ (↑(square c (M + 1)) : Set Plane) := by
          exact (Finset.mem_sdiff.mp hwring).1
        have hzouter : z ∈ (↑(square c (M + 1)) : Set Plane) := by
          exact hz
        have hwz : reduction L N w = reduction L N z := by
          rw [hwy, hred]
        exact hne (hinj hwouter hzouter hwz)
      have hletters : σ (reduction L N w) = τ (reduction L N w) :=
        hagree (reduction L N w) (by simpa using hredne)
      change bdy σ w = bdy τ w
      simp only [bdy, dif_pos hwring, hletters]
    · change bdy σ w = bdy τ w
      have hcond : ¬ (w ∈ square c (M + 1) ∧ w ∉ square c M) := by
        simpa only [Finset.mem_sdiff] using hwring
      simp only [bdy, Finset.mem_sdiff, dif_neg hcond]

end AKLT.W.GAP036

