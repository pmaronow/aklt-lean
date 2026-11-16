import AKLT.W.REC043.Fibres
import AKLT.W.REC043.Bonds

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC043

private theorem dot_comm (a b : Vec3) : dot a b = dot b a := by simp [dot, mul_comm]

/-- Every original leg is rooted in the original protected layer. -/
theorem leg_first_protected {G : Finset Plane} {e : Plane × Plane}
    (he : e ∈ originalLegs G) : e.1 ∈ protectedSites G := by
  obtain ⟨x, hx, hm⟩ := Finset.mem_biUnion.mp he
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hm
  obtain ⟨hzn, hzG⟩ := Finset.mem_sdiff.mp hz
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hzn
  have hdist : latticeDist x (x + d.step) = 1 := by
    cases d <;> simp [latticeDist, Compass.step]
  refine Finset.mem_filter.mpr ⟨hx, ?_⟩
  have hle : boundaryDepth G x ≤ (latticeDist x (x + d.step) : ℕ∞) :=
    iInf_le (fun y : {z | z ∉ G} => (latticeDist x y.val : ℕ∞)) ⟨x + d.step, hzG⟩
  exact hle.trans (by rw [hdist]; norm_num)

/-- All surviving original leg factors, in their original enumeration. -/
def legFactors {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (s : Plane → Vec3) : ℝ :=
  ∏ e : originalLegs G, if b = true ∧ e.val.1 ∈ D.active then
    1 + dot (τ e).val (s e.val.1) else 1

/-- The factors independent of the spin at the departure. -/
def exteriorFactors {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (u : Plane) (s : Plane → Vec3) : ℝ :=
  (∏ e ∈ exteriorBonds D u, (1 + dot (s e.1) (s e.2))) * legFactors D τ b s

private theorem leg_ne {G : Finset Plane} {u : Plane} (hu : u ∉ protectedSites G)
    (e : originalLegs G) : e.val.1 ≠ u := by
  intro he
  exact hu (he ▸ leg_first_protected e.property)

private theorem legFactors_update {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) {u : Plane} (hu : u ∉ protectedSites G)
    (s : Plane → Vec3) (a : Vec3) :
    legFactors D τ b (Function.update s u a) = legFactors D τ b s := by
  apply Finset.prod_congr rfl
  intro e he
  rw [Function.update_of_ne (leg_ne hu e)]

private theorem exteriorFactors_update {G : Finset Plane} (D : Network G)
    (τ : PinAssignment G) (b : Bool) {u : Plane} (hu : u ∉ protectedSites G)
    (s : Plane → Vec3) (a : Vec3) :
    exteriorFactors D τ b u (Function.update s u a) = exteriorFactors D τ b u s := by
  unfold exteriorFactors
  rw [legFactors_update D τ b hu]
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  have hne := (Finset.mem_filter.mp he).2
  simp only [not_or] at hne
  rw [Function.update_of_ne hne.1, Function.update_of_ne hne.2]

/-- The outside factors, including the original leg slots, agree after a step. -/
theorem exteriorFactors_step {G : Finset Plane} {D : Network G} {u o : Plane}
    (hu : D.AdmissibleStart u) (hp : D.Present u o) (τ : PinAssignment G)
    (b : Bool) (s : Plane → Vec3) :
    exteriorFactors (traceStep D u o) τ b u s = exteriorFactors D τ b u s := by
  unfold exteriorFactors
  rw [exteriorBonds_step hu hp]
  congr 1
  apply Finset.prod_congr rfl
  intro e he
  have hne := leg_ne hu.2.1 e
  have ha : e.val.1 ∈ (traceStep D u o).active ↔ e.val.1 ∈ D.active := by
    simp only [Network.active, Finset.mem_filter]
    change (_ ∧ Function.update D.status u _ e.val.1 ≠ .X) ↔ _
    rw [Function.update_of_ne hne]
  simp only [ha]

/-- Separate the variable incident factors from the common outside factors. -/
theorem factors_update {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) {u : Plane} (hu : u ∉ protectedSites G) (s : Plane → Vec3) (a : Vec3) :
    (∏ e ∈ D.bonds, (1 + dot (Function.update s u a e.1) (Function.update s u a e.2))) *
      legFactors D τ b (Function.update s u a) =
        (∏ o ∈ D.presentNeighbours u, (1 + dot a (s o))) * exteriorFactors D τ b u s := by
  rw [bond_product_split D u
    (fun x y => 1 + dot (Function.update s u a x) (Function.update s u a y))
    (fun x y => by rw [dot_comm])]
  have hp : (∏ o ∈ D.presentNeighbours u,
      (1 + dot (Function.update s u a u) (Function.update s u a o))) =
      ∏ o ∈ D.presentNeighbours u, (1 + dot a (s o)) := by
    apply Finset.prod_congr rfl
    intro o ho
    have hp := (Finset.mem_filter.mp ho).2
    have hne : o ≠ u := by
      intro h; subst o
      simpa [Adjacent, latticeDist] using hp.2.2.1
    rw [Function.update_self, Function.update_of_ne hne]
  rw [hp, mul_assoc]
  exact congrArg (fun x => (∏ o ∈ D.presentNeighbours u, (1 + dot a (s o))) * x)
    (exteriorFactors_update D τ b hu s a)

/-- The padded one-site law, with delta-zero rather than zero mass at X. -/
def paddedSiteFunctional (s : Status) (f : Vec3 → ℝ) : ℝ :=
  ∑ j : SpinLetter, paddedWeight s j * f (spinVector j)

/-- Exact disintegration at an unprotected site. This identity retains the
untouched original leg product inside the common exterior factor. -/
theorem partition_site_fibre {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (b : Bool) (u : G) (hu : u.val ∉ protectedSites G) (f : (Plane → Vec3) → ℝ) :
    D.partition τ b f =
      ∑ n : {x : G // x ≠ u} → SpinLetter,
        (∏ x : {x : G // x ≠ u}, paddedWeight (D.status x.val.val) (n x)) *
          exteriorFactors D τ b u.val (fibreSpins u n) *
            paddedSiteFunctional (D.status u.val) (fun a =>
              f (Function.update (fibreSpins u n) u.val a) *
                ∏ o ∈ D.presentNeighbours u.val, (1 + dot a (fibreSpins u n o))) := by
  classical
  rw [partition_eq_padded]
  have he : paddedPartition D τ b f =
      ∑ n : (x : G) → SpinLetter, (∏ x : G, paddedWeight (D.status x.val) (n x)) *
        (f (volumeSpins n) *
          (∏ e ∈ D.bonds, (1 + dot (volumeSpins n e.1) (volumeSpins n e.2))) *
            legFactors D τ b (volumeSpins n)) := by
    unfold paddedPartition legFactors
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [he, finite_site_fibre D u (fun a => f a *
    (∏ e ∈ D.bonds, (1 + dot (a e.1) (a e.2))) * legFactors D τ b a)]
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_assoc]
  congr 1
  unfold paddedSiteFunctional
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [mul_assoc (f _) _ _, factors_update D τ b hu]
  ring

end AKLT.W.REC043
