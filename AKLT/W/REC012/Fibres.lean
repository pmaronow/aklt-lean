module
public import AKLT.W.REC012.Ambient
public import AKLT.W.REC012.Geometry
public import AKLT.W.REC012.LocalProducts

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs
namespace AKLT.W.REC012

lemma dot_comm' (u v : Vec3) : dot u v = dot v u := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i hi
  ring

def fillSpin {G : Finset Plane} (y : Plane) (n : G.erase y → SpinLetter)
    (j : SpinLetter) : G → SpinLetter :=
  fun x => if h : x.val = y then j else n ⟨x.val, Finset.mem_erase.mpr ⟨h, x.property⟩⟩

def splitSpin {G : Finset Plane} (y : Plane) (hy : y ∈ G) :
    (G → SpinLetter) ≃ SpinLetter × (G.erase y → SpinLetter) where
  toFun n := (n ⟨y, hy⟩, fun x => n ⟨x.val, (Finset.mem_erase.mp x.property).2⟩)
  invFun p := fillSpin y p.2 p.1
  left_inv n := by
    funext x
    by_cases hx : x.val = y
    · simp only [fillSpin, dite_eq_left hx]
      exact congrArg n (Subtype.ext hx.symm)
    · simp [fillSpin, hx]
  right_inv p := by
    rcases p with ⟨j,n⟩
    apply Prod.ext
    · simp [fillSpin]
    · funext x
      simp [fillSpin, (Finset.mem_erase.mp x.property).1]

lemma ambientSpins_fill {G : Finset Plane} (y : Plane) (hy : y ∈ G)
    (n : G.erase y → SpinLetter) (j : SpinLetter) :
    ambientSpins G (fillSpin y n j) =
      Function.update (ambientSpins (G.erase y) n) y (spinVector j) := by
  funext x
  by_cases hx : x = y
  · subst x
    simp [ambientSpins, fillSpin, hy]
  · by_cases hxG : x ∈ G
    · have he : x ∈ G.erase y := Finset.mem_erase.mpr ⟨hx, hxG⟩
      simp [ambientSpins, fillSpin, hxG, he, hx]
    · simp [ambientSpins, hxG, hx]

lemma weightProduct_fill {G : Finset Plane} (D : Network G) (y : Plane) (hy : y ∈ G)
    (n : G.erase y → SpinLetter) (j : SpinLetter) :
    (∏ x : G, paddedWeight (D.status x.val) (fillSpin y n j x)) =
      paddedWeight (D.status y) j * ∏ x : G.erase y, paddedWeight (D.status x.val) (n x) := by
  classical
  rw [← Finset.mul_prod_erase (Finset.univ : Finset G)
    (fun x => paddedWeight (D.status x.val) (fillSpin y n j x)) (Finset.mem_univ ⟨y,hy⟩)]
  simp only [fillSpin, ↓reduceDIte]
  congr 1
  symm
  apply Finset.prod_bij (fun x _ => (⟨x.val, (Finset.mem_erase.mp x.property).2⟩ : G))
  · intro x hx
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    exact fun h => (Finset.mem_erase.mp x.property).1 (congrArg Subtype.val h)
  · intro x hx z hz h
    exact Subtype.ext (congrArg (fun q : G => q.val) h)
  · intro x hx
    have hn : x.val ≠ y := fun h => (Finset.mem_erase.mp hx).1 (Subtype.ext h)
    exact ⟨⟨x.val, Finset.mem_erase.mpr ⟨hn,x.property⟩⟩, Finset.mem_univ _, rfl⟩
  · intro x hx
    simp [(Finset.mem_erase.mp x.property).1]

def offBonds {G : Finset Plane} (D : Network G) (y : Plane) : Finset (Plane × Plane) :=
  D.bonds.filter fun e => ¬(e.1 = y ∨ e.2 = y)

def localIntegral {G : Finset Plane} (D : Network G) (y : Plane) (v : Plane → Vec3) : ℝ :=
  ∑ j : SpinLetter, paddedWeight (D.status y) j *
    ∏ e ∈ incident D y, (1 + dot (spinVector j) (v (otherEnd y e)))

def outsideFactor {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y : Plane) (n : G.erase y → SpinLetter) : ℝ :=
  (∏ x : G.erase y, paddedWeight (D.status x.val) (n x)) *
    (∏ e ∈ offBonds D y,
      (1 + dot (ambientSpins (G.erase y) n e.1) (ambientSpins (G.erase y) n e.2))) *
    pinProduct D τ (ambientSpins (G.erase y) n)

lemma pinProduct_update {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y : Plane) (v : Plane → Vec3) (z : Vec3) (hlegs : ∀ e : originalLegs G, e.val.1 ≠ y) :
    pinProduct D τ (Function.update v y z) = pinProduct D τ v := by
  unfold pinProduct
  apply Finset.prod_congr rfl
  intro e he
  rw [Function.update_of_ne (hlegs e)]

lemma bondProduct_update {G : Finset Plane} (D : Network G) (y : Plane)
    (v : Plane → Vec3) (z : Vec3) :
    (∏ e ∈ D.bonds, (1 + dot ((Function.update v y z) e.1) ((Function.update v y z) e.2))) =
      (∏ e ∈ offBonds D y, (1 + dot (v e.1) (v e.2))) *
        ∏ e ∈ incident D y, (1 + dot z (v (otherEnd y e))) := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not D.bonds (fun e => ¬(e.1 = y ∨ e.2 = y))]
  apply congrArg₂ (· * ·)
  · apply Finset.prod_congr rfl
    intro e he
    have hn := (Finset.mem_filter.mp he).2
    simp only [not_or] at hn
    rw [Function.update_of_ne hn.1, Function.update_of_ne hn.2]
  · have hs : D.bonds.filter (fun e => ¬¬(e.1 = y ∨ e.2 = y)) = incident D y := by
      ext e
      simp only [incident, Finset.mem_filter]
      tauto
    rw [hs]
    apply Finset.prod_congr rfl
    intro e he
    have hn := incident_other_ne D y he
    have hi := (Finset.mem_filter.mp he).2
    by_cases hy : e.1 = y
    · have he2 : e.2 ≠ y := by simpa [otherEnd, hy] using hn
      simp [Function.update, hy, he2, otherEnd]
    · have he2 : e.2 = y := hi.resolve_left hy
      simp [Function.update, hy, he2, otherEnd, dot_comm']

lemma ambientTerm_fill {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y : Plane) (hy : y ∈ G) (n : G.erase y → SpinLetter) (j : SpinLetter)
    (hlegs : ∀ e : originalLegs G, e.val.1 ≠ y) :
    ambientTerm D τ (fillSpin y n j) = outsideFactor D τ y n *
      (paddedWeight (D.status y) j *
        ∏ e ∈ incident D y, (1 + dot (spinVector j) (ambientSpins (G.erase y) n (otherEnd y e)))) := by
  unfold ambientTerm outsideFactor
  rw [weightProduct_fill D y hy n j, ambientSpins_fill y hy n j,
    pinProduct_update D τ y _ _ hlegs, bondProduct_update]
  ring

/-- Explicit finite summation over the departure-spin fibers. -/
lemma partition_fibres {G : Finset Plane} (D : Network G) (τ : PinAssignment G)
    (y : Plane) (hy : y ∈ G) (hlegs : ∀ e : originalLegs G, e.val.1 ≠ y) :
    D.partition τ true (fun _ => 1) = ∑ n : G.erase y → SpinLetter,
      outsideFactor D τ y n * localIntegral D y (ambientSpins (G.erase y) n) := by
  rw [partition_eq_ambient]
  unfold ambientPartition
  have heq : (∑ n : G → SpinLetter, ambientTerm D τ n) =
      ∑ p : SpinLetter × (G.erase y → SpinLetter), ambientTerm D τ (fillSpin y p.2 p.1) := by
    apply Fintype.sum_equiv (splitSpin y hy)
    intro n
    exact congrArg (ambientTerm D τ) ((splitSpin y hy).left_inv n).symm
  rw [heq, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp_rw [ambientTerm_fill D τ y hy n _ hlegs]
  rw [← Finset.mul_sum]
  rfl

end AKLT.W.REC012
