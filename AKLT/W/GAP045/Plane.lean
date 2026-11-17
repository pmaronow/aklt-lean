module
public import AKLT.W.GAP045.Patch

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Gap
namespace AKLT.W.GAP045
attribute [local instance] Classical.propDecidable
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- Insert a subvolume configuration, retaining the current exterior. -/
def insertVolume (P : PlaneSpec) (W V : Finset Plane) (σ : PlaneConfig P W)
    (τ : PlaneConfig P V) : PlaneConfig P W :=
  fun x => if hx : x.val ∈ V then τ ⟨x.val,hx⟩ else σ x

lemma insertVolume_outside (P : PlaneSpec) (W V : Finset Plane)
    (σ : PlaneConfig P W) (τ : PlaneConfig P V) :
    AgreeOutside (sitesInVolume W V) σ (insertVolume P W V σ τ) := by
  intro x hx
  have hx' : x.val ∉ V := by simpa [sitesInVolume] using hx
  simp [insertVolume, hx']

lemma insertVolume_inside (P : PlaneSpec) (W V : Finset Plane)
    (σ : PlaneConfig P W) (τ : PlaneConfig P V) (x : W) (hx : x.val ∈ V) :
    insertVolume P W V σ τ x = τ ⟨x.val,hx⟩ := by simp [insertVolume, hx]

lemma marginal_supported_inverse {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ]
    [DecidableEq Ω] [DecidableEq Ξ]
    (p : Weight Ω) (f : Ω → Ξ) (g : Ξ → Ω)
    (h : ∀ x, p x ≠ 0 → g (f x) = x) : marginal (marginal p f) g = p := by
  rw [marginal_comp]
  funext z
  unfold marginal
  rw [Finset.sum_eq_single z]
  · by_cases hz : p z = 0
    · simp [hz]
    · simp [Function.comp_def, h z hz]
  · intro x _ hxz
    by_cases hx : p x = 0
    · simp [hx]
    · simp [Function.comp_def, h x hx, hxz]
  · simp

lemma fibre_probability (P : PlaneSpec) (hP : RegularSpec P)
    (W V : Finset Plane) (η : Config P.Letter) (σ : PlaneConfig P W) :
    Probability (fibre (P.law W η) (sitesInVolume W V) σ) := by
  apply condition_probability (fun x => (hP.1 W η).1 x |>.le)
  exact event_pos_of_atom (fun x => (hP.1 W η).1 x |>.le) _ σ
    (fun _ _ => rfl) ((hP.1 W η).1 σ)

lemma fibre_to_local (P : PlaneSpec) (hP : RegularSpec P)
    (W V : Finset Plane) (hV : V ⊆ W) (η : Config P.Letter) (σ : PlaneConfig P W) :
    marginal (fibre (P.law W η) (sitesInVolume W V) σ)
      (fun τ => restrict V (fill P W η τ)) = P.law V (fill P W η σ) := by
  have he : AgreeOutside (sitesInVolume W V) σ =
      (fun τ => ∀ x : W, x.val ∉ V → τ x = σ x) := by
    funext τ
    apply propext
    simp only [AgreeOutside, sitesInVolume, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h x hx <;> exact (h x hx).symm
  simpa only [fibre, he] using hP.2.1 W V hV η σ

lemma local_to_fibre (P : PlaneSpec) (hP : RegularSpec P)
    (W V : Finset Plane) (hV : V ⊆ W) (η : Config P.Letter) (σ : PlaneConfig P W) :
    marginal (P.law V (fill P W η σ)) (insertVolume P W V σ) =
      fibre (P.law W η) (sitesInVolume W V) σ := by
  rw [← fibre_to_local P hP W V hV η σ]
  apply marginal_supported_inverse
  intro τ ht
  have hpos : 0 < fibre (P.law W η) (sitesInVolume W V) σ τ :=
    lt_of_le_of_ne ((fibre_probability P hP W V η σ).1 τ) (Ne.symm ht)
  have hs := condition_support (AgreeOutside (sitesInVolume W V) σ) τ hpos
  funext x
  by_cases hx : x.val ∈ V
  · simp [insertVolume, restrict, fill, hx, x.property]
  · have hsx := hs x (by simpa [sitesInVolume] using hx)
    simpa [insertVolume, hx] using hsx

/-- Lift both local components to the full exterior fibers. -/
def liftLocalCoupling (P : PlaneSpec) (hP : RegularSpec P)
    (W V : Finset Plane) (hV : V ⊆ W) (η ξ : Config P.Letter)
    (σ τ : PlaneConfig P W)
    (c : Coupling (P.law V (fill P W η σ)) (P.law V (fill P W ξ τ))) :
    Coupling (fibre (P.law W η) (sitesInVolume W V) σ)
      (fibre (P.law W ξ) (sitesInVolume W V) τ) where
  mass := (mapCoupling c (insertVolume P W V σ) (insertVolume P W V τ)).mass
  nonnegative := (mapCoupling c (insertVolume P W V σ) (insertVolume P W V τ)).nonnegative
  first_marginal x := ((mapCoupling c (insertVolume P W V σ)
    (insertVolume P W V τ)).first_marginal x).trans (congrFun (local_to_fibre P hP W V hV η σ) x)
  second_marginal y := ((mapCoupling c (insertVolume P W V σ)
    (insertVolume P W V τ)).second_marginal y).trans (congrFun (local_to_fibre P hP W V hV ξ τ) y)

lemma lifted_support (P : PlaneSpec) (hP : RegularSpec P)
    (W V : Finset Plane) (η ξ : Config P.Letter) (σ τ : PlaneConfig P W)
    (c : Coupling (fibre (P.law W η) (sitesInVolume W V) σ)
      (fibre (P.law W ξ) (sitesInVolume W V) τ))
    (v : PlaneConfig P W × PlaneConfig P W) (hv : 0 < c.mass v.1 v.2) :
    AgreeOutside (sitesInVolume W V) σ v.1 ∧ AgreeOutside (sitesInVolume W V) τ v.2 := by
  exact ⟨condition_support _ _ (hv.trans_le (coupling_atom_first c _ _)),
    condition_support _ _ (hv.trans_le (coupling_atom_second c _ _))⟩

lemma insert_agreement (P : PlaneSpec) (W V D : Finset Plane) (hD : D ⊆ V)
    (σ τ : PlaneConfig P W) (v : PlaneConfig P V × PlaneConfig P V)
    (hv : AgreeOn (sitesInVolume V D) v.1 v.2) :
    AgreeOn (sitesInVolume W D) (insertVolume P W V σ v.1) (insertVolume P W V τ v.2) := by
  intro x hx
  have hxD : x.val ∈ D := by simpa [sitesInVolume] using hx
  simp only [insertVolume_inside P W V σ v.1 x (hD hxD),
    insertVolume_inside P W V τ v.2 x (hD hxD)]
  exact hv ⟨x.val,hD hxD⟩ (by simpa [sitesInVolume] using hxD)

lemma local_laws_identical (P : PlaneSpec) (hP : RegularSpec P)
    (a y : Plane) (u l : ℕ) (i : ℤ) (hi : 2 ≤ i) (hg : ShellGeometry l a y u)
    (η ξ : Config P.Letter) (hηξ : ∀ z, z ≠ y → η z = ξ z)
    (σ τ : PlaneConfig P (square a u))
    (hs : AgreeOn (sitesInVolume (square a u) (shell a y u (i-1))) σ τ) :
    P.law (farVolume a y u i) (fill P (square a u) η σ) =
      P.law (farVolume a y u i) (fill P (square a u) ξ τ) := by
  apply hP.2.2
  intro x hx hd
  by_cases hxW : x ∈ square a u
  · have hxD := (hg.2.2.2 i hi).1 x (Finset.mem_sdiff.mpr ⟨hxW,hx⟩) hd
    have he := hs ⟨x,hxW⟩ (by simpa [sitesInVolume] using hxD)
    simpa [fill, hxW] using he
  · have hxy : x ≠ y := by
      intro he; subst x; exact (hg.2.2.2 i hi).2 hd
    simpa [fill, hxW] using hηξ x hxy

end AKLT.W.GAP045
