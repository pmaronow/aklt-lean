import AKLT.Blueprint.Q.NodesEnergy

noncomputable section
open AKLT.Defs AKLT.Challenge

namespace AKLT.W.Q055

theorem main : AKLT.Blueprint.Q.PlaneAssignmentReindexStatement := by
  classical
  intro W p α hbase U J hUW hJW hdisj a b

  let eU : {x // x ∈ U} ↪ W :=
    ⟨fun x => ⟨x.1, hUW x.2⟩,
      fun x y h => Subtype.ext (congrArg (fun z : W => z.val) h)⟩
  let eJ : {x // x ∈ J} ↪ W :=
    ⟨fun x => ⟨x.1, hJW x.2⟩,
      fun x y h => Subtype.ext (congrArg (fun z : W => z.val) h)⟩
  let U' : Finset W := U.attach.map eU
  let J' : Finset W := J.attach.map eJ

  have hcardU : U'.card = U.card := by
    simp [U']
  have hmemU (x : W) : x ∈ U' ↔ x.val ∈ U := by
    change x ∈ U.attach.map eU ↔ x.val ∈ U
    rw [Finset.mem_map]
    simp only [Finset.mem_attach, true_and]
    constructor
    · rintro ⟨y, hxy⟩
      have hval : y.val = x.val := congrArg (fun z : W => z.val) hxy
      exact hval ▸ y.property
    · intro hx
      refine ⟨⟨x.val, hx⟩, ?_⟩
      apply Subtype.ext
      rfl
  have hmemJ (x : W) : x ∈ J' ↔ x.val ∈ J := by
    change x ∈ J.attach.map eJ ↔ x.val ∈ J
    rw [Finset.mem_map]
    simp only [Finset.mem_attach, true_and]
    constructor
    · rintro ⟨y, hxy⟩
      have hval : y.val = x.val := congrArg (fun z : W => z.val) hxy
      exact hval ▸ y.property
    · intro hx
      refine ⟨⟨x.val, hx⟩, ?_⟩
      apply Subtype.ext
      rfl

  have hdisj' : Disjoint U' J' := by
    rw [Finset.disjoint_left]
    intro x hxU hxJ
    exact (Finset.disjoint_left.mp hdisj) (hmemU x |>.mp hxU) (hmemJ x |>.mp hxJ)

  let aW : PlaneConfiguration W := fun x => a x.val
  let bW : PlaneConfiguration W := fun x => b x.val

  have hJ (σ : PlaneConfiguration W) :
      (∀ x ∈ J, extendLetters σ x = a x) ↔ (∀ x ∈ J', σ x = aW x) := by
    constructor
    · intro h x hx
      have hxJ : x.val ∈ J := (hmemJ x).mp hx
      have hxW : x.val ∈ W := hJW hxJ
      simpa [aW, extendLetters, hxW] using h x.val hxJ
    · intro h x hx
      have hxW : x ∈ W := hJW hx
      have hxJ : (⟨x, hxW⟩ : W) ∈ J' := (hmemJ ⟨x, hxW⟩).mpr hx
      have hxval := h ⟨x, hxW⟩ hxJ
      simpa [aW, extendLetters, hxW] using hxval

  have hU (σ : PlaneConfiguration W) :
      (∀ x ∈ U, extendLetters σ x = b x) ↔ (∀ x ∈ U', σ x = bW x) := by
    constructor
    · intro h x hx
      have hxU : x.val ∈ U := (hmemU x).mp hx
      have hxW : x.val ∈ W := hUW hxU
      simpa [bW, extendLetters, hxW] using h x.val hxU
    · intro h x hx
      have hxW : x ∈ W := hUW hx
      have hxU : (⟨x, hxW⟩ : W) ∈ U' := (hmemU ⟨x, hxW⟩).mpr hx
      have hxval := h ⟨x, hxW⟩ hxU
      simpa [bW, extendLetters, hxW] using hxval

  have hJfun :
      (fun σ : PlaneConfiguration W => ∀ x ∈ J, extendLetters σ x = a x) =
        (fun σ => ∀ x ∈ J', σ x = aW x) := by
    funext σ
    exact propext (hJ σ)
  have hUfun :
      (fun σ : PlaneConfiguration W => ∀ x ∈ U, extendLetters σ x = b x) =
        (fun σ => ∀ x ∈ U', σ x = bW x) := by
    funext σ
    exact propext (hU σ)

  have h := hbase U' J' hdisj' aW bW
  rw [← hJfun, ← hUfun] at h
  rw [hcardU] at h
  exact h

end AKLT.W.Q055
