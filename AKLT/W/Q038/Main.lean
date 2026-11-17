module
public import AKLT.Blueprint.Q.NodesSplits

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Challenge

namespace AKLT.W.Q038

abbrev StarChart (n : ℕ) := EuclideanSpace ℂ (Fin n × (Fin 5 → Fin 5))

def starRow {n : ℕ} (v : StarChart n) (r : Fin n) : AKLT.Defs.StarHilbert :=
  WithLp.toLp 2 (fun s => v (r, s))

theorem starRow_eq {n : ℕ} (v : StarChart n) (r : Fin n) :
    starRow v r = WithLp.toLp 2 (fun s => v (r, s)) := rfl

theorem starRow_apply {n : ℕ} (v : StarChart n) (r : Fin n) (s : Fin 5 → Fin 5) :
    starRow v r s = v (r, s) := rfl

theorem starRow_zero {n : ℕ} (r : Fin n) :
    starRow (0 : StarChart n) r = 0 := by
  ext s
  change (0 : StarChart n) (r, s) = (0 : AKLT.Defs.StarHilbert) s
  rw [PiLp.zero_apply, PiLp.zero_apply]

def starFiberSpace (n : ℕ) (j : Fin 4) : Submodule ℂ (StarChart n) where
  carrier := {v | ∀ r, starRow v r ∈ Module.End.eigenspace (starCasimir j) 20}
  zero_mem' := by
    intro r
    rw [starRow_zero]
    exact (Module.End.eigenspace (starCasimir j) 20).zero_mem
  add_mem' := by
    intro v w hv hw r
    exact (Module.End.eigenspace (starCasimir j) 20).add_mem (hv r) (hw r)
  smul_mem' := by
    intro c v hv r
    exact (Module.End.eigenspace (starCasimir j) 20).smul_mem c (hv r)

def starRowProjection {n : ℕ} (j : Fin 4) (v : StarChart n) : StarChart n :=
  WithLp.toLp 2 (fun p =>
    (Module.End.eigenspace (starCasimir j) 20).starProjection (starRow v p.1) p.2)

theorem starRowProjection_apply {n : ℕ} (j : Fin 4) (v : StarChart n)
    (r : Fin n) (s : Fin 5 → Fin 5) :
    starRowProjection j v (r, s) =
      (Module.End.eigenspace (starCasimir j) 20).starProjection (starRow v r) s := rfl

-- Keep changes of row notation outside applications of the concrete Casimir.
theorem casimirCopies_starRow {L N : Size} (x : Site L N) {n : ℕ}
    (U : Hilbert L N ≃ₗᵢ[ℂ] StarChart n)
    (hCopies : AKLT.Blueprint.Q.casimirCopies x n U)
    (j : Fin 4) (ψ : Hilbert L N) (r : Fin n) (s : Fin 5 → Fin 5) :
    U (bondCasimir (AKLT.Blueprint.Q.starEdge x j) ψ) (r, s) =
      starCasimir j (starRow (U ψ) r) s :=
  (hCopies j ψ r s).trans
    (congrArg (fun v : AKLT.Defs.StarHilbert => starCasimir j v s) (starRow_eq (U ψ) r).symm)

theorem starRowProjection_mem {n : ℕ} (j : Fin 4) (v : StarChart n) :
    starRowProjection j v ∈ starFiberSpace n j := by
  intro r
  have hrow : starRow (starRowProjection j v) r =
      (Module.End.eigenspace (starCasimir j) 20).starProjection (starRow v r) := by
    ext s
    rfl
  rw [hrow]
  exact (Module.End.eigenspace (starCasimir j) 20).starProjection_apply_mem _

theorem starRowProjection_orthogonal {n : ℕ} (j : Fin 4) (v w : StarChart n)
    (hw : w ∈ starFiberSpace n j) :
    inner ℂ (v - starRowProjection j v) w = 0 := by
  let K : Submodule ℂ AKLT.Defs.StarHilbert := Module.End.eigenspace (starCasimir j) 20
  have hinner : inner ℂ (v - starRowProjection j v) w =
      ∑ r : Fin n, inner ℂ (starRow v r - K.starProjection (starRow v r)) (starRow w r) := by
    simp [K, starRowProjection, starRow, PiLp.inner_apply, Fintype.sum_prod_type]
  rw [hinner]
  apply Finset.sum_eq_zero
  intro r hr
  exact K.starProjection_inner_eq_zero (starRow v r) (starRow w r) (hw r)

theorem starFiberProjection_apply {n : ℕ} (j : Fin 4) (v : StarChart n)
    (r : Fin n) (s : Fin 5 → Fin 5) :
    (starFiberSpace n j).starProjection v (r, s) =
      (Module.End.eigenspace (starCasimir j) 20).starProjection (starRow v r) s := by
  let K : Submodule ℂ AKLT.Defs.StarHilbert := Module.End.eigenspace (starCasimir j) 20
  let F : Submodule ℂ (StarChart n) := starFiberSpace n j
  let p : StarChart n := starRowProjection j v
  have hp : p ∈ F := by
    intro t
    have hrow : starRow p t = K.starProjection (starRow v t) := by
      ext u
      rfl
    rw [hrow]
    exact K.starProjection_apply_mem (starRow v t)
  have hinner (w : StarChart n) :
      inner ℂ (v - p) w =
        ∑ t : Fin n, inner ℂ (starRow v t - K.starProjection (starRow v t))
          (starRow w t) := by
    simp [p, K, starRowProjection, starRow, PiLp.inner_apply, Fintype.sum_prod_type]
  have horth : ∀ w, w ∈ F → inner ℂ (v - p) w = 0 := by
    intro w hw
    rw [hinner]
    apply Finset.sum_eq_zero
    intro t ht
    exact K.starProjection_inner_eq_zero (starRow v t) (starRow w t) (hw t)
  have heq := F.eq_starProjection_of_mem_of_inner_eq_zero hp horth
  have hcoord := congrArg (fun z : StarChart n => z (r, s)) heq
  simpa [F, p, starRowProjection, starRow, K] using hcoord

theorem chart_projector_mem {L N : Size} (x : Site L N) {n : ℕ}
    (U : Hilbert L N ≃ₗᵢ[ℂ] StarChart n)
    (hCopies : AKLT.Blueprint.Q.casimirCopies x n U) (j : Fin 4) (ψ : Hilbert L N) :
    U (P (AKLT.Blueprint.Q.starEdge x j) ψ) ∈ starFiberSpace n j := by
  let e : Bond L N := AKLT.Blueprint.Q.starEdge x j
  let K : Submodule ℂ (Hilbert L N) := Module.End.eigenspace (bondCasimir e) 20
  let q : StarChart n := U (P e ψ)
  have hPmem : P e ψ ∈ K := by
    change K.starProjection ψ ∈ K
    exact K.starProjection_apply_mem ψ
  intro t
  rw [Module.End.mem_eigenspace_iff]
  have he := Module.End.mem_eigenspace_iff.mp hPmem
  ext u
  have hc : U (bondCasimir e (P e ψ)) (t, u) = starCasimir j (starRow q t) u := by
    exact casimirCopies_starRow x U hCopies j (P e ψ) t u
  calc
    starCasimir j (starRow q t) u = U (bondCasimir e (P e ψ)) (t, u) := hc.symm
    _ = U ((20 : ℂ) • P e ψ) (t, u) := by rw [he]
    _ = ((20 : ℂ) • starRow q t) u := by simp [q, starRow]

theorem chart_eigenspace_preimage {L N : Size} (x : Site L N) {n : ℕ}
    (U : Hilbert L N ≃ₗᵢ[ℂ] StarChart n)
    (hCopies : AKLT.Blueprint.Q.casimirCopies x n U) (j : Fin 4)
    (z : StarChart n) (hz : z ∈ starFiberSpace n j) :
    U.symm z ∈ Module.End.eigenspace (bondCasimir (AKLT.Blueprint.Q.starEdge x j)) 20 := by
  let e : Bond L N := AKLT.Blueprint.Q.starEdge x j
  change ∀ t, starRow z t ∈ Module.End.eigenspace (starCasimir j) 20 at hz
  have hrow t := Module.End.mem_eigenspace_iff.mp (hz t)
  have hmap : U (bondCasimir e (U.symm z)) = (20 : ℂ) • z := by
    ext p
    rcases p with ⟨t, u⟩
    calc
      U (bondCasimir e (U.symm z)) (t, u) =
        starCasimir j (starRow (U (U.symm z)) t) u :=
          casimirCopies_starRow x U hCopies j (U.symm z) t u
      _ = starCasimir j (starRow z t) u :=
        congrArg (fun w : StarChart n => starCasimir j (starRow w t) u)
          (U.apply_symm_apply z)
      _ = (20 : ℂ) * z (t, u) := by
        have hu := congrArg (fun w : AKLT.Defs.StarHilbert => w u) (hrow t)
        simpa only [PiLp.smul_apply, starRow_apply, smul_eq_mul] using hu
      _ = ((20 : ℂ) • z) (t, u) := by simp
  rw [Module.End.mem_eigenspace_iff]
  apply U.injective
  simpa using hmap

theorem chart_projector_orthogonal {L N : Size} (x : Site L N) {n : ℕ}
    (U : Hilbert L N ≃ₗᵢ[ℂ] StarChart n)
    (hCopies : AKLT.Blueprint.Q.casimirCopies x n U) (j : Fin 4) (ψ : Hilbert L N)
    (z : StarChart n) (hz : z ∈ starFiberSpace n j) :
    inner ℂ (U ψ - U (P (AKLT.Blueprint.Q.starEdge x j) ψ)) z = 0 := by
  let e : Bond L N := AKLT.Blueprint.Q.starEdge x j
  let K : Submodule ℂ (Hilbert L N) := Module.End.eigenspace (bondCasimir e) 20
  have hzK := chart_eigenspace_preimage x U hCopies j z hz
  have horth := K.starProjection_inner_eq_zero ψ (U.symm z) hzK
  calc
    inner ℂ (U ψ - U (P e ψ)) z =
        inner ℂ (U (ψ - P e ψ)) (U (U.symm z)) := by simp [map_sub]
    _ = inner ℂ (ψ - P e ψ) (U.symm z) := U.inner_map_map _ _
    _ = 0 := horth

theorem starFiberProjection_eq_rowProjection {n : ℕ} (j : Fin 4) (v : StarChart n) :
    (starFiberSpace n j).starProjection v = starRowProjection j v :=
  (starFiberSpace n j).eq_starProjection_of_mem_of_inner_eq_zero
    (starRowProjection_mem j v) (fun w hw => starRowProjection_orthogonal j v w hw)

theorem main : AKLT.Blueprint.Q.StarProjectorTransportStatement := by
  intro L N x n U hCopies j ψ r s
  let e : Bond L N := AKLT.Blueprint.Q.starEdge x j
  let F : Submodule ℂ (StarChart n) := starFiberSpace n j
  have hqproj : F.starProjection (U ψ) = U (P e ψ) :=
    F.eq_starProjection_of_mem_of_inner_eq_zero (chart_projector_mem x U hCopies j ψ)
      (fun z hz => chart_projector_orthogonal x U hCopies j ψ z hz)
  have hqp : U (P e ψ) = starRowProjection j (U ψ) :=
    hqproj.symm.trans (starFiberProjection_eq_rowProjection j (U ψ))
  calc
    U (P e ψ) (r, s) = starRowProjection j (U ψ) (r, s) :=
      congrArg (fun z : StarChart n => z (r, s)) hqp
    _ = (Module.End.eigenspace (starCasimir j) 20).starProjection (starRow (U ψ) r) s :=
      starRowProjection_apply j (U ψ) r s
    _ = (Module.End.eigenspace (starCasimir j) 20).starProjection
        (WithLp.toLp 2 (fun t => U ψ (r, t))) s :=
      congrArg (fun v : AKLT.Defs.StarHilbert =>
        (Module.End.eigenspace (starCasimir j) 20).starProjection v s) (starRow_eq (U ψ) r)

end AKLT.W.Q038

#print axioms AKLT.W.Q038.main
