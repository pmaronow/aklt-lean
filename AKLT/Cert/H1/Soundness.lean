module
public import AKLT.Cert.H1.PackedConstructor

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

namespace AKLT.Cert.H1
open AKLT.Defs AKLT.Gen.Gram
open scoped BigOperators

/-- A tensor outer product is one multiplication after spacing the second
factor's exponents by the first factor's length. Signed coefficients are allowed. -/
theorem packed_outer_product (B : Int) (m n : Nat) (f : Fin m → Int) (g : Fin n → Int) :
    (∑ i : Fin m, f i * B^i.val) * (∑ j : Fin n, g j * B^(m*j.val)) =
      ∑ j : Fin n, ∑ i : Fin m, (f i*g j) * B^(i.val+m*j.val) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [pow_add]
  ring

def lowerTriangularCheck (L : IntRows) : Bool :=
  L.zipIdx.all fun (r,i) => decide (r.length ≤ i+1)

theorem lowerTriangularCheck_sound {L : IntRows} (h : lowerTriangularCheck L = true)
    (n : Nat) (i j : Fin n) (hij : i < j) : matrix n L i j = 0 := by
  simp only [lowerTriangularCheck, List.all_eq_true, decide_eq_true_eq] at h
  unfold matrix
  by_cases hi : i.val < L.length
  · have hm : (L[i.val], i.val) ∈ L.zipIdx := by
      apply List.mem_zipIdx_iff_getElem?.mpr
      simp [hi]
    have hr := h _ hm
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getD_eq_default _ _ (by exact le_trans hr (by exact hij))
  · have hz : L.getD i.val [] = [] := List.getD_eq_default L [] (by omega)
    change (L.getD i.val []).getD j.val 0 = 0
    rw [hz]
    rfl

/-- Local-table certificates assert every entry used by the network, rather than
accepting an unverified array from the exporter. -/
theorem tableCheck_sound {s : SiteSpec} {t : Table} (h : tableCheck s t = true)
    (i : Nat) (hi : i < (localTable s).length) :
    t.get i = (localTable s).getD i .zero := by
  simp only [tableCheck, List.all_eq_true, decide_eq_true_eq] at h
  have hm : ((localTable s)[i], i) ∈ (localTable s).zipIdx := by
    apply List.mem_zipIdx_iff_getElem?.mpr
    simp [hi]
  simpa only [List.getD_eq_getElem _ _ hi] using h _ hm

/-- The generic Gram checker discharges the precise division-free row predicate
in Defs. Lower triangularity is a separate, purely structural data obligation. -/
theorem gramResidualRows_of_checked {M L : IntRows} {g d S : Nat}
    (h : checker M L (g : Int) (d : Int) (S : Int) = true) :
    GramResidualRows (matrix M.length M) (matrix M.length L) g d S := by
  simp only [checker, Bool.and_eq_true] at h
  obtain ⟨hm, hl, hls, _hs, hg, hd, hS⟩ := header_spec h.1
  have hdd := checkRows_strictDiagDominant hm hl hls h.2
  refine ⟨by exact_mod_cast hg, by exact_mod_cast hd, by exact_mod_cast hS, ?_⟩
  intro i
  have hdi := hdd i
  change (∑ j ∈ Finset.univ.erase i,
    |gramResidual (matrix M.length M) (matrix M.length L) g d S i j|) <
      gramResidual (matrix M.length M) (matrix M.length L) g d S i i at hdi
  exact ⟨lt_of_le_of_lt (Finset.sum_nonneg fun j _ => abs_nonneg _) hdi, hdi⟩

#print axioms tableCheck_sound
#print axioms gramResidualRows_of_checked
#print axioms packed_outer_product
#print axioms lowerTriangularCheck_sound
end AKLT.Cert.H1
