module
public import AKLT.W.REC096.Trace

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Blueprint.Rec

namespace AKLT.W.REC096

theorem initial_invariant (p : PairSetup) : PrefixInvariant p.normalized p.u p.c := by
  classical
  rcases p.pair with ⟨hcon, hu, hv, hc, hcx, hadj, hadjv, hgeom, huc, hvc⟩
  have hstatus (x : Plane) : p.normalized.status x = p.D.status x := rfl
  have hactive : p.normalized.active = p.D.active := rfl
  have hkept (x z : Plane) (hz : z ≠ p.c) :
      z ∈ p.normalized.kept x ↔ z ∈ p.D.kept x := by
    simp only [PairData.normalized, normalizeStart]
    split_ifs <;> simp [hz]
  refine ⟨hcon.1.1.1, ?_, ?_, ?_, ?_, hadj, ?_, ?_, ?_⟩
  · intro x
    change (if x = p.u ∧ p.D.status p.u = .U then (p.D.kept x).erase p.c
      else p.D.kept x) ⊆ neighbors x ∩ p.G
    split_ifs
    · intro z hz
      exact hcon.1.1.2.1 x (Finset.mem_of_mem_erase hz)
    · exact hcon.1.1.2.1 x
  · intro x hx hxu hU
    simpa [PairData.normalized, normalizeStart, hxu] using hcon.2.1 x hx hU
  · intro x hx hxu hD
    simpa [PairData.normalized, normalizeStart, hxu] using hcon.2.2.1 x hx hD
  · intro x hx z hz haxz
    have hxc : x ≠ p.c := by
      rintro rfl
      exact (Finset.mem_filter.mp hx).2 hcx
    have hzc : z ≠ p.c := by
      rintro rfl
      exact (Finset.mem_filter.mp hz).2 hcx
    rw [hkept x z hzc, hkept z x hxc]
    exact hcon.2.2.2 x hx z hz haxz
  · simpa only [hstatus, hcx] using (show Status.X ≠ .U by decide)
  · intro hU
    change p.D.status p.u = .U at hU
    change (if p.u = p.u ∧ p.D.status p.u = .U then (p.D.kept p.u).erase p.c
      else p.D.kept p.u) = _
    simp [hU, hcon.2.1 p.u (Finset.mem_filter.mp hu).1 hU]
  · intro hD x z hpx hpz
    have hD' : p.D.status p.u = .D := hD
    have hdU : p.D.status p.u ≠ .U := by rw [hD']; decide
    have he : p.normalized = p.D := by
      unfold PairData.normalized normalizeStart
      simp [hdU]
    rw [he] at hpx hpz
    rcases huc with hU | ⟨_, hdeg⟩
    · exact (hdU hU).elim
    · exact (Finset.card_le_one.mp hdeg) x (present_mem_neighbors hpx)
        z (present_mem_neighbors hpz)

theorem word_vertex_zero {n : ℕ} (u : Plane) (w : DirectionWord n) :
    wordVertex u w 0 = u := by simp [wordVertex]

theorem word_vertex_succ {n : ℕ} (u : Plane) (w : DirectionWord n) (j : ℕ) (hj : j < n) :
    wordVertex u w (j + 1) = wordVertex u w j + (w ⟨j, hj⟩).step := by
  classical
  have hs : (∑ k : Fin n, if k.val < j + 1 then (w k).step else 0) =
      (∑ k : Fin n, if k.val < j then (w k).step else 0) + (w ⟨j, hj⟩).step := by
    calc
      _ = ∑ k : Fin n, ((if k.val < j then (w k).step else 0) +
          (if k = ⟨j, hj⟩ then (w k).step else 0)) := by
        apply Finset.sum_congr rfl
        intro k _
        by_cases hk : k.val < j
        · have hkn : k ≠ ⟨j, hj⟩ := by
            intro he
            have he' : k.val = j := congrArg Fin.val he
            omega
          simp [hk, hkn, show k.val < j + 1 by omega]
        · by_cases he : k = ⟨j, hj⟩
          · subst k; simp
          · have hkn : ¬ k.val < j + 1 := by
              have : k.val ≠ j := by intro hv; exact he (Fin.ext hv)
              omega
            simp [hk, he, hkn]
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  simp only [wordVertex, hs, add_assoc]

theorem trace_concat {G : Finset Plane} (E : Network G) (l : List Plane) (y o : Plane) :
    traceNetwork E (l ++ [y, o]) = traceStep (traceNetwork E (l ++ [y])) y o := by
  induction l generalizing E with
  | nil => rfl
  | cons x l ih =>
    cases l with
    | nil => rfl
    | cons z l => simpa only [List.cons_append, traceNetwork] using ih (traceStep E x z)

theorem prefix_zero {G : Finset Plane} {n : ℕ} (E : Network G) (u : Plane)
    (w : DirectionWord n) : prefixNetwork E u w 0 = E := by
  unfold prefixNetwork wordVertices
  cases n <;> simp [List.range_succ_eq_map, traceNetwork]

theorem prefix_step {G : Finset Plane} {n : ℕ} (E : Network G) (u : Plane)
    (w : DirectionWord n) (j : ℕ) (hj : j < n) :
    prefixNetwork E u w (j + 1) =
      traceStep (prefixNetwork E u w j) (wordVertex u w j) (wordVertex u w (j + 1)) := by
  have hget (k : ℕ) (hk : k < n + 1) :
      (wordVertices u w)[k]'(by simpa [wordVertices] using hk) = wordVertex u w k := by
    simp [wordVertices]
  have ht₁ := List.take_succ_eq_append_getElem
    (l := wordVertices u w) (i := j) (by simpa [wordVertices] using (show j < n + 1 by omega))
  have ht₂ := List.take_succ_eq_append_getElem
    (l := wordVertices u w) (i := j + 1) (by simpa [wordVertices] using (show j + 1 < n + 1 by omega))
  simp only [wordVertices, List.getElem_map, List.getElem_range] at ht₁ ht₂
  unfold prefixNetwork wordVertices
  rw [ht₂, ht₁, List.append_assoc]
  exact trace_concat E _ _ _

def arrivalSite {n : ℕ} (p : PairSetup) (w : DirectionWord n) (j : ℕ) : Plane :=
  if j = 0 then p.c else wordVertex p.u w (j - 1)

theorem prefix_invariant {n : ℕ} (p : PairSetup) (T : Finset Plane) (w : DirectionWord n)
    (ht : StoppedNetworkTrail p.normalized p.u T w) (j : ℕ) (hj : j ≤ n) :
    PrefixInvariant (prefixNetwork p.normalized p.u w j)
      (wordVertex p.u w j) (arrivalSite p w j) ∧
    (∀ k : Fin n, j ≤ k.val →
      (prefixNetwork p.normalized p.u w j).Present
        (wordVertex p.u w k.val) (wordVertex p.u w (k.val + 1))) := by
  induction j with
  | zero =>
    simp only [prefix_zero, word_vertex_zero, arrivalSite, ↓reduceIte]
    exact ⟨initial_invariant p, fun k _ => ht.2.1 k⟩
  | succ j ih =>
    have hjn : j < n := by omega
    rcases ih (by omega) with ⟨hinv, hfuture⟩
    have hp := hfuture ⟨j, hjn⟩ le_rfl
    rw [prefix_step _ _ _ j hjn]
    constructor
    · simpa [arrivalSite] using invariant_step hinv (ht.2.2.1 j hjn).2 hp
    · intro k hk
      apply step_preserves_unused hinv hp (hfuture k (by omega))
      intro he
      have hki : k = ⟨j, hjn⟩ := ht.1 (show wordBond p.u w k = wordBond p.u w ⟨j, hjn⟩ from he)
      have : k.val = j := congrArg Fin.val hki
      omega

theorem arrival_eq {n : ℕ} (p : PairSetup) (w : DirectionWord n) (i : Fin n) :
    arrivalSite p w i.val = wordVertex p.u w i.val - (wordIncoming p.incoming w i).step := by
  by_cases hi : i.val = 0
  · simp [arrivalSite, hi, wordIncoming, word_vertex_zero, p.incoming_eq]
  · have hpred : i.val - 1 < n := by omega
    have hsucc : i.val - 1 + 1 = i.val := by omega
    have hv := word_vertex_succ p.u w (i.val - 1) hpred
    rw [hsucc] at hv
    simp only [arrivalSite, wordIncoming, hi, ↓reduceDIte, ↓reduceIte, hv]
    simp

end AKLT.W.REC096
