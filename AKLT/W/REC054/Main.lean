module
public import AKLT.W.REC054.LocalRules

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC054

open AKLT.Blueprint.Rec

private theorem traceNetwork_kept_of_not_mem {G : Finset Plane} (D : Network G)
    (l : List Plane) (x : Plane) (hx : x ∉ l) :
    (traceNetwork D l).kept x = D.kept x := by
  induction l generalizing D with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b bs =>
      have ha : x ≠ a := by intro h; subst x; exact hx (by simp)
      have hb : x ≠ b := by intro h; subst x; exact hx (by simp)
      have htail : x ∉ b :: bs := by
        intro h
        exact hx (by simp [h])
      change (traceNetwork (traceStep D a b) (b :: bs)).kept x = D.kept x
      rw [ih (D := traceStep D a b) htail]
      simp [traceStep, ha, hb]

private theorem traceNetwork_status_of_not_mem {G : Finset Plane} (D : Network G)
    (l : List Plane) (x : Plane) (hx : x ∉ l) :
    (traceNetwork D l).status x = D.status x := by
  induction l generalizing D with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b bs =>
      have ha : x ≠ a := by intro h; subst x; exact hx (by simp)
      have hb : x ≠ b := by intro h; subst x; exact hx (by simp)
      have htail : x ∉ b :: bs := by
        intro h
        exact hx (by simp [h])
      change (traceNetwork (traceStep D a b) (b :: bs)).status x = D.status x
      rw [ih (D := traceStep D a b) htail]
      simp [traceStep, ha]

private theorem traceNetwork_status_append_singleton {G : Finset Plane}
    (D : Network G) (xs : List Plane) (z : Plane) (hz : z ∉ xs) :
    (traceNetwork D (xs ++ [z])).status z = D.status z := by
  induction xs generalizing D with
  | nil => rfl
  | cons a xs ih =>
    cases xs with
    | nil =>
      have ha : a ≠ z := by
        intro h
        subst a
        exact hz (by simp)
      simp [traceNetwork, traceStep, Ne.symm ha]
    | cons b bs =>
      have htail : z ∉ b :: bs := by
        intro h
        exact hz (by simp [h])
      have ha : a ≠ z := by
        intro h
        subst a
        exact hz (by simp)
      change (traceNetwork (traceStep D a b) ((b :: bs) ++ [z])).status z = D.status z
      rw [ih (D := traceStep D a b) htail]
      simp [traceStep, Ne.symm ha]

private theorem wordVertices_split {n : ℕ} (u : Plane) (w : DirectionWord n) :
    wordVertices u w = (List.range n).map (wordVertex u w) ++ [wordVertex u w n] := by
  simp [wordVertices, List.range_succ]

private theorem protected_prefix_absent (p : PairSetup) {n : ℕ}
    (w : DirectionWord n) (htrail : StoppedNetworkTrail p.normalized p.u
      (protectedSites p.G) w) :
    ∀ x ∈ (List.range n).map (wordVertex p.u w), x ∉ protectedSites p.G := by
  intro x hx
  rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
  have hin : i < n := by simpa using hi
  exact (htrail.2.2.1 i hin).2

theorem main :
    AKLT.Blueprint.Rec.TerminalDefectStatement := by
  intro p n w htrail
  dsimp [AKLT.Blueprint.Rec.TerminalDefectStatement]
  let E := traceNetwork p.normalized (wordVertices p.u w)
  let e := wordVertex p.u w n
  have hcons : p.D.Consistent := p.pair.1
  have hprot : e ∈ protectedSites p.G := htrail.2.2.2
  have hu : p.u ∉ protectedSites p.G := p.interior
  have hprefix : ∀ x ∈ (List.range n).map (wordVertex p.u w),
      x ∉ protectedSites p.G := protected_prefix_absent p w htrail
  have hsplit : wordVertices p.u w = (List.range n).map (wordVertex p.u w) ++ [e] :=
    wordVertices_split p.u w
  have hnotE : e ∉ (List.range n).map (wordVertex p.u w) := by
    intro he
    exact (hprefix e he) hprot
  have hstatus : E.status e = .U := by
    change (traceNetwork p.normalized (wordVertices p.u w)).status e = .U
    have hstatus : p.normalized.status e = .U := by
      have := hcons.1.2 e hprot
      exact this.1
    rw [hsplit]
    exact traceNetwork_status_append_singleton p.normalized
      ((List.range n).map (wordVertex p.u w)) e hnotE ▸ hstatus
  have hAux : E.Auxiliary := by
    constructor
    · exact terminal_localRules p w htrail
    · intro x hx
      by_cases hxe : x = e
      · simpa [hxe] using hstatus
      · have hnot : x ∉ wordVertices p.u w := by
          rw [hsplit]
          simp only [List.mem_append, List.mem_singleton]
          exact fun h => h.elim (fun hm => (hprefix x hm) hx) (fun he => hxe he)
        have hxu : x ≠ p.u := by
          intro h
          subst x
          exact hu hx
        have hnorm : p.normalized.status x = p.D.status x := by
          rfl
        rw [traceNetwork_status_of_not_mem p.normalized (wordVertices p.u w) x hnot,
          hnorm]
        exact (hcons.1.2 x hx).1
  constructor
  · exact hAux
  constructor
  · exact hstatus
  · intro x hx hxe
    change E.kept x = neighbours x ∩ p.G
    have hnot : x ∉ wordVertices p.u w := by
      rw [hsplit]
      simp only [List.mem_append, List.mem_singleton]
      exact fun h => h.elim (fun hm => (hprefix x hm) hx) (fun he => hxe he)
    have hxu : x ≠ p.u := by
      intro h
      subst x
      exact hu hx
    have hkept : p.normalized.kept x = p.D.kept x := by
      simp [PairData.normalized, normalizeStart, hxu]
    rw [traceNetwork_kept_of_not_mem p.normalized (wordVertices p.u w) x hnot, hkept]
    exact (hcons.1.2 x hx).2

end AKLT.W.REC054
