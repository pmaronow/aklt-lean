module
public import AKLT.W.REC079.Closure
public import AKLT.W.REC079.LocalComparison
public import AKLT.W.REC078.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators ENNReal
open AKLT.Defs AKLT.Blueprint.Rec AKLT.Cert.H2

namespace AKLT.W.REC079

open AKLT.W.REC096

def pairSetup (p : PairData) (hu : p.u ∉ protectedSites p.G) : PairSetup :=
  { p with
    incoming := Classical.choose (adjacent_direction p.pair.2.2.2.2.2.1)
    incoming_eq := Classical.choose_spec (adjacent_direction p.pair.2.2.2.2.2.1)
    interior := hu }

theorem canonical_initial_direction (p : PairSetup) :
    (canonicalChart p.toPairData).direction p.incoming = kernelIncoming := by
  apply step_injective
  have h := (canonicalChart p.toPairData).step p.c p.incoming
  rw [← p.incoming_eq, canonicalChart_start, canonicalChart_centre] at h
  rw [show kernelCentre = (0 : Plane) from rfl, zero_add] at h
  simpa [kernelStart, kernelCentre, kernelIncoming, Compass.step] using h.symm

theorem canonical_word_incoming (p : PairSetup) {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    wordIncoming kernelIncoming (canonicalWord p.toPairData w) i =
      (canonicalChart p.toPairData).direction (wordIncoming p.incoming w i) := by
  rw [← canonical_initial_direction p]
  exact frame_incoming _ _ _ _

theorem canonical_word_straight (p : PairSetup) {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    wordStraight kernelIncoming (canonicalWord p.toPairData w) i = wordStraight p.incoming w i := by
  unfold wordStraight
  rw [canonical_word_incoming]
  simp only [canonicalWord, FrameChange.word, Equiv.apply_eq_iff_eq]

theorem chart_sub_step (F : LatticeChart) (x : Plane) (d : Compass) :
    F.point (x - d.step) = F.point x - (F.direction d).step := by
  apply (eq_sub_iff_add_eq).mpr
  rw [← F.step, sub_add_cancel]

theorem canonical_arrival (p : PairSetup) {n : ℕ} (w : DirectionWord n) (i : Fin n) :
    (canonicalChart p.toPairData).point (arrivalSite p w i.val) =
      wordVertex kernelStart (canonicalWord p.toPairData w) i.val -
        (wordIncoming kernelIncoming (canonicalWord p.toPairData w) i).step := by
  rw [arrival_eq, chart_sub_step, canonical_word_incoming,
    canonicalWord_vertex _ _ _ (Nat.le_of_lt i.isLt)]

theorem chart_neighbours (F : LatticeChart) (y z : Plane) :
    F.point z ∈ neighbours (F.point y) ↔ z ∈ neighbours y := by
  rw [← adjacent_iff, ← adjacent_iff]
  unfold Adjacent
  rw [F.distance]

theorem dot_comm_rec (a b : Vec3) : dot a b = dot b a := by
  simp only [dot, mul_comm]

theorem pairSignal_pair {G : Finset Plane} (E : Network G) (τ : PinAssignment G)
    (a b : Plane) (hab : a ≠ b) :
    pairSignal E τ {a, b} = |E.expectation τ true (fun n => dot (n a) (n b)) -
      E.expectation τ false (fun n => dot (n a) (n b))| := by
  classical
  have hp : ({a, b} : Finset Plane).toList.Perm [a, b] := by
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _) (by simp [hab])
    simp
  rcases List.perm_pair.mp hp with h | h
  · simp [pairSignal, h]
  · simp only [pairSignal, h]
    congr 2 <;> congr 1 <;> funext n <;> exact dot_comm_rec _ _

theorem pairSignal_zero_of_inactive {G : Finset Plane} (E : Network G) (τ : PinAssignment G)
    (a b : Plane) (hab : a ≠ b) (ha : a ∉ E.active ∨ b ∉ E.active) :
    pairSignal E τ {a, b} = 0 := by
  rw [pairSignal_pair E τ a b hab]
  rcases ha with ha | hb
  · have hf : (fun n : Plane → Vec3 => dot (n a) (n b)) ∘ E.spins = fun _ => 0 := by
      funext n
      simp [Network.spins, ha, dot]
    simp [Network.expectation, Network.partition, Function.comp_def] at hf ⊢
    simp_rw [show ∀ n : (x : E.active) → SpinLetter, dot (E.spins n a) (E.spins n b) = 0
      from congrFun hf]
    simp
  · have hf : ∀ n : (x : E.active) → SpinLetter, dot (E.spins n a) (E.spins n b) = 0 := by
      intro n
      simp [Network.spins, hb, dot]
    simp [Network.expectation, Network.partition, hf]

/-- Present neighbors at a true U departure occur in the kernel's live set. -/
theorem present_kernel_mem (p : PairSetup) {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (i : Fin n)
    (hU : (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U)
    {z : Plane}
    (hz : (prefixNetwork p.normalized p.u w i.val).Present (wordVertex p.u w i.val) z) :
    (canonicalChart p.toPairData).point z ∈
      insert (wordVertex kernelStart (canonicalWord p.toPairData w) (i.val + 1))
        (liveOtherNeighbours (canonicalWord p.toPairData w) i) := by
  classical
  let F := canonicalChart p.toPairData
  let cw := canonicalWord p.toPairData w
  have hinv := (prefix_invariant p _ w hw i.val (Nat.le_of_lt i.isLt)).1
  have hnearr : z ≠ arrivalSite p w i.val := by
    have hk := hz.2.2.2.1
    rw [hinv.liveU hU] at hk
    exact (Finset.mem_erase.mp hk).1
  have hzn : F.point z ∈ neighbours (wordVertex kernelStart cw i.val) := by
    rw [canonicalWord_vertex _ _ _ (Nat.le_of_lt i.isLt)]
    exact (chart_neighbours F _ z).mpr ((adjacent_iff _ _).mp hz.2.2.1)
  by_cases hout : F.point z = wordVertex kernelStart cw (i.val + 1)
  · exact Finset.mem_insert.mpr (Or.inl hout)
  · apply Finset.mem_insert.mpr ∘ Or.inr
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_erase.mpr
      refine ⟨hout, Finset.mem_erase.mpr ⟨?_, hzn⟩⟩
      rw [← canonical_arrival p w i]
      exact fun he => hnearr (F.point.injective he)
    · intro hdead
      have hX := kernel_dead_removed p.toPairData w i (F.point z) hdead
      dsimp only [F] at hX
      rw [Equiv.symm_apply_apply] at hX
      exact (Finset.mem_filter.mp hz.2.1).2 hX

theorem kernel_member_nonarrival (p : PairSetup) {n : ℕ} (w : DirectionWord n)
    (hw : StoppedNetworkTrail p.normalized p.u (insert p.v (protectedSites p.G)) w)
    (i : Fin n)
    (hU : (prefixNetwork p.normalized p.u w i.val).status (wordVertex p.u w i.val) = .U)
    {z : Plane} (hz : z ∈ insert
      (wordVertex kernelStart (canonicalWord p.toPairData w) (i.val + 1))
      (liveOtherNeighbours (canonicalWord p.toPairData w) i)) :
    (canonicalChart p.toPairData).point.symm z ∈
      (neighbours (wordVertex p.u w i.val)).erase (arrivalSite p w i.val) := by
  classical
  let F := canonicalChart p.toPairData
  have hinv := (prefix_invariant p _ w hw i.val (Nat.le_of_lt i.isLt)).1
  rcases Finset.mem_insert.mp hz with hout | hother
  · subst z
    rw [canonicalWord_vertex _ _ _ (by omega), Equiv.symm_apply_apply]
    have hp := (prefix_invariant p _ w hw i.val (Nat.le_of_lt i.isLt)).2 i le_rfl
    have hk := hp.2.2.2.1
    rw [hinv.liveU hU] at hk
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hk).1,
      (adjacent_iff _ _).mp hp.2.2.1⟩
  · have hn := Finset.mem_of_mem_erase (Finset.mem_filter.mp hother).1
    have hzn := (Finset.mem_erase.mp hn).2
    have hza := (Finset.mem_erase.mp hn).1
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      apply hza
      rw [← canonical_arrival p w i, ← he]
      exact (F.point.apply_symm_apply z).symm
    · apply (chart_neighbours F _ _).mp
      simpa only [F, Equiv.apply_symm_apply,
        canonicalWord_vertex _ _ _ (Nat.le_of_lt i.isLt)] using hzn

theorem neighbour_pair_type_formula (y : Plane) (a b : Compass) (hab : a ≠ b) :
    responsePairType {y + a.step, y + b.step} =
      if a = b.reverse then PairType.B else PairType.C := by
  classical
  cases a <;> cases b <;>
    simp_all [responsePairType, Compass.reverse, Compass.step] <;> omega

theorem chart_pair_type (F : LatticeChart) {y a b : Plane}
    (ha : a ∈ neighbours y) (hb : b ∈ neighbours y) (hab : a ≠ b) :
    responsePairType {F.point a, F.point b} = responsePairType {a, b} := by
  obtain ⟨da, _, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨db, _, rfl⟩ := Finset.mem_image.mp hb
  have hd : da ≠ db := by rintro rfl; exact hab rfl
  rw [F.step, F.step, neighbour_pair_type_formula _ _ _ (fun h => hd (F.direction.injective h)),
    neighbour_pair_type_formula _ _ _ hd, ← F.reverse]
  simp only [Equiv.apply_eq_iff_eq]

/-- Close the envelope obligation with the actual pair shift. Extra initial
removals give zero signals and need no response-pair assertion. -/
theorem local_envelope : Residual_LocalEnvelopeV2 := by
  classical
  intro p d hd hdepth n w hw hend i hU q hq
  have hu : p.u ∉ protectedSites p.G := by
    simpa only [vertex_zero] using (hw.2.2.1 0 (lt_of_le_of_lt (Nat.zero_le i.val) i.isLt)).2
  let ps := pairSetup p hu
  let F := canonicalChart p
  let E := prefixNetwork p.normalized p.u w i.val
  let y := wordVertex p.u w i.val
  have hsub := (Finset.mem_powersetCard.mp hq).1
  obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hq).2
  let a' := F.point.symm a
  let b' := F.point.symm b
  have hab' : a' ≠ b' := by
    intro he
    exact hab (F.point.symm.injective he)
  have ha := kernel_member_nonarrival ps w hw i hU (hsub (by simp : a ∈ ({a, b} : Finset Plane)))
  have hb := kernel_member_nonarrival ps w hw i hU (hsub (by simp : b ∈ ({a, b} : Finset Plane)))
  change a' ∈ (neighbours y).erase (arrivalSite ps w i.val) at ha
  change b' ∈ (neighbours y).erase (arrivalSite ps w i.val) at hb
  have himage : ({a, b} : Finset Plane).image F.point.symm = {a', b'} := by simp [a', b']
  change pairSignal (removeSite E y) p.τ (({a, b} : Finset Plane).image F.point.symm) ≤ _
  rw [himage]
  by_cases haa : a' ∈ E.active
  · by_cases hba : b' ∈ E.active
    · have hpa : a' ∈ nonarrivalNeighboursV2 E y (wordIncoming ps.incoming w i) := by
        change a' ∈ (neighbours y).erase (y - (wordIncoming ps.incoming w i).step) ∩ E.active
        have harr : arrivalSite ps w i.val = y - (wordIncoming ps.incoming w i).step := arrival_eq ps w i
        rw [← harr]
        exact Finset.mem_inter.mpr ⟨ha, haa⟩
      have hpb : b' ∈ nonarrivalNeighboursV2 E y (wordIncoming ps.incoming w i) := by
        change b' ∈ (neighbours y).erase (y - (wordIncoming ps.incoming w i).step) ∩ E.active
        have harr : arrivalSite ps w i.val = y - (wordIncoming ps.incoming w i).step := arrival_eq ps w i
        rw [← harr]
        exact Finset.mem_inter.mpr ⟨hb, hba⟩
      have hp := pair_closure ps _ n w hw i hU a' hpa b' hpb hab'
      have ht : responsePairType {a, b} = responsePairType {a', b'} := by
        have hh := chart_pair_type F (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab'
        simpa only [a', b', Equiv.apply_symm_apply] using hh
      have hh := AKLT.W.REC078.main p.G p.τ (removeSite E y)
        (responsePairType {a', b'}) a' b' y hp p.u p.v d hdepth
      rw [pairSignal_pair _ _ _ _ hab', ht]
      convert hh using 1
      simp only [pairShift, Finset.sup_insert, Finset.sup_singleton]
      have hdist (z : Plane) :
          min (latticeDist z kernelStart) (latticeDist z (kernelTarget p.X)) =
            min (latticeDist (F.point.symm z) p.u) (latticeDist (F.point.symm z) p.v) := by
        rw [← canonicalChart_start p, ← canonicalChart_target p]
        rw [← F.point.apply_symm_apply z]
        rw [F.distance, F.distance]
        simp only [Equiv.symm_apply_apply]
      rw [hdist a, hdist b]
    · rw [pairSignal_zero_of_inactive _ _ _ _ hab' (Or.inr ?_)]
      · exact responseEnvelope_nonneg _ _
      · rw [remove_active]
        exact fun h => hba (Finset.mem_of_mem_erase h)
  · rw [pairSignal_zero_of_inactive _ _ _ _ hab' (Or.inl ?_)]
    · exact responseEnvelope_nonneg _ _
    · rw [remove_active]
      exact fun h => haa (Finset.mem_of_mem_erase h)

end AKLT.W.REC079
