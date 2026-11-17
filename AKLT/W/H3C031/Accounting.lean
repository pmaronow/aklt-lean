module
public import CertData.H3.Bridge.Interface
public import AKLT.Cert.H2.Words

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs AKLT.Cert.H3 AKLT.Cert.H3.Production CertData.H3.Bridge

namespace AKLT.W.H3C031

private def tr (t : Plane) (z : Plane) : Plane := z + t

private theorem tr_inj (t : Plane) : Function.Injective (tr t) := by
  intro x y h
  dsimp [tr] at h
  exact add_right_cancel h

private theorem responsePairType_image_tr (p : Finset Plane) (t : Plane) :
    responsePairType (p.image (tr t)) = responsePairType p := by
  unfold responsePairType
  congr 1
  apply propext
  constructor
  · intro h x hx y hy
    rcases h (tr t x) (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      (tr t y) (Finset.mem_image.mpr ⟨y, hy, rfl⟩) with h | h
    · left
      change x.1 + t.1 = y.1 + t.1 at h
      exact add_right_cancel h
    · right
      change x.2 + t.2 = y.2 + t.2 at h
      exact add_right_cancel h
  · intro h x hx y hy
    rcases Finset.mem_image.mp hx with ⟨x₀, hx₀, rfl⟩
    rcases Finset.mem_image.mp hy with ⟨y₀, hy₀, rfl⟩
    rcases h x₀ hx₀ y₀ hy₀ with h | h
    · left
      change x₀.1 + t.1 = y₀.1 + t.1
      exact congrArg (fun z : ℤ => z + t.1) h
    · right
      change x₀.2 + t.2 = y₀.2 + t.2
      exact congrArg (fun z : ℤ => z + t.2) h

private def localLive (x : Plane) (incoming outgoing : Compass) (dead : Finset Plane) : Finset Plane :=
  ((neighbours x).erase (x - incoming.step) |>.erase (x + outgoing.step)) \ dead

private theorem neighbours_tr (x t : Plane) :
    neighbours (x + t) = (neighbours x).image (tr t) := by
  unfold neighbours tr
  rw [Finset.image_image]
  congr 1
  funext d
  simp [add_assoc, add_left_comm, add_comm]

private theorem localLive_tr (x t : Plane) (incoming outgoing : Compass) (dead : Finset Plane) :
    localLive (x + t) incoming outgoing (dead.image (tr t)) =
      (localLive x incoming outgoing dead).image (tr t) := by
  unfold localLive
  rw [neighbours_tr]
  have hin : (x + t) - incoming.step = tr t (x - incoming.step) := by
    dsimp [tr]
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hout : (x + t) + outgoing.step = tr t (x + outgoing.step) := by
    dsimp [tr]
    simp [add_assoc, add_left_comm, add_comm]
  rw [hin, hout, ← Finset.image_erase (tr_inj t), ← Finset.image_erase (tr_inj t),
    ← Finset.image_sdiff _ _ (tr_inj t)]


private def responseWeight (o : Plane) (incoming outgoing : Compass) (live p : Finset Plane) : ℚ :=
  (if o ∈ p then
    if live.card = 1 then betaPrimeBound (decide (outgoing = incoming))
    else betaBound (decide (outgoing = incoming))
  else alphaBound (decide (outgoing = incoming))) * kernelWitness (responsePairType p)

private def responseSum (o : Plane) (incoming outgoing : Compass) (live : Finset Plane) : ℚ :=
  ∑ p ∈ (insert o live).powersetCard 2, responseWeight o incoming outgoing live p

private theorem relaxedReward_eq_responseSum (x : Plane) (incoming outgoing : Compass)
    (dead : Finset Plane) :
    relaxedReward x incoming outgoing dead =
      responseSum (x + outgoing.step) incoming outgoing (localLive x incoming outgoing dead) := by
  rfl

private theorem responseSum_tr (o t : Plane) (incoming outgoing : Compass) (live : Finset Plane) :
    responseSum (o + t) incoming outgoing (live.image (tr t)) =
      responseSum o incoming outgoing live := by
  unfold responseSum
  symm
  apply Finset.sum_bij (fun p _ => p.image (tr t))
  · intro p hp
    rw [Finset.mem_powersetCard] at hp ⊢
    refine ⟨Finset.image_subset_iff.mpr ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp (hp.1 hz) with h | h
      · subst z
        simp [tr]
      · apply Finset.mem_insert.mpr
        right
        exact Finset.mem_image.mpr ⟨z, h, rfl⟩
    · rw [Finset.card_image_of_injective _ (tr_inj t), hp.2]
  · intro p hp q hq heq
    exact (Finset.image_inj (tr_inj t)).mp heq
  · intro q hq
    refine ⟨q.image (tr (-t)), ?_, ?_⟩
    · rw [Finset.mem_powersetCard] at hq ⊢
      refine ⟨Finset.image_subset_iff.mpr ?_, ?_⟩
      · intro z hz
        have hy' := hq.1 hz
        change tr (-t) z ∈ insert o live
        rw [Finset.mem_insert]
        rcases Finset.mem_insert.mp hy' with h | h
        · left
          rw [h]
          simp [tr]
        · right
          rcases Finset.mem_image.mp h with ⟨w, hw, hzw⟩
          have : z = tr t w := hzw.symm
          rw [this]
          simpa [tr, add_assoc, add_left_comm, add_comm] using hw
      · rw [Finset.card_image_of_injective _ (tr_inj (-t)), hq.2]
    · rw [Finset.image_image]
      have hfun : tr t ∘ tr (-t) = id := by
        funext z
        simp [tr]
      rw [hfun, Finset.image_id]
  · intro p hp
    have hmem : o + t ∈ (p.image (tr t)) ↔ o ∈ p := by
      rw [Finset.mem_image]
      constructor
      · rintro ⟨z, hz, h⟩
        have : z = o := by
          dsimp [tr] at h
          exact add_right_cancel h
        simpa [this] using hz
      · intro ho
        exact ⟨o, ho, rfl⟩
    unfold responseWeight
    have hcard : (live.image (tr t)).card = live.card :=
      Finset.card_image_of_injective _ (tr_inj t)
    rw [hcard, responsePairType_image_tr]
    by_cases ho : o ∈ p
    · have ho' : o + t ∈ p.image (tr t) := hmem.mpr ho
      simp [ho, ho']
    · have ho' : o + t ∉ p.image (tr t) := fun hh => ho (hmem.mp hh)
      simp [ho, ho']


theorem relaxedReward_translate (x t : Plane) (a d : Compass) (dead : Finset Plane) :
    relaxedReward (x + t) a d (dead.image (fun z => z + t)) =
      relaxedReward x a d dead := by
  change relaxedReward (x + t) a d (dead.image (tr t)) = _
  rw [relaxedReward_eq_responseSum, relaxedReward_eq_responseSum, localLive_tr]
  have ho : x + t + d.step = (x + d.step) + t := by abel
  rw [ho]
  exact responseSum_tr _ _ _ _ _

theorem snoc_incoming_last {n : Nat} (w : DirectionWord n) (d : Compass) :
    wordIncoming kernelIncoming (AKLT.Cert.H2.snoc w d) (Fin.last n) =
      AKLT.Cert.H2.nextIncoming kernelIncoming w := by
  unfold wordIncoming AKLT.Cert.H2.nextIncoming
  by_cases hn : n = 0
  · subst n; simp
  · simp only [Fin.val_last, dite_eq_right hn, dite_eq_left (show 0 < n by omega)]
    exact AKLT.Cert.H2.snoc_apply_lt w d _ (by omega)

theorem walk_incoming_code {n : Nat} (w : DirectionWord n) (walk : Walk)
    (h : WalkRepresents kernelStart 2 w walk) :
    walk.incoming = directionCode (AKLT.Cert.H2.nextIncoming kernelIncoming w) := by
  rw [h.2.2.1]
  by_cases hn : n = 0
  · subst n; rfl
  · simp [AKLT.Cert.H2.nextIncoming, windowArrival, hn, show 0 < n by omega]

theorem direction_code_inverse (d : Compass) : direction (directionCode d) = d := by
  cases d <;> rfl

theorem direction_code_lt (d : Compass) : directionCode d < 4 := by
  cases d <;> decide

theorem advance_code (x : Point) (d : Compass) :
    advance x (directionCode d) = x + d.step := by
  cases d <;> rfl

theorem snoc_witness_old {n : Nat} (w : DirectionWord n) (d : Compass) (i : Fin n) :
    witnessKappa (AKLT.Cert.H2.snoc w d) i.castSucc = witnessKappa w i := by
  classical
  have hin : wordIncoming kernelIncoming (AKLT.Cert.H2.snoc w d) i.castSucc =
      wordIncoming kernelIncoming w i := by
    unfold wordIncoming
    simp only [Fin.val_castSucc]
    split_ifs with hi
    · rfl
    · exact AKLT.Cert.H2.snoc_apply_lt w d _ (by omega)
  have hlive : liveOtherNeighbours (AKLT.Cert.H2.snoc w d) i.castSucc =
      liveOtherNeighbours w i := by
    unfold liveOtherNeighbours responseNeighbours
    simp only [Fin.val_castSucc, AKLT.Cert.H2.snoc_vertex _ w d i.val (by omega),
      AKLT.Cert.H2.snoc_vertex _ w d (i.val + 1) (by omega), hin]
    apply Finset.filter_congr
    intro z hz
    simp only [deadAt, Fin.val_castSucc,
      AKLT.Cert.H2.snoc_departure _ w d i.val (by omega)]
  simp only [witnessKappa, responsePairs, pairCoefficient, hlive,
    Fin.val_castSucc, AKLT.Cert.H2.snoc_vertex _ w d (i.val + 1) (by omega),
    AKLT.Cert.H2.snoc_old_straight]

theorem departures_represents {n : Nat} (w : DirectionWord n) (walk : Walk)
    (h : WalkRepresents kernelStart 2 w walk) (z : Point) :
    departures walk z = departureCount kernelStart w n z := by
  classical
  rw [departures, h.2.2.2.2.1]
  simp only [List.filter_map, List.map_reverse, List.filter_reverse, List.length_reverse,
    List.length_map, Function.comp_def, Bool.beq_eq_decide_eq]
  have hc := (List.nodup_finRange n).card_eq_countP
    (P := fun i : Fin n => wordVertex kernelStart w i.val = z)
  rw [List.toFinset_finRange, List.countP_eq_length_filter] at hc
  rw [← hc]
  unfold departureCount
  simp only [min_self]
  apply Finset.card_bij (fun i _ => i.val)
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, hi⟩
  · intro i hi j hj hij
    exact Fin.ext hij
  · intro j hj
    rcases Finset.mem_filter.mp hj with ⟨hj, hz⟩
    exact ⟨⟨j, Finset.mem_range.mp hj⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩, rfl⟩

theorem deadMaskAt_lt (walk : Walk) : deadMaskAt walk < 16 := by
  unfold deadMaskAt dirs
  dsimp only [List.foldl_cons, List.foldl_nil]
  split_ifs <;> omega

theorem deadMaskAt_mem (walk : Walk) (c : Compass) :
    c.step ∈ deadSet (deadMaskAt walk) ↔
      advance walk.pos (directionCode c) = kernelCentre ∨
        2 ≤ departures walk (advance walk.pos (directionCode c)) := by
  by_cases h0 : advance walk.pos 0 = (0,0) ∨ 2 ≤ departures walk (advance walk.pos 0) <;>
    by_cases h1 : advance walk.pos 1 = (0,0) ∨ 2 ≤ departures walk (advance walk.pos 1) <;>
    by_cases h2 : advance walk.pos 2 = (0,0) ∨ 2 ≤ departures walk (advance walk.pos 2) <;>
    by_cases h3 : advance walk.pos 3 = (0,0) ∨ 2 ≤ departures walk (advance walk.pos 3) <;>
    cases c <;>
    simp [deadMaskAt, dirs, h0, h1, h2, h3, kernelCentre, directionCode, deadSet,
      show (Finset.univ : Finset Compass) = {.east, .north, .west, .south} by decide,
      Compass.step, Nat.testBit] <;> decide +kernel


theorem deadMaskAt_image_mem {n : Nat} (w : DirectionWord n) (walk : Walk)
    (h : WalkRepresents kernelStart 2 w walk) (z : Point) (hz : z ∈ neighbours walk.pos) :
    z ∈ (deadSet (deadMaskAt walk)).image (fun y => y + walk.pos) ↔
      z = kernelCentre ∨ 2 ≤ departureCount kernelStart w n z := by
  classical
  rcases Finset.mem_image.mp hz with ⟨c, hc, rfl⟩
  have him : walk.pos + c.step ∈ (deadSet (deadMaskAt walk)).image (fun y => y + walk.pos) ↔
      c.step ∈ deadSet (deadMaskAt walk) := by
    constructor
    · rintro hz
      rcases Finset.mem_image.mp hz with ⟨y, hy, he⟩
      have he' : y = c.step := add_right_cancel (he.trans (add_comm _ _))
      simpa [he'] using hy
    · intro hc
      exact Finset.mem_image.mpr ⟨c.step, hc, add_comm _ _⟩
  rw [him, deadMaskAt_mem, advance_code, departures_represents w walk h]

theorem witness_last_reward {n : Nat} (w : DirectionWord n) (d : Compass)
    (walk : Walk) (h : WalkRepresents kernelStart 2 w walk) :
    witnessKappa (AKLT.Cert.H2.snoc w d) (Fin.last n) =
      relaxedReward (0,0) (AKLT.Cert.H2.nextIncoming kernelIncoming w) d
        (deadSet (deadMaskAt walk)) := by
  classical
  let a := AKLT.Cert.H2.nextIncoming kernelIncoming w
  let dead := (deadSet (deadMaskAt walk)).image (fun y => y + walk.pos)
  have hv : wordVertex kernelStart (AKLT.Cert.H2.snoc w d) n = walk.pos := by
    rw [AKLT.Cert.H2.snoc_vertex _ w d n le_rfl, ← h.2.1]
  have hvnext : wordVertex kernelStart (AKLT.Cert.H2.snoc w d) (n + 1) =
      walk.pos + d.step := by
    rw [AKLT.Cert.H2.vertex_succ _ _ n (by omega), hv]
    rw [show (⟨n, by omega⟩ : Fin (n+1)) = Fin.last n from Fin.ext rfl,
      AKLT.Cert.H2.snoc_last]
  have hlive : liveOtherView (AKLT.Cert.H2.snoc w d) (Fin.last n) =
      localLive walk.pos a d dead := by
    ext z
    simp only [liveOtherView, responseNeighbours, Fin.val_last, hv, hvnext,
      snoc_incoming_last, localLive, Finset.mem_filter, Finset.mem_erase,
      Finset.mem_sdiff, AKLT.Cert.H2.snoc_departure _ w d n le_rfl]
    by_cases hz : z ∈ neighbours walk.pos
    · rw [show z ∈ dead ↔ z = kernelCentre ∨ 2 ≤ departureCount kernelStart w n z from
        deadMaskAt_image_mem w walk h z hz]
      simp only [not_or, not_le]
      tauto
    · simp [hz]
  rw [witnessKappa_view]
  unfold kappaView
  rw [hlive]
  simp only [Fin.val_last, hvnext, wordStraight, AKLT.Cert.H2.snoc_last, snoc_incoming_last]
  change responseSum (walk.pos + d.step) a d (localLive walk.pos a d dead) = _
  rw [← relaxedReward_eq_responseSum]
  have ht := relaxedReward_translate (0,0) walk.pos a d (deadSet (deadMaskAt walk))
  have hz : ((0,0) : Plane) + walk.pos = walk.pos := zero_add _
  rw [hz] at ht
  exact ht

#print axioms relaxedReward_translate
#print axioms snoc_incoming_last
#print axioms walk_incoming_code
#print axioms direction_code_inverse
#print axioms direction_code_lt
#print axioms advance_code
#print axioms snoc_witness_old
#print axioms departures_represents
#print axioms deadMaskAt_lt
#print axioms deadMaskAt_mem
#print axioms deadMaskAt_image_mem
#print axioms witness_last_reward

end AKLT.W.H3C031
