module
public import AKLT.Blueprint.Rec.NodesWalk
public import AKLT.Blueprint.Mom.Assembly
public import AKLT.W.REC003.Main
public import AKLT.W.REC014.Main

@[expose] public section
set_option backward.privateInPublic true
set_option backward.proofsInPublic true

noncomputable section
open scoped BigOperators
open AKLT.Defs

namespace AKLT.W.REC044

theorem icoVector_normSq_one : ∀ j : IcoLetter, normSq (icoVector j) = 1 := by
  have hs5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hphi : goldenRatio ^ 2 = goldenRatio + 1 := by
    unfold goldenRatio
    nlinarith [hs5]
  have hr2 : icoRadius ^ 2 = goldenRatio + 2 := by
    unfold icoRadius
    exact Real.sq_sqrt (by unfold goldenRatio; positivity)
  have hrpos : 0 < icoRadius := by
    unfold icoRadius
    apply Real.sqrt_pos.2
    unfold goldenRatio
    positivity
  intro j
  rcases j with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [icoVector, signValue, normSq, dot, Fin.sum_univ_succ] <;>
    field_simp [ne_of_gt hrpos] <;> nlinarith [hphi, hr2]

theorem dSite_normSq : siteFunctional .D normSq = 3 / 5 := by
  have hm : moment normSq = 1 := by
    unfold moment
    simp [icoVector_normSq_one, IcoLetter, Fintype.card_prod]
  rw [AKLT.Blueprint.Mom.siteLawDecomposition.2, hm]
  norm_num [normSq, dot]

theorem dSite_mass : siteFunctional .D (fun _ => 1) = 1 := by
  rw [AKLT.Blueprint.Mom.siteLawDecomposition.2,
    AKLT.Blueprint.Mom.momentConstant]
  norm_num

theorem traceStep_present_mono {G : Finset Plane} (D : Network G) (a b x y : Plane)
    (h : (traceStep D a b).Present x y) : D.Present x y := by
  have hactive : (traceStep D a b).active ⊆ D.active := by
    intro z hz
    simp only [Network.active, Finset.mem_filter] at hz ⊢
    rcases hz with ⟨hzG, hzS⟩
    refine ⟨hzG, ?_⟩
    by_cases hza : z = a
    · subst z
      cases hs : D.status a <;> simp [traceStep, hs] at hzS ⊢
    · simpa [traceStep, hza] using hzS
  have hkept : ∀ z, (traceStep D a b).kept z ⊆ D.kept z := by
    intro z
    by_cases hza : z = a
    · subst z
      simp [traceStep, Finset.erase_subset]
    · by_cases hzb : z = b
      · subst z
        simp [traceStep, hza, Finset.erase_subset]
      · simp [traceStep, hza, hzb]
  rcases h with ⟨hx, hy, hadj, hyx, hxy⟩
  exact ⟨hactive hx, hactive hy, hadj, hkept x hyx, hkept y hxy⟩

theorem traceNetwork_present_mono {G : Finset Plane} (D : Network G) (l : List Plane)
    {x y : Plane} (h : (traceNetwork D l).Present x y) : D.Present x y := by
  induction l generalizing D with
  | nil => simpa [traceNetwork] using h
  | cons a l ih =>
    cases l with
    | nil => simpa [traceNetwork] using h
    | cons b rest =>
      apply traceStep_present_mono
      exact ih (D := traceStep D a b) (by simpa [traceNetwork] using h)

theorem traceStep_no_traced_bond {G : Finset Plane} (D : Network G) (a b : Plane) :
    ¬ (traceStep D a b).Present a b ∧ ¬ (traceStep D a b).Present b a := by
  constructor
  · intro h
    rcases h with ⟨_, _, _, hba, _⟩
    simp [traceStep] at hba
  · intro h
    rcases h with ⟨_, _, _, _, hab⟩
    simp [traceStep] at hab

theorem traceNetwork_no_traced_bond {G : Finset Plane} (D : Network G)
    (pre : List Plane) (a b : Plane) (suf : List Plane) :
    ¬ (traceNetwork D (pre ++ a :: b :: suf)).Present a b ∧
      ¬ (traceNetwork D (pre ++ a :: b :: suf)).Present b a := by
  induction pre generalizing D with
  | nil =>
      constructor
      · intro h
        have h' : (traceStep D a b).Present a b :=
          traceNetwork_present_mono (traceStep D a b) (b :: suf) (by simpa [traceNetwork] using h)
        exact (traceStep_no_traced_bond D a b).1 h'
      · intro h
        have h' : (traceStep D a b).Present b a :=
          traceNetwork_present_mono (traceStep D a b) (b :: suf) (by simpa [traceNetwork] using h)
        exact (traceStep_no_traced_bond D a b).2 h'
  | cons c pre ih =>
      cases pre with
      | nil =>
          simpa only [List.cons_append, List.nil_append, traceNetwork] using
            (ih (D := traceStep D c a))
      | cons d pre =>
          simpa only [List.cons_append, traceNetwork] using
            (ih (D := traceStep D c d))


theorem traceNetwork_status_of_not_mem_dropLast {G : Finset Plane} (D : Network G)
    (l : List Plane) (x : Plane) (h : x ∉ l.dropLast) :
    (traceNetwork D l).status x = D.status x := by
  induction l generalizing D with
  | nil => simp [traceNetwork]
  | cons a l ih =>
    cases l with
    | nil => simp [traceNetwork]
    | cons b rest =>
      have hp := h
      simp only [List.dropLast_cons_cons, List.mem_cons, not_or] at hp
      rcases hp with ⟨hxa, hrest⟩
      simp only [traceNetwork]
      rw [ih (D := traceStep D a b) hrest]
      simp [traceStep, hxa]

theorem wordVertex_mem_of_mem_dropLast {n : ℕ} (u : Plane) (w : DirectionWord n)
    {x : Plane} (h : x ∈ (wordVertices u w).dropLast) :
    ∃ j < n, wordVertex u w j = x := by
  have heq : (wordVertices u w).dropLast =
      (List.range n).map (wordVertex u w) := by
    unfold wordVertices
    rw [show n + 1 = n.succ by omega, List.range_succ, List.map_append,
      List.map_singleton, List.dropLast_concat]
  rw [heq] at h
  simp only [List.mem_map, List.mem_range] at h
  rcases h with ⟨j, hj, hval⟩
  exact ⟨j, hj, hval⟩

theorem wordVertices_split_terminal {n : ℕ} (u v : Plane) (w : DirectionWord n)
    (hn : 0 < n) (hend : wordVertex u w n = v) :
    wordVertices u w =
      (List.range (n - 1)).map (wordVertex u w) ++ [wordVertex u w (n - 1), v] := by
  have hlen : n + 1 = (n - 1).succ.succ := by omega
  unfold wordVertices
  rw [hlen, List.range_succ, List.range_succ, List.map_append, List.map_append]
  simp [hend, show n - 1 + 1 = n by omega]

theorem network_present_symm {G : Finset Plane} (D : Network G) {x y : Plane}
    (h : D.Present x y) : D.Present y x := by
  rcases h with ⟨hx, hy, hadj, hxy, hyx⟩
  have hdist : latticeDist y x = 1 := by
    dsimp [Adjacent, latticeDist] at hadj ⊢
    omega
  exact ⟨hy, hx, hdist, hyx, hxy⟩

theorem adjacent_mem_neighbours {x y : Plane} (h : Adjacent x y) : y ∈ neighbours x := by
  have hsum : (x.1 - y.1).natAbs + (x.2 - y.2).natAbs = 1 := h
  have hsplit : ((x.1 - y.1).natAbs = 1 ∧ (x.2 - y.2).natAbs = 0) ∨
      ((x.1 - y.1).natAbs = 0 ∧ (x.2 - y.2).natAbs = 1) := by omega
  have hdir : y = x + Compass.east.step ∨ y = x + Compass.north.step ∨
      y = x + Compass.west.step ∨ y = x + Compass.south.step := by
    rcases hsplit with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hcoord : x.1 - y.1 = 1 ∨ x.1 - y.1 = -1 := by
        simpa using (Int.natAbs_eq_iff.mp h1)
      have hcoord2 : x.2 - y.2 = 0 := by
        rcases Int.natAbs_eq_iff.mp h2 with h' | h' <;> norm_num at h' ⊢ <;> omega
      rcases hcoord with h' | h'
      · right; right; left
        ext <;> simp [Compass.step] <;> omega
      · left
        ext <;> simp [Compass.step] <;> omega
    · have hcoord : x.2 - y.2 = 1 ∨ x.2 - y.2 = -1 := by
        simpa using (Int.natAbs_eq_iff.mp h2)
      have hcoord1 : x.1 - y.1 = 0 := by
        rcases Int.natAbs_eq_iff.mp h1 with h' | h' <;> norm_num at h' ⊢ <;> omega
      rcases hcoord with h' | h'
      · right; right; right
        apply Prod.ext
        · simp [Compass.step]; omega
        · simp [Compass.step]; omega
      · right; left
        apply Prod.ext
        · simp [Compass.step]; omega
        · simp [Compass.step]; omega
  rcases hdir with he | hn | hw | hs
  · rw [he]
    simp [neighbours]
  · rw [hn]
    simp [neighbours]
  · rw [hw]
    simp [neighbours]
  · rw [hs]
    simp [neighbours]

theorem originalLeg_root_is_protected {G : Finset Plane} {x z : Plane}
    (hx : x ∈ G) (he : (x, z) ∈ originalLegs G) : x ∈ protectedSites G := by
  have hparts := he
  simp only [originalLegs, Finset.mem_biUnion, Finset.mem_image,
    Finset.mem_sdiff] at hparts
  rcases hparts with ⟨x', hx'G, z', ⟨hzNbr, hzOut⟩, heq⟩
  have hxEq : x' = x := by simpa using congrArg Prod.fst heq
  have hzEq : z' = z := by simpa using congrArg Prod.snd heq
  subst x'
  subst z'
  have hdist : latticeDist x z = 1 := by
    rcases Finset.mem_image.mp hzNbr with ⟨d, _, hd⟩
    subst z
    cases d <;> simp [latticeDist, Compass.step]
  have hbd : boundaryDepth G x ≤ 1 := by
    unfold boundaryDepth setDistance
    calc
      (⨅ y : {y : Plane // y ∉ G}, (latticeDist x y.val : ℕ∞)) ≤
          (latticeDist x z : ℕ∞) :=
        iInf_le (fun y : {y : Plane // y ∉ G} => (latticeDist x y.val : ℕ∞))
          ⟨z, hzOut⟩
      _ = 1 := by simp [hdist]
  have hbd2 : boundaryDepth G x ≤ 2 := le_trans hbd (by norm_num)
  simpa [protectedSites, hx] using hbd2

/-- Residual trace fact: a first-hit target has not been a departure site. -/
def Residual_FirstHitStatus : Prop :=
  ∀ G : Finset Plane, ∀ D : Network G, ∀ u v : Plane,
    D.AdmissibleStart u → AdmissibleTarget D v → u ≠ v →
    ∀ n : ℕ, ∀ w : DirectionWord n,
      StoppedNetworkTrail D u (insert v (protectedSites G)) w →
      wordVertex u w n = v →
      (traceNetwork D (wordVertices u w)).status v = D.status v

theorem firstHitStatus : Residual_FirstHitStatus := by
  intro G D u v hstart htarget hne n w htrail hend
  rcases htrail with ⟨_, _, hbefore, _⟩
  have hnot : v ∉ (wordVertices u w).dropLast := by
    intro hv
    obtain ⟨j, hj, hjv⟩ := wordVertex_mem_of_mem_dropLast u w hv
    have hvT : wordVertex u w j ∈ insert v (protectedSites G) := by
      rw [hjv]
      simp
    exact (hbefore j hj).1 hvT
  exact traceNetwork_status_of_not_mem_dropLast D (wordVertices u w) v hnot

/-- Residual trace fact: after the arrival at a D target, that site has no
remaining bond or original pin leg. -/
def Residual_FirstHitIsolation : Prop :=
  ∀ G : Finset Plane, ∀ D : Network G, D.Auxiliary → ∀ u v : Plane,
    D.AdmissibleStart u → AdmissibleTarget D v → u ≠ v →
    ∀ n : ℕ, ∀ w : DirectionWord n,
      StoppedNetworkTrail D u (insert v (protectedSites G)) w →
      wordVertex u w n = v → D.status v = .D →
      (traceNetwork D (wordVertices u w)).presentNeighbours v = ∅ ∧
      ∀ e ∈ originalLegs G, e.1 ≠ v

theorem firstHit_D_no_neighbours :
    ∀ G : Finset Plane, ∀ D : Network G,
      D.Auxiliary → ∀ u v : Plane, D.AdmissibleStart u → AdmissibleTarget D v →
      u ≠ v → ∀ n : ℕ, ∀ w : DirectionWord n,
      StoppedNetworkTrail D u (insert v (protectedSites G)) w →
      wordVertex u w n = v → D.status v = .D →
      (traceNetwork D (wordVertices u w)).presentNeighbours v = ∅ := by
  intro G D hD u v hstart htarget hne n w htrail hend hDv
  have hn : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := by omega
    subst n
    have huv : u = v := by simpa [wordVertex] using hend
    exact hne huv
  rcases htarget.2 with hU | ⟨hDstatus, hdegree⟩
  · have : False := by rw [hU.1] at hDv; cases hDv
    exact this.elim
  · rcases htrail with ⟨_, hpresent, _, _⟩
    let p := wordVertex u w (n - 1)
    have hArrival : D.Present p v := by
      have h := hpresent ⟨n - 1, by omega⟩
      simpa [p, show n - 1 + 1 = n by omega, hend] using h
    have hArrivalV : D.Present v p := network_present_symm D hArrival
    have hpNbr : p ∈ D.presentNeighbours v := by
      exact Finset.mem_filter.mpr ⟨adjacent_mem_neighbours hArrivalV.2.2.1, hArrivalV⟩
    have hsplit := wordVertices_split_terminal u v w hn hend
    have hNoArrival : ¬ (traceNetwork D (wordVertices u w)).Present v p := by
      rw [hsplit]
      simpa [p] using
        (traceNetwork_no_traced_bond D ((List.range (n - 1)).map (wordVertex u w)) p v []).2
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro z hz
    have hz' := Finset.mem_filter.mp hz
    have hzInitial : D.Present v z := traceNetwork_present_mono D (wordVertices u w) hz'.2
    have hzNbr : z ∈ D.presentNeighbours v :=
      Finset.mem_filter.mpr ⟨adjacent_mem_neighbours hzInitial.2.2.1, hzInitial⟩
    have hsame := (Finset.card_le_one.mp hdegree) z hzNbr p hpNbr
    subst z
    exact hNoArrival hz'.2

theorem firstHit_D_no_original_legs :
    ∀ G : Finset Plane, ∀ D : Network G, D.Auxiliary → ∀ u v : Plane,
      D.AdmissibleStart u → AdmissibleTarget D v → u ≠ v →
      ∀ n : ℕ, ∀ w : DirectionWord n,
      StoppedNetworkTrail D u (insert v (protectedSites G)) w →
      wordVertex u w n = v → D.status v = .D →
      ∀ e ∈ originalLegs G, e.1 ≠ v := by
  intro G D hD u v hstart htarget hne n w htrail hend hDv e he hroot
  have hvG : v ∈ G := by
    have hact : v ∈ G ∧ D.status v ≠ .X := by
      simpa [Network.active] using htarget.1
    exact hact.1
  rcases e with ⟨x, z⟩
  dsimp at hroot
  subst x
  have hp : v ∈ protectedSites G :=
    originalLeg_root_is_protected hvG (by simpa using he)
  have hU := hD.2 v hp
  rw [hDv] at hU
  cases hU

theorem firstHitIsolation : Residual_FirstHitIsolation := by
  intro G D hD u v hstart htarget hne n w htrail hend hDv
  exact ⟨firstHit_D_no_neighbours G D hD u v hstart htarget hne n w
      htrail hend hDv,
    firstHit_D_no_original_legs G D hD u v hstart htarget hne n w htrail hend hDv⟩

/-- Residual finite-sum fact: integrate a decoupled terminal site after proving
the full partition sum has a positive normalizer. -/
def Residual_IsolatedSiteLaw : Prop :=
  ∀ G : Finset Plane, ∀ E : Network G, ∀ τ : PinAssignment G,
    ∀ b : Bool, ∀ v : Plane, v ∈ E.active →
    (E.status v = .U ∨ E.status v = .D) →
    (E.status v = .D → E.presentNeighbours v = ∅) →
    (E.status v = .D → ∀ e ∈ originalLegs G, e.1 ≠ v) →
    0 < E.partition τ b (fun _ => 1) →
    E.expectation τ b (fun a => normSq (a v)) = AKLT.Blueprint.Rec.targetFactor E v

/-- Residual positivity fact for the traced network. -/
def Residual_TracePartitionPositive : Prop :=
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G,
    D.Auxiliary → ∀ u v : Plane, D.AdmissibleStart u →
    AdmissibleTarget D v → u ≠ v → ∀ n : ℕ, ∀ w : DirectionWord n,
    StoppedNetworkTrail D u (insert v (protectedSites G)) w →
    wordVertex u w n = v → ∀ b : Bool,
      0 < (traceNetwork D (wordVertices u w)).partition τ b (fun _ => 1)

/-- The requested theorem follows from first-hit trace invariants, the local
isolated-site sum, and positivity of its remaining partition. -/
theorem main_of_residuals (hStatus : Residual_FirstHitStatus)
    (hIsolation : Residual_FirstHitIsolation) (hSite : Residual_IsolatedSiteLaw)
    (hPositive : Residual_TracePartitionPositive) :
    AKLT.Blueprint.Rec.PairTerminalFactorStatement := by
  intro G τ D hD u v hstart htarget hne n w htrail hend b
  let E := traceNetwork D (wordVertices u w)
  have hs := hStatus G D u v hstart htarget hne n w htrail hend
  have hstatus : E.status v = D.status v := hs
  have htargetStatus : D.status v = .U ∨ D.status v = .D := htarget.2.elim
    (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have hvActiveG : v ∈ G ∧ D.status v ≠ .X := by
    simpa [Network.active] using htarget.1
  have hvG : v ∈ G := hvActiveG.1
  have hactive : v ∈ E.active := by
    simp only [Network.active, Finset.mem_filter]
    refine ⟨hvG, ?_⟩
    rw [hstatus]
    rcases htargetStatus with hU | hD'
    · rw [hU]
      decide
    · rw [hD']
      decide
  have hDterminal : D.status v = .D →
      E.presentNeighbours v = ∅ ∧ ∀ e ∈ originalLegs G, e.1 ≠ v := by
    intro hDv
    exact hIsolation G D hD u v hstart htarget hne n w htrail hend hDv
  have hEmpty : E.status v = .D → E.presentNeighbours v = ∅ := by
    intro hEv
    have hDv : D.status v = .D := by rw [← hstatus]; exact hEv
    exact (hDterminal hDv).1
  have hLegs : E.status v = .D → ∀ e ∈ originalLegs G, e.1 ≠ v := by
    intro hEv
    have hDv : D.status v = .D := by rw [← hstatus]; exact hEv
    exact (hDterminal hDv).2
  have hpos := hPositive G τ D hD u v hstart htarget hne n w htrail hend b
  have hlaw := hSite G E τ b v hactive (by rw [hstatus]; exact htargetStatus)
    hEmpty hLegs hpos
  change E.expectation τ b (fun a => normSq (a v)) = AKLT.Blueprint.Rec.targetFactor D v
  calc
    E.expectation τ b (fun a => normSq (a v)) = AKLT.Blueprint.Rec.targetFactor E v := hlaw
    _ = AKLT.Blueprint.Rec.targetFactor D v := by
      simp [AKLT.Blueprint.Rec.targetFactor, hstatus]

theorem main_of_core_residuals (hSite : Residual_IsolatedSiteLaw)
    (hPositive : Residual_TracePartitionPositive) :
    AKLT.Blueprint.Rec.PairTerminalFactorStatement :=
  main_of_residuals firstHitStatus firstHitIsolation hSite hPositive

/-- The zero atom has weight zero at a U site, so inserting its squared
norm leaves every one-site integral unchanged. -/
theorem uSite_normSq_mul (f : Vec3 → ℝ) :
    siteFunctional .U (fun z => normSq z * f z) = siteFunctional .U f := by
  simp [siteFunctional, Fintype.sum_option, spinWeight, spinVector,
    icoVector_normSq_one]

/-- A U spin has squared norm one under the full network law, including
arbitrary surviving bond and pin factors. -/
theorem partition_normSq_U {G : Finset Plane} (E : Network G)
    (τ : PinAssignment G) (b : Bool) (v : Plane) (hv : v ∈ E.active)
    (hU : E.status v = .U) :
    E.partition τ b (fun a => normSq (a v)) = E.partition τ b (fun _ => 1) := by
  open AKLT.W.REC003 in
  rw [partition_repr, partition_repr,
    spinIntegral_site E.active v hv, spinIntegral_site E.active v hv]
  unfold spinIntegral
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  simp only [Function.update_self, hU, one_mul]
  exact uSite_normSq_mul _

/-- All interaction factors are independent of an isolated site with no
original pin legs. -/
theorem interaction_update_isolated {G : Finset Plane} (E : Network G)
    (τ : PinAssignment G) (b : Bool) (v : Plane)
    (hiso : E.presentNeighbours v = ∅)
    (hlegs : ∀ e ∈ originalLegs G, e.1 ≠ v)
    (m : Plane → Vec3) (z : Vec3) :
    AKLT.W.REC003.interaction E τ b (Function.update m v z) =
      AKLT.W.REC003.interaction E τ b m := by
  open AKLT.W.REC003 in
  unfold interaction bondProduct legProduct
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    have hp := (Finset.mem_filter.mp he).2
    have hn : e.1 ≠ v ∧ e.2 ≠ v := by
      constructor
      · intro h
        have hmem := (mem_presentNeighbours E e.1 e.2).2 hp
        rw [h, hiso] at hmem
        simp at hmem
      · intro h
        have hmem := (mem_presentNeighbours E e.2 e.1).2 (present_symm hp)
        rw [h, hiso] at hmem
        simp at hmem
    rw [Function.update_of_ne hn.1, Function.update_of_ne hn.2]
  · apply Finset.prod_congr rfl
    intro e _
    rw [Function.update_of_ne (hlegs e.val e.property)]

/-- Fubini at an isolated D site gives its second moment times the
unnormalized partition; no division is used in this identity. -/
theorem partition_normSq_D {G : Finset Plane} (E : Network G)
    (τ : PinAssignment G) (b : Bool) (v : Plane) (hv : v ∈ E.active)
    (hD : E.status v = .D) (hiso : E.presentNeighbours v = ∅)
    (hlegs : ∀ e ∈ originalLegs G, e.1 ≠ v) :
    E.partition τ b (fun a => normSq (a v)) =
      (3 / 5 : ℝ) * E.partition τ b (fun _ => 1) := by
  open AKLT.W.REC003 in
  rw [partition_repr, partition_repr,
    spinIntegral_site E.active v hv, spinIntegral_site E.active v hv]
  unfold spinIntegral
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Function.update_self, hD, one_mul]
  simp_rw [interaction_update_isolated E τ b v hiso hlegs]
  rw [site_mul_const, dSite_normSq]
  have hc (c : ℝ) : siteFunctional .D (fun _ => c) = c := by
    have h := site_mul_const .D (fun _ => 1) c
    simpa [dSite_mass] using h
  rw [hc]
  ring

/-- Both local terminal cases, now with the finite-sum residual discharged. -/
theorem isolatedSiteLaw : Residual_IsolatedSiteLaw := by
  intro G E τ b v hv hs hiso hlegs hpos
  unfold Network.expectation
  rcases hs with hU | hD
  · rw [partition_normSq_U E τ b v hv hU, div_self (ne_of_gt hpos)]
    simp [AKLT.Blueprint.Rec.targetFactor, hU]
  · rw [partition_normSq_D E τ b v hv hD (hiso hD) (hlegs hD),
      mul_div_cancel_right₀ _ (ne_of_gt hpos)]
    simp [AKLT.Blueprint.Rec.targetFactor, hD]

/-- The existing positivity theorem applies to every traced network. -/
theorem tracePartitionPositive : Residual_TracePartitionPositive := by
  intro G τ D _ u v _ _ _ n w _ _ b
  exact AKLT.W.REC014.partition_positive (traceNetwork D (wordVertices u w)) τ b

/-- At the first target hit, a U target contributes one and an isolated D
target contributes three fifths, for either choice of the pins. -/
theorem main : AKLT.Blueprint.Rec.PairTerminalFactorStatement :=
  main_of_core_residuals isolatedSiteLaw tracePartitionPositive

end AKLT.W.REC044
