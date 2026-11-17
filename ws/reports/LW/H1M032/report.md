STATUS: PROVED

Files:

- [Main.lean](/home/ubuntu/aklt/wt/LW_H1M032/AKLT/W/H1M032/Main.lean): requested unconditional theorem.
- [Local.lean](/home/ubuntu/aklt/wt/LW_H1M032/AKLT/W/H1M032/Local.lean): explicit local vectors and their induced matrices.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_H1M032/AKLT/W/H1M032/Geometry.lean): distinct slot encodings and the disjoint partition of active tokens.
- [Tensor.lean](/home/ubuntu/aklt/wt/LW_H1M032/AKLT/W/H1M032/Tensor.lean): token coordinate formula, tensor product action, and span induction.
- [Sector.lean](/home/ubuntu/aklt/wt/LW_H1M032/AKLT/W/H1M032/Sector.lean): identification with the frozen sector vectors and arbitrary-matrix invariance.
- [Audit.lean](/home/ubuntu/aklt/wt/LW_H1M032/AKLT/W/H1M032/Audit.lean): exact-type check, exported signatures, and axiom audit of every exported theorem.
- [main-build.log](/home/ubuntu/aklt/reports/LW/H1M032/main-build.log), [audit-build.log](/home/ubuntu/aklt/reports/LW/H1M032/audit-build.log): verification output.

The required declaration is:

```lean
theorem AKLT.W.H1M032.main : AKLT.Blueprint.H1.SectorSpinStableStatement
```

Proof: for an arbitrary complex 2×2 matrix A, explicitly compute its action on a single and the sum of its two token actions on each unnormalized pair vector. The symmetric pair action is a three-dimensional matrix; the exterior pair action is multiplication by trace(A). A small `decide +kernel` proof checks that all sixteen potential group slots have distinct encodings. The actual group slots form a disjoint cover of the active tokens, including when the pattern is not covered. Factor the spectator coordinates out of each local sum, express the result through basis assignments updated in one group, and extend to the complex span by `Submodule.span_induction`. Specialize to the three matrices in the frozen spin definitions and multiply by 1/2.

The stronger exported result `exchangeSpace_matrix_stable` proves invariance under the sum of identical arbitrary one-spin matrices. No other blueprint leaf is used as a proved lemma. The earlier residual-only `Main.lean` is replaced; there are no residual assumptions.

Build commands and timings (PATH includes `$HOME/.elan/bin`):

- `lake build AKLT.W.H1M032.Main` — passed. Main module compilation: 6.2 s; final timed incremental build: 8.62 s wall time.
- `lake build AKLT.W.H1M032.Audit` — passed, 10.56 s wall time; Audit module compilation: 5.4 s. This checks `(AKLT.W.H1M032.main : AKLT.Blueprint.H1.SectorSpinStableStatement)` and prints axioms for every exported theorem.
- Source scan found no forbidden proof constructs. Only task-directory Lean files and task-report artifacts were written.

Open issues: none.

Exported declarations and their statements (Lean `#check @...` output):

```text
AKLT.W.H1M032.main : AKLT.Blueprint.H1.SectorSpinStableStatement

AKLT.W.H1M032.localDim : Bool → (ext : Prop) → [Decidable ext] → ℕ

AKLT.W.H1M032.localVector : Bool → (ext : Prop) → [Decidable ext] → ℕ → Fin 2 → Fin 2 → ℤ

AKLT.W.H1M032.localMatrix : Bool → (ext : Prop) → [Decidable ext] → Matrix (Fin 2) (Fin 2) ℂ → ℕ → ℕ → ℂ

AKLT.W.H1M032.local_action : ∀ (pair : Bool) (ext : Prop) [inst : Decidable ext] (A : Matrix (Fin 2) (Fin 2) ℂ),
  ∀ b < AKLT.W.H1M032.localDim pair ext,
    ∀ (i j : Fin 2),
      (∑ k, A i k * ↑(AKLT.W.H1M032.localVector pair ext b k j) +
          if pair = true then ∑ k, A j k * ↑(AKLT.W.H1M032.localVector pair ext b i k) else 0) =
        ∑ c ∈ Finset.range (AKLT.W.H1M032.localDim pair ext),
          AKLT.W.H1M032.localMatrix pair ext A c b * ↑(AKLT.W.H1M032.localVector pair ext c i j)

AKLT.W.H1M032.raw_slot_injective : ∀ (x y : ↥(AKLT.Defs.templateCorners ∪ AKLT.Defs.templateTips)) (a b : Fin 2),
  ((if a = 0 then AKLT.Defs.groupLeader ↑x else AKLT.Defs.groupSecond ↑x) =
      if b = 0 then AKLT.Defs.groupLeader ↑y else AKLT.Defs.groupSecond ↑y) →
    x = y ∧ a = b

AKLT.W.H1M032.boundaryGroup : (π : AKLT.Defs.PatternData) →
  ↥(AKLT.Defs.reductionGroups π) → ↥(AKLT.Defs.templateCorners ∪ AKLT.Defs.templateTips)

AKLT.W.H1M032.leader_second_ne : ∀ (π : AKLT.Defs.PatternData) (x : ↥(AKLT.Defs.reductionGroups π)),
  AKLT.Defs.groupLeader ↑x ≠ AKLT.Defs.groupSecond ↑x

AKLT.W.H1M032.different_group_slots : ∀ (π : AKLT.Defs.PatternData) (x y : ↥(AKLT.Defs.reductionGroups π)),
  x ≠ y →
    AKLT.Defs.groupLeader ↑x ≠ AKLT.Defs.groupLeader ↑y ∧
      AKLT.Defs.groupLeader ↑x ≠ AKLT.Defs.groupSecond ↑y ∧
        AKLT.Defs.groupSecond ↑x ≠ AKLT.Defs.groupLeader ↑y ∧ AKLT.Defs.groupSecond ↑x ≠ AKLT.Defs.groupSecond ↑y

AKLT.W.H1M032.secondOrLeader : (π : AKLT.Defs.PatternData) →
  (r : AKLT.Defs.Representation) → ↥(AKLT.Defs.reductionGroups π) → ↥(AKLT.Defs.reductionVectors π r)

AKLT.W.H1M032.groupSlots : (π : AKLT.Defs.PatternData) →
  (r : AKLT.Defs.Representation) → ↥(AKLT.Defs.reductionGroups π) → Finset ↥(AKLT.Defs.reductionVectors π r)

AKLT.W.H1M032.pair_tokens_ne : ∀ (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  (x : ↥(AKLT.Defs.reductionGroups π)),
  AKLT.Defs.groupIsPair π r ↑x = true → AKLT.Defs.leaderToken π r x ≠ AKLT.W.H1M032.secondOrLeader π r x

AKLT.W.H1M032.groupSlots_cover : ∀ (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation),
  Finset.univ.biUnion (AKLT.W.H1M032.groupSlots π r) = Finset.univ

AKLT.W.H1M032.mem_groupSlots_val : ∀ (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  (x : ↥(AKLT.Defs.reductionGroups π)),
  ∀ j ∈ AKLT.W.H1M032.groupSlots π r x, ↑j = AKLT.Defs.groupLeader ↑x ∨ ↑j = AKLT.Defs.groupSecond ↑x

AKLT.W.H1M032.groupSlots_disjoint : ∀ (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation),
  (↑Finset.univ).PairwiseDisjoint (AKLT.W.H1M032.groupSlots π r)

AKLT.W.H1M032.leader_mem_groupSlots : ∀ (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  (x : ↥(AKLT.Defs.reductionGroups π)), AKLT.Defs.leaderToken π r x ∈ AKLT.W.H1M032.groupSlots π r x

AKLT.W.H1M032.second_mem_groupSlots : ∀ (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  (x : ↥(AKLT.Defs.reductionGroups π)), AKLT.W.H1M032.secondOrLeader π r x ∈ AKLT.W.H1M032.groupSlots π r x

AKLT.W.H1M032.other_group_tokens_ne : ∀ (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  (x y : ↥(AKLT.Defs.reductionGroups π)),
  y ≠ x → ∀ j ∈ AKLT.W.H1M032.groupSlots π r x, AKLT.Defs.leaderToken π r y ≠ j ∧ AKLT.W.H1M032.secondOrLeader π r y ≠ j

AKLT.W.H1M032.token_apply : ∀ (J : Finset (Fin 20)) (j : ↥J) (A : Matrix (Fin 2) (Fin 2) ℂ)
  (v : EuclideanSpace ℂ (↥J → Fin 2)) (σ : ↥J → Fin 2),
  ((Matrix.toEuclideanLin (AKLT.Defs.tokenMatrix J j A)) v).ofLp σ = ∑ k, A (σ j) k * v.ofLp (Function.update σ j k)

@AKLT.W.H1M032.tensorGenerator : {G : Type} →
  [Fintype G] →
    {B : G → Type} →
      {J : Finset (Fin 20)} → ((x : G) → B x → (↥J → Fin 2) → ℂ) → ((x : G) → B x) → EuclideanSpace ℂ (↥J → Fin 2)

@AKLT.W.H1M032.tensorGenerator_update : ∀ {G : Type} [inst : Fintype G] [inst_1 : DecidableEq G] {B : G → Type}
  {J : Finset (Fin 20)} (v : (x : G) → B x → (↥J → Fin 2) → ℂ) (b : (x : G) → B x) (x : G) (c : B x) (σ : ↥J → Fin 2),
  (AKLT.W.H1M032.tensorGenerator v (Function.update b x c)).ofLp σ = (∏ y ∈ Finset.univ.erase x, v y (b y) σ) * v x c σ

@AKLT.W.H1M032.tensorGenerator_config : ∀ {G : Type} [inst : Fintype G] [inst_1 : DecidableEq G] {B : G → Type}
  {J : Finset (Fin 20)} (v : (x : G) → B x → (↥J → Fin 2) → ℂ) (b : (x : G) → B x) (x : G) (j : ↥J) (a : Fin 2)
  (σ : ↥J → Fin 2),
  (∀ (y : G), y ≠ x → v y (b y) (Function.update σ j a) = v y (b y) σ) →
    (AKLT.W.H1M032.tensorGenerator v b).ofLp (Function.update σ j a) =
      (∏ y ∈ Finset.univ.erase x, v y (b y) σ) * v x (b x) (Function.update σ j a)

@AKLT.W.H1M032.product_group_action : ∀ {G : Type} [inst : Fintype G] [inst_1 : DecidableEq G] {B : G → Type}
  {J : Finset (Fin 20)} [inst_2 : (x : G) → Fintype (B x)] (slots : G → Finset ↥J)
  (v : (x : G) → B x → (↥J → Fin 2) → ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) (b : (x : G) → B x) (x : G) (C : B x → ℂ),
  (∀ j ∈ slots x, ∀ (y : G), y ≠ x → ∀ (a : Fin 2) (σ : ↥J → Fin 2), v y (b y) (Function.update σ j a) = v y (b y) σ) →
    (∀ (σ : ↥J → Fin 2), ∑ j ∈ slots x, ∑ a, A (σ j) a * v x (b x) (Function.update σ j a) = ∑ c, C c * v x c σ) →
      (∑ j ∈ slots x, Matrix.toEuclideanLin (AKLT.Defs.tokenMatrix J j A)) (AKLT.W.H1M032.tensorGenerator v b) =
        ∑ c, C c • AKLT.W.H1M032.tensorGenerator v (Function.update b x c)

@AKLT.W.H1M032.sum_token_stable : ∀ {G : Type} [inst : Fintype G] [DecidableEq G] {B : G → Type} {J : Finset (Fin 20)}
  [inst_2 : (x : G) → Fintype (B x)] (slots : G → Finset ↥J),
  Finset.univ.biUnion slots = Finset.univ →
    (↑Finset.univ).PairwiseDisjoint slots →
      ∀ (v : (x : G) → B x → (↥J → Fin 2) → ℂ) (A : Matrix (Fin 2) (Fin 2) ℂ) (C : (x : G) → B x → B x → ℂ),
        (∀ (x : G),
            ∀ j ∈ slots x,
              ∀ (y : G), y ≠ x → ∀ (c : B y) (a : Fin 2) (σ : ↥J → Fin 2), v y c (Function.update σ j a) = v y c σ) →
          (∀ (x : G) (b : B x) (σ : ↥J → Fin 2),
              ∑ j ∈ slots x, ∑ a, A (σ j) a * v x b (Function.update σ j a) = ∑ c, C x c b * v x c σ) →
            ∀ ψ ∈ Submodule.span ℂ (Set.range (AKLT.W.H1M032.tensorGenerator v)),
              (Matrix.toEuclideanLin (∑ j, AKLT.Defs.tokenMatrix J j A)) ψ ∈
                Submodule.span ℂ (Set.range (AKLT.W.H1M032.tensorGenerator v))

AKLT.W.H1M032.groupVector : (π : AKLT.Defs.PatternData) →
  (r : AKLT.Defs.Representation) →
    (ε : AKLT.Defs.ExchangeSigns π) →
      (x : ↥(AKLT.Defs.reductionGroups π)) →
        AKLT.Defs.GroupBasis π r ε x → (↥(AKLT.Defs.reductionVectors π r) → Fin 2) → ℂ

AKLT.W.H1M032.groupActionMatrix : (π : AKLT.Defs.PatternData) →
  (r : AKLT.Defs.Representation) →
    (ε : AKLT.Defs.ExchangeSigns π) →
      Matrix (Fin 2) (Fin 2) ℂ →
        (x : ↥(AKLT.Defs.reductionGroups π)) → AKLT.Defs.GroupBasis π r ε x → AKLT.Defs.GroupBasis π r ε x → ℂ

AKLT.W.H1M032.sectorVector_eq_tensorGenerator : ∀ (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  (ε : AKLT.Defs.ExchangeSigns π) (b : AKLT.Defs.ExchangeBasis π r ε),
  AKLT.Blueprint.H1.sectorVector π r ε b = AKLT.W.H1M032.tensorGenerator (AKLT.W.H1M032.groupVector π r ε) b

AKLT.W.H1M032.exchangeSpace_eq_span : ∀ (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  (ε : AKLT.Defs.ExchangeSigns π),
  AKLT.Defs.exchangeSpace π r ε =
    Submodule.span ℂ (Set.range (AKLT.W.H1M032.tensorGenerator (AKLT.W.H1M032.groupVector π r ε)))

AKLT.W.H1M032.groupVector_local : ∀ (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  (ε : AKLT.Defs.ExchangeSigns π) (x : ↥(AKLT.Defs.reductionGroups π)),
  ∀ j ∈ AKLT.W.H1M032.groupSlots π r x,
    ∀ (y : ↥(AKLT.Defs.reductionGroups π)),
      y ≠ x →
        ∀ (c : AKLT.Defs.GroupBasis π r ε y) (a : Fin 2) (σ : ↥(AKLT.Defs.reductionVectors π r) → Fin 2),
          AKLT.W.H1M032.groupVector π r ε y c (Function.update σ j a) = AKLT.W.H1M032.groupVector π r ε y c σ

AKLT.W.H1M032.groupVector_action : ∀ (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  (ε : AKLT.Defs.ExchangeSigns π) (A : Matrix (Fin 2) (Fin 2) ℂ) (x : ↥(AKLT.Defs.reductionGroups π))
  (b : AKLT.Defs.GroupBasis π r ε x) (σ : ↥(AKLT.Defs.reductionVectors π r) → Fin 2),
  ∑ j ∈ AKLT.W.H1M032.groupSlots π r x, ∑ a, A (σ j) a * AKLT.W.H1M032.groupVector π r ε x b (Function.update σ j a) =
    ∑ c, AKLT.W.H1M032.groupActionMatrix π r ε A x c b * AKLT.W.H1M032.groupVector π r ε x c σ

AKLT.W.H1M032.exchangeSpace_matrix_stable : ∀ (π : AKLT.Defs.PatternData) (r : AKLT.Defs.Representation)
  (ε : AKLT.Defs.ExchangeSigns π) (A : Matrix (Fin 2) (Fin 2) ℂ),
  ∀ ψ ∈ AKLT.Defs.exchangeSpace π r ε,
    (Matrix.toEuclideanLin (∑ j, AKLT.Defs.tokenMatrix (AKLT.Defs.reductionVectors π r) j A)) ψ ∈
      AKLT.Defs.exchangeSpace π r ε
```

`#print axioms` output for every exported theorem:

```text
'AKLT.W.H1M032.local_action' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.raw_slot_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.leader_second_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.different_group_slots' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.pair_tokens_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.groupSlots_cover' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.mem_groupSlots_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.groupSlots_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.leader_mem_groupSlots' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.second_mem_groupSlots' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.other_group_tokens_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.token_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.tensorGenerator_update' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.tensorGenerator_config' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.product_group_action' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.sum_token_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.sectorVector_eq_tensorGenerator' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.exchangeSpace_eq_span' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.groupVector_local' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.groupVector_action' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.exchangeSpace_matrix_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1M032.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- Delivered `AKLT/W/H1M032/Main.lean` and five helper/audit modules.
- Exact export: `AKLT.W.H1M032.main : AKLT.Blueprint.H1.SectorSpinStableStatement`.
- Status: PROVED, unconditionally; no residual declarations remain.
- Proves arbitrary identical one-spin matrix sums preserve every exchange sector.
- Works for all patterns and both representations; no coveredness premise is added.
- All exported theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- Main build and exact-type/axiom audit pass.
- Existing statement/library files were not edited; earlier task-local partial Main was replaced.
- Limitations/deviations: none; Physlib was unnecessary.
- Open names: none. No orchestrator decision or further premise is needed.
