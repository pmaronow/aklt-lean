STATUS: PROVED

## Deliverable

```lean
theorem AKLT.W.GAP045.main : AKLT.Blueprint.Gap.ShellRowStatement
```

This is a closed theorem with exactly the requested name and type. No residual statements, additional assumptions, or other blueprint leaves are used as proved dependencies. The earlier partial implementation has been replaced; its skipped-row proof was retained in `Rows.lean`.

## Files

- [Main.lean](/home/ubuntu/aklt/wt/LW_GAP045/AKLT/W/GAP045/Main.lean)
- [Finite.lean](/home/ubuntu/aklt/wt/LW_GAP045/AKLT/W/GAP045/Finite.lean)
- [Match.lean](/home/ubuntu/aklt/wt/LW_GAP045/AKLT/W/GAP045/Match.lean)
- [Patch.lean](/home/ubuntu/aklt/wt/LW_GAP045/AKLT/W/GAP045/Patch.lean)
- [Plane.lean](/home/ubuntu/aklt/wt/LW_GAP045/AKLT/W/GAP045/Plane.lean)
- [Window.lean](/home/ubuntu/aklt/wt/LW_GAP045/AKLT/W/GAP045/Window.lean)
- [Rows.lean](/home/ubuntu/aklt/wt/LW_GAP045/AKLT/W/GAP045/Rows.lean)
- [Audit.lean](/home/ubuntu/aklt/wt/LW_GAP045/AKLT/W/GAP045/Audit.lean)

Validation artifacts in this report directory:

- [build-main.log](/home/ubuntu/aklt/reports/LW/GAP045/build-main.log) and [build-main.time](/home/ubuntu/aklt/reports/LW/GAP045/build-main.time).
- [audit.log](/home/ubuntu/aklt/reports/LW/GAP045/audit.log) and [audit.time](/home/ubuntu/aklt/reports/LW/GAP045/audit.time).

All source changes are confined to `AKLT/W/GAP045/`. The frozen statement and existing library files are unchanged.

## Proof

For an active surgery index, first use consistency to identify the full exterior fibre with the pushforward of the specification law on the far volume. Inserting its samples into the current configuration preserves the exterior, and gives exactly the full conditional marginals required by `RowConditions`.

If the predecessor shell agrees, the local separator hypothesis and the original boundary agreement imply equality of the two far-volume laws by range one. Their diagonal coupling makes the whole far volume agree. Exceptional rows are the identity point mass.

For a trial row with differing predecessor shells, the proof uses direct overlap matching. Write A for the near-shell sites and B for the window sites. Fix any assignment a on A. Finite energy gives, for every B assignment b,

```text
P(A=a, B=b) >= alpha^|A| P_B(b),
Q(A=a, B=b) >= alpha^|A| Q_B(b).
```

Match mass `alpha^|A| * min(P_B(b), Q_B(b))` in each label b, using normalized products of these restricted fibres. Complete the remaining marginals with their normalized product. The overlap formula and the window bound give shell agreement probability at least `p * alpha^|A|`. Since `|A| <= 8*l <= 16*l` and `0 < alpha <= 1`, this implies the requested `p * alpha^(16*l)` bound.

This is a deliberate variation from the suggested maximal-B-coupling followed by independent A resampling: the direct common-submeasure construction proves the existential row certificate with a stronger intermediate estimate. It does not change the statement. The zero remaining-mass case is proved explicitly. Empty A, B, and F and the endpoint `p * alpha^(16*l) = 1` require no exclusions.

At index h+1, the proof uses a product coupling when predecessor agreement does not apply. The success obligation is vacuous there, so no window bound at h+1 is invoked. The index inequality `j+2 <= lastShellIndex u` is proved from `j < h` and `h <= shellSpacing u`.

## Exported declarations and axioms

The principal supporting theorems are:

- `complete_subcoupling`: every nonnegative matrix dominated by two probability marginals extends to a coupling of those marginals.
- `match_submeasures` and `match_events`: common labelled submeasures give a coupling with event mass at least their total matched mass.
- `patch_coupling`: disjoint A and B, finite-energy assignment bounds, and B-marginal TV at most `1-t` give A-union-B agreement probability at least `t * alpha^A.card`.
- `local_to_fibre`: insertion pushes a consistent local law to the prescribed full exterior fibre.
- `local_laws_identical`: predecessor-shell agreement gives equality of the two far-volume laws.
- `local_success_coupling`: a trial row has a local coupling with shell agreement probability at least `p * alpha^(16*l)`.
- `row_of_local`: lifting a local coupling with the stated identical and success certificates gives `RowConditions`.
- `skipped_row`: every exceptional row has a point-mass certificate.
- `main`: the original closed `ShellRowStatement`.

`Audit.lean` checks the exact imported theorem type with:

```lean
example : AKLT.Blueprint.Gap.ShellRowStatement := AKLT.W.GAP045.main
```

It also runs `#check` and `#print axioms` for all 56 named declarations, including the helper definitions. Every dependency is among `propext`, `Classical.choice`, and `Quot.sound`. In particular:

```text
'AKLT.W.GAP045.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The exact statements and complete axiom output for every exported named declaration are reproduced below.

## Validation

- `lake build AKLT.W.GAP045.Main` — successful; final build took **30.16 s**, including `Rows` (16 s) and `Main` (6.2 s), with earlier helper modules already compiled.
- `lake env lean AKLT/W/GAP045/Audit.lean` — successful; **7.00 s**. This independently imports `Main`, checks the exact requested type, and audits every named declaration.
- Source scan found none of the prohibited proof escape mechanisms. The build has only style/unused-context warnings.
- `git status --short` reports only the task directory as untracked; no tracked files were changed.

## Open issues

None. No residual or V2 statement is needed. The proof delivers one surgery only, as requested.

## Full declaration and axiom audit

```text
AKLT.W.GAP045.marginal_total {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] (p : AKLT.Defs.Weight Ω) (f : Ω → Ξ) :
  ∑ b, AKLT.Defs.marginal p f b = ∑ x, p x
'AKLT.W.GAP045.marginal_total' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.marginal_nonnegative {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] {p : AKLT.Defs.Weight Ω}
  (hp : ∀ (x : Ω), 0 ≤ p x) (f : Ω → Ξ) (b : Ξ) : 0 ≤ AKLT.Defs.marginal p f b
'AKLT.W.GAP045.marginal_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.marginal_event {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] (p : AKLT.Defs.Weight Ω) (f : Ω → Ξ)
  (b : Ξ) : AKLT.Defs.marginal p f b = AKLT.Defs.eventMass p fun x => f x = b
'AKLT.W.GAP045.marginal_event' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.conditional_event {Ω : Type} [Fintype Ω] (p : AKLT.Defs.Weight Ω) (E A : Ω → Prop) :
  AKLT.Defs.conditionalProbability p E A = (AKLT.Defs.eventMass p fun x => E x ∧ A x) / AKLT.Defs.eventMass p E
'AKLT.W.GAP045.conditional_event' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.marginal_probability {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] {p : AKLT.Defs.Weight Ω}
  (hp : AKLT.Defs.Probability p) (f : Ω → Ξ) : AKLT.Defs.Probability (AKLT.Defs.marginal p f)
'AKLT.W.GAP045.marginal_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.marginal_comp {Ω Ξ Λ : Type} [Fintype Ω] [Fintype Ξ] [Fintype Λ] [DecidableEq Ξ] [DecidableEq Λ]
  (p : AKLT.Defs.Weight Ω) (f : Ω → Ξ) (g : Ξ → Λ) :
  AKLT.Defs.marginal (AKLT.Defs.marginal p f) g = AKLT.Defs.marginal p (g ∘ f)
'AKLT.W.GAP045.marginal_comp' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.marginal_test {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] (p : AKLT.Defs.Weight Ω) (f : Ω → Ξ)
  (g : Ξ → ℝ) : ∑ b, AKLT.Defs.marginal p f b * g b = ∑ x, p x * g (f x)
'AKLT.W.GAP045.marginal_test' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.event_nonnegative {Ω : Type} [Fintype Ω] {p : AKLT.Defs.Weight Ω} (hp : ∀ (x : Ω), 0 ≤ p x)
  (E : Ω → Prop) : 0 ≤ AKLT.Defs.eventMass p E
'AKLT.W.GAP045.event_nonnegative' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.event_mono {Ω : Type} [Fintype Ω] {p q : AKLT.Defs.Weight Ω} {E F : Ω → Prop} (hp : ∀ (x : Ω), 0 ≤ p x)
  (hpq : ∀ (x : Ω), p x ≤ q x) (hEF : ∀ (x : Ω), E x → F x) : AKLT.Defs.eventMass p E ≤ AKLT.Defs.eventMass q F
'AKLT.W.GAP045.event_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.event_le_one {Ω : Type} [Fintype Ω] {p : AKLT.Defs.Weight Ω} (hp : AKLT.Defs.Probability p)
  (E : Ω → Prop) : AKLT.Defs.eventMass p E ≤ 1
'AKLT.W.GAP045.event_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.condition_probability {Ω : Type} [Fintype Ω] {p : AKLT.Defs.Weight Ω} (hp : ∀ (x : Ω), 0 ≤ p x)
  (E : Ω → Prop) (he : 0 < AKLT.Defs.eventMass p E) : AKLT.Defs.Probability (AKLT.Defs.conditionOn p E)
'AKLT.W.GAP045.condition_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.condition_support {Ω : Type} [Fintype Ω] {p : AKLT.Defs.Weight Ω} (E : Ω → Prop) (x : Ω)
  (hx : 0 < AKLT.Defs.conditionOn p E x) : E x
'AKLT.W.GAP045.condition_support' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.event_pos_of_atom {Ω : Type} [Fintype Ω] {p : AKLT.Defs.Weight Ω} (hp : ∀ (x : Ω), 0 ≤ p x) (E : Ω → Prop)
  (x : Ω) (hx : E x) (hpx : 0 < p x) : 0 < AKLT.Defs.eventMass p E
'AKLT.W.GAP045.event_pos_of_atom' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.coupling_probability {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] {p : AKLT.Defs.Weight Ω}
  {q : AKLT.Defs.Weight Ξ} (hp : AKLT.Defs.Probability p) (c : AKLT.Defs.Coupling p q) :
  AKLT.Defs.Probability fun v => c.mass v.1 v.2
'AKLT.W.GAP045.coupling_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.coupling_atom_first {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] {p : AKLT.Defs.Weight Ω}
  {q : AKLT.Defs.Weight Ξ} (c : AKLT.Defs.Coupling p q) (x : Ω) (y : Ξ) : c.mass x y ≤ p x
'AKLT.W.GAP045.coupling_atom_first' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.coupling_atom_second {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] {p : AKLT.Defs.Weight Ω}
  {q : AKLT.Defs.Weight Ξ} (c : AKLT.Defs.Coupling p q) (x : Ω) (y : Ξ) : c.mass x y ≤ q y
'AKLT.W.GAP045.coupling_atom_second' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.complete_subcoupling {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] {p : AKLT.Defs.Weight Ω}
  {q : AKLT.Defs.Weight Ξ} (hp : AKLT.Defs.Probability p) (hq : AKLT.Defs.Probability q) (k : Ω → Ξ → ℝ)
  (hk : ∀ (x : Ω) (y : Ξ), 0 ≤ k x y) (hkp : ∀ (x : Ω), ∑ y, k x y ≤ p x) (hkq : ∀ (y : Ξ), ∑ x, k x y ≤ q y) :
  ∃ c, ∀ (x : Ω) (y : Ξ), k x y ≤ c.mass x y
'AKLT.W.GAP045.complete_subcoupling' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.tv_overlap {Ω : Type} [Fintype Ω] {p q : AKLT.Defs.Weight Ω} (hp : AKLT.Defs.Probability p)
  (hq : AKLT.Defs.Probability q) : AKLT.Defs.totalVariation p q = 1 - ∑ x, min (p x) (q x)
'AKLT.W.GAP045.tv_overlap' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.tv_marginal {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] (p q : AKLT.Defs.Weight Ω) (f : Ω → Ξ) :
  AKLT.Defs.totalVariation (AKLT.Defs.marginal p f) (AKLT.Defs.marginal q f) ≤ AKLT.Defs.totalVariation p q
'AKLT.W.GAP045.tv_marginal' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.main : AKLT.Blueprint.Gap.ShellRowStatement
'AKLT.W.GAP045.main' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.weighted_div_self {w U : ℝ} (hw : 0 ≤ w) (hU : 0 ≤ U) (h : w ≤ U) : w * U / U = w
'AKLT.W.GAP045.weighted_div_self' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.scaled_le {w a U : ℝ} (ha : 0 ≤ a) (hU : 0 ≤ U) (h : w ≤ U) : w * a / U ≤ a
'AKLT.W.GAP045.scaled_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.match_submeasures {Ω Ξ Λ : Type} [Fintype Ω] [Fintype Ξ] [Fintype Λ] {p : AKLT.Defs.Weight Ω}
  {q : AKLT.Defs.Weight Ξ} (hp : AKLT.Defs.Probability p) (hq : AKLT.Defs.Probability q) (u : Λ → AKLT.Defs.Weight Ω)
  (v : Λ → AKLT.Defs.Weight Ξ) (w : AKLT.Defs.Weight Λ) (hu : ∀ (b : Λ) (x : Ω), 0 ≤ u b x)
  (hv : ∀ (b : Λ) (y : Ξ), 0 ≤ v b y) (hw : ∀ (b : Λ), 0 ≤ w b) (hup : ∀ (x : Ω), ∑ b, u b x ≤ p x)
  (hvq : ∀ (y : Ξ), ∑ b, v b y ≤ q y) (hwu : ∀ (b : Λ), w b ≤ ∑ x, u b x) (hwv : ∀ (b : Λ), w b ≤ ∑ y, v b y)
  (E : Ω × Ξ → Prop) (hE : ∀ (b : Λ) (x : Ω) (y : Ξ), 0 < u b x → 0 < v b y → E (x, y)) :
  ∃ c, ∑ b, w b ≤ AKLT.Defs.eventMass (fun z => c.mass z.1 z.2) E
'AKLT.W.GAP045.match_submeasures' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.match_events {Ω Ξ Λ : Type} [Fintype Ω] [Fintype Ξ] [Fintype Λ] {p : AKLT.Defs.Weight Ω}
  {q : AKLT.Defs.Weight Ξ} (hp : AKLT.Defs.Probability p) (hq : AKLT.Defs.Probability q) (f : Ω → Λ) (g : Ξ → Λ)
  (G : Ω → Prop) (H : Ξ → Prop) (w : AKLT.Defs.Weight Λ) (hw : ∀ (b : Λ), 0 ≤ w b)
  (hwp : ∀ (b : Λ), w b ≤ AKLT.Defs.eventMass p fun x => f x = b ∧ G x)
  (hwq : ∀ (b : Λ), w b ≤ AKLT.Defs.eventMass q fun y => g y = b ∧ H y) (E : Ω × Ξ → Prop)
  (hE : ∀ (x : Ω) (y : Ξ), G x → H y → f x = g y → E (x, y)) :
  ∃ c, ∑ b, w b ≤ AKLT.Defs.eventMass (fun z => c.mass z.1 z.2) E
'AKLT.W.GAP045.match_events' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.mapCoupling {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] {p : AKLT.Defs.Weight Ω} {q : AKLT.Defs.Weight Ξ}
  (c : AKLT.Defs.Coupling p q) {Ω' Ξ' : Type} [Fintype Ω'] [Fintype Ξ'] [DecidableEq Ω'] [DecidableEq Ξ'] (f : Ω → Ω')
  (g : Ξ → Ξ') : AKLT.Defs.Coupling (AKLT.Defs.marginal p f) (AKLT.Defs.marginal q g)
'AKLT.W.GAP045.mapCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.event_marginal {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] (p : AKLT.Defs.Weight Ω) (f : Ω → Ξ)
  (E : Ξ → Prop) : AKLT.Defs.eventMass (AKLT.Defs.marginal p f) E = AKLT.Defs.eventMass p fun x => E (f x)
'AKLT.W.GAP045.event_marginal' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.mapCoupling_event {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] {p : AKLT.Defs.Weight Ω} {q : AKLT.Defs.Weight Ξ}
  (c : AKLT.Defs.Coupling p q) {Ω' Ξ' : Type} [Fintype Ω'] [Fintype Ξ'] [DecidableEq Ω'] [DecidableEq Ξ'] (f : Ω → Ω')
  (g : Ξ → Ξ') (E : Ω' × Ξ' → Prop) :
  AKLT.Defs.eventMass (fun z => (AKLT.W.GAP045.mapCoupling c f g).mass z.1 z.2) E =
    AKLT.Defs.eventMass (fun z => c.mass z.1 z.2) fun z => E (f z.1, g z.2)
'AKLT.W.GAP045.mapCoupling_event' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.independentCoupling {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] {p : AKLT.Defs.Weight Ω} {q : AKLT.Defs.Weight Ξ}
  (hp : AKLT.Defs.Probability p) (hq : AKLT.Defs.Probability q) : AKLT.Defs.Coupling p q
'AKLT.W.GAP045.independentCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.diagonalCoupling {Ω : Type} [Fintype Ω] {p q : AKLT.Defs.Weight Ω} (hp : ∀ (x : Ω), 0 ≤ p x)
  (he : p = q) : AKLT.Defs.Coupling p q
'AKLT.W.GAP045.diagonalCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.diagonal_positive {Ω : Type} [Fintype Ω] {p q : AKLT.Defs.Weight Ω} (hp : ∀ (x : Ω), 0 ≤ p x) (he : p = q)
  (x y : Ω) (h : 0 < (AKLT.W.GAP045.diagonalCoupling hp he).mass x y) : x = y
'AKLT.W.GAP045.diagonal_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.mapCoupling_positive {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] {p : AKLT.Defs.Weight Ω}
  {q : AKLT.Defs.Weight Ξ} (c : AKLT.Defs.Coupling p q) {Ω' Ξ' : Type} [Fintype Ω'] [Fintype Ξ'] [DecidableEq Ω']
  [DecidableEq Ξ'] (f : Ω → Ω') (g : Ξ → Ξ') (a : Ω') (b : Ξ') (h : 0 < (AKLT.W.GAP045.mapCoupling c f g).mass a b) :
  ∃ x y, 0 < c.mass x y ∧ f x = a ∧ g y = b
'AKLT.W.GAP045.mapCoupling_positive' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.event_eq_one_of_support {Ω : Type} [Fintype Ω] {p : AKLT.Defs.Weight Ω} (hp : AKLT.Defs.Probability p)
  (E : Ω → Prop) (hs : ∀ (x : Ω), 0 < p x → E x) : AKLT.Defs.eventMass p E = 1
'AKLT.W.GAP045.event_eq_one_of_support' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.extendBlock {ι : Type} [DecidableEq ι] {S : ι → Type} (B : Finset ι) (a : AKLT.Blueprint.Gap.Config S)
  (b : (x : ↥B) → S ↑x) : AKLT.Blueprint.Gap.Config S
'AKLT.W.GAP045.extendBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.restrict_extendBlock {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(x : ι) → Fintype (S x)]
  [∀ (x : ι), Nonempty (S x)] (B : Finset ι) (a : AKLT.Blueprint.Gap.Config S) (b : (x : ↥B) → S ↑x) :
  AKLT.Blueprint.Gap.restrict B (AKLT.W.GAP045.extendBlock B a b) = b
'AKLT.W.GAP045.restrict_extendBlock' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.restrict_eq_agree {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(x : ι) → Fintype (S x)]
  [∀ (x : ι), Nonempty (S x)] (B : Finset ι) (a : AKLT.Blueprint.Gap.Config S) (b : (x : ↥B) → S ↑x)
  (σ : AKLT.Blueprint.Gap.Config S) :
  AKLT.Blueprint.Gap.restrict B σ = b ↔ AKLT.Blueprint.Gap.AgreeOn B σ (AKLT.W.GAP045.extendBlock B a b)
'AKLT.W.GAP045.restrict_eq_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.assignment_mass {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(x : ι) → Fintype (S x)]
  [∀ (x : ι), Nonempty (S x)] {p : AKLT.Defs.Weight (AKLT.Blueprint.Gap.Config S)}
  (hp : AKLT.Defs.PositiveProbability p) {α : ℝ} (he : AKLT.Blueprint.Gap.AssignmentBound p α) (A B : Finset ι)
  (hd : Disjoint A B) (a : AKLT.Blueprint.Gap.Config S) (b : (x : ↥B) → S ↑x) :
  α ^ A.card * AKLT.Defs.marginal p (AKLT.Blueprint.Gap.restrict B) b ≤
    AKLT.Defs.eventMass p fun σ => AKLT.Blueprint.Gap.restrict B σ = b ∧ AKLT.Blueprint.Gap.AgreeOn A σ a
'AKLT.W.GAP045.assignment_mass' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.patch_coupling {ι : Type} [Fintype ι] [DecidableEq ι] {S : ι → Type} [(x : ι) → Fintype (S x)]
  [∀ (x : ι), Nonempty (S x)] {p q : AKLT.Defs.Weight (AKLT.Blueprint.Gap.Config S)}
  (hp : AKLT.Defs.PositiveProbability p) (hq : AKLT.Defs.PositiveProbability q) (A B : Finset ι) (hd : Disjoint A B)
  (α t : ℝ) (hα : 0 ≤ α) (hep : AKLT.Blueprint.Gap.AssignmentBound p α) (heq : AKLT.Blueprint.Gap.AssignmentBound q α)
  (htv :
    AKLT.Defs.totalVariation (AKLT.Defs.marginal p (AKLT.Blueprint.Gap.restrict B))
        (AKLT.Defs.marginal q (AKLT.Blueprint.Gap.restrict B)) ≤
      1 - t) :
  ∃ c,
    t * α ^ A.card ≤ AKLT.Defs.eventMass (fun z => c.mass z.1 z.2) fun z => AKLT.Blueprint.Gap.AgreeOn (A ∪ B) z.1 z.2
'AKLT.W.GAP045.patch_coupling' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.insertVolume (P : AKLT.Blueprint.Gap.PlaneSpec) (W V : Finset AKLT.Defs.Plane)
  (σ : AKLT.Blueprint.Gap.PlaneConfig P W) (τ : AKLT.Blueprint.Gap.PlaneConfig P V) : AKLT.Blueprint.Gap.PlaneConfig P W
'AKLT.W.GAP045.insertVolume' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.insertVolume_outside (P : AKLT.Blueprint.Gap.PlaneSpec) (W V : Finset AKLT.Defs.Plane)
  (σ : AKLT.Blueprint.Gap.PlaneConfig P W) (τ : AKLT.Blueprint.Gap.PlaneConfig P V) :
  AKLT.Defs.AgreeOutside (AKLT.Defs.sitesInVolume W V) σ (AKLT.W.GAP045.insertVolume P W V σ τ)
'AKLT.W.GAP045.insertVolume_outside' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.insertVolume_inside (P : AKLT.Blueprint.Gap.PlaneSpec) (W V : Finset AKLT.Defs.Plane)
  (σ : AKLT.Blueprint.Gap.PlaneConfig P W) (τ : AKLT.Blueprint.Gap.PlaneConfig P V) (x : ↥W) (hx : ↑x ∈ V) :
  AKLT.W.GAP045.insertVolume P W V σ τ x = τ ⟨↑x, hx⟩
'AKLT.W.GAP045.insertVolume_inside' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.marginal_supported_inverse {Ω Ξ : Type} [Fintype Ω] [Fintype Ξ] [DecidableEq Ω] [DecidableEq Ξ]
  (p : AKLT.Defs.Weight Ω) (f : Ω → Ξ) (g : Ξ → Ω) (h : ∀ (x : Ω), p x ≠ 0 → g (f x) = x) :
  AKLT.Defs.marginal (AKLT.Defs.marginal p f) g = p
'AKLT.W.GAP045.marginal_supported_inverse' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.fibre_probability (P : AKLT.Blueprint.Gap.PlaneSpec) (hP : AKLT.Blueprint.Gap.RegularSpec P)
  (W V : Finset AKLT.Defs.Plane) (η : AKLT.Blueprint.Gap.Config P.Letter) (σ : AKLT.Blueprint.Gap.PlaneConfig P W) :
  AKLT.Defs.Probability (AKLT.Blueprint.Gap.fibre (P.law W η) (AKLT.Defs.sitesInVolume W V) σ)
'AKLT.W.GAP045.fibre_probability' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.fibre_to_local (P : AKLT.Blueprint.Gap.PlaneSpec) (hP : AKLT.Blueprint.Gap.RegularSpec P)
  (W V : Finset AKLT.Defs.Plane) (hV : V ⊆ W) (η : AKLT.Blueprint.Gap.Config P.Letter)
  (σ : AKLT.Blueprint.Gap.PlaneConfig P W) :
  (AKLT.Defs.marginal (AKLT.Blueprint.Gap.fibre (P.law W η) (AKLT.Defs.sitesInVolume W V) σ) fun τ =>
      AKLT.Blueprint.Gap.restrict V (AKLT.Blueprint.Gap.fill P W η τ)) =
    P.law V (AKLT.Blueprint.Gap.fill P W η σ)
'AKLT.W.GAP045.fibre_to_local' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.local_to_fibre (P : AKLT.Blueprint.Gap.PlaneSpec) (hP : AKLT.Blueprint.Gap.RegularSpec P)
  (W V : Finset AKLT.Defs.Plane) (hV : V ⊆ W) (η : AKLT.Blueprint.Gap.Config P.Letter)
  (σ : AKLT.Blueprint.Gap.PlaneConfig P W) :
  AKLT.Defs.marginal (P.law V (AKLT.Blueprint.Gap.fill P W η σ)) (AKLT.W.GAP045.insertVolume P W V σ) =
    AKLT.Blueprint.Gap.fibre (P.law W η) (AKLT.Defs.sitesInVolume W V) σ
'AKLT.W.GAP045.local_to_fibre' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.liftLocalCoupling (P : AKLT.Blueprint.Gap.PlaneSpec) (hP : AKLT.Blueprint.Gap.RegularSpec P)
  (W V : Finset AKLT.Defs.Plane) (hV : V ⊆ W) (η ξ : AKLT.Blueprint.Gap.Config P.Letter)
  (σ τ : AKLT.Blueprint.Gap.PlaneConfig P W)
  (c : AKLT.Defs.Coupling (P.law V (AKLT.Blueprint.Gap.fill P W η σ)) (P.law V (AKLT.Blueprint.Gap.fill P W ξ τ))) :
  AKLT.Defs.Coupling (AKLT.Blueprint.Gap.fibre (P.law W η) (AKLT.Defs.sitesInVolume W V) σ)
    (AKLT.Blueprint.Gap.fibre (P.law W ξ) (AKLT.Defs.sitesInVolume W V) τ)
'AKLT.W.GAP045.liftLocalCoupling' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.lifted_support (P : AKLT.Blueprint.Gap.PlaneSpec) (hP : AKLT.Blueprint.Gap.RegularSpec P)
  (W V : Finset AKLT.Defs.Plane) (η ξ : AKLT.Blueprint.Gap.Config P.Letter) (σ τ : AKLT.Blueprint.Gap.PlaneConfig P W)
  (c :
    AKLT.Defs.Coupling (AKLT.Blueprint.Gap.fibre (P.law W η) (AKLT.Defs.sitesInVolume W V) σ)
      (AKLT.Blueprint.Gap.fibre (P.law W ξ) (AKLT.Defs.sitesInVolume W V) τ))
  (v : AKLT.Blueprint.Gap.PlaneConfig P W × AKLT.Blueprint.Gap.PlaneConfig P W) (hv : 0 < c.mass v.1 v.2) :
  AKLT.Defs.AgreeOutside (AKLT.Defs.sitesInVolume W V) σ v.1 ∧
    AKLT.Defs.AgreeOutside (AKLT.Defs.sitesInVolume W V) τ v.2
'AKLT.W.GAP045.lifted_support' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.insert_agreement (P : AKLT.Blueprint.Gap.PlaneSpec) (W V D : Finset AKLT.Defs.Plane) (hD : D ⊆ V)
  (σ τ : AKLT.Blueprint.Gap.PlaneConfig P W)
  (v : AKLT.Blueprint.Gap.PlaneConfig P V × AKLT.Blueprint.Gap.PlaneConfig P V)
  (hv : AKLT.Blueprint.Gap.AgreeOn (AKLT.Defs.sitesInVolume V D) v.1 v.2) :
  AKLT.Blueprint.Gap.AgreeOn (AKLT.Defs.sitesInVolume W D) (AKLT.W.GAP045.insertVolume P W V σ v.1)
    (AKLT.W.GAP045.insertVolume P W V τ v.2)
'AKLT.W.GAP045.insert_agreement' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.local_laws_identical (P : AKLT.Blueprint.Gap.PlaneSpec) (hP : AKLT.Blueprint.Gap.RegularSpec P)
  (a y : AKLT.Defs.Plane) (u l : ℕ) (i : ℤ) (hi : 2 ≤ i) (hg : AKLT.Blueprint.Gap.ShellGeometry l a y u)
  (η ξ : AKLT.Blueprint.Gap.Config P.Letter) (hηξ : ∀ (z : AKLT.Defs.Plane), z ≠ y → η z = ξ z)
  (σ τ : AKLT.Blueprint.Gap.PlaneConfig P (AKLT.Defs.square a u))
  (hs :
    AKLT.Blueprint.Gap.AgreeOn (AKLT.Defs.sitesInVolume (AKLT.Defs.square a u) (AKLT.Defs.shell a y u (i - 1))) σ τ) :
  P.law (AKLT.Defs.farVolume a y u i) (AKLT.Blueprint.Gap.fill P (AKLT.Defs.square a u) η σ) =
    P.law (AKLT.Defs.farVolume a y u i) (AKLT.Blueprint.Gap.fill P (AKLT.Defs.square a u) ξ τ)
'AKLT.W.GAP045.local_laws_identical' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.skipped_row (P : AKLT.Blueprint.Gap.PlaneSpec) (a y : AKLT.Defs.Plane) (u l h : ℕ) (p α : ℝ)
  (η ξ : AKLT.Blueprint.Gap.Config P.Letter) (j : Fin h)
  (ω :
    AKLT.Blueprint.Gap.PlaneConfig P (AKLT.Defs.square a u) × AKLT.Blueprint.Gap.PlaneConfig P (AKLT.Defs.square a u))
  (hex : ↑↑j + 2 ∈ AKLT.Defs.exceptionalIndices a y u) : ∃ r, AKLT.Blueprint.Gap.RowConditions P a y u l h p α η ξ j ω r
'AKLT.W.GAP045.skipped_row' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.row_of_local (P : AKLT.Blueprint.Gap.PlaneSpec) (hP : AKLT.Blueprint.Gap.RegularSpec P)
  (a y : AKLT.Defs.Plane) (u l h : ℕ) (p α : ℝ) (η ξ : AKLT.Blueprint.Gap.Config P.Letter) (j : Fin h)
  (ω :
    AKLT.Blueprint.Gap.PlaneConfig P (AKLT.Defs.square a u) × AKLT.Blueprint.Gap.PlaneConfig P (AKLT.Defs.square a u))
  (hex : ↑↑j + 2 ∉ AKLT.Defs.exceptionalIndices a y u)
  (hD : AKLT.Defs.shell a y u (↑↑j + 2) ⊆ AKLT.Defs.farVolume a y u (↑↑j + 2))
  (c :
    AKLT.Defs.Coupling
      (P.law (AKLT.Defs.farVolume a y u (↑↑j + 2)) (AKLT.Blueprint.Gap.fill P (AKLT.Defs.square a u) η ω.1))
      (P.law (AKLT.Defs.farVolume a y u (↑↑j + 2)) (AKLT.Blueprint.Gap.fill P (AKLT.Defs.square a u) ξ ω.2)))
  (hi :
    AKLT.Blueprint.Gap.AgreeOn (AKLT.Defs.sitesInVolume (AKLT.Defs.square a u) (AKLT.Defs.shell a y u (↑↑j + 1))) ω.1
        ω.2 →
      ∀ (x z : (x : ↥(AKLT.Defs.farVolume a y u (↑↑j + 2))) → P.Letter ↑x), 0 < c.mass x z → x = z)
  (hc :
    ↑j + 2 ≤ h →
      p * α ^ (16 * l) ≤
        AKLT.Defs.eventMass (fun z => c.mass z.1 z.2) fun z =>
          AKLT.Blueprint.Gap.AgreeOn
            (AKLT.Defs.sitesInVolume (AKLT.Defs.farVolume a y u (↑↑j + 2)) (AKLT.Defs.shell a y u (↑↑j + 2))) z.1 z.2) :
  ∃ r, AKLT.Blueprint.Gap.RowConditions P a y u l h p α η ξ j ω r
'AKLT.W.GAP045.row_of_local' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.window_tv_reindex (P : AKLT.Blueprint.Gap.PlaneSpec) (F B : Finset AKLT.Defs.Plane)
  (η ξ : AKLT.Blueprint.Gap.Config P.Letter) :
  AKLT.Defs.totalVariation (AKLT.Defs.marginal (P.law F η) (AKLT.Blueprint.Gap.restrict (AKLT.Defs.sitesInVolume F B)))
      (AKLT.Defs.marginal (P.law F ξ) (AKLT.Blueprint.Gap.restrict (AKLT.Defs.sitesInVolume F B))) ≤
    AKLT.Defs.totalVariation (AKLT.Blueprint.Gap.specMarginal P F B η) (AKLT.Blueprint.Gap.specMarginal P F B ξ)
'AKLT.W.GAP045.window_tv_reindex' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.sites_card_le (W V : Finset AKLT.Defs.Plane) : (AKLT.Defs.sitesInVolume W V).card ≤ V.card
'AKLT.W.GAP045.sites_card_le' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.shell_partition (a y : AKLT.Defs.Plane) (u l : ℕ) (i : ℤ) (F : Finset AKLT.Defs.Plane) :
  AKLT.Defs.sitesInVolume F (AKLT.Defs.nearShell a y u l i) ∪ AKLT.Defs.sitesInVolume F (AKLT.Defs.window a y u l i) =
    AKLT.Defs.sitesInVolume F (AKLT.Defs.shell a y u i)
'AKLT.W.GAP045.shell_partition' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.shell_disjoint (a y : AKLT.Defs.Plane) (u l : ℕ) (i : ℤ) (F : Finset AKLT.Defs.Plane) :
  Disjoint (AKLT.Defs.sitesInVolume F (AKLT.Defs.nearShell a y u l i))
    (AKLT.Defs.sitesInVolume F (AKLT.Defs.window a y u l i))
'AKLT.W.GAP045.shell_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.active_shell_bound (u h : ℕ) (hh : ↑h ≤ AKLT.Defs.shellSpacing u) (j : Fin h) :
  ↑↑j + 2 ≤ AKLT.Defs.lastShellIndex u
'AKLT.W.GAP045.active_shell_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
AKLT.W.GAP045.local_success_coupling (P : AKLT.Blueprint.Gap.PlaneSpec) (hP : AKLT.Blueprint.Gap.RegularSpec P) (l : ℕ)
  (p : ℝ) (Mstar : ℕ) (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hEnergy : AKLT.Blueprint.Gap.SpecEnergy P α)
  (hWindow : AKLT.Blueprint.Gap.SpecWindow P l p Mstar) (a y : AKLT.Defs.Plane) (u h : ℕ) (hu : Mstar ≤ u)
  (hy : AKLT.Defs.setDistance AKLT.Defs.supDist y ↑(AKLT.Defs.square a u) = 1)
  (hg : AKLT.Blueprint.Gap.ShellGeometry l a y u) (hh : ↑h ≤ AKLT.Defs.shellSpacing u) (j : Fin h) (hj : ↑j + 2 ≤ h)
  (hex : ↑↑j + 2 ∉ AKLT.Defs.exceptionalIndices a y u) (η ξ : AKLT.Blueprint.Gap.Config P.Letter) :
  ∃ c,
    p * α ^ (16 * l) ≤
      AKLT.Defs.eventMass (fun z => c.mass z.1 z.2) fun z =>
        AKLT.Blueprint.Gap.AgreeOn
          (AKLT.Defs.sitesInVolume (AKLT.Defs.farVolume a y u (↑↑j + 2)) (AKLT.Defs.shell a y u (↑↑j + 2))) z.1 z.2
'AKLT.W.GAP045.local_success_coupling' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## ORCH-SUMMARY

- STATUS: PROVED.
- Delivered `AKLT/W/GAP045/Main.lean` and seven supporting/audit modules.
- Exact theorem: `AKLT.W.GAP045.main : AKLT.Blueprint.Gap.ShellRowStatement`.
- No residual statements or unproved dependencies remain.
- Skipped rows are identity point masses.
- Agreeing predecessor shells use diagonal local resampling.
- Trial rows use direct common-submeasure matching and product completion.
- This replaces the suggested two-stage A resampling with a stronger overlap estimate.
- Full-law fibre marginals and exterior support follow from consistency and insertion.
- No W success estimate is used at h+1.
- Empty blocks/volumes and delta=1 are included.
- All 56 named declarations were type checked and axiom audited.
- Axioms are contained in propext, Classical.choice, Quot.sound.
- Build Main: success, 30.16 s; independent audit: success, 7.00 s.
- Frozen definitions and existing library files were not changed.
- No decisions or follow-up dependencies are required from the orchestrator.
