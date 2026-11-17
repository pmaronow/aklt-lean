STATUS: PARTIAL

The requested closed theorem is not proved. The replacement `main` compiles, but its exact type is

```lean
AKLT.W.H1C020.Residual_ringFubini →
AKLT.W.H1C020.Residual_centerContraction →
AKLT.Cert.H1.Production.Leaves.momentPolynomial
```

The earlier four representation/mode residuals have been replaced by two mathematical steps. Neither residual is assumed as an axiom or registered as an instance. They are explicit, closed `def ... : Prop` declarations, and all conditional results display them as arguments.

## Delivered files

- [Audit.lean](/home/ubuntu/aklt/wt/LW_H1C020/AKLT/W/H1C020/Audit.lean): Axiom checks for all 56 helper theorems; imported by Main.
- [Fubini.lean](/home/ubuntu/aklt/wt/LW_H1C020/AKLT/W/H1C020/Fubini.lean): Generic finite polynomial contraction over disjoint internal spin sets.
- [Geometry.lean](/home/ubuntu/aklt/wt/LW_H1C020/AKLT/W/H1C020/Geometry.lean): Local degree-four validity from NetworkGeometry.
- [GroupTokens.lean](/home/ubuntu/aklt/wt/LW_H1C020/AKLT/W/H1C020/GroupTokens.lean): Original-slot group indexing and inversion through the whole ring transfer.
- [Inversion.lean](/home/ubuntu/aklt/wt/LW_H1C020/AKLT/W/H1C020/Inversion.lean): Monomial parity signs and inversion of each rational local tensor.
- [Local.lean](/home/ubuntu/aklt/wt/LW_H1C020/AKLT/W/H1C020/Local.lean): Exact rational moment identities, leaf/tip radii, and local denominator clearing.
- [Main.lean](/home/ubuntu/aklt/wt/LW_H1C020/AKLT/W/H1C020/Main.lean): Conditional composition into the requested leaf; prints axioms of main.
- [Normalization.lean](/home/ubuntu/aklt/wt/LW_H1C020/AKLT/W/H1C020/Normalization.lean): Propagation of denominator factors through transfer and centre insertions.
- [Reduction.lean](/home/ubuntu/aklt/wt/LW_H1C020/AKLT/W/H1C020/Reduction.lean): Actual erased reduced integrand, two closed residuals, and their composition.
- [Transfer.lean](/home/ubuntu/aklt/wt/LW_H1C020/AKLT/W/H1C020/Transfer.lean): Expansion of list matrix entries and trace into sums over edge colours.

Every Lean file in the task directory is transitively imported by Main. No existing file outside the assigned task directory was edited. No other blueprint leaf was used as an unproved lemma; none of the new helper proofs imports a W leaf from the proved index.

## Proved work

- `momentNumerator_correct`: for `a+b+c ≤ d` and `a+b+c ≤ 4`, the executable integer numerator at `siteLCD d diluted` is exactly that denominator times `rationalStatusMoment`. Both ordinary and diluted moments, including the two degree-four tensor types, are checked.
- `localPolynomial_clear`: each valid local constructor equals `C s.totalDen * rationalLocal`. The normalized formula has the tip radius `3/5` and reduced-corner radius `1/2` or `1/3` explicitly.
- `polynomialRingValue_paths`: the list matrix product/trace is the closed transfer sum, using named list-entry lemmas rather than reducing a concrete matrix product.
- `network_localValidity`: NetworkGeometry supplies separate degree at most four and excludes simultaneous leaf/tip flags. Coveredness is not needed for this helper.
- `networkNumerator_clear`: for locally valid sites, `networkNumerator ss out next = C (centerScale next * networkDenominator ss) * rationalNetwork ss out next`. The scale is exactly `3` or `5`.
- `contractSpins_disjoint_mul`: if `V` and `W` are disjoint and `p`, `q` have internal support in `V`, `W`, then `contractSpins (V ∪ W) s (p*q) = contractSpins V s p * contractSpins W s q`. External vector tokens may overlap; no degree hypothesis is needed. This generic Fubini theorem is proved, but its application to the actual ring factors remains in the first residual.
- `invertPolynomial_vectorMonomial` and `rationalLocal_inversion`: the constructor's parity sign equals inversion on original `Fin 20` token indices.
- `ring_token_leader`, `ring_token_second`, and `network_tokenInversion`: identify the ring token numbers with original group leaders/second slots, using `Fin.ext` before scalar index calculations.
- `closedTransfer_inversion`: for GroupInversion and NetworkGeometry, inversion of the transfer with all local inversion flags erased is precisely the transfer with the supplied flags. This includes both representations.
- `ringTransfer_of_residual`, `rationalNetwork_of_residuals`, and `main`: compose the remaining two identities with all the proved algebra above.

## Open residuals

All names below are in namespace `AKLT.W.H1C020`; exact definitions follow.

```lean
def Residual_ringFubini : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation,
  ∀ I : Finset (Fin 20), GroupInversion π r I → ∀ ss : List PackedSite,
  NetworkGeometry π r I ss → ∀ codes : List Nat, CenterCode ss codes →
    closedTransfer rationalLocal (eraseNetworkInversion ss) codes = ringPolynomial π r codes
```

```lean
def Residual_centerContraction : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ ss : List PackedSite,
  CenterGeometry π ss → ∀ out : Nat, ringSites.getD out (0,0) = π.outgoing.step →
  ∀ next : Bool, reducedPolynomial π r next = ringPolynomial π r [] +
    MvPolynomial.C (1 / centerScale next) *
      centerInsertions (ringPolynomial π r) ss.length out next (centerPairs ss)
```

`Residual_ringFubini` is the geometric identification of the erased reduced integrand with the normalized ring tensor contraction. The inversion signs, integer numerators, matrix products, and cleared-denominator scale have already been removed from its conclusion. It only covers the zero insertion and the pair insertions used by the constructor. The missing proof must expand the actual `ringIntegrand`, identify retained corners versus replaced leaves and tip fields, reindex the internal spin sites, and apply the proved disjoint-set Fubini theorem. The generic Fubini theorem alone does not establish that geometric factorization.

`Residual_centerContraction` is the passage sum for the actual `reducedIntegrand`. It requires only centre flags, and contains no original-token inversion or local transfer tensor. The missing proof must isolate the three possible covered passage bonds, evaluate constant/second moments and vanishing odd terms, and identify the allowed pair insertions, excluding the outgoing site in next mode. The factor `1/3` or `1/5` is explicit in this residual.

These are task-local residuals, not claims that an unproved blueprint leaf is available. No counterexample was found. The full leaf remains open, and its exact-type check still fails because of these two arguments.

Useful existing proved material for continuing the geometry includes `AKLT.W.H1M023.Geometry` (retained pairs and single-leaf neighbours) and `AKLT.W.H1M006.Geometry` (`covered_incident_edges` and `passage_edge_mem_iff`). They were inspected but not used by the delivered proofs.

## Verification

The final build command was

```sh
PATH="$HOME/.elan/bin:$PATH" lake build AKLT.W.H1C020.Main
```

It passed, including Audit and Main. Timing for the final incremental build:

```text
elapsed_seconds=21.13
maximum_rss_kb=6876684
```

The build log is [build.log](/home/ubuntu/aklt/reports/LW/H1C020/build.log). The numerical moment helper was built in an earlier invocation; this timing is not a clean build of every helper. Earlier exploratory errors were resolved before the final successful build. Independent con-ron/NanoDa checks were not run.

The required unconditional exact-type check was also run separately from `/tmp`, with the expected failure in 6.67 seconds:

```text
/tmp/H1C020ExactType.lean:2:61: error: Type mismatch
  AKLT.W.H1C020.main
has type
  AKLT.W.H1C020.Residual_ringFubini →
    AKLT.W.H1C020.Residual_centerContraction → AKLT.Cert.H1.Production.Leaves.momentPolynomial
but is expected to have type
  AKLT.Cert.H1.Production.Leaves.momentPolynomial
```

No forbidden proof escape hatch was used. Bounded `maxHeartbeats` settings are used only for the finite moment proof and local inversion proof; no zero heartbeat limit is used. A source scan found none of the forbidden declarations/tactics.

## Axiom audit

`Audit.lean` runs `#print axioms` on every exported helper theorem; Main checks main. All 57 outputs use only the allowed axioms (or fewer). Full output for task-local declarations:

```text
'AKLT.W.H1C020.vectorPart_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.contractSpins_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.momentWeight_disjoint' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.contractSpins_disjoint_monomials' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.contractSpins_disjoint_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.bond_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.adjacent_symm' depends on axioms: [propext]
'AKLT.W.H1C020.presentBond_eq_false' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.groupSlots_le_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.tip_not_corner' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.groupSlots_tip_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.even_groupPoint_tip' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.odd_ringSite_not_center_adjacent' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.bool_toNat_le_one' does not depend on any axioms
'AKLT.W.H1C020.network_localValidity' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.ring_token_leader' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.ring_token_second' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.groupSlots_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.network_tokenInversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.openTransfer_inversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.closedTransfer_inversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.invertPolynomial_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.invertPolynomial_C' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.invertPolynomial_vectorVariable' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.inversionSign_eq_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.inversionSign_nil' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C020.inversionSign_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.invertPolynomial_vectorMonomial' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.invertPolynomial_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.invertPolynomial_listSum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.rationalLocal_inversion' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.colorExponent_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.momentNumerator_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.countColor_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.colorChoices_length' depends on axioms: [propext, Quot.sound]
'AKLT.W.H1C020.siteColors_length' depends on axioms: [propext]
'AKLT.W.H1C020.site_den_pos' does not depend on any axioms
'AKLT.W.H1C020.site_totalDen_pos' does not depend on any axioms
'AKLT.W.H1C020.localPolynomial_clear' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.openTransfer_clear' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.polynomialRingValue_clear' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.centerInsertions_scale' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.centerScale_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.networkNumerator_clear' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.centerGeometry_of_network' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.centerInsertions_cons' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.centerInsertions_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.invertPolynomial_centerInsertions' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.ringTransfer_of_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.rationalNetwork_of_residuals' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.getD_range_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.polyEntry_ofFn' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.polyEntry_identity' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.polyEntry_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.polynomialRingProduct_entry' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.polynomialRingValue_paths' depends on axioms: [propext, Classical.choice, Quot.sound]
'AKLT.W.H1C020.main' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Exported declarations and statements

The following is the complete source signature inventory. Names are prefixed by `AKLT.W.H1C020`; the source context opens `AKLT.Defs`, `AKLT.Cert.H1`, and `AKLT.Cert.H1.Production` where needed. Definition bodies are in the linked sources above, and the two residual bodies are reproduced above.

### Fubini.lean

```lean
abbrev LocalExp := LocalVariable →₀ Nat

abbrev VectorExp := (Fin 20 × Fin 3) →₀ Nat

def vectorPart (m : LocalExp) : VectorExp

def momentWeight (V : Finset Plane) (s : Plane → Status) (m : LocalExp) : ℚ

def ExponentSupported (V : Finset Plane) (m : LocalExp) : Prop

def InternallySupported (V : Finset Plane) (p : MvPolynomial LocalVariable ℚ) : Prop

lemma vectorPart_add (m n : LocalExp) : vectorPart (m+n) = vectorPart m + vectorPart n

lemma contractSpins_sum {α : Type*} (V : Finset Plane) (s : Plane → Status)
    (t : Finset α) (f : α → MvPolynomial LocalVariable ℚ) :
    contractSpins V s (∑ a ∈ t, f a) = ∑ a ∈ t, contractSpins V s (f a)

lemma momentWeight_disjoint (V W : Finset Plane) (s : Plane → Status)
    (hd : Disjoint V W) (m n : LocalExp)
    (hm : ExponentSupported V m) (hn : ExponentSupported W n) :
    momentWeight (V ∪ W) s (m+n) = momentWeight V s m * momentWeight W s n

lemma contractSpins_disjoint_monomials (V W : Finset Plane) (s : Plane → Status)
    (hd : Disjoint V W) (m n : LocalExp) (c d : ℚ)
    (hm : ExponentSupported V m) (hn : ExponentSupported W n) :
    contractSpins (V ∪ W) s (MvPolynomial.monomial m c * MvPolynomial.monomial n d) =
      contractSpins V s (MvPolynomial.monomial m c) *
        contractSpins W s (MvPolynomial.monomial n d)

theorem contractSpins_disjoint_mul (V W : Finset Plane) (s : Plane → Status)
    (hd : Disjoint V W) (p q : MvPolynomial LocalVariable ℚ)
    (hp : InternallySupported V p) (hq : InternallySupported W q) :
    contractSpins (V ∪ W) s (p*q) = contractSpins V s p * contractSpins W s q
```

### Geometry.lean

```lean
lemma bond_adjacent (π : PatternData) {e : Plane × Plane}
    (he : e ∈ π.bonds) : Adjacent e.1 e.2

lemma adjacent_symm {x y : Plane} (h : Adjacent x y) : Adjacent y x

lemma presentBond_eq_false (π : PatternData) (x y : Plane) (h : ¬ Adjacent x y) :
    presentBond π x y = false

lemma groupSlots_le_two (π : PatternData) (r : Representation) (x : Plane) :
    groupSlots π r x ≤ 2

lemma tip_not_corner {x : Plane} (hx : x ∈ templateTips) : x ∉ templateCorners

lemma groupSlots_tip_le_one (π : PatternData) (r : Representation) {x : Plane}
    (hx : x ∈ templateTips) : groupSlots π r x ≤ 1

lemma even_groupPoint_tip (i : Nat) (hi : i < 8) (heven : i%2 = 0) :
    groupPoint i ∈ templateTips

lemma odd_ringSite_not_center_adjacent (i : Nat) (hi : i < 8) (hodd : i%2 ≠ 0) :
    ¬ Adjacent (ringSites.getD i (0,0)) (0,0)

lemma bool_toNat_le_one (b : Bool) : b.toNat ≤ 1

lemma network_localValidity (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ss : List PackedSite) (hg : NetworkGeometry π r I ss) :
    ∀ s ∈ ss, LocalValidity s.spec
```

### GroupTokens.lean

```lean
lemma ring_token_leader (i : Nat) (hi : i < 8) :
    tokenIndex (ringLeader i) = groupLeader (groupPoint i)

lemma ring_token_second (i : Nat) (hi : i < 8) :
    tokenIndex (ringLeader i+1) = groupSecond (groupPoint i)

lemma groupSlots_two (π : PatternData) (r : Representation) (x : Plane)
    (h : groupSlots π r x = 2) : x ∈ reductionGroups π ∧ groupIsPair π r x = true

lemma network_tokenInversion (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I)
    (ss : List PackedSite) (hg : NetworkGeometry π r I ss)
    (i : Nat) (hi : i < ss.length) :
    (tokenIndex (ringLeader i) ∈ I ↔ (ss[i]).spec.inverted = true) ∧
      ∀ q < (ss[i]).spec.nslots,
        tokenIndex (ringLeader i+q) ∈ I ↔ (ss[i]).spec.inverted = true

def eraseNetworkInversion (ss : List PackedSite) : List PackedSite

lemma openTransfer_inversion (I : Finset (Fin 20)) (site : Nat)
    (ss : List PackedSite) (codes : List Nat) (a b : Nat)
    (htokens : ∀ i, ∀ hi : i < ss.length,
      (tokenIndex (ringLeader (site+i)) ∈ I ↔ (ss[i]).spec.inverted = true) ∧
        ∀ q < (ss[i]).spec.nslots,
          tokenIndex (ringLeader (site+i)+q) ∈ I ↔ (ss[i]).spec.inverted = true) :
    invertPolynomial I (openTransfer rationalLocal site (eraseNetworkInversion ss) codes a b) =
      openTransfer rationalLocal site ss codes a b

theorem closedTransfer_inversion (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I) (ss : List PackedSite)
    (hg : NetworkGeometry π r I ss) (codes : List Nat) :
    invertPolynomial I (closedTransfer rationalLocal (eraseNetworkInversion ss) codes) =
      closedTransfer rationalLocal ss codes
```

### Inversion.lean

```lean
def tokenIndex (t : Nat) : Fin 20

lemma invertPolynomial_mul (I : Finset (Fin 20)) (p q : VectorPolynomial) :
    invertPolynomial I (p*q) = invertPolynomial I p * invertPolynomial I q

lemma invertPolynomial_C (I : Finset (Fin 20)) (a : ℚ) :
    invertPolynomial I (MvPolynomial.C a) = MvPolynomial.C a

lemma invertPolynomial_vectorVariable (I : Finset (Fin 20)) (t c : Nat) :
    invertPolynomial I (vectorVariable t c) =
      MvPolynomial.C (if tokenIndex t ∈ I then (-1 : ℚ) else 1) * vectorVariable t c

def inversionSign (b : Bool) (cs : List Nat) : ℚ

lemma inversionSign_eq_pow (b : Bool) (cs : List Nat) :
    inversionSign b cs = if b then (-1 : ℚ) ^ (cs.filter (· != 0)).length else 1

lemma inversionSign_nil (b : Bool) : inversionSign b [] = 1

lemma inversionSign_cons (b : Bool) (a : Nat) (cs : List Nat) :
    inversionSign b (a::cs) =
      (if a == 0 then 1 else if b then -1 else 1) * inversionSign b cs

theorem invertPolynomial_vectorMonomial (I : Finset (Fin 20)) (t : Nat)
    (b : Bool) (cs : List Nat)
    (hI : ∀ q < cs.length, tokenIndex (t+q) ∈ I ↔ b = true) :
    invertPolynomial I (vectorMonomial t cs) =
      MvPolynomial.C (inversionSign b cs) * vectorMonomial t cs

lemma invertPolynomial_add (I : Finset (Fin 20)) (p q : VectorPolynomial) :
    invertPolynomial I (p+q) = invertPolynomial I p + invertPolynomial I q

lemma invertPolynomial_listSum (I : Finset (Fin 20)) (ps : List VectorPolynomial) :
    invertPolynomial I ps.sum = (ps.map (invertPolynomial I)).sum

def eraseInversion (s : SiteSpec) : SiteSpec

theorem rationalLocal_inversion (I : Finset (Fin 20)) (site : Nat) (s : SiteSpec)
    (l r v : Nat)
    (hhead : tokenIndex (ringLeader site) ∈ I ↔ s.inverted = true)
    (hslots : ∀ q < s.nslots, tokenIndex (ringLeader site+q) ∈ I ↔ s.inverted = true) :
    invertPolynomial I (rationalLocal site (eraseInversion s) l r v) =
      rationalLocal site s l r v
```

### Local.lean

```lean
def colorExponent (a b c : Nat) (k : Fin 3) : Nat

lemma colorExponent_sum (a b c : Nat) :
    (∑ k : Fin 3, colorExponent a b c k) = a+b+c

lemma momentNumerator_correct (d a b c : Nat) (diluted : Bool)
    (hd : a+b+c ≤ d) (hfour : a+b+c ≤ 4) :
    (momentNumerator (siteLCD d diluted) diluted a b c : ℚ) =
      (siteLCD d diluted : ℚ) *
        rationalStatusMoment (if diluted then .D else .U) (colorExponent a b c)

lemma countColor_sum_le (cs : List Nat) :
    countColor 1 cs + countColor 2 cs + countColor 3 cs ≤ cs.length

lemma colorChoices_length (n : Nat) (cs : List Nat) (hcs : cs ∈ colorChoices n) :
    cs.length = n

def siteDegree (s : SiteSpec) : Nat

def siteColors (s : SiteSpec) (l r v : Nat) (cs : List Nat) : List Nat

lemma siteColors_length (s : SiteSpec) (l r v : Nat) (cs : List Nat)
    (hcs : cs.length = s.nslots) :
    (siteColors s l r v cs).length = siteDegree s

def rationalLocal (site : Nat) (s : SiteSpec) (l r v : Nat) : VectorPolynomial

lemma site_den_pos (s : SiteSpec) : 0 < s.den

lemma site_totalDen_pos (s : SiteSpec) : 0 < s.totalDen

lemma localPolynomial_clear (site : Nat) (s : SiteSpec) (l r v : Nat)
    (hd : siteDegree s ≤ 4) (hleaf : s.leaf = true → s.tip = false) :
    localPolynomial site s l r v = MvPolynomial.C (s.totalDen : ℚ) *
      rationalLocal site s l r v
```

### Main.lean

```lean
theorem main (hF : Residual_ringFubini) (hC : Residual_centerContraction) :
    AKLT.Cert.H1.Production.Leaves.momentPolynomial
```

### Normalization.lean

```lean
def networkDenominator (ss : List PackedSite) : Nat

def LocalValidity (s : SiteSpec) : Prop

lemma openTransfer_clear (site : Nat) (ss : List PackedSite) (codes : List Nat)
    (hv : ∀ s ∈ ss, LocalValidity s.spec) (a b : Nat) :
    openTransfer localPolynomial site ss codes a b =
      MvPolynomial.C (networkDenominator ss : ℚ) *
        openTransfer rationalLocal site ss codes a b

lemma polynomialRingValue_clear (ss : List PackedSite) (codes : List Nat)
    (hv : ∀ s ∈ ss, LocalValidity s.spec) :
    polynomialRingValue ss codes = MvPolynomial.C (networkDenominator ss : ℚ) *
      closedTransfer rationalLocal ss codes

def centerInsertions (value : List Nat → VectorPolynomial) (n out : Nat)
    (next : Bool) (pairs : List (Nat × Nat)) : VectorPolynomial

lemma centerInsertions_scale (value : List Nat → VectorPolynomial) (n out : Nat)
    (next : Bool) (pairs : List (Nat × Nat)) (d : VectorPolynomial) :
    centerInsertions (fun codes => d * value codes) n out next pairs =
      d * centerInsertions value n out next pairs

def centerScale (next : Bool) : ℚ

def rationalNetwork (ss : List PackedSite) (out : Nat) (next : Bool) : VectorPolynomial

lemma centerScale_ne_zero (next : Bool) : centerScale next ≠ 0

lemma networkNumerator_clear (ss : List PackedSite) (out : Nat) (next : Bool)
    (hv : ∀ s ∈ ss, LocalValidity s.spec) :
    networkNumerator ss out next =
      MvPolynomial.C (centerScale next * (networkDenominator ss : ℚ)) *
        rationalNetwork ss out next
```

### Reduction.lean

```lean
def eraseCenterHom : MvPolynomial LocalVariable ℚ →+* MvPolynomial LocalVariable ℚ

def ringIntegrand (π : PatternData) (r : Representation) : MvPolynomial LocalVariable ℚ

def ringCoordinate (site color : Nat) : MvPolynomial LocalVariable ℚ

def insertedRingIntegrand (π : PatternData) (r : Representation) (codes : List Nat) :
    MvPolynomial LocalVariable ℚ

def ringPolynomial (π : PatternData) (r : Representation) (codes : List Nat) : VectorPolynomial

def CenterCode (ss : List PackedSite) (codes : List Nat) : Prop

def CenterGeometry (π : PatternData) (ss : List PackedSite) : Prop

lemma centerGeometry_of_network (π : PatternData) (r : Representation)
    (I : Finset (Fin 20)) (ss : List PackedSite) (hg : NetworkGeometry π r I ss) :
    CenterGeometry π ss

def Residual_ringFubini : Prop

def Residual_centerContraction : Prop

lemma centerInsertions_cons (value : List Nat → VectorPolynomial) (n out : Nat)
    (next : Bool) (x y : Nat) (pairs : List (Nat × Nat)) :
    centerInsertions value n out next ((x,y)::pairs) =
      if next && (x == out || y == out) then centerInsertions value n out next pairs
      else ((List.range 3).map (fun k => value (centerCodes n x y (k+1)))).sum +
        centerInsertions value n out next pairs

lemma centerInsertions_congr (f g : List Nat → VectorPolynomial) (n out : Nat)
    (next : Bool) (pairs : List (Nat × Nat))
    (h : ∀ xy ∈ pairs, ∀ k < 3,
      f (centerCodes n xy.1 xy.2 (k+1)) = g (centerCodes n xy.1 xy.2 (k+1))) :
    centerInsertions f n out next pairs = centerInsertions g n out next pairs

lemma invertPolynomial_centerInsertions (I : Finset (Fin 20))
    (value : List Nat → VectorPolynomial) (n out : Nat) (next : Bool)
    (pairs : List (Nat × Nat)) :
    invertPolynomial I (centerInsertions value n out next pairs) =
      centerInsertions (fun codes => invertPolynomial I (value codes)) n out next pairs

theorem ringTransfer_of_residual (hF : Residual_ringFubini)
    (π : PatternData) (hπ : π.Covered) (r : Representation)
    (I : Finset (Fin 20)) (hI : GroupInversion π r I) (ss : List PackedSite)
    (hg : NetworkGeometry π r I ss) (codes : List Nat) (hc : CenterCode ss codes) :
    closedTransfer rationalLocal ss codes = invertPolynomial I (ringPolynomial π r codes)

theorem rationalNetwork_of_residuals (hF : Residual_ringFubini)
    (hC : Residual_centerContraction) (π : PatternData) (hπ : π.Covered)
    (r : Representation) (I : Finset (Fin 20)) (hI : GroupInversion π r I)
    (ss : List PackedSite) (hg : NetworkGeometry π r I ss)
    (out : Nat) (hout : ringSites.getD out (0,0) = π.outgoing.step) (next : Bool) :
    rationalNetwork ss out next = invertPolynomial I (reducedPolynomial π r next)
```

### Transfer.lean

```lean
def openTransfer (f : Nat → SiteSpec → Nat → Nat → Nat → VectorPolynomial)
    (site : Nat) : List PackedSite → List Nat → Nat → Nat → VectorPolynomial

def closedTransfer (f : Nat → SiteSpec → Nat → Nat → Nat → VectorPolynomial)
    (ss : List PackedSite) (codes : List Nat) : VectorPolynomial

lemma getD_range_map {α : Type*} (f : Nat → α) (n i : Nat)
    (d : α) (hi : i < n) : ((List.range n).map f).getD i d = f i

lemma polyEntry_ofFn (f : Nat → Nat → VectorPolynomial) (i j : Nat)
    (hi : i < 4) (hj : j < 4) :
    polyEntry ((List.range 4).map fun a => (List.range 4).map (f a)) i j = f i j

lemma polyEntry_identity (i j : Nat) (hi : i < 4) (hj : j < 4) :
    polyEntry polyIdentity i j = if i == j then 1 else 0

lemma polyEntry_mul (a b : PolyFour) (i j : Nat) (hi : i < 4) (hj : j < 4) :
    polyEntry (polyMul a b) i j =
      ((List.range 4).map fun k => polyEntry a i k * polyEntry b k j).sum

lemma polynomialRingProduct_entry
    (site : Nat) (ss : List PackedSite) (codes : List Nat)
    (i j : Nat) (hi : i < 4) (hj : j < 4) :
    polyEntry (polynomialRingProduct site ss codes) i j =
      openTransfer localPolynomial site ss codes i j

lemma polynomialRingValue_paths (ss : List PackedSite) (codes : List Nat) :
    polynomialRingValue ss codes = closedTransfer localPolynomial ss codes
```

## ORCH-SUMMARY

- STATUS: PARTIAL. The closed exact target is not proved.
- Delivered Main plus nine transitively imported helper/audit files.
- `main : Residual_ringFubini → Residual_centerContraction → Leaves.momentPolynomial`.
- Open: `AKLT.W.H1C020.Residual_ringFubini`.
- Open: `AKLT.W.H1C020.Residual_centerContraction`.
- Replaced the previous four mode/representation residuals with two mathematical steps.
- Proved local rational moments, exact tip/leaf scaling, denominator propagation, and transfer expansion.
- Proved generic disjoint-set polynomial Fubini; its ring-geometry application remains open.
- Proved original-slot inversion, group-token indexing, and inversion through the ring transfer.
- Both representations and both current/next modes are covered by the conditional composition.
- No other unproved blueprint leaf is assumed; no proved-index W dependency is imported.
- Final `lake build AKLT.W.H1C020.Main` passed in 21.13 seconds (incremental).
- All 57 theorem axiom audits use only allowed axioms; forbidden-source scan is clean.
- Unconditional exact-type check still fails, explicitly recorded in the report/log.
- Independent con-ron/NanoDa checks were not run.
- Orchestrator must assign/prove the two residuals and then remove the arguments from main.
