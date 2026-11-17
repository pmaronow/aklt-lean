STATUS: COMPLETE

| Leaf in `AKLT.Blueprint.Rec` | Verdict | Difficulty | Fix |
| --- | --- | --- | --- |
| `SecondTermBoundStatement` | TRUE | hard | None |
| `PairResponseSplitStatement` | TRUE | hard | None |
| `RemovalEnvelopeStatement` | TRUE | medium | None |
| `RenewalActionStatement` | TRUE | medium | None |
| `RenewalFiniteIterationStatement` | TRUE | medium | None |
| `RenewalRemainderStatement` | TRUE | medium | None |
| `RenewalSourceStatement` | TRUE | medium | None |
| `RenewalScalarLimitStatement` | TRUE | easy | None |

Reviewed branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. All eight statements are true as written; no additional mathematical premises or corrections were identified. The conditional use of H1 and H2 in the second-term estimate matches the paper. No Lean proofs were written and the repository was not modified. Each JSONL record contains its reason, fix field, two-line route, and difficulty.

The exact statements are in [NodesRecursion.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesRecursion.lean:100) and [NodesRenewal.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/NodesRenewal.lean:12). The paper arguments are the proofs of [l:recineq](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:701), [l:renewal](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:928), and the removal step in [t:rec](/home/ubuntu/aklt/manuscript-v2/sec7-recursion.tex:1036). The finite expansion and its target conditions are in [p:pairwalk](/home/ubuntu/aklt/manuscript-v2/sec6-walks.tex:148).

**Definition tracing.** I read these application-specific dependency chains, including the subordinate definitions rather than relying on declaration comments:

- `PairData`, its `normalized`, `depth`, and `response` projections, `normalizeStart`, `firstLength`, `firstTerm`, `secondTerm`, `targetFactor`, `stoppedSum`, `protectedDistance`, and the exceptional/source constants in [Rec/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:66).
- `Network.ResponsePair`, `HasPairType`, `Consistent`, `Ordinary`, `Auxiliary`, `LocalRules`, `AdmissibleStart`, `active`, `Present`, `bonds`, `presentNeighbours`, `spins`, `partition`, `expectation`, `traceStep`, `traceNetwork`, `traceCoefficient`, `traceRatio`, and `responseEnvelope` in [Domain.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Domain.lean:10).
- Stopped-trail predicates/enumerations, direction words and vertices, and `OpenTrailBound` through `IsTrail`, `trailWeight`, revisit counts, incoming directions, `passageFactor`, and `localThreshold` in [Trails.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Trails.lean:9).
- `Top.H1Statement` through `LocalPatternBound`, covered-pattern rules, template sites/tips/corners and external slots, pattern bonds/active spins, and current/next finite functionals in [Pattern.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Pattern.lean:9).
- Pinned/free expectations through their sums, `extendIcoSpins`, and `PinAssignment` in [PinModel.lean](/home/ubuntu/aklt/repo/AKLT/Defs/PinModel.lean:9); the spin alphabet, U/D weights, explicit icosahedron vectors and their parameters, `dot`, `normSq`, and `UnitVector` in [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:9).
- Ambient lattice distance/adjacency, compass displacements, neighbours, oriented internal bonds, original legs, `setDistance`, `boundaryDepth`, and `protectedSites` in [Geometry.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8).
- `RenewalRows`, `renewalOp`, `renewalIterate`, `renewalSource`, and `hmin` in [Rec/Definitions.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Rec/Definitions.lean:203), with the actual two-constructor `PairType` and its finite enumeration in `Domain.lean`.

**SecondTermBoundStatement — TRUE, hard.** The `pair` field already supplies an ordinary consistent domain, a removed common centre, and both endpoint status/degree restrictions. Positive depth excludes both endpoints from the original protected set. Both starts are consequently unpinned, and an untouched U target has at most three present bonds because its centre is removed. The second expansion stops at exactly original `S`, since its target is already in `S`. The terminal protected defect accounts for at most twelve exceptional U departures. The common pointwise maximum remains inside the first finite sum. The resulting constant is exactly `2 * onePointConstant CV q ^ 2 = sourceConstant CV q`. `OpenTrailBound` explicitly supplies `CV≥1` and `0<q<1`; neither H3 nor a fixed certified rate is needed.

Route: bound each residual by `K_* q^r_v` using the second expansion and terminal-cover estimate.  
Then enlarge the first-trail class to all first hits of `S`, apply its common one-point bound, and use `r_u+r_v ≥ 2d`.

Lean traps: prove distance finiteness before applying `.toNat`; extract `0<q<1` before reversing exponent comparisons. Normalizing the second start changes no expectation because its centre remains removed. Coefficients are rational before casting to real, and both trace ratios are positive. `StoppedNetworkTrail` tests bonds in the initial network; their preservation until use is a trace invariant to establish, rather than a definitional equality.

**PairResponseSplitStatement — TRUE, hard.** Both expansions use the same normalized network, trail class, length cutoff, and mass-free coefficients. Its partitions agree with those of `p.D`. The pair restrictions and explicit exclusions from `S` supply the finite expansion's start and target conditions. A first hit of `v` has unchanged U law, or isolated D law, giving respectively `1` or `3/5` independently of pins. Other terminal sites lie in `S` and give exactly the residual in `secondTerm`. No analytic summability or H1/H2 premise is needed.

Route: transfer both expectations to `p.normalized` and apply the finite expansion with stopping set `insert p.v S`.  
Subtract, splitting on the endpoint being `p.v` and using the common target factor in that branch.

Lean traps: the sum is finite over `range (bonds.card+1)`, including every permitted length. Length zero cannot stop at `insert v S` because `u≠v` and `u∉S`. `targetFactor` uses the original target status, unchanged before its first hit. Its `3/5` is real, whereas departure coefficients `1/3` and `1/5` are rational.

**RemovalEnvelopeStatement — TRUE, medium.** Give `G\Y` status U and everything else status X, with kept sets `neighbours x ∩ G`. The removal hypothesis makes this domain ordinary and consistent, with active set `G\Y` and bonds `internalBonds (G\Y)`. The given centre is removed and in `G`; distance two chooses one of the two declared pair types. The expectation difference is a member of the envelope class at its exact depth. That depth is a natural: `u∈G\Y` makes `G` nonempty, and a site with maximal first coordinate gives a protected boundary site. Distance to this nonempty set is finite for every lattice site. Depth zero is permitted.

Route: construct the full-kept U/X removal domain, choose B or C, and identify its expectations with the pinned/free sums.  
Choose the natural value of its finite protected depth and apply bounded supremum membership.

Lean traps: network sums use `SpinLetter = Option IcoLetter`, while removal sums use `IcoLetter`; eliminate zero-weight `none` configurations at U sites when reindexing. Pins stay indexed by `originalLegs G`, with no hole pins. Real `sSup` membership requires `BddAbove`: the support norm bound and positive normalizers bound all responses by 2. Adjoining zero supplies nonemptiness, not boundedness. The chosen natural depth is cast separately into `ℕ∞` for the distance and `ℤ` for the envelope.

**RenewalActionStatement — TRUE, medium.** `RenewalRows` supplies nonnegative coefficients, positive `h`, and explicit weighted-row summability. Since `PairType` is exactly B and C, `hmin>0` and `hmin≤h X`. Since `0<θ<1`, `θ^(-s)≥1`. Action summands are thus bounded by `(B/hmin)` times a summable weighted row, and are nonnegative. `B≥0` follows by evaluating its bound at any type and integer.

Route: dominate `m X Y s * f Y (d-s)` by `(B/hmin) * m X Y s * h Y * θ^(-s)`.  
Apply summable domination, then nonnegativity of the real `tsum`.

Lean traps: the index is the countable product `PairType × ℕ`, not a finite universal set. The shift in `d-j.2` is coerced to `ℤ`; subtraction is not truncated natural subtraction. A weighted real `tsum` inequality alone would be insufficient without the explicit `Summable` conjunct, which is present.

**RenewalFiniteIterationStatement — TRUE, medium.** The hypotheses imply `0<θ<1` and `0<q<1`, so the source is nonnegative and bounded by `max 2 CT`. At nonpositive integers it equals 2, and `F≤2` supplies the one-step inequality there. Positive integers use the stated recursion. The operator preserves order and is linear on bounded functions with summable rows; its finite iterates remain bounded. The paper's constant-extension condition on negative `F` is unnecessary for this conclusion.

Route: extend `F≤KF+g` to all integers using `F≤2` and positivity on `d≤0`.  
Induct on `k` with bounded-function positivity/linearity and the finite-range sum recurrence.

Lean traps: the output quantifiers are `X:PairType`, `d:ℤ`; the input recursion quantifies `d:ℕ` and casts it. Justify `Int.toNat` conversion on the positive branch. At `k=0`, the iterate is `F` and the sum is empty, giving equality. No negative-index value is inadvertently replaced by zero.

**RenewalRemainderStatement — TRUE, medium.** The shifted row bound implies the unshifted bound `Kh≤ρh`. Compare `F` with `2h/hmin` and iterate. This is uniform in `d`, so arbitrarily negative shifted arguments cause no loss. The base case follows from `h X≥hmin>0` and `F≤2`.

Route: derive the summable unshifted row bound and `F≤2h/hmin`.  
Apply positivity and induction to obtain `K^kF≤(2/hmin)ρ^k h`.

Lean traps: establish positivity of the two-entry minimum before dividing. `ρ^k` is a natural power. Derive unshifted summability by domination rather than inferring it merely from a real `tsum` inequality.

**RenewalSourceStatement — TRUE, medium.** For `d≤0`, `θ^d≥1`; for `d>0`, `q^(2*d.toNat)≤θ^d`. Thus the source is bounded by `(max 2 CT/hmin)h X θ^d` on every integer. For `e X d=h X θ^d`, weighted rows give `Ke≤ρe` with summability. Positivity supplies all iterate bounds, including `k=0` and `CT=0`.

Route: compare the source with `(max 2 CT/hmin)e` on all integers.  
Factor the shifted powers in `Ke`, then use the weighted row bound and induction.

Lean traps: `θ^d` and `θ^(-(s:ℤ))` are integer powers of a strictly positive base; the source's `q` power is natural. The comparison function `e` is unbounded over negative `d`, so the bounded-function action leaf does not apply to it directly. Weighted-row summability supplies the pointwise summability needed instead.

**RenewalScalarLimitStatement — TRUE, easy.** Geometric partial sums converge to `1/(1-ρ)` and `ρ^k→0`. The finite upper bounds converge to the stated right side, and order is preserved in the limit. `1-ρ>0`, avoiding division by zero.

Route: evaluate the limit of the upper-bound expression using geometric partial sums.  
Pass the constant lower bound `x` through that limit.

Lean traps: `Finset.range k` contains `0,…,k-1`, so its geometric numerator is `1-ρ^k`. The empty sum at `k=0` is correct. No separate arbitrary-series summability premise is needed.

**Validation and self-sufficiency.** [Inspect.lean](/home/ubuntu/aklt/reports/TS_REC_11/scratch/Inspect.lean) only imports the existing module and prints declarations. It completed under Lean `v4.35.0-rc2` with exit code 0 and 13 declaration inspections; [Inspect.log](/home/ubuntu/aklt/reports/TS_REC_11/scratch/Inspect.log) records the elaborated statements and casts. All eight leaves are closed `Prop` definitions without silently dropped instance parameters. Finite spin/word sums use finite subtype/function instances, not `Fintype Plane`. Noncomputable finset predicates use classical decidability, which writers can enable locally. The scratch environment links the existing package directory and reads existing build products; no repository build was run.

Intermediate blueprint declarations such as `PairExpansionStatement` and `OnePointSumStatement` are propositions, not proofs. A writer must establish the corresponding paper facts or use subsequently proved theorems; importing their definitions does not supply hypotheses. These facts follow from the concrete definitions and explicit inputs here, so this is proof workload rather than a missing mathematical premise. The difficulty ratings include that workload.

Boundary cases reviewed include an empty volume (excluded by a pair witness), protected removal endpoints (`d=0`), nonpositive renewal indices, zero source constant, zero kernel, and zero iterations. The renewal hypotheses admit `m=0`, `h=1`, `q=1/2`, `θ=1/2`, `ρ=1/2`, `CT=0`, and `F=0`. Pair/removal geometry also has concrete instances: a square of radius three with only its centre removed admits both B and C endpoint pairs at protected depth one. No structural vacuity was found.
