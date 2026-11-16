STATUS: COMPLETE

The statement-layer design is complete and the top assembly implication is proved by the Lean kernel. The mathematical interface propositions remain unproved targets for their assigned lanes. This delivery does not assert an unconditional proof of MainStatementV2.

**Files and build surface.**

Import `AKLT.Defs.All` for shared definitions and `AKLT.Blueprint.Top.All` for all closed interfaces and assembly. `AKLT.Blueprint.Top.Audit` additionally checks that all 47 interface wrappers have the closed type `Prop` and prints the assembly theorem and its dependencies.

| File | Lines | SHA-256 |
|---|---:|---|
| [AKLT/Challenge/MainV2.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Challenge/MainV2.lean) | 25 | `19d6f5e6e7c89913f5af32317d7f64bba66e9e3761ef81d2dcc7941f12a321d5` |
| [AKLT/Defs/All.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/All.lean) | 7 | `cacfcf5785e9dbc7027e9439a9bcea957a2c231eac9ef29da067ba49f4c06b26` |
| [AKLT/Defs/Automaton.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean) | 121 | `f56fe52ba441d0a37ffa90280955298d04902824370fdede4c8e25bfa0681cfe` |
| [AKLT/Defs/Computational.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean) | 90 | `e4d4c3ee6b8b1c50edf66a95ae6cedd1471d6aabbc86dd65ce55d1a2024bff48` |
| [AKLT/Defs/Domain.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean) | 137 | `a24232e28c2655a64e751c7ef0816625bfd6039d402f975677ded3a70c454a70` |
| [AKLT/Defs/FiniteNetwork.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean) | 107 | `dbcf451e51a0e32d1fa8a058e7db1dfbd6f5269bf0af8f98b2e9e6a6c1addf8c` |
| [AKLT/Defs/Frame.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean) | 71 | `4559e49749302e1d9844bc925c77aa597a45f5958ba6cc06bae07fc8fc742456` |
| [AKLT/Defs/FrameModel.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean) | 93 | `bed820e8eb8156962c51af8e4c5a8c65ee4f9d65cdfa7f5637205902b4ac204f` |
| [AKLT/Defs/Geometry.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean) | 121 | `66aa3e0c6d60bcf3bbf9cb39c2a791d991808c01cc2a4f34cb789f054c327595` |
| [AKLT/Defs/Kernel.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean) | 128 | `b0b15a6df64cee96a95a30c394d0b2218c96434a69019020781327be8cc51e6f` |
| [AKLT/Defs/Moment.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean) | 88 | `947764cfa2dd537a1a2ffef468f8f02719bdc60446764d18c6edf1d4f3d52b9b` |
| [AKLT/Defs/Operator.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean) | 248 | `99fe47a56a4efb026ca577976f36e9bd32b0ac9614aa653a3994b721a3e991ef` |
| [AKLT/Defs/OperatorContracts.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean) | 103 | `9b7cb0c594373a0cf5c3261c5b686ec30b353d8633a617b7371c9db35b53bdf4` |
| [AKLT/Defs/Pattern.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean) | 103 | `7ad6da346ae877e76fc6672d01e56fff3acca5fa3f9bf80dca57acad42b0c725` |
| [AKLT/Defs/PinModel.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/PinModel.lean) | 63 | `9eccdde4a42c5b5f037444ccf5d05eafae4f9a48238d01b4aa089146a9b301ee` |
| [AKLT/Defs/Polynomial.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Polynomial.lean) | 45 | `696cf3c485efcfce5b99a24981e58f670193d165f79fceb16df8d50476e2981f` |
| [AKLT/Defs/Probability.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean) | 98 | `1004145b668c650e5f4c78f6880a98647fce961db82dc66441f05476ab10ae8a` |
| [AKLT/Defs/Quantum.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Quantum.lean) | 55 | `0e849a2cf0e9a5969b5ec9805c1720c610637932cc7d2a12a352cd1d7dd53df9` |
| [AKLT/Defs/Response.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean) | 77 | `db08c4a8adbfefb66db262060ca9c7e8579653f2d4ecbb9c1aa9d01a5219d577` |
| [AKLT/Defs/Specification.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Specification.lean) | 38 | `2d4b6af1a5afcef65f323256f058147f145112e69d052c4a951bda48ff0343a1` |
| [AKLT/Defs/Stationary.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean) | 166 | `742a873ff71bf95961d868a8bc2051b6b4402117d466651ec68d762bd7eec429` |
| [AKLT/Defs/Trails.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean) | 100 | `8f6dbbd4ba8e7d35206528c488d7c0e3a7c3a770501e428ab0c1f6750c2b5cef` |
| [AKLT/Blueprint/Top/All.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/All.lean) | 5 | `e6fe6880bd065457ac4b08d906d8336cf3c8eed62e922a945cfefd033b7edb3e` |
| [AKLT/Blueprint/Top/Assembly.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Assembly.lean) | 27 | `f99c41cd98017d08d7820062615ca19278bfcaad29fb37a1ec5e7efd78d0aa47` |
| [AKLT/Blueprint/Top/Audit.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Audit.lean) | 55 | `d0d9e7f80419c882d109c281924b83fa3ac67b08fba546052516319a393dd72a` |
| [AKLT/Blueprint/Top/Coefficients.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Coefficients.lean) | 78 | `0ac0044b9582783c81baa6e3718c2af2330e2110f3ae87ec6dd2c5cc5510fb2a` |
| [AKLT/Blueprint/Top/Common.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Common.lean) | 75 | `62d397a792189442950a10ad5d4349a603d623d00a9b1dc0124fb005a1d2869c` |
| [AKLT/Blueprint/Top/Computation.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean) | 186 | `c54e79f04a1ed97e7840af08a3cb0664f4a7775b96aca971657f3d33752c178b` |
| [AKLT/Blueprint/Top/Operator.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Operator.lean) | 150 | `681918869fd7c92a736e7be4f05f3cedcf4af11c20475894c8e6e090d89ea584` |
| [AKLT/Blueprint/Top/Quantum.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Quantum.lean) | 103 | `b221e24c81a0a0262cd3e5fd4082d977979f8a02c655c82b7a7cbf725c30bb57` |
| [AKLT/Blueprint/Top/Response.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Response.lean) | 63 | `d03bf1c2a72fd22c8cab37efc5fd7b9c936a4ec74db058b7efbf21f58aca5830` |
| [AKLT/Blueprint/Top/Windows.lean](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Windows.lean) | 34 | `9ddaf2ab79a5dfd070450aca32077a0766ec31dd79404d0ee135c14d841b239f` |

The frozen `AKLT/Challenge/Main.lean` was not edited. Its SHA-256 is `e2d03b1b487a0f71544563eb2a2f3b242f37369bd30aab2eb3bf4738a385abcd`.
`MainV2.lean` has 25 lines and imports exactly Mathlib and AKLT.Challenge.Main. Its ready marker contains `19d6f5e6e7c89913f5af32317d7f64bba66e9e3761ef81d2dcc7941f12a321d5`. The marker was written immediately after the first successful 13.21-second build and still passes `sha256sum -c`.

**Challenge statement.**

```lean
def MainStatementV2 : Prop :=
  (∀ L N : Size, B L N ≠ 0 ∧
    LinearMap.ker (H L N) = Submodule.span ℂ {B L N}) ∧
  ∃ c : ℝ, 0 < c ∧ ∃ L₀ : ℕ, 3 ≤ L₀ ∧
    ∀ L N : Size, L₀ ≤ L.val → L₀ ≤ N.val →
      ∀ μ : ℝ, μ ≠ 0 → (H L N).HasEigenvalue (μ : ℂ) → c ≤ μ
```

**Proved export.**

```lean
theorem mainV2_of_parts : InputsStatement → RecStatement → CutMOSStatement →
    MainWStatement → TorusKernelStatement → MainStatementV2
```

The proof extracts the selected H1/H2/H3 inputs, obtains the response witnesses from Rec, applies CutMOS with the displayed exp(-2E), applies MainW to the resulting W parameters, and uses the independent TorusKernel proposition for every size. QD is an exported target used inside the eventual lane-A proof of MainW; it is not a redundant extra argument of this assembly.

**Kernel dependency audit.**

There is one hand-written exported theorem in this delivery. Its exact output is:

```text
'AKLT.Blueprint.Top.mainV2_of_parts' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The three dependencies are exactly the permitted logical foundations. All 47 closed interface wrappers elaborate as `: Prop`, with no section hypotheses, mathematical typeclass assumptions or implicit mathematical parameters. The auxiliary definitions and finite enumeration instances contain no postulates or unproved proof terms.

**Build commands and timings.**

```bash
export PATH="$HOME/.elan/bin:$PATH"
lake build AKLT.Challenge.MainV2
# First successful build: real 13.21 s (Main 3.1 s, MainV2 2.7 s)
lake build AKLT.Blueprint.Top.Assembly AKLT.Blueprint.Top.Computation AKLT.Blueprint.Top.Operator
# Full affected dependency rebuild: real 38.77 s
lake build AKLT.Blueprint.Top.All AKLT.Defs.All
# Import-surface build: real 10.41 s
lake build AKLT.Blueprint.Top.Audit
# Closedness and dependency audit: real 9.27 s
```

The final source rebuild used `lake build AKLT.Blueprint.Top.Audit AKLT.Defs.All` and passed in 19.75 seconds. Logs: [build.log](build.log), [audit.log](audit.log), [final-build.log](final-build.log), and [constants-check.log](constants-check.log). Only project modules were built; Mathlib was already prebuilt. There were no sub-agents, updates, package writes, or unrestricted parallel builds. Independent targets in each Lake invocation number at most three; this stays within the six-process brief.

**Modelling choices and Lean traps checked.**

- The Hamiltonian and VBS state are the frozen Challenge definitions. All final spectral assertions refer to those constants. Natural Size subtypes encode exactly the periods at least three, with no parity predicates.
- Plane distances are ambient lattice distances, including after removals. Original pin legs remain individually indexed; frame boundaries have one admissible letter per exterior site. These types are never interchanged.
- Every partition sum and every fixed-length path sum is finite, including its empty-product configuration. U has twelve positive atoms; its optional zero label has weight zero. D has the exact 3/5 mixture plus the 2/5 zero atom. No measure, disintegration or arbitrary-function rotational invariance is used.
- Total coordinate maps simplify trace updates; all networks used by the contracts have an explicit finite active volume. Validity, ordinary protection, consistent kept sets and auxiliary defects are separate predicates. Removed sites have no new pin factors or scalar mass.
- The covered pattern has thirteen sites, twenty explicit slots, both corner slots, and covering U tips whose kept sets are not constrained by a global tip rule. The departure coefficient is computed from the evolving status.
- True revisits count previous departures. The initial virtual incoming edge is not marked used; its reversal is explicitly forbidden. All trail bonds are unordered finite sets, so a reversed repeat is still a repeat.
- The kernel uses the amended alpha/beta/beta-prime table, actual dead neighbours and ambient shifts. The short cutoff is twelve; the dyadic h_C differs from 6/5 by -1/22517998136852480. Exposure sums include the x factor at the rewarded position and use theta-independent orderings.
- Infinite nonnegative kernels use ENNReal, avoiding the real tsum convention on divergent series. All-length H3 is an all-cutoff assertion, and finiteness of shifted kernels is a theorem target. No finite prefix is mistaken for H3.
- Stationary certificates keep the initial-bond and known-site rules forever on Z^2, use L>=m+2=12, cap every stored value, and distinguish value scale 2^16 from coefficient scale 2^48. No spatial quotient or parity improvement appears.
- Operator matrices are rebuilt from the pattern, rational moment contractions, leaf replacements, inversion, Pauli entries and unnormalized integer sector vectors. An explicit basis bijection determines the finite certificate order. Complex positivity uses ComplexOrder. Integer sector forms are not confused with orthonormal operator matrices. The positive congruence scale is 15 D0 q, and lower-triangular L need not be invertible.
- Lean sum/product bodies containing addition are parenthesized; otherwise the binder can end before the addition. Dependent Fin prefix embeddings explicitly bind their size proof. The keywords prefix and Pi were avoided as local names. Fintype instances for small enums are explicit because the toolchain deriving plugin produced an incompatible list coercion.
- The only resource adjustment is maxRecDepth 2048 in Stationary.lean for finite-square subtype elaboration. No unbounded heartbeat setting, evaluation effects or untrusted computation is present.
- A source scan found no forbidden proof placeholders or execution mechanisms. The literal #print axioms commands are the required audit. MainV2 imports were checked, its hash verified, and the frozen Main diff is empty.
- Small Python Fraction checks confirmed the transcription of q, the dyadic witness, H2 denominators, C_V majorant and nine-decimal row assembly. Those are fidelity checks only; no native result is claimed as a Lean input proof.

**Differences from the LaTeX.**

Every interface has a row below, including changes that are only finite indexing, squared norms, explicit domain predicates or equivalent form inequalities. These rows identify the chosen Lean encoding; mathematical equivalence lemmas needed by downstream proofs remain their owners' proof obligations. No parity, graph-scope, volume threshold or numerical weakening is introduced in the headline statement.

| Plan label | Lean form and difference |
|---|---|
| `d:model` | The model is reused by definitional aliases to the frozen H and B; no alternate torus physics is introduced. Site and bond types are the frozen Size/ZMod types. |
| `d:moment` | R^3 is Fin 3 -> R with an explicit scalar product; the twelve atoms use Fin 3 x Fin 2 x Fin 2. The U functional permits a zero atom of weight zero, while D has weights 1/20 at the twelve vertices and 2/5 at zero. Distances use extended naturals, with decay zero at infinity. |
| `l:moments` | The positive-degree D tensor is encoded by rationalStatusMoment. Covariance is stated for an arbitrary finite product Fin n, arbitrary U/D choices and site-dependent orthogonal matrices. This includes the single-site clauses and is slightly more explicit than the prose site-by-site extension. |
| `d:pinmodel` | Volumes and removals are Finsets. Original legs are separately indexed subtypes. Partition observables are functions of total coordinate maps extended by zero outside the active support; the zero values are only indexing defaults. The original G and original pins remain parameters after removals. |
| `l:finitefacts` | Finite active networks are indexed by Fin n, with ordered distinct-endpoint bonds counted once and a finite list of unrelated unit pins at each vertex. Free positivity is stated for a finite list of scalar-product factors with explicit degree counts. The normalized free-positivity clause follows from the separately stated positive partition sum. Norm bounds use squared norms. |
| `l:35` | Norm inequalities and the range ball use squared norms (9/25). The local U/D bound is the primitive statement; the conditional-mean sentence is obtained by substituting the finitely many factors on a positive fibre, using FiniteFactsStatement. It is not a separate literal conjunct. |
| `l:exact` | Arbitrary finite positive weighted unit laws use FrameData plus MomentLaw; repeated atom labels are permitted. Mixtures use Option labels and explicit zero weights at U sites. Separate degree includes the whole inserted polynomial. |
| `h:P` | ResponseProperty includes A>=2 and 0<theta<1 as conjuncts instead of external binder restrictions. PStatement is its existential closure. Empty-set distance is infinity with decay zero; for an admissible pair the original protected layer is nonempty. |
| `d:poly` | Homogeneous forms use ordinary monomial coefficient arrays Fin(d+1)->C. The matrix action is returned as its actual substituted MvPolynomial. Physical evaluation multiplies the frozen orthonormal coefficients by square-root binomial factors. Spinors are chosen explicitly only on the three finite alphabets. |
| `d:frame` | A finite set with weights is represented by FrameData n plus injectivity and the IsFrame predicate. Weighted laws for quadrature have a separate predicate that permits repeated labels. |
| `l:tight` | Isometry is expressed as the exact norm-square identity (equivalent for the explicitly linear evaluation map). The statement includes arbitrary compatible finite spinor choices, arbitrary site frames on a torus, and the particular frozen three-frame evaluation. |
| `l:threeframes` | Frame letters are labels; injection, norm, antipodality and moment properties are explicit conjuncts. Both signs of the interaction bounds and attainment are retained. |
| `d:framemodel` | Laws are real finite weight functions divided by their actual partition sums. Strict positivity is a theorem target in PlaneEnergyStatement. Conditional expectations are explicit fibre quotients. The gap has ENNReal codomain to give infinity for a singleton; gap bounds use PoincareLower. |
| `l:planeenergy` | Partial conditioning is encoded by finite equality events on a disjoint J, with an arbitrary target assignment on U. The k-site lower bound includes the one-site cases. Conditioning consistency is equality of actual marginal laws. Torus nearest-neighbour Markov dependence is included explicitly; conditional plane block gaps follow via consistency from the arbitrary-volume plane gap clause. |
| `d:shells` | The radius u is a natural number, with positivity supplied in consumers. Shell indices and floor radii are integers. sqrt(sqrt(u)) realizes u^(1/4) on its stated domain. All shells, windows and exceptional indices are explicit finite filters of physical sites. |
| `d:W` | WindowProperty includes the positivity/size restrictions as conjuncts and universally quantifies every colouring, translate, exterior seed, integer trial, and two independent finite frame boundaries. |
| `l:shellgeom` | Parallel clearance is written as the coordinate distance to each exterior lattice half-plane. The side-meets-square hypothesis is explicit. All other clauses use finite subsets and extended-natural distances. |
| `t:cutMOS` | ResponseProperty carries its domain restrictions. CutMOSStatement universally quantifies A and theta, fixes l0=64 and the displayed exp(-2E), and supplies one integer Mstar. Positivity and the upper bound one for p0, plus Mstar>=1, are retained inside WindowProperty. |
| `d:domain` | Network uses total status/kept maps for easy trace updates; validity forces the original finite support, local half-edge restrictions and degree bound. Ordinary, auxiliary and consistent are separate predicates. All partition sums are over the finite active subset. Protected original legs are retained and there is no mass field. |
| `l:response` | A step is represented by its current auxiliary network rather than a path index j. Coefficients are the actual logarithmic-mean formulas. The three-neighbour and two-neighbour identities, the one-neighbour response and D ratio-one cases are explicit. The intermediate crude bound beta-prime<=bar-beta follows arithmetically from 35510/100000<=36751/100000. |
| `d:pattern` | Thirteen template sites and all twenty external slots are explicit. Raw status/kept data are separated from Covered. Tip kept sets are deliberately ignored for present bonds. Current and next are finite sums on the same active set, with the passage status/bond change specified. |
| `h:H1` | LocalPatternBound is parameterized by the two thresholds and includes their domain restrictions. H1Statement specializes it to the frozen rational thresholds. |
| `d:weights` | Words are Fin n -> Compass. Used bonds are unordered two-element Finsets, and revisit means a previous departure, not an arrival. Inverse threshold weights are specialized to the paper's two frozen thresholds. |
| `h:H2` | OpenTrailBound retains arbitrary C_V and q, starts, incoming directions and lengths. The closed H2Statement specializes only its two constants to the selected numerical theorem. |
| `l:log-mean-bounds` | The exact enclosure arithmetic uses Q and the analytic monotonicity uses R, with explicit casts. Nonincreasing in each variable is encoded as the equivalent joint coordinatewise inequality. All amended table entries are preserved. |
| `l:response-typed` | CoveredDeparture makes the normalization/matching of non-tip status and kept data explicit, while allowing covering tips. The actual analytic coefficients and all inequalities used to derive the table bounds are retained. |
| `d:kernel` | At each fixed length the sum is finite. Infinite nonnegative series use ENNReal instead of real tsum, avoiding its value zero on nonsummable series. Finiteness is an explicit MTheta conclusion. Exposure products are a recursive ordered sum, not a second independent product convention. |
| `d:kernel-order` | First visits are Fin n indices; mergeSort uses the exact rational score, an explicit zero-reward infinity branch and path-index ties. The dyadic h_C is not 6/5. The long ordering is straight-first then turning, both in path order. |
| `h:H3` | The closed contract uses the stated all-finite-cutoff rational inequality. The full nonnegative M1 row inequality is included separately in StationaryAssemblyStatement, with ENNReal semantics. |
| `l:Mtheta` | Shifted entries and the majorant use ENNReal. The statement includes the shift bound, all-entry finiteness, and the same positive vector at an existential theta and rho. Negative integer shifts are exact zpow; the majorant uses real rpow for n/2. |
| `t:rec` | The existential theta and rho additionally retain ShiftedWitness and the exact displayed renewal amplitude. This makes the plan's “one may take” clause an explicit part of the closed proposition. |
| `t:H1` | This has its own closed H1TheoremStatement, in addition to the parameterized H1 property and fixed H1Statement wrapper. |
| `t:inputs` | InputsStatement contains the exact semantic H1/H2/H3 conclusions and q_*<2499/2500<1. The prose identifying the three proof routes is represented by separate reconstruction/check Props, rather than a proof-method field in a mathematical proposition. No certificate correctness is asserted by merely importing the module. |
| `d:memory-automaton` | The raw state type is a subtype of the finite compass-word type. At memory zero, arrival has an unused default; all automaton theorems require m>=1. Absolute labels are preserved. |
| `d:memorygrowth` | The matrix is regenerated by a four-direction sum and exact successor equality. True endpoint-window masses use the whole true trail weight. The selected small test is the m=6 instance. |
| `l:alm` | The constant uses sSup/sInf on finite ranges, with the zero-memory case excluded by m>=1. W_r is evaluated at a fixed start/incoming direction; the all-start conclusion uses the translation/rotation symmetry of the actual lattice weights. The statement also permits any larger constant. |
| `l:H2-dihedral` | The quotient orbit count is expressed by 115 representatives and unique orbit coverage, avoiding an assumed Setoid instance. The raw count is 916. Symmetry and representative-row soundness are explicit predicates. |
| `p:H2-test` | The witness is an existential positive integer function on the regenerated raw state type, with attained lower/upper extrema. Its maximum row ratio is expressed by an all-row inequality plus an equality row. The integer row form uses the regenerated matrix entries with the exact common denominator. |
| `l:H2-CV` | The finite prefix estimates are uniform. The base-constant bound is stated for every positive vector of max/min ratio at most six, hence applies to the selected witness. The H2 conclusion has the semantic H2-test witness assertion as premise; no growth-lemma theorem is added as a hypothesis. |
| `l:automaton-quotient` | The statement includes existence of labelled quotient data from a compatible surjective raw map, then equality of every finite stopped iterate. Compatibility makes all admissibility, kind, successor and nonrevisit-arrival checks explicit. Unused nonraw word values are immaterial. |
| `p:automaton10` | The supplied finite quotient is expressed existentially, with actual raw-word cardinality, representatives, surjectivity and labelled edge counts. No external data file or hash is assumed correct. |
| `d:phaseweights` | Phase transitions are a 4-by-4 coefficient function with explicit diagonal and the two permitted off-diagonal cases. Finite folds sum all phase histories. |
| `l:phase-expansion` | The sum over histories is a four-coordinate fold. The statement includes both its exact long-order contribution and its factorization at every prefix length. |
| `d:stationary-walk` | States are curried Phase, Fin q and Plane coordinates. The centre/target rows are zero. Centre values/transitions contribute zero. Initial-bond exclusion and known-site rules remain active at every time. |
| `l:stationary-domination` | The statement includes pointwise domination of every true suffix phase transition and the resulting finite-horizon continuation sums. Prefixes have L>=12=m+2; no weaker cutoff is substituted. |
| `l:Bellman-soundness` | A finitely branching graph is represented by a list of destination/real-weight pairs at each state. A real-valued F is automatically finite-valued. Both finite sums and their ENNReal full sum are bounded. The terminal-equality sufficient condition is the immediate special case of the displayed supersolution hypothesis. |
| `d:stationary-certificate` | Arrays use natural numbers (so nonnegativity is structural), a finite square subtype for stored values, and positive caps. Exact coefficient ceilings have scale 2^48, values scale 2^16. Passes contains every free/local row, cap and terminal condition. |
| `l:stationary-local-global` | Rational potentials express the displayed inequality exactly. The statement also explicitly bounds all finite continuation sums. It includes coefficient-ceiling soundness as a rational inequality. |
| `d:prefix-bound` | Short trails and surviving prefixes are generated as finite direction words. Prefix phases use the actual trail history. J is an exact rational number; a hit at twelve is excluded from the surviving-prefix part. |
| `l:prefix-domination` | The full nonnegative sum is represented by its equivalent bound at every finite true-trail cutoff. No prefix-only inequality is substituted for the all-length assertion. |
| `l:kernel-reflection` | The statement explicitly preserves raw closedness, first direction, weights, ordering, response pairs, coefficients, pair type and B shift, and gives equality for every cutoff. The B/S potential is never assumed to be reflected data. |
| `p:stationary-check` | The five arrays and a correct regenerated quotient are existential data. Prefix ceilings are inequalities after multiplication by 10^9 in Q. Spatial count 19881 and type Fin 3741 are explicit. No files are imported as facts. |
| `l:stationary-assembly` | The same five passing arrays and exact prefix ceilings imply the two finite row inequalities, their rational assembly bounds, the full ENNReal M1 row bounds and H3. Proof dependencies such as prefix domination and reflection are not extra premises. |
| `l:Iw` | Z_w is an explicit passage-deleted finite functional. A reconstructed rational polynomial is related to each original partition sum by an explicit equality target. Affinity and orthogonal covariance are polynomial statements. |
| `l:leaf` | One-bond leaf laws are expressed by equality for every neighbour vector in the closed unit ball, with an existential positive A and ball vector u. This is the factor identity used in the reductions. Zero-bond local positivity is explicit. |
| `d:reduction` | The two representations are finite constructors. Surviving vector tokens are a subset of the twenty original slot indices, so inactive variables are ignored rather than renumbered globally. Every replacement and internal moment contraction is reconstructed from the pattern. |
| `c:reduce` | The reduced polynomial is rational and evaluated in R. Positivity is tested on twenty unit vectors with unused variables absent, equivalent to the paper's k surviving vectors. The common positive K and ball-vector data are explicit. |
| `d:Pauli` | Operators and product densities are explicit finite tensor-basis matrices. Rational real/imaginary Pauli entries are available separately for reconstruction. Vector-affinity counts total degree over each triple of coordinates, not coordinatewise multilinearity alone. |
| `l:inversion` | The trace identity is stated for any finite active token set J and any supported rational vector-affine polynomial. Complex positive-(semi)definiteness uses Mathlib's ComplexOrder scope. The closed-ball conclusion includes unit vectors. |
| `l:Ostruct` | Commutation is expressed in finite tensor coordinates, with SU(2) specified by g* g=I and det g=1. U-pair compression and D-pair exchange are actual linear-map identities. |
| `d:exchange` | The sector basis is an integer tensor-coordinate function. Symmetric middle vectors and antisymmetric vectors are unnormalized, exactly as in the LaTeX. Signs on singles and U pairs are ignored; this only repeats identical sectors. Central subspaces inherit the ambient Hilbert inner product. |
| `l:sector` | An operator on a supported sector is represented by an ambient linear map that preserves the sector; Hermiticity and the three commutation relations are imposed only on that sector. Equality is of eigenvalue sets, with a separate positive-definiteness equivalence. No multiplicity equality is asserted. |
| `l:gram-residual` | Matrices use Fin n indices and explicit integer row sums. Positivity of the diagonal is retained. Positive definiteness is asserted for casts to both R and C. The zero-L case is an allowed instance, not a separate required witness. |
| `l:integercheck` | The matrices are reconstructed from rational polynomials, inversion, Pauli entries and integer sector vectors. floor only totalizes integer extraction; the statement explicitly requires equality with the unrounded form after denominator clearing. The exact complex scale is 15 D0 q. Optional Bareiss divisibility and principal-minor identities are separate conjuncts. |
| `p:certificate` | All supported exchange sign assignments are checked (unused signs repeat sectors). Each certificate supplies an explicit bijection from Fin t to the actual central-sector basis, allowing a concrete verified data order without relying on Fintype.equivFin. The reindexed matrix is still reconstructed from the polynomial. Positive g,d,S and both strict residual conditions are explicit. No matrix, factor generation or pivot data are postulated. |
| `t:main` | Size replaces integer periods with natural periods at least three. Nonzero eigenvalues are real values embedded in C, as in the frozen Challenge. All-size nonzero B and kernel equality precede the existential eventual gap. mainV2_of_parts is explicitly an implication from closed interface Props, not an unconditional proof of their inhabitants. |
| `p:toruskernel` | Simplicity is expressed by two-site bonds and injective bond indexing; degree four is the neighbour-cardinality assertion. Reorientation is a Boolean sign choice in the actual polynomial product, followed by the frozen coordinate conversion. |
| `l:star` | The five-site star reuses the frozen spin matrices and projector formula. The infimum definition of g_star is accompanied by explicit positivity, attainment and minimality targets. This is an auxiliary finite star, not a new torus Hamiltonian. |
| `t:QD` | The operator inequality is expressed as quadratic-form coercivity for every real Poincare lower bound gamma, rather than multiplication by an abstract scalar infimum. The density identity retains pi, squared modulus and the exact frozen norm. The eigenvalue-gap sentence is the corresponding consequence with the separate kernel/positivity facts. |
| `t:mainW` | The W premise is the existential closure of WindowProperty over l0,p0,Mstar. The conclusion EventualMain includes the eventual ground-line equality and spectral bound, with no parity assumptions. |

**Open proof obligations.**

The assigned design work is complete. The 47 closed Props are obligations, not proved facts. In particular H1 pattern coverage/operator certificates, H2 raw-window enumeration and witness checks, H3 quotient reconstruction/Bellman data/prefix checks, response recursion, cut geometry/windows, and the quantum/classical/periodic gap proofs still require inhabitants supplied by their owners. No certificate file, stored matrix, orbit list, gzip hash, or native exit code is trusted. There is no unconditional theorem claiming MainStatementV2 in this delivery.

The notation and contracts are now available for those proofs. The finite computational definitions are mathematical specifications; optimized kernel checkers, balanced lookup structures, sharding and data encodings belong to the certificate lanes. The optional Bareiss fallback is specified but is not required by the primary Gram/residual proposition.

**Complete declaration-to-label registry.**

This registry lists 411 hand-written mathematical definitions, predicates, data types and the proved theorem. Compiler-generated recursors/decidability/repr functions and anonymous typeclass instances are standard representation infrastructure, not additional mathematical assertions. The finite instances are all explicit enum proofs or Fintype.ofFinite on a finite subtype. [declarations.json](declarations.json) contains the same registry with the full Lean source of each declaration.

| Lean declaration | Kind | Source | Plan label(s) |
|---|---|---|---|
| `AKLT.Challenge.MainStatementV2` | def | [AKLT/Challenge/MainV2.lean:18](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Challenge/MainV2.lean:18) | [t:main](#latex-t-main) |
| `AKLT.Defs.RawWindow` | def | [AKLT/Defs/Automaton.lean:9](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:9) | [d:memory-automaton](#latex-d-memory-automaton) |
| `AKLT.Defs.MemoryWindow` | abbrev | [AKLT/Defs/Automaton.lean:13](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:13) | [d:memory-automaton](#latex-d-memory-automaton) |
| `AKLT.Defs.windowArrival` | def | [AKLT/Defs/Automaton.lean:20](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:20) | [d:memory-automaton](#latex-d-memory-automaton) |
| `AKLT.Defs.windowSuccessor` | def | [AKLT/Defs/Automaton.lean:24](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:24) | [d:memory-automaton](#latex-d-memory-automaton) |
| `AKLT.Defs.WindowAdmissible` | def | [AKLT/Defs/Automaton.lean:28](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:28) | [d:memory-automaton](#latex-d-memory-automaton) |
| `AKLT.Defs.StepKind` | inductive | [AKLT/Defs/Automaton.lean:34](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:34) | [d:memory-automaton](#latex-d-memory-automaton) |
| `AKLT.Defs.windowKind` | def | [AKLT/Defs/Automaton.lean:42](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:42) | [d:memory-automaton](#latex-d-memory-automaton) |
| `AKLT.Defs.kindWeight` | def | [AKLT/Defs/Automaton.lean:47](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:47) | [d:memorygrowth](#latex-d-memorygrowth) |
| `AKLT.Defs.memoryMatrix` | def | [AKLT/Defs/Automaton.lean:53](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:53) | [d:memorygrowth](#latex-d-memorygrowth) |
| `AKLT.Defs.lastWindowWord` | def | [AKLT/Defs/Automaton.lean:59](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:59) | [d:memorygrowth](#latex-d-memorygrowth) |
| `AKLT.Defs.memoryTrailMass` | def | [AKLT/Defs/Automaton.lean:63](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:63) | [d:memorygrowth](#latex-d-memorygrowth) |
| `AKLT.Defs.MemoryQuotient` | structure | [AKLT/Defs/Automaton.lean:69](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:69) | [l:automaton-quotient](#latex-l-automaton-quotient) |
| `AKLT.Defs.MemoryQuotient.Correct` | def | [AKLT/Defs/Automaton.lean:78](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:78) | [l:automaton-quotient](#latex-l-automaton-quotient) |
| `AKLT.Defs.CompatibleProjection` | def | [AKLT/Defs/Automaton.lean:88](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:88) | [l:automaton-quotient](#latex-l-automaton-quotient) |
| `AKLT.Defs.quotientEdgeCount` | def | [AKLT/Defs/Automaton.lean:97](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:97) | [p:automaton10](#latex-p-automaton10) |
| `AKLT.Defs.SquareSymmetry` | abbrev | [AKLT/Defs/Automaton.lean:101](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:101) | [l:H2-dihedral](#latex-l-H2-dihedral) |
| `AKLT.Defs.turnLeft` | def | [AKLT/Defs/Automaton.lean:104](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:104) | [l:H2-dihedral](#latex-l-H2-dihedral) |
| `AKLT.Defs.reflectDirection` | def | [AKLT/Defs/Automaton.lean:107](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:107) | [l:H2-dihedral](#latex-l-H2-dihedral) |
| `AKLT.Defs.symmetryDirection` | def | [AKLT/Defs/Automaton.lean:110](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:110) | [l:H2-dihedral](#latex-l-H2-dihedral) |
| `AKLT.Defs.symmetryWord` | def | [AKLT/Defs/Automaton.lean:114](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:114) | [l:H2-dihedral](#latex-l-H2-dihedral) |
| `AKLT.Defs.SameWindowOrbit` | def | [AKLT/Defs/Automaton.lean:118](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Automaton.lean:118) | [l:H2-dihedral](#latex-l-H2-dihedral) |
| `AKLT.Defs.openTrailTotal` | def | [AKLT/Defs/Computational.lean:9](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:9) | [l:alm](#latex-l-alm) |
| `AKLT.Defs.memoryWitnessRatio` | def | [AKLT/Defs/Computational.lean:14](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:14) | [l:alm](#latex-l-alm) |
| `AKLT.Defs.memoryBaseConstant` | def | [AKLT/Defs/Computational.lean:18](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:18) | [l:alm](#latex-l-alm) |
| `AKLT.Defs.rawBackward` | def | [AKLT/Defs/Computational.lean:23](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:23) | [l:automaton-quotient](#latex-l-automaton-quotient) |
| `AKLT.Defs.quotientBackward` | def | [AKLT/Defs/Computational.lean:33](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:33) | [l:automaton-quotient](#latex-l-automaton-quotient) |
| `AKLT.Defs.finiteOperatorSum` | def | [AKLT/Defs/Computational.lean:42](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:42) | [l:phase-expansion](#latex-l-phase-expansion) |
| `AKLT.Defs.appendWords` | def | [AKLT/Defs/Computational.lean:46](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:46) | [l:phase-expansion](#latex-l-phase-expansion) |
| `AKLT.Defs.takeWord` | def | [AKLT/Defs/Computational.lean:50](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:50) | [l:phase-expansion](#latex-l-phase-expansion) |
| `AKLT.Defs.truePhaseCoefficient` | def | [AKLT/Defs/Computational.lean:54](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:54) | [l:phase-expansion](#latex-l-phase-expansion) |
| `AKLT.Defs.longOrdering` | def | [AKLT/Defs/Computational.lean:59](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:59) | [d:kernel-order](#latex-d-kernel-order) |
| `AKLT.Defs.truePhaseSuffix` | def | [AKLT/Defs/Computational.lean:64](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:64) | [l:phase-expansion](#latex-l-phase-expansion) |
| `AKLT.Defs.trueContinuationSum` | def | [AKLT/Defs/Computational.lean:72](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:72) | [l:stationary-domination](#latex-l-stationary-domination) |
| `AKLT.Defs.stationaryReward` | def | [AKLT/Defs/Computational.lean:78](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:78) | [d:stationary-walk](#latex-d-stationary-walk) |
| `AKLT.Defs.stationaryContinuationSum` | def | [AKLT/Defs/Computational.lean:82](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:82) | [l:stationary-domination](#latex-l-stationary-domination) |
| `AKLT.Defs.listBackward` | def | [AKLT/Defs/Computational.lean:87](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Computational.lean:87) | [l:Bellman-soundness](#latex-l-Bellman-soundness) |
| `AKLT.Defs.Network` | structure | [AKLT/Defs/Domain.lean:10](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:10) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.active` | def | [AKLT/Defs/Domain.lean:15](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:15) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.Present` | def | [AKLT/Defs/Domain.lean:19](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:19) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.bonds` | def | [AKLT/Defs/Domain.lean:26](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:26) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.presentNeighbours` | def | [AKLT/Defs/Domain.lean:30](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:30) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.LocalRules` | def | [AKLT/Defs/Domain.lean:34](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:34) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.Ordinary` | def | [AKLT/Defs/Domain.lean:42](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:42) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.Auxiliary` | def | [AKLT/Defs/Domain.lean:47](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:47) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.Consistent` | def | [AKLT/Defs/Domain.lean:51](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:51) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.spins` | def | [AKLT/Defs/Domain.lean:58](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:58) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.partition` | def | [AKLT/Defs/Domain.lean:63](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:63) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.expectation` | def | [AKLT/Defs/Domain.lean:73](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:73) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.ratio` | def | [AKLT/Defs/Domain.lean:78](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:78) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.Network.AdmissibleStart` | def | [AKLT/Defs/Domain.lean:82](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:82) | [d:trace](#latex-d-trace) |
| `AKLT.Defs.traceStep` | def | [AKLT/Defs/Domain.lean:88](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:88) | [d:trace](#latex-d-trace) |
| `AKLT.Defs.traceNetwork` | def | [AKLT/Defs/Domain.lean:94](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:94) | [d:trace](#latex-d-trace) |
| `AKLT.Defs.traceCoefficient` | def | [AKLT/Defs/Domain.lean:99](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:99) | [d:trace](#latex-d-trace) |
| `AKLT.Defs.traceRatio` | def | [AKLT/Defs/Domain.lean:105](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:105) | [d:trace](#latex-d-trace) |
| `AKLT.Defs.PairType` | inductive | [AKLT/Defs/Domain.lean:110](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:110) | [d:pairenv](#latex-d-pairenv) |
| `AKLT.Defs.HasPairType` | def | [AKLT/Defs/Domain.lean:117](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:117) | [d:pairenv](#latex-d-pairenv) |
| `AKLT.Defs.Network.ResponsePair` | def | [AKLT/Defs/Domain.lean:121](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:121) | [d:pairenv](#latex-d-pairenv) |
| `AKLT.Defs.responseEnvelope` | def | [AKLT/Defs/Domain.lean:129](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Domain.lean:129) | [d:pairenv](#latex-d-pairenv) |
| `AKLT.Defs.FiniteSpinNetwork` | structure | [AKLT/Defs/FiniteNetwork.lean:10](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:10) | [l:finitefacts](#latex-l-finitefacts) |
| `AKLT.Defs.FiniteSpinNetwork.Valid` | def | [AKLT/Defs/FiniteNetwork.lean:17](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:17) | [l:finitefacts](#latex-l-finitefacts) |
| `AKLT.Defs.FiniteSpinNetwork.weight` | def | [AKLT/Defs/FiniteNetwork.lean:23](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:23) | [l:finitefacts](#latex-l-finitefacts) |
| `AKLT.Defs.FiniteSpinNetwork.partition` | def | [AKLT/Defs/FiniteNetwork.lean:31](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:31) | [l:finitefacts](#latex-l-finitefacts) |
| `AKLT.Defs.conditionalProbability` | def | [AKLT/Defs/FiniteNetwork.lean:36](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:36) | [l:CE](#latex-l-CE) |
| `AKLT.Defs.conditionOn` | def | [AKLT/Defs/FiniteNetwork.lean:42](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:42) | [l:CE](#latex-l-CE) |
| `AKLT.Defs.eventMass` | def | [AKLT/Defs/FiniteNetwork.lean:47](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:47) | [l:CE](#latex-l-CE) |
| `AKLT.Defs.localProduct` | def | [AKLT/Defs/FiniteNetwork.lean:52](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:52) | [l:35](#latex-l-35) |
| `AKLT.Defs.localMean` | def | [AKLT/Defs/FiniteNetwork.lean:55](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:55) | [l:35](#latex-l-35) |
| `AKLT.Defs.evaluateReduced` | def | [AKLT/Defs/FiniteNetwork.lean:59](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:59) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.productDensity` | def | [AKLT/Defs/FiniteNetwork.lean:63](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:63) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.invertVectors` | def | [AKLT/Defs/FiniteNetwork.lean:68](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:68) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.PositiveOn` | def | [AKLT/Defs/FiniteNetwork.lean:72](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:72) | [l:sector](#latex-l-sector) |
| `AKLT.Defs.eigenvaluesOn` | def | [AKLT/Defs/FiniteNetwork.lean:77](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:77) | [l:sector](#latex-l-sector) |
| `AKLT.Defs.exchangeSpace` | def | [AKLT/Defs/FiniteNetwork.lean:82](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:82) | [d:exchange](#latex-d-exchange) |
| `AKLT.Defs.tokenMatrix` | def | [AKLT/Defs/FiniteNetwork.lean:88](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:88) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.totalSpinZ` | def | [AKLT/Defs/FiniteNetwork.lean:93](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:93) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.totalSpinPlus` | def | [AKLT/Defs/FiniteNetwork.lean:96](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:96) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.totalSpinMinus` | def | [AKLT/Defs/FiniteNetwork.lean:99](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:99) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.centralSpace` | def | [AKLT/Defs/FiniteNetwork.lean:103](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FiniteNetwork.lean:103) | [d:exchange](#latex-d-exchange) |
| `AKLT.Defs.FrameData` | structure | [AKLT/Defs/Frame.lean:9](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:9) | [d:frame](#latex-d-frame) |
| `AKLT.Defs.IsFrame` | def | [AKLT/Defs/Frame.lean:14](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:14) | [d:frame](#latex-d-frame) |
| `AKLT.Defs.MomentLaw` | def | [AKLT/Defs/Frame.lean:22](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:22) | [l:exact](#latex-l-exact) |
| `AKLT.Defs.momentLawFunctional` | def | [AKLT/Defs/Frame.lean:28](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:28) | [l:exact](#latex-l-exact) |
| `AKLT.Defs.frameRotation` | def | [AKLT/Defs/Frame.lean:33](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:33) | [l:threeframes](#latex-l-threeframes) |
| `AKLT.Defs.frameVector` | def | [AKLT/Defs/Frame.lean:37](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:37) | [l:threeframes](#latex-l-threeframes) |
| `AKLT.Defs.frameBound` | def | [AKLT/Defs/Frame.lean:41](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:41) | [l:threeframes](#latex-l-threeframes) |
| `AKLT.Defs.frameRatio` | def | [AKLT/Defs/Frame.lean:44](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:44) | [l:threeframes](#latex-l-threeframes) |
| `AKLT.Defs.frameEnergy` | def | [AKLT/Defs/Frame.lean:47](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:47) | [l:planeenergy](#latex-l-planeenergy) |
| `AKLT.Defs.Spinor` | abbrev | [AKLT/Defs/Frame.lean:50](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:50) | [d:poly](#latex-d-poly) |
| `AKLT.Defs.pauli` | def | [AKLT/Defs/Frame.lean:53](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:53) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.spinDensity` | def | [AKLT/Defs/Frame.lean:60](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:60) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.frameSpinor` | def | [AKLT/Defs/Frame.lean:65](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Frame.lean:65) | [d:poly](#latex-d-poly) |
| `AKLT.Defs.ProperPlaneColouring` | def | [AKLT/Defs/FrameModel.lean:10](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:10) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.ProperTorusColouring` | def | [AKLT/Defs/FrameModel.lean:14](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:14) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.PlaneConfiguration` | abbrev | [AKLT/Defs/FrameModel.lean:19](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:19) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.exteriorSites` | def | [AKLT/Defs/FrameModel.lean:22](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:22) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.FrameBoundary` | abbrev | [AKLT/Defs/FrameModel.lean:25](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:25) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.extendLetters` | def | [AKLT/Defs/FrameModel.lean:29](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:29) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.extendBoundary` | def | [AKLT/Defs/FrameModel.lean:33](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:33) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.planeWeight` | def | [AKLT/Defs/FrameModel.lean:37](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:37) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.planeLaw` | def | [AKLT/Defs/FrameModel.lean:46](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:46) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.marginal` | def | [AKLT/Defs/FrameModel.lean:50](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:50) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.planeMarginal` | def | [AKLT/Defs/FrameModel.lean:54](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:54) | [d:W](#latex-d-W) |
| `AKLT.Defs.TorusConfiguration` | abbrev | [AKLT/Defs/FrameModel.lean:59](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:59) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.torusWeight` | def | [AKLT/Defs/FrameModel.lean:62](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:62) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.torusLaw` | def | [AKLT/Defs/FrameModel.lean:70](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:70) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.torusReference` | def | [AKLT/Defs/FrameModel.lean:74](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:74) | [l:tight](#latex-l-tight) |
| `AKLT.Defs.frameEval` | def | [AKLT/Defs/FrameModel.lean:78](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:78) | [l:tight](#latex-l-tight) |
| `AKLT.Defs.WindowProperty` | def | [AKLT/Defs/FrameModel.lean:83](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/FrameModel.lean:83) | [d:W](#latex-d-W) |
| `AKLT.Defs.Plane` | abbrev | [AKLT/Defs/Geometry.lean:8](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:8) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.latticeDist` | def | [AKLT/Defs/Geometry.lean:11](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:11) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.supDist` | def | [AKLT/Defs/Geometry.lean:14](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:14) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.Compass` | inductive | [AKLT/Defs/Geometry.lean:17](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:17) | [d:memory-automaton](#latex-d-memory-automaton) |
| `AKLT.Defs.Compass.step` | def | [AKLT/Defs/Geometry.lean:25](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:25) | [d:memory-automaton](#latex-d-memory-automaton) |
| `AKLT.Defs.Compass.reverse` | def | [AKLT/Defs/Geometry.lean:32](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:32) | [d:memory-automaton](#latex-d-memory-automaton) |
| `AKLT.Defs.Adjacent` | def | [AKLT/Defs/Geometry.lean:39](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:39) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.neighbours` | def | [AKLT/Defs/Geometry.lean:44](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:44) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.positiveNeighbours` | def | [AKLT/Defs/Geometry.lean:47](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:47) | [d:pinmodel](#latex-d-pinmodel) |
| `AKLT.Defs.internalBonds` | def | [AKLT/Defs/Geometry.lean:50](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:50) | [d:pinmodel](#latex-d-pinmodel) |
| `AKLT.Defs.originalLegs` | def | [AKLT/Defs/Geometry.lean:54](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:54) | [d:pinmodel](#latex-d-pinmodel) |
| `AKLT.Defs.setDistance` | def | [AKLT/Defs/Geometry.lean:58](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:58) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.boundaryDepth` | def | [AKLT/Defs/Geometry.lean:62](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:62) | [d:pinmodel](#latex-d-pinmodel) |
| `AKLT.Defs.protectedSites` | def | [AKLT/Defs/Geometry.lean:66](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:66) | [d:pinmodel](#latex-d-pinmodel) |
| `AKLT.Defs.decay` | def | [AKLT/Defs/Geometry.lean:71](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:71) | [h:P](#latex-h-P) |
| `AKLT.Defs.square` | def | [AKLT/Defs/Geometry.lean:74](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:74) | [d:shells](#latex-d-shells) |
| `AKLT.Defs.squareCorners` | def | [AKLT/Defs/Geometry.lean:79](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:79) | [d:shells](#latex-d-shells) |
| `AKLT.Defs.shellSpacing` | def | [AKLT/Defs/Geometry.lean:83](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:83) | [d:shells](#latex-d-shells) |
| `AKLT.Defs.shellRadius` | def | [AKLT/Defs/Geometry.lean:86](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:86) | [d:shells](#latex-d-shells) |
| `AKLT.Defs.lastShellIndex` | def | [AKLT/Defs/Geometry.lean:89](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:89) | [d:shells](#latex-d-shells) |
| `AKLT.Defs.farVolume` | def | [AKLT/Defs/Geometry.lean:92](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:92) | [d:shells](#latex-d-shells) |
| `AKLT.Defs.shell` | def | [AKLT/Defs/Geometry.lean:97](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:97) | [d:shells](#latex-d-shells) |
| `AKLT.Defs.nearShell` | def | [AKLT/Defs/Geometry.lean:102](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:102) | [d:shells](#latex-d-shells) |
| `AKLT.Defs.window` | def | [AKLT/Defs/Geometry.lean:108](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:108) | [d:shells](#latex-d-shells) |
| `AKLT.Defs.exceptionalIndices` | def | [AKLT/Defs/Geometry.lean:112](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:112) | [d:shells](#latex-d-shells) |
| `AKLT.Defs.geometryThreshold` | def | [AKLT/Defs/Geometry.lean:119](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Geometry.lean:119) | [l:shellgeom](#latex-l-shellgeom) |
| `AKLT.Defs.kernelStart` | def | [AKLT/Defs/Kernel.lean:9](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:9) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.kernelCentre` | def | [AKLT/Defs/Kernel.lean:10](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:10) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.kernelTarget` | def | [AKLT/Defs/Kernel.lean:11](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:11) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.kernelIncoming` | def | [AKLT/Defs/Kernel.lean:12](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:12) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.ClosedTrail` | def | [AKLT/Defs/Kernel.lean:15](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:15) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.deadAt` | def | [AKLT/Defs/Kernel.lean:21](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:21) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.responseNeighbours` | def | [AKLT/Defs/Kernel.lean:25](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:25) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.liveOtherNeighbours` | def | [AKLT/Defs/Kernel.lean:30](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:30) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.responsePairs` | def | [AKLT/Defs/Kernel.lean:36](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:36) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.pairCoefficient` | def | [AKLT/Defs/Kernel.lean:40](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:40) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.responsePairType` | def | [AKLT/Defs/Kernel.lean:47](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:47) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.pairShift` | def | [AKLT/Defs/Kernel.lean:52](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:52) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.responseKappa` | def | [AKLT/Defs/Kernel.lean:56](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:56) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.kernelWitness` | def | [AKLT/Defs/Kernel.lean:61](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:61) | [d:kernel-order](#latex-d-kernel-order) |
| `AKLT.Defs.kernelRho` | def | [AKLT/Defs/Kernel.lean:66](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:66) | [d:kernel-order](#latex-d-kernel-order) |
| `AKLT.Defs.witnessKappa` | def | [AKLT/Defs/Kernel.lean:69](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:69) | [d:kernel-order](#latex-d-kernel-order) |
| `AKLT.Defs.firstVisitList` | def | [AKLT/Defs/Kernel.lean:73](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:73) | [d:kernel-order](#latex-d-kernel-order) |
| `AKLT.Defs.shortOrderLE` | def | [AKLT/Defs/Kernel.lean:78](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:78) | [d:kernel-order](#latex-d-kernel-order) |
| `AKLT.Defs.kernelOrdering` | def | [AKLT/Defs/Kernel.lean:90](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:90) | [d:kernel-order](#latex-d-kernel-order) |
| `AKLT.Defs.exposureSum` | def | [AKLT/Defs/Kernel.lean:96](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:96) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.closedContribution` | def | [AKLT/Defs/Kernel.lean:101](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:101) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.kernelLengthCoefficient` | def | [AKLT/Defs/Kernel.lean:105](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:105) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.shiftKernel` | def | [AKLT/Defs/Kernel.lean:111](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:111) | [d:kernel](#latex-d-kernel) |
| `AKLT.Defs.shiftedKernel` | def | [AKLT/Defs/Kernel.lean:115](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:115) | [d:kernel](#latex-d-kernel), [l:Mtheta](#latex-l-Mtheta) |
| `AKLT.Defs.kernelPartialRow` | def | [AKLT/Defs/Kernel.lean:119](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:119) | [h:H3](#latex-h-H3) |
| `AKLT.Defs.PositiveVectorBound` | def | [AKLT/Defs/Kernel.lean:125](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Kernel.lean:125) | [h:H3](#latex-h-H3) |
| `AKLT.Defs.Vec3` | abbrev | [AKLT/Defs/Moment.lean:9](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:9) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.dot` | def | [AKLT/Defs/Moment.lean:12](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:12) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.normSq` | def | [AKLT/Defs/Moment.lean:15](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:15) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.UnitVector` | abbrev | [AKLT/Defs/Moment.lean:18](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:18) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.BallVector` | abbrev | [AKLT/Defs/Moment.lean:21](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:21) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.goldenRatio` | def | [AKLT/Defs/Moment.lean:24](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:24) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.icoRadius` | def | [AKLT/Defs/Moment.lean:27](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:27) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.IcoLetter` | abbrev | [AKLT/Defs/Moment.lean:30](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:30) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.signValue` | def | [AKLT/Defs/Moment.lean:33](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:33) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.icoVector` | def | [AKLT/Defs/Moment.lean:36](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:36) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.icoSet` | def | [AKLT/Defs/Moment.lean:44](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:44) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.moment` | def | [AKLT/Defs/Moment.lean:47](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:47) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.Status` | inductive | [AKLT/Defs/Moment.lean:50](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:50) | [d:domain](#latex-d-domain) |
| `AKLT.Defs.SpinLetter` | abbrev | [AKLT/Defs/Moment.lean:58](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:58) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.spinVector` | def | [AKLT/Defs/Moment.lean:61](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:61) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.spinWeight` | def | [AKLT/Defs/Moment.lean:67](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:67) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.siteFunctional` | def | [AKLT/Defs/Moment.lean:72](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:72) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.DegreeFour` | def | [AKLT/Defs/Moment.lean:76](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:76) | [l:moments](#latex-l-moments) |
| `AKLT.Defs.SeparateDegreeFour` | def | [AKLT/Defs/Moment.lean:79](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:79) | [l:moments](#latex-l-moments) |
| `AKLT.Defs.productFunctional` | def | [AKLT/Defs/Moment.lean:83](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Moment.lean:83) | [l:moments](#latex-l-moments) |
| `AKLT.Defs.Representation` | inductive | [AKLT/Defs/Operator.lean:10](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:10) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.patternDegree` | def | [AKLT/Defs/Operator.lean:17](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:17) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.SingleReplacement` | def | [AKLT/Defs/Operator.lean:21](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:21) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.reducedSpinSites` | def | [AKLT/Defs/Operator.lean:25](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:25) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.reductionGroups` | def | [AKLT/Defs/Operator.lean:31](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:31) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.groupLeader` | def | [AKLT/Defs/Operator.lean:35](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:35) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.groupSecond` | def | [AKLT/Defs/Operator.lean:41](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:41) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.groupIsPair` | def | [AKLT/Defs/Operator.lean:44](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:44) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.reductionVectors` | def | [AKLT/Defs/Operator.lean:49](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:49) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.replacementRadius` | def | [AKLT/Defs/Operator.lean:54](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:54) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.leafNeighbour` | def | [AKLT/Defs/Operator.lean:58](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:58) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.LocalVariable` | abbrev | [AKLT/Defs/Operator.lean:63](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:63) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.formalDot` | def | [AKLT/Defs/Operator.lean:66](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:66) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.rationalMoment` | def | [AKLT/Defs/Operator.lean:70](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:70) | [l:moments](#latex-l-moments) |
| `AKLT.Defs.rationalStatusMoment` | def | [AKLT/Defs/Operator.lean:77](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:77) | [l:moments](#latex-l-moments) |
| `AKLT.Defs.contractSpins` | def | [AKLT/Defs/Operator.lean:81](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:81) | [l:moments](#latex-l-moments) |
| `AKLT.Defs.reducedIntegrand` | def | [AKLT/Defs/Operator.lean:91](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:91) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.reducedPolynomial` | def | [AKLT/Defs/Operator.lean:106](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:106) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.reducedDifference` | def | [AKLT/Defs/Operator.lean:112](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:112) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.VectorAffine` | def | [AKLT/Defs/Operator.lean:117](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:117) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.invertPolynomial` | def | [AKLT/Defs/Operator.lean:121](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:121) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.GroupInversion` | def | [AKLT/Defs/Operator.lean:127](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:127) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.pauliExponent` | def | [AKLT/Defs/Operator.lean:132](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:132) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.pauliOperator` | def | [AKLT/Defs/Operator.lean:137](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:137) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.ratComplexMul` | def | [AKLT/Defs/Operator.lean:143](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:143) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.rationalPauli` | def | [AKLT/Defs/Operator.lean:146](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:146) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.rationalOperatorEntry` | def | [AKLT/Defs/Operator.lean:153](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:153) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.ExchangeSigns` | abbrev | [AKLT/Defs/Operator.lean:160](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:160) | [d:exchange](#latex-d-exchange) |
| `AKLT.Defs.GroupBasis` | def | [AKLT/Defs/Operator.lean:163](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:163) | [d:exchange](#latex-d-exchange) |
| `AKLT.Defs.ExchangeBasis` | abbrev | [AKLT/Defs/Operator.lean:171](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:171) | [d:exchange](#latex-d-exchange) |
| `AKLT.Defs.exchangeWeight` | def | [AKLT/Defs/Operator.lean:175](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:175) | [d:exchange](#latex-d-exchange) |
| `AKLT.Defs.centralWeight` | def | [AKLT/Defs/Operator.lean:183](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:183) | [d:exchange](#latex-d-exchange) |
| `AKLT.Defs.CentralBasis` | abbrev | [AKLT/Defs/Operator.lean:187](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:187) | [d:exchange](#latex-d-exchange) |
| `AKLT.Defs.exchangeBasisVector` | def | [AKLT/Defs/Operator.lean:196](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:196) | [d:exchange](#latex-d-exchange) |
| `AKLT.Defs.rationalSectorEntry` | def | [AKLT/Defs/Operator.lean:213](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:213) | [l:integercheck](#latex-l-integercheck) |
| `AKLT.Defs.ClearsDenominator` | def | [AKLT/Defs/Operator.lean:219](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:219) | [l:integercheck](#latex-l-integercheck) |
| `AKLT.Defs.integerSectorMatrix` | def | [AKLT/Defs/Operator.lean:224](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:224) | [l:integercheck](#latex-l-integercheck) |
| `AKLT.Defs.thresholdSectorMatrix` | def | [AKLT/Defs/Operator.lean:231](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:231) | [l:integercheck](#latex-l-integercheck) |
| `AKLT.Defs.gramResidual` | def | [AKLT/Defs/Operator.lean:238](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:238) | [l:gram-residual](#latex-l-gram-residual) |
| `AKLT.Defs.GramResidualRows` | def | [AKLT/Defs/Operator.lean:242](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Operator.lean:242) | [l:gram-residual](#latex-l-gram-residual) |
| `AKLT.Defs.supportSpins` | def | [AKLT/Defs/OperatorContracts.lean:9](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:9) | [l:Iw](#latex-l-Iw) |
| `AKLT.Defs.withoutPassageFunctional` | def | [AKLT/Defs/OperatorContracts.lean:13](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:13) | [l:Iw](#latex-l-Iw) |
| `AKLT.Defs.originalPatternPolynomial` | def | [AKLT/Defs/OperatorContracts.lean:24](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:24) | [l:Iw](#latex-l-Iw) |
| `AKLT.Defs.coveredSiteField` | def | [AKLT/Defs/OperatorContracts.lean:32](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:32) | [l:leaf](#latex-l-leaf) |
| `AKLT.Defs.SupportedVectors` | def | [AKLT/Defs/OperatorContracts.lean:36](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:36) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.complexSectorMatrix` | def | [AKLT/Defs/OperatorContracts.lean:40](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:40) | [l:integercheck](#latex-l-integercheck) |
| `AKLT.Defs.indexedSectorMatrix` | def | [AKLT/Defs/OperatorContracts.lean:49](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:49) | [l:integercheck](#latex-l-integercheck) |
| `AKLT.Defs.leaderToken` | def | [AKLT/Defs/OperatorContracts.lean:55](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:55) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.secondToken` | def | [AKLT/Defs/OperatorContracts.lean:62](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:62) | [d:reduction](#latex-d-reduction) |
| `AKLT.Defs.exchangeOperator` | def | [AKLT/Defs/OperatorContracts.lean:69](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:69) | [d:exchange](#latex-d-exchange) |
| `AKLT.Defs.symmetricPairProjection` | def | [AKLT/Defs/OperatorContracts.lean:74](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:74) | [d:exchange](#latex-d-exchange) |
| `AKLT.Defs.tensorPowerMatrix` | def | [AKLT/Defs/OperatorContracts.lean:79](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:79) | [d:Pauli](#latex-d-Pauli) |
| `AKLT.Defs.leadingMinor` | def | [AKLT/Defs/OperatorContracts.lean:83](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:83) | [l:integercheck](#latex-l-integercheck) |
| `AKLT.Defs.bareissState` | def | [AKLT/Defs/OperatorContracts.lean:88](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:88) | [l:integercheck](#latex-l-integercheck) |
| `AKLT.Defs.bareissPivot` | def | [AKLT/Defs/OperatorContracts.lean:100](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/OperatorContracts.lean:100) | [l:integercheck](#latex-l-integercheck) |
| `AKLT.Defs.templateSites` | def | [AKLT/Defs/Pattern.lean:9](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:9) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.templateTips` | def | [AKLT/Defs/Pattern.lean:12](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:12) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.templateCorners` | def | [AKLT/Defs/Pattern.lean:15](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:15) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.externalSlot` | def | [AKLT/Defs/Pattern.lean:18](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:18) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.PatternData` | structure | [AKLT/Defs/Pattern.lean:27](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:27) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.PatternData.statusAt` | def | [AKLT/Defs/Pattern.lean:33](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:33) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.PatternData.keptAt` | def | [AKLT/Defs/Pattern.lean:37](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:37) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.PatternData.Covered` | def | [AKLT/Defs/Pattern.lean:41](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:41) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.PatternData.bonds` | def | [AKLT/Defs/Pattern.lean:60](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:60) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.PatternData.active` | def | [AKLT/Defs/Pattern.lean:67](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:67) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.PatternData.spins` | def | [AKLT/Defs/Pattern.lean:71](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:71) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.patternFunctional` | def | [AKLT/Defs/Pattern.lean:76](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:76) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.patternCurrent` | def | [AKLT/Defs/Pattern.lean:90](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:90) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.patternNext` | def | [AKLT/Defs/Pattern.lean:94](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:94) | [d:pattern](#latex-d-pattern) |
| `AKLT.Defs.LocalPatternBound` | def | [AKLT/Defs/Pattern.lean:98](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Pattern.lean:98) | [h:H1](#latex-h-H1) |
| `AKLT.Defs.PinAssignment` | abbrev | [AKLT/Defs/PinModel.lean:9](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/PinModel.lean:9) | [d:pinmodel](#latex-d-pinmodel) |
| `AKLT.Defs.extendIcoSpins` | def | [AKLT/Defs/PinModel.lean:12](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/PinModel.lean:12) | [d:pinmodel](#latex-d-pinmodel) |
| `AKLT.Defs.pinnedSum` | def | [AKLT/Defs/PinModel.lean:16](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/PinModel.lean:16) | [d:pinmodel](#latex-d-pinmodel) |
| `AKLT.Defs.freeSum` | def | [AKLT/Defs/PinModel.lean:25](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/PinModel.lean:25) | [d:pinmodel](#latex-d-pinmodel) |
| `AKLT.Defs.pinnedExpectation` | def | [AKLT/Defs/PinModel.lean:31](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/PinModel.lean:31) | [d:pinmodel](#latex-d-pinmodel) |
| `AKLT.Defs.freeExpectation` | def | [AKLT/Defs/PinModel.lean:35](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/PinModel.lean:35) | [d:pinmodel](#latex-d-pinmodel) |
| `AKLT.Defs.partitionRatio` | def | [AKLT/Defs/PinModel.lean:39](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/PinModel.lean:39) | [d:pinmodel](#latex-d-pinmodel) |
| `AKLT.Defs.ResponseProperty` | def | [AKLT/Defs/PinModel.lean:44](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/PinModel.lean:44) | [h:P](#latex-h-P) |
| `AKLT.Defs.cutCost` | def | [AKLT/Defs/PinModel.lean:56](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/PinModel.lean:56) | [t:cutMOS](#latex-t-cutMOS) |
| `AKLT.Defs.cutProbability` | def | [AKLT/Defs/PinModel.lean:61](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/PinModel.lean:61) | [t:cutMOS](#latex-t-cutMOS) |
| `AKLT.Defs.BinaryForm` | abbrev | [AKLT/Defs/Polynomial.lean:10](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Polynomial.lean:10) | [d:poly](#latex-d-poly) |
| `AKLT.Defs.binaryNormSq` | def | [AKLT/Defs/Polynomial.lean:13](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Polynomial.lean:13) | [d:poly](#latex-d-poly) |
| `AKLT.Defs.binaryEval` | def | [AKLT/Defs/Polynomial.lean:17](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Polynomial.lean:17) | [d:poly](#latex-d-poly) |
| `AKLT.Defs.binaryPolynomial` | def | [AKLT/Defs/Polynomial.lean:21](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Polynomial.lean:21) | [d:poly](#latex-d-poly) |
| `AKLT.Defs.binaryActionPolynomial` | def | [AKLT/Defs/Polynomial.lean:26](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Polynomial.lean:26) | [d:poly](#latex-d-poly) |
| `AKLT.Defs.physicalEval` | def | [AKLT/Defs/Polynomial.lean:33](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Polynomial.lean:33) | [d:poly](#latex-d-poly) |
| `AKLT.Defs.hamiltonian` | abbrev | [AKLT/Defs/Polynomial.lean:40](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Polynomial.lean:40) | [d:model](#latex-d-model) |
| `AKLT.Defs.vbs` | abbrev | [AKLT/Defs/Polynomial.lean:43](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Polynomial.lean:43) | [d:model](#latex-d-model) |
| `AKLT.Defs.Weight` | abbrev | [AKLT/Defs/Probability.lean:9](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:9) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.normalize` | def | [AKLT/Defs/Probability.lean:12](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:12) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.PositiveProbability` | def | [AKLT/Defs/Probability.lean:16](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:16) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.Probability` | def | [AKLT/Defs/Probability.lean:20](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:20) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.expectation` | def | [AKLT/Defs/Probability.lean:24](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:24) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.totalVariation` | def | [AKLT/Defs/Probability.lean:28](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:28) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.complexMean` | def | [AKLT/Defs/Probability.lean:32](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:32) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.variance` | def | [AKLT/Defs/Probability.lean:36](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:36) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.AgreeOutside` | def | [AKLT/Defs/Probability.lean:40](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:40) | [l:CE](#latex-l-CE) |
| `AKLT.Defs.conditionalExpectation` | def | [AKLT/Defs/Probability.lean:44](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:44) | [l:CE](#latex-l-CE) |
| `AKLT.Defs.conditionalVariance` | def | [AKLT/Defs/Probability.lean:53](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:53) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.blockDirichlet` | def | [AKLT/Defs/Probability.lean:62](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:62) | [l:CE](#latex-l-CE) |
| `AKLT.Defs.dirichlet` | def | [AKLT/Defs/Probability.lean:68](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:68) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.PoincareLower` | def | [AKLT/Defs/Probability.lean:74](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:74) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.heatBathGap` | def | [AKLT/Defs/Probability.lean:79](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:79) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.hamming` | def | [AKLT/Defs/Probability.lean:85](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:85) | [d:moment](#latex-d-moment) |
| `AKLT.Defs.Coupling` | structure | [AKLT/Defs/Probability.lean:91](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Probability.lean:91) | [d:framemodel](#latex-d-framemodel) |
| `AKLT.Defs.torusNeighbours` | def | [AKLT/Defs/Quantum.lean:10](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Quantum.lean:10) | [p:toruskernel](#latex-p-toruskernel) |
| `AKLT.Defs.polynomialState` | def | [AKLT/Defs/Quantum.lean:14](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Quantum.lean:14) | [d:poly](#latex-d-poly) |
| `AKLT.Defs.reorientedB` | def | [AKLT/Defs/Quantum.lean:19](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Quantum.lean:19) | [p:toruskernel](#latex-p-toruskernel) |
| `AKLT.Defs.StarHilbert` | abbrev | [AKLT/Defs/Quantum.lean:23](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Quantum.lean:23) | [l:star](#latex-l-star) |
| `AKLT.Defs.starAtSite` | def | [AKLT/Defs/Quantum.lean:26](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Quantum.lean:26) | [l:star](#latex-l-star) |
| `AKLT.Defs.starCasimir` | def | [AKLT/Defs/Quantum.lean:30](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Quantum.lean:30) | [l:star](#latex-l-star) |
| `AKLT.Defs.starHamiltonian` | def | [AKLT/Defs/Quantum.lean:38](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Quantum.lean:38) | [l:star](#latex-l-star) |
| `AKLT.Defs.starGap` | def | [AKLT/Defs/Quantum.lean:42](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Quantum.lean:42) | [l:star](#latex-l-star) |
| `AKLT.Defs.siteHamiltonian` | def | [AKLT/Defs/Quantum.lean:45](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Quantum.lean:45) | [l:star](#latex-l-star) |
| `AKLT.Defs.EventualMain` | def | [AKLT/Defs/Quantum.lean:49](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Quantum.lean:49) | [t:mainW](#latex-t-mainW) |
| `AKLT.Defs.logarithmicMean` | def | [AKLT/Defs/Response.lean:9](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:9) | [l:log-mean-bounds](#latex-l-log-mean-bounds) |
| `AKLT.Defs.reciprocalLogMean` | def | [AKLT/Defs/Response.lean:12](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:12) | [l:log-mean-bounds](#latex-l-log-mean-bounds) |
| `AKLT.Defs.logMeanLower` | def | [AKLT/Defs/Response.lean:15](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:15) | [l:log-mean-bounds](#latex-l-log-mean-bounds) |
| `AKLT.Defs.logMeanUpper` | def | [AKLT/Defs/Response.lean:20](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:20) | [l:log-mean-bounds](#latex-l-log-mean-bounds) |
| `AKLT.Defs.removeSite` | def | [AKLT/Defs/Response.lean:25](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:25) | [d:ratios](#latex-d-ratios) |
| `AKLT.Defs.stepRatio` | def | [AKLT/Defs/Response.lean:29](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:29) | [d:ratios](#latex-d-ratios) |
| `AKLT.Defs.removedPairMean` | def | [AKLT/Defs/Response.lean:33](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:33) | [d:ratios](#latex-d-ratios) |
| `AKLT.Defs.responseI` | def | [AKLT/Defs/Response.lean:38](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:38) | [d:ratios](#latex-d-ratios) |
| `AKLT.Defs.responseJ` | def | [AKLT/Defs/Response.lean:44](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:44) | [d:ratios](#latex-d-ratios) |
| `AKLT.Defs.responseBeta` | def | [AKLT/Defs/Response.lean:48](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:48) | [l:response](#latex-l-response) |
| `AKLT.Defs.responseAlpha` | def | [AKLT/Defs/Response.lean:53](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:53) | [l:response](#latex-l-response) |
| `AKLT.Defs.responseBetaPrime` | def | [AKLT/Defs/Response.lean:58](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:58) | [l:response](#latex-l-response) |
| `AKLT.Defs.normalizeRotation` | def | [AKLT/Defs/Response.lean:63](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:63) | [l:local](#latex-l-local) |
| `AKLT.Defs.CoveredDeparture` | def | [AKLT/Defs/Response.lean:69](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Response.lean:69) | [l:local](#latex-l-local) |
| `AKLT.Defs.inducedBoundary` | def | [AKLT/Defs/Specification.lean:10](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Specification.lean:10) | [l:planeenergy](#latex-l-planeenergy) |
| `AKLT.Defs.conditionalPlaneLaw` | def | [AKLT/Defs/Specification.lean:15](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Specification.lean:15) | [l:planeenergy](#latex-l-planeenergy) |
| `AKLT.Defs.conditionalTorusLaw` | def | [AKLT/Defs/Specification.lean:21](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Specification.lean:21) | [l:planeenergy](#latex-l-planeenergy) |
| `AKLT.Defs.sitesInVolume` | def | [AKLT/Defs/Specification.lean:27](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Specification.lean:27) | [l:planeenergy](#latex-l-planeenergy) |
| `AKLT.Defs.ParallelClearance` | def | [AKLT/Defs/Specification.lean:31](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Specification.lean:31) | [l:shellgeom](#latex-l-shellgeom) |
| `AKLT.Defs.Phase` | inductive | [AKLT/Defs/Stationary.lean:10](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:10) | [d:phaseweights](#latex-d-phaseweights) |
| `AKLT.Defs.phaseTerminal` | def | [AKLT/Defs/Stationary.lean:17](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:17) | [d:phaseweights](#latex-d-phaseweights) |
| `AKLT.Defs.phaseInitial` | def | [AKLT/Defs/Stationary.lean:20](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:20) | [d:phaseweights](#latex-d-phaseweights) |
| `AKLT.Defs.phaseDiagonal` | def | [AKLT/Defs/Stationary.lean:23](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:23) | [d:phaseweights](#latex-d-phaseweights) |
| `AKLT.Defs.phaseTransition` | def | [AKLT/Defs/Stationary.lean:31](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:31) | [d:phaseweights](#latex-d-phaseweights) |
| `AKLT.Defs.relaxedReward` | def | [AKLT/Defs/Stationary.lean:37](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:37) | [d:stationary-walk](#latex-d-stationary-walk) |
| `AKLT.Defs.freeCoefficient` | def | [AKLT/Defs/Stationary.lean:47](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:47) | [d:stationary-walk](#latex-d-stationary-walk) |
| `AKLT.Defs.stationaryCoefficient` | def | [AKLT/Defs/Stationary.lean:53](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:53) | [d:stationary-walk](#latex-d-stationary-walk) |
| `AKLT.Defs.stationaryApply` | def | [AKLT/Defs/Stationary.lean:64](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:64) | [d:stationary-walk](#latex-d-stationary-walk) |
| `AKLT.Defs.freeApply` | def | [AKLT/Defs/Stationary.lean:70](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:70) | [d:stationary-walk](#latex-d-stationary-walk) |
| `AKLT.Defs.certificateRadius` | def | [AKLT/Defs/Stationary.lean:75](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:75) | [d:stationary-certificate](#latex-d-stationary-certificate) |
| `AKLT.Defs.certificateValueScale` | def | [AKLT/Defs/Stationary.lean:78](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:78) | [d:stationary-certificate](#latex-d-stationary-certificate) |
| `AKLT.Defs.certificateCoefficientScale` | def | [AKLT/Defs/Stationary.lean:81](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:81) | [d:stationary-certificate](#latex-d-stationary-certificate) |
| `AKLT.Defs.coefficientCeiling` | def | [AKLT/Defs/Stationary.lean:84](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:84) | [d:stationary-certificate](#latex-d-stationary-certificate) |
| `AKLT.Defs.StationaryData` | structure | [AKLT/Defs/Stationary.lean:87](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:87) | [d:stationary-certificate](#latex-d-stationary-certificate) |
| `AKLT.Defs.StationaryData.extended` | def | [AKLT/Defs/Stationary.lean:92](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:92) | [d:stationary-certificate](#latex-d-stationary-certificate) |
| `AKLT.Defs.StationaryData.potential` | def | [AKLT/Defs/Stationary.lean:98](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:98) | [d:stationary-certificate](#latex-d-stationary-certificate) |
| `AKLT.Defs.StationaryData.Passes` | def | [AKLT/Defs/Stationary.lean:103](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:103) | [d:stationary-certificate](#latex-d-stationary-certificate) |
| `AKLT.Defs.prefixPhases` | def | [AKLT/Defs/Stationary.lean:121](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:121) | [d:prefix-bound](#latex-d-prefix-bound) |
| `AKLT.Defs.FirstDirection` | def | [AKLT/Defs/Stationary.lean:128](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:128) | [d:prefix-bound](#latex-d-prefix-bound) |
| `AKLT.Defs.SurvivingPrefix` | def | [AKLT/Defs/Stationary.lean:132](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:132) | [d:prefix-bound](#latex-d-prefix-bound) |
| `AKLT.Defs.firstDirectionPartialRow` | def | [AKLT/Defs/Stationary.lean:137](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:137) | [d:prefix-bound](#latex-d-prefix-bound) |
| `AKLT.Defs.stationaryPrefixBound` | def | [AKLT/Defs/Stationary.lean:144](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:144) | [d:prefix-bound](#latex-d-prefix-bound) |
| `AKLT.Defs.stationaryCases` | def | [AKLT/Defs/Stationary.lean:153](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:153) | [p:stationary-check](#latex-p-stationary-check) |
| `AKLT.Defs.stationaryPrefixCeiling` | def | [AKLT/Defs/Stationary.lean:157](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Stationary.lean:157) | [p:stationary-check](#latex-p-stationary-check) |
| `AKLT.Defs.localThreshold` | def | [AKLT/Defs/Trails.lean:9](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:9) | [d:weights](#latex-d-weights) |
| `AKLT.Defs.passageFactor` | def | [AKLT/Defs/Trails.lean:12](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:12) | [d:weights](#latex-d-weights) |
| `AKLT.Defs.alphaBound` | def | [AKLT/Defs/Trails.lean:15](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:15) | [l:log-mean-bounds](#latex-l-log-mean-bounds) |
| `AKLT.Defs.betaBound` | def | [AKLT/Defs/Trails.lean:18](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:18) | [l:log-mean-bounds](#latex-l-log-mean-bounds) |
| `AKLT.Defs.betaPrimeBound` | def | [AKLT/Defs/Trails.lean:21](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:21) | [l:log-mean-bounds](#latex-l-log-mean-bounds) |
| `AKLT.Defs.DirectionWord` | abbrev | [AKLT/Defs/Trails.lean:24](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:24) | [d:weights](#latex-d-weights) |
| `AKLT.Defs.wordVertex` | def | [AKLT/Defs/Trails.lean:27](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:27) | [d:weights](#latex-d-weights) |
| `AKLT.Defs.wordBond` | def | [AKLT/Defs/Trails.lean:31](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:31) | [d:weights](#latex-d-weights) |
| `AKLT.Defs.IsTrail` | def | [AKLT/Defs/Trails.lean:35](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:35) | [d:weights](#latex-d-weights) |
| `AKLT.Defs.wordIncoming` | def | [AKLT/Defs/Trails.lean:39](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:39) | [d:weights](#latex-d-weights) |
| `AKLT.Defs.wordStraight` | def | [AKLT/Defs/Trails.lean:43](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:43) | [d:weights](#latex-d-weights) |
| `AKLT.Defs.departureCount` | def | [AKLT/Defs/Trails.lean:47](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:47) | [d:weights](#latex-d-weights) |
| `AKLT.Defs.wordRevisit` | def | [AKLT/Defs/Trails.lean:51](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:51) | [d:weights](#latex-d-weights) |
| `AKLT.Defs.trailWeight` | def | [AKLT/Defs/Trails.lean:55](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:55) | [d:weights](#latex-d-weights) |
| `AKLT.Defs.trailBaseWeight` | def | [AKLT/Defs/Trails.lean:59](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:59) | [d:weights](#latex-d-weights) |
| `AKLT.Defs.OpenTrailBound` | def | [AKLT/Defs/Trails.lean:63](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:63) | [h:H2](#latex-h-H2) |
| `AKLT.Defs.certifiedRate` | def | [AKLT/Defs/Trails.lean:72](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:72) | [t:inputs](#latex-t-inputs) |
| `AKLT.Defs.wordVertices` | def | [AKLT/Defs/Trails.lean:75](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:75) | [d:trace](#latex-d-trace) |
| `AKLT.Defs.StoppedNetworkTrail` | def | [AKLT/Defs/Trails.lean:80](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:80) | [d:trace](#latex-d-trace) |
| `AKLT.Defs.stoppedNetworkTrails` | def | [AKLT/Defs/Trails.lean:88](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:88) | [d:trace](#latex-d-trace) |
| `AKLT.Defs.AdmissibleTarget` | def | [AKLT/Defs/Trails.lean:94](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Defs/Trails.lean:94) | [p:pairwalk](#latex-p-pairwalk) |
| `AKLT.Blueprint.Top.mainV2_of_parts` | theorem | [AKLT/Blueprint/Top/Assembly.lean:12](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Assembly.lean:12) | [t:main](#latex-t-main) |
| `AKLT.Blueprint.Top.LogMeanBoundsStatement` | def | [AKLT/Blueprint/Top/Coefficients.lean:11](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Coefficients.lean:11) | [l:log-mean-bounds](#latex-l-log-mean-bounds) |
| `AKLT.Blueprint.Top.ResponseStatement` | def | [AKLT/Blueprint/Top/Coefficients.lean:31](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Coefficients.lean:31) | [l:response](#latex-l-response) |
| `AKLT.Blueprint.Top.ResponseTypedStatement` | def | [AKLT/Blueprint/Top/Coefficients.lean:55](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Coefficients.lean:55) | [l:response-typed](#latex-l-response-typed) |
| `AKLT.Blueprint.Top.MomentsStatement` | def | [AKLT/Blueprint/Top/Common.lean:13](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Common.lean:13) | [l:moments](#latex-l-moments) |
| `AKLT.Blueprint.Top.FiniteFactsStatement` | def | [AKLT/Blueprint/Top/Common.lean:32](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Common.lean:32) | [l:finitefacts](#latex-l-finitefacts) |
| `AKLT.Blueprint.Top.ThreeFactorMeanStatement` | def | [AKLT/Blueprint/Top/Common.lean:52](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Common.lean:52) | [l:35](#latex-l-35) |
| `AKLT.Blueprint.Top.ExactStatement` | def | [AKLT/Blueprint/Top/Common.lean:61](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Common.lean:61) | [l:exact](#latex-l-exact) |
| `AKLT.Blueprint.Top.ALMStatement` | def | [AKLT/Blueprint/Top/Computation.lean:11](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:11) | [l:alm](#latex-l-alm) |
| `AKLT.Blueprint.Top.H2DihedralStatement` | def | [AKLT/Blueprint/Top/Computation.lean:23](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:23) | [l:H2-dihedral](#latex-l-H2-dihedral) |
| `AKLT.Blueprint.Top.H2TestStatement` | def | [AKLT/Blueprint/Top/Computation.lean:39](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:39) | [p:H2-test](#latex-p-H2-test) |
| `AKLT.Blueprint.Top.H2CVStatement` | def | [AKLT/Blueprint/Top/Computation.lean:54](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:54) | [l:H2-CV](#latex-l-H2-CV) |
| `AKLT.Blueprint.Top.AutomatonQuotientStatement` | def | [AKLT/Blueprint/Top/Computation.lean:65](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:65) | [l:automaton-quotient](#latex-l-automaton-quotient) |
| `AKLT.Blueprint.Top.Automaton10Statement` | def | [AKLT/Blueprint/Top/Computation.lean:79](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:79) | [p:automaton10](#latex-p-automaton10) |
| `AKLT.Blueprint.Top.PhaseExpansionStatement` | def | [AKLT/Blueprint/Top/Computation.lean:87](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:87) | [l:phase-expansion](#latex-l-phase-expansion) |
| `AKLT.Blueprint.Top.StationaryDominationStatement` | def | [AKLT/Blueprint/Top/Computation.lean:98](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:98) | [l:stationary-domination](#latex-l-stationary-domination) |
| `AKLT.Blueprint.Top.BellmanSoundnessStatement` | def | [AKLT/Blueprint/Top/Computation.lean:113](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:113) | [l:Bellman-soundness](#latex-l-Bellman-soundness) |
| `AKLT.Blueprint.Top.StationaryLocalGlobalStatement` | def | [AKLT/Blueprint/Top/Computation.lean:123](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:123) | [l:stationary-local-global](#latex-l-stationary-local-global) |
| `AKLT.Blueprint.Top.PrefixDominationStatement` | def | [AKLT/Blueprint/Top/Computation.lean:136](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:136) | [l:prefix-domination](#latex-l-prefix-domination) |
| `AKLT.Blueprint.Top.KernelReflectionStatement` | def | [AKLT/Blueprint/Top/Computation.lean:143](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:143) | [l:kernel-reflection](#latex-l-kernel-reflection) |
| `AKLT.Blueprint.Top.StationaryCheckStatement` | def | [AKLT/Blueprint/Top/Computation.lean:161](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:161) | [p:stationary-check](#latex-p-stationary-check) |
| `AKLT.Blueprint.Top.StationaryAssemblyStatement` | def | [AKLT/Blueprint/Top/Computation.lean:170](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Computation.lean:170) | [l:stationary-assembly](#latex-l-stationary-assembly) |
| `AKLT.Blueprint.Top.IntegratePassageStatement` | def | [AKLT/Blueprint/Top/Operator.lean:12](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Operator.lean:12) | [l:Iw](#latex-l-Iw) |
| `AKLT.Blueprint.Top.LeafStatement` | def | [AKLT/Blueprint/Top/Operator.lean:37](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Operator.lean:37) | [l:leaf](#latex-l-leaf) |
| `AKLT.Blueprint.Top.ReduceStatement` | def | [AKLT/Blueprint/Top/Operator.lean:48](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Operator.lean:48) | [c:reduce](#latex-c-reduce) |
| `AKLT.Blueprint.Top.InversionStatement` | def | [AKLT/Blueprint/Top/Operator.lean:63](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Operator.lean:63) | [l:inversion](#latex-l-inversion) |
| `AKLT.Blueprint.Top.OperatorStructureStatement` | def | [AKLT/Blueprint/Top/Operator.lean:75](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Operator.lean:75) | [l:Ostruct](#latex-l-Ostruct) |
| `AKLT.Blueprint.Top.SectorStatement` | def | [AKLT/Blueprint/Top/Operator.lean:93](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Operator.lean:93) | [l:sector](#latex-l-sector) |
| `AKLT.Blueprint.Top.GramResidualStatement` | def | [AKLT/Blueprint/Top/Operator.lean:109](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Operator.lean:109) | [l:gram-residual](#latex-l-gram-residual) |
| `AKLT.Blueprint.Top.IntegerCheckStatement` | def | [AKLT/Blueprint/Top/Operator.lean:118](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Operator.lean:118) | [l:integercheck](#latex-l-integercheck) |
| `AKLT.Blueprint.Top.CertificateStatement` | def | [AKLT/Blueprint/Top/Operator.lean:142](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Operator.lean:142) | [p:certificate](#latex-p-certificate) |
| `AKLT.Blueprint.Top.ThreeFramesStatement` | def | [AKLT/Blueprint/Top/Quantum.lean:13](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Quantum.lean:13) | [l:threeframes](#latex-l-threeframes) |
| `AKLT.Blueprint.Top.TightStatement` | def | [AKLT/Blueprint/Top/Quantum.lean:32](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Quantum.lean:32) | [l:tight](#latex-l-tight) |
| `AKLT.Blueprint.Top.TorusKernelStatement` | def | [AKLT/Blueprint/Top/Quantum.lean:53](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Quantum.lean:53) | [p:toruskernel](#latex-p-toruskernel) |
| `AKLT.Blueprint.Top.StarStatement` | def | [AKLT/Blueprint/Top/Quantum.lean:62](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Quantum.lean:62) | [l:star](#latex-l-star) |
| `AKLT.Blueprint.Top.QDStatement` | def | [AKLT/Blueprint/Top/Quantum.lean:73](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Quantum.lean:73) | [t:QD](#latex-t-QD) |
| `AKLT.Blueprint.Top.PlaneEnergyStatement` | def | [AKLT/Blueprint/Top/Quantum.lean:82](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Quantum.lean:82) | [l:planeenergy](#latex-l-planeenergy) |
| `AKLT.Blueprint.Top.H1Statement` | def | [AKLT/Blueprint/Top/Response.lean:10](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Response.lean:10) | [h:H1](#latex-h-H1) |
| `AKLT.Blueprint.Top.H1TheoremStatement` | def | [AKLT/Blueprint/Top/Response.lean:13](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Response.lean:13) | [t:H1](#latex-t-H1) |
| `AKLT.Blueprint.Top.H2Statement` | def | [AKLT/Blueprint/Top/Response.lean:18](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Response.lean:18) | [h:H2](#latex-h-H2) |
| `AKLT.Blueprint.Top.H3Statement` | def | [AKLT/Blueprint/Top/Response.lean:21](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Response.lean:21) | [h:H3](#latex-h-H3) |
| `AKLT.Blueprint.Top.InputsStatement` | def | [AKLT/Blueprint/Top/Response.lean:25](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Response.lean:25) | [t:inputs](#latex-t-inputs) |
| `AKLT.Blueprint.Top.PStatement` | def | [AKLT/Blueprint/Top/Response.lean:30](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Response.lean:30) | [h:P](#latex-h-P) |
| `AKLT.Blueprint.Top.renewalAmplitude` | def | [AKLT/Blueprint/Top/Response.lean:33](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Response.lean:33) | [t:rec](#latex-t-rec) |
| `AKLT.Blueprint.Top.ShiftedWitness` | def | [AKLT/Blueprint/Top/Response.lean:39](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Response.lean:39) | [l:Mtheta](#latex-l-Mtheta) |
| `AKLT.Blueprint.Top.RecStatement` | def | [AKLT/Blueprint/Top/Response.lean:46](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Response.lean:46) | [t:rec](#latex-t-rec) |
| `AKLT.Blueprint.Top.MThetaStatement` | def | [AKLT/Blueprint/Top/Response.lean:53](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Response.lean:53) | [l:Mtheta](#latex-l-Mtheta) |
| `AKLT.Blueprint.Top.ShellGeometryStatement` | def | [AKLT/Blueprint/Top/Windows.lean:11](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Windows.lean:11) | [l:shellgeom](#latex-l-shellgeom) |
| `AKLT.Blueprint.Top.CutMOSStatement` | def | [AKLT/Blueprint/Top/Windows.lean:25](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Windows.lean:25) | [t:cutMOS](#latex-t-cutMOS) |
| `AKLT.Blueprint.Top.MainWStatement` | def | [AKLT/Blueprint/Top/Windows.lean:31](/home/ubuntu/aklt/wt/ARCH_0/AKLT/Blueprint/Top/Windows.lean:31) | [t:mainW](#latex-t-mainW) |

**Exported closed propositions, with their complete Lean statements.**

<details>
<summary>AKLT.Blueprint.Top.LogMeanBoundsStatement — l:log-mean-bounds</summary>

```lean
def LogMeanBoundsStatement : Prop :=
  reciprocalLogMean 1 = 1 ∧
  (∀ c : ℝ, 3 / 5 ≤ c → c ≤ 1 → ∀ x x' y y' : ℝ,
    0 < x → x ≤ x' → 0 < y → y ≤ y' →
    1 / (3 * logarithmicMean (c * x') y') - 1 / (5 * logarithmicMean x' y') ≤
      1 / (3 * logarithmicMean (c * x) y) - 1 / (5 * logarithmicMean x y)) ∧
  (∀ c x y : ℝ, 3 / 5 ≤ c → c ≤ 1 → 116 / 125 ≤ x → 1 ≤ y →
    1 / (3 * logarithmicMean (c * x) y) - 1 / (5 * logarithmicMean x y) ≤
      reciprocalLogMean ((116 / 125) * c) / 3 - reciprocalLogMean (116 / 125) / 5) ∧
  (∀ s : ℚ, 0 < s → s < 1 → (logMeanLower s : ℝ) ≤ reciprocalLogMean s ∧
    reciprocalLogMean s ≤ (logMeanUpper s : ℝ)) ∧
  ∀ straight : Bool,
    logMeanUpper ((116 / 125) * localThreshold straight) / 3 - logMeanLower (116 / 125) / 5 ≤
      alphaBound straight ∧
    logMeanUpper ((116 / 125) * localThreshold straight) / 3 ≤ betaBound straight ∧
    logMeanUpper (localThreshold straight) / 3 ≤ betaPrimeBound straight ∧
    0 < betaPrimeBound straight ∧ betaPrimeBound straight ≤ betaBound straight
```

</details>

<details>
<summary>AKLT.Blueprint.Top.ResponseStatement — l:response</summary>

```lean
def ResponseStatement : Prop :=
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ y : Plane, D.AdmissibleStart y → ∀ o ∈ D.presentNeighbours y,
    0 < stepRatio D τ false y o ∧ stepRatio D τ false y o ≤ 1 ∧
    0 < stepRatio D τ true y o ∧ stepRatio D τ true y o ≤ 12 / 5 ∧
    (D.status y = .D → stepRatio D τ true y o = 1 ∧ stepRatio D τ false y o = 1) ∧
    (D.status y = .U → (D.presentNeighbours y).card = 1 →
      stepRatio D τ true y o = 1 ∧ stepRatio D τ false y o = 1) ∧
    (∀ f : Plane, D.status y = .U → D.presentNeighbours y = {o, f} → o ≠ f →
      0 < responseBetaPrime D τ y o f ∧ responseBetaPrime D τ y o f ≤ 35510 / 100000 ∧
      Real.log (stepRatio D τ false y o) - Real.log (stepRatio D τ true y o) =
        responseBetaPrime D τ y o f *
          (removedPairMean D τ true y f o - removedPairMean D τ false y f o)) ∧
    ∀ f g : Plane, D.status y = .U → D.presentNeighbours y = {o, f, g} →
      o ≠ f → o ≠ g → f ≠ g →
      0 < responseAlpha D τ y o f g ∧ responseAlpha D τ y o f g ≤ 18094 / 100000 ∧
      0 < responseBeta D τ y o f g ∧ responseBeta D τ y o f g ≤ 36751 / 100000 ∧
      Real.log (stepRatio D τ false y o) - Real.log (stepRatio D τ true y o) =
        responseAlpha D τ y o f g * (removedPairMean D τ true y f g - removedPairMean D τ false y f g) +
        responseBeta D τ y o f g * ((removedPairMean D τ true y f o - removedPairMean D τ false y f o) +
          (removedPairMean D τ true y g o - removedPairMean D τ false y g o))
```

</details>

<details>
<summary>AKLT.Blueprint.Top.ResponseTypedStatement — l:response-typed</summary>

```lean
def ResponseTypedStatement : Prop :=
  H1Statement →
  (∀ straight : Bool, alphaBound straight ≤ 18094 / 100000 ∧
    betaBound straight ≤ 36751 / 100000 ∧ betaPrimeBound straight ≤ 36751 / 100000) ∧
  ∀ G : Finset Plane, ∀ τ : PinAssignment G, ∀ D : Network G, D.Auxiliary →
    ∀ y : Plane, D.AdmissibleStart y → D.status y = .U →
    ∀ incoming outgoing : Compass, CoveredDeparture D y incoming outgoing →
    let o := y + outgoing.step
    let straight := decide (outgoing = incoming)
    (∀ f : Plane, D.presentNeighbours y = {o, f} → o ≠ f →
      0 < responseBetaPrime D τ y o f ∧
      responseBetaPrime D τ y o f ≤ (betaPrimeBound straight : ℝ) ∧
      responseBetaPrime D τ y o f ≤ reciprocalLogMean (localThreshold straight : ℝ) / 3) ∧
    ∀ f g : Plane, D.presentNeighbours y = {o, f, g} → o ≠ f → o ≠ g → f ≠ g →
      0 < responseAlpha D τ y o f g ∧ responseAlpha D τ y o f g ≤ (alphaBound straight : ℝ) ∧
      0 < responseBeta D τ y o f g ∧ responseBeta D τ y o f g ≤ (betaBound straight : ℝ) ∧
      responseBeta D τ y o f g ≤ reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) / 3 ∧
      responseAlpha D τ y o f g ≤ reciprocalLogMean ((116 / 125) * (localThreshold straight : ℝ)) / 3 -
        reciprocalLogMean (116 / 125) / 5 ∧
      responseI D τ true y o f g ≥ (localThreshold straight : ℝ) * responseJ D τ true y f g ∧
      responseI D τ false y o f g ≥ responseJ D τ false y f g ∧
      responseJ D τ false y f g ≥ 1 ∧ responseJ D τ true y f g ≥ 116 / 125
```

</details>

<details>
<summary>AKLT.Blueprint.Top.MomentsStatement — l:moments</summary>

```lean
def MomentsStatement : Prop :=
  Function.Injective icoVector ∧ (∀ j, normSq (icoVector j) = 1) ∧
  (∀ j, ∃ k, icoVector k = -icoVector j) ∧ moment (fun _ => 1) = 1 ∧
  (∀ i, moment (fun n => n i) = 0) ∧
  (∀ i j k, moment (fun n => n i * n j * n k) = 0) ∧
  (∀ i j : Fin 3, moment (fun n => n i * n j) = if i = j then 1 / 3 else 0) ∧
  (∀ i j k l : Fin 3, moment (fun n => n i * n j * n k * n l) =
    ((if i = j ∧ k = l then 1 else 0) + (if i = k ∧ j = l then 1 else 0) +
      (if i = l ∧ j = k then 1 else 0)) / 15) ∧
  (∀ m : Fin 3 → ℕ, (∑ i, m i) ≤ 4 → ∀ s : Status, s = .U ∨ s = .D →
    siteFunctional s (fun n => ∏ i, n i ^ m i) = (rationalStatusMoment s m : ℝ)) ∧
  ∀ n : ℕ, ∀ s : Fin n → Status, (∀ x, s x = .U ∨ s x = .D) →
    ∀ p : MvPolynomial (Fin n × Fin 3) ℝ, SeparateDegreeFour p →
    ∀ R : Fin n → Matrix (Fin 3) (Fin 3) ℝ, (∀ x, (R x).transpose * R x = 1) →
    productFunctional s (fun a => MvPolynomial.eval (fun v => ((R v.1).mulVec (a v.1)) v.2) p) =
      productFunctional s (fun a => MvPolynomial.eval (fun v => a v.1 v.2) p)
```

</details>

<details>
<summary>AKLT.Blueprint.Top.FiniteFactsStatement — l:finitefacts</summary>

```lean
def FiniteFactsStatement : Prop :=
  (∀ s : Status, s = .U ∨ s = .D → ∀ j : SpinLetter,
    0 < spinWeight s j → normSq (spinVector j) ≤ 1) ∧
  ∀ n : ℕ, ∀ D : FiniteSpinNetwork n, D.Valid →
    0 < D.partition true (fun _ => 1) ∧ 0 < D.partition false (fun _ => 1) ∧
    (∀ pairs : List (Fin n × Fin n),
      (∀ x, (D.bonds.filter fun e => e.1 = x ∨ e.2 = x).card +
        (pairs.filter fun e => e.1 = x).length + (pairs.filter fun e => e.2 = x).length ≤ 4) →
      0 ≤ D.partition false (fun a => (pairs.map fun e => dot (a e.1) (a e.2)).prod)) ∧
    ∀ pinned : Bool, ∀ x y : Fin n, x ≠ y → (x, y) ∉ D.bonds → (y, x) ∉ D.bonds →
      ∀ σ : Fin n → SpinLetter,
      let E := fun τ : Fin n → SpinLetter => ∀ z, z ≠ x → z ≠ y → τ z = σ z
      let p := normalize (D.weight pinned)
      0 < eventMass p E → ∀ a b : SpinLetter,
        conditionalProbability p E (fun τ => τ x = a ∧ τ y = b) =
          conditionalProbability p E (fun τ => τ x = a) *
            conditionalProbability p E (fun τ => τ y = b)
```

</details>

<details>
<summary>AKLT.Blueprint.Top.ThreeFactorMeanStatement — l:35</summary>

```lean
def ThreeFactorMeanStatement : Prop :=
  (∀ k : ℕ, k ≤ 3 → ∀ a : Fin k → Vec3, (∀ j, normSq (a j) ≤ 1) →
    ∀ s : Status, s = .U ∨ s = .D →
      0 < siteFunctional s (localProduct a) ∧ normSq (localMean s a) ≤ (3 / 5 : ℝ)^2) ∧
  {b : Vec3 | ∃ a : Fin 3 → UnitVector, localMean .U (fun j => (a j).val) = b} =
    {b : Vec3 | normSq b ≤ (3 / 5 : ℝ)^2}
```

</details>

<details>
<summary>AKLT.Blueprint.Top.ExactStatement — l:exact</summary>

```lean
def ExactStatement : Prop :=
  ∀ n : ℕ, ∀ k : Fin n → ℕ, ∀ F : (x : Fin n) → FrameData (k x),
    (∀ x, MomentLaw (F x)) → ∀ s : Fin n → Status, (∀ x, s x = .U ∨ s x = .D) →
    ∀ p : MvPolynomial (Fin n × Fin 3) ℝ, SeparateDegreeFour p →
    let atom : (x : Fin n) → Option (Fin (k x)) → Vec3 := fun x j =>
      match j with | none => (0 : Vec3) | some i => (F x).point i
    let weight : (x : Fin n) → Option (Fin (k x)) → ℝ := fun x j =>
      match j with
      | none => if s x = .D then (2 / 5 : ℝ) else 0
      | some i => (if s x = .D then (3 / 5 : ℝ) else 1) * (F x).weight i
    (∑ a : (x : Fin n) → Option (Fin (k x)),
      (∏ x, weight x (a x)) * MvPolynomial.eval (fun v => atom v.1 (a v.1) v.2) p) =
      productFunctional s (fun a => MvPolynomial.eval (fun v => a v.1 v.2) p)
```

</details>

<details>
<summary>AKLT.Blueprint.Top.ALMStatement — l:alm</summary>

```lean
def ALMStatement : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∀ n : ℕ, m ≤ n → ∀ u : Plane, ∀ incoming : Compass, ∀ ω' : MemoryWindow m,
      memoryTrailMass m (n + 1) u incoming ω' ≤
        ∑ ω : MemoryWindow m, memoryTrailMass m n u incoming ω * memoryMatrix m ω ω') ∧
    ∀ v : MemoryWindow m → ℝ, (∀ ω, 0 < v ω) → ∀ q : ℝ, 0 < q → q < 1 →
      (∀ ω, (∑ ω', (memoryMatrix m ω ω' : ℝ) * v ω') ≤ q * v ω) →
      OpenTrailBound (memoryBaseConstant m q v) q ∧
      ∀ CV : ℝ, memoryBaseConstant m q v ≤ CV → OpenTrailBound CV q
```

</details>

<details>
<summary>AKLT.Blueprint.Top.H2DihedralStatement — l:H2-dihedral</summary>

```lean
def H2DihedralStatement : Prop :=
  (∀ m : ℕ, ∀ g : SquareSymmetry, ∀ w : DirectionWord m, RawWindow w →
    RawWindow (symmetryWord g w) ∧ ∀ d : Compass,
      (WindowAdmissible (symmetryWord g w) (symmetryDirection g d) ↔ WindowAdmissible w d) ∧
      windowKind (symmetryWord g w) (symmetryDirection g d) = windowKind w d ∧
      windowSuccessor (symmetryWord g w) (symmetryDirection g d) = symmetryWord g (windowSuccessor w d)) ∧
  Fintype.card (MemoryWindow 6) = 916 ∧
  ∃ reps : Fin 115 → MemoryWindow 6, Function.Injective reps ∧
    (∀ w : MemoryWindow 6, ∃! j : Fin 115, SameWindowOrbit w.val (reps j).val) ∧
    ∀ v : MemoryWindow 6 → ℝ,
      (∀ ω, 0 < v ω) → (∀ ω ω', SameWindowOrbit ω.val ω'.val → v ω = v ω') →
      ∀ q : ℝ, (∀ j, (∑ ω', (memoryMatrix 6 (reps j) ω' : ℝ) * v ω') ≤ q * v (reps j)) →
        ∀ ω, (∑ ω', (memoryMatrix 6 ω ω' : ℝ) * v ω') ≤ q * v ω
```

</details>

<details>
<summary>AKLT.Blueprint.Top.H2TestStatement — p:H2-test</summary>

```lean
def H2TestStatement : Prop :=
  (2695605 : ℚ) * kindWeight .straight = 935000 ∧
  (2695605 : ℚ) * kindWeight .turn = 961000 ∧
  (2695605 : ℚ) * kindWeight .revisit = 539121 ∧
  ∃ v : MemoryWindow 6 → ℤ, ∃ lo hi : ℤ,
    0 < lo ∧ (∀ ω, lo ≤ v ω ∧ v ω ≤ hi) ∧ (∃ ω, v ω = lo) ∧ (∃ ω, v ω = hi) ∧
    (hi : ℚ) / lo = 250000000000 / 46594269069 ∧ (hi : ℚ) / lo < 6 ∧
    (∀ ω ω', SameWindowOrbit ω.val ω'.val → v ω = v ω') ∧
    (∀ ω, (∑ ω', memoryMatrix 6 ω ω' * (v ω' : ℚ)) / (v ω : ℚ) ≤ certifiedRate) ∧
    (∃ ω, (∑ ω', memoryMatrix 6 ω ω' * (v ω' : ℚ)) / (v ω : ℚ) = certifiedRate) ∧
    (∀ ω, (1120437614225 : ℤ) *
      (∑ ω', ⌊(2695605 : ℚ) * memoryMatrix 6 ω ω'⌋ * v ω') ≤
        1119948287353 * 2695605 * v ω) ∧ certifiedRate < (2499 / 2500 : ℚ)
```

</details>

<details>
<summary>AKLT.Blueprint.Top.H2CVStatement — l:H2-CV</summary>

```lean
def H2CVStatement : Prop :=
  (∀ u : Plane, ∀ incoming : Compass, ∀ r : ℕ, r ≤ 6 →
    openTrailTotal r u incoming ≤ passageFactor false ^ r) ∧
  (6 * (200 / (187 * certifiedRate))^6 < (10 : ℚ)) ∧
  (∀ v : MemoryWindow 6 → ℝ, (∀ ω, 0 < v ω) → memoryWitnessRatio v ≤ 6 →
    memoryBaseConstant 6 (certifiedRate : ℝ) v ≤ 6 * (200 / (187 * (certifiedRate : ℝ)))^6 ∧
    memoryBaseConstant 6 (certifiedRate : ℝ) v < 10) ∧
  (H2TestStatement → H2Statement)
```

</details>

<details>
<summary>AKLT.Blueprint.Top.AutomatonQuotientStatement — l:automaton-quotient</summary>

```lean
def AutomatonQuotientStatement : Prop :=
  (∀ m q : ℕ, 1 ≤ m → ∀ π : DirectionWord m → Fin q, CompatibleProjection m q π →
    ∃ Q : MemoryQuotient m q, Q.Correct ∧ ∀ w, RawWindow w → Q.project w = π w) ∧
  ∀ m q : ℕ, 1 ≤ m → ∀ Q : MemoryQuotient m q, Q.Correct →
    (∀ w : DirectionWord m, RawWindow w → ∀ d : Compass, WindowAdmissible w d →
      RawWindow (windowSuccessor w d)) ∧
    ∀ p : ℕ, ∀ weight : Fin p → Fin p → StepKind → Compass → Compass → Plane → ℚ,
      (∀ φ ψ d a a' x, weight φ ψ .revisit d a x = weight φ ψ .revisit d a' x) →
      ∀ terminal : Plane → Bool, ∀ G : Fin p → Fin q → Plane → ℚ,
      ∀ R : ℕ, ∀ φ : Fin p, ∀ w : DirectionWord m, RawWindow w → ∀ x : Plane,
        ((rawBackward m p weight terminal)^[R]) (fun ψ ω y => G ψ (Q.project ω) y) φ w x =
          ((quotientBackward Q p weight terminal)^[R]) G φ (Q.project w) x
```

</details>

<details>
<summary>AKLT.Blueprint.Top.Automaton10Statement — p:automaton10</summary>

```lean
def Automaton10Statement : Prop :=
  Fintype.card (MemoryWindow 10) = 60092 ∧
  ∃ Q : MemoryQuotient 10 3741, Q.Correct ∧
    quotientEdgeCount Q .straight = 2516 ∧ quotientEdgeCount Q .turn = 5032 ∧
    quotientEdgeCount Q .revisit = 1872
```

</details>

<details>
<summary>AKLT.Blueprint.Top.PhaseExpansionStatement — l:phase-expansion</summary>

```lean
def PhaseExpansionStatement : Prop :=
  ∀ n : ℕ, ∀ w : DirectionWord n, IsTrail kernelStart kernelIncoming w →
    (∑ φ, prefixPhases w φ * phaseTerminal φ) =
      trailBaseWeight kernelStart w * exposureSum w (witnessKappa w) (longOrdering w) ∧
    ∀ L : ℕ, ∀ hL : L ≤ n,
      let initialWord : DirectionWord L := fun i => w ⟨i.val, Nat.lt_of_lt_of_le i.isLt hL⟩
      (∑ φ, prefixPhases w φ * phaseTerminal φ) =
        ∑ φ, prefixPhases initialWord φ * truePhaseSuffix w L φ
```

</details>

<details>
<summary>AKLT.Blueprint.Top.StationaryDominationStatement — l:stationary-domination</summary>

```lean
def StationaryDominationStatement : Prop :=
  (∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ n L : ℕ, 12 ≤ L → L ≤ n → ∀ w : DirectionWord n,
      ClosedTrail X w → SurvivingPrefix X d₀ (takeWord w L) →
      ∀ i : Fin n, L ≤ i.val → ∀ φ ψ : Phase,
        truePhaseCoefficient w i φ ψ ≤ stationaryCoefficient Q X d₀ φ
          (Q.project (lastWindowWord 10 (takeWord w i.val)))
          (wordVertex kernelStart w i.val) (w i) ψ) ∧
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ L : ℕ, 12 ≤ L → ∀ P : DirectionWord L, SurvivingPrefix X d₀ P → ∀ φ : Phase, ∀ R : ℕ,
      trueContinuationSum X P φ R ≤ stationaryContinuationSum Q X d₀ φ
        (Q.project (lastWindowWord 10 P)) (wordVertex kernelStart P L) R
```

</details>

<details>
<summary>AKLT.Blueprint.Top.BellmanSoundnessStatement — l:Bellman-soundness</summary>

```lean
def BellmanSoundnessStatement : Prop :=
  ∀ α : Type, ∀ edges : α → List (α × ℝ), ∀ terminal : Set α,
    (∀ s, ∀ e ∈ edges s, 0 ≤ e.2) → (∀ s ∈ terminal, edges s = []) →
    ∀ g F : α → ℝ, (∀ s, 0 ≤ g s) → (∀ s, s ∉ terminal → g s = 0) →
    (∀ s, 0 ≤ F s) → (∀ s, g s + listBackward edges F s ≤ F s) →
    ∀ s, (∀ n : ℕ, (∑ j ∈ Finset.range (n + 1), ((listBackward edges)^[j]) g s) ≤ F s) ∧
      (∑' j : ℕ, ENNReal.ofReal (((listBackward edges)^[j]) g s)) ≤ ENNReal.ofReal (F s)
```

</details>

<details>
<summary>AKLT.Blueprint.Top.StationaryLocalGlobalStatement — l:stationary-local-global</summary>

```lean
def StationaryLocalGlobalStatement : Prop :=
  (∀ t : ℚ, 0 ≤ t → t ≤ (coefficientCeiling t : ℚ) / certificateCoefficientScale) ∧
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ C : StationaryData 3741, C.Passes Q X d₀ →
    (∀ φ a, freeApply Q (fun ψ b => (C.cap ψ b : ℚ) / certificateValueScale) φ a ≤
      (C.cap φ a : ℚ) / certificateValueScale) ∧
    ∀ φ a x, 0 ≤ C.potential φ a x ∧ C.potential φ a x ≤ (C.cap φ a : ℚ) / certificateValueScale ∧
      (x ∉ square (0, 0) certificateRadius → C.potential φ a x = (C.cap φ a : ℚ) / certificateValueScale) ∧
      stationaryReward X φ a x + stationaryApply Q X d₀ C.potential φ a x ≤ C.potential φ a x ∧
      ∀ R : ℕ, stationaryContinuationSum Q X d₀ φ a x R ≤ C.potential φ a x
```

</details>

<details>
<summary>AKLT.Blueprint.Top.PrefixDominationStatement — l:prefix-domination</summary>

```lean
def PrefixDominationStatement : Prop :=
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ X : PairType, ∀ d₀ : Compass, d₀ ≠ .east →
    ∀ C : StationaryData 3741, C.Passes Q X d₀ → ∀ R : ℕ,
      firstDirectionPartialRow X d₀ R ≤ stationaryPrefixBound Q X d₀ C
```

</details>

<details>
<summary>AKLT.Blueprint.Top.KernelReflectionStatement — l:kernel-reflection</summary>

```lean
def KernelReflectionStatement : Prop :=
  (∀ n : ℕ, ∀ w : DirectionWord n,
    let w' := fun i => reflectDirection (w i)
    (ClosedTrail .B w ↔ ClosedTrail .B w') ∧
    (FirstDirection w .north ↔ FirstDirection w' .south) ∧
    trailWeight kernelStart kernelIncoming w = trailWeight kernelStart kernelIncoming w' ∧
    kernelOrdering w = kernelOrdering w' ∧ closedContribution w = closedContribution w' ∧
    ∀ i : Fin n, wordStraight kernelIncoming w i = wordStraight kernelIncoming w' i ∧
      wordRevisit kernelStart w i = wordRevisit kernelStart w' i ∧
      (responsePairs w i).image (fun p => p.image (fun z => (z.1, -z.2))) = responsePairs w' i ∧
      ∀ p ∈ responsePairs w i,
        pairCoefficient w i p = pairCoefficient w' i (p.image (fun z => (z.1, -z.2))) ∧
        responsePairType p = responsePairType (p.image (fun z => (z.1, -z.2))) ∧
        pairShift .B p = pairShift .B (p.image (fun z => (z.1, -z.2)))) ∧
  ∀ R : ℕ, firstDirectionPartialRow .B .north R = firstDirectionPartialRow .B .south R
```

</details>

<details>
<summary>AKLT.Blueprint.Top.StationaryCheckStatement — p:stationary-check</summary>

```lean
def StationaryCheckStatement : Prop :=
  (square (0, 0) certificateRadius).card = 19881 ∧
  ∃ Q : MemoryQuotient 10 3741, Q.Correct ∧
    ∃ C : PairType × Compass → StationaryData 3741,
      ∀ k ∈ stationaryCases, (C k).Passes Q k.1 k.2 ∧
        (10^9 : ℚ) * stationaryPrefixBound Q k.1 k.2 (C k) ≤ stationaryPrefixCeiling k.1 k.2
```

</details>

<details>
<summary>AKLT.Blueprint.Top.StationaryAssemblyStatement — l:stationary-assembly</summary>

```lean
def StationaryAssemblyStatement : Prop :=
  ∀ Q : MemoryQuotient 10 3741, Q.Correct → ∀ C : PairType × Compass → StationaryData 3741,
    (∀ k ∈ stationaryCases, (C k).Passes Q k.1 k.2 ∧
      (10^9 : ℚ) * stationaryPrefixBound Q k.1 k.2 (C k) ≤ stationaryPrefixCeiling k.1 k.2) →
    (∀ R : ℕ, kernelPartialRow .B R ≤
      2 * stationaryPrefixBound Q .B .north (C (.B, .north)) + stationaryPrefixBound Q .B .west (C (.B, .west))) ∧
    (2 * stationaryPrefixBound Q .B .north (C (.B, .north)) + stationaryPrefixBound Q .B .west (C (.B, .west)) ≤
      kernelRho * kernelWitness .B) ∧
    (∀ R : ℕ, kernelPartialRow .C R ≤
      stationaryPrefixBound Q .C .north (C (.C, .north)) + stationaryPrefixBound Q .C .west (C (.C, .west)) +
        stationaryPrefixBound Q .C .south (C (.C, .south))) ∧
    (stationaryPrefixBound Q .C .north (C (.C, .north)) + stationaryPrefixBound Q .C .west (C (.C, .west)) +
      stationaryPrefixBound Q .C .south (C (.C, .south)) ≤ kernelRho * kernelWitness .C) ∧
    (∀ X : PairType, (∑ Y : PairType, shiftedKernel 1 X Y * ENNReal.ofReal (kernelWitness Y : ℝ)) ≤
      ENNReal.ofReal ((kernelRho * kernelWitness X : ℚ) : ℝ)) ∧ H3Statement
```

</details>

<details>
<summary>AKLT.Blueprint.Top.IntegratePassageStatement — l:Iw</summary>

```lean
def IntegratePassageStatement : Prop :=
  ∀ π : PatternData, π.Covered →
    (∀ next : Bool, VectorAffine (originalPatternPolynomial π next)) ∧
    (∀ next : Bool, ∀ m : Fin 20 → UnitVector,
      evaluateReduced (originalPatternPolynomial π next) (fun j => (m j).val) =
        if next then patternNext π m else patternCurrent π m) ∧
    (∀ next : Bool, ∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 → ∀ m : Fin 20 → Vec3,
      evaluateReduced (originalPatternPolynomial π next) (fun j => R.mulVec (m j)) =
        evaluateReduced (originalPatternPolynomial π next) m) ∧
    ∀ m : Fin 20 → UnitVector, ∀ f g : Plane,
      ({π.outgoing.step, f, g} : Finset Plane) = {(1, 0), (0, 1), (-1, 0)} →
      π.outgoing.step ≠ f → π.outgoing.step ≠ g → f ≠ g →
      let I := fun n : Plane → Vec3 => 1 +
        (dot (n f) (n g) + dot (n f) (n π.outgoing.step) + dot (n g) (n π.outgoing.step)) / 3
      let J := fun n : Plane → Vec3 => 1 + dot (n f) (n g) / 5
      patternCurrent π m = withoutPassageFunctional π m I ∧
      patternNext π m = withoutPassageFunctional π m J ∧ 0 < patternNext π m ∧
      ∀ c : ℝ, 0 < c → c < 1 →
        patternCurrent π m - c * patternNext π m =
          withoutPassageFunctional π m (fun n => (1 - c) +
            (dot (n f) (n π.outgoing.step) + dot (n g) (n π.outgoing.step)) / 3 +
              (1 / 3 - c / 5) * dot (n f) (n g))
```

</details>

<details>
<summary>AKLT.Blueprint.Top.LeafStatement — l:leaf</summary>

```lean
def LeafStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector,
    ∀ x ∈ templateCorners ∪ templateTips, π.statusAt x ≠ .X →
      (patternDegree π x = 0 → 0 < siteFunctional (π.statusAt x) (coveredSiteField m x)) ∧
      (patternDegree π x = 1 → ∃ A : ℝ, 0 < A ∧ ∃ u : Vec3, normSq u ≤ 1 ∧
        ∀ v : Vec3, normSq v ≤ 1 →
          siteFunctional (π.statusAt x) (fun n => coveredSiteField m x n * (1 + dot n v)) =
            A * (1 + (replacementRadius π x : ℝ) * dot u v))
```

</details>

<details>
<summary>AKLT.Blueprint.Top.ReduceStatement — c:reduce</summary>

```lean
def ReduceStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ c : ℚ, 0 < c → c < 1 →
    VectorAffine (reducedDifference π r c) ∧
    (∀ R : Matrix (Fin 3) (Fin 3) ℝ, R.transpose * R = 1 → ∀ u : Fin 20 → Vec3,
      evaluateReduced (reducedDifference π r c) (fun j => R.mulVec (u j)) =
        evaluateReduced (reducedDifference π r c) u) ∧
    ((∀ u : Fin 20 → UnitVector, 0 ≤ evaluateReduced (reducedDifference π r c) (fun j => (u j).val)) →
      ∀ m : Fin 20 → UnitVector, 0 ≤ patternCurrent π m - (c : ℝ) * patternNext π m) ∧
    ∀ m : Fin 20 → UnitVector, ∃ K : ℝ, 0 < K ∧ ∃ u : Fin 20 → Vec3,
      (∀ j ∈ reductionVectors π r, normSq (u j) ≤ 1) ∧
      patternCurrent π m = K * evaluateReduced (reducedPolynomial π r false) u ∧
      patternNext π m = K * evaluateReduced (reducedPolynomial π r true) u
```

</details>

<details>
<summary>AKLT.Blueprint.Top.InversionStatement — l:inversion</summary>

```lean
def InversionStatement : Prop :=
  (∀ u : Vec3, normSq u ≤ 1 → (spinDensity u).PosSemidef ∧ (spinDensity u).trace = 1) ∧
  ∀ J : Finset (Fin 20), ∀ p : MvPolynomial (Fin 20 × Fin 3) ℚ,
    VectorAffine p → SupportedVectors J p → ∀ I : Finset (Fin 20), I ⊆ J →
    (∀ u : Fin 20 → Vec3, (∀ j ∈ J, normSq (u j) ≤ 1) →
      (evaluateReduced p u : ℂ) =
        (pauliOperator J (invertPolynomial I p) * productDensity J (invertVectors I u)).trace) ∧
    ((pauliOperator J (invertPolynomial I p)).PosSemidef →
      ∀ u : Fin 20 → Vec3, (∀ j ∈ J, normSq (u j) ≤ 1) → 0 ≤ evaluateReduced p u)
```

</details>

<details>
<summary>AKLT.Blueprint.Top.OperatorStructureStatement — l:Ostruct</summary>

```lean
def OperatorStructureStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ I : Finset (Fin 20), GroupInversion π r I →
    ∀ c : ℚ, 0 < c → c < 1 →
    let J := reductionVectors π r
    let M := pauliOperator J (invertPolynomial I (reducedDifference π r c))
    let O := Matrix.toEuclideanLin M
    M.IsHermitian ∧ (∀ σ τ, (M σ τ).im = 0) ∧
    (∀ g : Matrix (Fin 2) (Fin 2) ℂ, g.conjTranspose * g = 1 → g.det = 1 →
      Commute M (tensorPowerMatrix J g)) ∧
    Commute O (totalSpinZ J) ∧ Commute O (totalSpinPlus J) ∧ Commute O (totalSpinMinus J) ∧
    ∀ x : reductionGroups π, ∀ h : groupIsPair π r x.val = true,
      (π.statusAt x.val = .U →
        let proj := symmetricPairProjection J (leaderToken π r x) (secondToken π r x h)
        O = proj * O * proj) ∧
      (π.statusAt x.val = .D → Commute O (exchangeOperator J (leaderToken π r x) (secondToken π r x h)))
```

</details>

<details>
<summary>AKLT.Blueprint.Top.SectorStatement — l:sector</summary>

```lean
def SectorStatement : Prop :=
  ∀ π : PatternData, ∀ r : Representation, ∀ ε : ExchangeSigns π,
    let J := reductionVectors π r
    let S := exchangeSpace π r ε
    let C := centralSpace π r ε
    ∀ O : Module.End ℂ (EuclideanSpace ℂ (J → Fin 2)),
      (∀ ψ ∈ S, O ψ ∈ S) →
      (∀ ψ ∈ S, ∀ χ ∈ S, inner ℂ (O ψ) χ = inner ℂ ψ (O χ)) →
      (∀ ψ ∈ S, O (totalSpinZ J ψ) = totalSpinZ J (O ψ)) →
      (∀ ψ ∈ S, O (totalSpinPlus J ψ) = totalSpinPlus J (O ψ)) →
      (∀ ψ ∈ S, O (totalSpinMinus J ψ) = totalSpinMinus J (O ψ)) →
      (∀ ψ ∈ C, O ψ ∈ C) ∧ eigenvaluesOn C O = eigenvaluesOn S O ∧
        (PositiveOn C O ↔ PositiveOn S O)
```

</details>

<details>
<summary>AKLT.Blueprint.Top.GramResidualStatement — l:gram-residual</summary>

```lean
def GramResidualStatement : Prop :=
  ∀ n : ℕ, ∀ M L : Matrix (Fin n) (Fin n) ℤ, M.IsSymm →
    (∀ i j, i < j → L i j = 0) → ∀ g d S : ℕ, GramResidualRows M L g d S →
      ((gramResidual M L g d S).map (Int.castRingHom ℝ)).PosDef ∧
      ((gramResidual M L g d S).map (Int.castRingHom ℂ)).PosDef ∧
      (M.map (Int.castRingHom ℝ)).PosDef ∧ (M.map (Int.castRingHom ℂ)).PosDef
```

</details>

<details>
<summary>AKLT.Blueprint.Top.IntegerCheckStatement — l:integercheck</summary>

```lean
def IntegerCheckStatement : Prop :=
  (∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ I : Finset (Fin 20), GroupInversion π r I →
    ∀ D₀ : ℕ, ClearsDenominator π r D₀ → ∀ p q : ℕ, 0 < p → 0 < q → (p : ℚ) / q < 1 →
    ∀ ε : ExchangeSigns π,
      (∀ next : Bool, (integerSectorMatrix π r ε I D₀ next).IsSymm ∧
        ∀ a b, (integerSectorMatrix π r ε I D₀ next a b : ℚ) =
          (if next then 5 else 3) * (D₀ : ℚ) * rationalSectorEntry π r ε
            (invertPolynomial I (reducedPolynomial π r next)) a b) ∧
      (∀ a b, (thresholdSectorMatrix π r ε I D₀ p q a b : ℂ) =
        (15 * (D₀ : ℂ) * q) * complexSectorMatrix π r ε
          (invertPolynomial I (reducedDifference π r ((p : ℚ) / q))) a b) ∧
      ((complexSectorMatrix π r ε (invertPolynomial I (reducedDifference π r ((p : ℚ) / q)))).PosDef ↔
        ((thresholdSectorMatrix π r ε I D₀ p q).map (Int.castRingHom ℂ)).PosDef)) ∧
  ∀ n : ℕ, ∀ M : Matrix (Fin n) (Fin n) ℤ, M.IsSymm →
    ((M.map (Int.castRingHom ℝ)).PosDef ↔ ∀ k : ℕ, ∀ h : k ≤ n, 0 < k → 0 < leadingMinor M k h) ∧
    ∀ j : ℕ, ∀ h : j < n, (∀ k < j, bareissPivot M k ≠ 0) →
      bareissPivot M j = leadingMinor M (j + 1) (by omega) ∧
      ∀ i l : Fin n, j < i.val → j < l.val →
        (bareissState M j).2 ∣
          (bareissPivot M j * (bareissState M j).1 i l -
            (bareissState M j).1 i ⟨j, h⟩ * (bareissState M j).1 ⟨j, h⟩ l)
```

</details>

<details>
<summary>AKLT.Blueprint.Top.CertificateStatement — p:certificate</summary>

```lean
def CertificateStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ r : Representation, ∀ I : Finset (Fin 20), GroupInversion π r I →
    ∀ D₀ : ℕ, ClearsDenominator π r D₀ → ∀ p q : ℕ, 0 < p → 0 < q → (p : ℚ) / q < 1 →
    (∀ ε : ExchangeSigns π, ∃ t : ℕ, ∃ index : Fin t ≃ CentralBasis π r ε, ∃ g d S : ℕ,
      ∃ L : Matrix (Fin t) (Fin t) ℤ,
        (∀ i j, i < j → L i j = 0) ∧ GramResidualRows (indexedSectorMatrix π r ε I D₀ p q index) L g d S) →
      ∀ m : Fin 20 → UnitVector, 0 ≤ patternCurrent π m - ((p : ℝ) / q) * patternNext π m
```

</details>

<details>
<summary>AKLT.Blueprint.Top.ThreeFramesStatement — l:threeframes</summary>

```lean
def ThreeFramesStatement : Prop :=
  frameRotation.transpose * frameRotation = 1 ∧ frameRotation.det = 1 ∧
  0 < frameBound ∧ frameBound < 1 ∧ 0 < frameRatio ∧ frameRatio < 1 ∧
  (∀ j : Fin 3, Function.Injective (frameVector j) ∧
    (∀ a, normSq (frameVector j a) = 1) ∧ (∀ a, ∃ b, frameVector j b = -frameVector j a) ∧
    ∀ p : MvPolynomial (Fin 3) ℝ, DegreeFour p →
      (1 / 12 : ℝ) * (∑ a : IcoLetter, MvPolynomial.eval (frameVector j a) p) =
        moment (fun a => MvPolynomial.eval a p)) ∧
  (∀ i j : Fin 3, i ≠ j → ∀ a b : IcoLetter,
    frameBound ≤ 1 + dot (frameVector i a) (frameVector j b) ∧
    1 + dot (frameVector i a) (frameVector j b) ≤ 2 - frameBound ∧
    frameBound ≤ 1 - dot (frameVector i a) (frameVector j b) ∧
    1 - dot (frameVector i a) (frameVector j b) ≤ 2 - frameBound ∧
    frameVector i a ≠ frameVector j b ∧ frameVector i a ≠ -frameVector j b) ∧
  ∃ i j : Fin 3, i ≠ j ∧ ∃ a b : IcoLetter,
    1 - dot (frameVector i a) (frameVector j b) = frameBound
```

</details>

<details>
<summary>AKLT.Blueprint.Top.TightStatement — l:tight</summary>

```lean
def TightStatement : Prop :=
  (∀ j : Fin 3, ∀ a : IcoLetter,
    (∑ k : Fin 2, Complex.normSq (frameSpinor j a k)) = 1 ∧
      (fun k l => frameSpinor j a k * star (frameSpinor j a l)) = spinDensity (frameVector j a)) ∧
  (∀ n : ℕ, ∀ F : FrameData n, IsFrame F → ∀ ζ : Fin n → Spinor,
    (∀ a, (∑ k, Complex.normSq (ζ a k)) = 1 ∧
      (fun k l => ζ a k * star (ζ a l)) = spinDensity (F.point a)) →
    ∀ p : BinaryForm 4,
      (∑ a, 5 * F.weight a * Complex.normSq (binaryEval 4 p (ζ a))) = binaryNormSq 4 p) ∧
  (∀ L N : Size, ∀ κ : Site L N → Fin 3, ∀ ψ : Hilbert L N,
    (∑ σ, torusReference L N σ * Complex.normSq (frameEval κ ψ σ)) = ‖ψ‖^2) ∧
  ∀ L N : Size, ∀ k : Site L N → ℕ, ∀ F : (x : Site L N) → FrameData (k x),
    (∀ x, IsFrame (F x)) → ∀ ζ : (x : Site L N) → Fin (k x) → Spinor,
    (∀ x a, (∑ i, Complex.normSq (ζ x a i)) = 1 ∧
      (fun i j => ζ x a i * star (ζ x a j)) = spinDensity ((F x).point a)) →
    ∀ ψ : Hilbert L N,
      (∑ σ : (x : Site L N) → Fin (k x), (∏ x, 5 * (F x).weight (σ x)) *
        Complex.normSq (physicalEval ψ (fun x => ζ x (σ x)))) = ‖ψ‖^2
```

</details>

<details>
<summary>AKLT.Blueprint.Top.TorusKernelStatement — p:toruskernel</summary>

```lean
def TorusKernelStatement : Prop :=
  ∀ L N : Size,
    (∀ e : Bond L N, (bondSites e).card = 2) ∧ Function.Injective (@bondSites L N) ∧
    (∀ x : Site L N, (torusNeighbours x).card = 4 ∧ x ∉ torusNeighbours x) ∧
    B L N ≠ 0 ∧ LinearMap.ker (H L N) = Submodule.span ℂ {B L N} ∧
    ∀ ε : Bond L N → Bool, Submodule.span ℂ {reorientedB L N ε} = Submodule.span ℂ {B L N}
```

</details>

<details>
<summary>AKLT.Blueprint.Top.StarStatement — l:star</summary>

```lean
def StarStatement : Prop :=
  0 < starGap ∧ starHamiltonian.HasEigenvalue (starGap : ℂ) ∧
  (∀ μ : ℝ, 0 < μ → starHamiltonian.HasEigenvalue (μ : ℂ) → starGap ≤ μ) ∧
  ∀ L N : Size, (∑ x : Site L N, siteHamiltonian x) = 2 • H L N ∧
    ∀ x : Site L N, ∀ ψ : Hilbert L N,
      starGap * ‖ψ - (LinearMap.ker (siteHamiltonian x)).starProjection ψ‖^2 ≤
        (inner ℂ ψ (siteHamiltonian x ψ)).re
```

</details>

<details>
<summary>AKLT.Blueprint.Top.QDStatement — t:QD</summary>

```lean
def QDStatement : Prop :=
  ∀ L N : Size, ∀ κ : Site L N → Fin 3, ProperTorusColouring κ →
    (∀ σ, torusLaw L N κ σ =
      torusReference L N σ * Complex.normSq (frameEval κ (B L N) σ) / ‖B L N‖^2) ∧
    ∀ γ : ℝ, PoincareLower (torusLaw L N κ) γ → ∀ ψ : Hilbert L N,
      inner ℂ (B L N) ψ = 0 → (starGap / 2) * γ * ‖ψ‖^2 ≤ (inner ℂ ψ (H L N ψ)).re
```

</details>

<details>
<summary>AKLT.Blueprint.Top.PlaneEnergyStatement — l:planeenergy</summary>

```lean
def PlaneEnergyStatement : Prop :=
  0 < frameEnergy ∧ frameEnergy ≤ 1 ∧
  (∀ κ : Plane → Fin 3, ProperPlaneColouring κ → ∀ W : Finset Plane, ∀ η : FrameBoundary W,
    PositiveProbability (planeLaw κ W η) ∧
    (∀ V : Finset Plane, V ⊆ W → ∀ σ : PlaneConfiguration W,
      conditionalPlaneLaw κ W V η σ = planeLaw κ V (inducedBoundary W V η σ)) ∧
    (∀ U J : Finset Plane, U ⊆ W → J ⊆ W → Disjoint U J →
      ∀ a b : Plane → IcoLetter,
      conditionalProbability (planeLaw κ W η)
        (fun σ => ∀ x ∈ J, extendLetters σ x = a x)
        (fun σ => ∀ x ∈ U, extendLetters σ x = b x) ≥ frameEnergy ^ U.card) ∧
    PoincareLower (planeLaw κ W η) (frameRatio ^ (internalBonds W).card)) ∧
  ∀ L N : Size, ∀ κ : Site L N → Fin 3, ProperTorusColouring κ →
    PositiveProbability (torusLaw L N κ) ∧
    (∀ U : Finset (Site L N), ∀ σ ξ : TorusConfiguration L N,
      (∀ z ∈ (U.biUnion torusNeighbours) \ U, σ z = ξ z) →
        conditionalTorusLaw L N κ U σ = conditionalTorusLaw L N κ U ξ) ∧
    ∀ U J : Finset (Site L N), Disjoint U J → ∀ a b : TorusConfiguration L N,
      conditionalProbability (torusLaw L N κ) (fun σ => ∀ x ∈ J, σ x = a x)
        (fun σ => ∀ x ∈ U, σ x = b x) ≥ frameEnergy ^ U.card
```

</details>

<details>
<summary>AKLT.Blueprint.Top.H1Statement — h:H1</summary>

```lean
def H1Statement : Prop := LocalPatternBound (961 / 1000) (187 / 200)
```

</details>

<details>
<summary>AKLT.Blueprint.Top.H1TheoremStatement — t:H1</summary>

```lean
def H1TheoremStatement : Prop :=
  ∀ π : PatternData, π.Covered → ∀ m : Fin 20 → UnitVector,
    (if π.outgoing = .north then (961 / 1000 : ℝ) else 187 / 200) * patternNext π m ≤ patternCurrent π m
```

</details>

<details>
<summary>AKLT.Blueprint.Top.H2Statement — h:H2</summary>

```lean
def H2Statement : Prop := OpenTrailBound 10 (certifiedRate : ℝ)
```

</details>

<details>
<summary>AKLT.Blueprint.Top.H3Statement — h:H3</summary>

```lean
def H3Statement : Prop := PositiveVectorBound
```

</details>

<details>
<summary>AKLT.Blueprint.Top.InputsStatement — t:inputs</summary>

```lean
def InputsStatement : Prop :=
  H1Statement ∧ H2Statement ∧ H3Statement ∧ certifiedRate < (2499 / 2500 : ℚ) ∧
    (2499 / 2500 : ℚ) < 1
```

</details>

<details>
<summary>AKLT.Blueprint.Top.PStatement — h:P</summary>

```lean
def PStatement : Prop := ∃ A θ : ℝ, ResponseProperty A θ
```

</details>

<details>
<summary>AKLT.Blueprint.Top.RecStatement — t:rec</summary>

```lean
def RecStatement : Prop :=
  ∀ CV q : ℝ, H1Statement → OpenTrailBound CV q → H3Statement →
    ∃ θ ρ : ℝ, q^2 < θ ∧ θ < 1 ∧ (kernelRho : ℝ) < ρ ∧ ρ < 1 ∧
      ShiftedWitness θ ρ ∧ ResponseProperty (renewalAmplitude CV q ρ) θ
```

</details>

<details>
<summary>AKLT.Blueprint.Top.MThetaStatement — l:Mtheta</summary>

```lean
def MThetaStatement : Prop :=
  ∀ CV q : ℝ, OpenTrailBound CV q → H3Statement →
    (∀ θ : ℝ, q^2 < θ → θ ≤ 1 → ∀ X Y : PairType,
      shiftedKernel θ X Y ≠ ⊤ ∧ shiftedKernel θ X Y ≤
        ∑' n : ℕ, ENNReal.ofReal ((n : ℝ) * (18094 / 100000 + 2 * (36751 / 100000 : ℝ)) *
          CV * q^n * Real.rpow θ (-(n : ℝ) / 2 - 1))) ∧
    (∀ n : ℕ, ∀ X : PairType, ∀ w : DirectionWord n, ClosedTrail X w →
      ∀ i : Fin n, ∀ p ∈ responsePairs w i, (pairShift X p : ℝ) ≤ (n : ℝ) / 2 + 1) ∧
    ∃ θ ρ : ℝ, q^2 < θ ∧ θ < 1 ∧ (kernelRho : ℝ) < ρ ∧ ρ < 1 ∧ ShiftedWitness θ ρ
```

</details>

<details>
<summary>AKLT.Blueprint.Top.ShellGeometryStatement — l:shellgeom</summary>

```lean
def ShellGeometryStatement : Prop :=
  ∀ l₀ : ℕ, 1 ≤ l₀ → ∀ a y : Plane, ∀ u : ℕ, geometryThreshold l₀ ≤ u →
    setDistance supDist y (↑(square a u) : Set Plane) = 1 →
    (exceptionalIndices a y u).card ≤ 1 ∧
    (∀ i : ℤ, 2 ≤ i → i ≤ lastShellIndex u → shell a y u i ⊆ farVolume a y u i) ∧
    (∀ i : ℤ, 2 ≤ i → i ≤ lastShellIndex u → i ∉ exceptionalIndices a y u →
      (nearShell a y u l₀ i).card ≤ 8 * l₀ ∧ ParallelClearance a y u i) ∧
    ∀ i : ℤ, 2 ≤ i →
      (∀ x ∈ square a u \ farVolume a y u i,
        setDistance supDist x (↑(farVolume a y u i) : Set Plane) ≤ 1 → x ∈ shell a y u (i - 1)) ∧
      ¬ setDistance supDist y (↑(farVolume a y u i) : Set Plane) ≤ 1
```

</details>

<details>
<summary>AKLT.Blueprint.Top.CutMOSStatement — t:cutMOS</summary>

```lean
def CutMOSStatement : Prop :=
  ∀ A θ : ℝ, ResponseProperty A θ →
    ∃ Mstar : ℕ, WindowProperty 64 (cutProbability A θ) Mstar
```

</details>

<details>
<summary>AKLT.Blueprint.Top.MainWStatement — t:mainW</summary>

```lean
def MainWStatement : Prop :=
  (∃ l₀ : ℕ, ∃ p₀ : ℝ, ∃ Mstar : ℕ, WindowProperty l₀ p₀ Mstar) → EventualMain
```

</details>

**Exact LaTeX source for every represented label.**

The following blocks are copied byte-for-byte from the full revision plan, including all amended statements. All 65 exported interface blocks were independently compared against interfaces.tex and match verbatim. Additional internal labels are included whenever a shared definition or the top assembly uses them. [interfaces.json](interfaces.json) records the 65 interface mappings in machine-readable form.

<a id="latex-d-model"></a>
**d:model.**

Lean: `AKLT.Defs.hamiltonian`, `AKLT.Defs.vbs`.

```latex
\begin{definition}\label{d:model}
For integers \(L,N\ge3\), let \(\Lambda=\Lambda_{L,N}=\mathbb Z_L\times\mathbb Z_N\)
with its simple, unoriented nearest-neighbour edge set \(E_{L,N}\).
The Hilbert space is \(\mathcal H_\Lambda=\bigotimes_{x\in\Lambda}V_4\).
Each site carries the spin-\(2\) space \(V_4\), and \(P_{\{x,y\}}\)
is the orthogonal projection onto total spin \(4\) in \(V_4\otimes V_4\).
Fix one orientation of each edge and set
\[
 q_{xy}=z_{x,1}z_{y,2}-z_{x,2}z_{y,1},\qquad
 B_{L,N}=\prod_{e\in E_{L,N}}q_e,\qquad
 H_{L,N}=\sum_{e\in E_{L,N}}P_e.
\]
Every edge is counted once. The spectral gap of \(H_{L,N}\) means its
smallest positive eigenvalue.
\end{definition}
```

<a id="latex-t-main"></a>
**t:main.**

Lean: `AKLT.Challenge.MainStatementV2`, `AKLT.Blueprint.Top.mainV2_of_parts`.

```latex
\begin{theorem}\label{t:main}
For every \(L,N\ge3\), \(B_{L,N}\ne0\) and
\(\ker H_{L,N}=\mathbb C B_{L,N}\).
There exist \(c>0\) and an integer \(L_0\ge3\) such that, for all
integers \(L,N\ge L_0\), every nonzero eigenvalue of \(H_{L,N}\)
is at least \(c\).
\end{theorem}
```

<a id="latex-d-moment"></a>
**d:moment.**

Lean: `AKLT.Defs.Plane`, `AKLT.Defs.latticeDist`, `AKLT.Defs.supDist`, `AKLT.Defs.Adjacent`, `AKLT.Defs.neighbours`, `AKLT.Defs.setDistance`, `AKLT.Defs.Vec3`, `AKLT.Defs.dot`, `AKLT.Defs.normSq`, `AKLT.Defs.UnitVector`, `AKLT.Defs.BallVector`, `AKLT.Defs.goldenRatio`, `AKLT.Defs.icoRadius`, `AKLT.Defs.IcoLetter`, `AKLT.Defs.signValue`, `AKLT.Defs.icoVector`, `AKLT.Defs.icoSet`, `AKLT.Defs.moment`, `AKLT.Defs.SpinLetter`, `AKLT.Defs.spinVector`, `AKLT.Defs.spinWeight`, `AKLT.Defs.siteFunctional`, `AKLT.Defs.totalVariation`, `AKLT.Defs.hamming`.

```latex
\begin{definition}\label{d:moment}
Write \(\mathbb S^2=\{a\in\mathbb R^3:|a|=1\}\), put
\(\phi=(1+\sqrt5)/2\), \(r=\sqrt{\phi+2}\), and set
\[
 D=\frac1r\{(0,\pm1,\pm\phi),(\pm1,\pm\phi,0),(\pm\phi,0,\pm1)\},
 \qquad
 \mathcal M(f)=\frac1{12}\sum_{a\in D}f(a).
\]
All indicated signs are independent. Define finite probability laws
\(\lambda_{\mathrm U}=\frac1{12}\sum_{a\in D}\delta_a\) and
\(\lambda_{\mathrm D}=\frac35\lambda_{\mathrm U}+\frac25\delta_0\).
Products of these functionals always mean finite sums.
For plane sites, \(d\) denotes ambient \(\ell^1\) distance and
\(\operatorname{dist}_\infty\) denotes ambient \(\ell^\infty\) distance.
Distances to an empty set are \(+\infty\); a product over an empty site
set has its one empty configuration. For finite probabilities, use
\[
 d_{\rm TV}(p,p')=\tfrac12\sum_z|p(z)-p'(z)|,\qquad
 \operatorname{Var}_\mu f=\mu(|f-\mu f|^2),\qquad
 d_H(n,n')=\sum_x\mathbf1_{\{n_x\ne n'_x\}} .
\]
\end{definition}
```

<a id="latex-l-moments"></a>
**l:moments.**

Lean: `AKLT.Defs.DegreeFour`, `AKLT.Defs.SeparateDegreeFour`, `AKLT.Defs.productFunctional`, `AKLT.Defs.rationalMoment`, `AKLT.Defs.rationalStatusMoment`, `AKLT.Defs.contractSpins`, `AKLT.Blueprint.Top.MomentsStatement`.

```latex
\begin{lemma}\label{l:moments}
The set \(D\) has twelve distinct unit vectors and is antipodal.
For \(i,j,k,l\in\{1,2,3\}\),
\[
 \begin{gathered}
 \mathcal M(1)=1,\qquad \mathcal M(n_i)=\mathcal M(n_in_jn_k)=0,\qquad
 \mathcal M(n_in_j)=\delta_{ij}/3,\\
 \mathcal M(n_in_jn_kn_l)=
 (\delta_{ij}\delta_{kl}+\delta_{ik}\delta_{jl}+\delta_{il}\delta_{jk})/15.
 \end{gathered}
\]
For every polynomial \(p\) of total degree at most four and every
\(R\in\mathrm O(3)\), \(\mathcal M(p\circ R)=\mathcal M(p)\).
The same covariance holds for \(\lambda_{\mathrm D}\); its constant
moment is one and its moments of positive degree at most four are
\(3/5\) times those displayed above.
These assertions hold site by site for polynomials of separate degree
at most four in a finite product of spins.
\end{lemma}
```

<a id="latex-d-pinmodel"></a>
**d:pinmodel.**

Lean: `AKLT.Defs.positiveNeighbours`, `AKLT.Defs.internalBonds`, `AKLT.Defs.originalLegs`, `AKLT.Defs.boundaryDepth`, `AKLT.Defs.protectedSites`, `AKLT.Defs.PinAssignment`, `AKLT.Defs.extendIcoSpins`, `AKLT.Defs.pinnedSum`, `AKLT.Defs.freeSum`, `AKLT.Defs.pinnedExpectation`, `AKLT.Defs.freeExpectation`, `AKLT.Defs.partitionRatio`.

```latex
\begin{definition}\label{d:pinmodel}
For finite \(G\subset\mathbb Z^2\), let
\[
 \mathcal L(G)=\{(x,z):x\in G,\ z\notin G,\ d(x,z)=1\},\qquad
 S(G)=\{x\in G:d(x,\mathbb Z^2\setminus G)\le2\}.
\]
A pin assignment is \(\tau\in(\mathbb S^2)^{\mathcal L(G)}\).
For \(Y\subset G\), write \(D_Y=G\setminus Y\) and define
\[
 Z^\tau_{D_Y}[f]=
 \sum_{n\in D^{D_Y}}12^{-|D_Y|}f(n)
 \prod_{\substack{\{x,y\}\subset D_Y\\d(x,y)=1}}(1+n_x\cdot n_y)
 \prod_{\substack{(x,z)\in\mathcal L(G)\\x\in D_Y}}
       (1+\tau_{xz}\cdot n_x).
\]
The free sum \(Z^0_{D_Y}[f]\) omits all leg factors.
Write \(Z^\bullet_{D_Y}=Z^\bullet_{D_Y}[1]\),
\(\mathbb E^\bullet_{D_Y}f=Z^\bullet_{D_Y}[f]/Z^\bullet_{D_Y}\),
and \(\Psi_{D_Y}(\tau)=Z^\tau_{D_Y}/Z^0_{D_Y}\).
Here and below \(\bullet\) is either \(\tau\) or \(0\).
The empty partition sum is one. There are no new factors on legs into \(Y\).
Different original legs may carry unrelated unit pins, even if their
outside endpoints coincide.
\end{definition}
```

<a id="latex-l-finitefacts"></a>
**l:finitefacts.**

Lean: `AKLT.Defs.FiniteSpinNetwork`, `AKLT.Defs.FiniteSpinNetwork.Valid`, `AKLT.Defs.FiniteSpinNetwork.weight`, `AKLT.Defs.FiniteSpinNetwork.partition`, `AKLT.Blueprint.Top.FiniteFactsStatement`.

```latex
\begin{lemma}\label{l:finitefacts}
Consider a finite network with site laws \(\lambda_{\mathrm U}\) or
\(\lambda_{\mathrm D}\), retained distinct-endpoint bonds
\(1+n_x\cdot n_y\), and retained original unit-pin factors
\(1+\tau_\ell\cdot n_x\), with at most four factors incident to each site.
Its pinned and free partition sums are strictly positive, including
the empty network. Non-neighbours are conditionally independent given
the other spins on every conditioning event of positive probability.
If \(f\) is a product of scalar products of spins and the product of
\(f\) with the bond factors has separate degree at most four at every
site, then \(Z^0[f]\ge0\), hence \(\mathbb E^0 f\ge0\).
All normalized spins have norm at most one.
\end{lemma}
```

<a id="latex-l-35"></a>
**l:35.**

Lean: `AKLT.Defs.localProduct`, `AKLT.Defs.localMean`, `AKLT.Blueprint.Top.ThreeFactorMeanStatement`.

```latex
\begin{lemma}\label{l:35}
For \(0\le k\le3\) and \(|a_j|\le1\), the probability law proportional to
\(\prod_{j=1}^k(1+n\cdot a_j)\lambda_{\mathrm U}(\mathrm dn)\)
has mean of norm at most \(3/5\). The same bound holds with
\(\lambda_{\mathrm D}\) in place of \(\lambda_{\mathrm U}\).
Moreover,
\[
 \left\{
 \frac{\mathcal M\!\left(n\prod_{j=1}^3(1+n\cdot a_j)\right)}
      {\mathcal M\!\left(\prod_{j=1}^3(1+n\cdot a_j)\right)}
       :a_1,a_2,a_3\in\mathbb S^2
 \right\}=\{b\in\mathbb R^3:|b|\le3/5\}.
\]
Consequently an unpinned site having at most three present factors
has conditional mean of norm at most \(3/5\), on every positive
conditioning fibre.
\end{lemma}
```

<a id="latex-l-exact"></a>
**l:exact.**

Lean: `AKLT.Defs.MomentLaw`, `AKLT.Defs.momentLawFunctional`, `AKLT.Blueprint.Top.ExactStatement`.

```latex
\begin{lemma}\label{l:exact}
At each site of a finite set choose any positive weighted unit-vector
law whose moments through degree four equal those of \(\mathcal M\).
A polynomial of separate degree at most four has the same product
functional under these laws as under \(\lambda_{\mathrm U}\) at all
sites. The analogous assertion holds after replacing any chosen site
laws by \(3/5\) times that law plus \(2/5\,\delta_0\).
In particular this applies to partition products of factors
\(1\pm n_x\cdot n_y\) and \(1\pm n_x\cdot a\), \(|a|=1\), whenever
each variable occurs at most four times, and to inserted observables
only when their degrees are included in this same bound.
\end{lemma}
```

<a id="latex-h-P"></a>
**h:P.**

Lean: `AKLT.Defs.decay`, `AKLT.Defs.ResponseProperty`, `AKLT.Blueprint.Top.PStatement`.

```latex
\begin{definition}[(P)]\label{h:P}
For \(A\ge2\) and \(0<\theta<1\), property \(\mathsf P(A,\theta)\)
means that, for every finite \(G\subset\mathbb Z^2\), every unit-pin
assignment on \(\mathcal L(G)\), every
\(Y\subset G\setminus S(G)\), and all \(u,v\in G\setminus Y\) with
\(d(u,v)=2\) and a common neighbour in \(Y\),
\[
 \left|\mathbb E^\tau_{G\setminus Y}(n_u\cdot n_v)
             -\mathbb E^0_{G\setminus Y}(n_u\cdot n_v)\right|
 \le A\theta^{\min\{d(u,S(G)),d(v,S(G))\}} .
\]
The distances are ambient plane distances to the original \(S(G)\);
removed sites are not added to the boundary.
\end{definition}
```

<a id="latex-d-poly"></a>
**d:poly.**

Lean: `AKLT.Defs.Spinor`, `AKLT.Defs.frameSpinor`, `AKLT.Defs.BinaryForm`, `AKLT.Defs.binaryNormSq`, `AKLT.Defs.binaryEval`, `AKLT.Defs.binaryPolynomial`, `AKLT.Defs.binaryActionPolynomial`, `AKLT.Defs.physicalEval`, `AKLT.Defs.polynomialState`.

```latex
\begin{definition}\label{d:poly}
Let \(V_d\) be the homogeneous binary polynomials of degree \(d\).
Its monomials \(z_1^{d-j}z_2^j\), \(0\le j\le d\), are orthogonal with
squared norms \(\binom dj^{-1}\). The action is
\((U_gp)(z)=p(g^{-1}z)\). Use \(V_4\) at each physical site.
For each of the finitely many frame letters \(a\) choose one unit
spinor \(\zeta(a)\in\mathbb C^2\) with
\(\zeta(a)\zeta(a)^*=(I+a\cdot\sigma)/2\).
No spinor choice on the whole sphere is part of the definitions.
\end{definition}
```

<a id="latex-p-toruskernel"></a>
**p:toruskernel.**

Lean: `AKLT.Defs.torusNeighbours`, `AKLT.Defs.reorientedB`, `AKLT.Blueprint.Top.TorusKernelStatement`.

```latex
\begin{proposition}\label{p:toruskernel}
For every \(L,N\ge3\), the torus is simple and has four distinct
neighbours at each site, \(B_{L,N}\ne0\), and
\(\ker H_{L,N}=\mathbb C B_{L,N}\).
Changing edge orientations does not change this one-dimensional space.
\end{proposition}
```

<a id="latex-l-star"></a>
**l:star.**

Lean: `AKLT.Defs.StarHilbert`, `AKLT.Defs.starAtSite`, `AKLT.Defs.starCasimir`, `AKLT.Defs.starHamiltonian`, `AKLT.Defs.starGap`, `AKLT.Defs.siteHamiltonian`, `AKLT.Blueprint.Top.StarStatement`.

```latex
\begin{lemma}\label{l:star}
Let \(h_\star=\sum_{j=1}^4P_{\{0,j\}}\) on \(V_4^{\otimes5}\).
Its smallest positive eigenvalue \(g_\star\) exists and is positive.
For \(L,N\ge3\), set \(H_x=\sum_{e\ni x}P_e\) and
\(\mathcal S_x=\ker H_x\). Then
\[
 H_x\ge g_\star(I-\Pi_{\mathcal S_x}),\qquad
 \sum_xH_x=2H_{L,N}.
\]
\end{lemma}
```

<a id="latex-d-frame"></a>
**d:frame.**

Lean: `AKLT.Defs.FrameData`, `AKLT.Defs.IsFrame`.

```latex
\begin{definition}\label{d:frame}
A frame is a finite set \(A\subset\mathbb S^2\) with positive weights
\(w(a)\) summing to one such that
\(\sum_{a\in A}w(a)p(a)=\mathcal M(p)\)
for every real polynomial \(p\) of degree at most four.
\end{definition}
```

<a id="latex-l-tight"></a>
**l:tight.**

Lean: `AKLT.Defs.torusReference`, `AKLT.Defs.frameEval`, `AKLT.Blueprint.Top.TightStatement`.

```latex
\begin{lemma}\label{l:tight}
For every frame \((A,w)\) and every \(p\in V_4\),
\[
 \sum_{a\in A}5w(a)|p(\zeta(a))|^2=\|p\|_{V_4}^2.
\]
For site frames \((D_x,w_x)\), set \(\Omega=\prod_xD_x\),
\(\pi(s)=\prod_x5w_x(s_x)\), and
\(\iota\varphi(s)=\varphi((\zeta(s_x))_x)\).
Then \(\iota:\mathcal H_\Lambda\to\ell^2(\Omega,\pi)\) is an isometry.
\end{lemma}
```

<a id="latex-l-threeframes"></a>
**l:threeframes.**

Lean: `AKLT.Defs.frameRotation`, `AKLT.Defs.frameVector`, `AKLT.Defs.frameBound`, `AKLT.Defs.frameRatio`, `AKLT.Blueprint.Top.ThreeFramesStatement`.

```latex
\begin{lemma}\label{l:threeframes}
Let
\[
 T=\begin{pmatrix}99/101&-20/101&0\\20/101&99/101&0\\0&0&1\end{pmatrix},
 \quad D^{(j)}=T^jD\ (j=0,1,2),\quad
 b=\frac{5-\sqrt5}{505},\quad r_b=\frac b{2-b}.
\]
The matrix \(T\) is in \(\mathrm{SO}(3)\).
Each \(D^{(j)}\), with uniform weights \(1/12\), is an antipodal frame.
For \(i\ne j\), \(a\in D^{(i)}\), \(a'\in D^{(j)}\),
\[
 0<b<1,\qquad b\le1\pm a\cdot a'\le2-b,\qquad0<r_b<1.
\]
The common lower bound \(b\) is attained, and distinct frames are
disjoint even up to antipodal signs.
\end{lemma}
```

<a id="latex-d-framemodel"></a>
**d:framemodel.**

Lean: `AKLT.Defs.ProperPlaneColouring`, `AKLT.Defs.ProperTorusColouring`, `AKLT.Defs.PlaneConfiguration`, `AKLT.Defs.exteriorSites`, `AKLT.Defs.FrameBoundary`, `AKLT.Defs.extendLetters`, `AKLT.Defs.extendBoundary`, `AKLT.Defs.planeWeight`, `AKLT.Defs.planeLaw`, `AKLT.Defs.marginal`, `AKLT.Defs.TorusConfiguration`, `AKLT.Defs.torusWeight`, `AKLT.Defs.torusLaw`, `AKLT.Defs.Weight`, `AKLT.Defs.normalize`, `AKLT.Defs.PositiveProbability`, `AKLT.Defs.Probability`, `AKLT.Defs.expectation`, `AKLT.Defs.complexMean`, `AKLT.Defs.variance`, `AKLT.Defs.conditionalVariance`, `AKLT.Defs.dirichlet`, `AKLT.Defs.PoincareLower`, `AKLT.Defs.heatBathGap`, `AKLT.Defs.Coupling`.

```latex
\begin{definition}\label{d:framemodel}
Given any proper three-colouring \(\kappa\) of a plane or torus,
put \(D_x=D^{(\kappa(x))}\), with weights \(1/12\).
On the torus define
\[
 \mu^{\mathrm{af}}_{\kappa,L,N}(s)=
 \frac1{Z^{\mathrm{af}}}\prod_x\frac1{12}
       \prod_{\{x,y\}\in E_{L,N}}(1-s_x\cdot s_y).
\]
On the plane, for finite \(W\subset\mathbb Z^2\) and
\(\eta_z\in D_z\) at exterior neighbour sites, define
\[
 \mu^{+,\eta}_{\kappa,W}(n)=\frac1{Z^{+,\eta}_{\kappa,W}}
 \prod_{x\in W}\frac1{12}
 \prod_{\substack{\{x,y\}\subset W\\d(x,y)=1}}(1+n_x\cdot n_y)
 \prod_{\substack{x\in W,z\notin W\\d(x,z)=1}}(1+n_x\cdot\eta_z).
\]
Only the finitely many needed exterior letters are specified.
These laws have full support. Write \(E_U\) for conditioning off \(U\),
\(\operatorname{Var}_U f=E_U|f-E_Uf|^2\), and
\[
 \mathcal D_\mu(f)=\sum_x\mu(\operatorname{Var}_x f),\qquad
 \lambda(\mu)=\inf_{\operatorname{Var}_\mu f>0}
             \frac{\mathcal D_\mu(f)}{\operatorname{Var}_\mu f}.
\]
All generators have one update per physical site. A gap lower bound is
always equivalently a Poincare inequality, including one-point spaces.
\end{definition}
```

<a id="latex-t-QD"></a>
**t:QD.**

Lean: `AKLT.Blueprint.Top.QDStatement`.

```latex
\begin{theorem}\label{t:QD}
For every \(L,N\ge3\) and every proper torus three-colouring,
\[
 \mu^{\mathrm{af}}(s)=
 \frac{\pi(s)|\iota B_{L,N}(s)|^2}{\|B_{L,N}\|^2},\qquad
 H_{L,N}\big|_{B_{L,N}^{\perp}}\ge
       \frac{g_\star}{2}\lambda(\mu^{\mathrm{af}})I .
\]
In particular
\(\operatorname{gap}(H_{L,N})\ge(g_\star/2)\lambda(\mu^{\mathrm{af}})\).
\end{theorem}
```

<a id="latex-l-planeenergy"></a>
**l:planeenergy.**

Lean: `AKLT.Defs.frameEnergy`, `AKLT.Defs.inducedBoundary`, `AKLT.Defs.conditionalPlaneLaw`, `AKLT.Defs.conditionalTorusLaw`, `AKLT.Defs.sitesInVolume`, `AKLT.Blueprint.Top.PlaneEnergyStatement`.

```latex
\begin{lemma}\label{l:planeenergy}
All the frame specifications above are consistent under conditioning
and have nearest-neighbour Markov dependence. Uniformly over proper
colourings, finite volumes, admissible frame-valued boundaries, and
fully specified one-site fibres, every letter has conditional
probability at least
\[
 \alpha=\frac1{12}r_b^4\in(0,1].
\]
The same lower bound holds after conditioning on fewer letters.
Any prescribed assignment on \(k\) sites, under arbitrary consistent
partial conditioning off those sites, has conditional probability
at least \(\alpha^k\).
For a finite plane block \(Q\), the single-site heat bath of every conditional block law in \(Q\) has Poincare gap at least
\(r_b^{|E(Q)|}\), where \(E(Q)\) is its internal edge set.
\end{lemma}
```

<a id="latex-d-shells"></a>
**d:shells.**

Lean: `AKLT.Defs.square`, `AKLT.Defs.squareCorners`, `AKLT.Defs.shellSpacing`, `AKLT.Defs.shellRadius`, `AKLT.Defs.lastShellIndex`, `AKLT.Defs.farVolume`, `AKLT.Defs.shell`, `AKLT.Defs.nearShell`, `AKLT.Defs.window`, `AKLT.Defs.exceptionalIndices`.

```latex
\begin{definition}\label{d:shells}
For \(a\in\mathbb Z^2\), integer \(u\ge1\), put
\(C_u(a)=a+\{-u,\ldots,u\}^2\).
For \(\operatorname{dist}_\infty(y,C_u(a))=1\), let
\(s=u^{1/4}\), \(k_i=\lfloor is\rfloor\), \(i_1=\lfloor s\rfloor+1\).
For an integer \(l_0\ge1\) define
\[
 \begin{split}
 F_i&=\{x\in C_u(a):|x-y|_\infty>(i-1)s\},\\
 D_i&=\{x\in C_u(a):|x-y|_\infty=k_i\},\\
 A_i&=\{x\in D_i:\operatorname{dist}_\infty
                    (x,\mathbb Z^2\setminus C_u(a))\le l_0\},\qquad
 B_i=D_i\setminus A_i .
 \end{split}
\]
Let \(I_0\) consist of the integers \(2\le i\le i_1\) for which
some point of \(D_i\) is at distance strictly less than \(s/3\)
from a corner site of \(C_u(a)\).
All these are sets of physical sites.
\end{definition}
```

<a id="latex-d-W"></a>
**d:W.**

Lean: `AKLT.Defs.planeMarginal`, `AKLT.Defs.WindowProperty`.

```latex
\begin{definition}[(W)]\label{d:W}
The family of plane frame specifications has \(\mathsf W(l_0,p_0,M_\star)\)
if \(l_0,M_\star\) are positive integers, \(0<p_0\le1\), and,
for every proper plane three-colouring, every translate \(C_u(a)\)
with integer \(u\ge M_\star\), every \(y\) as in Definition~\ref{d:shells},
every integer \(2\le i\le u^{1/4}\) outside \(I_0\), and every two
admissible frame-valued boundary conditions \(\eta,\xi\) for \(F_i\),
\[
 d_{\mathrm{TV}}\!\left(
       \mu^{+,\eta}_{\kappa,F_i,B_i},
       \mu^{+,\xi}_{\kappa,F_i,B_i}\right)\le1-p_0 .
\]
The subscript \(B_i\) denotes a marginal. Boundaries are arbitrary
within their site alphabets; they need not agree anywhere.
\end{definition}
```

<a id="latex-t-mainW"></a>
**t:mainW.**

Lean: `AKLT.Defs.EventualMain`, `AKLT.Blueprint.Top.MainWStatement`.

```latex
\begin{theorem}\label{t:mainW}
If the plane frame family satisfies (W), there exist \(c>0\) and
an integer \(L_0\ge3\) such that
\(\ker H_{L,N}=\mathbb C B_{L,N}\) and every nonzero eigenvalue is
at least \(c\), for all integers \(L,N\ge L_0\).
\end{theorem}
```

<a id="latex-l-shellgeom"></a>
**l:shellgeom.**

Lean: `AKLT.Defs.geometryThreshold`, `AKLT.Defs.ParallelClearance`, `AKLT.Blueprint.Top.ShellGeometryStatement`.

```latex
\begin{lemma}\label{l:shellgeom}
For \(u\ge M_{\mathrm g}(l_0)=\max\{16,6(l_0+1)\}^4\),
\(|I_0|\le1\), and \(D_i\subset F_i\) for \(2\le i\le i_1\).
For \(2\le i\le i_1\) outside \(I_0\), \(|A_i|\le8l_0\).
Every side of \(y+[-k_i,k_i]^2\) parallel to an edge of \(C_u(a)\)
and meeting \(C_u(a)\) is at distance at least \(s/3\) from the
exterior half-plane beyond that edge.
For \(i\ge2\), every point of \(C_u(a)\setminus F_i\)
within \(\ell^\infty\) distance one of \(F_i\) lies in \(D_{i-1}\);
\(y\) is not within that distance of \(F_i\).
\end{lemma}
```

<a id="latex-t-cutMOS"></a>
**t:cutMOS.**

Lean: `AKLT.Defs.cutCost`, `AKLT.Defs.cutProbability`, `AKLT.Blueprint.Top.CutMOSStatement`.

```latex
\begin{theorem}\label{t:cutMOS}
If \(\mathsf P(A,\theta)\) holds, then the family of plane frame
specifications has \(\mathsf W(64,p_0,M_\star)\), with common
\(p_0\in(0,1]\) and integer \(M_\star\ge1\) depending only on
\(A,\theta\). The constants work for every proper plane
three-colouring and every translate.
Specifically, let
\[
 E=1+4A+10A\theta^{-4}
       \left[48\theta^{14}\left(17+\frac1{1-\theta}\right)+1\right],
 \qquad p_0=e^{-2E}.
\]
There exists an integer \(M_\star\ge1\) for which (W) holds
with this displayed choice of \(p_0\).
\end{theorem}
```

<a id="latex-d-domain"></a>
**d:domain.**

Lean: `AKLT.Defs.Network`, `AKLT.Defs.Network.active`, `AKLT.Defs.Network.Present`, `AKLT.Defs.Network.bonds`, `AKLT.Defs.Network.presentNeighbours`, `AKLT.Defs.Network.LocalRules`, `AKLT.Defs.Network.Ordinary`, `AKLT.Defs.Network.Auxiliary`, `AKLT.Defs.Network.Consistent`, `AKLT.Defs.Network.spins`, `AKLT.Defs.Network.partition`, `AKLT.Defs.Network.expectation`, `AKLT.Defs.Network.ratio`, `AKLT.Defs.Status`.

```latex
\begin{definition}\label{d:domain}
Fix finite \(G\), \(S=S(G)\), and original unit pins \(\tau\).
A domain assigns statuses \(\mathrm U,\mathrm D,\mathrm X\);
\(\mathrm X\) sites are removed. Each nonremoved site has a kept
subset of its incident bonds inside \(G\). A bond is present if both
ends are nonremoved and both keep it. A \(\mathrm D\) site has at
most two present bonds. Protected sites in \(S\) have status
\(\mathrm U\) and keep every incident bond inside \(G\).
Use \(\lambda_{\mathrm U},\lambda_{\mathrm D}\) at the corresponding
sites and define
\[
 Z_D^\tau[f]=\sum_n f(n)
       \prod_{\text{present }\{x,y\}}(1+n_x\cdot n_y)
       \prod_{\substack{(x,z)\in\mathcal L(G)\\x\in S}}
                   (1+\tau_{xz}\cdot n_x)
       \prod_{x:\,\mathrm{st}(x)\ne\mathrm X}\lambda_{\mathrm{st}(x)}(n_x).
\]
The sum is over the product of the supports \(D\) at \(\mathrm U\)
sites and \(D\cup\{0\}\) at \(\mathrm D\) sites.
Define the free sum, normalized expectations and \(\Psi_D\) as before.
The class \(\mathcal D_{\mathrm{cons}}(G)\) consists of domains in
which every \(\mathrm U\) site keeps all its bonds, every \(\mathrm D\)
site keeps exactly two, and every bond between nonremoved sites is
kept by both ends or by neither.
An auxiliary network has the same data but permits protected
\(\mathrm U\) sites to have arbitrary kept subsets. It retains every
original leg factor. Neither domains nor auxiliary networks carry
a scalar trace mass. Only the networks occurring below, with at most
four factors at each site, are used.
\end{definition}
```

<a id="latex-d-trace"></a>
**d:trace.**

Lean: `AKLT.Defs.Network.AdmissibleStart`, `AKLT.Defs.traceStep`, `AKLT.Defs.traceNetwork`, `AKLT.Defs.traceCoefficient`, `AKLT.Defs.traceRatio`, `AKLT.Defs.wordVertices`, `AKLT.Defs.StoppedNetworkTrail`, `AKLT.Defs.stoppedNetworkTrails`.

```latex
\begin{definition}\label{d:trace}
A trail uses distinct present unoriented bonds. Its prefixes are
\(w_j=(v_0,\ldots,v_j)\), and \(\mathcal T_D(u,T)\) denotes trails
starting at \(u\) and stopping at their first hit of \(T\).
No trail departs from \(S\).
At departure from \(y=v_{j-1}\), drop \(\{y,v_j\}\) at both ends.
If \(y\) is \(\mathrm U\), change it to \(\mathrm D\), keeping its
other kept bonds. If \(y\) is \(\mathrm D\), remove it.
Call the resulting network \(D[w_j]\), with \(D[w_0]=D\).
Admissible initial starts are unpinned sites outside \(S\) of status
\(\mathrm U\) with at most three present bonds, or status \(\mathrm D\)
with at most one. The same restrictions then hold at every later
departure. Set
\[
 a_D(w)=3^{-N_{\mathrm U}(w)}5^{-N_{\mathrm D}(w)},\qquad
 R_D^\bullet(w)=Z^\bullet_{D[w]}/Z^\bullet_D,
\]
where the counts record the status at departure, not the original status.
Original legs are always unchanged, including at a terminal hit of \(S\).
\end{definition}
```

<a id="latex-p-pairwalk"></a>
**p:pairwalk.**

Lean: `AKLT.Defs.AdmissibleTarget`.

```latex
\begin{proposition}\label{p:pairwalk}
Let \(D\) be a domain or auxiliary network, and let \(u\) be an
admissible initial start. Let \(v\ne u\) be nonremoved; if it is
\(\mathrm U\), assume at most three incident factors, counting
original legs; if it is \(\mathrm D\), assume at most one present bond.
Put \(T=S\cup\{v\}\). For \(\bullet=\tau,0\),
\[
 \mathbb E_D^\bullet(n_u\cdot n_v)=
 \sum_{w\in\mathcal T_D(u,T)}a_D(w)R_D^\bullet(w)
           \mathbb E_{D[w]}^\bullet(n_{v_{|w|}}\cdot n_v).
\]
If the endpoint is \(v\), its last factor is independent of the
choice of \(\bullet\): it is \(1\) for status \(\mathrm U\),
and \(3/5\) for status \(\mathrm D\).
Every partition product with an inserted observable used in this
identity has separate degree at most four.
\end{proposition}
```

<a id="latex-d-ratios"></a>
**d:ratios.**

Lean: `AKLT.Defs.removeSite`, `AKLT.Defs.stepRatio`, `AKLT.Defs.removedPairMean`, `AKLT.Defs.responseI`, `AKLT.Defs.responseJ`.

```latex
\begin{definition}\label{d:ratios}
At a step \(j\), put
\(\rho_j^\bullet=Z^\bullet_{D[w_j]}/Z^\bullet_{D[w_{j-1}]}\).
At a \(\mathrm D\) departure \(\rho_j^\tau=\rho_j^0=1\).
At a \(\mathrm U\) departure from \(y\) to \(o\), let \(E'\)
be the pre-step network with \(y\) removed.
If the other present neighbours are \(f,g\), set
\[
 I=1+\tfrac13(P_{fg}+P_{fo}+P_{go}),\quad
 J=1+\tfrac15P_{fg},\quad P_{ab}=n_a\cdot n_b,\qquad
 (\rho_j^\bullet)^{-1}=\mathbb E_{E'}^\bullet I/
                                      \mathbb E_{E'}^\bullet J.
\]
With only one other neighbour \(f\), use \(I=1+P_{fo}/3,\ J=1\);
with no other neighbour, \(\rho_j^\bullet=1\).
Straight/turning refers to the incoming direction, with a designated
absent incoming bond at the first step.
\end{definition}
```

<a id="latex-l-response"></a>
**l:response.**

Lean: `AKLT.Defs.responseBeta`, `AKLT.Defs.responseAlpha`, `AKLT.Defs.responseBetaPrime`, `AKLT.Blueprint.Top.ResponseStatement`.

```latex
\begin{lemma}\label{l:response}
At a \(\mathrm U\) departure \(y\notin S\), write
\(r_{ab}=\mathbb E^\tau_{E'}P_{ab}-\mathbb E^0_{E'}P_{ab}\).
With three present neighbours,
\[
 \log\rho_j^0-\log\rho_j^\tau
       =\alpha_jr_{fg}+\beta_j(r_{fo}+r_{go}),\qquad
 0<\alpha_j\le\bar\alpha=\frac{18094}{100000},\quad
 0<\beta_j\le\bar\beta=\frac{36751}{100000}.
\]
With two present neighbours the response is \(\beta_j'r_{fo}\),
where \(0<\beta_j'\le35510/100000\le\bar\beta\);
with one it is zero. Also \(\rho_j^0\le1\) and
\(\rho_j^\tau\le12/5\).
A \(\mathrm D\) departure has zero logarithmic response.
\end{lemma}
```

<a id="latex-d-pattern"></a>
**d:pattern.**

Lean: `AKLT.Defs.templateSites`, `AKLT.Defs.templateTips`, `AKLT.Defs.templateCorners`, `AKLT.Defs.externalSlot`, `AKLT.Defs.PatternData`, `AKLT.Defs.PatternData.statusAt`, `AKLT.Defs.PatternData.keptAt`, `AKLT.Defs.PatternData.Covered`, `AKLT.Defs.PatternData.bonds`, `AKLT.Defs.PatternData.active`, `AKLT.Defs.PatternData.spins`, `AKLT.Defs.patternFunctional`, `AKLT.Defs.patternCurrent`, `AKLT.Defs.patternNext`.

```latex
\begin{definition}\label{d:pattern}
Let \(\mathsf T=\{z:d(z,0)\le2\}\), with passage site \(0\),
arrival site \(\mathsf s=(0,-1)\), other neighbours
\(\mathsf e=(1,0),\mathsf N=(0,1),\mathsf W=(-1,0)\),
four corners \((\pm1,\pm1)\), and tips \((\pm2,0),(0,\pm2)\).
The external slots are the two external bonds at each corner and
the three at each tip, twenty in total.
A pattern chooses an out-neighbour \(o\in\{\mathsf e,\mathsf N,\mathsf W\}\)
and statuses/kept sets with the following rules.
The passage site is \(\mathrm U\) and keeps precisely its three
non-arrival bonds. The arrival site is removed or is \(\mathrm D\)
keeping two of its three non-passage bonds.
Each other neighbour is \(\mathrm U,\mathrm X\), or \(\mathrm D\)
keeping its passage bond and one other bond; \(o\) is not removed.
Each corner is \(\mathrm U,\mathrm X\), or \(\mathrm D\) keeping
two of its four bonds. Every \(\mathrm U\) site other than the
passage site keeps all four bonds.
Between nonremoved non-tip sites, a bond is kept by both ends or
by neither. Tips are covering \(\mathrm U\) sites; their bond to
a neighbour \(z\) is present exactly when \(z\) is nonremoved and
keeps that bond. No consistency condition with a global tip kept
set is imposed.
For \(m\in(\mathbb S^2)^{20}\), include every external slot factor
at every nonremoved corner and tip, including both corner slots
when the corresponding actual external bonds are missing.
Let \(Z_{\rm cur}(\pi;m)\) be the finite product functional of
all present template bonds and these slots, using the status laws.
Let \(Z_{\rm next}(\pi;m)\) change the passage law to
\(\lambda_{\mathrm D}\) and drop its out-bond.
The resulting class is \(\mathcal P_{\rm ext}\); it is straight
when \(o=\mathsf N\), and turning otherwise.
\end{definition}
```

<a id="latex-h-H1"></a>
**h:H1.**

Lean: `AKLT.Defs.LocalPatternBound`, `AKLT.Blueprint.Top.H1Statement`.

```latex
\begin{definition}[(H1)]\label{h:H1}
For \(c_{\mathrm s},c_{\mathrm t}\in(0,1]\), (H1) means that
for every \(\pi\in\mathcal P_{\rm ext}\) and every
\(m\in(\mathbb S^2)^{20}\),
\[
 Z_{\rm cur}(\pi;m)\ge c_{\rm type(\pi)}Z_{\rm next}(\pi;m).
\]
In the paper the fixed thresholds are
\(c_{\mathrm s}=961/1000\), \(c_{\mathrm t}=187/200\).
No minimum, minimizing pins, or optimal inversion is asserted.
\end{definition}
```

<a id="latex-l-local"></a>
**l:local.**

Lean: `AKLT.Defs.normalizeRotation`, `AKLT.Defs.CoveredDeparture`.

```latex
\begin{lemma}\label{l:local}
At any \(\mathrm U\) departure outside \(S\) whose normalized
non-tip template data belong to \(\mathcal P_{\rm ext}\), (H1)
implies \(\rho_j^\tau\le1/c_{\rm type}\).
The conclusion is uniform in all original unit pins, all outside
spins of norm at most one, all missing external factors, and all
actual tip statuses and kept sets allowed by the ordinary-domain rules.
\end{lemma}
```

<a id="latex-d-weights"></a>
**d:weights.**

Lean: `AKLT.Defs.localThreshold`, `AKLT.Defs.passageFactor`, `AKLT.Defs.DirectionWord`, `AKLT.Defs.wordVertex`, `AKLT.Defs.wordBond`, `AKLT.Defs.IsTrail`, `AKLT.Defs.wordIncoming`, `AKLT.Defs.wordStraight`, `AKLT.Defs.departureCount`, `AKLT.Defs.wordRevisit`, `AKLT.Defs.trailWeight`, `AKLT.Defs.trailBaseWeight`.

```latex
\begin{definition}\label{d:weights}
Put \(x_{\mathrm s}=1/c_{\mathrm s}\), \(x_{\mathrm t}=1/c_{\mathrm t}\).
A lattice trail \(w=(v_0,\ldots,v_n)\) has distinct unoriented
nearest-neighbour bonds. Give it a designated unit incoming direction
\(a\), and forbid \(v_1-v_0=-a\) when \(n\ge1\); the virtual
incoming bond is not itself a used bond of the trail.
For departure \(i\), \(0\le i<n\), give weight \(1/5\) if \(v_i\)
has been departed from earlier, and otherwise weight \(x_{\mathrm s}/3\)
for continuing in the incoming direction and \(x_{\mathrm t}/3\)
for a turn. Let \(\mathsf W(w)\) be the product, with
\(\mathsf W(\varnothing)=1\).
\end{definition}
```

<a id="latex-h-H2"></a>
**h:H2.**

Lean: `AKLT.Defs.OpenTrailBound`, `AKLT.Blueprint.Top.H2Statement`.

```latex
\begin{definition}[(H2)]\label{h:H2}
For \(C_V\ge1\) and \(0<q<1\), (H2) means that for every
integer \(n\ge0\), every start and every designated incoming direction,
\[
 \sum_{\substack{|w|=n\\\text{initial reversal forbidden}}}
                      \mathsf W(w)\le C_Vq^n .
\]
The sum is over plane lattice trails with those specified initial data.
\end{definition}
```

<a id="latex-d-pairenv"></a>
**d:pairenv.**

Lean: `AKLT.Defs.PairType`, `AKLT.Defs.HasPairType`, `AKLT.Defs.Network.ResponsePair`, `AKLT.Defs.responseEnvelope`.

```latex
\begin{definition}\label{d:pairenv}
For \(D\in\mathcal D_{\rm cons}(G)\), let \(P_B(D)\) and \(P_C(D)\)
be the ordered nonremoved pairs \((u,v)\) at distance two,
collinear or diagonal respectively, with a designated common neighbour
\(c\) of status \(\mathrm X\). Each endpoint is \(\mathrm U\),
or \(\mathrm D\) with at most one present bond.
For integer \(d\ge0\), let \(F_X(d)\) be the supremum of
\[
 \left|\mathbb E_D^\tau(n_u\cdot n_v)
                    -\mathbb E_D^0(n_u\cdot n_v)\right|
\]
over every finite \(G\), every original unit-pin assignment,
every \(D\in\mathcal D_{\rm cons}(G)\), and every pair in \(P_X(D)\)
with \(\min\{d(u,S(G)),d(v,S(G))\}\ge d\).
Use supremum zero for an empty class, and set \(F_X(d)=F_X(0)\)
for negative integers. Thus \(0\le F_X\le2\), and \(F_X\)
is nonincreasing.
\end{definition}
```

<a id="latex-l-log-mean-bounds"></a>
**l:log-mean-bounds.**

Lean: `AKLT.Defs.logarithmicMean`, `AKLT.Defs.reciprocalLogMean`, `AKLT.Defs.logMeanLower`, `AKLT.Defs.logMeanUpper`, `AKLT.Defs.alphaBound`, `AKLT.Defs.betaBound`, `AKLT.Defs.betaPrimeBound`, `AKLT.Blueprint.Top.LogMeanBoundsStatement`.

```latex
\begin{lemma}\label{l:log-mean-bounds}
Let \(\mathcal L(x,y)=(x-y)/(\log x-\log y)\) for \(x\ne y\)
and \(\mathcal L(x,x)=x\), for positive \(x,y\).
Put \(f(s)=1/\mathcal L(s,1)\), so \(f(1)=1\).
For \(3/5\le c\le1\), the function
\[
 G_c(x,y)=\frac1{3\mathcal L(cx,y)}-\frac1{5\mathcal L(x,y)}
\]
is nonincreasing in each positive variable. In particular,
for \(x\ge a=116/125\), \(y\ge1\),
\[
 G_c(x,y)\le f(ac)/3-f(a)/5.
\]
For rational \(0<s<1\), put \(t=(1-s)/(1+s)\) and
\[
 f_-(s)=\frac2{1-s}\sum_{k=0}^{7}\frac{t^{2k+1}}{2k+1},
 \qquad
 f_+(s)=f_-(s)+\frac{2t^{17}}{17(1-t^2)(1-s)}.
\]
Then \(f_-(s)\le f(s)\le f_+(s)\).
For the two rows of the following table, all numbers are exact rationals:
\[
 \begin{array}{c|c|ccc}
 \tau&c_\tau&a_\tau&b_\tau&b'_\tau\\ \hline
 {\rm s}&961/1000&145217/10^6&352782/10^6&340008/10^6\\
 {\rm t}&187/200&150000/10^6&357549/10^6&344661/10^6
 \end{array}
\]
They satisfy
\[
 \frac{f_+(ac_\tau)}3-\frac{f_-(a)}5\le a_\tau,\qquad
 \frac{f_+(ac_\tau)}3\le b_\tau,\qquad
 \frac{f_+(c_\tau)}3\le b'_\tau,\qquad
 0<b'_\tau\le b_\tau .
\]
\end{lemma}
```

<a id="latex-l-response-typed"></a>
**l:response-typed.**

Lean: `AKLT.Blueprint.Top.ResponseTypedStatement`.

```latex
\begin{lemma}\label{l:response-typed}
Fix \(c_{\rm s}=961/1000\), \(c_{\rm t}=187/200\) and assume (H1).
At a covered \(\mathrm U\) departure of type \(\tau\in\{{\rm s},{\rm t}\}\),
the response coefficients in Lemma~\ref{l:response} satisfy
\[
 0<\alpha_j\le a_\tau,\qquad 0<\beta_j\le b_\tau
       \quad\hbox{with three present neighbours},\qquad
 0<\beta'_j\le b'_\tau\quad\hbox{with two}.
\]
Here the exact constants are those of Lemma~\ref{l:log-mean-bounds};
in particular \(a_{\rm t}=150000/10^6\).
With \(a=116/125\), their analytic bounds are
\[
 \beta_j\le f(ac_\tau)/3,\qquad
 \beta'_j\le f(c_\tau)/3,\qquad
 \alpha_j\le f(ac_\tau)/3-f(a)/5.
\]
These follow using \(I^\tau\ge c_\tau J^\tau\),
\(I^0\ge J^0\ge1\), and \(J^\tau\ge a\).
Also \(a_\tau\le18094/100000\) and
\(b_\tau,b'_\tau\le36751/100000\).
\end{lemma}
```

<a id="latex-d-kernel"></a>
**d:kernel.**

Lean: `AKLT.Defs.kernelStart`, `AKLT.Defs.kernelCentre`, `AKLT.Defs.kernelTarget`, `AKLT.Defs.kernelIncoming`, `AKLT.Defs.ClosedTrail`, `AKLT.Defs.deadAt`, `AKLT.Defs.responseNeighbours`, `AKLT.Defs.liveOtherNeighbours`, `AKLT.Defs.responsePairs`, `AKLT.Defs.pairCoefficient`, `AKLT.Defs.responsePairType`, `AKLT.Defs.pairShift`, `AKLT.Defs.responseKappa`, `AKLT.Defs.exposureSum`, `AKLT.Defs.closedContribution`, `AKLT.Defs.kernelLengthCoefficient`, `AKLT.Defs.shiftKernel`, `AKLT.Defs.shiftedKernel`.

```latex
\begin{definition}\label{d:kernel}
For \(X=B,C\), fix \(c=0\), \(u=(-1,0)\), and \(v=(1,0)\)
for \(B\), \(v=(0,1)\) for \(C\).
Let \(\mathcal T_n^X\) be the length-\(n\) plane trails avoiding \(c\),
from \(u\) to their first hit of \(v\), with incoming direction \(u-c\).
A departure is a lattice revisit when its site was departed from earlier.
At a lattice first visit \(i\), put \(x_i=x_{\tau_i}\) according to
its straight/turn type. Of the three neighbours other than the arrival
site, write \(o\) for the outgoing neighbour and \(f,g\) for the others.
A neighbour is dead if it is \(c\) or was departed from twice before \(i\).
The outgoing neighbour of a true trail is not dead.
If \(f,g\) are both live, assign coefficient \(a_{\tau_i}\) to
\(\{f,g\}\), and \(b_{\tau_i}\) to each of \(\{f,o\},\{g,o\}\).
If exactly one of \(f,g\) is live, assign \(b'_{\tau_i}\) to its
pair with \(o\); if neither is live there is no response pair.
The constants are those of Lemma~\ref{l:log-mean-bounds}.
A live pair \(p\) has type \(Y=B,C\) and shift
\[
 s(p)=\max_{z\in p}\min\{d(z,u),d(z,v)\}.
\]
Let \(\kappa_{Y,s}(i)\) sum its assigned coefficients.
For any fixed, \(\theta\)-independent orderings \(\sigma_w\) of lattice
first visits, define
\[
 \begin{split}
 M_{XY,s}
 &=\sum_{n\ge1}\sum_{w\in\mathcal T_n^X}
     3^{-n}(3/5)^{\operatorname{rev}(w)}
     \sum_k\kappa_{Y,s}(\sigma_w(k))
                   \prod_{l\le k}x_{\sigma_w(l)},\\
 M_\theta[X,Y]&=\sum_{s\ge0}M_{XY,s}\theta^{-s}.
 \end{split}
\]
These are nonnegative series. The identity
\(3^{-n}(3/5)^r=3^{-(n-r)}5^{-r}\) retains the mass-free
trace coefficients. This \(M\) is the modified type-dependent kernel,
not the original uniform-coefficient matrix.
\end{definition}
```

<a id="latex-d-kernel-order"></a>
**d:kernel-order.**

Lean: `AKLT.Defs.longOrdering`, `AKLT.Defs.kernelWitness`, `AKLT.Defs.kernelRho`, `AKLT.Defs.witnessKappa`, `AKLT.Defs.firstVisitList`, `AKLT.Defs.shortOrderLE`, `AKLT.Defs.kernelOrdering`.

```latex
\begin{definition}\label{d:kernel-order}
Fix
\[
 h=(1,h_C),\quad h_C=\frac{5404319552844595}{4503599627370496},
 \qquad \rho_0=\frac{993015}{10^6},\qquad L=12 .
\]
For a first visit set \(\kappa_h(i)=\sum_{Y,s}\kappa_{Y,s}(i)h_Y\).
For a closed trail of length \(n\le L\), let \(\sigma_w\) order its
first visits by increasing
\((x_i-1)/(x_i\kappa_h(i))\), with value \(+\infty\) when
\(\kappa_h(i)=0\), breaking ties by increasing path index.
For \(n>L\), list straight first visits in path order and then
turning first visits in path order.
Hereafter \(M_{XY,s}\) and \(M_\theta\) use exactly these orderings.
They do not depend on \(\theta\).
\end{definition}
```

<a id="latex-h-H3"></a>
**h:H3.**

Lean: `AKLT.Defs.kernelPartialRow`, `AKLT.Defs.PositiveVectorBound`, `AKLT.Blueprint.Top.H3Statement`.

```latex
\begin{definition}[(H3\(_h\))]\label{h:H3}
For the type-dependent kernel and fixed orderings of
Definitions~\ref{d:kernel}--\ref{d:kernel-order}, (H3\(_h\)) is the
following mathematical assertion, with the specified \(h,\rho_0\):
for \(X=B,C\) and every integer \(R_0\ge0\),
\[
 \sum_{n=1}^{R_0}\sum_{w\in\mathcal T_n^X}
 3^{-n}(3/5)^{\operatorname{rev}(w)}
 \sum_k\kappa_h(\sigma_w(k))\prod_{l\le k}x_{\sigma_w(l)}
       \le\rho_0h_X .
\]
Equivalently, the full nonnegative sums satisfy \(M_1h\le\rho_0h\).
No bound for the former uniform-coefficient matrix is part of this
contract. Its proof in this revision uses the stationary lattice
Bellman certificates, with no periodic spatial walk or remainder.
\end{definition}
```

<a id="latex-l-Mtheta"></a>
**l:Mtheta.**

Lean: `AKLT.Defs.shiftedKernel`, `AKLT.Blueprint.Top.ShiftedWitness`, `AKLT.Blueprint.Top.MThetaStatement`.

```latex
\begin{lemma}\label{l:Mtheta}
Assume (H2) and (H3\(_h\)) for the type-dependent kernel.
For every \(q^2<\theta\le1\), all entries of \(M_\theta\) are
finite. There exist \(q^2<\theta<1\) and \(\rho_0<\rho<1\)
such that the same vector \(h\) satisfies \(M_\theta h\le\rho h\).
Every shift of a length-\(n\) trail is at most \(n/2+1\), and
each matrix entry is bounded by
\[
 \sum_{n\ge1} n(\bar\alpha+2\bar\beta)
                      C_V q^n\theta^{-n/2-1}.
\]
\end{lemma}
```

<a id="latex-t-rec"></a>
**t:rec.**

Lean: `AKLT.Blueprint.Top.renewalAmplitude`, `AKLT.Blueprint.Top.RecStatement`.

```latex
\begin{theorem}\label{t:rec}
Fix \((c_{\rm s},c_{\rm t})=(961/1000,187/200)\).
Assume (H1), (H2) with any \(C_V\ge1\), \(0<q<1\), and
(H3\(_h\)) for the type-dependent kernel and fixed orderings above.
Then there exist \(A\ge2\) and \(0<\theta<1\) such that
\(\mathsf P(A,\theta)\) holds.
One may take the \(\theta,\rho,h\) supplied by the shifted-witness
lemma and
\[
 A=\frac{\max h}{\min h}\,
       \frac{\max\{2,\,2(12/5)^{24}(C_V/(1-q))^2\}}{1-\rho}.
\]
\end{theorem}
```

<a id="latex-t-H1"></a>
**t:H1.**

Lean: `AKLT.Blueprint.Top.H1TheoremStatement`.

```latex
\begin{theorem}\label{t:H1}
For every \(\pi\in\mathcal P_{\rm ext}\) and every
\(m\in(\mathbb S^2)^{20}\),
\[
 Z_{\rm cur}(\pi;m)\ge
 \begin{cases}
 (961/1000)Z_{\rm next}(\pi;m),&\pi\text{ straight},\\
 (187/200)Z_{\rm next}(\pi;m),&\pi\text{ turning}.
 \end{cases}
\]
\end{theorem}
```

<a id="latex-t-inputs"></a>
**t:inputs.**

Lean: `AKLT.Defs.certifiedRate`, `AKLT.Blueprint.Top.InputsStatement`.

```latex
\begin{theorem}\label{t:inputs}
At \(c_{\rm s}=961/1000\), \(c_{\rm t}=187/200\), (H1) holds
by the operator-only Gram/residual certificates of Appendix D.
Property (H2) holds with
\[
 q=\frac{1119948287353}{1120437614225}<\frac{2499}{2500}<1,
 \qquad C_V=10 .
\]
For the type-dependent coefficients of Lemma~\ref{l:log-mean-bounds},
the orderings and vector \(h\) of Definition~\ref{d:kernel-order},
and \(\rho_0=993015/10^6\), property (H3\(_h\)) holds.
The latter assertion is supplied by five stationary lattice Bellman
certificates with memory \(m=10\), exact prefix \(L=12\ge m+2\),
radius \(R=70\), value scale \(2^{16}\), and coefficient scale
\(2^{48}\), using the checked 3741-state automaton quotient.
\end{theorem}
```

<a id="latex-l-CE"></a>
**l:CE.**

Lean: `AKLT.Defs.conditionalProbability`, `AKLT.Defs.conditionOn`, `AKLT.Defs.eventMass`, `AKLT.Defs.AgreeOutside`, `AKLT.Defs.conditionalExpectation`, `AKLT.Defs.blockDirichlet`.

```latex
\begin{lemma}\label{l:CE}
For a positive probability \(\mu\) on a finite product
\(\Omega=\prod_{x\in V}S_x\), with nonempty finite alphabets,
\(E_U\) is a self-adjoint orthogonal projection preserving constants
and \(\mu\). For real or complex \(f\),
\[
 \langle f,(I-E_U)f\rangle_\mu
   =\mu(\operatorname{Var}_U f)=\|f-E_Uf\|_\mu^2,\qquad
 \operatorname{Var}_\mu f=\mu(\operatorname{Var}_U f)
                          +\operatorname{Var}_\mu(E_Uf).
\]
A finite sum \(\sum_a(I-E_{B_a})\), allowing repeated blocks,
has quadratic form \(\sum_a\mu(\operatorname{Var}_{B_a}f)\).
\end{lemma}
```

<a id="latex-d-memory-automaton"></a>
**d:memory-automaton.**

Lean: `AKLT.Defs.RawWindow`, `AKLT.Defs.MemoryWindow`, `AKLT.Defs.windowArrival`, `AKLT.Defs.windowSuccessor`, `AKLT.Defs.WindowAdmissible`, `AKLT.Defs.StepKind`, `AKLT.Defs.windowKind`, `AKLT.Defs.Compass`, `AKLT.Defs.Compass.step`, `AKLT.Defs.Compass.reverse`.

```latex
\begin{definition}\label{d:memory-automaton}
Let \(\mathcal E=\{{\rm E}=(1,0),{\rm N}=(0,1),
{\rm W}=(-1,0),{\rm S}=(0,-1)\}\).
For \(m\ge1\), \(\Omega_m\) consists of sequences
\(\omega=(d_1,\ldots,d_m)\in\mathcal E^m\) whose path from zero
uses distinct unoriented bonds. Write \(z_0=0\),
\(z_j=\sum_{i\le j}d_i\), and \(a(\omega)=d_m\).
A direction \(d\) is admissible if \(d\ne-d_m\) and
\(\{z_m,z_m+d\}\) is not a used bond of this window.
Its successor is \(\omega d=(d_2,\ldots,d_m,d)\).
Its kind \(k(\omega,d)\) is \({\rm r}\) if
\(z_m\in\{z_0,\ldots,z_{m-1}\}\), otherwise \({\rm s}\)
if \(d=d_m\), and \({\rm t}\) otherwise.
Direction labels remain absolute lattice directions.
\end{definition}
```

<a id="latex-d-memorygrowth"></a>
**d:memorygrowth.**

Lean: `AKLT.Defs.kindWeight`, `AKLT.Defs.memoryMatrix`, `AKLT.Defs.lastWindowWord`, `AKLT.Defs.memoryTrailMass`.

```latex
\begin{definition}\label{d:memorygrowth}
On \(\Omega_m\), define the nonnegative one-step matrix
\[
 \mathsf A_m(\omega,\omega')=
 \sum_{\substack{d\ {\rm admissible}\\\omega d=\omega'}}
 \gamma(\omega,d),\qquad
 \gamma(\omega,d)=
 \begin{cases}1/5,&k={\rm r},\\
 x_{\rm s}/3,&k={\rm s},\\x_{\rm t}/3,&k={\rm t}.
 \end{cases}
\]
For a prescribed start and incoming direction with initial reversal
forbidden, let \(A_n(\omega)\) be the true total \(\mathsf W\)-weight
of length-\(n\) trails whose last \(m\) steps form \(\omega\),
for \(n\ge m\), and let \(W_n=\sum_{|w|=n}\mathsf W(w)\).
The adopted finite test is \(m=6\) and extension length \(1\).
\end{definition}
```

<a id="latex-l-alm"></a>
**l:alm.**

Lean: `AKLT.Defs.openTrailTotal`, `AKLT.Defs.memoryWitnessRatio`, `AKLT.Defs.memoryBaseConstant`, `AKLT.Blueprint.Top.ALMStatement`.

```latex
\begin{lemma}\label{l:alm}
For \(n\ge m\),
\[
 A_{n+1}(\omega')\le\sum_\omega A_n(\omega)\mathsf A_m(\omega,\omega').
\]
If \(v_\omega>0\), \(0<q<1\), and \(\mathsf A_mv\le qv\),
then (H2) holds with
\[
 C_V=\max\left\{
      \max_{0\le r<m}W_rq^{-r},\
      \frac{\max v}{\min v}W_mq^{-m}\right\}.
\]
Any larger finite constant is also valid.
\end{lemma}
```

<a id="latex-l-H2-dihedral"></a>
**l:H2-dihedral.**

Lean: `AKLT.Defs.SquareSymmetry`, `AKLT.Defs.turnLeft`, `AKLT.Defs.reflectDirection`, `AKLT.Defs.symmetryDirection`, `AKLT.Defs.symmetryWord`, `AKLT.Defs.SameWindowOrbit`, `AKLT.Blueprint.Top.H2DihedralStatement`.

```latex
\begin{lemma}\label{l:H2-dihedral}
The dihedral group of the square acts on \(\Omega_m\) by applying
the same lattice symmetry to every direction. This action preserves
admissibility, kind, successor and the weights of \(\mathsf A_m\);
thus \(\mathsf A_m(g\omega,g\omega')=\mathsf A_m(\omega,\omega')\).
For any positive vector constant on these orbits, a row inequality
\((\mathsf A_mv)_\omega\le qv_\omega\) checked at one representative
of every orbit holds on every raw window.
For \(m=6\), \(|\Omega_6|=916\) and there are \(115\) orbits.
\end{lemma}
```

<a id="latex-p-H2-test"></a>
**p:H2-test.**

Lean: `AKLT.Blueprint.Top.H2TestStatement`.

```latex
\begin{proposition}\label{p:H2-test}
At the two fixed H1 thresholds there exists a positive integer
vector \(v\) on \(\Omega_6\), constant on dihedral orbits, with
\[
 \frac{\max v}{\min v}=\frac{250000000000}{46594269069}<6,\qquad
 \max_\omega\frac{(\mathsf A_6v)_\omega}{v_\omega}
       =q_*:=\frac{1119948287353}{1120437614225}<\frac{2499}{2500}.
\]
The weights have common denominator \(D_2=2695605\), with
numerators \(935000,961000,539121\) for \({\rm s},{\rm t},{\rm r}\).
For \(q_*=q_{\rm num}/q_{\rm den}\), the required row test is
\[
 q_{\rm den}\sum_{d\ {\rm admissible}}n_{k(\omega,d)}v_{\omega d}
          \le q_{\rm num}D_2v_\omega .
\]
It suffices to check the \(115\) orbit rows after proving
Lemma~\ref{l:H2-dihedral}; checking all \(916\) raw rows is also valid.
\end{proposition}
```

<a id="latex-l-H2-CV"></a>
**l:H2-CV.**

Lean: `AKLT.Blueprint.Top.H2CVStatement`.

```latex
\begin{lemma}\label{l:H2-CV}
With \(m=6\), \(q=q_*\), and the vector in Proposition~\ref{p:H2-test},
the constant supplied by Lemma~\ref{l:alm} is at most \(10\).
Indeed, uniformly over the prescribed start and incoming direction,
\[
 W_r\le x_{\rm t}^r\quad(0\le r\le6),\qquad
 \max\left\{\max_{r<6}W_rq^{-r},\
                 \frac{\max v}{\min v}W_6q^{-6}\right\}
 \le6\left(\frac{200}{187q}\right)^6<10.
\]
Consequently (H2) holds with the explicit rational constants
\(q=q_*\) and \(C_V=10\).
\end{lemma}
```

<a id="latex-l-automaton-quotient"></a>
**l:automaton-quotient.**

Lean: `AKLT.Defs.MemoryQuotient`, `AKLT.Defs.MemoryQuotient.Correct`, `AKLT.Defs.CompatibleProjection`, `AKLT.Defs.rawBackward`, `AKLT.Defs.quotientBackward`, `AKLT.Blueprint.Top.AutomatonQuotientStatement`.

```latex
\begin{lemma}\label{l:automaton-quotient}
Let \(\pi:\Omega_m\to Q\) be a surjection onto a finite set.
Suppose that windows with the same image have, for each absolute
direction, identical admissibility and kind, and their admissible
successors have the same image. Suppose also that two such windows
have the same final direction whenever their class has an admissible
non-revisit transition.
Then admissibility, kind and successor define a well-defined automaton
on \(Q\). Every phase-and-position transition whose coefficients
depend only on the absolute direction, kind, position, and final
direction on non-revisit edges factors through this automaton.
For every function \(G(\varphi,q,x)\), its pullback by \(\pi\)
intertwines the raw and quotient backward operators. This
intertwining also holds for each finite stopped continuation sum.
\end{lemma}
```

<a id="latex-p-automaton10"></a>
**p:automaton10.**

Lean: `AKLT.Defs.quotientEdgeCount`, `AKLT.Blueprint.Top.Automaton10Statement`.

```latex
\begin{proposition}\label{p:automaton10}
There are \(60092\) raw windows in \(\Omega_{10}\).
The supplied map to \(Q=\{0,\ldots,3740\}\), with its supplied
representative per class, is surjective and satisfies every
hypothesis of Lemma~\ref{l:automaton-quotient}.
Its admissible labelled edges consist of \(2516\) straight,
\(5032\) turning and \(1872\) revisit edges.
\end{proposition}
```

<a id="latex-d-phaseweights"></a>
**d:phaseweights.**

Lean: `AKLT.Defs.Phase`, `AKLT.Defs.phaseTerminal`, `AKLT.Defs.phaseInitial`, `AKLT.Defs.phaseDiagonal`, `AKLT.Defs.phaseTransition`.

```latex
\begin{definition}\label{d:phaseweights}
The phases are \({\rm A},{\rm B},{\rm C},{\rm D}\). Their
diagonal transition weights, in kind order \({\rm s},{\rm t},{\rm r}\), are
\[
 \begin{array}{c|ccc}
 {\rm A}&x_{\rm s}/3&x_{\rm t}/3&1/5\\
 {\rm B}&x_{\rm s}/3&1/3&1/5\\
 {\rm C}&x_{\rm s}/3&1/3&1/5\\
 {\rm D}&1/3&1/3&1/5
 \end{array}
\]
At a first visit with reward \(\kappa_h\), additionally allow
\({\rm A}\to{\rm C}\) with weight \(x_{\rm t}\kappa_h/3\) on a turn,
or \({\rm B}\to{\rm D}\) with weight \(x_{\rm s}\kappa_h/3\)
on a straight passage. No other phase change is allowed.
At a revisit there is no phase change.
Start with weight one in each of \({\rm A},{\rm B}\);
the terminal reward is \(g=(0,0,1,1)\).
For a true trail, use its actual revisit kinds and its actual
type-dependent live-pair reward from Definition~\ref{d:kernel}.
\end{definition}
```

<a id="latex-l-phase-expansion"></a>
**l:phase-expansion.**

Lean: `AKLT.Defs.finiteOperatorSum`, `AKLT.Defs.appendWords`, `AKLT.Defs.takeWord`, `AKLT.Defs.truePhaseCoefficient`, `AKLT.Defs.truePhaseSuffix`, `AKLT.Blueprint.Top.PhaseExpansionStatement`.

```latex
\begin{lemma}\label{l:phase-expansion}
For a true closed trail \(w\) ordered with straight first visits
before turning first visits, its \(h\)-weighted contribution to
\(M_1\) equals the sum over phase histories starting in
\({\rm A}\) or \({\rm B}\) and ending in \({\rm C}\) or \({\rm D}\)
of the products of the weights in Definition~\ref{d:phaseweights}.
Equivalently this sum is
\[
 3^{-|w|}(3/5)^{\operatorname{rev}(w)}
       \sum_k\kappa_h(\sigma_w(k))\prod_{l\le k}x_{\sigma_w(l)}.
\]
Splitting such a phase history at any prefix length gives the
product of its exact prefix weight and its corresponding suffix weight.
\end{lemma}
```

<a id="latex-d-stationary-walk"></a>
**d:stationary-walk.**

Lean: `AKLT.Defs.stationaryReward`, `AKLT.Defs.relaxedReward`, `AKLT.Defs.freeCoefficient`, `AKLT.Defs.stationaryCoefficient`, `AKLT.Defs.stationaryApply`, `AKLT.Defs.freeApply`.

```latex
\begin{definition}\label{d:stationary-walk}
Fix \(X=B,C\), \(d_0\in\{{\rm N},{\rm W},{\rm S}\}\),
the sites \(u,c,v\) of Definition~\ref{d:kernel}, and \(a=u+d_0\).
The state space is
\(\{{\rm A},{\rm B},{\rm C},{\rm D}\}\times Q\times\mathbb Z^2\).
At positions \(c,v\) there are no outgoing transitions.
At any other position \(x\), an admissible automaton direction \(d\)
goes to position \(x+d\) and the quotient successor window.
At \(x=u\) or \(a\), forbid reuse of \(\{u,a\}\) in either
direction and kill every memory-detected revisit departure;
every other allowed departure there has weight \(1/5\),
in the same phase and with no response.
At other positions use the automaton kind and the phase weights.
For a non-revisit response, declare only \(c\) dead among the three
neighbours other than the arrival site, and use the type-dependent
three-neighbour or two-neighbour reward rule of Definition~\ref{d:kernel}.
A transition into \(c\) has zero contribution.
Let \(T_{X,d_0}\) be this nonnegative backward operator, with zero
terminal rows, and \(g(\varphi,q,x)=\mathbf1_{\{x=v\}}g_\varphi\).
The free operator \(\mathsf W\) omits positions and special-site
rules, uses the same quotient automaton and phase weights, and
treats all three response neighbours as live.
\end{definition}
```

<a id="latex-l-stationary-domination"></a>
**l:stationary-domination.**

Lean: `AKLT.Defs.trueContinuationSum`, `AKLT.Defs.stationaryContinuationSum`, `AKLT.Blueprint.Top.StationaryDominationStatement`.

```latex
\begin{lemma}\label{l:stationary-domination}
Let \(P=(v_0,\ldots,v_L)\) be a true prefix avoiding \(c,v\),
with \(v_0=u\), \(v_1=u+d_0\), and \(L\ge m+2\), \(m=10\).
Every true continuation to its first hit of \(v\), together with
each phase history, is dominated by the corresponding path of
\(T_{X,d_0}\) from its prefix phase, last-window class and endpoint.
The comparison holds for every finite suffix horizon and hence
for their nonnegative suprema.
In this comparison:
forgotten true revisits have weight \(1/5\) no greater than any
relaxed first-visit diagonal weight; forgetting dead non-outgoing
neighbours only increases the reward, using \(b'_\tau\le b_\tau\);
and the known-site killing rules cannot kill a true continuation.
Indeed, the known initial departures at times \(0,1\) are outside
the memory at every suffix time, and a memory-detected additional
departure at \(u\) or \(u+d_0\) would be a forbidden third departure.
\end{lemma}
```

<a id="latex-l-Bellman-soundness"></a>
**l:Bellman-soundness.**

Lean: `AKLT.Defs.listBackward`, `AKLT.Blueprint.Top.BellmanSoundnessStatement`.

```latex
\begin{lemma}\label{l:Bellman-soundness}
Let \(T\) be a nonnegative, finitely branching weighted transition
operator on a set of states, with zero rows on a terminal set.
Let \(g\ge0\) be supported on that terminal set.
If a finite-valued function \(F\ge0\) satisfies
\(g+TF\le F\), then for every integer \(n\ge0\),
\[
 \sum_{j=0}^{n}T^jg\le F .
\]
Consequently the nonnegative sum of all finite first-hit path
weights times their terminal rewards is finite and at most \(F\).
It suffices that \(F=g\) on terminal states and \(TF\le F\)
elsewhere.
\end{lemma}
```

<a id="latex-d-stationary-certificate"></a>
**d:stationary-certificate.**

Lean: `AKLT.Defs.certificateRadius`, `AKLT.Defs.certificateValueScale`, `AKLT.Defs.certificateCoefficientScale`, `AKLT.Defs.coefficientCeiling`, `AKLT.Defs.StationaryData`, `AKLT.Defs.StationaryData.extended`, `AKLT.Defs.StationaryData.potential`, `AKLT.Defs.StationaryData.Passes`.

```latex
\begin{definition}\label{d:stationary-certificate}
For a case \((X,d_0)\), fix \(R=70\),
\(B_R=\{-R,\ldots,R\}^2\), \(V=2^{16}\), and \(D_3=2^{48}\).
Supply integers \(Z_{\varphi,q}>0\) and
\(U_{\varphi,q,x}\ge0\), \(x\in B_R\).
Set \(\widetilde U_{\varphi,q,x}=U_{\varphi,q,x}\) inside \(B_R\)
and \(Z_{\varphi,q}\) outside, and \(F=\widetilde U/V\), \(z=Z/V\).
For each individual transition coefficient \(t\) of the exact
stationary or free operator, use the proved rational ceiling
\(\widehat t=p(t)/D_3\), \(p(t)=\lceil D_3t\rceil\);
zero coefficients may be omitted.
The certificate checks all the following:
\[
 \begin{gathered}
 \sum_{\text{free edges }e\text{ from }(\varphi,q)}
       p(t_e)Z_{\operatorname{dest}(e)}
       \le D_3Z_{\varphi,q},\qquad Z_{{\rm C},q},Z_{{\rm D},q}\ge V,\\
 0\le U_{\varphi,q,x}\le Z_{\varphi,q},\qquad
 U_{\varphi,q,c}=0,\qquad U_{\varphi,q,v}=Vg_\varphi,\\
 \sum_{\text{stationary edges }e\text{ from }(\varphi,q,x)}
       p(t_e)\widetilde U_{\operatorname{dest}(e)}
       \le D_3 U_{\varphi,q,x}
       \quad(x\in B_R\setminus\{c,v\}).
 \end{gathered}
\]
All tests are integer inequalities on the regenerated automaton,
directions, phases and lattice sites, not on a trusted supplied matrix.
\end{definition}
```

<a id="latex-l-stationary-local-global"></a>
**l:stationary-local-global.**

Lean: `AKLT.Blueprint.Top.StationaryLocalGlobalStatement`.

```latex
\begin{lemma}\label{l:stationary-local-global}
Every certificate of Definition~\ref{d:stationary-certificate}
defines a finite-valued \(F\) on the entire lattice with
\(F=z\) outside \(B_R\), \(F\le z\), and
\[
 g+T_{X,d_0}F\le F .
\]
For an inside site this follows from its checked integer row and
coefficient ceilings. For an outside site every successor value
is at most its corresponding \(z\), and the exact stationary row
is dominated by the free row; the checked free inequality
implies \(\mathsf Wz\le z\).
Thus \(F\) bounds every stopped continuation as in
Lemma~\ref{l:Bellman-soundness}.
\end{lemma}
```

<a id="latex-d-prefix-bound"></a>
**d:prefix-bound.**

Lean: `AKLT.Defs.prefixPhases`, `AKLT.Defs.FirstDirection`, `AKLT.Defs.SurvivingPrefix`, `AKLT.Defs.firstDirectionPartialRow`, `AKLT.Defs.stationaryPrefixBound`.

```latex
\begin{definition}\label{d:prefix-bound}
For each case \((X,d_0)\), let \(S_{X,d_0}\) be the exact
\(h\)-weighted kernel sum over closed trails of lengths \(1\le n\le L=12\)
with first direction \(d_0\), using their prescribed short-trail orderings.
Let \(\mathcal P_{X,d_0,L}\) be all true length-\(L\) prefixes
avoiding \(c\) and \(v\), with first direction \(d_0\).
For \(P\) in this set, let \(p_\varphi(P)\) be the sum of its
exact phase-history products ending in phase \(\varphi\), starting
with weights one in A and B. Use actual trail revisits, actual dead
neighbours and the type-dependent rewards, with the long-trail
straight-first phase weights.
Write \(x(P)\) for its endpoint and \(q(P)\) for its last-window class.
For the potential of its case define the rational number
\[
 J_{X,d_0}=S_{X,d_0}
       +\sum_{P\in\mathcal P_{X,d_0,12}}\sum_\varphi
                    p_\varphi(P)F(\varphi,q(P),x(P)).
\]
A hit at time \(12\) is in \(S_{X,d_0}\), not in the prefix sum.
\end{definition}
```

<a id="latex-l-prefix-domination"></a>
**l:prefix-domination.**

Lean: `AKLT.Blueprint.Top.PrefixDominationStatement`.

```latex
\begin{lemma}\label{l:prefix-domination}
For every case whose integer certificate passes, the \(h\)-weighted
contribution of all true closed trails of that first direction,
over every length, is at most \(J_{X,d_0}\).
This holds uniformly for every finite length cutoff, with the same
upper bound. The short part uses the exact order through \(12\);
all longer trails split uniquely into a surviving length-\(12\)
prefix and a dominated stopped suffix.
\end{lemma}
```

<a id="latex-l-kernel-reflection"></a>
**l:kernel-reflection.**

Lean: `AKLT.Blueprint.Top.KernelReflectionStatement`.

```latex
\begin{lemma}\label{l:kernel-reflection}
For row B, reflection \((x_1,x_2)\mapsto(x_1,-x_2)\) fixes
\(c,u,v\), interchanges the first directions N and S, and preserves
every trail weight, type, dead pair, shift, \(h\)-reward and
prescribed ordering. Hence the true B/N and B/S kernel contributions
are equal at every length and every finite cutoff.
No corresponding reduction is asserted for row C.
\end{lemma}
```

<a id="latex-p-stationary-check"></a>
**p:stationary-check.**

Lean: `AKLT.Defs.stationaryCases`, `AKLT.Defs.stationaryPrefixCeiling`, `AKLT.Blueprint.Top.StationaryCheckStatement`.

```latex
\begin{proposition}\label{p:stationary-check}
For the five cases B/N, B/W, C/N, C/W, C/S, there exist
integer arrays \(Z,U\) satisfying every check in
Definition~\ref{d:stationary-certificate}, with
\(m=10,L=12,R=70\) and the specified scales.
Their regenerated quotient has \(3741\) states and the spatial
square has \(19881\) sites. Their exact rational prefix evaluations obey
\[
 \begin{array}{c|ccccc}
 (X,d_0)&(B,{\rm N})&(B,{\rm W})&(C,{\rm N})&(C,{\rm W})&(C,{\rm S})\\ \hline
 10^9J_{X,d_0}\ \le&
 351207554&290599163&527872005&380754375&273048088
 \end{array}
\]
Each displayed upper bound denotes an exact integer inequality
after clearing the rational prefix denominator.
\end{proposition}
```

<a id="latex-l-stationary-assembly"></a>
**l:stationary-assembly.**

Lean: `AKLT.Blueprint.Top.StationaryAssemblyStatement`.

```latex
\begin{lemma}\label{l:stationary-assembly}
With the five certified potentials and their exact prefix bounds,
\[
 (M_1h)_B\le2J_{B,{\rm N}}+J_{B,{\rm W}}\le\rho_0h_B,\qquad
 (M_1h)_C\le J_{C,{\rm N}}+J_{C,{\rm W}}+J_{C,{\rm S}}
                                      \le\rho_0h_C ,
\]
where \(h_C=5404319552844595/4503599627370496\) and
\(\rho_0=993015/10^6<1\).
The same inequalities hold for every finite true-trail cutoff;
therefore (H3\(_h\)) holds for the modified kernel.
\end{lemma}
```

<a id="latex-l-Iw"></a>
**l:Iw.**

Lean: `AKLT.Defs.supportSpins`, `AKLT.Defs.withoutPassageFunctional`, `AKLT.Defs.originalPatternPolynomial`, `AKLT.Blueprint.Top.IntegratePassageStatement`.

```latex
\begin{lemma}\label{l:Iw}
Let \(Z_w\) be the finite template functional after deleting
the passage site and its incident factors, retaining all other
present bonds and all covered slot factors. Put \(P_{ab}=n_a\cdot n_b\)
for nonremoved sites and zero if either is removed.
For the out-neighbour \(o\) and the other two neighbours \(f,g\),
\[
 Z_{\rm cur}=Z_w[I],\qquad Z_{\rm next}=Z_w[J]>0,\qquad
 I=1+\tfrac13(P_{fg}+P_{fo}+P_{go}),\quad J=1+\tfrac15P_{fg}.
\]
For \(0<c<1\), \(F_c=Z_{\rm cur}-cZ_{\rm next}=Z_w[I-cJ]\), with
\[
 I-cJ=(1-c)+\tfrac13(P_{fo}+P_{go})+(\tfrac13-\tfrac c5)P_{fg}.
\]
Both partition polynomials are affine in each slot vector and
invariant under simultaneous orthogonal transformations of the slots.
\end{lemma}
```

<a id="latex-l-leaf"></a>
**l:leaf.**

Lean: `AKLT.Defs.coveredSiteField`, `AKLT.Blueprint.Top.LeafStatement`.

```latex
\begin{lemma}\label{l:leaf}
In a covered template, integrating a nonremoved tip or corner
with no present internal bond gives a positive factor depending
only on its own slots.
A tip with its one internal bond to \(x\) gives
\(A(1+(3/5)u\cdot n_x)\), \(A>0,\ |u|\le1\).
A corner with exactly one internal bond to \(x\) gives
\(A(1+\rho u\cdot n_x)\), \(A>0,\ |u|\le1\), where
\(\rho=1/2\) for status \(\mathrm U\) and \(\rho=1/3\)
for status \(\mathrm D\).
\end{lemma}
```

<a id="latex-d-reduction"></a>
**d:reduction.**

Lean: `AKLT.Defs.evaluateReduced`, `AKLT.Defs.Representation`, `AKLT.Defs.patternDegree`, `AKLT.Defs.SingleReplacement`, `AKLT.Defs.reducedSpinSites`, `AKLT.Defs.reductionGroups`, `AKLT.Defs.groupLeader`, `AKLT.Defs.groupSecond`, `AKLT.Defs.groupIsPair`, `AKLT.Defs.reductionVectors`, `AKLT.Defs.replacementRadius`, `AKLT.Defs.leafNeighbour`, `AKLT.Defs.LocalVariable`, `AKLT.Defs.formalDot`, `AKLT.Defs.reducedIntegrand`, `AKLT.Defs.reducedPolynomial`, `AKLT.Defs.reducedDifference`, `AKLT.Defs.GroupInversion`, `AKLT.Defs.leaderToken`, `AKLT.Defs.secondToken`.

```latex
\begin{definition}\label{d:reduction}
Delete tips and corners with no present internal bond, dropping
their common positive factors. Replace every bonded tip by a
single vector and radius \(3/5\).
In the reduced representation also replace each one-bond corner
by a single vector of radius \(1/2\) or \(1/3\) according to
Lemma~\ref{l:leaf}; in the unreduced representation retain its spin
and two slots. Other bonded corners retain their two slots.
Let \(u=(u_1,\ldots,u_k)\) list these remaining vectors, and define
\(\widehat Z_{\rm cur},\widehat Z_{\rm next}\) by these replacements,
\(\widehat F_c=\widehat Z_{\rm cur}-c\widehat Z_{\rm next}\).
A group is one single vector or the two slots of a retained corner.
\end{definition}
```

<a id="latex-c-reduce"></a>
**c:reduce.**

Lean: `AKLT.Blueprint.Top.ReduceStatement`.

```latex
\begin{corollary}\label{c:reduce}
In either representation, \(\widehat F_c\) is real, affine in
each vector and invariant under simultaneous \(\mathrm O(3)\).
If \(\widehat F_c\ge0\) on \((\mathbb S^2)^k\), then
\(F_c\ge0\) on \((\mathbb S^2)^{20}\).
For each original slot assignment there are a common \(K>0\)
and vectors \(\widehat u\) in the closed unit ball such that
\(Z_{\rm cur}=K\widehat Z_{\rm cur}(\widehat u)\) and
\(Z_{\rm next}=K\widehat Z_{\rm next}(\widehat u)\).
\end{corollary}
```

<a id="latex-d-Pauli"></a>
**d:Pauli.**

Lean: `AKLT.Defs.productDensity`, `AKLT.Defs.invertVectors`, `AKLT.Defs.tokenMatrix`, `AKLT.Defs.totalSpinZ`, `AKLT.Defs.totalSpinPlus`, `AKLT.Defs.totalSpinMinus`, `AKLT.Defs.pauli`, `AKLT.Defs.spinDensity`, `AKLT.Defs.VectorAffine`, `AKLT.Defs.invertPolynomial`, `AKLT.Defs.pauliExponent`, `AKLT.Defs.pauliOperator`, `AKLT.Defs.ratComplexMul`, `AKLT.Defs.rationalPauli`, `AKLT.Defs.rationalOperatorEntry`, `AKLT.Defs.SupportedVectors`, `AKLT.Defs.tensorPowerMatrix`.

```latex
\begin{definition}\label{d:Pauli}
For a real polynomial affine in each vector, expand uniquely
\[
 F(u)=\sum_{a\in\{0,1,2,3\}^k}f_a\prod_i u_i^{a_i},
 \qquad u_i^0=1,\qquad
 \mathcal O(F)=\sum_a f_a\bigotimes_i\sigma_{a_i},\quad\sigma_0=I.
\]
For \(\mathcal I\subset\{1,\ldots,k\}\), invert those vectors,
writing \(u^{\mathcal I}\) and \(F^{\mathcal I}(u)=F(u^{\mathcal I})\).
For \(|a|\le1\), put \(\rho(a)=(I+a\cdot\sigma)/2\).
Set \(S_z=\frac12\sum_i\sigma_3^{(i)}\) and
\(S_\pm=\sum_i(\sigma_1^{(i)}\pm\mathrm i\sigma_2^{(i)})/2\).
\end{definition}
```

<a id="latex-l-inversion"></a>
**l:inversion.**

Lean: `AKLT.Blueprint.Top.InversionStatement`.

```latex
\begin{lemma}\label{l:inversion}
For \(|u_i|\le1\), each \(\rho(u_i)\) is positive semidefinite
of trace one, and
\[
 F(u)=\operatorname{Tr}\!\left[
      \mathcal O(F^{\mathcal I})
                 \bigotimes_i\rho((u^{\mathcal I})_i)\right].
\]
Thus a single inversion \(\mathcal I\) with
\(\mathcal O(F^{\mathcal I})\ge0\) implies \(F\ge0\)
on the product of closed unit balls, in particular on unit vectors.
\end{lemma}
```

<a id="latex-l-Ostruct"></a>
**l:Ostruct.**

Lean: `AKLT.Blueprint.Top.OperatorStructureStatement`.

```latex
\begin{lemma}\label{l:Ostruct}
For \(\mathcal I\) a union of vector groups and
\(\mathcal O=\mathcal O(\widehat F_c^{\mathcal I})\),
the matrix in the standard tensor basis is real symmetric.
It commutes with \(U^{\otimes k}\) for every \(U\in\mathrm{SU}(2)\)
and with \(S_z,S_+,S_-\).
For a retained \(\mathrm U\)-corner pair, if \(\Pi\) projects that
pair onto \(\operatorname{Sym}^2\mathbb C^2\), then
\(\mathcal O=\Pi\mathcal O\Pi\).
For a retained \(\mathrm D\)-corner pair, \(\mathcal O\) commutes
with exchange of its two factors.
\end{lemma}
```

<a id="latex-d-exchange"></a>
**d:exchange.**

Lean: `AKLT.Defs.exchangeSpace`, `AKLT.Defs.centralSpace`, `AKLT.Defs.ExchangeSigns`, `AKLT.Defs.GroupBasis`, `AKLT.Defs.ExchangeBasis`, `AKLT.Defs.exchangeWeight`, `AKLT.Defs.centralWeight`, `AKLT.Defs.CentralBasis`, `AKLT.Defs.exchangeBasisVector`, `AKLT.Defs.exchangeOperator`, `AKLT.Defs.symmetricPairProjection`.

```latex
\begin{definition}\label{d:exchange}
Let \(V\) be the tensor product of \(\mathbb C^2\) for singles,
\(\operatorname{Sym}^2\mathbb C^2\) for retained \(\mathrm U\)-pairs,
and \(\mathbb C^2\otimes\mathbb C^2\) for retained \(\mathrm D\)-pairs.
For each assignment \(\epsilon\) of exchange signs to the
\(\mathrm D\)-pairs, let \(V_\epsilon\) replace each of those
pair factors by its symmetric or exterior square.
If there are \(t\) singles, let \(\kappa=0\) for even \(t\),
\(\kappa=1/2\) for odd \(t\), and
\(V_\epsilon^\circ=\ker(S_z-\kappa I)|_{V_\epsilon}\).
The standard sector basis uses \(e_\pm\) for singles and
\(e_+\otimes e_+\), \(e_+\otimes e_-+e_-\otimes e_+\),
\(e_-\otimes e_-\) for symmetric pairs, with
\(e_+\otimes e_--e_-\otimes e_+\) for antisymmetric pairs.
\end{definition}
```

<a id="latex-l-sector"></a>
**l:sector.**

Lean: `AKLT.Defs.PositiveOn`, `AKLT.Defs.eigenvaluesOn`, `AKLT.Blueprint.Top.SectorStatement`.

```latex
\begin{lemma}\label{l:sector}
Let \(V'\) be any tensor sector formed from singles and
symmetric or exterior pair factors as above.
If a Hermitian \(\mathcal O'\) on \(V'\) commutes with
\(S_z,S_+,S_-\), then it preserves the central-weight space
\(V'^\circ\), and its restriction there has the same set of
eigenvalues as \(\mathcal O'\).
In particular \(\mathcal O'\) is positive definite if and only if
that restriction is positive definite.
\end{lemma}
```

<a id="latex-l-gram-residual"></a>
**l:gram-residual.**

Lean: `AKLT.Defs.gramResidual`, `AKLT.Defs.GramResidualRows`, `AKLT.Blueprint.Top.GramResidualStatement`.

```latex
\begin{lemma}\label{l:gram-residual}
Let \(M\) be a symmetric integer matrix of size \(n\).
Let \(g,d,S\) be positive integers and \(L\) an integer
lower-triangular \(n\times n\) matrix; no invertibility is required.
Define the symmetric integer residual
\[
 E=dS^2M-gLL^{\mathsf T}.
\]
If, for every row,
\[
 E_{ii}>0,\qquad E_{ii}>\sum_{j\ne i}|E_{ij}|,
\]
then \(E\) and \(M\) are positive definite over \(\mathbb R\)
and, as Hermitian matrices, over \(\mathbb C\).
The case \(L=0\), \(g=d=S=1\), is the direct strict
diagonal-dominance certificate.
All hypotheses can be checked with integer sums, products,
absolute values and comparisons, without division or determinants.
\end{lemma}
```

<a id="latex-l-integercheck"></a>
**l:integercheck.**

Lean: `AKLT.Defs.rationalSectorEntry`, `AKLT.Defs.ClearsDenominator`, `AKLT.Defs.integerSectorMatrix`, `AKLT.Defs.thresholdSectorMatrix`, `AKLT.Defs.complexSectorMatrix`, `AKLT.Defs.indexedSectorMatrix`, `AKLT.Defs.leadingMinor`, `AKLT.Defs.bareissState`, `AKLT.Defs.bareissPivot`, `AKLT.Blueprint.Top.IntegerCheckStatement`.

```latex
\begin{lemma}\label{l:integercheck}
For \(c=p/q\in(0,1)\) rational with positive integers \(p,q\),
choose a positive integer \(D_0\) clearing the coefficients of
\(3D_0\widehat Z_{\rm cur}\) and \(5D_0\widehat Z_{\rm next}\).
In the integer-coordinate central-sector basis, let \(A_\epsilon\)
and \(A'_\epsilon\) be the Hermitian-form matrices of their
inverted Pauli operators. These are symmetric integer matrices.
The form of \(\mathcal O(\widehat F_c^{\mathcal I})\) on the sector
is positive definite if and only if
\[
 M_\epsilon=5qA_\epsilon-3pA'_\epsilon
\]
is positive definite. The primary verification uses the integer
Gram/residual witness of Lemma~\ref{l:gram-residual}.
As an optional fallback only, positivity is equivalent to positivity of all its
leading principal minors. More explicitly, for a size-\(t\) matrix
set \(A^{(0)}=M_\epsilon\), \(p_{-1}=1\), and for \(0\le j<t\)
set \(p_j=A^{(j)}_{jj}\) and update the trailing entries by
\[
 A^{(j+1)}_{il}
    =\frac{p_jA^{(j)}_{il}-A^{(j)}_{ij}A^{(j)}_{jl}}{p_{j-1}}
       \quad(i,l>j).
\]
As long as preceding pivots are nonzero, each division is exact
in the integers and \(p_j\) is the leading principal minor of
order \(j+1\). Acceptance requires every division exact and every
pivot positive.
\end{lemma}
```

<a id="latex-p-certificate"></a>
**p:certificate.**

Lean: `AKLT.Blueprint.Top.CertificateStatement`.

```latex
\begin{proposition}\label{p:certificate}
Let \(c=p/q\in(0,1)\), with \(p,q\in\mathbb Z_{>0}\).
Choose either allowed representation, an inversion which is a
union of groups, and a justified positive denominator \(D_0\).
For every supported central exchange sector reconstruct
\(M_\epsilon=5qA_\epsilon-3pA'_\epsilon\) as in
Lemma~\ref{l:integercheck}.
Suppose that for each sector there are positive integers
\(g_\epsilon,d_\epsilon,S_\epsilon\) and an integer lower-triangular
matrix \(L_\epsilon\) of its dimension such that
\[
 E_\epsilon=d_\epsilon S_\epsilon^2M_\epsilon
                  -g_\epsilon L_\epsilon L_\epsilon^{\mathsf T},
 \qquad
 (E_\epsilon)_{ii}>
          \sum_{j\ne i}|(E_\epsilon)_{ij}|\quad\text{for every }i.
\]
Then \(F_c(m)\ge0\) for every \(m\in(\mathbb S^2)^{20}\).
The operator may vanish on the discarded antisymmetric
\(\mathrm U\)-pair subspaces; positive definiteness is required
only on the supported exchange sectors.
\end{proposition}
```

