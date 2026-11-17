STATUS: COMPLETE

All eight assigned leaves are **TRUE** and self-sufficient. No corrected statement or additional premise is required. None is globally vacuous.

The names below are in namespace `AKLT.Blueprint.Gap`, module `AKLT.Blueprint.Gap.NodesShell`. The repository snapshot inspected was commit `7a3393531c12080d76aefbdab300ac0c2df834b7`. The repository was read only; all generated files are in this report directory.

| Leaf | Paper label | Verdict | Difficulty | Rationale |
|---|---|---|---|---|
| [FiniteTrialFailureStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:72) | `l:stopped` | TRUE | medium | Stochastic row failure bounds multiply under finite path summation. |
| [TraceDisagreementStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:82) | `l:stopped` | TRUE | easy | Endpoint nonagreement can occur only on the no-success event, up to zero atoms. |
| [TerminalRadiusStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:94) | `p:surgery` | TRUE | medium | Choose h=floor(s); restrict the stopped coupling and compare exponents. |
| [ScaleExistenceStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:107) | `l:hamming` | TRUE | easy | One natural number can exceed all four finite lower thresholds. |
| [BinomialTailStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:112) | `l:hamming` | TRUE | medium | The twentieth binomial term gives the displayed reciprocal bound. |
| [ScaleGeometryStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:118) | `l:hamming` | TRUE | easy | The scale hypotheses give both thresholds and shellSpacing(n^8)=n^2. |
| [HammingCardinalityStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:126) | `l:hamming` | TRUE | medium | Count the near ball and full square by their integer coordinate intervals. |
| [HammingBudgetStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesShell.lean:133) | `l:hamming` | TRUE | easy | Each of the two cost terms is at most n^8/2000. |

The declaration comments contain line references from a different manuscript layout. The paper links below use the actual lines in the supplied `sec4-periodic-gap.tex`.

**Definitions followed.** The finite-probability leaves unfold to [Weight, Probability, totalVariation and Coupling](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:8), [eventMass](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:47), [marginal](/home/ubuntu/aklt/repo/AKLT/Defs/FrameModel.lean:50), and the following local vocabulary:

| Local definitions | Meaning checked |
|---|---|
| [Config, restrict, AgreeOn](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:15) | Dependent functions on physical sites; agreement compares letters at the same site. |
| [disagreement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:81) | Sum of coupling masses over pairs failing AgreeOn. |
| [PlaneSpec, its instances, PlaneConfig, fill, specMarginal](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:106) | Finite nonempty site alphabets; laws are arbitrary real weights. The marginal is a finite pushforward of fill/restrict. |
| [farSites, PairTrace, traceLaw](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:176) | Far sites are a filtered square subtype; a trace has m+1 pair states; step j uses input j.castSucc and output j.succ. |
| [ScaleConditions](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:272) | Exactly the four scale inequalities, with the final one in the reals. |
| [StoppedEstimate](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/Definitions.lean:315) | An explicit hypothesis supplying a full-law coupling for every admissible h and the far-region disagreement bound with natural exponent h-3. |
| [Plane and supDist](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:8), [setDistance](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:58), [square and shellSpacing](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:74), [geometryThreshold](/home/ubuntu/aklt/repo/AKLT/Defs/Geometry.lean:119) | Integer plane, maximum of coordinate natAbs differences, extended-natural infimum distance, inclusive coordinate squares, nested real square roots, and max(16,6(l+1))^4. |

`StoppedEstimate` and the tail inequality are explicit premises in the terminal and budget leaves respectively. Their writers need not establish those premises or assume a different named leaf. No consistency, range-one, colouring, or torus facts are needed by these eight obligations.

**`FiniteTrialFailureStatement` — TRUE; medium.** [Paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:179).

traceLaw is the nonnegative product initial(t 0) * product_j K_j(t j.castSucc)(t j.succ). Every selected transition has failure row mass at most 1-delta; unselected rows have mass 1. Summing the finite path law gives the claimed product bound without independence. Empty J (including m=0) gives event mass 1 and power 0; delta=1 with nonempty J gives zero. Probability initial excludes an empty state space. Lean traps: retain the explicit Fintype Omega instance, use classical decidability for arbitrary E, and use j.castSucc for input and j.succ for output.

Proof route:

1. Restrict each selected kernel row to the complement of E j, whose total mass is at most 1-delta; leave other rows stochastic.
2. Sum paths backwards (or induct on time), multiplying one factor 1-delta for each member of J and using the normalized initial law.

**`TraceDisagreementStatement` — TRUE; easy.** [Paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:164).

The endpoint marginal identity rewrites disagreement as the w-mass of endpoint nonagreement. On every positive w atom, the stated implication makes endpoint nonagreement imply failure of every selected event. Nonnegative zero atoms contribute nothing, so event-mass monotonicity gives the inequality. Nonempty site alphabets are unnecessary: if Config S is empty then Probability w is impossible, and an empty site set has disagreement zero. Lean traps: distinguish Config S, its pair type, and PairTrace; use classical logic to negate the existential and avoid extending the implication to zero atoms.

Proof route:

1. Expand disagreement and marginal, interchange the finite sums, and identify the endpoint nonagreement indicator under w.
2. For each path split w t=0 versus w t>0, apply the support implication contrapositively, and sum the resulting nonnegative indicator inequality.

**`TerminalRadiusStatement` — TRUE; medium.** [Paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:200).

Write s=sqrt(sqrt u), beta=1-p*alpha^(16*l), and h=floor(s) in the naturals. The stated threshold implies s>=16, so h>=4 and the stopped estimate applies. Since h*s<=s^2=sqrt u, its agreement region contains the target filter. A nonnegative full-law coupling bounds target marginal half-L1 variation by its disagreement mass, even without normalized laws. Finally h-3>=s-4>0 and 0<=beta<1 give the real-power bound, with beta=0 treated separately. Lean traps: StoppedEstimate has a natural exponent, the conclusion a real exponent; no RegularSpec or Probability law premise is available, so use the homogeneous coupling inequality rather than a lemma restricted to probability laws.

Proof route:

1. Choose h=Nat.floor(s), obtain the stopped coupling, and restrict it to the target subset to bound total variation by beta^(h-3).
2. Use the floor inequality and antitonicity in the exponent for positive beta; for beta=0 both exponents are positive, so both powers vanish.

The target volume is a filter of the original square, so both occurrences of `specMarginal` use the same coordinate restriction: `fill` never reads their different exterior values at a target site. Although the existing [CouplingMarginalTVStatement](/home/ubuntu/aklt/repo/AKLT/Blueprint/Gap/NodesFinite.lean:51) assumes normalized laws, its elementary half-L1 coupling bound is homogeneous. A writer should establish that more general finite-sum bound here instead of attempting to derive normalization from `StoppedEstimate`. Adding `RegularSpec P` is unnecessary.

**`ScaleExistenceStatement` — TRUE; easy.** [Paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:249).

ScaleConditions consists exactly of four lower bounds on n: n>=44, n^8>=Mstar, n^2>=max(50000,6*(l+1)), and n^12*d^20>=50000*2^20*20!. For every real d>0, d^20 is positive and the last bound is finite; one natural n can exceed all four thresholds. The choice precedes all translates, specifications, boundaries and torus sizes. Lean traps: the first three inequalities are natural, the last real; cast the factorial, powers, and n consistently. An upper bound d<=1/2 is unnecessary for existence.

Proof route:

1. Let C=50000*2^20*(20! : R) and choose a natural n above 44, Mstar, max(50000,6*(l+1)), and C/d^20 using the Archimedean property.
2. Since n>=1, n<=n^2,n^8,n^12; these stronger lower bounds imply all four ScaleConditions after multiplying the last one by positive d^20.

**`BinomialTailStatement` — TRUE; medium.** [Paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:261).

For r=n-3 and n>=44, r>=41 and each of the 20 falling factors r,r-1,...,r-19 is at least n-22>=n/2>0. Since 0<d<=1/2, (1-d)^(-1)>=1+d>0. The twentieth term of the binomial expansion therefore bounds (1-d)^(-r) below by n^20*d^20/(2^20*20!), and reciprocation gives exactly the displayed inequality. Lean traps: n-3 is truncated natural subtraction, harmless because n>=44; 1/2 is real division, factorial is cast to R, and d^20*n^20 is strictly positive.

Proof route:

1. Set r=n-3, compare ((1-d)^(-1))^r with (1+d)^r, and retain the nonnegative twentieth binomial term.
2. Bound its falling factors below by n/2, cancel the positive factorial, and take reciprocals using d>0, n>=44 and 1-d>0.

**`ScaleGeometryStatement` — TRUE; easy.** [Paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:280).

ScaleConditions gives n>=44 and n^2>=max(50000,6*(l+1)). Consequently max(16,6*(l+1))<=n^2, so geometryThreshold l<=n^8; the Mstar bound is already present. As n is natural, sqrt(sqrt((n^8 : N) : R))=(n : R)^2. Thus n<=shellSpacing(n^8), n*shellSpacing(n^8)=n^3, and shellSpacing(n^8)>=16. No premise on the sign of d is needed: its inequality is unused. Lean traps: shellSpacing is nested real square roots, not an integer fourth root; cast natural powers before simplifying the roots.

Proof route:

1. Use the first three ScaleConditions clauses to bound both Mstar and geometryThreshold l by n^8, and infer n>=4.
2. Rewrite shellSpacing(n^8) as (n:R)^2 using nonnegative square-root identities, then finish the index, radius and spacing claims arithmetically.

**`HammingCardinalityStatement` — TRUE; medium.** [Paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:291).

The complement of farSites is the subset of square a (n^8) at sup-distance at most n^3 from y. Its coordinate inclusion injects into the integer square of radius n^3 about y, which has (2*n^3+1)^2 sites; the full square has exactly (2*n^8+1)^2 sites. For n>=1 these are at most 9*n^6 and 9*n^16, hence at most the stated 25 multiples. No exterior-site or location hypothesis on y is needed. Lean traps: Finset.univ here has type Finset (square a (n^8)), not Finset Plane; Fintype.card of the square is the cardinality of its finite subtype; the strict far inequality becomes a non-strict near inequality. The n>=1 premise excludes n=0, where the second bound would be 1<=0.

Proof route:

1. Map the near-site subtype injectively into the integer coordinate product [y1-n^3,y1+n^3] x [y2-n^3,y2+n^3], and count both coordinate intervals.
2. Count the full translated square similarly; cast the two natural cardinalities to R and use n>=1 to bound each side length by 3*n^k, which is stronger than the required constants.

**`HammingBudgetStatement` — TRUE; easy.** [Paper argument](/home/ubuntu/aklt/manuscript-v2/sec4-periodic-gap.tex:298).

ScaleConditions implies n>=44, n^2>=50000 and n^12*d^20>=50000*2^20*20!. Thus 25*n^6<=n^8/2000. Multiplying the explicitly assumed tail bound by nonnegative 25*n^16 and using the last scale inequality bounds the other term by n^8/2000. Their sum is exactly the stated budget. All divisors are positive since d>0 and n>=44; no independent tail lemma or specification assumptions are needed. Lean traps: the exponent n-3 is natural subtraction, whereas ((n^8 : N) : R)/1000 is real division; rewrite Nat.cast_pow before cancelling real powers. The premise d<=1/2 is harmless but not needed for this algebraic implication once the tail bound is assumed.

Proof route:

1. Use n^2>=50000 to bound the near term by (n:R)^8/2000, and apply the supplied tail inequality to the far term.
2. Cancel only positive d^20 and powers of n, use n^12*d^20>=50000*2^20*20! to get the second (n:R)^8/2000 bound, then add and rewrite the cast of n^8.

**Shared Lean and degenerate-case checks.**

- Lean printing retained the quantified `Fintype` instances and the explicit `DecidableEq` binder. `TraceDisagreementStatement` needs no per-site `Nonempty` assumption. Arbitrary event predicates and configuration equalities can be handled with `classical`.
- All relevant divisions are real divisions. In particular `1/2` is not natural division, and the budget right-hand side casts `n^8` to the reals before dividing by 1000. The tail and scale reciprocals have positive denominators.
- The tail exponent `n-3` and stopped exponent `h-3` use natural subtraction; their lower bounds remove truncation concerns. The terminal exponent `shellSpacing u-4` is real, requiring real-power conversion and a separate zero-base check.
- An empty trial set, including m=0, gives the power-zero bound 1. For delta=1 and a nonempty trial set the failure mass is zero. Empty probability state spaces contradict the normalization premise, but this does not make either general leaf vacuous. An empty site set has its unique empty configuration.
- The square always contains its center. An empty filtered target has a unique empty restriction and zero marginal variation. An arbitrary location of y is allowed in the cardinality leaf. Its hypothesis n>=1 is necessary: n=0 would make the full-square bound read 1<=0.

**Validation.** [Lean inspection input](/home/ubuntu/aklt/reports/TS_GAP_07/scratch/inspect.lean) imported the existing compiled module and printed all eight declarations with Lean 4.35.0-rc2; it exited successfully. The [saved output](/home/ubuntu/aklt/reports/TS_GAP_07/scratch/inspect.txt) also prints explicit power and division types for the binomial and terminal statements. This was one Lean process; no proofs or sorry declarations were written and no library rebuild was requested.

The reproducible [Python checks](/home/ubuntu/aklt/reports/TS_GAP_07/scratch/checks.py) passed 120 finite-chain models, 320 coupling checks with unnormalized masses, 120 exact rational binomial-tail cases, 375 translated cardinality checks, 30 scale checks, 24 algebraic budget checks, and 6 terminal floor checks. These checks include the permitted endpoints and supplement the mathematical audit; they are not formal proofs. [Results](/home/ubuntu/aklt/reports/TS_GAP_07/scratch/checks.txt).

The machine-readable deliverable is [verdicts.jsonl](/home/ubuntu/aklt/reports/TS_GAP_07/verdicts.jsonl). Every entry contains its reason, fix field, two-line proof route, and difficulty.
