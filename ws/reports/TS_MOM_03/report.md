STATUS: COMPLETE

| Leaf | Verdict | Decisive check | Difficulty |
|---|---|---|---|
| `AKLT.Blueprint.Mom.FactorizedConditioningStatement` | TRUE | Positive fibre mass permits rank-one cancellation, including signed factors. | medium |
| `AKLT.Blueprint.Mom.TripleNormalizerStatement` | TRUE | The explicit U average gives exactly 1 + tripleP/3 for arbitrary fields. | medium |
| `AKLT.Blueprint.Mom.TripleNumeratorStatement` | TRUE | Second and fourth tensors give all three numerator coordinates with factor 15. | hard |
| `AKLT.Blueprint.Mom.TripleGeometryStatement` | TRUE | Squared norms of the sum and pairwise differences give all four inequalities. | easy |
| `AKLT.Blueprint.Mom.TripleSOSIdentityStatement` | TRUE | Exact Gram expansion agrees under precisely the three unit equalities. | medium |
| `AKLT.Blueprint.Mom.BallFieldSplitStatement` | TRUE | Normalize nonzero fields; use weight 1/2 and a fixed unit vector at zero. | medium |
| `AKLT.Blueprint.Mom.ProductMixtureStatement` | TRUE | Pad to three factors and expand eight sign choices; k=0 and zero weights work. | medium |
| `AKLT.Blueprint.Mom.PositiveMixtureEstimateStatement` | TRUE | The denominator is at least 1/2; reweight by t*A and use squared-norm convexity. | medium |

All eight leaves are true and self-sufficient as written. No missing premise, counterexample, or unintended vacuity was found. No correction is required. Difficulty estimates concern Lean proofs from the existing imports without assuming another unproved blueprint leaf; deriving the concrete fourth-moment identities makes the numerator leaf the largest task.

The audit used repository branch `main`, commit `7a3393531c12080d76aefbdab300ac0c2df834b7`, and the exact declarations in [NodesFinite.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesFinite.lean:95) and [NodesMean.lean](/home/ubuntu/aklt/repo/AKLT/Blueprint/Mom/NodesMean.lean:28). The paper sources are [Lemma l:finitefacts](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:126) and [Lemma l:35](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:197), together with the explicit moment argument in [Lemma l:moments](/home/ubuntu/aklt/manuscript-v2/sec2-moments.tex:35). The repository was read only.

Definition chains were traced through [Moment.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Moment.lean:8), [Probability.lean](/home/ubuntu/aklt/repo/AKLT/Defs/Probability.lean:8), and [FiniteNetwork.lean](/home/ubuntu/aklt/repo/AKLT/Defs/FiniteNetwork.lean:35), and the node-local definitions `twoSiteFibre`, `tripleP`, `tripleV`, and `tripleSOS`. In particular:

- `Vec3 = Fin 3 → ℝ`, `dot a b = ∑ i, a i*b i`, `normSq a = dot a a`, and `UnitVector = {a // normSq a = 1}`.
- `SpinLetter = Option (Fin 3 × Fin 2 × Fin 2)` has thirteen labels. `siteFunctional .U` gives `none` weight zero and each geometric label weight `1/12`. Its nonzero vectors are exactly the twelve signed coordinate vectors specified by `icoVector`, `signValue`, `goldenRatio`, and `icoRadius`.
- `localProduct` multiplies over every index in `Fin k`; its empty product is one. The triple definitions use exactly the three pairwise dot products and the paper's scalar and vector coefficients.
- `normalize w` divides by the actual finite sum of `w`. `eventMass` is an indicator sum. `conditionalProbability` divides the joint indicator sum by the same event mass. `twoSiteFibre` imposes agreement precisely off the two named sites.

The moment identities needed by the first two triple leaves follow from these fixed definitions. They are not unstated assumptions on an arbitrary law. The imported `siteLawDecomposition` is a proved helper, whereas declarations such as `SecondScalarMomentStatement` and `FourthScalarMomentStatement` are propositions and cannot be used as proofs by themselves. A writer may need to establish the corresponding finite-sum calculations locally.

**FactorizedConditioningStatement — TRUE, medium.**

For x != y, the two-site fibre is in bijection with SpinLetter x SpinLetter. Writing T=sum w, U=sum u and V=sum v, its raw mass is S=C*U*V. Nonnegative w and strictly positive eventMass(normalize w,E) imply T>0 and S>0, hence C,U,V are nonzero. The joint and marginal conditional probabilities are C*u(a)*v(b)/S, C*u(a)*V/S and C*U*v(b)/S, which satisfy the claimed identity. Individual nonnegativity of C,u,v is unnecessary.

Lean traps: SpinLetter has 13 labels, including none; arbitrary predicates require classical decidability; normalize and conditionalProbability use total real division, so establish the nonzero denominators before cancellation. n=0,1 cannot supply distinct x,y, as intended.

Proof route, line 1: Reindex the fibre by the two free letters and factor its mass and the joint/marginal event sums.  
Proof route, line 2: Use positive event mass to justify cancellation of the global normalizer and C*(sum u)*(sum v), then close the scalar identity.

**TripleNormalizerStatement — TRUE, medium.**

The actual U functional is the uniform average over the twelve icoVector labels; its none atom has weight zero. Expanding the three affine factors uses only the constant, first, second and third moments: 1, 0, delta/3 and 0. It gives exactly 1+tripleP(a)/3 for arbitrary real fields, without a unit-ball premise. These moments follow from the explicit sign-symmetric coordinates and goldenRatio^2=goldenRatio+1, icoRadius^2=goldenRatio+2; they are not extra assumptions. Exact checks covered all 35 monomials through degree four and the full normalizer polynomial in nine formal field coordinates.

Lean traps: siteFunctional sums over SpinLetter, not icoSet; fractions are real; the separate moment Statement definitions are propositions, not available proofs.

Proof route, line 1: Use the proved siteLawDecomposition to replace siteFunctional U by the explicit twelve-label average, and establish its moments through degree three from the coordinates.  
Proof route, line 2: Expand localProduct on Fin 3 and the coordinate dot products; odd terms vanish and the second tensor contracts to tripleP/3.

**TripleNumeratorStatement — TRUE, hard.**

Multiplying the three-factor product by v_i has degree at most four in the spin. The first and third tensors vanish, the second tensor gives 5*(a0+a1+a2) after multiplication by 15, and the fourth tensor gives a0*(a1 dot a2)+a1*(a0 dot a2)+a2*(a0 dot a1), exactly tripleV. The explicit twelve-vector law has the required fourth tensor, so no field norm or extra law premise is needed. Exact coefficient checks passed for all three numerator coordinates with nine formal field variables.

Lean traps: i is Fin 3; the fourth tensor has three Kronecker pairings and coefficient 1/15; tensors declared as other Statement props cannot simply be assumed. Reestablish their concrete finite-sum identities if no proved helper is supplied.

Proof route, line 1: Identify the U functional with moment and derive its second/fourth tensors and vanishing odd tensors from the explicit twelve-label sum.  
Proof route, line 2: Expand v_i*localProduct coordinatewise, contract the three fourth-order pairings, and collect terms after multiplication by 15.

**TripleGeometryStatement — TRUE, easy.**

With all three squared lengths equal to one, normSq(a0+a1+a2)=3+2*tripleP(a)>=0 gives tripleP(a)>=-3/2 and hence the stated real lower bound 1/2. For each pair, normSq(aj-ak)=2-2*dot(aj,ak)>=0 gives the requested nonnegative deficit. Coincident, antipodal and zero-sum unit triples cause no failure; the lower bound is attained by a 120-degree triple.

Lean trap: Vec3 is the raw Pi type Fin 3 -> R, whose default norm is a sup norm; use normSq/dot or explicitly transport to EuclideanSpace rather than importing a norm inequality for the wrong norm.

Proof route, line 1: Expand the nonnegative squared norm of the sum of the three fields and use the three unit equalities to bound tripleP below.  
Proof route, line 2: Expand the three nonnegative squared norms of pairwise differences to bound each dot product above by one; finish with real linear arithmetic.

**TripleSOSIdentityStatement — TRUE, medium.**

Write x=dot(a0,a1), y=dot(a0,a2), z=dot(a1,a2). Then tripleV=(5+z)*a0+(5+y)*a1+(5+x)*a2. Expanding its squared norm and replacing each squared field length by one yields precisely the stated polynomial in x,y,z. An exact symbolic check in the six Gram entries found that the residual without the unit assumptions is (1-normSq(a0))*(5+z)^2+(1-normSq(a1))*(5+y)^2+(1-normSq(a2))*(5+x)^2, so the listed hypotheses suffice. No linear independence or extra geometric inequality is required.

Lean traps: make dot bilinearity/symmetry and Fin 3 sums explicit before ring; tripleSOS is only nonnegative after separate geometric inequalities, but this leaf asserts just the identity.

Proof route, line 1: Rewrite tripleV as the three fields with scalar coefficients 5 plus the opposite pairwise dot product, and expand its squared norm bilinearly.  
Proof route, line 2: Replace the three diagonal Gram entries by one, unfold tripleP and tripleSOS, and verify the remaining scalar polynomial identity by ring.

**BallFieldSplitStatement — TRUE, medium.**

For nonzero a, let rho=sqrt(normSq(a)), e_i=a_i/rho and t=(1+rho)/2. The sum-of-squares definition and normSq(a)<=1 give 0<rho<=1, normSq(e)=1, and a=(2*t-1)*e, establishing the equality for every v simultaneously. For a=0 take e=(1,0,0) and t=1/2. Thus the zero and unit-boundary cases are covered without additional assumptions.

Lean traps: normSq is the Euclidean sum of squares rather than the Pi type's default norm; prove rho!=0 before division and use Real.sq_sqrt with nonnegativity; UnitVector is a subtype whose normSq equality must be provided, and negation in the formula is on e.val.

Proof route, line 1: Separate a=0; otherwise normalize a by sqrt(normSq a), prove the resulting vector is in UnitVector, and choose t=(1+sqrt(normSq a))/2.  
Proof route, line 2: Use a=(2*t-1)*e and dot linearity to verify the affine identity for all v, with t in [0,1].

**ProductMixtureStatement — TRUE, medium.**

Choose the field-level witnesses independently of v, pad to three slots using any fixed unit vector with mixing parameter 1/2, and distribute the resulting three two-term sums. The 2^3=8 sign choices give unit signed fields and weights equal to products of t_j or 1-t_j; all weights are nonnegative and their sum is one. Padding represents absent factors by the constant one, so k=0,1,2 are valid as well as k=3, and endpoint parameters allow zero mixture weights. No separate ball-norm premise is needed because the decompositions are supplied. Exact polynomial checks covered all k and 85 parameter combinations.

Lean traps: retain the forall-v part when choosing witnesses; explicitly reindex Fin 3 -> Bool by Fin 8; negated unit vectors need subtype proofs; use classical choice/decidability and the Fin k embedding justified by k<=3.

Proof route, line 1: Choose each supplied decomposition, and pad the k factors to three by 1=(1/2)*(1+dot(v,e))+(1/2)*(1-dot(v,e)) for a fixed unit e.  
Proof route, line 2: Distribute over the eight sign choices, form product weights and signed unit triples, and use finite distributivity to check positivity, total weight one and the pointwise equality.

**PositiveMixtureEstimateStatement — TRUE, medium.**

Let D=sum(t_eta*A_eta). Nonnegative t, sum t=1 and A_eta>=1/2 give D>=1/2>0 and each A_eta>0. The weights p_eta=t_eta*A_eta/D are a finite probability, and the displayed mixture vector is sum p_eta*(B_eta/A_eta). Convexity of the Euclidean sum of coordinate squares bounds its normSq by sum p_eta*r^2=r^2. Zero t values and r=0 work without further premises; an empty alpha is excluded by sum t=1, rather than making the whole statement vacuous. The premise r>=0 is harmless and actually unnecessary for this squared-norm conclusion.

Lean traps: the Fintype alpha instance is retained in the elaborated statement; no DecidableEq or Nonempty instance is missing; invoke classical locally if needed and use normSq rather than the Pi type's sup norm. All divisions have strictly positive denominators.

Proof route, line 1: Prove D>=1/2, then set p_eta=t_eta*A_eta/D and Y_eta=B_eta/A_eta; establish p_eta>=0, sum p=1 and the displayed vector equals sum p_eta*Y_eta.  
Proof route, line 2: Apply the finite squared-norm convexity inequality (or expand the nonnegative weighted variance) to obtain normSq(sum p_eta*Y_eta)<=sum p_eta*normSq(Y_eta)<=r^2.

Fix: None required. Optional weakening: remove 0<=r, since only r^2 occurs.

The hypotheses are jointly satisfiable in the substantive cases. For conditioning, use two sites and constant positive weights. All three fields may be the same unit vector for the unit-triple leaves. The zero field satisfies the splitting premise, and zero fields can be padded in the product leaf. For the estimate, a singleton alphabet with `t=A=1`, `B=0`, and `r=0` satisfies every premise. The impossible distinct-site cases at n=0,1 and the impossible empty-alphabet normalization are expected boundary cases, not reasons to label either whole statement VACUOUS.

Validation artifacts are [checks.py](/home/ubuntu/aklt/reports/TS_MOM_03/scratch/checks.py), [checks.json](/home/ubuntu/aklt/reports/TS_MOM_03/scratch/checks.json), and [Inspect.log](/home/ubuntu/aklt/reports/TS_MOM_03/scratch/Inspect.log). Exact rational arithmetic in ℚ(√5) checked all 35 coordinate monomials through degree four for the explicit twelve-atom law. Formal polynomial arithmetic checked the normalizer, all three numerator coordinates with nine unrestricted field variables, and the SOS identity in six Gram entries. Additional exact checks covered 507 conditional joint/marginal comparisons on the thirteen-letter alphabet, 85 padded-product cases with k=0,1,2,3, and 96 positive-mixture cases including radius zero and denominator lower-bound equality. The finite samples supplement the general reasoning above; they are not universal proofs.

One Lean 4.35.0-rc2 inspection process imported the existing compiled node module and successfully printed every assigned declaration and the core definitions. It confirmed the `Fin 3` index, retained `[Fintype α]` binder, and quantifier order. No Lean proofs were written, no repository modules were rebuilt or modified, and no sub-agents were launched. The scratch package directory links to the existing repository `.lake/packages`.
