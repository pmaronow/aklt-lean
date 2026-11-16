STATUS: COMPLETE

Adjudicated all five numbered findings in §1 of REF-R4, and only finding 1
of REF-R7 as requested. **All six are CONFIRMED.** The corrections below
form one compatible set. In particular, E14 is the single replacement
closure lemma for both reports, not two competing fixes.

All target paths and line numbers refer to the frozen directory
`/home/ubuntu/aklt/manuscript/bundle/manuscript/`. Only this adjudication
directory was written. No subagents were used. The independent checker
`check_adj_r4.py` uses Python integers and `fractions.Fraction`, with no
imports from the referee or manuscript programs. Its complete output is
`check_adj_r4.out`. I also reran the supplied referee checker, recording
`check_r4.out`. The supplied pattern data were compared class by class;
the large H1, H2 and H3′ certificate computations were not rerun.

The main theorem and every numerical constant can be retained. In
particular, neither the response envelopes nor the kernel must be
enlarged. The corrected analytic argument has the same inputs (H1),
(H2), (H3′), the same local class of 7,962 covered patterns, and the same
constant
\[
C_T=2(12/5)^{24}\bigl(C_V/(1-q)\bigr)^2.
\]
This conclusion concerns these findings; it is not an adjudication of
the other findings of REF-R7 or an independent certification of Section 8.

## FINDING R4-1: CONFIRMED

The initial-D restriction is absent in `sec6-walks.tex:40,53–55,85`.
A D site can initially have two present bonds. Direct integration,
using \(\int n_i n_j\,\lambda_D(dn)=\delta_{ij}/5\), gives, for its
two neighbours \(f,o\),
\[
Z_D^\cdot=Z_{E'}^\cdot[1+P_{fo}/5],\qquad
Z_{D;[(y,o)]}^\cdot=(3/5)Z_{E'}^\cdot,
\quad
\rho_1^\cdot=\frac{3/5}{1+\E_{E'}^\cdot[P_{fo}]/5}.
\]
Here the first bracket denotes an inserted observable, and \(E'\) is
the network with \(y\) removed. Thus the ratio is generally pin-dependent.
Every later D departure has already lost an arrival bond, so its
remaining present degree is at most one and its ratio is exactly 3/5.

For an independent exact check, take
\(G=\{(a,b):|a|+|b|\le3\}\), with
\(S=\{2\le|a|+|b|\le3\}\). Set \(y=(0,0)\) to D, keeping only
its bonds to \(f=(-1,0),o=(1,0)\); remove \((0,\pm1)\).
The U sites \(f,o\) keep just their bonds to \(y\) and to
\((-2,0),(2,0)\), respectively. All S sites are U and keep every
bond. Pin every original leg to \((0,0,1)\). This satisfies Definition
6.1. It need not satisfy the additional consistency requirements, which
the exposure lemma does not assume. The one-step stopped trail
\(w=(y,o)\) has an interior terminal site and no first-U-departure
steps, so the asserted exposure right-hand side is zero.

The exact computation in my checker integrates the twelve radius-three
sites first. The remaining radius-two sites form an eight-vertex ring
with connector kernel
\[
B_\tau=\begin{pmatrix}
4/3&0&0&2/3\\0&2/5&0&0\\0&0&2/5&0\\2/3&0&0&8/15
\end{pmatrix},\qquad
B_0=\operatorname{diag}(1,1/3,1/3,1/3)
\]
in the basis \((1,n_1,n_2,n_3)\). Each axial outer tip gives a
normalized factor \(1+3n_3/5\) when pinned, and 1 when free. The
local ring tensor is \(\int\phi_a\phi_b(1+h n_3)\,dn\).
The numerator inserts \(n_k\) at two opposite axial sites and sums
over \(k\); the two interior leaves give a further factor 1/9.
This derives the transfer calculation directly from second and fourth
sphere moments. Independently, the free result follows from the two
eight-edge paths in the original sixteen-edge ring:
\(\E_{E'}^0P_{fo}=\frac19(2\,3^{-8})/(1+3\,3^{-16})\).

Commands, run from the adjudication directory:

```bash
python3 -B check_adj_r4.py > check_adj_r4.out
python3 -B /home/ubuntu/aklt/referee/REF-R4/check_r4.py > check_r4.out
```

Independent output:

```text
diamond free P_fo = 243/7174454
diamond free R = 21523362/35872513
diamond pinned P_fo = 162376940888609/7284251314603125
diamond pinned R = 21852753943809375/36583633513904234
nonzero R_free - R_pinned = 3489587459989787505333/1312346868814765314920042
initial D two-bond bound: rho/3 <= 1/4 < 1/3 <= omega_1
```

These independently reproduce the referee's interior counterexample.
The needed restriction holds for T1: `sec7-recursion.tex:7` requires a
D start in \(P_X(D)\) to have at most one present bond. For the second
expansion its start \(v\) has that property as well. At an initial
two-bond D site in the more general one-point estimate, the correct
uniform bound is \(\rho_1^\cdot\le3/4\), so its weighted factor is
at most 1/4, below the first lattice weight \(\omega_1\ge1/3\).
It therefore needs no exception factor or new constant.

Corrections (E05 also makes the network convention from R4-3 explicit):

**E05 — `sec6-walks.tex: replace lines 53–53`.**

```latex
For $w\in\mathcal T_D(u,T)$ as in Proposition~\ref{p:pairwalk}, we have
$R^\cdot_D(w)=\prod_{j=1}^{|w|}\rho^\cdot_j$ with
$\rho^\cdot_j=Z^\cdot_{D;[w_j]}/Z^\cdot_{D;[w_{j-1}]}$.
Let $y=v_{j-1}$ be the site left at step $j$, $o=v_j$ the
out-neighbour, and $E'$ the auxiliary spin network obtained from
$D;[w_{j-1}]$ by removing $y$, retaining its scalar mass. Step $j$ is
a \emph{revisit} if $y$ has status $\mathrm D$ in $D;[w_{j-1}]$ and
a \emph{first visit} otherwise. Integrating out $y$, we find:
```

**E06 — `sec6-walks.tex: replace lines 55–55`.**

```latex
\item for a revisit with at most one present bond at departure,
$\rho^\tau_j=\rho^0_j=3/5$, since
$\int(1+n\cdot n_o)\lambda_{\mathrm D}(\dd n)=1$.
The only possible two-bond $\mathrm D$ departure is the initial step.
If its present neighbours are $f,o$, then
\[
\rho^\cdot_1=
\frac{3/5}{1+\frac15\E^\cdot_{E'}[P_{fo}]}\le\frac34.
\]
Indeed, every later departure has already lost its arrival bond;
a $\mathrm D$ site has at most two present bonds before that arrival;
```

**E07 — `sec6-walks.tex: replace lines 85–85`.**

```latex
Let $w\in\mathcal T_D(u,T)$ under the hypotheses of
Proposition~\ref{p:pairwalk}. If $u$ initially has status $\mathrm D$,
assume in addition that it has at most one present bond in $D$.
Let $\Phi$ be the set of first-visit steps of $w$, and suppose that
$\rho^\tau_j\le x_j$ for $j\in\Phi$, with numbers $x_j\ge1$.
Then for every ordering $\sigma$ of $\Phi$,
```

**E13 — `sec6-walks.tex: replace lines 149–149`.**

```latex
Every trail of $D$ is a trail of $\Z^2$. We prove the same pointwise
bound for both dots $\tau$ and $0$. If the initial site has status
$\mathrm D$ and two present bonds, the formula above gives
$\rho^\cdot_1\le3/4$, hence
$3^{-1}\rho^\cdot_1\le1/4\le\omega_1$, since the first lattice
departure has $\omega_1\ge1/3$. Every other departure from status
$\mathrm D$ has at most one present bond, so
$3^{-1}\rho^\cdot_j=1/5$. This equals $\omega_j$ if the site was
left before by $w$, and is at most $\omega_j$ otherwise. For a
first-visit step whose pattern is in $\Pext$,
Lemma~\ref{l:local} and (H1) give
$\rho^\tau_j\le x_{\mathrm{type}}$, while
Lemma~\ref{l:response} gives $\rho^0_j\le1\le x_{\mathrm{type}}$;
thus $3^{-1}\rho^\cdot_j\le\omega_j$. At any other first-visit
step, Lemma~\ref{l:response} gives
$3^{-1}\rho^\cdot_j\le4/5\le(12/5)\omega_j$.
There are at most $12$ such steps, so pointwise
\[
3^{-|w|}\max\{R^\tau_D(w),R^0_D(w)\}
\le (12/5)^{12}\mathsf W(w).
\]
Since $|w|\ge d(x,S)$, summing (H2) over the possible lengths gives
the claim.
```

**E15 — `sec7-recursion.tex: replace lines 68–68`.** State the common normalization convention and check the added exposure hypothesis before the expansions.

```latex
Let $G$, $\tau$, $D$ and $(u, v) \in P_X(D)$ with centre $c$ be as in \eqref{e:FX} with $d_0 = \min(d(u, S), d(v, S)) \ge d \ge 1$; in particular $u, v \notin S$, and $u$ has at most three present bonds because $c$ is removed. At the start of each expansion, normalize a starting site of status $\mathrm U$ by dropping its kept bond to the removed centre, as in Lemma~\ref{l:closure}; all histories below use this convention. This changes no partition function, ratio or correlation. If the starting site has status $\mathrm D$, it has at most one present bond by the definition of $P_X(D)$, as required by Lemma~\ref{l:exposure} in $T_1$. By Proposition~\ref{p:pairwalk} with $T = S \cup \{v\}$, applied to $\tau$ and to $0$, the trails are the same in both expansions, and
```

The exposure display `e:exposure` and its telescoping proof
remain unchanged after E07. The one-point statement and its common
majorant are supplied by E11–E12 under R4-3. No modification is needed
to the definition of \(P_X\), `e:FX`, `e:kernel`, `h:H3`, or the
conclusions of Theorem 7.4.

## FINDING R4-2: CONFIRMED

I checked the kept sets, rather than inferring them from present degrees.
Take \(G=[-4,4]^2\cap\mathbb Z^2\), remove \(c=(0,0)\), and
make every other site U with all bonds kept. Then
\(S=\{(a,b):\max(|a|,|b|)\ge3\}\), and
\(u=(-1,0),v=(1,0)\) form an allowed B pair. The trail
\[
(u,(-1,1),(-2,1),(-2,0),u,(-1,-1),(0,-1),(1,-1),v)
\]
uses eight distinct bonds and avoids \(S\cup\{v\}\) until its
last site. After normalizing \(u\)'s bond to \(c\), its first
departure leaves the west and south bonds kept. At step four, arrival
from the west drops the west bond; the live site is D with only its
south bond kept. Hence item (2)'s universal two-kept-bond assertion is
false even in the T1 application.

At the empty prefix the printed normalization has not yet happened;
the initial U site still keeps its bond to \(c\), contrary to its
purported arrival-bond description. Both defects are corrected by
normalizing only an initial U site before forming \(D_0\) and by
distinguishing the live endpoint from non-live D sites. A bond to a
removed site has no effect on either partition function.

The independent finite-set computation uses the graph above, checks
condition (C), all non-live kept sets and consistent closure after every
interior-endpoint prefix of the displayed trail, and reports:

```text
j=0 printed arrival-bond assertion: False
j=4 live u: status=D, kept=[(-1, -1)]
eight-step trace mass = 3/5
```

Command: `python3 -B check_adj_r4.py > check_adj_r4.out`.
The boundary counterexample is also valid; its independent output and
range analysis are given under R7-1 below.

Here is the single full closure replacement. It treats the empty prefix,
live D sites, underlying mass-one domains and terminal boundary sites
simultaneously. It also states the variant needed for trails stopping
only at S: avoidance of the distinguished target was never used by the
kept-set induction.

**E14 — `sec7-recursion.tex: replace lines 17–31`.**

```latex
\begin{lemma}\label{l:closure}
Let $D\in\Dcons(G)$, $(u,v)\in P_X(D)$ with centre $c$, and
$u\notin S$. Let $w=(v_0,\dots,v_m)$ be a trail from $u$ that does
not visit $S$ before its last site. Thus the lemma also applies when
the trail is required to avoid $v$ before its last site. Before forming
$D_0$, if $u$ has status $\mathrm U$, drop its kept bond to $c$;
this changes no partition function because $c$ is removed. Let $D_j$
be the auxiliary spin network after tracing the prefix $w_j$ from
these normalized initial data. Then, for $0\le j\le m$:
\begin{enumerate}
\item Every visited site other than the live endpoint $v_j$ has
status $\mathrm D$ or $\mathrm X$.
\item Condition (C) holds between non-removed sites. Every
$\mathrm D$ site other than $v_j$ keeps exactly two bonds, and every
$\mathrm U$ site other than $v_j$ keeps all its bonds. If $j\ge1$,
the live endpoint has status $\mathrm U$ or $\mathrm D$: in the
first case it keeps all its bonds inside $G$ except its arrival bond;
in the second it keeps exactly one bond. The other end of the arrival
bond has status $\mathrm D$ or $\mathrm X$. At $j=0$, a live
$\mathrm U$ site keeps its three non-$c$ bonds, while a live
$\mathrm D$ site retains its original two kept bonds and has at most
one present bond.
\item Whenever $v_j\notin S$, the underlying mass-one data
$E'_{j+1}$ obtained by removing $v_j$ belong to $\Dcons(G)$.
\end{enumerate}
If $v_m=e\in S$, then $e$ has status $\mathrm U$ and has lost only
its arrival bond. This is the sole kept-set defect in the underlying
terminal trace relative to $\Dcons(G)$; all its original leg factors
are retained. No removal of $e$, and no membership in $\Dcons(G)$
after such a removal, is asserted.

Consequently, for $0\le j<m$, if step $j+1$ is a first visit at
$y=v_j$, its pattern, with arrival site $v_{j-1}$ or $c$ when
$j=0$, belongs to $\Pext$. The pairs among its non-removed remaining
neighbours belong to $P_B(E'_{j+1})\cup P_C(E'_{j+1})$, with
centre $y$.
\end{lemma}

\begin{proof}
At $j=0$, condition (C) is unchanged by dropping a bond to the
removed centre. Removing the live endpoint restores the original
kept-set conditions at every remaining site. For a later departure
from a live $\mathrm U$ site, its arrival bond (or its bond to $c$
at the initial departure) and its out-bond are distinct; dropping the
out-bond and changing its status to $\mathrm D$ leaves exactly two
kept bonds. If the initial site is $\mathrm D$, it can depart only
by its sole present bond and becomes $\mathrm X$. Every later live
$\mathrm D$ site has lost its arrival bond from a two-bond kept set;
at a departure it becomes $\mathrm X$. On arrival, an unvisited
$\mathrm U$ site loses just its arrival bond, and a $\mathrm D$
site loses one of its two kept bonds. All traversed bonds are dropped
by both ends. These observations prove (1) and (2) inductively.

Before a hit of $S$, the live endpoint is the only possible exception
to the full $\mathrm U$ and two-bond $\mathrm D$ kept sets. Removing
it leaves condition (C) intact and does not remove a protected site;
this proves (3). At a first hit $e\in S$, that site was unvisited
and has status $\mathrm U$, so only its arrival bond is lost.

At a first-visit departure $y$, the arrival site is removed or has
status $\mathrm D$ with two kept bonds other than its bond to $y$.
Every other $\mathrm U$ site keeps all its bonds. By (C), each
other non-removed neighbour of $y$ that has status $\mathrm D$
keeps its bond to $y$ and one other bond; every non-live
$\mathrm D$ corner keeps two bonds. These are the rules of
Definition~\ref{d:pattern}, with the tips replaced by their covering
tips and external slots filled as in Lemma~\ref{l:local}. Finally,
any two non-removed remaining neighbours of $y$ are at distance two
with common neighbour $y$, which is removed in $E'_{j+1}$.
A $\mathrm D$ neighbour has at most one present bond after this
removal, so the response pairs have the stated pair classes.
The argument uses no avoidance of the distinguished target $v$.
\end{proof}
```

The induction in this replacement is enough for every first
expansion, including every nonterminal response domain in T1. The
unchanged pair-class definition then applies after removing the
responding site. At a terminal boundary hit, only a spin network is
claimed. Its use in T2 is made explicit by E01–E03, E10–E12 and E16
below. Thus there is no change to either response envelope or any
kernel entry. This same replacement also resolves R7-1.

## FINDING R4-3: CONFIRMED

Definition 6.1 (`sec6-walks.tex:10`) requires all S sites to keep
every bond. Tracing (`:37`) drops the last traversed bond at its S
endpoint. The resulting object is not in the proposition's declared
input class, yet `sec7-recursion.tex:80` applies the proposition to it.
The alternative \(D=D_0;[w_0]\) in the one-point lemma does not
extend the proposition's hypothesis. There is a literal type mismatch.

The existing trace rule does mention the factor 3/5; it is not absent
from the printed mathematics. What must be made explicit is that this
scalar is part of the traced object, rather than part of its status/kept
assignment. The eight-step closure check above has mass 3/5 because
the second departure from u changes D to X. Erasing that mass would
change R, though it would leave every normalized expectation unchanged.

The consistent repair is to retain the original protected-boundary
domain class for \(\mathsf F_X\), and define auxiliary networks for
traces. Their S sites stay U and retain all original pin factors, while
their kept sets may lose bonds. Network partition functions include
their positive scalar mass. A mass cancels in expectations and in the
same-step ratios, except for the explicitly added mass at a D departure.
All denominators are positive: choose all remaining spins near one unit
vector not antipodal to any of the finitely many pins. Every bond and
pin factor is then positive on an open product set, and each site
measure has a positive uniform component.

The step identity, the pair-walk induction, free positivity and the
first-U response bounds use present bonds, the site measures and absence
of legs at departure sites. They do not use the full kept sets on S.
Consequently they extend to the stated networks. The definition retains
the D present-degree bound of two; arbitrary histories that would leave
a three-present-bond D site are not silently admitted. Every history
used by the proof starts with at most three present bonds and leaves
sites outside S, so this bound is preserved.

The twelve-exception assertion needs an argument independent of ordinary
domain membership. After a first stopped trail ending at e, the only
non-live kept-set defect is the missing arrival bond at e. Normalize
the U start v by dropping its bond to the removed centre. Induct on the
second trace while carrying e as a fixed marked defect. Away from e,
non-live U sites still keep all bonds, non-live D sites keep two, and
condition (C) persists. At a U departure y′ with \(d(y',e)>2\), the
whole radius-two template avoids the defect, so the ordinary covered
pattern applies. Missing external slot factors are covered by the
explicit convex averaging in `sec6-walks.tex:126`. The remaining possible
U departures lie in the twelve-site set
\(\{y':0<d(y',e)\le2\}\). The endpoint e cannot be departed
from, and each site can be left as U at most once. The bound is spatial;
these need not be the final twelve steps. There is no need to add
boundary-defective domains to \(\mathsf F_X\).

Command: `python3 -B check_adj_r4.py > check_adj_r4.out`. Relevant output:

```text
eight-step trace mass = 3/5
terminal e in S = True
terminal e keeps all bonds = False
removing terminal e is consistent = False
radius-two sites other than e = 12
```

The one-point proof E13 gives a single pointwise bound for both boundary
conditions. I state the resulting bound on the sum of their maxima,
because that is exactly the quantity used at `sec7-recursion.tex:82`.
This is stronger than the original displayed conclusion and follows
from the same domination, without doubling its constant.

Corrections:

**E01 — `sec6-walks.tex: insert after line 17`.**

```latex
For tracing we also use an \emph{auxiliary spin network} on $G$. It has
the same statuses, site measures and kept-bond data as a domain, with at
most two present bonds at each $\mathrm D$ site, but the sites of $S$
may keep arbitrary subsets of their bonds; they still have status
$\mathrm U$. It also carries a scalar mass $\mu>0$. Its partition
function is $\mu$ times the right-hand side of \eqref{e:ZD}, with all
the original leg factors retained, and its free partition function omits
those leg factors. A domain is identified with the corresponding network
of mass $1$. The definitions of $\E^\cdot$, $\Psi$ and trails extend to
these networks. Whenever membership in $\Dcons(G)$ is asserted, it refers
to the underlying data with mass reset to $1$; this does not change
normalized expectations. In particular, $\Dcons(G)$ retains its original
protected-boundary requirements. The positivity, conditional independence
and conditional-mean facts below also hold for auxiliary spin networks.
```

**E02 — `sec6-walks.tex: replace lines 37–37`.**

```latex
A \emph{trail} in a domain or auxiliary spin network $D$ from $u$ is a
sequence $w=(v_0,\dots,v_m)$ with $v_0=u$ such that
$\{v_{i-1},v_i\}$ are distinct present bonds of $D$; $|w|=m$ is its
length. For $T\subset G$ let $\mathcal T_D(u,T)$ be the set of trails
with $v_m\in T$ and $v_i\notin T$ for $i<m$. All tracing below starts
at a site with at most three present bonds and has no departures from
$S$. The \emph{traced spin network} $D;[w]$ is obtained step by step:
at step $j$, the bond $\{v_{j-1},v_j\}$ is dropped by both ends, and
the status of $v_{j-1}$ changes from $\mathrm U$ to $\mathrm D$
(keeping its remaining bonds), or from $\mathrm D$ to $\mathrm X$.
The mass is unchanged in the first case and is multiplied by $3/5$ in
the second case, the mass of $(3/5)\delta_0$. All original leg factors
are unchanged. Thus the final mass is
$\mu(D)(3/5)^{N_{\mathrm D}(w)}$, where $N_{\mathrm D}(w)$ counts
the departures from status $\mathrm D$ during this trace. We write
$w_j=(v_0,\dots,v_j)$. A stopped trace can have a terminal site in
$S$ with its arrival bond dropped; it is an auxiliary spin network,
and need not be a domain of Definition~\ref{d:domain}.
```

**E03 — `sec6-walks.tex: replace lines 40–40`.**

```latex
Let $D$ be a domain or auxiliary spin network on $G$, let
$u\in G\setminus S$ be a site that is not removed and has at most
three present bonds, let $v\ne u$ be a site that is not removed, and
$T=S\cup\{v\}$. Then, with the dot standing for $\tau$ or $0$,
```

**E10 — `sec6-walks.tex: replace lines 130–130`.**

```latex
Lemma~\ref{l:local} applies to every first-visit step whose pattern is
in $\Pext$. Lemma~\ref{l:closure} in \S\ref{s:recursion} supplies
these patterns throughout the first expansion. If that expansion
stops at $e\in S$, its terminal trace is an auxiliary spin network
with the single kept-set defect at $e$. In the second expansion of
$T_2$, at most $12$ first-visit departures, at sites $y'$ with
$0<d(y',e)\le2$, may fail to have a covered pattern. At those
departures we use $\rho^\tau_j\le12/5$ from
Lemma~\ref{l:response}. These exceptional departures need not be
the last departures of the second trail.
```

**E11 — `sec6-walks.tex: replace lines 142–142`.**

```latex
Assume (H1) and (H2). Let $D$ be a domain or auxiliary spin network
on $G$, let $x\in G\setminus S$ be a site that is not removed and
has at most three present bonds, with a designated arrival direction,
and suppose that all first-visit steps of every trail in
$\mathcal T_D(x,S)$, except at most $12$ steps of each trail, have
their patterns in $\Pext$. Then
```

**E12 — `sec6-walks.tex: replace lines 143–145`.** The pointwise proof gives this common majorant; it directly justifies the sum of maxima in sec7:82.

```latex
\begin{equation*}
\sum_{w\in\mathcal T_D(x,S)}3^{-|w|}
\max\{R^\tau_D(w),R^0_D(w)\}
\le \Bigl(\frac{12}{5}\Bigr)^{12}
\frac{C_V}{1-q}\,q^{d(x,S)}.
\end{equation*}
```

**E16 — `sec7-recursion.tex: replace lines 80–80`.**

```latex
\emph{The term $T_2$.} Let $w\in\mathcal W_1$ end at $e\in S$.
The terminal object $D;[w]$ is an auxiliary spin network, so
Proposition~\ref{p:pairwalk} applies in it from $v$ with target $e$
and stopping set $S$; $v$ was not visited by $w$ and still has at
most three present bonds. Since terminal scalar products have absolute
value at most one,
\[
|\mathcal X^\cdot(w)|\le
\sum_{w'\in\mathcal T_{D;[w]}(v,S)}
3^{-|w'|}R^\cdot_{D;[w]}(w').
\]
By Lemma~\ref{l:closure}, the underlying terminal trace satisfies the
consistent-domain rules except that $e$ has dropped its arrival bond.
Before the second expansion, if $v$ has status $\mathrm U$, drop
its kept bond to the removed centre $c$; this changes no partition
function or ratio. Repeat the kept-set induction of
Lemma~\ref{l:closure}, allowing this fixed defect at $e$ as well as
the current live endpoint. Before the second trail hits $S$, every
first-visit departure at $y'$ with $d(y',e)>2$ has the ordinary
$\Pext$ pattern: the defect is outside its template. Missing
external factors are covered by the averaging in
Lemma~\ref{l:local}. The possible exceptional first-visit departures
therefore lie in $\{y':0<d(y',e)\le2\}$, a set of $12$ sites;
a site can be departed from with status $\mathrm U$ at most once.
All departures remain outside $S$ and all original leg factors remain
unchanged. This proves the hypotheses of Lemma~\ref{l:onepoint} for
the second expansion. That lemma also applies to the first sum over
all $\mathcal T_D(u,S)$, using the normalization at $u$ and the
variant of Lemma~\ref{l:closure} that does not exclude $v$. Its
pointwise bound applies to the maximum of the pinned and free ratios.
Consequently,
```

E05 and E13 are also required and appear under R4-1; E14 is
the shared closure correction. The displayed estimate at
`sec7-recursion.tex:81–83` is unchanged. Its first factor is covered
by the closure variant that permits a visit to v, and its second by
the just-proved one-defect induction. With
\(K=(12/5)^{12}C_V/(1-q)\), each boundary condition gives at most
\(K^2q^{d(u,S)+d(v,S)}\); summing the two terms gives exactly the
printed \(C_T=2K^2\). H1, H2, H3′, all Section 8 inputs, and the
main theorem need no quantitative change.

## FINDING R4-4: CONFIRMED

The statement at `sec6-walks.tex:44` includes “with one present bond
in D”; the endpoint explanation at `:48` omits it. Use the same diamond
domain as R4-1, but start at f and take target y, so the target is D
with two initial bonds. In the one-step term f → y, the target still
has its bond to o. Given \(n_o=a\), its law has density
\((1+n\cdot a)\lambda_D(dn)\), normalized by 1, and
\[
\int n(1+n\cdot a)\lambda_D(dn)=a/5,
\qquad
\int |n|^2(1+n\cdot a)\lambda_D(dn)=3/5.
\]
Thus it need not be independent of the remaining spins. The numerical
value of its squared norm happens still to be 3/5; that does not justify
the independence assertion. These identities follow exactly from the
second moments and odd-moment vanishing, and are recorded in the checker:

```bash
python3 -B check_adj_r4.py > check_adj_r4.out
```

```text
terminal D, remaining unit bond a: E[n|a]=a/5, E[|n|^2|a]=3/5
```

The minimal repair repeats the qualification in the proof. There is
no need to strengthen the proposition or to assert independence for
the two-bond case:

**E04 — `sec6-walks.tex: replace lines 48–48`.** Only the final endpoint explanation changes; the rest of the proof line is retained verbatim.

```latex
Write $n_u \cdot n_v = \sum_{\beta = 1}^3 n_u^\beta n_v^\beta$ and fix $\beta$. In $Z^\cdot_D[n_u^\beta n_v^\beta]$, integrate the spin of $u$ using Lemma~\ref{l:stepid} with $a = e_\beta$; the site $u$ carries no leg because $u \notin S$, and the factor $n_v^\beta$ does not involve $n_u$. This gives a sum over the present bonds $\{u, v_1\}$ of $\frac13 Z^\cdot_{D;[(u, v_1)]}[n_{v_1}^\beta n_v^\beta]$. If $v_1 \notin T$ we repeat the step at $v_1$: it carries no leg, a site of status $\mathrm U$ has at most three remaining factors after the arrival bond is dropped, and a site of status $\mathrm D$ at most one. The procedure stops at the first visit of $T$, and a step from a site without remaining bonds contributes $0$. Every trail is finite, so after finitely many steps we obtain $Z^\cdot_D[n_u^\beta n_v^\beta] = \sum_w 3^{-|w|} Z^\cdot_{D;[w]}[n_{v_{|w|}}^\beta n_v^\beta]$. Summing over $\beta$ and dividing by $Z^\cdot_D$ gives \eqref{e:pairwalk}. If $v_{|w|}=v$, the last bracket is $|n_v|^2$. If $v$ has
status $\mathrm D$ with one present bond in $D$, that bond was the
arrival bond, so after arrival $n_v$ is independent of the rest with
law $\lambda_{\mathrm D}$, and $\E|n_v|^2=3/5$.
```

No other statement changes in consequence of this finding.
The endpoint hypotheses of the actual recursion already satisfy the
qualified statement.

## FINDING R4-5: CONFIRMED

Definition 6.1 permits arbitrary U kept sets in general domains;
only its consistent subclass forces them to be full. Definition 6.6
does not expressly impose fullness at U sites or specify the passage
site's three non-arrival bonds. Condition (C) alone does not do so.
For example, take s removed and all other template sites U, let y
drop both its s bond and its e bond, and let e also drop its y bond.
Keep all other bonds and take out-neighbour N. This satisfies the
literal status and consistency rules at `sec6-walks.tex:104,108`.
Integrating y then gives only
\(1+P_{\mathsf N\mathsf W}/3\), whereas `app-local.tex:26`
uses all three non-arrival bonds and the corresponding three pair
terms. The intended fullness condition is needed.

I read `programs/h1-patterns/code/pext.py:49–53,109–122,125–154`.
Its effective construction gives y all three non-arrival bonds, and
its consistent site options give U sites their full kept sets.
The label “P_ext” in that program's initial docstring also describes
a historical broader class; the relevant routine for the manuscript
is `enumerate_pext_consistent`, not `enumerate_pext`.

My independent enumeration uses precisely the clarified full-U rules,
projects D-corner kept sets to their two internal bonds after slot
enlargement, imposes (C), deletes isolated common factors, and quotients
by the stated reflection. It then compares all effective keys with
`programs/data/pext/pext7962.json`, not just their number. Command and
output:

```bash
python3 -B check_adj_r4.py > check_adj_r4.out
```

```text
clarified pattern enumeration: raw=49261, classes=7962, straight=2696, turns=5266
classes equal supplied pext7962.json = True
independent-only classes = 0 ; data-only classes = 0
```

The intermediate raw count is specific to this implementation: it
identifies different external D-corner kept choices before enumeration
and keeps turns with one designated orientation. It is not the paper's
pre-quotient count of 106,101. Equality of the final effective key sets
is the relevant check. This confirms that the clarification preserves
the published counts and the computer input class, without relying
on notes from the full source tree.

Corrections:

**E08 — `sec6-walks.tex: replace lines 104–104`.**

```latex
A \emph{pattern} $\pi$ consists of an out-neighbour
$o\in\{\mathsf e,\mathsf N,\mathsf W\}$ and statuses and kept bonds
of the sites $\mathsf s,\mathsf e,\mathsf N,\mathsf W$ and of the
corners, with the site measures of Definition~\ref{d:domain}. The
passage site $y$ has status $\mathrm U$ and keeps precisely its three
bonds to $\mathsf e,\mathsf N,\mathsf W$, so $\{y,\mathsf s\}$ is
dropped. Every other site of status $\mathrm U$ keeps all four of
its lattice bonds, and $o$ is not removed. For unit vectors
$m=(m_\ell)$ on the slots, let $Z_{\mathrm{cur}}(\pi;m)$ be the
integral over the spins of $\mathsf T(y)$ minus the removed sites,
with the site measures of the statuses, of the product of the factors
of the present bonds inside $\mathsf T(y)$ and of
$1+m_\ell\cdot n_z$ for every slot $\ell$ at a non-removed site $z$;
the tips have status $\mathrm U$. Let
$Z_{\mathrm{next}}(\pi;m)$ be the same integral after the step,
that is, with the measure of $y$ replaced by $\lambda_{\mathrm D}$
and the bond $\{y,o\}$ dropped. Define
```

**E09 — `sec6-walks.tex: replace lines 108–108`.** The original class rules and tip-bond convention are retained verbatim, followed by this clarification.

```latex
The class $\Pext$ consists of the patterns in which: $\mathsf s$ is removed or has status $\mathrm D$ keeping two of its three bonds other than $\{y, \mathsf s\}$; each of $\mathsf e, \mathsf N, \mathsf W$ has status $\mathrm U$, $\mathrm X$, or $\mathrm D$ keeping the bond to $y$ and one other bond; each corner has status $\mathrm U$, $\mathrm X$, or $\mathrm D$ keeping two of its four bonds; and condition (C) holds for the bonds between non-removed sites of $\mathsf T(y)$ other than the tips. (The statuses of the tips are not part of a pattern; a bond between a tip and its neighbour $z$ is present in $Z_{\mathrm{cur}}$ and $Z_{\mathrm{next}}$ if and only if $z$ is not removed and keeps it.) A pattern is straight or a turn according to $o$.
These are local covered spin integrals, not domains with the
protected-boundary condition on $S(G)$. The tips are the covering
$\mathrm U$ tips of Lemma~\ref{l:local}; condition (C) is not imposed
between their original global kept sets and the other template sites.
Both external slot factors at each non-removed corner are included in
the covered integrals, even when an actual external bond is absent.
Such missing factors are filled by the convex-averaging enlargement
in the proof of Lemma~\ref{l:local}.
```

The displayed definition of \(c(\pi)\), H1, the counts at
`sec6-walks.tex:111`, Theorem 8.3 and Appendix D need no edits:
their existing formulas and computations already use these conventions.
This check verifies the interface and enumeration; it does not rerun
the positivity certificates themselves.

## FINDING R7-1: CONFIRMED

This is the terminal part of the same closure defect, so it receives
the same correction E14. In \(G=[-4,4]^2\cap\mathbb Z^2\) with
only \(c=(0,0)\) removed, take \(u=(-1,0),v=(1,0)\) and
\(w=(u,(-2,0),(-3,0))\). Its terminal site
\(e=(-3,0)\) has distance two from the complement of G and lies in
S; the preceding sites do not lie in \(S\cup\{v\}\). The trace
drops e's arrival bond. Removing e then makes a protected site X,
contradicting Definition 6.1 regardless of every other kept set.

Command and exact finite-set output:

```bash
python3 -B check_adj_r4.py > check_adj_r4.out
```

```text
terminal e in S = True
terminal e keeps all bonds = False
removing terminal e is consistent = False
```

The exact terminal correction is the following portion of E14,
targeting `sec7-recursion.tex:18–24` as part of the full replacement
of lines 17–31 already given under R4-2. This is a quotation of the
shared replacement, **not an additional overlapping edit**:

```latex
\item Whenever $v_j\notin S$, the underlying mass-one data
$E'_{j+1}$ obtained by removing $v_j$ belong to $\Dcons(G)$.
\end{enumerate}
If $v_m=e\in S$, then $e$ has status $\mathrm U$ and has lost only
its arrival bond. This is the sole kept-set defect in the underlying
terminal trace relative to $\Dcons(G)$; all its original leg factors
are retained. No removal of $e$, and no membership in $\Dcons(G)$
after such a removal, is asserted.
```

The ordinary removal assertion is restricted to live endpoints outside
S, and first-visit/pair-class assertions are restricted to actual
departures, \(j<m\). Its proof at E14 handles that distinction.
To apply the pair identity and one-point estimate to a terminal trace,
also apply E01–E03, E10–E13 and E16 exactly as above. These edits
expressly include the terminal-trace class and establish the twelve
exceptions rather than treating the trace as a consistent domain.
No separate repair, new boundary envelope or changed constant is needed.

## Consolidated manuscript edits in file order

Apply each E-number once, using original frozen-source line numbers.
The replacements preserve every existing label and numbered environment.
The insertion introduces no numbered statement. The machine-readable
manifest `edits.json` contains these same exact replacements.

No manuscript edits outside Sections 6–7 are required **as a consequence
of these six findings**. In particular, retain `d:domain`'s original
protected class, the pair classes and envelopes, all labels and numbers,
the displayed kernel, H1–H3′ and their constants, the pattern counts,
`e:recineq` including \(C_T\), the conclusions and constants of
Theorem 7.4 and Hypothesis (P), Section 8's certified inputs, Appendix A's
constant choices, and Theorem 1.1. Appendix D's existing full-U and
covered-slot formulas agree with E08–E09 and require no alteration.

Validation of this edit set is recorded in `validation.out`: the
independent exact checker exits successfully; the reconstructed covered
pattern classes agree class by class; all replacement ranges are
disjoint; and a review copy of the manuscript compiles with the same
labels and theorem/equation numbers. The frozen inputs were not edited.

| Edit | Frozen target | Finding(s) | Change |
|---|---|---|---|
| E01 | `sec6-walks.tex` after 17 | R4-3 / R7-1 | Define auxiliary networks, positive trace mass and unchanged boundary legs. |
| E02 | `sec6-walks.tex:37–37` | R4-3 / R7-1 | Define tracing in that class and record all D-to-X scalar masses. |
| E03 | `sec6-walks.tex:40–40` | R4-3 / R7-1 | Extend the pair-walk proposition to auxiliary networks. |
| E04 | `sec6-walks.tex:48–48` | R4-4 | Qualify the endpoint-independence explanation by one initial present bond. |
| E05 | `sec6-walks.tex:53–53` | R4-1 / R4-3 | Use network partition ratios and a mass-preserving removed-site network. |
| E06 | `sec6-walks.tex:55–55` | R4-1 | Separate the constant D ratio from the initial two-bond D formula. |
| E07 | `sec6-walks.tex:85–85` | R4-1 | Restrict exposure to an initial D site of present degree at most one. |
| E08 | `sec6-walks.tex:104–104` | R4-5 | Specify full U kept sets and the three kept passage-site bonds. |
| E09 | `sec6-walks.tex:108–108` | R4-5 | Specify covering tips and external-slot enlargement independently of global consistency. |
| E10 | `sec6-walks.tex:130–130` | R4-3 / R7-1 | Locate the at-most-twelve exceptional departures near the first terminal site e. |
| E11 | `sec6-walks.tex:142–142` | R4-3 / R7-1 | State the one-point estimate for networks with the required degree bounds. |
| E12 | `sec6-walks.tex:143–145` | R4-3 / R7-1 | State its common bound on the sum of pinned/free maxima. |
| E13 | `sec6-walks.tex:149–149` | R4-1 / R4-3 | Prove the common domination, including an initial two-bond D site. |
| E14 | `sec7-recursion.tex:17–31` | R4-2 / R7-1 | Replace the shared closure lemma and proof with correct prefix/live/terminal cases. |
| E15 | `sec7-recursion.tex:68–68` | R4-1 / R4-2 / R4-3 | Use normalized histories throughout and check the added exposure hypothesis in T1. |
| E16 | `sec7-recursion.tex:80–80` | R4-3 / R7-1 | Justify the second expansion, its one boundary defect, and both one-point applications. |
