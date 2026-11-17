# MANUSCRIPT_DELTAS — part 1 (draft)

Base: manuscript commit `32487a2`. Each entry has kind `correction`; before text is from that frozen source, and after text is from the final merged working copy. Shared corrections appear under each affected finding. Source-line scopes are used so the context and final merged wording are explicit.

## R4-1 — Initial diluted departure

kind: correction

Adjudication: `ADJ-R4` — CONFIRMED.

Counterexample or reason: A starting D site can have two present bonds, and its first ratio depends on the pins: (3/5)/(1+E[P_fo]/5), rather than always 3/5. Restrict exposure to initial D degree at most one, check this in the recursion, and use the bound 3/4 in the common one-point majorant.

Changed locations: [sec6-walks.tex](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:90): 90–97, 99–109, 139–144, 254–276; [sec7-recursion.tex](/home/ubuntu/aklt/manuscript-corrected/sec7-recursion.tex:126): 126.

`sec6-walks.tex` — frozen lines 53; final lines 90–97.

Before:

```latex
For $w \in \mathcal T_D(u, T)$ we have $R^\cdot_D(w) = \prod_{j = 1}^{|w|} \rho^\cdot_j$ with $\rho^\cdot_j = Z^\cdot_{D;[w_j]} / Z^\cdot_{D;[w_{j - 1}]}$. Let $y = v_{j - 1}$ be the site left at step $j$, $o = v_j$ the out-neighbour, and $E'$ the domain $D;[w_{j - 1}]$ with $y$ removed. Step $j$ is a \emph{revisit} if $y$ has status $\mathrm D$ in $D;[w_{j - 1}]$ and a \emph{first visit} otherwise. Integrating out $y$, we find:
```

After:

```latex
For $w\in\mathcal T_D(u,T)$ as in Proposition~\ref{p:pairwalk}, we have
$R^\cdot_D(w)=\prod_{j=1}^{|w|}\rho^\cdot_j$ with
$\rho^\cdot_j=Z^\cdot_{D;[w_j]}/Z^\cdot_{D;[w_{j-1}]}$.
Let $y=v_{j-1}$ be the site left at step $j$, $o=v_j$ the
out-neighbor, and $E'$ the auxiliary spin network obtained from
$D;[w_{j-1}]$ by removing $y$, retaining its scalar mass. Step $j$ is
a \emph{revisit} if $y$ has status $\mathrm D$ in $D;[w_{j-1}]$ and
a \emph{first visit} otherwise. Integrating out $y$, we find:
```

`sec6-walks.tex` — frozen lines 55; final lines 99–109.

Before:

```latex
\item for a revisit, $\rho^\tau_j = \rho^0_j = 3/5$, since $\int (1 + n \cdot n_o) \lambda_{\mathrm D}(\dd n) = 1$;
```

After:

```latex
\item for a revisit with at most one present bond at departure,
$\rho^\tau_j=\rho^0_j=3/5$, since
$\int(1+n\cdot n_o)\lambda_{\mathrm D}(\dd n)=1$.
The only possible two-bond $\mathrm D$ departure is the initial step.
If its present neighbors are $f,o$, then
\[
\rho^\cdot_1=
\frac{3/5}{1+\frac15\E^\cdot_{E'}[P_{fo}]}\le\frac34.
\]
Indeed, every later departure has already lost its arrival bond;
a $\mathrm D$ site has at most two present bonds before that arrival;
```

`sec6-walks.tex` — frozen lines 85; final lines 139–144.

Before:

```latex
Let $w \in \mathcal T_D(u, T)$, let $\Phi$ be the set of its first-visit steps, and suppose that $\rho^\tau_j \le x_j$ for $j \in \Phi$, with numbers $x_j \ge 1$. Then for every ordering $\sigma$ of $\Phi$,
```

After:

```latex
Let $w\in\mathcal T_D(u,T)$ under the hypotheses of
Proposition~\ref{p:pairwalk}. If $u$ initially has status $\mathrm D$,
assume in addition that it has at most one present bond in $D$.
Let $\Phi$ be the set of first-visit steps of $w$, and suppose that
$\rho^\tau_j\le x_j$ for $j\in\Phi$, with numbers $x_j\ge1$.
Then for every ordering $\sigma$ of $\Phi$,
```

`sec6-walks.tex` — frozen lines 149; final lines 254–276.

Before:

```latex
Every trail of $D$ is a trail of $\Z^2$. A step that leaves a site visited before by $w$ is a revisit in $D;[w_{j - 1}]$, with $3^{-1} \rho^\tau_j = 1/5 = \omega_j$. A step that leaves a site of status $\mathrm D$ not visited before by $w$ has $3^{-1} \rho^\tau_j = 1/5 \le \omega_j$. A first-visit step with pattern $\pi \in \Pext$ has $\rho^\tau_j \le 1/c(\pi) \le x_{\mathrm{type}}$ by Lemma~\ref{l:local} and (H1), so $3^{-1} \rho^\tau_j \le \omega_j$. Any other first-visit step has $3^{-1} \rho^\tau_j \le 4/5 \le \frac{12}{5} \omega_j$ by Lemma~\ref{l:response}, since $\omega_j \ge 1/3$ for first visits. Hence $3^{-|w|} R^\tau_D(w) \le (12/5)^{12} \mathsf W(w)$, and since $|w| \ge d(x, S)$, (H2) gives the claim.
```

After:

```latex
Every trail of $D$ is a trail of $\Z^2$ with initial reversal forbidden for the designated arrival direction, since the bond $\{x-a,x\}$ is absent in $D$. We prove the same pointwise
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

`sec7-recursion.tex` — frozen lines 68; final lines 126.

Before:

```latex
Let $G$, $\tau$, $D$ and $(u, v) \in P_X(D)$ with centre $c$ be as in \eqref{e:FX} with $d_0 = \min(d(u, S), d(v, S)) \ge d \ge 1$; in particular $u, v \notin S$, and $u$ has at most three present bonds because $c$ is removed. By Proposition~\ref{p:pairwalk} with $T = S \cup \{v\}$, applied to $\tau$ and to $0$, the trails are the same in both expansions, and
```

After:

```latex
Let $G$, $\tau$, $D$, and $(u, v) \in P_X(D)$ with center $c$ be as in \eqref{e:FX} with $d_0 = \min(d(u, S), d(v, S)) \ge d \ge 1$; in particular $u, v \notin S$, and $u$ has at most three present bonds because $c$ is removed. At the start of each expansion, normalize a starting site of status $\mathrm U$ by dropping its kept bond to the removed center, as in Lemma~\ref{l:closure}; all histories below use this convention. This changes no partition function, ratio, or correlation. If the starting site has status $\mathrm D$, it has at most one present bond by the definition of $P_X(D)$, as required by Lemma~\ref{l:exposure} in $T_1$. By Proposition~\ref{p:pairwalk} with $T = S \cup \{v\}$, applied to $\tau$ and to $0$, the trails are the same in both expansions, and
```

## R4-2 — Closure at the live endpoint

kind: correction

Adjudication: `ADJ-R4` — CONFIRMED.

Counterexample or reason: In the adjudicated eight-step trail, the live D endpoint has one kept bond at step four. Normalize the starting U bond to the removed center before the empty prefix, distinguish live from non-live sites, and assert consistent-domain membership only after permissible removals.

Changed locations: [sec7-recursion.tex](/home/ubuntu/aklt/manuscript-corrected/sec7-recursion.tex:17): 17–89, 126.

`sec7-recursion.tex` — frozen lines 17–31; final lines 17–89.

Before:

```latex
\begin{lemma}\label{l:closure}
Let $D \in \Dcons(G)$, $(u, v) \in P_X(D)$ with centre $c$, and $u \notin S$. Let $w$ be a trail in $D$ from $u$ that does not visit $S \cup \{v\}$ before its last site, let $w_j$ be its prefixes and $D_j = D;[w_j]$, where at the first step the site $u$ also drops its bond to $c$. Then for every $j$:
\begin{enumerate}
\item every site other than $v_j$ that is visited by $w_j$ has status $\mathrm D$ or $\mathrm X$ in $D_j$;
\item every bond between two non-removed sites of $D_j$ satisfies (C), every site of status $\mathrm D$ keeps exactly two bonds, and every site of status $\mathrm U$ other than $v_j$ keeps all its bonds; $v_j$ has status $\mathrm U$ or $\mathrm D$ and has dropped exactly its arrival bond, whose other end has status $\mathrm D$ or $\mathrm X$;
\item the domain $E'_{j + 1}$ obtained from $D_j$ by removing $v_j$ belongs to $\Dcons(G)$.
\end{enumerate}
Consequently, if step $j + 1$ is a first visit at $y = v_j \notin S$, its pattern (Definition~\ref{d:pattern}), with arrival site $v_{j - 1}$, or $c$ if $j = 0$, belongs to $\Pext$. Moreover, the pairs $(f, g)$, $(f, o)$, $(g, o)$ of non-removed remaining neighbours of $y$ belong to $P_B(E'_{j + 1}) \cup P_C(E'_{j + 1})$, with centre $y$.
\end{lemma}

\begin{proof}
Along $w$, statuses change only from $\mathrm U$ to $\mathrm D$ (at a first visit, keeping the two bonds of the site other than the arrival and out-bonds) and from $\mathrm D$ to $\mathrm X$ (at a revisit). At the first step, $u$ keeps the two bonds other than the out-bond and the bond to $c$, or, if $u$ has status $\mathrm D$ in $D$, it leaves by its only present bond and becomes $\mathrm X$. This gives (1) and the claim on kept sets in (2). A bond dropped by a site of status $\mathrm D$ in $D_j$ is either a bond to a removed site, which is unconstrained, or a bond already dropped in $D$, which satisfies (C) in $D$, or a bond used by $w$. A bond used by $w$ is dropped by both its ends, and both ends were visited by $w$; they have status $\mathrm D$ or $\mathrm X$, except the live end $v_j$ for its arrival bond. This proves (2). Removing $v_j$ makes the arrival bond a bond to a removed site, and $v_j$ was the only site violating the conditions of $\Dcons(G)$, which proves (3).

At a first visit at $y = v_j$, the site $y$ has status $\mathrm U$, its arrival bond is dropped, and the arrival site $s = v_{j - 1}$ (or $c$) has status $\mathrm D$, keeping two of its three bonds other than $\{s, y\}$, or $\mathrm X$. By (2) and (C), every other non-removed site of the template has status $\mathrm U$ with all its bonds, or $\mathrm D$ with exactly two kept bonds, and a neighbour of $y$ of status $\mathrm D$ keeps its bond to $y$, because $y$ keeps all its bonds other than the arrival bond. These are the rules of Definition~\ref{d:pattern}; the statuses of the tips and the bonds of the corners leaving the template are not part of the pattern. Finally, the remaining neighbours $f, g, o$ of $y$ are pairwise at distance $2$ with the common neighbour $y$, which is removed in $E'_{j + 1}$; each has status $\mathrm U$, or status $\mathrm D$ with its bond to $y$ among its two kept bonds and hence at most one present bond in $E'_{j + 1}$.
\end{proof}
```

After:

```latex
\begin{lemma}\label{l:closure}
Let $D\in\Dcons(G)$, $(u,v)\in P_X(D)$ with center $c$, and
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
neighbors belong to $P_B(E'_{j+1})\cup P_C(E'_{j+1})$, with
center $y$.
\end{lemma}

\begin{proof}
At $j=0$, condition (C) is unchanged by dropping a bond to the
removed center. Removing the live endpoint restores the original
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
other non-removed neighbor of $y$ that has status $\mathrm D$
keeps its bond to $y$ and one other bond; every non-live
$\mathrm D$ corner keeps two bonds. These are the rules of
Definition~\ref{d:pattern}, with the tips replaced by their covering
tips and external slots filled as in Lemma~\ref{l:local}. Finally,
any two non-removed remaining neighbors of $y$ are at distance two
with common neighbor $y$, which is removed in $E'_{j+1}$.
A $\mathrm D$ neighbor has at most one present bond after this
removal, so the response pairs have the stated pair classes.
The argument uses no avoidance of the distinguished target $v$.
\end{proof}
```

`sec7-recursion.tex` — frozen lines 68; final lines 126.

Before:

```latex
Let $G$, $\tau$, $D$ and $(u, v) \in P_X(D)$ with centre $c$ be as in \eqref{e:FX} with $d_0 = \min(d(u, S), d(v, S)) \ge d \ge 1$; in particular $u, v \notin S$, and $u$ has at most three present bonds because $c$ is removed. By Proposition~\ref{p:pairwalk} with $T = S \cup \{v\}$, applied to $\tau$ and to $0$, the trails are the same in both expansions, and
```

After:

```latex
Let $G$, $\tau$, $D$, and $(u, v) \in P_X(D)$ with center $c$ be as in \eqref{e:FX} with $d_0 = \min(d(u, S), d(v, S)) \ge d \ge 1$; in particular $u, v \notin S$, and $u$ has at most three present bonds because $c$ is removed. At the start of each expansion, normalize a starting site of status $\mathrm U$ by dropping its kept bond to the removed center, as in Lemma~\ref{l:closure}; all histories below use this convention. This changes no partition function, ratio, or correlation. If the starting site has status $\mathrm D$, it has at most one present bond by the definition of $P_X(D)$, as required by Lemma~\ref{l:exposure} in $T_1$. By Proposition~\ref{p:pairwalk} with $T = S \cup \{v\}$, applied to $\tau$ and to $0$, the trails are the same in both expansions, and
```

## R4-3 — Auxiliary networks and the second expansion

kind: correction

Adjudication: `ADJ-R4` — CONFIRMED.

Counterexample or reason: A stopped trace drops its arrival bond at a protected boundary site, so it need not be an original domain. Define networks with positive scalar trace mass and original leg factors, extend the pair expansion, and prove the second expansion has at most twelve exceptional first U departures in the radius-two neighborhood of its fixed boundary defect. The one-point bound controls the sum of pinned/free maxima.

Changed locations: [sec6-walks.tex](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:18): 18–32, 51–68, 71–74, 90–97, 213–222, 239–250, 254–276; [sec7-recursion.tex](/home/ubuntu/aklt/manuscript-corrected/sec7-recursion.tex:126): 126, 138–168.

`sec6-walks.tex` — frozen lines 18; final lines 18–32.

Before:

```latex
% No text at this insertion point.
```

After:

```latex
For tracing we also use an \emph{auxiliary spin network} on $G$. It has
the same statuses, site measures, and kept-bond data as a domain, with at
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

`sec6-walks.tex` — frozen lines 37; final lines 51–68.

Before:

```latex
A \emph{trail} in a domain $D$ from $u$ is a sequence $w = (v_0, \dots, v_m)$ with $v_0 = u$ such that $\{v_{i - 1}, v_i\}$ are distinct present bonds of $D$; $|w| = m$ is its length. For $T \subset G$ let $\mathcal T_D(u, T)$ be the set of trails with $v_m \in T$ and $v_i \notin T$ for $i < m$. The \emph{traced domain} $D;[w]$ is obtained from $D$ step by step: at step $j$ the bond $\{v_{j - 1}, v_j\}$ is dropped by both ends, and the status of $v_{j - 1}$ changes from $\mathrm U$ to $\mathrm D$ (keeping its remaining bonds) or from $\mathrm D$ to $\mathrm X$; in the latter case we multiply the partition function by $\frac35$, the mass of $\frac35 \delta_0$. We write $w_j = (v_0, \dots, v_j)$.
```

After:

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

`sec6-walks.tex` — frozen lines 40; final lines 71–74.

Before:

```latex
Let $D$ be a domain on $G$, let $u \in G \setminus S$ be a site that is not removed and has at most three present bonds, let $v \neq u$ be a site that is not removed, and $T = S \cup \{v\}$. Then, with the dot standing for $\tau$ or $0$,
```

After:

```latex
Let $D$ be a domain or auxiliary spin network on $G$, let
$u\in G\setminus S$ be a site that is not removed and has at most
three present bonds, let $v\ne u$ be a site that is not removed, and
$T=S\cup\{v\}$. Then, with the dot standing for $\tau$ or $0$,
```

`sec6-walks.tex` — frozen lines 53; final lines 90–97.

Before:

```latex
For $w \in \mathcal T_D(u, T)$ we have $R^\cdot_D(w) = \prod_{j = 1}^{|w|} \rho^\cdot_j$ with $\rho^\cdot_j = Z^\cdot_{D;[w_j]} / Z^\cdot_{D;[w_{j - 1}]}$. Let $y = v_{j - 1}$ be the site left at step $j$, $o = v_j$ the out-neighbour, and $E'$ the domain $D;[w_{j - 1}]$ with $y$ removed. Step $j$ is a \emph{revisit} if $y$ has status $\mathrm D$ in $D;[w_{j - 1}]$ and a \emph{first visit} otherwise. Integrating out $y$, we find:
```

After:

```latex
For $w\in\mathcal T_D(u,T)$ as in Proposition~\ref{p:pairwalk}, we have
$R^\cdot_D(w)=\prod_{j=1}^{|w|}\rho^\cdot_j$ with
$\rho^\cdot_j=Z^\cdot_{D;[w_j]}/Z^\cdot_{D;[w_{j-1}]}$.
Let $y=v_{j-1}$ be the site left at step $j$, $o=v_j$ the
out-neighbor, and $E'$ the auxiliary spin network obtained from
$D;[w_{j-1}]$ by removing $y$, retaining its scalar mass. Step $j$ is
a \emph{revisit} if $y$ has status $\mathrm D$ in $D;[w_{j-1}]$ and
a \emph{first visit} otherwise. Integrating out $y$, we find:
```

`sec6-walks.tex` — frozen lines 130; final lines 213–222.

Before:

```latex
Lemma~\ref{l:local} applies to every first-visit step whose pattern is in $\Pext$. Lemma~\ref{l:closure} in \S\ref{s:recursion} shows that this is the case for every first-visit step of every trail used in the recursion, except at most $12$ steps near the end of the trails of the stopped term $T_2$, where only the crude bound $\rho^\tau_j \le 12/5$ of Lemma~\ref{l:response} is used.
```

After:

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

`sec6-walks.tex` — frozen lines 142–145; final lines 239–250.

Before:

```latex
Assume (H1) and (H2). Let $D \in \Dcons(G)$ or $D = D_0;[w_0]$ for some $D_0 \in \Dcons(G)$ and a trail $w_0$, let $x \in G \setminus S$ be a site that is not removed and has at most three present bonds, with a designated arrival direction, and suppose that all first-visit steps of every trail in $\mathcal T_D(x, S)$, except at most $12$ steps of each trail, have their patterns in $\Pext$. Then
\begin{equation*}
\sum_{w \in \mathcal T_D(x, S)} 3^{-|w|} R^\tau_D(w) \le \Bigl( \frac{12}{5} \Bigr)^{12} \frac{C_V}{1 - q} \, q^{d(x, S)} .
\end{equation*}
```

After:

```latex
Assume (H1) and (H2). Let $D$ be a domain or auxiliary spin network
on $G$, let $x\in G\setminus S$ be a site that is not removed and
has at most three present bonds, with a designated arrival direction $a$ such that the bond $\{x-a,x\}$ is absent in $D$,
and suppose that all first-visit steps of every trail in
$\mathcal T_D(x,S)$, except at most $12$ steps of each trail, have
their patterns in $\Pext$. Then
\begin{equation*}
\sum_{w\in\mathcal T_D(x,S)}3^{-|w|}
\max\{R^\tau_D(w),R^0_D(w)\}
\le \Bigl(\frac{12}{5}\Bigr)^{12}
\frac{C_V}{1-q}\,q^{d(x,S)}.
\end{equation*}
```

`sec6-walks.tex` — frozen lines 149; final lines 254–276.

Before:

```latex
Every trail of $D$ is a trail of $\Z^2$. A step that leaves a site visited before by $w$ is a revisit in $D;[w_{j - 1}]$, with $3^{-1} \rho^\tau_j = 1/5 = \omega_j$. A step that leaves a site of status $\mathrm D$ not visited before by $w$ has $3^{-1} \rho^\tau_j = 1/5 \le \omega_j$. A first-visit step with pattern $\pi \in \Pext$ has $\rho^\tau_j \le 1/c(\pi) \le x_{\mathrm{type}}$ by Lemma~\ref{l:local} and (H1), so $3^{-1} \rho^\tau_j \le \omega_j$. Any other first-visit step has $3^{-1} \rho^\tau_j \le 4/5 \le \frac{12}{5} \omega_j$ by Lemma~\ref{l:response}, since $\omega_j \ge 1/3$ for first visits. Hence $3^{-|w|} R^\tau_D(w) \le (12/5)^{12} \mathsf W(w)$, and since $|w| \ge d(x, S)$, (H2) gives the claim.
```

After:

```latex
Every trail of $D$ is a trail of $\Z^2$ with initial reversal forbidden for the designated arrival direction, since the bond $\{x-a,x\}$ is absent in $D$. We prove the same pointwise
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

`sec7-recursion.tex` — frozen lines 68; final lines 126.

Before:

```latex
Let $G$, $\tau$, $D$ and $(u, v) \in P_X(D)$ with centre $c$ be as in \eqref{e:FX} with $d_0 = \min(d(u, S), d(v, S)) \ge d \ge 1$; in particular $u, v \notin S$, and $u$ has at most three present bonds because $c$ is removed. By Proposition~\ref{p:pairwalk} with $T = S \cup \{v\}$, applied to $\tau$ and to $0$, the trails are the same in both expansions, and
```

After:

```latex
Let $G$, $\tau$, $D$, and $(u, v) \in P_X(D)$ with center $c$ be as in \eqref{e:FX} with $d_0 = \min(d(u, S), d(v, S)) \ge d \ge 1$; in particular $u, v \notin S$, and $u$ has at most three present bonds because $c$ is removed. At the start of each expansion, normalize a starting site of status $\mathrm U$ by dropping its kept bond to the removed center, as in Lemma~\ref{l:closure}; all histories below use this convention. This changes no partition function, ratio, or correlation. If the starting site has status $\mathrm D$, it has at most one present bond by the definition of $P_X(D)$, as required by Lemma~\ref{l:exposure} in $T_1$. By Proposition~\ref{p:pairwalk} with $T = S \cup \{v\}$, applied to $\tau$ and to $0$, the trails are the same in both expansions, and
```

`sec7-recursion.tex` — frozen lines 80; final lines 138–168.

Before:

```latex
\emph{The term $T_2$.} Let $w \in \mathcal W_1$, ending at $e \in S$. By Proposition~\ref{p:pairwalk} in $D;[w]$, started at $v$ with target $e$ and stopping set $S$, $|\mathcal X^\cdot(w)| \le \sum_{w' \in \mathcal T_{D;[w]}(v, S)} 3^{-|w'|} R^\cdot_{D;[w]}(w')$. In $D;[w]$ the only violation of the rules of $\Dcons(G)$ is at $e$, whose arrival bond is dropped (Lemma~\ref{l:closure}(2)). A first-visit step of $w'$ at $y'$ whose template does not contain both $e$ and the other end of that bond has its pattern in $\Pext$ by the argument of Lemma~\ref{l:closure}; the remaining first-visit steps have $e \in \mathsf T(y')$ and $y' \neq e$, so there are at most $12$ of them. Every $w \in \mathcal W_1$ belongs to $\mathcal T_D(u, S)$. The proof of Lemma~\ref{l:onepoint} applies to $R^0$ as well as to $R^\tau$, since $\rho^0_j \le 1 \le x_j$ for first visits and $\rho^0_j = 3/5$ for revisits. Applying Lemma~\ref{l:onepoint} in $D$ from $u$ and in $D;[w]$ from $v$, we obtain
```

After:

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
its kept bond to the removed center $c$; this changes no partition
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

## R4-4 — Endpoint independence

kind: correction

Adjudication: `ADJ-R4` — CONFIRMED.

Counterexample or reason: If the target is initially D with two present bonds, arrival leaves a bond to another spin. Its conditional mean is a/5, so the asserted independence is unjustified. Repeat the one-initial-present-bond qualification in the proof.

Changed locations: [sec6-walks.tex](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:82): 82–85.

`sec6-walks.tex` — frozen lines 48; final lines 82–85.

Before:

```latex
Write $n_u \cdot n_v = \sum_{\beta = 1}^3 n_u^\beta n_v^\beta$ and fix $\beta$. In $Z^\cdot_D[n_u^\beta n_v^\beta]$, integrate the spin of $u$ using Lemma~\ref{l:stepid} with $a = e_\beta$; the site $u$ carries no leg because $u \notin S$, and the factor $n_v^\beta$ does not involve $n_u$. This gives a sum over the present bonds $\{u, v_1\}$ of $\frac13 Z^\cdot_{D;[(u, v_1)]}[n_{v_1}^\beta n_v^\beta]$. If $v_1 \notin T$ we repeat the step at $v_1$: it carries no leg, a site of status $\mathrm U$ has at most three remaining factors after the arrival bond is dropped, and a site of status $\mathrm D$ at most one. The procedure stops at the first visit of $T$, and a step from a site without remaining bonds contributes $0$. Every trail is finite, so after finitely many steps we obtain $Z^\cdot_D[n_u^\beta n_v^\beta] = \sum_w 3^{-|w|} Z^\cdot_{D;[w]}[n_{v_{|w|}}^\beta n_v^\beta]$. Summing over $\beta$ and dividing by $Z^\cdot_D$ gives \eqref{e:pairwalk}. If $v_{|w|} = v$, the last bracket is $|n_v|^2$, and if $v$ has status $\mathrm D$ its only remaining bond was the arrival bond, so after arrival $n_v$ is independent of the rest with law $\lambda_{\mathrm D}$, and $\E|n_v|^2 = 3/5$.
```

After:

```latex
Write $n_u \cdot n_v = \sum_{\beta = 1}^3 n_u^\beta n_v^\beta$ and fix $\beta$. In $Z^\cdot_D[n_u^\beta n_v^\beta]$, integrate the spin of $u$ using Lemma~\ref{l:stepid} with $a = e_\beta$; the site $u$ carries no leg because $u \notin S$, and the factor $n_v^\beta$ does not involve $n_u$. This gives a sum over the present bonds $\{u, v_1\}$ of $\frac13 Z^\cdot_{D;[(u, v_1)]}[n_{v_1}^\beta n_v^\beta]$. If $v_1 \notin T$ we repeat the step at $v_1$: it carries no leg, a site of status $\mathrm U$ has at most three remaining factors after the arrival bond is dropped, and a site of status $\mathrm D$ at most one. The procedure stops at the first visit of $T$, and a step from a site without remaining bonds contributes $0$. Every trail is finite, so after finitely many steps we obtain $Z^\cdot_D[n_u^\beta n_v^\beta] = \sum_w 3^{-|w|} Z^\cdot_{D;[w]}[n_{v_{|w|}}^\beta n_v^\beta]$. Summing over $\beta$ and dividing by $Z^\cdot_D$ gives \eqref{e:pairwalk}. If $v_{|w|}=v$, the last bracket is $|n_v|^2$. If $v$ has
status $\mathrm D$ with one present bond in $D$, that bond was the
arrival bond, so after arrival $n_v$ is independent of the rest with
law $\lambda_{\mathrm D}$, and $\E|n_v|^2=3/5$.
```

## R4-5 — Full U pattern data and covered slots

kind: correction

Adjudication: `ADJ-R4` — CONFIRMED.

Counterexample or reason: General domains allow partial U kept sets, but the local integral formulas and the 7,962 archived effective patterns require full U sets away from the passage site and exactly three non-arrival passage bonds. State those restrictions and the covering-tip/external-slot convention explicitly.

Changed locations: [sec6-walks.tex](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:163): 163–179, 183–191.

`sec6-walks.tex` — frozen lines 104; final lines 163–179.

Before:

```latex
A \emph{pattern} $\pi$ consists of an out-neighbour $o \in \{\mathsf e, \mathsf N, \mathsf W\}$ and statuses and kept bonds of the sites $\mathsf s, \mathsf e, \mathsf N, \mathsf W$ and of the corners, as in Definition~\ref{d:domain}, with $y$ of status $\mathrm U$, the bond $\{y, \mathsf s\}$ dropped, and $o$ not removed. For unit vectors $m = (m_\ell)$ on the slots, let $Z_{\mathrm{cur}}(\pi; m)$ be the integral over the spins of $\mathsf T(y)$ minus the removed sites, with the site measures of the statuses, of the product of the factors of the present bonds inside $\mathsf T(y)$ and of $1 + m_\ell \cdot n_z$ for every slot $\ell$ at $z$; the tips have status $\mathrm U$. Let $Z_{\mathrm{next}}(\pi; m)$ be the same integral after the step, that is, with the measure of $y$ replaced by $\lambda_{\mathrm D}$ and the bond $\{y, o\}$ dropped. Define
```

After:

```latex
A \emph{pattern} $\pi$ consists of an out-neighbor
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

`sec6-walks.tex` — frozen lines 108; final lines 183–191.

Before:

```latex
The class $\Pext$ consists of the patterns in which: $\mathsf s$ is removed or has status $\mathrm D$ keeping two of its three bonds other than $\{y, \mathsf s\}$; each of $\mathsf e, \mathsf N, \mathsf W$ has status $\mathrm U$, $\mathrm X$, or $\mathrm D$ keeping the bond to $y$ and one other bond; each corner has status $\mathrm U$, $\mathrm X$, or $\mathrm D$ keeping two of its four bonds; and condition (C) holds for the bonds between non-removed sites of $\mathsf T(y)$ other than the tips. (The statuses of the tips are not part of a pattern; a bond between a tip and its neighbour $z$ is present in $Z_{\mathrm{cur}}$ and $Z_{\mathrm{next}}$ if and only if $z$ is not removed and keeps it.) A pattern is straight or a turn according to $o$.
```

After:

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

## R7-1 — Terminal boundary closure

kind: correction

Adjudication: `ADJ-R4` — CONFIRMED.

Counterexample or reason: The allowed trail from (-1,0) through (-2,0) to (-3,0) in the square [-4,4]^2 ends in S and drops its arrival bond there. Removing that protected endpoint violates the original domain definition. Use the shared R4 closure lemma and auxiliary-network expansion instead.

Changed locations: [sec6-walks.tex](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:18): 18–32, 51–68, 71–74, 213–222, 239–250; [sec7-recursion.tex](/home/ubuntu/aklt/manuscript-corrected/sec7-recursion.tex:17): 17–89, 138–168.

`sec6-walks.tex` — frozen lines 18; final lines 18–32.

Before:

```latex
% No text at this insertion point.
```

After:

```latex
For tracing we also use an \emph{auxiliary spin network} on $G$. It has
the same statuses, site measures, and kept-bond data as a domain, with at
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

`sec6-walks.tex` — frozen lines 37; final lines 51–68.

Before:

```latex
A \emph{trail} in a domain $D$ from $u$ is a sequence $w = (v_0, \dots, v_m)$ with $v_0 = u$ such that $\{v_{i - 1}, v_i\}$ are distinct present bonds of $D$; $|w| = m$ is its length. For $T \subset G$ let $\mathcal T_D(u, T)$ be the set of trails with $v_m \in T$ and $v_i \notin T$ for $i < m$. The \emph{traced domain} $D;[w]$ is obtained from $D$ step by step: at step $j$ the bond $\{v_{j - 1}, v_j\}$ is dropped by both ends, and the status of $v_{j - 1}$ changes from $\mathrm U$ to $\mathrm D$ (keeping its remaining bonds) or from $\mathrm D$ to $\mathrm X$; in the latter case we multiply the partition function by $\frac35$, the mass of $\frac35 \delta_0$. We write $w_j = (v_0, \dots, v_j)$.
```

After:

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

`sec6-walks.tex` — frozen lines 40; final lines 71–74.

Before:

```latex
Let $D$ be a domain on $G$, let $u \in G \setminus S$ be a site that is not removed and has at most three present bonds, let $v \neq u$ be a site that is not removed, and $T = S \cup \{v\}$. Then, with the dot standing for $\tau$ or $0$,
```

After:

```latex
Let $D$ be a domain or auxiliary spin network on $G$, let
$u\in G\setminus S$ be a site that is not removed and has at most
three present bonds, let $v\ne u$ be a site that is not removed, and
$T=S\cup\{v\}$. Then, with the dot standing for $\tau$ or $0$,
```

`sec6-walks.tex` — frozen lines 130; final lines 213–222.

Before:

```latex
Lemma~\ref{l:local} applies to every first-visit step whose pattern is in $\Pext$. Lemma~\ref{l:closure} in \S\ref{s:recursion} shows that this is the case for every first-visit step of every trail used in the recursion, except at most $12$ steps near the end of the trails of the stopped term $T_2$, where only the crude bound $\rho^\tau_j \le 12/5$ of Lemma~\ref{l:response} is used.
```

After:

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

`sec6-walks.tex` — frozen lines 142–145; final lines 239–250.

Before:

```latex
Assume (H1) and (H2). Let $D \in \Dcons(G)$ or $D = D_0;[w_0]$ for some $D_0 \in \Dcons(G)$ and a trail $w_0$, let $x \in G \setminus S$ be a site that is not removed and has at most three present bonds, with a designated arrival direction, and suppose that all first-visit steps of every trail in $\mathcal T_D(x, S)$, except at most $12$ steps of each trail, have their patterns in $\Pext$. Then
\begin{equation*}
\sum_{w \in \mathcal T_D(x, S)} 3^{-|w|} R^\tau_D(w) \le \Bigl( \frac{12}{5} \Bigr)^{12} \frac{C_V}{1 - q} \, q^{d(x, S)} .
\end{equation*}
```

After:

```latex
Assume (H1) and (H2). Let $D$ be a domain or auxiliary spin network
on $G$, let $x\in G\setminus S$ be a site that is not removed and
has at most three present bonds, with a designated arrival direction $a$ such that the bond $\{x-a,x\}$ is absent in $D$,
and suppose that all first-visit steps of every trail in
$\mathcal T_D(x,S)$, except at most $12$ steps of each trail, have
their patterns in $\Pext$. Then
\begin{equation*}
\sum_{w\in\mathcal T_D(x,S)}3^{-|w|}
\max\{R^\tau_D(w),R^0_D(w)\}
\le \Bigl(\frac{12}{5}\Bigr)^{12}
\frac{C_V}{1-q}\,q^{d(x,S)}.
\end{equation*}
```

`sec7-recursion.tex` — frozen lines 17–31; final lines 17–89.

Before:

```latex
\begin{lemma}\label{l:closure}
Let $D \in \Dcons(G)$, $(u, v) \in P_X(D)$ with centre $c$, and $u \notin S$. Let $w$ be a trail in $D$ from $u$ that does not visit $S \cup \{v\}$ before its last site, let $w_j$ be its prefixes and $D_j = D;[w_j]$, where at the first step the site $u$ also drops its bond to $c$. Then for every $j$:
\begin{enumerate}
\item every site other than $v_j$ that is visited by $w_j$ has status $\mathrm D$ or $\mathrm X$ in $D_j$;
\item every bond between two non-removed sites of $D_j$ satisfies (C), every site of status $\mathrm D$ keeps exactly two bonds, and every site of status $\mathrm U$ other than $v_j$ keeps all its bonds; $v_j$ has status $\mathrm U$ or $\mathrm D$ and has dropped exactly its arrival bond, whose other end has status $\mathrm D$ or $\mathrm X$;
\item the domain $E'_{j + 1}$ obtained from $D_j$ by removing $v_j$ belongs to $\Dcons(G)$.
\end{enumerate}
Consequently, if step $j + 1$ is a first visit at $y = v_j \notin S$, its pattern (Definition~\ref{d:pattern}), with arrival site $v_{j - 1}$, or $c$ if $j = 0$, belongs to $\Pext$. Moreover, the pairs $(f, g)$, $(f, o)$, $(g, o)$ of non-removed remaining neighbours of $y$ belong to $P_B(E'_{j + 1}) \cup P_C(E'_{j + 1})$, with centre $y$.
\end{lemma}

\begin{proof}
Along $w$, statuses change only from $\mathrm U$ to $\mathrm D$ (at a first visit, keeping the two bonds of the site other than the arrival and out-bonds) and from $\mathrm D$ to $\mathrm X$ (at a revisit). At the first step, $u$ keeps the two bonds other than the out-bond and the bond to $c$, or, if $u$ has status $\mathrm D$ in $D$, it leaves by its only present bond and becomes $\mathrm X$. This gives (1) and the claim on kept sets in (2). A bond dropped by a site of status $\mathrm D$ in $D_j$ is either a bond to a removed site, which is unconstrained, or a bond already dropped in $D$, which satisfies (C) in $D$, or a bond used by $w$. A bond used by $w$ is dropped by both its ends, and both ends were visited by $w$; they have status $\mathrm D$ or $\mathrm X$, except the live end $v_j$ for its arrival bond. This proves (2). Removing $v_j$ makes the arrival bond a bond to a removed site, and $v_j$ was the only site violating the conditions of $\Dcons(G)$, which proves (3).

At a first visit at $y = v_j$, the site $y$ has status $\mathrm U$, its arrival bond is dropped, and the arrival site $s = v_{j - 1}$ (or $c$) has status $\mathrm D$, keeping two of its three bonds other than $\{s, y\}$, or $\mathrm X$. By (2) and (C), every other non-removed site of the template has status $\mathrm U$ with all its bonds, or $\mathrm D$ with exactly two kept bonds, and a neighbour of $y$ of status $\mathrm D$ keeps its bond to $y$, because $y$ keeps all its bonds other than the arrival bond. These are the rules of Definition~\ref{d:pattern}; the statuses of the tips and the bonds of the corners leaving the template are not part of the pattern. Finally, the remaining neighbours $f, g, o$ of $y$ are pairwise at distance $2$ with the common neighbour $y$, which is removed in $E'_{j + 1}$; each has status $\mathrm U$, or status $\mathrm D$ with its bond to $y$ among its two kept bonds and hence at most one present bond in $E'_{j + 1}$.
\end{proof}
```

After:

```latex
\begin{lemma}\label{l:closure}
Let $D\in\Dcons(G)$, $(u,v)\in P_X(D)$ with center $c$, and
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
neighbors belong to $P_B(E'_{j+1})\cup P_C(E'_{j+1})$, with
center $y$.
\end{lemma}

\begin{proof}
At $j=0$, condition (C) is unchanged by dropping a bond to the
removed center. Removing the live endpoint restores the original
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
other non-removed neighbor of $y$ that has status $\mathrm D$
keeps its bond to $y$ and one other bond; every non-live
$\mathrm D$ corner keeps two bonds. These are the rules of
Definition~\ref{d:pattern}, with the tips replaced by their covering
tips and external slots filled as in Lemma~\ref{l:local}. Finally,
any two non-removed remaining neighbors of $y$ are at distance two
with common neighbor $y$, which is removed in $E'_{j+1}$.
A $\mathrm D$ neighbor has at most one present bond after this
removal, so the response pairs have the stated pair classes.
The argument uses no avoidance of the distinguished target $v$.
\end{proof}
```

`sec7-recursion.tex` — frozen lines 80; final lines 138–168.

Before:

```latex
\emph{The term $T_2$.} Let $w \in \mathcal W_1$, ending at $e \in S$. By Proposition~\ref{p:pairwalk} in $D;[w]$, started at $v$ with target $e$ and stopping set $S$, $|\mathcal X^\cdot(w)| \le \sum_{w' \in \mathcal T_{D;[w]}(v, S)} 3^{-|w'|} R^\cdot_{D;[w]}(w')$. In $D;[w]$ the only violation of the rules of $\Dcons(G)$ is at $e$, whose arrival bond is dropped (Lemma~\ref{l:closure}(2)). A first-visit step of $w'$ at $y'$ whose template does not contain both $e$ and the other end of that bond has its pattern in $\Pext$ by the argument of Lemma~\ref{l:closure}; the remaining first-visit steps have $e \in \mathsf T(y')$ and $y' \neq e$, so there are at most $12$ of them. Every $w \in \mathcal W_1$ belongs to $\mathcal T_D(u, S)$. The proof of Lemma~\ref{l:onepoint} applies to $R^0$ as well as to $R^\tau$, since $\rho^0_j \le 1 \le x_j$ for first visits and $\rho^0_j = 3/5$ for revisits. Applying Lemma~\ref{l:onepoint} in $D$ from $u$ and in $D;[w]$ from $v$, we obtain
```

After:

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
its kept bond to the removed center $c$; this changes no partition
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

## R5-1 — Nonnegative remainder vector

kind: correction

Adjudication: `ADJ-R5` — CONFIRMED.

Counterexample or reason: There are 64 memory-10 windows with zero indegree; the constructed vector is zero there in every phase. Strict positivity and ratios over all coordinates fail. Allow z>=0, check terminal mass vanishes on its zero set, divide only where z>0, require finite data and successful inequalities, and use the actual stored lcheck.

Changed locations: [app-tail.tex](/home/ubuntu/aklt/manuscript-corrected/app-tail.tex:76): 76, 90–96, 120–123, 151–164, 176, 179–187.

`app-tail.tex` — frozen lines 76; final lines 76.

Before:

```latex
Let $V_t$ be a memory walk with $t_* < T$, and let $\mathbb W$ be its weight matrix on $\Omega \times \{\mathrm A, \mathrm B, \mathrm C, \mathrm D\}$ without rules, $\mathbb W((\omega, \varphi), (\omega \cdot d, \varphi'))$ the weight of the step $d$ from phase $\varphi$ to phase $\varphi'$ in (II). Suppose that $z \colon \Omega \times \{\mathrm A, \mathrm B, \mathrm C, \mathrm D\} \to (0, \infty)$, $\lambda \in (0, 1)$ and $a \ge 0$ satisfy $z \mathbb W \le \lambda z$ and $V_T(\omega, \xi, \varphi) \le a \, z(\omega, \varphi)$ for all $\omega, \xi, \varphi$. Then
```

After:

```latex
Let $V_t$ be a memory walk with $t_* < T$, and let $\mathbb W$ be its weight matrix on $\Omega \times \{\mathrm A, \mathrm B, \mathrm C, \mathrm D\}$ without rules, $\mathbb W((\omega, \varphi), (\omega \cdot d, \varphi'))$ the weight of the step $d$ from phase $\varphi$ to phase $\varphi'$ in (II). Suppose that $z \colon \Omega \times \{\mathrm A, \mathrm B, \mathrm C, \mathrm D\} \to [0, \infty)$, $\lambda \in (0, 1)$ and $a \ge 0$ satisfy $z \mathbb W \le \lambda z$ and $V_T(\omega, \xi, \varphi) \le a \, z(\omega, \varphi)$ for all $\omega, \xi, \varphi$. Then
```

`app-tail.tex` — frozen lines 90; final lines 90–96.

Before:

```latex
The matrix $\mathbb W$ is block triangular in the phases ($\mathrm A \to \mathrm A, \mathrm C$; $\mathrm B \to \mathrm B, \mathrm D$; $\mathrm C \to \mathrm C$; $\mathrm D \to \mathrm D$), and its spectral radius is that of the block $\mathrm A \to \mathrm A$, the memory-$10$ walk with the weights $x_{\mathrm s}/3$, $x_{\mathrm t}/3$, $1/5$. A sub-invariant $z$ is obtained from the left Perron vectors of the diagonal blocks and the solutions of $z_{\mathrm C} (\lambda - \mathbb W_{\mathrm{CC}}) = z_{\mathrm A} \mathbb W_{\mathrm{AC}}$, $z_{\mathrm D} (\lambda - \mathbb W_{\mathrm{DD}}) = z_{\mathrm B} \mathbb W_{\mathrm{BD}}$; only the inequality $z \mathbb W \le \lambda z$ is used, and it is checked directly.
```

After:

```latex
The matrix $\mathbb W$ is block triangular in the phases ($\mathrm A \to \mathrm A, \mathrm C$; $\mathrm B \to \mathrm B, \mathrm D$; $\mathrm C \to \mathrm C$; $\mathrm D \to \mathrm D$), and its spectral radius is that of the block $\mathrm A \to \mathrm A$, the memory-$10$ walk with the weights $x_{\mathrm s}/3$, $x_{\mathrm t}/3$, $1/5$. A nonnegative candidate $z$ is obtained by power iteration in the diagonal blocks and approximate solution of
$z_{\mathrm C}(\lambda-\mathbb W_{\mathrm{CC}})=z_{\mathrm A}\mathbb W_{\mathrm{AC}}$ and
$z_{\mathrm D}(\lambda-\mathbb W_{\mathrm{DD}})=z_{\mathrm B}\mathbb W_{\mathrm{BD}}$;
only the inequality $z\mathbb W\le\lambda z$ is used, and it is checked directly.
The constructed vector is zero in each phase at exactly the $64$ windows of indegree zero, and positive at every other window.
No update can put mass at a window of indegree zero, so $V_T$ vanishes there for $T\ge21$.
In applying Lemma~\ref{l:remainder}, we check this zero-support condition and take ratios only where $z>0$.
```

`app-tail.tex` — frozen lines 114; final lines 120–123.

Before:

```latex
By Lemma~\ref{l:CW} it suffices to bound $(M_1 h)_X = \sum_n \mathsf m_X(n)$ for both rows, and we split the sum over the even $n$ as in Table~\ref{tab:tail}. The trails of length at most $20$ are enumerated exactly. For $22 \le n \le 106$ we use Lemma~\ref{l:memdom}(1) and $\mathcal T^X_n = \bigcup_{D_0} \mathcal T^{X, D_0}_n$, a disjoint union. For $108 \le n \le 260$ we use Lemma~\ref{l:memdom}(2); note that $n = 108$ is beyond the range of mode A, because the rules (R1) at $[u + D_0]$ and (R2) can act at images for closed trails of length $2P - 4 = 108$. For $n > 260$ we use Lemma~\ref{l:remainder} with $T = 260$ for the walk of mode B, with $\lambda = 0.97953279$ (the memory-$10$ walk with the weights $x_{\mathrm s}/3$, $x_{\mathrm t}/3$, $1/5$ has growth $0.9795328$), a vector $z$ for which $z \mathbb W \le \lambda z$ is verified, and $a = \max V_{260}/z$. The entries of the table are computed as described in \S\ref{s:tailtrust}.
```

After:

```latex
By Lemma~\ref{l:CW} it suffices to bound $(M_1 h)_X = \sum_n \mathsf m_X(n)$ for both rows, and we split the sum over the even $n$ as in Table~\ref{tab:tail}. The trails of length at most $20$ are enumerated exactly. For $22 \le n \le 106$ we use Lemma~\ref{l:memdom}(1) and $\mathcal T^X_n = \bigcup_{D_0} \mathcal T^{X, D_0}_n$, a disjoint union. For $108 \le n \le 260$ we use Lemma~\ref{l:memdom}(2); note that $n = 108$ is beyond the range of mode A, because the rules (R1) at $[u + D_0]$ and (R2) can act at images for closed trails of length $2P - 4 = 108$. For $n>260$ we use Lemma~\ref{l:remainder} with $T=260$ for the walk of mode B, taking $\lambda$ to be the stored binary64 value \texttt{lcheck} used in both the sub-invariance check and the remainder calculation, with $0<\lambda\le0.979532789<0.97953279$.
The nonnegative vector $z$ satisfies the directly checked inequality $z\mathbb W\le\lambda z$.
We verify $V_{260}(\omega,\xi,\varphi)=0$ whenever $z(\omega,\varphi)=0$, and choose $a$ as an upward-rounded upper bound for
$\max_{z(\omega,\varphi)>0}V_{260}(\omega,\xi,\varphi)/z(\omega,\varphi)$. The entries of the table are computed as described in \S\ref{s:tailtrust}.
```

`app-tail.tex` — frozen lines 121; final lines 151–164.

Before:

```latex
\emph{Arithmetic.} All quantities are sums of products of nonnegative numbers, and no subtraction occurs. The programs set the rounding mode upward before any computation; the constants $\cs, \ct$ are decreased and $\bar\alpha, \bar\beta$ increased by one unit in the last place after decimal conversion, and $1/3$, $1/5$, $1/\cs$, $1/\ct$ are computed by upward division. The walk is stored in binary32 and the enumeration in binary64; every product, sum and conversion is rounded upward, so every stored value is at least the exact one, and underflow produces a positive subnormal number, never $0$. In the check of $z \mathbb W \le \lambda z$ the left side is rounded upward and the right side downward, and $1 - \lambda$ is rounded downward. The output decimals are rounded upward as well (the C library rounds conversions in the current rounding mode), and the table sums them exactly as rational numbers. The programs must be compiled with \texttt{-frounding-math}: the compiler ignores the \texttt{FENV\_ACCESS} pragma, and without this option it may evaluate or move floating-point operations across the changes of the rounding mode. The hypothesis $\lambda < 1$ of Lemma~\ref{l:remainder} is not checked by the program and must be read off its output.
```

After:

```latex
\emph{Arithmetic.}
The enumeration and walk bounds are evaluated as sums of products of nonnegative quantities.
The constants $\cs,\ct$ are decreased and $\bar\alpha,\bar\beta$ increased by one unit in the last place after decimal conversion;
$1/3$, $1/5$, $1/\cs$ and $1/\ct$ are computed by upward division.
The walk arrays are stored in binary32 and the enumeration in binary64.
Bound-producing products, sums and conversions, and their output decimals, are rounded upward, with gradual underflow.
The ordering search and the construction of a candidate $z$ need not use upward rounding: any chosen ordering gives an upper bound for the per-trail minimum, and the stored candidate is subsequently treated as an exact dyadic vector.
In checking $z\mathbb W\le\lambda z$, the left side is rounded upward and the right side downward; $1-\lambda$ is rounded downward in the remainder formula.
Acceptance requires finite nonnegative data, $0<\lambda<1$, the checked sub-invariance inequality, and $V_T=0$ wherever $z=0$.
Ratios defining $a$ are taken only at positive coordinates of $z$, with upward rounding; nonfinite values or failed checks reject the certificate.
The table uses exact rational sums of the upward-printed per-length bounds and the upward-printed remainder, followed by decimal ceilings.
The programs must be compiled with \texttt{-frounding-math}, without unsafe reassociation; the archived rerun also used \texttt{-ffp-contract=off}.
Correct directed arithmetic, conversions and decimal output, and gradual underflow, are part of the computational trust assumption.
The explicit support and finiteness guards are implemented in \texttt{tailmem4\_checked.c} and \texttt{tailmem5\_checked.c}, archived under \texttt{reports/ADJ-R5/audit/} relative to the project root; the production records identified above were generated by the original sources. Their zero-support condition follows from the indegree argument above.
```

`app-tail.tex` — frozen lines 125; final lines 176.

Before:

```latex
\emph{What must be trusted.} A reader who accepts the lemmas of this appendix has to trust that \texttt{tailmem4.c} and \texttt{tailmem5.c} (about $360$ lines of C each) implement the walk of \S\ref{s:memwalk}, the exact enumeration and the check of Lemma~\ref{l:remainder}, and that the floating-point environment implements IEEE~754 arithmetic with directed rounding. The checks (1)--(3) test the first point independently; they are not themselves rigorous.
```

After:

```latex
\emph{What must be trusted.} A reader who accepts the lemmas of this appendix has to trust that the implementations and explicit checks identified above implement the walk of \S\ref{s:memwalk}, the exact enumeration and the support-aware check of Lemma~\ref{l:remainder}, and that the floating-point environment implements IEEE~754 arithmetic with directed rounding. The checks (1)--(3) test the first point independently; they are not themselves rigorous.
```

`app-tail.tex` — frozen lines 128; final lines 179–187.

Before:

```latex
With the type-dependent coefficients of Remark~\ref{r:typedep} in place of $\bar\alpha, \bar\beta$ (and the coefficient $\beta'$ of the surviving pair when exactly one of $f, g$ is known to be removed), a variant of the same programs (\texttt{tailmem6.c}) with $h_C = 1.20$ gives $(M_1 h)_B \le 0.91301$ and $(M_1 h)_C / h_C \le 0.91825$, hence $\rho(M_1) \le 0.91825$. The six coefficient bounds of Remark~\ref{r:typedep} were confirmed by an independent interval branch and bound, and the exact part $n \le 20$ of this computation by the independent enumeration; the memory-walk part was not recomputed. This variant is not used in the main line.
```

After:

```latex
With the type-dependent coefficients of Remark~\ref{r:typedep} in place of $\bar\alpha, \bar\beta$ (and the coefficient $\beta'$ of the surviving pair when exactly one of $f, g$ is known to be removed), a variant of the same programs (\texttt{tailmem6.c}) with $h_C = 1.20$ gives $(M_1 h)_B \le 0.91301$ and $(M_1 h)_C / h_C \le 0.91825$, hence $\rho(M_1) \le 0.91825$. The six coefficient bounds of Remark~\ref{r:typedep} were confirmed by an independent interval branch and bound, and the exact part $n \le 20$ of this computation by the independent enumeration; the memory-walk part was not recomputed. The seven production records for this variant are
\texttt{c961\_935\_A\_B\_1.txt}, \texttt{c961\_935\_A\_B\_2.txt},
\texttt{c961\_935\_A\_C\_1.txt}, \texttt{c961\_935\_A\_C\_2.txt},
\texttt{c961\_935\_A\_C\_3.txt}, \texttt{c961\_935\_B\_B.txt},
\texttt{c961\_\allowbreak 935\_\allowbreak B\_\allowbreak C.txt} in \texttt{agents/\allowbreak 62-kernel-tail/\allowbreak out/}.
Their exact assembly, using the binary64 value of $1.20$, gives row bounds
$0.913009554182608$ and a quotient less than $0.918245584$.
The unsplit implementation uses the additional start-site deletion described in \S\ref{s:tailtrust}, justified by the same degree argument, and the remainder uses the nonnegative-vector formulation of Lemma~\ref{l:remainder}.
This variant is not used in the main line.
```

## R5-2 — Tail archive and exact assembly

kind: correction

Adjudication: `ADJ-R5` — CONFIRMED-MODIFIED.

Counterexample or reason: The frozen bundle omits production records that do exist in the full archive. Identify the seven corrected logs, commands, exact assembler, and exact dyadic denominator. Exact assembly retains Table C.1; the old B upper bound must be 0.987731 and the outward new/old ratio interval must end at 1.0000333.

Changed locations: [app-tail.tex](/home/ubuntu/aklt/manuscript-corrected/app-tail.tex:128): 128–149, 151–164, 166–174, 176, 179–187; [sec8-computer-assisted.tex](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:3): 3.

`app-tail.tex` — frozen lines 119; final lines 128–149.

Before:

```latex
\emph{Programs.} \texttt{tailmem5.c} computes, for one row and one class $D_0$, the exact sums $\mathsf m(\mathcal T^{X, D_0}_n)$, $n \le 20$, by depth-first search with the per-trail optimal ordering, the initial vector (I), and the memory walk of mode A up to $t = 109$, printing $r^{\mathrm A}_{X, D_0}(n)$ for every $n$. \texttt{tailmem4.c} does the same without the class split for mode B up to $T = 260$, computes $z$ by power iteration, checks $z \mathbb W \le \lambda z$, and prints $a$, $\lambda$ and the bound of Lemma~\ref{l:remainder}. The table is assembled by summing the printed per-$n$ values. The state space of the walk has $60{,}092 \times 1{,}568 \times 4 \approx 3.8 \cdot 10^8$ entries (three gigabytes in single precision); each of the five mode-A runs takes about five minutes and each of the two mode-B runs about twenty minutes on one core.
```

After:

```latex
\emph{Programs.} \texttt{tailmem5.c} computes, for one row and one class $D_0$, the exact sums $\mathsf m(\mathcal T^{X, D_0}_n)$, $n \le 20$, by depth-first search with the per-trail optimal ordering, the initial vector (I), and the memory walk of mode A up to $t = 109$, printing $r^{\mathrm A}_{X, D_0}(n)$ for every $n$. \texttt{tailmem4.c} does the same without the class split for mode B up to $T = 260$, computes $z$ by power iteration, checks $z \mathbb W \le \lambda z$, and prints $a$, $\lambda$ and the bound of Lemma~\ref{l:remainder}.
The archived mode-A summary through $109$ is a memory-walk mass, and includes the unproved-for-trails value at $108$; only its per-length outputs through $106$ are used in Table~\ref{tab:tail}.
The unsplit mode-B production runs use \texttt{tailmem4.c}.
The archived unused unsplit option of \texttt{tailmem5.c} additionally deletes a window-detected revisit at $[u]$ while the rules act, whereas (R1) with $D_0=\ast$ retains it with weight $1/5$.
This additional deletion cannot remove a genuine trail in the valid range: the known time-$0$ visit, a window-detected later visit, and another departure would exceed the three available bonds at $u$.
It defines a stronger auxiliary rule and is not used for the mode-B entries of the table.
The obsolete validity comments and summary labels in the archived sources must not be used in place of Lemma~\ref{l:memdom}. The table is assembled from the five files
\texttt{r961A\_B\_1.txt}, \texttt{r961A\_B\_2.txt},
\texttt{r961A\_C\_1.txt}, \texttt{r961A\_C\_2.txt},
\texttt{r961A\_C\_3.txt} and the two files
\texttt{r961B\_B.txt}, \texttt{r961B\_C.txt}, archived in
\texttt{agents/75-audit-tail/out/rerun/} in the full project.
The commands are recorded in \texttt{agents/75-audit-tail/code/run\_all.sh}
and \texttt{run\_rest1.sh}, \texttt{run\_rest2.sh}; the rerun used
\texttt{gcc -O2 -frounding-math -ffp-contract=off}.
The exact assembly is implemented in \texttt{agents/75-audit-tail/code/assemble75.py}:
sum the printed decimals as rational numbers, using the class multiplicities in the caption,
the mode-A values for $22\le n\le106$, the mode-B values for $108\le n\le260$,
and the printed mode-B remainder, without subtracting any rounded tail totals.
The denominator is the exact binary64 number $h_C=2769713770832855/2251799813685248$.
The assembled numerators are $0.987762443170525$ and $1.1914067844431$;
their quotients are at most $0.987763$ and $0.968624$. The state space of the walk has $60{,}092 \times 1{,}568 \times 4 \approx 3.8 \cdot 10^8$ entries (three gigabytes in single precision); each of the five mode-A runs takes about five minutes and each of the two mode-B runs about twenty minutes on one core.
```

`app-tail.tex` — frozen lines 121; final lines 151–164.

Before:

```latex
\emph{Arithmetic.} All quantities are sums of products of nonnegative numbers, and no subtraction occurs. The programs set the rounding mode upward before any computation; the constants $\cs, \ct$ are decreased and $\bar\alpha, \bar\beta$ increased by one unit in the last place after decimal conversion, and $1/3$, $1/5$, $1/\cs$, $1/\ct$ are computed by upward division. The walk is stored in binary32 and the enumeration in binary64; every product, sum and conversion is rounded upward, so every stored value is at least the exact one, and underflow produces a positive subnormal number, never $0$. In the check of $z \mathbb W \le \lambda z$ the left side is rounded upward and the right side downward, and $1 - \lambda$ is rounded downward. The output decimals are rounded upward as well (the C library rounds conversions in the current rounding mode), and the table sums them exactly as rational numbers. The programs must be compiled with \texttt{-frounding-math}: the compiler ignores the \texttt{FENV\_ACCESS} pragma, and without this option it may evaluate or move floating-point operations across the changes of the rounding mode. The hypothesis $\lambda < 1$ of Lemma~\ref{l:remainder} is not checked by the program and must be read off its output.
```

After:

```latex
\emph{Arithmetic.}
The enumeration and walk bounds are evaluated as sums of products of nonnegative quantities.
The constants $\cs,\ct$ are decreased and $\bar\alpha,\bar\beta$ increased by one unit in the last place after decimal conversion;
$1/3$, $1/5$, $1/\cs$ and $1/\ct$ are computed by upward division.
The walk arrays are stored in binary32 and the enumeration in binary64.
Bound-producing products, sums and conversions, and their output decimals, are rounded upward, with gradual underflow.
The ordering search and the construction of a candidate $z$ need not use upward rounding: any chosen ordering gives an upper bound for the per-trail minimum, and the stored candidate is subsequently treated as an exact dyadic vector.
In checking $z\mathbb W\le\lambda z$, the left side is rounded upward and the right side downward; $1-\lambda$ is rounded downward in the remainder formula.
Acceptance requires finite nonnegative data, $0<\lambda<1$, the checked sub-invariance inequality, and $V_T=0$ wherever $z=0$.
Ratios defining $a$ are taken only at positive coordinates of $z$, with upward rounding; nonfinite values or failed checks reject the certificate.
The table uses exact rational sums of the upward-printed per-length bounds and the upward-printed remainder, followed by decimal ceilings.
The programs must be compiled with \texttt{-frounding-math}, without unsafe reassociation; the archived rerun also used \texttt{-ffp-contract=off}.
Correct directed arithmetic, conversions and decimal output, and gradual underflow, are part of the computational trust assumption.
The explicit support and finiteness guards are implemented in \texttt{tailmem4\_checked.c} and \texttt{tailmem5\_checked.c}, archived under \texttt{reports/ADJ-R5/audit/} relative to the project root; the production records identified above were generated by the original sources. Their zero-support condition follows from the indegree argument above.
```

`app-tail.tex` — frozen lines 123; final lines 166–174.

Before:

```latex
\emph{Independent checks.} (1) An independent enumeration from the definition \eqref{e:kernel} reproduces, for every $n \le 20$ and every class, the exact sums used in the table to a relative error of $7 \cdot 10^{-13}$; it also reproduces, for every $n \le 22$, the kernel with the forward ordering computed by a third, symbolic enumeration (to $4 \cdot 10^{-10}$, the precision of its output), and for $n \le 16$ the trail counts and masses of a fourth implementation. (2) An independent implementation of the memory walk of \S\ref{s:memwalk}, run at memory $m = 4$ and $m = 6$ on the quotient by $\langle (9, 9), (9, -9) \rangle$, reproduces the output of \texttt{tailmem5.c} at the same parameters to a relative error of $10^{-5}$ for every $n$, both rows, all classes and both modes. (3) The exact sums $\mathsf m(\mathcal T^{X, D_0}_n)$ with the straights-first ordering were enumerated up to $n = 26$; they are dominated by the memory walk at every $n$ and in every class, for $m = 4, 6$ and for $m = 10$. At $m = 10$ the ratio of the bound to the exact sum lies, in the five classes, between $1.03$ and $1.21$ at $n = 22$ and between $1.19$ and $1.81$ at $n = 26$; for the rows it is $1.05$ ($B$) and $1.08$ ($C$) at $n = 22$. (4) The numbers of Table~\ref{tab:tail} come from a recomputation from the source, compiled as above, with the coefficients $\bar\alpha = 0.18094$, $\bar\beta = 0.36751$ entered directly. An earlier run with the truncated values $0.18093$, $0.36750$ gave $0.987730$ and $0.968592$; every per-$n$ output of the two runs differs by a factor in $[1.0000322, 1.0000332]$. Since every term of \eqref{e:mT} carries exactly one of the coefficients, linearly and with a nonnegative weight, and the orderings may be kept, the earlier run alone also gives $\rho(M_1) \le 0.987730 \cdot 0.18094/0.18093 < 0.98779$.
```

After:

```latex
\emph{Independent checks.} (1) An independent enumeration from the definition \eqref{e:kernel} reproduces, for every $n \le 20$ and every class, the exact sums used in the table to a relative error of $7 \cdot 10^{-13}$; it also reproduces, for every $n \le 22$, the kernel with the forward ordering computed by a third, symbolic enumeration (to $4 \cdot 10^{-10}$, the precision of its output), and for $n \le 16$ the trail counts and masses of a fourth implementation. (2) An independent implementation of the memory walk of \S\ref{s:memwalk}, run at memory $m = 4$ and $m = 6$ on the quotient by $\langle (9, 9), (9, -9) \rangle$, reproduces the output of \texttt{tailmem5.c} at the same parameters to a relative error of $10^{-5}$ for every $n$, both rows, all classes and both modes. (3) The exact sums $\mathsf m(\mathcal T^{X, D_0}_n)$ with the straights-first ordering were enumerated up to $n = 26$; they are dominated by the memory walk at every $n$ and in every class, for $m = 4, 6$ and for $m = 10$. At $m = 10$ the ratio of the bound to the exact sum lies, in the five classes, between $1.03$ and $1.21$ at $n = 22$ and between $1.19$ and $1.81$ at $n = 26$; for the rows it is $1.05$ ($B$) and $1.08$ ($C$) at $n = 22$. (4) The numbers of Table~\ref{tab:tail} come from the archived recomputation with
$\bar\alpha=0.18094$, $\bar\beta=0.36751$ entered directly, as identified above.
Exact assembly of the earlier outputs with $0.18093$, $0.36750$ gives the row bounds
$0.987731$ and $0.968592$.
Every printed per-$n$ output of the two runs differs by a factor in
$[1.0000322,1.0000333]$.
Since every term of \eqref{e:mT} carries exactly one response coefficient, linearly and with a nonnegative weight,
and the earlier orderings may be kept, the earlier run alone also gives
$\rho(M_1)\le0.987731\cdot0.18094/0.18093<0.98779$.
```

`app-tail.tex` — frozen lines 125; final lines 176.

Before:

```latex
\emph{What must be trusted.} A reader who accepts the lemmas of this appendix has to trust that \texttt{tailmem4.c} and \texttt{tailmem5.c} (about $360$ lines of C each) implement the walk of \S\ref{s:memwalk}, the exact enumeration and the check of Lemma~\ref{l:remainder}, and that the floating-point environment implements IEEE~754 arithmetic with directed rounding. The checks (1)--(3) test the first point independently; they are not themselves rigorous.
```

After:

```latex
\emph{What must be trusted.} A reader who accepts the lemmas of this appendix has to trust that the implementations and explicit checks identified above implement the walk of \S\ref{s:memwalk}, the exact enumeration and the support-aware check of Lemma~\ref{l:remainder}, and that the floating-point environment implements IEEE~754 arithmetic with directed rounding. The checks (1)--(3) test the first point independently; they are not themselves rigorous.
```

`app-tail.tex` — frozen lines 128; final lines 179–187.

Before:

```latex
With the type-dependent coefficients of Remark~\ref{r:typedep} in place of $\bar\alpha, \bar\beta$ (and the coefficient $\beta'$ of the surviving pair when exactly one of $f, g$ is known to be removed), a variant of the same programs (\texttt{tailmem6.c}) with $h_C = 1.20$ gives $(M_1 h)_B \le 0.91301$ and $(M_1 h)_C / h_C \le 0.91825$, hence $\rho(M_1) \le 0.91825$. The six coefficient bounds of Remark~\ref{r:typedep} were confirmed by an independent interval branch and bound, and the exact part $n \le 20$ of this computation by the independent enumeration; the memory-walk part was not recomputed. This variant is not used in the main line.
```

After:

```latex
With the type-dependent coefficients of Remark~\ref{r:typedep} in place of $\bar\alpha, \bar\beta$ (and the coefficient $\beta'$ of the surviving pair when exactly one of $f, g$ is known to be removed), a variant of the same programs (\texttt{tailmem6.c}) with $h_C = 1.20$ gives $(M_1 h)_B \le 0.91301$ and $(M_1 h)_C / h_C \le 0.91825$, hence $\rho(M_1) \le 0.91825$. The six coefficient bounds of Remark~\ref{r:typedep} were confirmed by an independent interval branch and bound, and the exact part $n \le 20$ of this computation by the independent enumeration; the memory-walk part was not recomputed. The seven production records for this variant are
\texttt{c961\_935\_A\_B\_1.txt}, \texttt{c961\_935\_A\_B\_2.txt},
\texttt{c961\_935\_A\_C\_1.txt}, \texttt{c961\_935\_A\_C\_2.txt},
\texttt{c961\_935\_A\_C\_3.txt}, \texttt{c961\_935\_B\_B.txt},
\texttt{c961\_\allowbreak 935\_\allowbreak B\_\allowbreak C.txt} in \texttt{agents/\allowbreak 62-kernel-tail/\allowbreak out/}.
Their exact assembly, using the binary64 value of $1.20$, gives row bounds
$0.913009554182608$ and a quotient less than $0.918245584$.
The unsplit implementation uses the additional start-site deletion described in \S\ref{s:tailtrust}, justified by the same degree argument, and the remainder uses the nonnegative-vector formulation of Lemma~\ref{l:remainder}.
This variant is not used in the main line.
```

`sec8-computer-assisted.tex` — frozen lines 3; final lines 3.

Before:

```latex
In this section we state the three computer-assisted inputs of the proof and describe how they are verified. Hypothesis~(H1) is a statement about the $7{,}962$ functions \eqref{e:cpi} of the local patterns; we verify it in exact integer and rational arithmetic. The hypotheses (H2) and (H3$'$) concern only the two numbers $\cs, \ct$; they are statements about weighted sums over trails of $\Z^2$, and we verify them in floating-point arithmetic with upward rounding. The programs and their output files are kept with the project; we refer to them by file name.
```

After:

```latex
In this section we state the three computer-assisted inputs of the proof and describe how they are verified. Hypothesis~(H1) is a statement about the $7{,}962$ functions \eqref{e:cpi} of the local patterns; we verify it in exact integer and rational arithmetic. The hypotheses (H2) and (H3$'$) concern only the two numbers $\cs, \ct$; they are statements about weighted sums over trails of $\Z^2$, and we verify them in floating-point arithmetic with upward rounding. The programs and output files are kept with the project; the production records and exact rational assembly for (H3$'$) are identified in \S\ref{s:tailtrust} and are to be included with the accompanying programs.
```

## R5-3 — H2 integer initialization

kind: correction

Adjudication: `ADJ-R5` — CONFIRMED.

Counterexample or reason: The frozen alm8.c forms 4^i in signed int through i=23, overflowing at i=16 even for m=8. Describe the existing corrected audit implementation that validates the fixed instance and initializes powers only through eight, and locate its exact checker and vector.

Changed locations: [sec8-computer-assisted.tex](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:33): 33–45.

`sec8-computer-assisted.tex` — frozen lines 33; final lines 33–45.

Before:

```latex
\emph{Certificate.} The program \texttt{alm8.c} computes $\mathsf M_8$ for windows of length $m = 8$ ($7{, }500$ windows) at $(\cs, \ct) = (0.961, 0.935)$, with all weights given as exact integer quotients rounded upward, all sums and products evaluated in floating point with the rounding mode set upward, and the Collatz--Wielandt quotient for a power-iteration vector $h$ evaluated with upward rounding. Every computed number is therefore at least the exact one, and the output is $\max_\varsigma (\mathsf M_8 h)_\varsigma / h_\varsigma \le 0.85594872 \le 0.98075^8$, that is, $q \le 0.98075$. The bound was reproduced by an independent program in exact rational arithmetic: the windows are grouped into the $938$ classes of the dihedral group, which preserves $\mathsf M_8$, the test vector $h$ is rational, positive, constant on classes and has $\max h / \min h = 100$, and the exact value of $\max_\varsigma (\mathsf M_8 h)_\varsigma / h_\varsigma$ is at most $0.8559487104$. With the exact numbers $\mathsf W_n$, $n < 16$, the constant of Lemma~\ref{l:alm} is $C_V \le 153$. Replacing the window revisit weight $1/4$ by the true value $1/5$, which the proof of Lemma~\ref{l:alm} allows, gives $q \le 0.97606$.
```

After:

```latex
\emph{Certificate.}
For the certified instance, \texttt{alm8\_checked.c}, archived under \texttt{reports/ADJ-R5/audit/} relative to the project root, first validates $m=k=8$ and the integer parameters $9610,9350$, and initializes only the powers $4^i$ for $0\le i\le8$; all integer codes and array indices in this instance are within their checked ranges.
It computes $\mathsf M_8$ on the $7{,}500$ windows with weights given by exact integer quotients rounded upward.
The matrix sums and products and the final Collatz--Wielandt verification use upward rounding; the intervening power iteration only chooses a test vector. The final upward evaluation bounds
$\max_\varsigma(\mathsf M_8h)_\varsigma/h_\varsigma$ by $0.85594872$.
Its upper bound is printed with upward rounding, together with the exact hexadecimal representation of the stored binary64 bound.
The desired rate is certified by the exact rational comparison
$0.85594872<(3923/4000)^8$, giving $q\le0.98075$;
no printed value obtained by taking a numerical root is used as a certificate. The bound was reproduced by an independent program in exact rational arithmetic: the windows are grouped into the $938$ classes of the dihedral group, which preserves $\mathsf M_8$, the test vector $h$ is rational, positive, constant on classes and has $\max h / \min h = 100$, and the exact value of $\max_\varsigma (\mathsf M_8 h)_\varsigma / h_\varsigma$ is at most $0.8559487104$. The exact checker and vector are \texttt{h2\_exact.py} and \texttt{h2\_integer\_certificate.tsv} in the same audit directory. The base sums use the initial-step convention of \S\ref{s:H2def} and $\mathsf W_0=1$.
At the rational rate $q=0.98075$ they satisfy
$\max_{n<8}\mathsf W_nq^{-n}<1.473$ and
$\max_{8\le n<16}\mathsf W_nq^{-n}<1.506$.
Together with $\max h/\min h=100$ and $\mathsf M_8h\le q^8h$, the induction of Lemma~\ref{l:alm} therefore gives $C_V\le153$. Replacing the window revisit weight $1/4$ by the true value $1/5$, which the proof of Lemma~\ref{l:alm} allows, gives $q \le 0.97606$.
```

## R5-4 — H2 certified output

kind: correction

Adjudication: `ADJ-R5` — CONFIRMED.

Counterexample or reason: The nearest-rounded decimal 0.85594871 is smaller than the stored upper dyadic, and exp/log evaluation is not a certified eighth root. Use upward decimal output and hexadecimal output, then the exact rational inequality 0.85594872<(3923/4000)^8.

Changed locations: [sec8-computer-assisted.tex](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:33): 33–45.

`sec8-computer-assisted.tex` — frozen lines 33; final lines 33–45.

Before:

```latex
\emph{Certificate.} The program \texttt{alm8.c} computes $\mathsf M_8$ for windows of length $m = 8$ ($7{, }500$ windows) at $(\cs, \ct) = (0.961, 0.935)$, with all weights given as exact integer quotients rounded upward, all sums and products evaluated in floating point with the rounding mode set upward, and the Collatz--Wielandt quotient for a power-iteration vector $h$ evaluated with upward rounding. Every computed number is therefore at least the exact one, and the output is $\max_\varsigma (\mathsf M_8 h)_\varsigma / h_\varsigma \le 0.85594872 \le 0.98075^8$, that is, $q \le 0.98075$. The bound was reproduced by an independent program in exact rational arithmetic: the windows are grouped into the $938$ classes of the dihedral group, which preserves $\mathsf M_8$, the test vector $h$ is rational, positive, constant on classes and has $\max h / \min h = 100$, and the exact value of $\max_\varsigma (\mathsf M_8 h)_\varsigma / h_\varsigma$ is at most $0.8559487104$. With the exact numbers $\mathsf W_n$, $n < 16$, the constant of Lemma~\ref{l:alm} is $C_V \le 153$. Replacing the window revisit weight $1/4$ by the true value $1/5$, which the proof of Lemma~\ref{l:alm} allows, gives $q \le 0.97606$.
```

After:

```latex
\emph{Certificate.}
For the certified instance, \texttt{alm8\_checked.c}, archived under \texttt{reports/ADJ-R5/audit/} relative to the project root, first validates $m=k=8$ and the integer parameters $9610,9350$, and initializes only the powers $4^i$ for $0\le i\le8$; all integer codes and array indices in this instance are within their checked ranges.
It computes $\mathsf M_8$ on the $7{,}500$ windows with weights given by exact integer quotients rounded upward.
The matrix sums and products and the final Collatz--Wielandt verification use upward rounding; the intervening power iteration only chooses a test vector. The final upward evaluation bounds
$\max_\varsigma(\mathsf M_8h)_\varsigma/h_\varsigma$ by $0.85594872$.
Its upper bound is printed with upward rounding, together with the exact hexadecimal representation of the stored binary64 bound.
The desired rate is certified by the exact rational comparison
$0.85594872<(3923/4000)^8$, giving $q\le0.98075$;
no printed value obtained by taking a numerical root is used as a certificate. The bound was reproduced by an independent program in exact rational arithmetic: the windows are grouped into the $938$ classes of the dihedral group, which preserves $\mathsf M_8$, the test vector $h$ is rational, positive, constant on classes and has $\max h / \min h = 100$, and the exact value of $\max_\varsigma (\mathsf M_8 h)_\varsigma / h_\varsigma$ is at most $0.8559487104$. The exact checker and vector are \texttt{h2\_exact.py} and \texttt{h2\_integer\_certificate.tsv} in the same audit directory. The base sums use the initial-step convention of \S\ref{s:H2def} and $\mathsf W_0=1$.
At the rational rate $q=0.98075$ they satisfy
$\max_{n<8}\mathsf W_nq^{-n}<1.473$ and
$\max_{8\le n<16}\mathsf W_nq^{-n}<1.506$.
Together with $\max h/\min h=100$ and $\mathsf M_8h\le q^8h$, the induction of Lemma~\ref{l:alm} therefore gives $C_V\le153$. Replacing the window revisit weight $1/4$ by the true value $1/5$, which the proof of Lemma~\ref{l:alm} allows, gives $q \le 0.97606$.
```

## R5-5 — Initial trail convention

kind: correction

Adjudication: `ADJ-R5` — CONFIRMED.

Counterexample or reason: With all four initial directions, the reproduced ratio-100 base-sum bound exceeds 201 and cannot give C_V<=153. Forbid only immediate initial reversal, designate an absent incoming bond in the one-point lemma, and state the restricted base sums that retain C_V<=153.

Changed locations: [sec6-walks.tex](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:227): 227–232, 235, 239–244, 254–276; [sec8-computer-assisted.tex](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:16): 16, 33–45.

`sec6-walks.tex` — frozen lines 135; final lines 227–232.

Before:

```latex
Let $x_{\mathrm s} = 1/\cs$ and $x_{\mathrm t} = 1/\ct$. For a trail $w = (v_0, \dots, v_m)$ of $\Z^2$ with a designated arrival direction at $v_0$, let $\mathsf W(w) = \prod_{j = 1}^m \omega_j$, where $\omega_j = 1/5$ if step $j$ leaves a site among $v_0, \dots, v_{j - 2}$ (a site left before), and $\omega_j = x_{\mathrm s}/3$ or $x_{\mathrm t}/3$ if it is a straight or turning first visit.
```

After:

```latex
Let $x_{\mathrm s}=1/\cs$ and $x_{\mathrm t}=1/\ct$.
For a trail $w=(v_0,\dots,v_m)$ of $\Z^2$ with a designated unit arrival direction $a$ at $v_0$, we require $v_1-v_0\ne-a$ when $m\ge1$.
The arrival direction is used to classify the first passage; its virtual incoming bond is not otherwise included among the bonds of $w$.
Let $\mathsf W(w)=\prod_{j=1}^m\omega_j$, with the empty product equal to $1$,
where $\omega_j=1/5$ if step $j$ leaves a site among $v_0,\dots,v_{j-2}$,
and otherwise $\omega_j=x_{\mathrm s}/3$ if $v_j-v_{j-1}$ equals the arrival direction ($a$ for $j=1$, $v_{j-1}-v_{j-2}$ for $j>1$), and $\omega_j=x_{\mathrm t}/3$ otherwise.
```

`sec6-walks.tex` — frozen lines 138; final lines 235.

Before:

```latex
There exist $C_V < \infty$ and $q < 1$ such that for all $n \ge 0$, all starting points and all arrival directions, $\sum_{|w| = n} \mathsf W(w) \le C_V q^n$, where the sum runs over the trails of $\Z^2$ of length $n$ with that start and arrival direction.
```

After:

```latex
There exist $C_V < \infty$ and $q < 1$ such that for all $n \ge 0$, all starting points and all arrival directions, $\sum_{|w| = n} \mathsf W(w) \le C_V q^n$, where the sum runs over the trails of $\Z^2$ of length $n$ with that start and arrival direction and with initial reversal forbidden as above.
```

`sec6-walks.tex` — frozen lines 142; final lines 239–244.

Before:

```latex
Assume (H1) and (H2). Let $D \in \Dcons(G)$ or $D = D_0;[w_0]$ for some $D_0 \in \Dcons(G)$ and a trail $w_0$, let $x \in G \setminus S$ be a site that is not removed and has at most three present bonds, with a designated arrival direction, and suppose that all first-visit steps of every trail in $\mathcal T_D(x, S)$, except at most $12$ steps of each trail, have their patterns in $\Pext$. Then
```

After:

```latex
Assume (H1) and (H2). Let $D$ be a domain or auxiliary spin network
on $G$, let $x\in G\setminus S$ be a site that is not removed and
has at most three present bonds, with a designated arrival direction $a$ such that the bond $\{x-a,x\}$ is absent in $D$,
and suppose that all first-visit steps of every trail in
$\mathcal T_D(x,S)$, except at most $12$ steps of each trail, have
their patterns in $\Pext$. Then
```

`sec6-walks.tex` — frozen lines 149; final lines 254–276.

Before:

```latex
Every trail of $D$ is a trail of $\Z^2$. A step that leaves a site visited before by $w$ is a revisit in $D;[w_{j - 1}]$, with $3^{-1} \rho^\tau_j = 1/5 = \omega_j$. A step that leaves a site of status $\mathrm D$ not visited before by $w$ has $3^{-1} \rho^\tau_j = 1/5 \le \omega_j$. A first-visit step with pattern $\pi \in \Pext$ has $\rho^\tau_j \le 1/c(\pi) \le x_{\mathrm{type}}$ by Lemma~\ref{l:local} and (H1), so $3^{-1} \rho^\tau_j \le \omega_j$. Any other first-visit step has $3^{-1} \rho^\tau_j \le 4/5 \le \frac{12}{5} \omega_j$ by Lemma~\ref{l:response}, since $\omega_j \ge 1/3$ for first visits. Hence $3^{-|w|} R^\tau_D(w) \le (12/5)^{12} \mathsf W(w)$, and since $|w| \ge d(x, S)$, (H2) gives the claim.
```

After:

```latex
Every trail of $D$ is a trail of $\Z^2$ with initial reversal forbidden for the designated arrival direction, since the bond $\{x-a,x\}$ is absent in $D$. We prove the same pointwise
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

`sec8-computer-assisted.tex` — frozen lines 16; final lines 16.

Before:

```latex
Let $\mathsf A_n(\varsigma)$ be the sum of $\mathsf W(w)$ over the trails $w$ of length $n \ge m$ with a fixed start and arrival direction whose last $m$ steps form $\varsigma$. Then $\mathsf A_{n + k}(\varsigma') \le \sum_\varsigma \mathsf A_n(\varsigma) \mathsf M_k(\varsigma, \varsigma')$. Consequently, let $h$ be any vector with positive entries and $\lambda = \max_\varsigma (\mathsf M_k h)_\varsigma / h_\varsigma$. Then, with $q = \lambda^{1/k}$ and $\mathsf W_n = \sum_{|w| = n} \mathsf W(w)$,
```

After:

```latex
Let $\mathsf A_n(\varsigma)$ be the sum of $\mathsf W(w)$ over the trails $w$ of length $n \ge m$ with a fixed start and arrival direction and with initial reversal forbidden as in \S\ref{s:H2def} whose last $m$ steps form $\varsigma$. Then $\mathsf A_{n + k}(\varsigma') \le \sum_\varsigma \mathsf A_n(\varsigma) \mathsf M_k(\varsigma, \varsigma')$. Consequently, let $h$ be any vector with positive entries and $\lambda = \max_\varsigma (\mathsf M_k h)_\varsigma / h_\varsigma$. Then, with $q = \lambda^{1/k}$ and $\mathsf W_n = \sum_{|w| = n} \mathsf W(w)$,
```

`sec8-computer-assisted.tex` — frozen lines 33; final lines 33–45.

Before:

```latex
\emph{Certificate.} The program \texttt{alm8.c} computes $\mathsf M_8$ for windows of length $m = 8$ ($7{, }500$ windows) at $(\cs, \ct) = (0.961, 0.935)$, with all weights given as exact integer quotients rounded upward, all sums and products evaluated in floating point with the rounding mode set upward, and the Collatz--Wielandt quotient for a power-iteration vector $h$ evaluated with upward rounding. Every computed number is therefore at least the exact one, and the output is $\max_\varsigma (\mathsf M_8 h)_\varsigma / h_\varsigma \le 0.85594872 \le 0.98075^8$, that is, $q \le 0.98075$. The bound was reproduced by an independent program in exact rational arithmetic: the windows are grouped into the $938$ classes of the dihedral group, which preserves $\mathsf M_8$, the test vector $h$ is rational, positive, constant on classes and has $\max h / \min h = 100$, and the exact value of $\max_\varsigma (\mathsf M_8 h)_\varsigma / h_\varsigma$ is at most $0.8559487104$. With the exact numbers $\mathsf W_n$, $n < 16$, the constant of Lemma~\ref{l:alm} is $C_V \le 153$. Replacing the window revisit weight $1/4$ by the true value $1/5$, which the proof of Lemma~\ref{l:alm} allows, gives $q \le 0.97606$.
```

After:

```latex
\emph{Certificate.}
For the certified instance, \texttt{alm8\_checked.c}, archived under \texttt{reports/ADJ-R5/audit/} relative to the project root, first validates $m=k=8$ and the integer parameters $9610,9350$, and initializes only the powers $4^i$ for $0\le i\le8$; all integer codes and array indices in this instance are within their checked ranges.
It computes $\mathsf M_8$ on the $7{,}500$ windows with weights given by exact integer quotients rounded upward.
The matrix sums and products and the final Collatz--Wielandt verification use upward rounding; the intervening power iteration only chooses a test vector. The final upward evaluation bounds
$\max_\varsigma(\mathsf M_8h)_\varsigma/h_\varsigma$ by $0.85594872$.
Its upper bound is printed with upward rounding, together with the exact hexadecimal representation of the stored binary64 bound.
The desired rate is certified by the exact rational comparison
$0.85594872<(3923/4000)^8$, giving $q\le0.98075$;
no printed value obtained by taking a numerical root is used as a certificate. The bound was reproduced by an independent program in exact rational arithmetic: the windows are grouped into the $938$ classes of the dihedral group, which preserves $\mathsf M_8$, the test vector $h$ is rational, positive, constant on classes and has $\max h / \min h = 100$, and the exact value of $\max_\varsigma (\mathsf M_8 h)_\varsigma / h_\varsigma$ is at most $0.8559487104$. The exact checker and vector are \texttt{h2\_exact.py} and \texttt{h2\_integer\_certificate.tsv} in the same audit directory. The base sums use the initial-step convention of \S\ref{s:H2def} and $\mathsf W_0=1$.
At the rational rate $q=0.98075$ they satisfy
$\max_{n<8}\mathsf W_nq^{-n}<1.473$ and
$\max_{8\le n<16}\mathsf W_nq^{-n}<1.506$.
Together with $\max h/\min h=100$ and $\mathsf M_8h\le q^8h$, the induction of Lemma~\ref{l:alm} therefore gives $C_V\le153$. Replacing the window revisit weight $1/4$ by the true value $1/5$, which the proof of Lemma~\ref{l:alm} allows, gives $q \le 0.97606$.
```

## R5-6 — Tail cutoff and unsplit implementation

kind: correction

Adjudication: `ADJ-R5` — CONFIRMED.

Counterexample or reason: A genuine length-108 trail can encounter a false quotient image, so archived mode-A summaries through 109 do not certify every included trail length. Use mode-A outputs only through 106 and mode B from 108. Document the unused stronger unsplit start deletion and the optional archived variant without reinterpreting their output.

Changed locations: [app-tail.tex](/home/ubuntu/aklt/manuscript-corrected/app-tail.tex:128): 128–149, 176, 179–187.

`app-tail.tex` — frozen lines 119; final lines 128–149.

Before:

```latex
\emph{Programs.} \texttt{tailmem5.c} computes, for one row and one class $D_0$, the exact sums $\mathsf m(\mathcal T^{X, D_0}_n)$, $n \le 20$, by depth-first search with the per-trail optimal ordering, the initial vector (I), and the memory walk of mode A up to $t = 109$, printing $r^{\mathrm A}_{X, D_0}(n)$ for every $n$. \texttt{tailmem4.c} does the same without the class split for mode B up to $T = 260$, computes $z$ by power iteration, checks $z \mathbb W \le \lambda z$, and prints $a$, $\lambda$ and the bound of Lemma~\ref{l:remainder}. The table is assembled by summing the printed per-$n$ values. The state space of the walk has $60{,}092 \times 1{,}568 \times 4 \approx 3.8 \cdot 10^8$ entries (three gigabytes in single precision); each of the five mode-A runs takes about five minutes and each of the two mode-B runs about twenty minutes on one core.
```

After:

```latex
\emph{Programs.} \texttt{tailmem5.c} computes, for one row and one class $D_0$, the exact sums $\mathsf m(\mathcal T^{X, D_0}_n)$, $n \le 20$, by depth-first search with the per-trail optimal ordering, the initial vector (I), and the memory walk of mode A up to $t = 109$, printing $r^{\mathrm A}_{X, D_0}(n)$ for every $n$. \texttt{tailmem4.c} does the same without the class split for mode B up to $T = 260$, computes $z$ by power iteration, checks $z \mathbb W \le \lambda z$, and prints $a$, $\lambda$ and the bound of Lemma~\ref{l:remainder}.
The archived mode-A summary through $109$ is a memory-walk mass, and includes the unproved-for-trails value at $108$; only its per-length outputs through $106$ are used in Table~\ref{tab:tail}.
The unsplit mode-B production runs use \texttt{tailmem4.c}.
The archived unused unsplit option of \texttt{tailmem5.c} additionally deletes a window-detected revisit at $[u]$ while the rules act, whereas (R1) with $D_0=\ast$ retains it with weight $1/5$.
This additional deletion cannot remove a genuine trail in the valid range: the known time-$0$ visit, a window-detected later visit, and another departure would exceed the three available bonds at $u$.
It defines a stronger auxiliary rule and is not used for the mode-B entries of the table.
The obsolete validity comments and summary labels in the archived sources must not be used in place of Lemma~\ref{l:memdom}. The table is assembled from the five files
\texttt{r961A\_B\_1.txt}, \texttt{r961A\_B\_2.txt},
\texttt{r961A\_C\_1.txt}, \texttt{r961A\_C\_2.txt},
\texttt{r961A\_C\_3.txt} and the two files
\texttt{r961B\_B.txt}, \texttt{r961B\_C.txt}, archived in
\texttt{agents/75-audit-tail/out/rerun/} in the full project.
The commands are recorded in \texttt{agents/75-audit-tail/code/run\_all.sh}
and \texttt{run\_rest1.sh}, \texttt{run\_rest2.sh}; the rerun used
\texttt{gcc -O2 -frounding-math -ffp-contract=off}.
The exact assembly is implemented in \texttt{agents/75-audit-tail/code/assemble75.py}:
sum the printed decimals as rational numbers, using the class multiplicities in the caption,
the mode-A values for $22\le n\le106$, the mode-B values for $108\le n\le260$,
and the printed mode-B remainder, without subtracting any rounded tail totals.
The denominator is the exact binary64 number $h_C=2769713770832855/2251799813685248$.
The assembled numerators are $0.987762443170525$ and $1.1914067844431$;
their quotients are at most $0.987763$ and $0.968624$. The state space of the walk has $60{,}092 \times 1{,}568 \times 4 \approx 3.8 \cdot 10^8$ entries (three gigabytes in single precision); each of the five mode-A runs takes about five minutes and each of the two mode-B runs about twenty minutes on one core.
```

`app-tail.tex` — frozen lines 125; final lines 176.

Before:

```latex
\emph{What must be trusted.} A reader who accepts the lemmas of this appendix has to trust that \texttt{tailmem4.c} and \texttt{tailmem5.c} (about $360$ lines of C each) implement the walk of \S\ref{s:memwalk}, the exact enumeration and the check of Lemma~\ref{l:remainder}, and that the floating-point environment implements IEEE~754 arithmetic with directed rounding. The checks (1)--(3) test the first point independently; they are not themselves rigorous.
```

After:

```latex
\emph{What must be trusted.} A reader who accepts the lemmas of this appendix has to trust that the implementations and explicit checks identified above implement the walk of \S\ref{s:memwalk}, the exact enumeration and the support-aware check of Lemma~\ref{l:remainder}, and that the floating-point environment implements IEEE~754 arithmetic with directed rounding. The checks (1)--(3) test the first point independently; they are not themselves rigorous.
```

`app-tail.tex` — frozen lines 128; final lines 179–187.

Before:

```latex
With the type-dependent coefficients of Remark~\ref{r:typedep} in place of $\bar\alpha, \bar\beta$ (and the coefficient $\beta'$ of the surviving pair when exactly one of $f, g$ is known to be removed), a variant of the same programs (\texttt{tailmem6.c}) with $h_C = 1.20$ gives $(M_1 h)_B \le 0.91301$ and $(M_1 h)_C / h_C \le 0.91825$, hence $\rho(M_1) \le 0.91825$. The six coefficient bounds of Remark~\ref{r:typedep} were confirmed by an independent interval branch and bound, and the exact part $n \le 20$ of this computation by the independent enumeration; the memory-walk part was not recomputed. This variant is not used in the main line.
```

After:

```latex
With the type-dependent coefficients of Remark~\ref{r:typedep} in place of $\bar\alpha, \bar\beta$ (and the coefficient $\beta'$ of the surviving pair when exactly one of $f, g$ is known to be removed), a variant of the same programs (\texttt{tailmem6.c}) with $h_C = 1.20$ gives $(M_1 h)_B \le 0.91301$ and $(M_1 h)_C / h_C \le 0.91825$, hence $\rho(M_1) \le 0.91825$. The six coefficient bounds of Remark~\ref{r:typedep} were confirmed by an independent interval branch and bound, and the exact part $n \le 20$ of this computation by the independent enumeration; the memory-walk part was not recomputed. The seven production records for this variant are
\texttt{c961\_935\_A\_B\_1.txt}, \texttt{c961\_935\_A\_B\_2.txt},
\texttt{c961\_935\_A\_C\_1.txt}, \texttt{c961\_935\_A\_C\_2.txt},
\texttt{c961\_935\_A\_C\_3.txt}, \texttt{c961\_935\_B\_B.txt},
\texttt{c961\_\allowbreak 935\_\allowbreak B\_\allowbreak C.txt} in \texttt{agents/\allowbreak 62-kernel-tail/\allowbreak out/}.
Their exact assembly, using the binary64 value of $1.20$, gives row bounds
$0.913009554182608$ and a quotient less than $0.918245584$.
The unsplit implementation uses the additional start-site deletion described in \S\ref{s:tailtrust}, justified by the same degree argument, and the remainder uses the nonnegative-vector formulation of Lemma~\ref{l:remainder}.
This variant is not used in the main line.
```

## R6-1 — Pattern restriction shared with R4

kind: correction

Adjudication: `ADJ-R6` — CONFIRMED.

Counterexample or reason: The broad U-kept-set reading permits a ratio 1040285/1131207<187/200. The full U and passage-site restrictions and filled corner slots already added for R4-5 exclude that counterexample and match all 7,962 records; do not duplicate the same restrictions.

Changed locations: [sec6-walks.tex](/home/ubuntu/aklt/manuscript-corrected/sec6-walks.tex:163): 163–191.

`sec6-walks.tex` — frozen lines 104–108; final lines 163–191.

Before:

```latex
A \emph{pattern} $\pi$ consists of an out-neighbour $o \in \{\mathsf e, \mathsf N, \mathsf W\}$ and statuses and kept bonds of the sites $\mathsf s, \mathsf e, \mathsf N, \mathsf W$ and of the corners, as in Definition~\ref{d:domain}, with $y$ of status $\mathrm U$, the bond $\{y, \mathsf s\}$ dropped, and $o$ not removed. For unit vectors $m = (m_\ell)$ on the slots, let $Z_{\mathrm{cur}}(\pi; m)$ be the integral over the spins of $\mathsf T(y)$ minus the removed sites, with the site measures of the statuses, of the product of the factors of the present bonds inside $\mathsf T(y)$ and of $1 + m_\ell \cdot n_z$ for every slot $\ell$ at $z$; the tips have status $\mathrm U$. Let $Z_{\mathrm{next}}(\pi; m)$ be the same integral after the step, that is, with the measure of $y$ replaced by $\lambda_{\mathrm D}$ and the bond $\{y, o\}$ dropped. Define
\begin{equation}\label{e:cpi}
c(\pi) = \inf_{m \in (\Sph)^{20}} \frac{Z_{\mathrm{cur}}(\pi; m)}{Z_{\mathrm{next}}(\pi; m)} .
\end{equation}
The class $\Pext$ consists of the patterns in which: $\mathsf s$ is removed or has status $\mathrm D$ keeping two of its three bonds other than $\{y, \mathsf s\}$; each of $\mathsf e, \mathsf N, \mathsf W$ has status $\mathrm U$, $\mathrm X$, or $\mathrm D$ keeping the bond to $y$ and one other bond; each corner has status $\mathrm U$, $\mathrm X$, or $\mathrm D$ keeping two of its four bonds; and condition (C) holds for the bonds between non-removed sites of $\mathsf T(y)$ other than the tips. (The statuses of the tips are not part of a pattern; a bond between a tip and its neighbour $z$ is present in $Z_{\mathrm{cur}}$ and $Z_{\mathrm{next}}$ if and only if $z$ is not removed and keeps it.) A pattern is straight or a turn according to $o$.
```

After:

```latex
A \emph{pattern} $\pi$ consists of an out-neighbor
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
\begin{equation}\label{e:cpi}
c(\pi) = \inf_{m \in (\Sph)^{20}} \frac{Z_{\mathrm{cur}}(\pi; m)}{Z_{\mathrm{next}}(\pi; m)} .
\end{equation}
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

## R6-2 — Reduced and unreduced dimensions

kind: correction

Adjudication: `ADJ-R6` — CONFIRMED.

Counterexample or reason: Pattern ID 113 has twelve unreduced vectors. The reduced representation always has at most eleven, and every representation actually selected in the two certificate files has at most eleven. Distinguish these claims.

Changed locations: [app-local.tex](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:282): 282.

`app-local.tex` — frozen lines 282; final lines 282.

Before:

```latex
\emph{Patterns.} The reflection $x_1 \mapsto -x_1$ maps $\Pext$ onto itself, preserves the type of a step, permutes the slots, and leaves $c(\pi)$ unchanged. The list of patterns is produced by a computer enumeration of the rules of Definition~\ref{d:pattern}, modulo this reflection (the turns are stored with $o = \mathsf e$) and modulo patterns that give the same functions $Z_{\mathrm{cur}}$ and $Z_{\mathrm{next}}$ up to a common positive factor (the factor of the sites without present bonds, Lemma~\ref{l:leaf}(1)). A second enumeration, written independently from Definition~\ref{d:pattern}, finds $106{,}101$ configurations that satisfy the rules and the same $7{,}962$ classes, $2{,}696$ straight and $5{,}266$ turns, class by class. In the representations of \S\ref{s:localred}, the number of vectors is $k \le 11$.
```

After:

```latex
\emph{Patterns.} The reflection $x_1 \mapsto -x_1$ maps $\Pext$ onto itself, preserves the type of a step, permutes the slots, and leaves $c(\pi)$ unchanged. The list of patterns is produced by a computer enumeration of the rules of Definition~\ref{d:pattern}, modulo this reflection (the turns are stored with $o = \mathsf e$) and modulo patterns that give the same functions $Z_{\mathrm{cur}}$ and $Z_{\mathrm{next}}$ up to a common positive factor (the factor of the sites without present bonds, Lemma~\ref{l:leaf}(1)). A second enumeration, written independently from Definition~\ref{d:pattern}, counts $106{,}101$ consistent site assignments before choosing an out-neighbor, distinguishing the choices of outside corner legs, and obtains the same $7{,}962$ classes, $2{,}696$ straight and $5{,}266$ turns, class by class. Its program and output are \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak code/\allowbreak enum\_\allowbreak pext.py} and \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak out/\allowbreak enum\_\allowbreak pext.txt}, relative to \texttt{agents/\allowbreak } in the full project archive. The additional validation files identified below are also in that archive and are absent from the frozen program bundle. The reduced representation of \S\ref{s:localred} always has $k \le 11$. The unreduced representation can have $k = 12$, but every representation selected in the two certificate files has $k \le 11$.
```

## R6-3 — Exact examples rather than global minima

kind: correction

Adjudication: `ADJ-R6` — CONFIRMED.

Counterexample or reason: Exact closed-form values for particular patterns do not certify global class minima. The archived H1 certificates assert only 961/1000 or 187/200. Replace global-ranking claims with selected examples while retaining their exact values, IDs, and the precise negative-control threshold convention.

Changed locations: [app-constants.tex](/home/ubuntu/aklt/manuscript-corrected/app-constants.tex:17): 17; [app-local.tex](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:196): 196, 270, 272–273, 295–296; [sec1-intro-statement.tex](/home/ubuntu/aklt/manuscript-corrected/sec1-intro-statement.tex:18): 18; [sec8-computer-assisted.tex](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:78): 78–79, 85, 89.

`app-constants.tex` — frozen lines 17; final lines 17.

Before:

```latex
$\min_\pi c(\pi)$ & $0.961240\ldots$, $0.935565\ldots$ & straight, turn; closed forms (\S\ref{s:closed}) \\
```

After:

```latex
$c(\pi)$ for two decoupled examples & $3825127/3979368$, $1071655/1145463$ & straight and turn examples; closed forms (Proposition~\ref{p:closed}, \S\ref{s:closed}) \\
```

`app-local.tex` — frozen lines 196; final lines 196.

Before:

```latex
For many patterns, every site other than $y$ and its neighbours hangs on the rest by a single bond, possibly through a chain of such sites. For these patterns the infimum $c(\pi)$ has a closed form, which gives a second proof of Theorem~\ref{t:H1} on them, independent of \S\ref{s:inversion}, and the exact values of $c(\pi)$ for the tightest patterns. The main input is a sharp bound on the mean of a spin under several fields. For $r = (r_1, r_2, r_3) \in [0, 1]^3$ let $s_1 = r_1 + r_2 + r_3$, $s_2 = r_1 r_2 + r_1 r_3 + r_2 r_3$, $s_3 = r_1 r_2 r_3$, and
```

After:

```latex
For many patterns, every site other than $y$ and its neighbours hangs on the rest by a single bond, possibly through a chain of such sites. For these patterns the infimum $c(\pi)$ has a closed form, which gives a second proof of Theorem~\ref{t:H1} on them, independent of \S\ref{s:inversion}, and the exact values of $c(\pi)$ for the examples below. The main input is a sharp bound on the mean of a spin under several fields. For $r = (r_1, r_2, r_3) \in [0, 1]^3$ let $s_1 = r_1 + r_2 + r_3$, $s_2 = r_1 r_2 + r_1 r_3 + r_2 r_3$, $s_3 = r_1 r_2 r_3$, and
```

`app-local.tex` — frozen lines 270; final lines 270.

Before:

```latex
Of the $7{,}962$ patterns of $\Pext$, $4{,}735$ are decoupled ($1{,}553$ straight and $3{,}182$ turns), among them the three tightest patterns of the class. For these three the minimum in \eqref{e:closed} is rational, since $a = 0$ or the minimum is attained at $t = 1$, where the square root is $\rho_f + \rho_g$. The values are as follows; in each case the test of Proposition~\ref{p:closed}, in rational arithmetic, holds at the stated value of $c(\pi)$ and fails at that value plus $10^{-12}$.
```

After:

```latex
Of the $7{,}962$ patterns of $\Pext$, $4{,}735$ are decoupled ($1{,}553$ straight and $3{,}182$ turns), including the following three examples. For these three the minimum in \eqref{e:closed} is rational, since $a = 0$ or the minimum is attained at $t = 1$, where the square root is $\rho_f + \rho_g$. The values are as follows; in each case the test of Proposition~\ref{p:closed}, in rational arithmetic, holds at the stated value of $c(\pi)$ and fails at that value plus $10^{-12}$.
```

`app-local.tex` — frozen lines 272–273; final lines 272–273.

Before:

```latex
\item The tightest straight pattern: $\mathsf e$, $\mathsf N$ and the corner $(1, -1)$ have status $\mathrm U$; $\mathsf W$ has status $\mathrm D$ and keeps its bonds to $y$ and to its tip; $\mathsf s$ has status $\mathrm D$ and keeps its bonds to $(1, -1)$ and to its tip; the corner $(-1, 1)$ has status $\mathrm D$ and keeps its bond to $\mathsf N$; the corners $(1, 1)$ and $(-1, -1)$ are removed. Here $\rho_o = \rho_{\mathsf N} = 7/24$, $\rho_{\mathsf e} = 740/2193$, $\rho_{\mathsf W} = 3/25$, and $c(\pi) = 3825127/3979368 = 0.961240\ldots$
\item The tightest turn ($o = \mathsf e$): $\mathsf s$ is removed; $\mathsf N$ has status $\mathrm D$ and keeps its bonds to $y$ and to its tip; the corners $(1, 1)$ and $(-1, 1)$ have status $\mathrm D$ and keep their bonds to $\mathsf e$ and $\mathsf W$, respectively; all other sites have status $\mathrm U$. Here $\rho_{\mathsf e} = \rho_{\mathsf W} = 112/275$, $\rho_{\mathsf N} = 3/25$, and $c(\pi) = 1071655/1145463 = 0.935565\ldots$
```

After:

```latex
\item The straight example in the first row of Table~\ref{tab:H1}: $\mathsf e$, $\mathsf N$ and the corner $(1, -1)$ have status $\mathrm U$; $\mathsf W$ has status $\mathrm D$ and keeps its bonds to $y$ and to its tip; $\mathsf s$ has status $\mathrm D$ and keeps its bonds to $(1, -1)$ and to its tip; the corner $(-1, 1)$ has status $\mathrm D$ and keeps its bond to $\mathsf N$; the corners $(1, 1)$ and $(-1, -1)$ are removed. Here $\rho_o = \rho_{\mathsf N} = 7/24$, $\rho_{\mathsf e} = 740/2193$, $\rho_{\mathsf W} = 3/25$, and $c(\pi) = 3825127/3979368 = 0.961240\ldots$
\item The turn example in the second row of Table~\ref{tab:H1} ($o = \mathsf e$): $\mathsf s$ is removed; $\mathsf N$ has status $\mathrm D$ and keeps its bonds to $y$ and to its tip; the corners $(1, 1)$ and $(-1, 1)$ have status $\mathrm D$ and keep their bonds to $\mathsf e$ and $\mathsf W$, respectively; all other sites have status $\mathrm U$. Here $\rho_{\mathsf e} = \rho_{\mathsf W} = 112/275$, $\rho_{\mathsf N} = 3/25$, and $c(\pi) = 1071655/1145463 = 0.935565\ldots$
```

`app-local.tex` — frozen lines 296; final lines 295–296.

Before:

```latex
\item The stored certificates of the tightest patterns are rejected when the threshold is raised $2 \cdot 10^{-5}$ above the numerical minimum of the ratio.
```

After:

```latex
\item On the decoupled patterns, the floating-point value of $c$ at which the inversion test fails exceeds the closed form \eqref{e:closed} by at most $2.5 \cdot 10^{-15}$, and the two agree to $10^{-7}$ on $4{,}250$ of the $4{,}735$ patterns.
\item The stored certificates of the numerically selected patterns are rejected at thresholds obtained by adding $2\cdot10^{-5}$ to the numerical minimum and rounding upward to a multiple of $10^{-5}$; see \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak code/\linebreak[1]negctl.py} and \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak out/\allowbreak negctl\_\allowbreak hard.json}.
```

`sec1-intro-statement.tex` — frozen lines 18; final lines 18.

Before:

```latex
The proof of Theorem~\ref{t:main} is computer-assisted. Three statements are verified by computer, all at the pair of constants $(\cs, \ct) = (0.961, 0.935)$ (Theorem~\ref{t:inputs}). Hypothesis~(H1) is a list of $7{,}962$ inequalities, one for each local configuration (``pattern'') in an explicit class $\Pext$ of radius-$2$ neighbourhoods of the square lattice. Each inequality asserts that a ratio of two functions of at most twenty unit vectors in $\R^3$, affine in each vector, is at least $\cs$ or $\ct$ on the whole product of spheres. We verify it in exact integer and rational arithmetic, with tests of positive definiteness of integer matrices for each pattern, one for each exchange-symmetry sector of the pattern (\S\ref{s:H1} and Appendix~\ref{s:local}); the smallest margins are $2.4 \cdot 10^{-4}$ and $5.6 \cdot 10^{-4}$. Hypothesis~(H2), a bound on the growth of weighted trail sums, and Hypothesis~(H3$'$), a bound on the spectral radius of a $2 \times 2$ kernel built from closed trails, are verified in floating-point arithmetic with upward rounding (\S\ref{s:H2}, \S\ref{s:H3} and Appendix~\ref{s:tail}); the bound for (H2) was also reproduced in exact rational arithmetic. These two hypotheses use (H1) only through the two numbers $\cs$ and $\ct$. Everything else is proved here or cited with a precise locator. One cited result, \cite[Theorem~4.1]{MO94} as it is invoked in \cite{MOS94}, is applied to a finite single-spin space larger than the two-valued one for which its proof is written out; Remark~\ref{r:finiteS} explains why the proof applies. The constants $c$ and $L_0$ are not explicit.
```

After:

```latex
The proof of Theorem~\ref{t:main} is computer-assisted. Three statements are verified by computer, all at the pair of constants $(\cs, \ct) = (0.961, 0.935)$ (Theorem~\ref{t:inputs}). Hypothesis~(H1) is a list of $7{,}962$ inequalities, one for each local configuration (``pattern'') in an explicit class $\Pext$ of radius-$2$ neighbourhoods of the square lattice. Each inequality asserts that a ratio of two functions of at most twenty unit vectors in $\R^3$, affine in each vector, is at least $\cs$ or $\ct$ on the whole product of spheres. We verify it in exact integer and rational arithmetic, with tests of positive definiteness of integer matrices for each pattern, one for each exchange-symmetry sector of the pattern (\S\ref{s:H1} and Appendix~\ref{s:local}); the margins on the first two decoupled examples of Table~\ref{tab:H1} are $2.4 \cdot 10^{-4}$ and $5.6 \cdot 10^{-4}$. Hypothesis~(H2), a bound on the growth of weighted trail sums, and Hypothesis~(H3$'$), a bound on the spectral radius of a $2 \times 2$ kernel built from closed trails, are verified in floating-point arithmetic with upward rounding (\S\ref{s:H2}, \S\ref{s:H3} and Appendix~\ref{s:tail}); the bound for (H2) was also reproduced in exact rational arithmetic. These two hypotheses use (H1) only through the two numbers $\cs$ and $\ct$. Everything else is proved here or cited with a precise locator. One cited result, \cite[Theorem~4.1]{MO94} as it is invoked in \cite{MOS94}, is applied to a finite single-spin space larger than the two-valued one for which its proof is written out; Remark~\ref{r:finiteS} explains why the proof applies. The constants $c$ and $L_0$ are not explicit.
```

`sec8-computer-assisted.tex` — frozen lines 66–67; final lines 78–79.

Before:

```latex
tightest straight & $c(\pi) = 3825127/3979368 = 0.961240\ldots$ & $0.961240$ \\
tightest turn & $c(\pi) = 1071655/1145463 = 0.935565\ldots$ & $0.935565$ \\
```

After:

```latex
straight example (ID 7645) & $c(\pi) = 3825127/3979368 = 0.961240\ldots$ & $0.961240$ \\
turn example (ID 1382) & $c(\pi) = 1071655/1145463 = 0.935565\ldots$ & $0.935565$ \\
```

`sec8-computer-assisted.tex` — frozen lines 73; final lines 85.

Before:

```latex
\caption{The hardest patterns of $\Pext$, which has $2{,}696$ straight patterns and $5{,}266$ turns. The first three are decoupled, so their values are exact closed forms (\S\ref{s:closed}); in the third, all sites other than $\mathsf N$ and $\mathsf s$ have status $\mathrm U$. In the generic steps, every site of the template has status $\mathrm U$, except the arrival site $\mathsf s$, which has status $\mathrm D$ and keeps its bonds to the corners $(1, -1)$ and $(-1, -1)$; there $k$ is the number of vectors of Appendix~\ref{s:local}. The bound of an inversion certificate is the floating-point value of the supremum of the $c$ for which its integer matrices \eqref{e:Meps} are positive definite; it is not used in the proof, in which the exact test is made at $c = 961/1000$ or $187/200$. The largest of these matrices has size $245 \times 245$, and the certificates of all $7{,}962$ patterns were produced in about $34$ CPU-minutes.}\label{tab:H1}
```

After:

```latex
\caption{Selected patterns of $\Pext$, which has $2{,}696$ straight patterns and $5{,}266$ turns. The first two rows give the smallest values found numerically in the straight and turning classes; global optimality is not certified. The first three are decoupled, so their values are exact closed forms (\S\ref{s:closed}); in the third, all sites other than $\mathsf N$ and $\mathsf s$ have status $\mathrm U$. In the generic steps, every site of the template has status $\mathrm U$, except the arrival site $\mathsf s$, which has status $\mathrm D$ and keeps its bonds to the corners $(1, -1)$ and $(-1, -1)$; there $k$ is the number of vectors of Appendix~\ref{s:local}. The bound of an inversion certificate is the floating-point value of the supremum of the $c$ for which its integer matrices \eqref{e:Meps} are positive definite; it is not used in the proof, in which the exact test is made at $c = 961/1000$ or $187/200$. With the exchange signs split as in \eqref{e:Meps}, the largest tested matrix has size $179 \times 179$, and the certificates of all $7{,}962$ patterns were produced in about $34$ CPU-minutes.}\label{tab:H1}
```

`sec8-computer-assisted.tex` — frozen lines 77; final lines 89.

Before:

```latex
The constants of Theorem~\ref{t:H1} cannot be raised much with the present template. For the third pattern of Table~\ref{tab:H1}, $c(\pi) = 416114/444675 = 0.935771\ldots$ exactly, by \eqref{e:5469}, so (H1) fails for every $\ct > 416114/444675$ with the template and the slots of Definition~\ref{d:pattern}. The margins of Theorem~\ref{t:H1} on the two tightest patterns are $2.4 \cdot 10^{-4}$ and $5.6 \cdot 10^{-4}$. We also note that the method of \S\ref{s:H3} does not give $\rho(M_1) < 1$ at $(\cs, \ct) = (0.960, 0.925)$, so that the pair $(0.961, 0.935)$ leaves little room in either direction.
```

After:

```latex
The constants of Theorem~\ref{t:H1} cannot be raised much with the present template. For the third pattern of Table~\ref{tab:H1}, $c(\pi) = 416114/444675 = 0.935771\ldots$ exactly, by \eqref{e:5469}, so (H1) fails for every $\ct > 416114/444675$ with the template and the slots of Definition~\ref{d:pattern}. The margins of Theorem~\ref{t:H1} on the first two decoupled examples of Table~\ref{tab:H1} are $2.4 \cdot 10^{-4}$ and $5.6 \cdot 10^{-4}$. We also note that the method of \S\ref{s:H3} does not give $\rho(M_1) < 1$ at $(\cs, \ct) = (0.960, 0.925)$, so that the pair $(0.961, 0.935)$ leaves little room in either direction.
```

## R6-4 — Validation provenance and precise claims

kind: correction

Adjudication: `ADJ-R6` — CONFIRMED-MODIFIED.

Counterexample or reason: The full archive supplies the disputed independent enumerator, ratio comparisons, spin checks, second implementation, and 600-case test. Identify their locations and actual scope; disclose that the 30-trial mutation output has no archived generating driver. Round the recorded 2.4424906541753444e-15 excess upward to 2.5e-15.

Changed locations: [app-local.tex](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:282): 282, 292–293, 295–296, 298, 300.

`app-local.tex` — frozen lines 282; final lines 282.

Before:

```latex
\emph{Patterns.} The reflection $x_1 \mapsto -x_1$ maps $\Pext$ onto itself, preserves the type of a step, permutes the slots, and leaves $c(\pi)$ unchanged. The list of patterns is produced by a computer enumeration of the rules of Definition~\ref{d:pattern}, modulo this reflection (the turns are stored with $o = \mathsf e$) and modulo patterns that give the same functions $Z_{\mathrm{cur}}$ and $Z_{\mathrm{next}}$ up to a common positive factor (the factor of the sites without present bonds, Lemma~\ref{l:leaf}(1)). A second enumeration, written independently from Definition~\ref{d:pattern}, finds $106{,}101$ configurations that satisfy the rules and the same $7{,}962$ classes, $2{,}696$ straight and $5{,}266$ turns, class by class. In the representations of \S\ref{s:localred}, the number of vectors is $k \le 11$.
```

After:

```latex
\emph{Patterns.} The reflection $x_1 \mapsto -x_1$ maps $\Pext$ onto itself, preserves the type of a step, permutes the slots, and leaves $c(\pi)$ unchanged. The list of patterns is produced by a computer enumeration of the rules of Definition~\ref{d:pattern}, modulo this reflection (the turns are stored with $o = \mathsf e$) and modulo patterns that give the same functions $Z_{\mathrm{cur}}$ and $Z_{\mathrm{next}}$ up to a common positive factor (the factor of the sites without present bonds, Lemma~\ref{l:leaf}(1)). A second enumeration, written independently from Definition~\ref{d:pattern}, counts $106{,}101$ consistent site assignments before choosing an out-neighbor, distinguishing the choices of outside corner legs, and obtains the same $7{,}962$ classes, $2{,}696$ straight and $5{,}266$ turns, class by class. Its program and output are \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak code/\allowbreak enum\_\allowbreak pext.py} and \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak out/\allowbreak enum\_\allowbreak pext.txt}, relative to \texttt{agents/\allowbreak } in the full project archive. The additional validation files identified below are also in that archive and are absent from the frozen program bundle. The reduced representation of \S\ref{s:localred} always has $k \le 11$. The unreduced representation can have $k = 12$, but every representation selected in the two certificate files has $k \le 11$.
```

`app-local.tex` — frozen lines 292–293; final lines 292–293.

Before:

```latex
\item An evaluator of $Z_{\mathrm{cur}}$ and $Z_{\mathrm{next}}$ written independently from Definition~\ref{d:pattern}, with all template sites kept as spins, agrees with the integer coefficients at three random points of every pattern, to a relative error of $2.3 \cdot 10^{-15}$.
\item For all $7{,}962$ certificates, the integer matrices commute exactly with the total spin operators, written in the basis of \S\ref{s:inversion}; the hypothesis of Lemma~\ref{l:sector} is thus verified as well as proved. A change of a single non-constant coefficient of $3 D \hat Z_{\mathrm{cur}}$ by $1$ was detected by these exact checks in $30$ of $30$ random trials.
```

After:

```latex
\item An independent evaluator keeps the passage site, tips, and corners as spins and compares the ratio $Z_{\mathrm{cur}}/Z_{\mathrm{next}}$ with the ratio obtained from the integer coefficients, at three random points with untied slot vectors for every pattern. There are $23{,}893$ comparisons, including seven additional zero-slot cases, and the largest observed relative discrepancy is less than $2.4\cdot10^{-15}$. The programs are \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak code/\allowbreak brute.py} and \texttt{xcheck\_\allowbreak brute.py} in the same directory; the output is \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak out/\allowbreak xcheck\_\allowbreak brute\_\allowbreak all.json}.
\item For all $7{,}962$ certificates, the integer matrices commute exactly with the total spin operators in the basis of \S\ref{s:inversion}; see \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak code/\allowbreak su2check.py} and \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak out/\allowbreak su2check\_\allowbreak all\_\allowbreak summary.json}. The archived output \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak out/\allowbreak unitpert.txt} records detection of a change by $1$ to a single non-constant coefficient of $3D\hat Z_{\mathrm{cur}}$ in all $30$ trials; its generating driver is not archived.
```

`app-local.tex` — frozen lines 295–296; final lines 295–296.

Before:

```latex
\item On the decoupled patterns, the floating-point value of $c$ at which the inversion test fails exceeds the closed form \eqref{e:closed} by at most $2.4 \cdot 10^{-15}$, and the two agree to $10^{-7}$ on $4{,}250$ of the $4{,}735$ patterns.
\item The stored certificates of the tightest patterns are rejected when the threshold is raised $2 \cdot 10^{-5}$ above the numerical minimum of the ratio.
```

After:

```latex
\item On the decoupled patterns, the floating-point value of $c$ at which the inversion test fails exceeds the closed form \eqref{e:closed} by at most $2.5 \cdot 10^{-15}$, and the two agree to $10^{-7}$ on $4{,}250$ of the $4{,}735$ patterns.
\item The stored certificates of the numerically selected patterns are rejected at thresholds obtained by adding $2\cdot10^{-5}$ to the numerical minimum and rounding upward to a multiple of $10^{-5}$; see \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak code/\linebreak[1]negctl.py} and \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak out/\allowbreak negctl\_\allowbreak hard.json}.
```

`app-local.tex` — frozen lines 298; final lines 298.

Before:

```latex
A second implementation, written independently of the programs above, re-verifies the certificates of both files. It computes $Z_{\mathrm{cur}}$ and $Z_{\mathrm{next}}$ by exact symbolic integration over the sites of the patch, using the moment formulas of the uniform measure on $S^2$ in integer arithmetic; it assembles the operators from exchange operators; and it proves positivity by an exact integer congruence followed by a test of strict diagonal dominance. It confirms all $7{, }962$ certificates of the operator-only file, with the threshold of each pattern determined from the pattern itself, and without the reduction to one sector of Lemma~\ref{l:sector}: the operator is assembled on the whole space $(\C^2)^{\otimes n}$, it is checked exactly to have no entries between different values of the total $S^z$, and positivity is proved on every block. For the $4{, }992$ patterns without an unvisited corner with two slots the operator is positive definite on the whole space; for the other $2{, }970$ it annihilates the antisymmetric vectors of each such corner pair and is positive definite on their complement in every block, so it is positive semidefinite on the whole space. The same implementation confirms the $4{, }735$ closed-form certificates, with the same decoupled patterns and the same radii, and its numerical minimization over the full set of slot vectors reaches the closed-form minimum on each of these patterns to within $1.4 \cdot 10^{-8}$ and never goes below it.
```

After:

```latex
A second implementation, in \texttt{73-\allowbreak reimplement-\allowbreak H1/\allowbreak code/\linebreak[1]wick.py}, \texttt{opcert.py}, \texttt{run\_\allowbreak opall.py}, \texttt{closed.py}, \texttt{run\_\allowbreak k1.py}, \texttt{numeval.py}, and \texttt{run\_\allowbreak k1b.py} in the same directory, re-verifies the certificates of both files independently of the programs above. It computes $Z_{\mathrm{cur}}$ and $Z_{\mathrm{next}}$ by exact symbolic integration over the sites of the patch, using the moment formulas of the uniform measure on $S^2$ in integer arithmetic; it assembles the operators from exchange operators; and it proves positivity by an exact integer congruence followed by a test of strict diagonal dominance. It confirms all $7{, }962$ certificates of the operator-only file, with the threshold of each pattern determined from the pattern itself, and without the reduction to one sector of Lemma~\ref{l:sector}: the operator is assembled on the whole space $(\C^2)^{\otimes n}$, it is checked exactly to have no entries between different values of the total $S^z$, and positivity is proved on every block. For the $4{, }992$ patterns without an unvisited corner with two slots the operator is positive definite on the whole space; for the other $2{, }970$ it annihilates the antisymmetric vectors of each such corner pair and is positive definite on their complement in every block, so it is positive semidefinite on the whole space. The same implementation confirms the $4{, }735$ closed-form certificates, with the same decoupled patterns and the same radii, and its numerical minimization over the full set of slot vectors reaches the closed-form minimum on each of these patterns to within $1.4 \cdot 10^{-8}$ and never goes below it. The corresponding outputs are \texttt{operator\_\allowbreak only\_\allowbreak results.jsonl}, \texttt{k1\_\allowbreak exact.jsonl}, \texttt{k1b\_\allowbreak numerics.jsonl}, and \texttt{summary.txt} under \texttt{73-\allowbreak reimplement-\allowbreak H1/\allowbreak out/\allowbreak }.
```

`app-local.tex` — frozen lines 300; final lines 300.

Before:

```latex
\emph{What must be trusted.} A reader who accepts the lemmas of this appendix must trust that the list of patterns is $\Pext$ modulo the reflection and duplicates, which two independent enumerations confirm, and four pieces of code. The program \texttt{cert.py} must compute the coefficients of $3 D \hat Z_{\mathrm{cur}}$ and $5 D \hat Z_{\mathrm{next}}$ correctly (about $100$ lines, compared with the independent evaluator in check (1)), and it must assemble the matrices and their eigenspaces correctly (about $90$ lines, whose output satisfies the exact structural checks above). The fraction-free elimination (about $20$ lines) agrees with an exact $LDL^{\mathsf T}$ decomposition on $600$ random symmetric test matrices. For the second proof, \texttt{closed\_exact.py} (about $70$ lines) must implement Proposition~\ref{p:closed}. Finally, the reader must trust the integer and rational arithmetic of Python and the integer tensor contraction of numpy in the absence of overflow. Since overflow is excluded by run-time assertions, the checker must not be run with assertions disabled, and the tip radius, a parameter of the programs, must be left at its value $3/5$.
```

After:

```latex
\emph{What must be trusted.} A reader who accepts the lemmas of this appendix must trust that the list of patterns is $\Pext$ modulo the reflection and duplicates, which two independent enumerations confirm, and four pieces of code. The program \texttt{cert.py} must compute the coefficients of $3 D \hat Z_{\mathrm{cur}}$ and $5 D \hat Z_{\mathrm{next}}$ correctly (about $100$ lines, compared with the independent evaluator in check (1)), and it must assemble the matrices and their eigenspaces correctly (about $90$ lines, whose output satisfies the exact structural checks above). The fraction-free elimination (about $20$ lines) agrees with an exact $LDL^{\mathsf T}$ decomposition on $600$ random symmetric test matrices; the test is \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak code/\allowbreak test\_\allowbreak bareiss72.py}, and its result is recorded in \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak NOTES.md} and \texttt{LOG.md} in that directory. For the second proof, \texttt{closed\_exact.py} (about $70$ lines) must implement Proposition~\ref{p:closed}. Finally, the reader must trust the integer and rational arithmetic of Python and the integer tensor contraction of numpy in the absence of overflow. The binary64 error bounds above and the run-time assertions exclude overflow for accepted certificates; therefore the checker must not be run with assertions disabled, and the tip radius, a parameter of the programs, must be left at its value $3/5$.
```

## R6-5 — Floating shadow guards

kind: correction

Adjudication: `ADJ-R6` — CONFIRMED.

Counterexample or reason: Floating point is also used for tensor overflow guards and diagnostics. Explain the binary64 lower error factor eta and why passing nonnegative shadow checks bound all accepted integer contractions and coefficient sums below overflow; retain unbounded-integer positivity and exact rational closed tests.

Changed locations: [app-local.tex](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:284): 284, 286, 300.

`app-local.tex` — frozen lines 284; final lines 284.

Before:

```latex
\emph{Programs.} The program \texttt{cert.py} computes, for a pattern, a representation and an inversion set $\mathcal I$, the integer coefficients of $3 D \hat Z_{\mathrm{cur}}$ and $5 D \hat Z_{\mathrm{next}}$. It integrates out $y$ by Lemma~\ref{l:Iw} and contracts the remaining sites as the ring $\mathsf e, (1, 1), \mathsf N, (-1, 1), \mathsf W, (-1, -1), \mathsf s, (1, -1)$, with the exact moment tensors of the site measures. All tensors in this contraction have nonnegative integer entries. The contraction is carried out in $64$-bit integer arithmetic, with run-time assertions that every entry stays below $2^{61}$. The program then forms the matrices $A_\epsilon$, $A'_\epsilon$ of \S\ref{s:inversion}: it changes the signs of the coefficients according to $\mathcal I$, substitutes the Pauli matrices with real and imaginary parts kept separately, and passes to the basis of \S\ref{s:inversion} for the pairs, again with assertions on the magnitudes and with a fallback to unbounded integers. It checks exactly that the imaginary parts vanish, that the matrices are symmetric, that the antisymmetric vector of every pair of a corner of status $\mathrm U$ is annihilated from the left and from the right, and that no entry joins two basis vectors with different eigenvalues of $\Sigma_3$ or different exchange signs. Finally it tests $M_\epsilon$ on $V_\epsilon^{\circ}$, for every $\epsilon$, by fraction-free elimination in unbounded integers.
```

After:

```latex
\emph{Programs.} The program \texttt{cert.py} computes, for a pattern, a representation and an inversion set $\mathcal I$, the integer coefficients of $3 D \hat Z_{\mathrm{cur}}$ and $5 D \hat Z_{\mathrm{next}}$. It integrates out $y$ by Lemma~\ref{l:Iw} and contracts the remaining sites as the ring $\mathsf e, (1, 1), \mathsf N, (-1, 1), \mathsf W, (-1, -1), \mathsf s, (1, -1)$, with the exact moment tensors of the site measures. All tensors in this contraction have nonnegative integer entries. The contraction is carried out in $64$-bit integer arithmetic, with binary64 shadow computations used for conservative overflow guards. The small integer moment tensors are first stored exactly in binary64 arrays and then converted to integers. Assume binary64 round-to-nearest arithmetic, let $u=2^{-53}$, $\gamma_{32}=32u/(1-32u)$, and $\eta=(1-u)^2(1-\gamma_{32})>1-10^{-12}>3/4$. Each contracted entry is a sum of at most sixteen nonnegative products, so its shadow $\widehat s$ and exact value $s$ satisfy $\widehat s\ge\eta s$ (two input conversions and at most thirty-two arithmetic roundings suffice). Thus a passing shadow guard $\widehat s<2^{61}$ implies $s<2^{61}/\eta$, and a sum of three such contraction entries is smaller than $2^{63}$. The subsequent shadow bounds for the current and next coefficient sums are computed from these nonnegative integer arrays; their passing threshold $2^{58}$ implies exact sums smaller than $2^{58}/\eta<2^{59}$. Consequently every accepted coefficient computation is free of integer overflow, including its intermediate sums. The program then forms the matrices $A_\epsilon$, $A'_\epsilon$ of \S\ref{s:inversion}: it changes the signs of the coefficients according to $\mathcal I$, substitutes the Pauli matrices with real and imaginary parts kept separately, and passes to the basis of \S\ref{s:inversion} for the pairs, again with assertions on the magnitudes and with a fallback to unbounded integers. It checks exactly that the imaginary parts vanish, that the matrices are symmetric, that the antisymmetric vector of every pair of a corner of status $\mathrm U$ is annihilated from the left and from the right, and that no entry joins two basis vectors with different eigenvalues of $\Sigma_3$ or different exchange signs. Finally it tests $M_\epsilon$ on $V_\epsilon^{\circ}$, for every $\epsilon$, by fraction-free elimination in unbounded integers.
```

`app-local.tex` — frozen lines 286; final lines 286.

Before:

```latex
The program \texttt{closed\_exact.py} carries out the pruning of \S\ref{s:closed} and the test of Proposition~\ref{p:closed} in rational arithmetic. The program \texttt{run\_prod.py} chooses the representation and $\mathcal I$ for each pattern. It minimizes $\hat Z_{\mathrm{cur}} / \hat Z_{\mathrm{next}}$ numerically and lets $\mathcal I$ consist of the groups whose vectors have a negative total component along the principal axis of the minimizer, using floating-point eigenvalues to discard choices that cannot succeed. Floating-point arithmetic is used only for this choice. The program \texttt{verify\_all.py} re-derives every certificate of a file from the stored data alone, without any optimization.
```

After:

```latex
The program \texttt{closed\_exact.py} carries out the pruning of \S\ref{s:closed} and the test of Proposition~\ref{p:closed} in rational arithmetic. The program \texttt{run\_prod.py} chooses the representation and $\mathcal I$ for each pattern. It minimizes $\hat Z_{\mathrm{cur}} / \hat Z_{\mathrm{next}}$ numerically and lets $\mathcal I$ consist of the groups whose vectors have a negative total component along the principal axis of the minimizer, using floating-point eigenvalues to discard choices that cannot succeed. Floating-point arithmetic is used for this choice, for the conservative overflow guards just described, and for diagnostics. Positivity is decided in unbounded integer arithmetic, and the closed-form tests use exact rational arithmetic. The program \texttt{verify\_all.py} re-derives every certificate of a file from the stored data alone, without any optimization.
```

`app-local.tex` — frozen lines 300; final lines 300.

Before:

```latex
\emph{What must be trusted.} A reader who accepts the lemmas of this appendix must trust that the list of patterns is $\Pext$ modulo the reflection and duplicates, which two independent enumerations confirm, and four pieces of code. The program \texttt{cert.py} must compute the coefficients of $3 D \hat Z_{\mathrm{cur}}$ and $5 D \hat Z_{\mathrm{next}}$ correctly (about $100$ lines, compared with the independent evaluator in check (1)), and it must assemble the matrices and their eigenspaces correctly (about $90$ lines, whose output satisfies the exact structural checks above). The fraction-free elimination (about $20$ lines) agrees with an exact $LDL^{\mathsf T}$ decomposition on $600$ random symmetric test matrices. For the second proof, \texttt{closed\_exact.py} (about $70$ lines) must implement Proposition~\ref{p:closed}. Finally, the reader must trust the integer and rational arithmetic of Python and the integer tensor contraction of numpy in the absence of overflow. Since overflow is excluded by run-time assertions, the checker must not be run with assertions disabled, and the tip radius, a parameter of the programs, must be left at its value $3/5$.
```

After:

```latex
\emph{What must be trusted.} A reader who accepts the lemmas of this appendix must trust that the list of patterns is $\Pext$ modulo the reflection and duplicates, which two independent enumerations confirm, and four pieces of code. The program \texttt{cert.py} must compute the coefficients of $3 D \hat Z_{\mathrm{cur}}$ and $5 D \hat Z_{\mathrm{next}}$ correctly (about $100$ lines, compared with the independent evaluator in check (1)), and it must assemble the matrices and their eigenspaces correctly (about $90$ lines, whose output satisfies the exact structural checks above). The fraction-free elimination (about $20$ lines) agrees with an exact $LDL^{\mathsf T}$ decomposition on $600$ random symmetric test matrices; the test is \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak code/\allowbreak test\_\allowbreak bareiss72.py}, and its result is recorded in \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak NOTES.md} and \texttt{LOG.md} in that directory. For the second proof, \texttt{closed\_exact.py} (about $70$ lines) must implement Proposition~\ref{p:closed}. Finally, the reader must trust the integer and rational arithmetic of Python and the integer tensor contraction of numpy in the absence of overflow. The binary64 error bounds above and the run-time assertions exclude overflow for accepted certificates; therefore the checker must not be run with assertions disabled, and the tip radius, a parameter of the programs, must be left at its value $3/5$.
```

## R6-6 — Zero-radius parametrization

kind: correction

Adjudication: `ADJ-R6` — CONFIRMED.

Counterexample or reason: The angle between mu_f and mu_g is undefined when a radius is zero, as in ID 5469. Write mu_x=rho_x d_x with an arbitrary unit d_x at zero radius and t=d_f dot d_g; the formulas then require no division by a radius.

Changed locations: [app-local.tex](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:263): 263.

`app-local.tex` — frozen lines 263; final lines 263.

Before:

```latex
For fixed $\mu_f, \mu_g$, the minimum over $|\mu_o| = \rho_o$ of $\mu_o \cdot (\mu_f + \mu_g)$ is $-\rho_o |\mu_f + \mu_g|$, and with $t$ the cosine of the angle between $\mu_f$ and $\mu_g$ we have $\mu_f \cdot \mu_g = at$ and $|\mu_f + \mu_g|^2 = \rho_f^2 + \rho_g^2 + 2at$; every $t \in [-1, 1]$ occurs. Minimizing over $t$, we obtain \eqref{e:closed}.
```

After:

```latex
For fixed $\mu_f, \mu_g$, the minimum over $|\mu_o| = \rho_o$ of $\mu_o \cdot (\mu_f + \mu_g)$ is $-\rho_o |\mu_f + \mu_g|$. Write $\mu_x = \rho_x d_x$ for $x \in \{f,g\}$, with $d_x$ a unit vector chosen arbitrarily when $\rho_x = 0$, and put $t = d_f \cdot d_g$. Then $\mu_f \cdot \mu_g = at$ and $|\mu_f + \mu_g|^2 = \rho_f^2 + \rho_g^2 + 2at$; every $t \in [-1,1]$ occurs in this parametrization. Minimizing over $t$, we obtain \eqref{e:closed}.
```

## R6-7 — Largest tested split block

kind: correction

Adjudication: `ADJ-R6` — CONFIRMED.

Counterexample or reason: The stored size 245 can combine exchange blocks (131+48+48+18). The largest individual matrix actually tested after exchange-sign splitting has size 179. Correct the exact-largest claim and retain the valid upper bounds of 245.

Changed locations: [sec8-computer-assisted.tex](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:85): 85.

`sec8-computer-assisted.tex` — frozen lines 73; final lines 85.

Before:

```latex
\caption{The hardest patterns of $\Pext$, which has $2{,}696$ straight patterns and $5{,}266$ turns. The first three are decoupled, so their values are exact closed forms (\S\ref{s:closed}); in the third, all sites other than $\mathsf N$ and $\mathsf s$ have status $\mathrm U$. In the generic steps, every site of the template has status $\mathrm U$, except the arrival site $\mathsf s$, which has status $\mathrm D$ and keeps its bonds to the corners $(1, -1)$ and $(-1, -1)$; there $k$ is the number of vectors of Appendix~\ref{s:local}. The bound of an inversion certificate is the floating-point value of the supremum of the $c$ for which its integer matrices \eqref{e:Meps} are positive definite; it is not used in the proof, in which the exact test is made at $c = 961/1000$ or $187/200$. The largest of these matrices has size $245 \times 245$, and the certificates of all $7{,}962$ patterns were produced in about $34$ CPU-minutes.}\label{tab:H1}
```

After:

```latex
\caption{Selected patterns of $\Pext$, which has $2{,}696$ straight patterns and $5{,}266$ turns. The first two rows give the smallest values found numerically in the straight and turning classes; global optimality is not certified. The first three are decoupled, so their values are exact closed forms (\S\ref{s:closed}); in the third, all sites other than $\mathsf N$ and $\mathsf s$ have status $\mathrm U$. In the generic steps, every site of the template has status $\mathrm U$, except the arrival site $\mathsf s$, which has status $\mathrm D$ and keeps its bonds to the corners $(1, -1)$ and $(-1, -1)$; there $k$ is the number of vectors of Appendix~\ref{s:local}. The bound of an inversion certificate is the floating-point value of the supremum of the $c$ for which its integer matrices \eqref{e:Meps} are positive definite; it is not used in the proof, in which the exact test is made at $c = 961/1000$ or $187/200$. With the exchange signs split as in \eqref{e:Meps}, the largest tested matrix has size $179 \times 179$, and the certificates of all $7{,}962$ patterns were produced in about $34$ CPU-minutes.}\label{tab:H1}
```

## R1-1 — Edge-orientation signs

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: An oriented determinant changes sign on reversing its edge. Reversing one edge at a vertex gives B=-1 and the unsigned local product +1 in the adjudicated example. Include c_x, the product of incident orientation signs, in rho_x and in the second local factorization.

Changed locations: [sec2-frames-Q.tex](/home/ubuntu/aklt/manuscript-corrected/sec2-frames-Q.tex:114): 114–119, 128.

`sec2-frames-Q.tex` — frozen lines 101; final lines 114–119.

Before:

```latex
We first show that $U F = F \, \iota B / \|B\|$ defines a unitary map $U \colon L^2(\mu^\circ) \to \ell^2(\Omega, \pi)$ with $U E_x = P_x U$. Unitarity follows from \eqref{e:mucirc} and $\iota B(s) \neq 0$. Write $\iota B(s) = \beta_x(s_x; s_{N(x)}) \, \rho_x(s_{\Lambda \setminus x})$, where $\rho_x$ is the product of the factors of bonds not containing $x$. By \eqref{e:mucirc}, $\mu^\circ(t \mid s_{\Lambda \setminus x})$ is proportional to $w_x(t) |\beta_x(t; s_{N(x)})|^2$. Hence, for fixed $s_{\Lambda \setminus x}$,
```

After:

```latex
We first show that $U F = F \, \iota B / \|B\|$ defines a unitary map $U \colon L^2(\mu^\circ) \to \ell^2(\Omega, \pi)$ with $U E_x = P_x U$. Unitarity follows from \eqref{e:mucirc} and $\iota B(s) \neq 0$. For $e=\{x,y\}$ write $q_e=\epsilon_{e,x}q_{xy}$, with $\epsilon_{e,x}\in\{\pm1\}$, and set $c_x=\prod_{e\ni x}\epsilon_{e,x}$. Define
\begin{equation*}
\rho_x(s_{\Lambda\setminus x})
=c_x\prod_{e\not\ni x}q_e\bigl((\zeta(s_z))_{z\in e}\bigr).
\end{equation*}
Then $\iota B(s)=\beta_x(s_x;s_{N(x)})\rho_x(s_{\Lambda\setminus x})$. By \eqref{e:mucirc}, $\mu^\circ(t \mid s_{\Lambda \setminus x})$ is proportional to $w_x(t) |\beta_x(t; s_{N(x)})|^2$. Hence, for fixed $s_{\Lambda \setminus x}$,
```

`sec2-frames-Q.tex` — frozen lines 110; final lines 128.

Before:

```latex
Let $\psi \in \mathcal S_x$. By Lemma~\ref{l:divisibility} with $R = \{x\}$, $\psi = b_{\{x\}} \chi$ with $\chi$ independent of $z_x$, so $\iota \psi(t, s_{\Lambda \setminus x}) = \beta_x(t; s_{N(x)}) \, \chi((\zeta(s_y))_{y \neq x})$. For fixed $s_{\Lambda \setminus x}$ this is a multiple of $\beta_x(\, \cdot \,; s_{N(x)})$, so $\iota \psi \in \Ran P_x$. Hence $\|(1 - P_x) \iota \varphi\| \le \|\iota \varphi - \iota \Pi_{\mathcal S_x} \varphi\| = \|(1 - \Pi_{\mathcal S_x}) \varphi\|$, where we used that $\iota$ is an isometry.
```

After:

```latex
Let $\psi \in \mathcal S_x$. By Lemma~\ref{l:divisibility} with $R = \{x\}$, $\psi = b_{\{x\}} \chi$ with $\chi$ independent of $z_x$, so $\iota \psi(t, s_{\Lambda \setminus x}) = c_x\,\beta_x(t; s_{N(x)}) \, \chi((\zeta(s_y))_{y \neq x})$. For fixed $s_{\Lambda \setminus x}$ this is a multiple of $\beta_x(\, \cdot \,; s_{N(x)})$, so $\iota \psi \in \Ran P_x$. Hence $\|(1 - P_x) \iota \varphi\| \le \|\iota \varphi - \iota \Pi_{\mathcal S_x} \varphi\| = \|(1 - \Pi_{\mathcal S_x}) \varphi\|$, where we used that $\iota$ is an isometry.
```

## R1-2 — Individual positive factors

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: For one site with four identical neighboring letters, Z=16/5 and mu(a)/w(a)=5(1+gamma_+)^4/16, exceeding the asserted one-factor upper bound. Bound each internal/boundary bond factor and assert positive site weights.

Changed locations: [sec2-frames-Q.tex](/home/ubuntu/aklt/manuscript-corrected/sec2-frames-Q.tex:155): 155.

`sec2-frames-Q.tex` — frozen lines 137; final lines 155.

Before:

```latex
All weights in \eqref{e:muD} and \eqref{e:muDW} lie in $[1 - \gamma_+, 1 + \gamma_+]$ times the site weights.
```

After:

```latex
Every internal bond factor and every boundary bond factor in \eqref{e:muD} and \eqref{e:muDW} lies in $[1-\gamma_+,1+\gamma_+]$, and all site weights are positive.
```

## R1-3 — Exact internal frame proof

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: A citation without a locator and a numerical moment check do not supply the promised exact design input. Give explicit icosahedron/dodecahedron coordinates, exact second/fourth moments, odd-moment cancellation, and the dual-face calculation, proving the design property internally.

Changed locations: [sec2-frames-Q.tex](/home/ubuntu/aklt/manuscript-corrected/sec2-frames-Q.tex:63): 63–76.

`sec2-frames-Q.tex` — frozen lines 63; final lines 63–76.

Before:

```latex
Let $D_{\mathrm I} \subset \Sph$ be the twelve vertices of a regular icosahedron and $D_{\mathrm{II}} \subset \Sph$ the twenty normalized centres of its faces, the vertices of the dual dodecahedron. With uniform weights $w_{\mathrm I} \equiv 1/12$ and $w_{\mathrm{II}} \equiv 1/20$, both are spherical $5$-designs (see \cite{DGS77}; we also checked the moments up to degree $6$ numerically, with errors below $10^{-15}$ up to degree $5$), so both are frames. Both sets are invariant under $a \mapsto -a$. A direct computation shows that for $a \in D_{\mathrm I}$ and $b \in D_{\mathrm{II}}$,
```

After:

```latex
Let $D_{\mathrm I} \subset \Sph$ be the twelve vertices of a regular icosahedron and $D_{\mathrm{II}} \subset \Sph$ the twenty normalized centers of its faces, the vertices of the dual dodecahedron. Here is an exact verification of the design property. Put $\phi=(1+\sqrt5)/2$, and let $\operatorname{cyc}$ denote the three cyclic coordinate permutations, with independent indicated signs. In a common orientation the unnormalized vertex sets are
\begin{equation*}
I_0=\{\operatorname{cyc}(0,\pm1,\pm\phi)\},\qquad
D_0=\{(\pm1,\pm1,\pm1)\}\cup
\{\operatorname{cyc}(0,\pm\phi,\pm\phi^{-1})\},
\end{equation*}
and $D_{\mathrm I}=I_0/\sqrt{\phi+2}$, $D_{\mathrm{II}}=D_0/\sqrt3$. For each $b_0\in D_0$, the three $a_0\in I_0$ with $a_0\cdot b_0=1+\phi$ have pairwise dot product $\phi$ and sum $(1+\phi)b_0$, so these are the corresponding face-center directions. Both sets are invariant under independent coordinate sign changes and cyclic permutations. Using $\phi^2=\phi+1$, their uniform averages satisfy, for $i\ne j$,
\begin{equation*}
\frac1{|D|}\sum_{a\in D}a_i^2=\frac13,\qquad
\frac1{|D|}\sum_{a\in D}a_i^4=\frac15,\qquad
\frac1{|D|}\sum_{a\in D}a_i^2a_j^2=\frac1{15},
\quad D=D_{\mathrm I},D_{\mathrm{II}}.
\end{equation*}
Every monomial with an odd coordinate exponent has average zero. Together with the constant moment, these are all the moments through total degree $5$, and they equal the normalized spherical moments. Thus the uniform weights $w_{\mathrm I}\equiv1/12$ and $w_{\mathrm{II}}\equiv1/20$ make both sets spherical $5$-designs, and hence frames. Both sets are invariant under $a\mapsto-a$. The same coordinates give the following cross-frame inner products:
```

## R2-1 — Zero total in Cauchy–Schwarz

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: For the constant function, every X_a and Y_a is zero and the displayed total quotient is 0/0. Separate the zero Dirichlet-form case, then assume the total denominator is strictly positive.

Changed locations: [sec3-knabe.tex](/home/ubuntu/aklt/manuscript-corrected/sec3-knabe.tex:105): 105–111.

`sec3-knabe.tex` — frozen lines 105; final lines 105–111.

Before:

```latex
\emph{Weighted weights.} Let $\varphi \in L^2(\mu)$, and set $X_a = \langle \varphi, B_a \varphi \rangle$ and $Y_a = \langle \varphi, A_a \varphi \rangle$. Let $G_a$ be the orthogonal projection onto $\ker A_a$. Since $Q_x \ge 0$ and $w > 0$ on $R$, $\ker B_a = \bigcap_{x \in R + a} \ker Q_x = \ker A_a$, so $B_a = G_a^\perp B_a G_a^\perp$. If $G_a^\perp \varphi = 0$ then $X_a = Y_a = 0$. Otherwise, by Cauchy--Schwarz and Lemma~\ref{l:fibre},
```

After:

```latex
\emph{Weighted weights.} Let $\varphi \in L^2(\mu)$, and set $X_a = \langle \varphi, B_a \varphi \rangle$ and $Y_a = \langle \varphi, A_a \varphi \rangle$. If $\langle\varphi,\mathcal L\varphi\rangle=0$, positivity gives $Q_x\varphi=0$ for every $x$, hence $A_a\varphi=B_a\varphi=0$ for every $a$; the required bound
\begin{equation*}
\Bigl\langle\varphi,\sum_aB_a^2\varphi\Bigr\rangle
\ge g(\ell)\frac{\mathsf s^4}{\ell^2}
\langle\varphi,\mathcal L\varphi\rangle
\end{equation*}
then holds with both sides zero. In the remaining calculation assume $\langle\varphi,\mathcal L\varphi\rangle>0$, so $\sum_aY_a=\ell^2\langle\varphi,\mathcal L\varphi\rangle>0$. Let $G_a$ be the orthogonal projection onto $\ker A_a$. Since $Q_x \ge 0$ and $w > 0$ on $R$, $\ker B_a = \bigcap_{x \in R + a} \ker Q_x = \ker A_a$, so $B_a = G_a^\perp B_a G_a^\perp$. If $G_a^\perp \varphi = 0$ then $X_a = Y_a = 0$. Otherwise, by Cauchy--Schwarz and Lemma~\ref{l:fibre},
```

## R2-2 — Nontrivial gap spaces

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: A singleton product or empty volume has no nonconstant function and no smallest positive eigenvalue. Require coordinate alphabets of at least two elements and restrict spectral-gap assertions to nonempty finite volumes.

Changed locations: [sec3-knabe.tex](/home/ubuntu/aklt/manuscript-corrected/sec3-knabe.tex:7): 7; [sec4-mixing-to-gap.tex](/home/ubuntu/aklt/manuscript-corrected/sec4-mixing-to-gap.tex:7): 7.

`sec3-knabe.tex` — frozen lines 7; final lines 7.

Before:

```latex
Let $L, N \ge 3$ and $\Lambda = \Z_L \times \Z_N$, let $(S_x)_{x \in \Lambda}$ be finite sets, and let $\mu$ be a probability measure on $\prod_x S_x$ of the form
```

After:

```latex
Let $L, N \ge 3$ and $\Lambda = \Z_L \times \Z_N$, let $(S_x)_{x \in \Lambda}$ be finite sets with $|S_x|\ge2$, and let $\mu$ be a probability measure on $\prod_x S_x$ of the form
```

`sec4-mixing-to-gap.tex` — frozen lines 7; final lines 7.

Before:

```latex
Consider the frame model on $\Z^2$ with the checkerboard frame and the finite-volume measures $\mu^\eta_{D, W}$ of \eqref{e:muDW}. For $o \in \{0, 1\}$ and $c \in \Z^2$ let
```

After:

```latex
Consider the frame model on $\Z^2$ with the checkerboard frame and the finite-volume measures $\mu^\eta_{D, W}$ of \eqref{e:muDW}. Throughout this section, assertions about spectral gaps concern nonempty finite volumes and single-spin spaces with at least two elements. For $o \in \{0, 1\}$ and $c \in \Z^2$ let
```

## R2-3 — Final surgery index

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: The window hypothesis is available only for integer i<=s, whereas i_1=floor(s)+1>s. Restrict the uniform success bound to the eligible indices and retain agreement-preserving resampling at the final step; the propagation proof already uses only eligible indices.

Changed locations: [sec4-mixing-to-gap.tex](/home/ubuntu/aklt/manuscript-corrected/sec4-mixing-to-gap.tex:101): 101.

`sec4-mixing-to-gap.tex` — frozen lines 101; final lines 101.

Before:

```latex
\emph{Step $i$.} Let $2 \le i \le i_1$. If $i \in I_0$, the pair is not changed. Otherwise we apply a surgery on $F_i$, with a kernel $T_i$ defined as follows. The cells within distance $1$ of $F_i$ lie in $F_i$, in $D_{i - 1}$, or outside $\mathcal C_M$ at distance more than $(i - 1)s - 1 \ge 1$ from $y$, where $\tau$ and $\tau'$ agree. Hence if $\omega_{D_{i - 1}} = \omega'_{D_{i - 1}}$, then $\hat\mu^{\omega\tau}_{F_i} = \hat\mu^{\omega'\tau'}_{F_i}$, and $T_i$ resamples $F_i$ from this measure with the same configuration for both components. If $\omega_{D_{i - 1}} \neq \omega'_{D_{i - 1}}$, $T_i$ first draws the two configurations on $B_i$ from a maximal coupling of the marginals $\hat\mu^{\omega\tau}_{F_i, B_i}$ and $\hat\mu^{\omega'\tau'}_{F_i, B_i}$, then completes each to $F_i$ independently from the conditional laws given $B_i$, and finally replaces the configurations on $A_i$ by independent samples from their conditional laws given the rest. Each of these operations preserves the laws $\hat\mu^{\omega\tau}_{F_i}$ and $\hat\mu^{\omega'\tau'}_{F_i}$. By \eqref{e:W}, the two configurations agree on $B_i$ with probability at least $p_0$ (if $i \le s$). The last operation does not change $B_i$, and for every configuration $\sigma$ of $A_i$ the conditional probability of $\sigma$ given the rest is at least $\alpha^{|A_i|}$, by the chain rule and finite energy. Hence, by Lemma~\ref{l:shellgeom}, the two configurations agree on $D_i = A_i \cup B_i$ after step $i$ with probability at least $p_0 \alpha^{2 |A_i|} \ge \delta$, conditionally on any configuration before step $i$.
```

After:

```latex
\emph{Step $i$.} Let $2 \le i \le i_1$. If $i \in I_0$, the pair is not changed. Otherwise we apply a surgery on $F_i$, with a kernel $T_i$ defined as follows. The cells within distance $1$ of $F_i$ lie in $F_i$, in $D_{i - 1}$, or outside $\mathcal C_M$ at distance more than $(i - 1)s - 1 \ge 1$ from $y$, where $\tau$ and $\tau'$ agree. Hence if $\omega_{D_{i - 1}} = \omega'_{D_{i - 1}}$, then $\hat\mu^{\omega\tau}_{F_i} = \hat\mu^{\omega'\tau'}_{F_i}$, and $T_i$ resamples $F_i$ from this measure with the same configuration for both components. If $\omega_{D_{i - 1}} \neq \omega'_{D_{i - 1}}$, $T_i$ first draws the two configurations on $B_i$ from a maximal coupling of the marginals $\hat\mu^{\omega\tau}_{F_i, B_i}$ and $\hat\mu^{\omega'\tau'}_{F_i, B_i}$, then completes each to $F_i$ independently from the conditional laws given $B_i$, and finally replaces the configurations on $A_i$ by independent samples from their conditional laws given the rest. Each of these operations preserves the laws $\hat\mu^{\omega\tau}_{F_i}$ and $\hat\mu^{\omega'\tau'}_{F_i}$. By \eqref{e:W}, the two configurations agree on $B_i$ with probability at least $p_0$ (if $i \le s$). The last operation does not change $B_i$, and for every configuration $\sigma$ of $A_i$ the conditional probability of $\sigma$ given the rest is at least $\alpha^{|A_i|}$, by the chain rule and finite energy. Hence, for $i\notin I_0$ with $i\le s$, Lemma~\ref{l:shellgeom} gives agreement on $D_i=A_i\cup B_i$ after step $i$ with probability at least $p_0\alpha^{2|A_i|}\ge\delta$, conditionally on any configuration before step $i$. At the final unskipped step $i_1>s$ we use the same kernel, retaining identical resampling when the incoming separator agrees, without asserting this success bound.
```

## R2-4 — Integral geometric parameters

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: A nonintegral M need not give a square with (2M+1)^2 cells; for M=1/2 there is one cell. Make square sizes and thresholds integral, require l_0>=1, and specify integer shell indices while retaining the real scale s=M^(1/4).

Changed locations: [sec4-mixing-to-gap.tex](/home/ubuntu/aklt/manuscript-corrected/sec4-mixing-to-gap.tex:37): 37, 68, 81.

`sec4-mixing-to-gap.tex` — frozen lines 37; final lines 37.

Before:

```latex
Let $\mathcal C_M = \{ c \in \Z^2 : |c|_\infty \le M\}$, a square of side $2M + 1$. For boundary conditions $\eta, \eta'$ outside $\mathcal C_M$ let $\mathcal Q_{M, \eta, \eta'} = \{ c \in \mathcal C_M : |c - z|_\infty > M^{1/2} \text{ for all } z \text{ with } \eta_z \neq \eta'_z \}$. A set $W$ is \emph{$M_0$-compatible} if it is a finite union of translates of $\mathcal C_{M_0}$ by vectors of $(2 M_0 + 1) \Z^2$; by translation invariance we may and do also call its translates $M_0$-compatible.
```

After:

```latex
All square-size parameters $M$, $M'$, and $M_0$ range over $\Z_{\ge0}$, and their thresholds are chosen integral. Let $\mathcal C_M = \{ c \in \Z^2 : |c|_\infty \le M\}$, a square of side $2M + 1$. For boundary conditions $\eta, \eta'$ outside $\mathcal C_M$ let $\mathcal Q_{M, \eta, \eta'} = \{ c \in \mathcal C_M : |c - z|_\infty > M^{1/2} \text{ for all } z \text{ with } \eta_z \neq \eta'_z \}$. A set $W$ is \emph{$M_0$-compatible} if it is a finite union of translates of $\mathcal C_{M_0}$ by vectors of $(2 M_0 + 1) \Z^2$; by translation invariance we may and do also call its translates $M_0$-compatible.
```

`sec4-mixing-to-gap.tex` — frozen lines 68; final lines 68.

Before:

```latex
where $l_0 \in \N$ is a parameter. The set $D_i$ is the intersection of $\mathcal C_M$ with the $\ell^\infty$ sphere of radius $k_i = \lfloor i s \rfloor$ around $y$, and $D_i \subset F_i$. Only the indices $i \le i_1$, where $i_1 = \lfloor s \rfloor + 1$, will be used. Let $I_0$ be the set of $i \in \{2, \dots, i_1\}$ such that $D_i$ is at $\ell^\infty$ distance less than $s/3$ from one of the four corner cells of $\mathcal C_M$. (Without the restriction $i \le i_1$, the set $I_0$ could have two elements: for $y = (0, -M - 1)$, $D_i$ comes close to the two lower corner cells when $k_i \approx M$ and to the two upper ones when $k_i \approx 2M + 1$.)
```

After:

```latex
where $l_0 \in \Z_{\ge1}$ is a parameter; the shell indices $i$ are integers. The set $D_i$ is the intersection of $\mathcal C_M$ with the $\ell^\infty$ sphere of radius $k_i = \lfloor i s \rfloor$ around $y$, and $D_i \subset F_i$. Only the indices $i \le i_1$, where $i_1 = \lfloor s \rfloor + 1$, will be used. Let $I_0$ be the set of $i \in \{2, \dots, i_1\}$ such that $D_i$ is at $\ell^\infty$ distance less than $s/3$ from one of the four corner cells of $\mathcal C_M$. (Without the restriction $i \le i_1$, the set $I_0$ could have two elements: for $y = (0, -M - 1)$, $D_i$ comes close to the two lower corner cells when $k_i \approx M$ and to the two upper ones when $k_i \approx 2M + 1$.)
```

`sec4-mixing-to-gap.tex` — frozen lines 81; final lines 81.

Before:

```latex
We say that \emph{the window estimate holds for $\hat\mu$} if there exist $l_0 \in \N$, $p_0 \in (0, 1]$ and $M_\star$ such that for all $M \ge M_\star$, all $y$ with $\operatorname{dist}_\infty(y, \mathcal C_M) = 1$, all $i$ with $2 \le i \le s$ and $i \notin I_0$, and all configurations $\eta, \xi$ on $\Z^2 \setminus F_i$,
```

After:

```latex
We say that \emph{the window estimate holds for $\hat\mu$} if there exist $l_0 \in \Z_{\ge1}$, $p_0 \in (0, 1]$, and $M_\star\in\Z_{\ge1}$ such that for all $M \ge M_\star$, all $y$ with $\operatorname{dist}_\infty(y, \mathcal C_M) = 1$, all $i$ with $2 \le i \le s$ and $i \notin I_0$, and all configurations $\eta, \xi$ on $\Z^2 \setminus F_i$,
```

## R2-5 — Established local example values

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: The global minimum row and repeated tightest-pattern wording exceed the certificate targets. State exact values of two decoupled examples and consistently qualify all related labels, margins, and negative-control descriptions, merged with R6-3.

Changed locations: [app-constants.tex](/home/ubuntu/aklt/manuscript-corrected/app-constants.tex:17): 17; [app-local.tex](/home/ubuntu/aklt/manuscript-corrected/app-local.tex:196): 196, 270, 272–273, 295–296; [sec1-intro-statement.tex](/home/ubuntu/aklt/manuscript-corrected/sec1-intro-statement.tex:18): 18; [sec8-computer-assisted.tex](/home/ubuntu/aklt/manuscript-corrected/sec8-computer-assisted.tex:78): 78–79, 85, 89.

`app-constants.tex` — frozen lines 17; final lines 17.

Before:

```latex
$\min_\pi c(\pi)$ & $0.961240\ldots$, $0.935565\ldots$ & straight, turn; closed forms (\S\ref{s:closed}) \\
```

After:

```latex
$c(\pi)$ for two decoupled examples & $3825127/3979368$, $1071655/1145463$ & straight and turn examples; closed forms (Proposition~\ref{p:closed}, \S\ref{s:closed}) \\
```

`app-local.tex` — frozen lines 196; final lines 196.

Before:

```latex
For many patterns, every site other than $y$ and its neighbours hangs on the rest by a single bond, possibly through a chain of such sites. For these patterns the infimum $c(\pi)$ has a closed form, which gives a second proof of Theorem~\ref{t:H1} on them, independent of \S\ref{s:inversion}, and the exact values of $c(\pi)$ for the tightest patterns. The main input is a sharp bound on the mean of a spin under several fields. For $r = (r_1, r_2, r_3) \in [0, 1]^3$ let $s_1 = r_1 + r_2 + r_3$, $s_2 = r_1 r_2 + r_1 r_3 + r_2 r_3$, $s_3 = r_1 r_2 r_3$, and
```

After:

```latex
For many patterns, every site other than $y$ and its neighbours hangs on the rest by a single bond, possibly through a chain of such sites. For these patterns the infimum $c(\pi)$ has a closed form, which gives a second proof of Theorem~\ref{t:H1} on them, independent of \S\ref{s:inversion}, and the exact values of $c(\pi)$ for the examples below. The main input is a sharp bound on the mean of a spin under several fields. For $r = (r_1, r_2, r_3) \in [0, 1]^3$ let $s_1 = r_1 + r_2 + r_3$, $s_2 = r_1 r_2 + r_1 r_3 + r_2 r_3$, $s_3 = r_1 r_2 r_3$, and
```

`app-local.tex` — frozen lines 270; final lines 270.

Before:

```latex
Of the $7{,}962$ patterns of $\Pext$, $4{,}735$ are decoupled ($1{,}553$ straight and $3{,}182$ turns), among them the three tightest patterns of the class. For these three the minimum in \eqref{e:closed} is rational, since $a = 0$ or the minimum is attained at $t = 1$, where the square root is $\rho_f + \rho_g$. The values are as follows; in each case the test of Proposition~\ref{p:closed}, in rational arithmetic, holds at the stated value of $c(\pi)$ and fails at that value plus $10^{-12}$.
```

After:

```latex
Of the $7{,}962$ patterns of $\Pext$, $4{,}735$ are decoupled ($1{,}553$ straight and $3{,}182$ turns), including the following three examples. For these three the minimum in \eqref{e:closed} is rational, since $a = 0$ or the minimum is attained at $t = 1$, where the square root is $\rho_f + \rho_g$. The values are as follows; in each case the test of Proposition~\ref{p:closed}, in rational arithmetic, holds at the stated value of $c(\pi)$ and fails at that value plus $10^{-12}$.
```

`app-local.tex` — frozen lines 272–273; final lines 272–273.

Before:

```latex
\item The tightest straight pattern: $\mathsf e$, $\mathsf N$ and the corner $(1, -1)$ have status $\mathrm U$; $\mathsf W$ has status $\mathrm D$ and keeps its bonds to $y$ and to its tip; $\mathsf s$ has status $\mathrm D$ and keeps its bonds to $(1, -1)$ and to its tip; the corner $(-1, 1)$ has status $\mathrm D$ and keeps its bond to $\mathsf N$; the corners $(1, 1)$ and $(-1, -1)$ are removed. Here $\rho_o = \rho_{\mathsf N} = 7/24$, $\rho_{\mathsf e} = 740/2193$, $\rho_{\mathsf W} = 3/25$, and $c(\pi) = 3825127/3979368 = 0.961240\ldots$
\item The tightest turn ($o = \mathsf e$): $\mathsf s$ is removed; $\mathsf N$ has status $\mathrm D$ and keeps its bonds to $y$ and to its tip; the corners $(1, 1)$ and $(-1, 1)$ have status $\mathrm D$ and keep their bonds to $\mathsf e$ and $\mathsf W$, respectively; all other sites have status $\mathrm U$. Here $\rho_{\mathsf e} = \rho_{\mathsf W} = 112/275$, $\rho_{\mathsf N} = 3/25$, and $c(\pi) = 1071655/1145463 = 0.935565\ldots$
```

After:

```latex
\item The straight example in the first row of Table~\ref{tab:H1}: $\mathsf e$, $\mathsf N$ and the corner $(1, -1)$ have status $\mathrm U$; $\mathsf W$ has status $\mathrm D$ and keeps its bonds to $y$ and to its tip; $\mathsf s$ has status $\mathrm D$ and keeps its bonds to $(1, -1)$ and to its tip; the corner $(-1, 1)$ has status $\mathrm D$ and keeps its bond to $\mathsf N$; the corners $(1, 1)$ and $(-1, -1)$ are removed. Here $\rho_o = \rho_{\mathsf N} = 7/24$, $\rho_{\mathsf e} = 740/2193$, $\rho_{\mathsf W} = 3/25$, and $c(\pi) = 3825127/3979368 = 0.961240\ldots$
\item The turn example in the second row of Table~\ref{tab:H1} ($o = \mathsf e$): $\mathsf s$ is removed; $\mathsf N$ has status $\mathrm D$ and keeps its bonds to $y$ and to its tip; the corners $(1, 1)$ and $(-1, 1)$ have status $\mathrm D$ and keep their bonds to $\mathsf e$ and $\mathsf W$, respectively; all other sites have status $\mathrm U$. Here $\rho_{\mathsf e} = \rho_{\mathsf W} = 112/275$, $\rho_{\mathsf N} = 3/25$, and $c(\pi) = 1071655/1145463 = 0.935565\ldots$
```

`app-local.tex` — frozen lines 296; final lines 295–296.

Before:

```latex
\item The stored certificates of the tightest patterns are rejected when the threshold is raised $2 \cdot 10^{-5}$ above the numerical minimum of the ratio.
```

After:

```latex
\item On the decoupled patterns, the floating-point value of $c$ at which the inversion test fails exceeds the closed form \eqref{e:closed} by at most $2.5 \cdot 10^{-15}$, and the two agree to $10^{-7}$ on $4{,}250$ of the $4{,}735$ patterns.
\item The stored certificates of the numerically selected patterns are rejected at thresholds obtained by adding $2\cdot10^{-5}$ to the numerical minimum and rounding upward to a multiple of $10^{-5}$; see \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak code/\linebreak[1]negctl.py} and \texttt{72-\allowbreak audit-\allowbreak H1-\allowbreak certificates/\allowbreak out/\allowbreak negctl\_\allowbreak hard.json}.
```

`sec1-intro-statement.tex` — frozen lines 18; final lines 18.

Before:

```latex
The proof of Theorem~\ref{t:main} is computer-assisted. Three statements are verified by computer, all at the pair of constants $(\cs, \ct) = (0.961, 0.935)$ (Theorem~\ref{t:inputs}). Hypothesis~(H1) is a list of $7{,}962$ inequalities, one for each local configuration (``pattern'') in an explicit class $\Pext$ of radius-$2$ neighbourhoods of the square lattice. Each inequality asserts that a ratio of two functions of at most twenty unit vectors in $\R^3$, affine in each vector, is at least $\cs$ or $\ct$ on the whole product of spheres. We verify it in exact integer and rational arithmetic, with tests of positive definiteness of integer matrices for each pattern, one for each exchange-symmetry sector of the pattern (\S\ref{s:H1} and Appendix~\ref{s:local}); the smallest margins are $2.4 \cdot 10^{-4}$ and $5.6 \cdot 10^{-4}$. Hypothesis~(H2), a bound on the growth of weighted trail sums, and Hypothesis~(H3$'$), a bound on the spectral radius of a $2 \times 2$ kernel built from closed trails, are verified in floating-point arithmetic with upward rounding (\S\ref{s:H2}, \S\ref{s:H3} and Appendix~\ref{s:tail}); the bound for (H2) was also reproduced in exact rational arithmetic. These two hypotheses use (H1) only through the two numbers $\cs$ and $\ct$. Everything else is proved here or cited with a precise locator. One cited result, \cite[Theorem~4.1]{MO94} as it is invoked in \cite{MOS94}, is applied to a finite single-spin space larger than the two-valued one for which its proof is written out; Remark~\ref{r:finiteS} explains why the proof applies. The constants $c$ and $L_0$ are not explicit.
```

After:

```latex
The proof of Theorem~\ref{t:main} is computer-assisted. Three statements are verified by computer, all at the pair of constants $(\cs, \ct) = (0.961, 0.935)$ (Theorem~\ref{t:inputs}). Hypothesis~(H1) is a list of $7{,}962$ inequalities, one for each local configuration (``pattern'') in an explicit class $\Pext$ of radius-$2$ neighbourhoods of the square lattice. Each inequality asserts that a ratio of two functions of at most twenty unit vectors in $\R^3$, affine in each vector, is at least $\cs$ or $\ct$ on the whole product of spheres. We verify it in exact integer and rational arithmetic, with tests of positive definiteness of integer matrices for each pattern, one for each exchange-symmetry sector of the pattern (\S\ref{s:H1} and Appendix~\ref{s:local}); the margins on the first two decoupled examples of Table~\ref{tab:H1} are $2.4 \cdot 10^{-4}$ and $5.6 \cdot 10^{-4}$. Hypothesis~(H2), a bound on the growth of weighted trail sums, and Hypothesis~(H3$'$), a bound on the spectral radius of a $2 \times 2$ kernel built from closed trails, are verified in floating-point arithmetic with upward rounding (\S\ref{s:H2}, \S\ref{s:H3} and Appendix~\ref{s:tail}); the bound for (H2) was also reproduced in exact rational arithmetic. These two hypotheses use (H1) only through the two numbers $\cs$ and $\ct$. Everything else is proved here or cited with a precise locator. One cited result, \cite[Theorem~4.1]{MO94} as it is invoked in \cite{MOS94}, is applied to a finite single-spin space larger than the two-valued one for which its proof is written out; Remark~\ref{r:finiteS} explains why the proof applies. The constants $c$ and $L_0$ are not explicit.
```

`sec8-computer-assisted.tex` — frozen lines 66–67; final lines 78–79.

Before:

```latex
tightest straight & $c(\pi) = 3825127/3979368 = 0.961240\ldots$ & $0.961240$ \\
tightest turn & $c(\pi) = 1071655/1145463 = 0.935565\ldots$ & $0.935565$ \\
```

After:

```latex
straight example (ID 7645) & $c(\pi) = 3825127/3979368 = 0.961240\ldots$ & $0.961240$ \\
turn example (ID 1382) & $c(\pi) = 1071655/1145463 = 0.935565\ldots$ & $0.935565$ \\
```

`sec8-computer-assisted.tex` — frozen lines 73; final lines 85.

Before:

```latex
\caption{The hardest patterns of $\Pext$, which has $2{,}696$ straight patterns and $5{,}266$ turns. The first three are decoupled, so their values are exact closed forms (\S\ref{s:closed}); in the third, all sites other than $\mathsf N$ and $\mathsf s$ have status $\mathrm U$. In the generic steps, every site of the template has status $\mathrm U$, except the arrival site $\mathsf s$, which has status $\mathrm D$ and keeps its bonds to the corners $(1, -1)$ and $(-1, -1)$; there $k$ is the number of vectors of Appendix~\ref{s:local}. The bound of an inversion certificate is the floating-point value of the supremum of the $c$ for which its integer matrices \eqref{e:Meps} are positive definite; it is not used in the proof, in which the exact test is made at $c = 961/1000$ or $187/200$. The largest of these matrices has size $245 \times 245$, and the certificates of all $7{,}962$ patterns were produced in about $34$ CPU-minutes.}\label{tab:H1}
```

After:

```latex
\caption{Selected patterns of $\Pext$, which has $2{,}696$ straight patterns and $5{,}266$ turns. The first two rows give the smallest values found numerically in the straight and turning classes; global optimality is not certified. The first three are decoupled, so their values are exact closed forms (\S\ref{s:closed}); in the third, all sites other than $\mathsf N$ and $\mathsf s$ have status $\mathrm U$. In the generic steps, every site of the template has status $\mathrm U$, except the arrival site $\mathsf s$, which has status $\mathrm D$ and keeps its bonds to the corners $(1, -1)$ and $(-1, -1)$; there $k$ is the number of vectors of Appendix~\ref{s:local}. The bound of an inversion certificate is the floating-point value of the supremum of the $c$ for which its integer matrices \eqref{e:Meps} are positive definite; it is not used in the proof, in which the exact test is made at $c = 961/1000$ or $187/200$. With the exchange signs split as in \eqref{e:Meps}, the largest tested matrix has size $179 \times 179$, and the certificates of all $7{,}962$ patterns were produced in about $34$ CPU-minutes.}\label{tab:H1}
```

`sec8-computer-assisted.tex` — frozen lines 77; final lines 89.

Before:

```latex
The constants of Theorem~\ref{t:H1} cannot be raised much with the present template. For the third pattern of Table~\ref{tab:H1}, $c(\pi) = 416114/444675 = 0.935771\ldots$ exactly, by \eqref{e:5469}, so (H1) fails for every $\ct > 416114/444675$ with the template and the slots of Definition~\ref{d:pattern}. The margins of Theorem~\ref{t:H1} on the two tightest patterns are $2.4 \cdot 10^{-4}$ and $5.6 \cdot 10^{-4}$. We also note that the method of \S\ref{s:H3} does not give $\rho(M_1) < 1$ at $(\cs, \ct) = (0.960, 0.925)$, so that the pair $(0.961, 0.935)$ leaves little room in either direction.
```

After:

```latex
The constants of Theorem~\ref{t:H1} cannot be raised much with the present template. For the third pattern of Table~\ref{tab:H1}, $c(\pi) = 416114/444675 = 0.935771\ldots$ exactly, by \eqref{e:5469}, so (H1) fails for every $\ct > 416114/444675$ with the template and the slots of Definition~\ref{d:pattern}. The margins of Theorem~\ref{t:H1} on the first two decoupled examples of Table~\ref{tab:H1} are $2.4 \cdot 10^{-4}$ and $5.6 \cdot 10^{-4}$. We also note that the method of \S\ref{s:H3} does not give $\rho(M_1) < 1$ at $(\cs, \ct) = (0.960, 0.925)$, so that the pair $(0.961, 0.935)$ leaves little room in either direction.
```

## R3-1 — Positive normalizers

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: Nonnegative continuous factors may vanish pointwise; antipodal pins give a one-site density vanishing at two points but integral 2/3. Prove strictly positive finite partition functions using a common spin direction and an open product neighborhood, including diluted sites and positive trace mass, and prove the reference window law has full support.

Changed locations: [sec5-cut.tex](/home/ubuntu/aklt/manuscript-corrected/sec5-cut.tex:11): 11, 79.

`sec5-cut.tex` — frozen lines 11; final lines 11.

Before:

```latex
and we write $\E^\tau_D$ and $\E^0_D$ for the corresponding probability measures on $(\Sph)^D$, and $\Psi_D(\tau) = Z^\tau_D / Z^0_D$. Note that the legs of $D$ into $Y$ carry no factor. We will use three elementary facts.
```

After:

```latex
Both partition functions in \eqref{e:Zpin} are finite and strictly positive. For $D\ne\emptyset$, choose $q\in\Sph$ different from the negatives of all surviving pins and put every spin equal to $q$. Every bond factor is then $2$ and every leg factor is positive. By continuity, the integrand is positive on a product of open spherical neighborhoods of positive product measure. The integrand is bounded, so its integral is finite. For $D=\emptyset$, the partition functions equal $1$. The same argument applies to any retained subsets of bonds and legs, and to site measures with positive uniform components; a positive scalar trace mass also preserves positivity. We write $\E^\tau_D$ and $\E^0_D$ for the corresponding probability measures on $(\Sph)^D$, and $\Psi_D(\tau) = Z^\tau_D / Z^0_D$. Note that the legs of $D$ into $Y$ carry no factor. We will use three elementary facts.
```

`sec5-cut.tex` — frozen lines 79; final lines 79.

Before:

```latex
Inserting this into \eqref{e:windowlaw}, we obtain $\mu^\eta_{D, F}(n_B = \mathsf s) = c(\eta) \, \nu(\mathsf s) \, e^{-e(\eta, \mathsf s)}$, where $\nu(\mathsf s)$ is proportional to $W_B(\mathsf s) Z^{\mathsf s}_{G_1}$ and normalized, and $c(\eta)$ does not depend on $\mathsf s$. Summing over $\mathsf s$ gives $c(\eta)^{-1} = \sum_{\mathsf s} \nu(\mathsf s) e^{-e(\eta, \mathsf s)} \in [e^{-\varepsilon}, e^{\varepsilon}]$, which proves \eqref{e:cutratio}.
```

After:

```latex
Inserting this into \eqref{e:windowlaw}, we obtain $\mu^\eta_{D, F}(n_B = \mathsf s) = c(\eta) \, \nu(\mathsf s) \, e^{-e(\eta, \mathsf s)}$, where $\nu(\mathsf s)$ is proportional to $W_B(\mathsf s) Z^{\mathsf s}_{G_1}$ and normalized, and $c(\eta)$ does not depend on $\mathsf s$. Every weight of $\nu$ is strictly positive: $W_B(\mathsf s)>0$ by the positive site weights and \eqref{e:icodod}, and $Z^{\mathsf s}_{G_1}>0$ by the positivity just established, also when $G_1=\emptyset$. Summing over $\mathsf s$ gives $c(\eta)^{-1} = \sum_{\mathsf s} \nu(\mathsf s) e^{-e(\eta, \mathsf s)} \in [e^{-\varepsilon}, e^{\varepsilon}]$, which proves \eqref{e:cutratio}.
```

## R3-2 — Nonempty removal list

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: The removal bound refers to x_1 even when the old hypotheses allow p=0. Require p>=1 and establish that the finite nonempty U-prime gives a nonempty cut X before choosing its connected ordering.

Changed locations: [sec5-cut.tex](/home/ubuntu/aklt/manuscript-corrected/sec5-cut.tex:102): 102, 221.

`sec5-cut.tex` — frozen lines 102; final lines 102.

Before:

```latex
Assume Hypothesis~(P). Let $G$ and $\tau$ be as in \eqref{e:P}, and let $x_1, \dots, x_p$ be distinct sites of $G$ with $b(x_j) = d(x_j, \Z^2 \setminus G) \ge 3$, such that every $x_j$ with $j \ge 2$ has a neighbour among $x_1, \dots, x_{j - 1}$. Let $X = \{x_1, \dots, x_p\}$. Then
```

After:

```latex
Assume Hypothesis~(P). Let $G$ and $\tau$ be as in \eqref{e:P}, and let $p\ge1$ and $x_1,\dots,x_p$ be distinct sites of $G$ with $b(x_j) = d(x_j, \Z^2 \setminus G) \ge 3$, such that every $x_j$ with $j \ge 2$ has a neighbour among $x_1, \dots, x_{j - 1}$. Let $X = \{x_1, \dots, x_p\}$. Then
```

`sec5-cut.tex` — frozen lines 221; final lines 221.

Before:

```latex
Fix $o$, $l_0 = 20$, and $M$, $y$, $i$ as in Definition~\ref{d:W} with $M$ so large that $s \ge s_0(l_0)$ and $M \ge M_{\mathrm g}(l_0)$. Let $F$, $B$, $G$, $X$, $G_1$, $G_2$ be as in \eqref{e:Xcut}. Let $\eta$ be a configuration outside $F_i$ and $\mathsf s$ a window configuration. The pin configuration $\eta \mathsf s$ on the legs of $G$ consists of letters of the frames, which are unit vectors. By Lemma~\ref{l:Xconn}, we can order $X$ so that every site after the first has a previously listed neighbour, and by Lemma~\ref{l:cutgeom}(3), $b(x) \ge 3$ on $X$. Lemma~\ref{l:removal} and \eqref{e:cutsum} with $\vartheta = \theta$ give
```

After:

```latex
Fix $o$, $l_0 = 20$, and $M$, $y$, $i$ as in Definition~\ref{d:W} with $M$ so large that $s \ge s_0(l_0)$ and $M \ge M_{\mathrm g}(l_0)$. Let $F$, $B$, $G$, $X$, $G_1$, $G_2$ be as in \eqref{e:Xcut}. Let $\eta$ be a configuration outside $F_i$ and $\mathsf s$ a window configuration. The pin configuration $\eta \mathsf s$ on the legs of $G$ consists of letters of the frames, which are unit vectors. The proof of Lemma~\ref{l:Xconn} gives a finite nonempty $U'$; a site of $U'$ with maximal first coordinate has a nearest neighbor outside $U'$, so $X\ne\emptyset$. By Lemma~\ref{l:Xconn}, we can therefore order $X$ so that every site after the first has a previously listed neighbor, and by Lemma~\ref{l:cutgeom}(3), $b(x) \ge 3$ on $X$. Lemma~\ref{l:removal} and \eqref{e:cutsum} with $\vartheta = \theta$ give
```

## R3-3 — Signed side depths

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: With y=(0,-M-1), the bottom side misses the square yet its distance to the half-plane beyond the top edge is 2M+2+k, not at most zero. Use signed inward depths and distinguish sides meeting the square, beyond the chosen edge, or beyond the opposite edge. The count of 48 cells/192 sites is retained.

Changed locations: [sec5-cut.tex](/home/ubuntu/aklt/manuscript-corrected/sec5-cut.tex:179): 179.

`sec5-cut.tex` — frozen lines 179; final lines 179.

Before:

```latex
It remains to count the cells of the second case with a given $t = j$. Such a cell lies on the $\ell^\infty$ sphere of radius $k \pm j$ around $y$ and on the ring $\{c : h(c) = h'\}$ for one of at most three integers $h' \in [l_0/2 + j - 2, l_0/2 + j)$. Both are boundaries of axis-parallel squares, so they meet in at most $8$ cells unless a side of the sphere lies on a side of the ring, that is, unless a side of the sphere of radius $k \pm j$ that meets $\mathcal C_M$ is parallel to an edge $\mathcal E$ of $\mathcal C_M$ at distance exactly $h'$ from the half-plane beyond $\mathcal E$. When the radius changes from $k$ to $k \pm j$, the distance of such a side changes by $j$. By Lemma~\ref{l:shellgeom}, the sides of the sphere of radius $k$ that are parallel to an edge and meet $\mathcal C_M$ are at distance at least $s/3$; those of radius $k \pm j$ are therefore at distance at least $s/3 - j \ge s/3 - s/12 > l_0/2 + j$ when $s$ is large, or they come from a side of radius $k$ that does not meet $\mathcal C_M$ (distance at most $0$), and then their distance is at most $j < l_0/2 + j - 2$. In both cases it differs from $h'$. Hence there are at most $2 \cdot 3 \cdot 8 = 48$ cells, that is, at most $192$ sites, with $t = j$, and their contribution is at most
```

After:

```latex
It remains to count the cells of the second case with a given $t = j$. Such a cell lies on the $\ell^\infty$ sphere of radius $k \pm j$ around $y$ and on the ring $\{c : h(c) = h'\}$ for one of at most three integers $h' \in [l_0/2 + j - 2, l_0/2 + j)$. Both are boundaries of axis-parallel squares, so they meet in at most $8$ cells unless a side of the sphere lies on a side of the ring, that is, unless a side of the sphere of radius $k \pm j$ that meets $\mathcal C_M$ is parallel to an edge $\mathcal E$ of $\mathcal C_M$ at distance exactly $h'$ from the half-plane beyond $\mathcal E$. Use signed inward depths of the supporting lines: for a vertical line $x_1=a$, set $\delta_{\rm L}=a+M+1$ and $\delta_{\rm R}=M+1-a$, and define the bottom and top depths analogously. Changing the radius from $k$ to $k\pm j$ changes each signed depth by at most $j$. Since $y\in[-M-1,M+1]^2$ and $k-j\ge1$, the varying-coordinate intervals of the original and shifted sides meet $[-M,M]$. Thus an original side either meets $\mathcal C_M$, lies beyond the specified edge $\mathcal E$, or lies beyond the opposite edge. In the first case Lemma~\ref{l:shellgeom} gives signed depth at least $s/3$, so the shifted depth is at least $s/3-j>l_0/2+j$ for $j\le s/12$ and $s>3l_0$. In the second case the original depth is at most $0$, so the shifted depth is at most $j<l_0/2+j-2$. In the third case the original depth is at least $2M+2$, so the shifted depth is at least $2M+2-j>l_0/2+j$ for $s$ large. None can equal $h'$. Hence there are at most $2 \cdot 3 \cdot 8 = 48$ cells, that is, at most $192$ sites, with $t = j$, and their contribution is at most
```

## R3-4 — Bounded cut cost

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: F(d)=(d+1)^(-8) is not o(d^(-8)) but still bounds the crude O(M^2) long-part cost uniformly. Big-O decay suffices for bounded cost; little-o additionally makes that contribution vanish.

Changed locations: [sec5-cut.tex](/home/ubuntu/aklt/manuscript-corrected/sec5-cut.tex:229): 229.

`sec5-cut.tex` — frozen lines 229; final lines 229.

Before:

```latex
The proof uses \eqref{e:P} only through the bound \eqref{e:cutsum}. The same argument works if $A \theta^d$ in \eqref{e:P} is replaced by any function $\mathsf F(d)$ with $\sum_d \mathsf F(d) < \infty$ and $\sup_d d^2 \mathsf F(d) < \infty$, the latter for the $O(M^{1/2})$ sites of the long sides of the cut, which are at distance of order $M^{1/4}$ from the pins; with the crude count $|X| \le 4(2M + 1)^2$ used above one needs $\mathsf F(d) = o(d^{-8})$ instead. Theorem~\ref{t:rec} gives exponential decay.
```

After:

```latex
The proof uses \eqref{e:P} only through the bound \eqref{e:cutsum}. The same argument works if $A \theta^d$ in \eqref{e:P} is replaced by any function $\mathsf F(d)$ with $\sum_d \mathsf F(d) < \infty$ and $\sup_d d^2 \mathsf F(d) < \infty$, the latter for the $O(M^{1/2})$ sites of the long sides of the cut, which are at distance of order $M^{1/4}$ from the pins; with the crude count $|X|\le4(2M+1)^2$ used above, $\mathsf F(d)=O(d^{-8})$ suffices for a uniform bound, while $\mathsf F(d)=o(d^{-8})$ makes the long-part contribution tend to zero. Theorem~\ref{t:rec} gives exponential decay.
```

## R7-2 — Overview residual and stopped trails

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: The first removal includes the quartic residual giving the fixed 0.0707 cost. Pair expansion also includes trails stopped at S and their terminal correlation factors. Restore both features in the overview, using the auxiliary-network terminology from R4.

Changed locations: [sec1-intro-statement.tex](/home/ubuntu/aklt/manuscript-corrected/sec1-intro-statement.tex:30): 30, 32.

`sec1-intro-statement.tex` — frozen lines 30; final lines 30.

Before:

```latex
\emph{The cut lemma} (\S\ref{s:cut}). The window law of $B_i$ in $F_i$ is a ratio of partition functions, and these are the same for the frame model and the continuous model on $\Sph$ because every site has at most four factors and the frames are $4$-designs. Removing a closed cut $X$ that separates $B_i$ from the boundary factorizes the partition function, and Lemma~\ref{l:cut} shows that the window law differs from a law that does not depend on the boundary condition by a factor $e^{\pm 2 \varepsilon}$, where $\varepsilon$ is the change of $\log$ of a ratio of pinned and free partition functions under the soft removal of $X$. Removing $X$ one site at a time, $\varepsilon$ is bounded by a sum over the cut of pair-correlation responses $|\E^\tau[n_u \cdot n_v] - \E^0[n_u \cdot n_v]|$ at pairs of sites next to a removed site. Hypothesis (P), decay of these responses in the distance to the pins, therefore implies the estimate of the previous step (Theorem~\ref{t:cutMOS}).
```

After:

```latex
\emph{The cut lemma} (\S\ref{s:cut}). The window law of $B_i$ in $F_i$ is a ratio of partition functions, and these are the same for the frame model and the continuous model on $\Sph$ because every site has at most four factors and the frames are $4$-designs. Removing a closed cut $X$ that separates $B_i$ from the boundary factorizes the partition function, and Lemma~\ref{l:cut} shows that the window law differs from a law that does not depend on the boundary condition by a factor $e^{\pm 2 \varepsilon}$, where $\varepsilon$ is the change of $\log$ of a ratio of pinned and free partition functions under the soft removal of $X$. Removing $X$ one site at a time, $\varepsilon$ is bounded by a fixed additive constant plus a sum over the cut of pair-correlation responses $|\E^\tau[n_u \cdot n_v] - \E^0[n_u \cdot n_v]|$ at pairs of sites next to a removed site. Hypothesis (P), decay of these responses in the distance to the pins, therefore implies the estimate of the previous step (Theorem~\ref{t:cutMOS}).
```

`sec1-intro-statement.tex` — frozen lines 32; final lines 32.

Before:

```latex
\emph{The pair recursion} (\S\ref{s:walks}--\S\ref{s:recursion}). Hypothesis (P) is proved by a walk expansion. A pair correlation is a sum over trails from one site of the pair to the other, weighted by $3^{-|w|}$ and by ratios of partition functions of traced domains. The difference between the pinned and the free ratio telescopes over the steps of the trail, and the response of each step is, exactly, a linear combination of pair responses of the same type around the removed passage site. This closes into a linear recursion for the worst pair response at distance $d$, with a nonnegative $2 \times 2$ kernel built from closed trails. The recursion contracts if the per-step ratios are bounded by the constants $\cs, \ct$ of (H1), if the weighted trail sums decay geometrically (H2), and if the kernel has spectral radius below $1$ (H3$'$) (Theorem~\ref{t:rec}).
```

After:

```latex
\emph{The pair recursion} (\S\ref{s:walks}--\S\ref{s:recursion}). Hypothesis (P) is proved by a walk expansion. A pair correlation is expanded over trails from one site of the pair, stopped at the other site or at the protected boundary layer, weighted by $3^{-|w|}$ and by ratios of partition functions of traced spin networks, with their terminal correlation factors. In the response, trails ending at the other site give the closed-trail kernel, while trails ending at the protected layer give an exponentially decaying error. The difference between the pinned and the free ratio telescopes over the steps of the trail, and the response of each step is, exactly, a linear combination of pair responses of the same type around the removed passage site. This closes into a linear recursion for the worst pair response at distance $d$, with a nonnegative $2 \times 2$ kernel built from closed trails. The recursion contracts if the per-step ratios are bounded by the constants $\cs, \ct$ of (H1), if the weighted trail sums decay geometrically (H2), and if the kernel has spectral radius below $1$ (H3$'$) (Theorem~\ref{t:rec}).
```

## R7-3 — Auxiliary spin support

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: The diluted measure has mass 2/5 at zero and integral |n|^2 equal to 3/5. Qualify the unit-vector convention: physical/ordinary spins and pins are unit, while auxiliary traced spins may also be zero.

Changed locations: [sec1-intro-statement.tex](/home/ubuntu/aklt/manuscript-corrected/sec1-intro-statement.tex:44): 44.

`sec1-intro-statement.tex` — frozen lines 44; final lines 44.

Before:

```latex
Throughout, $\Sph$ is the unit sphere in $\R^3$ and $\dd n$ is the normalized uniform measure on it. On $\Z^2$ we write $d(x, y) = |x_1 - y_1| + |x_2 - y_2|$ for the graph distance and $|x - y|_\infty$ for the $\ell^\infty$ distance; $x \sim y$ means $d(x, y) = 1$. For probability measures $\nu, \nu'$ on a finite set, $\TV(\nu, \nu') = \sup_A |\nu(A) - \nu'(A)|$. For a reversible Markov generator $\mathcal L$ on $L^2(\nu)$ with Dirichlet form $\mathcal E$, the spectral gap is $\gap = \inf \{ \mathcal E(F, F) / \Var_\nu(F) : F \text{ not constant} \}$. All spin configurations are of unit vectors; a ``pin'' is a unit vector attached to a boundary bond.
```

After:

```latex
Throughout, $\Sph$ is the unit sphere in $\R^3$ and $\dd n$ is the normalized uniform measure on it. On $\Z^2$ we write $d(x, y) = |x_1 - y_1| + |x_2 - y_2|$ for the graph distance and $|x - y|_\infty$ for the $\ell^\infty$ distance; $x \sim y$ means $d(x, y) = 1$. For probability measures $\nu, \nu'$ on a finite set, $\TV(\nu, \nu') = \sup_A |\nu(A) - \nu'(A)|$. For a reversible Markov generator $\mathcal L$ on $L^2(\nu)$ with Dirichlet form $\mathcal E$, the spectral gap is $\gap = \inf \{ \mathcal E(F, F) / \Var_\nu(F) : F \text{ not constant} \}$. Physical frame spins, ordinary continuous spins, and pins are unit vectors. Auxiliary traced spins may lie in $\Sph \cup \{0\}$, as in Definition~\ref{d:domain}; a ``pin'' is always a unit vector attached to a boundary bond.
```

## R7-4 — Acyclic dependencies

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: The cut proof invokes the earlier frame definition and shell geometry, contrary to the broad claim of no dependencies on Sections 2–4. State the actual acyclic dependency claim: those proofs do not use the main theorem, the concluding gap theorem, or consequences of the window estimate.

Changed locations: [sec4-mixing-to-gap.tex](/home/ubuntu/aklt/manuscript-corrected/sec4-mixing-to-gap.tex:138): 138.

`sec4-mixing-to-gap.tex` — frozen lines 138; final lines 138.

Before:

```latex
The proof of Theorem~\ref{t:main} uses results of \S\ref{s:cut}--\S\ref{s:computer}; their proofs do not use \S\ref{s:frames}--\S\ref{s:mixing}, so the order of the argument is not circular.
```

After:

```latex
The proof of Theorem~\ref{t:main} uses results of \S\ref{s:cut}--\S\ref{s:computer}. Their proofs use earlier frame definitions and shell geometry, but do not use Theorem~\ref{t:main}, the conclusion of Theorem~\ref{t:mainW}, or any consequence of the window estimate. These dependencies are acyclic.
```

## R7-5 — Shared exact frame input

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: This duplicates R1-3: the required exact design fact lacked the promised locator. The same internal coordinate-and-moment proof resolves both findings once.

Changed locations: [sec2-frames-Q.tex](/home/ubuntu/aklt/manuscript-corrected/sec2-frames-Q.tex:63): 63–76.

`sec2-frames-Q.tex` — frozen lines 63; final lines 63–76.

Before:

```latex
Let $D_{\mathrm I} \subset \Sph$ be the twelve vertices of a regular icosahedron and $D_{\mathrm{II}} \subset \Sph$ the twenty normalized centres of its faces, the vertices of the dual dodecahedron. With uniform weights $w_{\mathrm I} \equiv 1/12$ and $w_{\mathrm{II}} \equiv 1/20$, both are spherical $5$-designs (see \cite{DGS77}; we also checked the moments up to degree $6$ numerically, with errors below $10^{-15}$ up to degree $5$), so both are frames. Both sets are invariant under $a \mapsto -a$. A direct computation shows that for $a \in D_{\mathrm I}$ and $b \in D_{\mathrm{II}}$,
```

After:

```latex
Let $D_{\mathrm I} \subset \Sph$ be the twelve vertices of a regular icosahedron and $D_{\mathrm{II}} \subset \Sph$ the twenty normalized centers of its faces, the vertices of the dual dodecahedron. Here is an exact verification of the design property. Put $\phi=(1+\sqrt5)/2$, and let $\operatorname{cyc}$ denote the three cyclic coordinate permutations, with independent indicated signs. In a common orientation the unnormalized vertex sets are
\begin{equation*}
I_0=\{\operatorname{cyc}(0,\pm1,\pm\phi)\},\qquad
D_0=\{(\pm1,\pm1,\pm1)\}\cup
\{\operatorname{cyc}(0,\pm\phi,\pm\phi^{-1})\},
\end{equation*}
and $D_{\mathrm I}=I_0/\sqrt{\phi+2}$, $D_{\mathrm{II}}=D_0/\sqrt3$. For each $b_0\in D_0$, the three $a_0\in I_0$ with $a_0\cdot b_0=1+\phi$ have pairwise dot product $\phi$ and sum $(1+\phi)b_0$, so these are the corresponding face-center directions. Both sets are invariant under independent coordinate sign changes and cyclic permutations. Using $\phi^2=\phi+1$, their uniform averages satisfy, for $i\ne j$,
\begin{equation*}
\frac1{|D|}\sum_{a\in D}a_i^2=\frac13,\qquad
\frac1{|D|}\sum_{a\in D}a_i^4=\frac15,\qquad
\frac1{|D|}\sum_{a\in D}a_i^2a_j^2=\frac1{15},
\quad D=D_{\mathrm I},D_{\mathrm{II}}.
\end{equation*}
Every monomial with an odd coordinate exponent has average zero. Together with the constant moment, these are all the moments through total degree $5$, and they equal the normalized spherical moments. Thus the uniform weights $w_{\mathrm I}\equiv1/12$ and $w_{\mathrm{II}}\equiv1/20$ make both sets spherical $5$-designs, and hence frames. Both sets are invariant under $a\mapsto-a$. The same coordinates give the following cross-frame inner products:
```

## FN-R1-square — Weighted squared modulus

kind: correction

Adjudication: `ADJ-MINOR` — CONFIRMED.

Counterexample or reason: Changing one spinor representative by exp(i*pi/8) can multiply the degree-four evaluation by i and its ordinary square by -1, while probabilities stay fixed. The Gibbs law uses the normalized squared modulus, reference weights, and checkerboard change of variables.

Changed locations: [sec1-intro-statement.tex](/home/ubuntu/aklt/manuscript-corrected/sec1-intro-statement.tex:24): 24.

`sec1-intro-statement.tex` — frozen lines 24; final lines 24.

Before:

```latex
\emph{From the quantum gap to a classical heat bath} (\S\ref{s:frames}). Replace each spin by the twelve vertices of an icosahedron on one sublattice and the twenty vertices of a dodecahedron on the other. Both are spherical $5$-designs, so the corresponding spin-$2$ coherent states form tight frames, and the frame map is an isometry from $\mathcal H_\Lambda$ into a space of functions of a finite-state configuration. The ground state $B$ becomes a nowhere-vanishing function whose square is a nearest-neighbour Gibbs measure $\mu_D$ with strictly positive weights. Theorem~\ref{t:QD} shows that $\gap(H_{L, N})$ is bounded below by a fixed multiple of the spectral gap of the single-site heat-bath dynamics of $\mu_D$, and that the ground state is unique.
```

After:

```latex
\emph{From the quantum gap to a classical heat bath} (\S\ref{s:frames}). Replace each spin by the twelve vertices of an icosahedron on one sublattice and the twenty vertices of a dodecahedron on the other. Both are spherical $5$-designs, so the corresponding spin-$2$ coherent states form tight frames, and the frame map is an isometry from $\mathcal H_\Lambda$ into a space of functions of a finite-state configuration. The frame image of $B$ is nowhere vanishing; its normalized squared modulus, weighted by the frame reference measure and followed by the checkerboard change of variables, gives the nearest-neighbor Gibbs measure $\mu_D$ with strictly positive weights. Theorem~\ref{t:QD} shows that $\gap(H_{L, N})$ is bounded below by a fixed multiple of the spectral gap of the single-site heat-bath dynamics of $\mu_D$, and that the ground state is unique.
```

