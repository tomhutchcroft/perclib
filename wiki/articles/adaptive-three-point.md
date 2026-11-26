---
{
  "id": "adaptive-three-point",
  "title": "Adaptive resampling and multipoint inequalities",
  "subtitle": "Shared exploration, independent continuations and mixed witnesses",
  "kind": "method",
  "category": "Inequalities",
  "summary": "Predictable sharing gives adaptive Harris and BK inequalities. Stopped depth-first searches then prove the three-point and higher-order product bounds.",
  "context": [
    "Independent Bernoulli coordinates on a finite set; probabilities may be zero or one.",
    "A coordinate is assigned to the shared set before either of its two states is revealed.",
    "The graph application uses an ordinary depth-first search, stopped at the first of two targets."
  ],
  "related": [
    "multipoint-trees",
    "disjoint-occurrence",
    "stopped-exploration",
    "cutoff-hydrodynamics"
  ],
  "sourceIds": [
    "gladkov-decision-trees-2024",
    "hutchcroft-lrp-2"
  ],
  "aliases": [
    "Gladkov inequality",
    "Delfino–Viti constant",
    "adaptive BK",
    "decision-tree Harris inequality",
    "higher-order Gladkov inequality"
  ],
  "prototypeUses": []
}
---

## Predictable sharing {#section-hybrid}

<p>Let $E$ be finite, let $\mu=\bigotimes_{e\in E}\operatorname{Bernoulli}(p_e)$, and let $X,Y$ be independent with law $\mu$. A decision tree queries previously unqueried coordinates. Before reading $(X_e,Y_e)$, it decides whether to put $e$ in a set $S$; both this decision and the next coordinate may depend on all previously revealed pairs. Coordinates left unqueried when the tree stops are outside $S$. Define</p>
<div class="math-display">$$H_e=\begin{cases}X_e&e\in S,\\Y_e&e\notin S,\end{cases}\qquad
H'_e=\begin{cases}Y_e&e\in S,\\X_e&e\notin S.\end{cases}$$</div>

<a id="tag-Q3MP" data-assertion="proposition" data-title="Predictable coordinate swaps preserve the product pair law"></a>
<p>The pair $(H,H')$ has law $\mu\otimes\mu$.</p>
<p><em>Proof.</em> Complete the tree by querying every remaining coordinate and assigning it outside $S$. The map $(X,Y)\mapsto(H,H')$ is invertible. At the first node its decision is known, so the corresponding output pair determines the input pair by either keeping or reversing its order. This recovers the next node. Repeating reconstructs the entire input and the path taken through the tree.</p>
<p>At every coordinate, swapping the two bits preserves their product weight: the weights of $01$ and $10$ are both $p_e(1-p_e)$. The bijection therefore preserves the weight of each pair of configurations, including zero-weight configurations when $p_e$ is an endpoint. This proves the assertion. Independent randomization of the tree is allowed by conditioning on its seed.</p>

## Positive association under sharing {#section-harris}

<a id="tag-26TT" data-assertion="theorem" data-title="Adaptive Harris inequality for two events with the same monotonicity"></a>
<p>If $A,B\subseteq\{0,1\}^E$ are both increasing or both decreasing, then</p>
<div class="math-display">$$\mathbb P(X\in A,\ H\in B)\geq\mu(A)\mu(B).$$</div>
<p><em>Proof.</em> Choose a deepest node that assigns its coordinate $e$ to $S$, and change only that assignment. Fix all bits except $X_e,Y_e$. Whether this node is reached is independent of those two bits: its preceding queries do not include $e$. If it is not reached, nothing changes. If it is reached, no later node assigns anything to $S$. Thus $H$ off $e$ is fixed, although subsequent query orders may depend on the two bits.</p>
<p>Let $a_i$ be the indicator of $A$ when $X_e=i$, and $b_i$ the indicator of $B$ when the hybrid bit at $e$ is $i$. Write $p=p_e$. Before the change, the conditional joint probability is $(1-p)a_0b_0+pa_1b_1$; afterwards it is $[(1-p)a_0+pa_1][(1-p)b_0+pb_1]$. Their difference is</p>
<div class="math-display">$$p(1-p)(a_1-a_0)(b_1-b_0)\geq0.$$</div>
<p>Remove shared assignments one by one. Once none remain, $H=Y$ is independent of $X$, giving the required product. This argument works for either common direction of monotonicity.</p>

## Disjointness only on shared coordinates {#section-bk}

<p>For an increasing event $A$, an open witness in a configuration $x$ is a set $I\subseteq\{e:x_e=1\}$ such that opening every coordinate of $I$ forces $A$. Every witness for an increasing event can be replaced by its open coordinates: the configuration opening precisely those coordinates already satisfies the original witness, and monotonicity handles all larger configurations.</p>
<p>Write $A\mathbin{\square_S}B$ for the event that there are open witnesses $I$ for $A$ in $X$ and $J$ for $B$ in $H$ with $I\cap J\subseteq E\setminus S$. Overlap is allowed where the two configurations use different copies of the coordinate. When $S=E$ this is ordinary disjoint occurrence; when $S=\varnothing$ it is $\{X\in A,Y\in B\}$.</p>

<a id="tag-7LLO" data-assertion="theorem" data-title="Adaptive BK inequality with overlap allowed only on independent coordinates"></a>
<p>For increasing events $A,B$ and every predictable sharing tree,</p>
<div class="math-display">$$\mathbb P(A\mathbin{\square_S}B)\leq\mu(A)\mu(B).$$</div>
<p><em>Proof.</em> Change a deepest shared assignment as in the preceding proof. On a fixed restriction off its coordinate $e$, suppose the node is reached, and let $S_0$ be the other shared coordinates. Define four zero-one quantities $k_0,k_A,k_B,k_{AB}$ by the existence of a pair of witnesses disjoint on $S_0$. In $k_0$, neither witness may use $e$; in $k_A$, only the witness for $A$ may use it; in $k_B$, only the witness for $B$ may use it; and in $k_{AB}$, both may use it. Every allowed use of $e$ treats its bit as open; the two configurations off $e$ remain fixed. Then</p>
<div class="math-display">$$k_0\leq k_A\wedge k_B,\qquad k_A\vee k_B\leq k_{AB}.$$</div>
<p>Before the change, $e$ is shared and cannot occur in both witnesses. The conditional probability is therefore $(1-p)k_0+p(k_A\vee k_B)$. Afterwards, the four bit pairs give</p>
<div class="math-display">$$(1-p)^2k_0+p(1-p)(k_A+k_B)+p^2k_{AB}.$$</div>
<p>The latter minus the former is</p>
<div class="math-display">$$p(1-p)(k_A\wedge k_B-k_0)+p^2(k_{AB}-(k_A\vee k_B))\geq0.$$</div>
<p>Thus removing the shared assignment can only increase the probability. Iterating leaves $S=\varnothing$, whose probability is $\mu(A)\mu(B)$. This also proves ordinary finite-coordinate BK by starting with every coordinate shared.</p>
<p>This four-case computation avoids transferring a coordinate from a witness for one event to a witness for another. The contradictory bit states in the source's proof of Theorem 4.3 are recorded in the <a href="/errata/gladkov-decision-trees-2024/">provisional errata</a>; the inequality itself is retained.</p>

## Two continuations of a stopped search {#section-stopped}

<a id="tag-LNMI" data-assertion="proposition" data-title="Stopped-leaf Cauchy–Schwarz bound for two continuations"></a>
<p>Run a finite decision tree using $X$ alone, put every queried coordinate in $S$, and stop. Let $R$ be any event determined by its leaf, and let $B\subseteq R$. With $H=X$ on $S$ and $H=Y$ elsewhere, if $\mu(R)&gt;0$, then</p>
<div class="math-display">$$\mathbb P(X\in B,H\in B)=\sum_{\ell\subseteq R}\delta_\ell q_\ell^2
\geq\frac{\mu(B)^2}{\mu(R)},\quad
\delta_\ell=\mathbb P(\text{leaf }\ell),\quad q_\ell=\mathbb P(B\mid\ell).$$</div>
<p>If $\mu(R)=0$, both the joint probability and $\mu(B)$ vanish. The lower bound still holds if the search continues with further predictable assignments while retaining its original shared coordinates, provided $B=R\cap C$ for an increasing or decreasing event $C$.</p>
<p><em>Proof.</em> A leaf fixes exactly the queried bits of $X$. Conditional on it, the two unqueried configurations are independent with the original product law. The hybrid has the same queried bits, so replaying the stopped search on it reaches the same leaf. The two conditional probabilities of $B$ are both $q_\ell$, proving the identity. Cauchy–Schwarz gives</p>
<div class="math-display">$$\left(\sum_{\ell\subseteq R}\delta_\ell q_\ell\right)^2
\leq\left(\sum_{\ell\subseteq R}\delta_\ell\right)
\left(\sum_{\ell\subseteq R}\delta_\ell q_\ell^2\right).$$</div>
<p>The two sums on the left and in the first factor are $\mu(B)$ and $\mu(R)$. For the continued tree, additionally condition on any already revealed bits of $Y$. The remaining bits are still independent products. On a leaf in $R$, the two events are the same monotone section of $C$, so <a href="/tag/26TT/">adaptive Harris</a> gives a conditional lower bound $q_\ell^2$. Integrating and applying the same Cauchy–Schwarz inequality proves the last assertion.</p>
<p>The direction is a lower bound, generally strict. For example, take the path $a-b-c$ with both edges having probability $1/2$, explore the entire cluster of $a$, and independently resample unqueried edges. Let $R$ mean that the three vertices are not all connected. For either $B=\{a,b,c\text{ all separate}\}$ or $B=\{a\text{ separate from the connected pair }b,c\}$, one has $\mu(R)=3/4$, $\mu(B)=1/4$, and the joint probability is $1/8&gt;1/12=\mu(B)^2/\mu(R)$. This gives the explicit correction to Corollary 5.3 in the errata.</p>

## The stopped depth-first path {#section-dfs}

<p>Now let $E$ be the edges of a finite graph and let $a,b,c$ be distinct. Fix an ordering of the neighbours at each vertex. Starting at $a$, perform recursive depth-first search in $X$: at the current vertex, query an unqueried incident edge, and immediately descend along it if it is open and leads to an unvisited vertex. Return to the parent only after all incident edges have been processed. Stop immediately upon first visiting $b$ or $c$, or when the search finishes. Every queried edge is shared. Write $R_b,R_c$ for the two successful stopping outcomes and $D$ for the event that $a,b,c$ lie in one cluster.</p>

<a id="tag-VN5Z" data-assertion="proposition" data-title="The stopped DFS path supplies two mixed connection witnesses"></a>
<p>For the hybrid associated to this search,</p>
<div class="math-display">$$\{R_b, X\in D, H\in D\}
\subseteq (ac\mathbin{\square_S}bc)\cup(bc\mathbin{\square_S}ac),$$</div>
<p>where $uv$ denotes the connection event between $u$ and $v$. With $b,c$ interchanged,</p>
<div class="math-display">$$\{R_c, X\in D, H\in D\}
\subseteq (ab\mathbin{\square_S}bc)\cup(bc\mathbin{\square_S}ab).$$</div>
<p><em>Proof.</em> On $R_b$, the active recursion stack is a simple open path $P$ from $a$ to $b$. All its edges are shared. Every previously visited vertex outside $P$ has been completely processed; call this set $Q$. All edges incident to $Q$ have been queried. Any such edge from $Q$ to an unvisited vertex is closed, since otherwise the search would have visited that vertex before returning from $Q$. Every queried open edge has both endpoints in $P\cup Q$. These properties hold in both $X$ and $H$, which agree on every queried edge.</p>
<p>The vertex $c$ is unvisited. In either configuration, a path from $c$ to $P$ cannot enter $Q$ before meeting $P$: its first entry into the visited set through $Q$ would use a shared closed edge. Take the initial segment up to its first intersection with $P$. This segment uses no shared edge, since every shared open edge has two visited endpoints.</p>
<p>Choose such segments in $X$ and $H$, ending at $v_X,v_H\in P$. If $v_X$ precedes $v_H$ along $P$ from $a$ to $b$, join the first segment to the $a$--$v_X$ portion of $P$ and the second to the $v_H$--$b$ portion. They witness $ac$ in $X$ and $bc$ in $H$, with disjoint shared edges. If the order is reversed, they witness $bc$ in $X$ and $ac$ in $H$. Equal endpoints cause no difficulty: the two portions of $P$ share a vertex but no edge. The two off-path segments may overlap, entirely outside $S$, exactly as mixed disjoint occurrence permits. The proof on $R_c$ is the same with the targets interchanged.</p>

## The product bound {#section-three-point}

<a id="tag-C7UK" data-assertion="theorem" data-title="Finite Gladkov three-point product and union bounds"></a>
<p>For independent bond percolation on a finite graph and distinct vertices $a,b,c$,</p>
<div class="math-display">$$\mathbb P(D)^2\leq8\tau(a,b)\tau(a,c)\tau(b,c),\qquad
\mathbb P(D)^2\leq2\mathbb P(ab\cup ac)^2\tau(b,c).$$</div>
<p>All edge probabilities in $[0,1]$ are allowed.</p>
<p><em>Proof.</em> Put $r_b=\mathbb P(R_b)$ and $t_b=\mathbb P(R_b\cap D)$, with analogous notation for $c$. For $r_b&gt;0$, the stopped-leaf bound and the mixed-witness inclusion give</p>
<div class="math-display">$$\frac{t_b^2}{r_b}\leq\mathbb P(R_b,X\in D,H\in D)
\leq2\tau(a,c)\tau(b,c),$$</div>
<p>where the last inequality is <a href="/tag/7LLO/">adaptive BK</a> applied to the two events in the union. The same conclusion $t_b\leq\sqrt{2r_b\tau(a,c)\tau(b,c)}$ holds when $r_b=0$, since then $t_b=0$. Interchanging the targets and using $r_b\leq\tau(a,b)$ and $r_c\leq\tau(a,c)$ yields</p>
<div class="math-display">$$\begin{aligned}
\mathbb P(D)=t_b+t_c
&\leq\sqrt{2r_b\tau(a,c)\tau(b,c)}+\sqrt{2r_c\tau(a,b)\tau(b,c)}\\
&\leq2\sqrt{2\tau(a,b)\tau(a,c)\tau(b,c)}.
\end{aligned}$$</div>
<p>Squaring proves the first inequality without dividing by any connection probability.</p>
<p>For the second, take $R=R_b\cup R_c=ab\cup ac$. The two DFS inclusions together imply</p>
<div class="math-display">$$\{X\in D,H\in D\}
\subseteq ((ab\cup ac)\mathbin{\square_S}bc)\cup(bc\mathbin{\square_S}(ab\cup ac)).$$</div>
<p>The stopped-leaf lower bound is $\mathbb P(D)^2/\mathbb P(R)$ when $\mathbb P(R)&gt;0$, and adaptive BK bounds the joint probability above by $2\mathbb P(R)\tau(b,c)$. If $\mathbb P(R)=0$, then $\mathbb P(D)=0$. This proves the second inequality in every case.</p>
<p>This supplies the finite theorem previously cited in <a href="/tag/87RB/">87RB</a>. Its existing finite-witness exhaustion and repeated-vertex argument now give the countable-model result from the proofs here, without local finiteness or finite susceptibility. Together with <a href="/tag/MRZO/">the sharp averaged two-point bound</a>, it supplies both remaining cited probability inputs in <a href="/tag/X8F6/">the radial good-scale assembly</a>. The all-scale fictitious estimates and the critical-dimensional hydrodynamic limit remain separate arguments.</p>

## Stopping with one marked vertex left {#section-many-witnesses}

<p>Let $A$ be a set of $n\geq3$ marked vertices in a finite graph, fix $a_0\in A$, and write $D_F$ for the event that all vertices of a finite set $F$ lie in one cluster. Run the same recursive DFS from $a_0$, now stopping immediately after it has visited $n-1$ vertices of $A$, or when its search is exhausted. Let $R_a$ be the outcome in which $a\in A\setminus\{a_0\}$ is the one marked vertex still unvisited. As before, share every queried edge and independently resample the rest.</p>

<a id="tag-9KP0" data-assertion="proposition" data-title="An all-but-one DFS gives a nontrivial marked partition with mixed witnesses"></a>
<p>On $R_a\cap\{X\in D_A,H\in D_A\}$, there is a nonempty set $U\subseteq A\setminus\{a_0,a\}$ such that either</p>
<div class="math-display">$$D_{A\setminus U}\mathbin{\square_S}D_{U\cup\{a\}}
\quad\hbox{or}\quad
D_{U\cup\{a\}}\mathbin{\square_S}D_{A\setminus U}$$</div>
<p>occurs.</p>
<p><em>Proof.</em> Let $T$ be the discovery tree on all visited vertices and let $P$ be its active stack, a path from $a_0$ to the last discovered marked vertex $b$. Every vertex of $T$ outside $P$ has been completely processed. Exactly as in <a href="/tag/VN5Z/">VN5Z</a>, paths from the unvisited vertex $a$ to $P$ in the two configurations have initial segments using only unshared edges and meeting $T$ only at their endpoints $v_X,v_H\in P$.</p>
<p>Suppose $v_X$ precedes $v_H$ along $P$. If $v_X$ is internal to $P$, split $T$ at $v_X$: put the component of $T\setminus\{v_X\}$ containing $b$, together with $v_X$, in $T_R$; put all other components and $v_X$ in $T_L$. These two connected subtrees meet only at $v_X$ and have disjoint edge sets. Assign any mark at $v_X$ to the left side. The resulting marked partition has $a_0$ on the left and $b$ on the right; write $U$ for the right-hand marks. The first continuation segment, together with $T_L$, witnesses $D_{A\setminus U}$ in $X$. Since $v_H\in T_R$, the second segment and $T_R$ witness $D_{U\cup\{a\}}$ in $H$. Their shared edges are disjoint.</p>
<p>If $v_X=a_0$, instead take $T_L$ to be the single root and $T_R=T$, assigning only $a_0$ to the left. If $v_X=b$, then also $v_H=b$; take $T_L=T$ and $T_R$ to be the single vertex $b$, assigning only $b$ to the right. Both partitions are nontrivial because $a_0\ne b$. If $v_H$ precedes $v_X$, interchange the configurations. In every case the off-tree paths can overlap only on unshared coordinates, as required.</p>

## The higher-order inequality {#section-higher-order}

<a id="tag-5BQO" data-assertion="theorem" data-title="Higher-order Gladkov inequality with a singleton part"></a>
<p>For independent bond percolation on a countable vertex set, a finite marked set $A$ of size $n\geq3$, and any fixed $a_0\in A$, write $\tau(F)=\mathbb P(D_F)$. Then</p>
<div class="math-display">$$\tau(A)^2\leq
2(n-1)\sum_{a\in A\setminus\{a_0\}}\tau(A\setminus\{a\})
\sum_{\varnothing\ne U\subseteq A\setminus\{a_0,a\}}
\tau(U\cup\{a\})\tau(A\setminus U).$$</div>
<p>Consequently,</p>
<div class="math-display">$$\tau(A)^2\leq2(n-1)^2(2^{n-2}-1)
\max_{A=A_1\sqcup A_2\sqcup A_3}
\tau(A_1\cup A_2)\tau(A_2\cup A_3)\tau(A_3\cup A_1),$$</div>
<p>where the maximum is over nonempty parts. It is enough to maximize over partitions with $A_3=\{a\}$ for some $a\ne a_0$, and $a_0\in A_1$. In particular, the larger constant $4(n-1)^2(2^{n-2}-1)$ stated in Theorem II.3.1 is valid.</p>
<p><em>Proof.</em> First take a finite graph and the all-but-one DFS. Put $r_a=\mathbb P(R_a)$ and $t_a=\mathbb P(R_a\cap D_A)$. The stopped-leaf bound gives</p>
<div class="math-display">$$t_a^2\leq r_a\mathbb P(R_a,X\in D_A,H\in D_A),$$</div>
<p>including $r_a=0$. By <a href="/tag/9KP0/">the marked partition</a>, a union bound, and <a href="/tag/7LLO/">adaptive BK</a>,</p>
<div class="math-display">$$\mathbb P(R_a,X\in D_A,H\in D_A)
\leq2\sum_{\varnothing\ne U\subseteq A\setminus\{a_0,a\}}
\tau(U\cup\{a\})\tau(A\setminus U).$$</div>
<p>The factor two accounts for the two orders of the attachment points. The successful leaf event $R_a$ implies that all of $A\setminus\{a\}$ have been connected by the discovery tree, so $r_a\leq\tau(A\setminus\{a\})$. On $D_A$, exactly one of the $n-1$ outcomes $R_a$ occurs. Hence $\tau(A)=\sum_a t_a$, and Cauchy–Schwarz gives $\tau(A)^2\leq(n-1)\sum_a t_a^2$. Substitution proves the first estimate.</p>
<p>For each term take $A_1=A\setminus(U\cup\{a\})$, $A_2=U$, and $A_3=\{a\}$. These are nonempty, with $a_0\in A_1$, and their three pairwise unions are precisely the three sets in that term. There are $(n-1)(2^{n-2}-1)$ terms. Bounding each by the maximum proves the second estimate.</p>
<p>For a countable model, exhaust the vertices by finite sets containing $A$, closing all edges outside each restriction. Every connection of a finite marked set has a finite path witness, so all probabilities in these inequalities increase to their full-model values. There are finitely many subsets and partitions involved; pass to the limit in the finite sums and maxima. No local finiteness or susceptibility assumption is used. With $n=3$, the coefficient is eight, agreeing with the three-point theorem.</p>
<p>This completes the probability input in <a href="/tag/C4A5/">the recursive geometric estimate</a> and <a href="/tag/2GTM/">the four-point matching consequence</a>. Their existing conditional statements and constants remain unchanged. The source's proof ends with the smaller factor two also obtained here; it implies the factor four in its statement.</p>

## Four marked vertices {#section-four-point}

<a id="tag-MTVN" data-assertion="corollary" data-title="Unconditional four-point matching bound with the sharpened prefactor"></a>
<p>For four distinct vertices, put $t_{ij}=\tau(x_i,x_j)$ and $t_A=\mathbb P(x_1,x_2,x_3,x_4\text{ lie in one cluster})$. Then</p>
<div class="math-display">$$t_A^4\leq186624\left(\prod_{1\leq i&lt;j\leq4}t_{ij}\right)
\max\{t_{12}t_{34},t_{13}t_{24},t_{14}t_{23}\}.$$</div>
<p><em>Proof.</em> A nonempty three-part partition of four marks has sizes $1,1,2$. For singleton marks $a,b$ and the other two marks $c,d$, its product is $t_{ab}t_{acd}t_{bcd}$. Applying the three-point theorem to both triple factors gives</p>
<div class="math-display">$$(t_{ab}t_{acd}t_{bcd})^2
\leq64\left(\prod_{i&lt;j}t_{ij}\right)t_{ab}t_{cd}.$$</div>
<p>The higher-order theorem has coefficient $2\cdot3^2\cdot(2^2-1)=54$. Squaring it, inserting this estimate and taking the maximum over the three complementary pairings gives $54^2\cdot64=186624$. The argument includes zero pair probabilities. The counterexample in <a href="/tag/2GTM/">2GTM</a> still shows why one prescribed pairing cannot replace the maximum.</p>


## Three resampling orders {#section-three-resamplings}

<p>Fix three distinct marked vertices $a,b,c$ in a finite graph. Write $D$ for the event that all three are connected and $F$ for the event that all three lie in different clusters. The other three possible partitions are denoted $ab|c$, $ac|b$ and $a|bc$. Set</p>
<div class="math-display">$$t=\mathbb P(D),\quad s=\mathbb P(F),\quad
x=\mathbb P(ab|c),\quad y=\mathbb P(ac|b),\quad z=\mathbb P(a|bc),\qquad s+t+x+y+z=1.$$</div>
<p>Let $R_a$ mean that $a$ is disconnected from both $b$ and $c$, and define $R_b,R_c$ similarly. Their probabilities are</p>
<div class="math-display">$$r_a=s+z,\qquad r_b=s+y,\qquad r_c=s+x.$$</div>
<p>In particular, $R_a$ is the intersection of two nonconnection events. Their union would instead be $D^c$.</p>
<p>Let $X,Y$ be independent percolation configurations. In each of the following schemes, explore whole $X$-clusters in the displayed order. Exploring a cluster queries every incident edge, including its closed boundary. Already queried edges keep their previous assignment. An edge first queried in a shared stage enters $S$; one first queried in an unshared stage does not. The assigned stage is known before its state is queried, so each scheme is a predictable sharing tree. Leave all remaining edges unshared.</p>
<div class="math-display">$$\begin{array}{c|ccc}
&amp;\text{first cluster}&amp;\text{second cluster}&amp;\text{third cluster}\\
S_1&amp;c\text{ shared}&amp;a\text{ unshared}&amp;b\text{ shared}\\
S_2&amp;b\text{ shared}&amp;a\text{ unshared}&amp;c\text{ shared}\\
S_3&amp;a\text{ unshared}&amp;b\text{ shared}&amp;c\text{ shared}
\end{array}$$</div>
<p>Write $H_i=X$ on $S_i$ and $H_i=Y$ elsewhere, and let $H'_i$ be the complementary hybrid. Put $E_1=\{X\in F,H_1\in ab\}$, $E_2=\{X\in F,H_2\in ac\}$ and $E_3=\{X\in F,H_3\in ab\cup ac\}$.</p>

<a id="tag-HKLH" data-assertion="proposition" data-title="Three cluster-resampling orders give a path inclusion and an independent-hybrid lower bound"></a>
<p>With these conventions,</p>
<div class="math-display">$$E_3\subseteq E_1\cup E_2,\qquad
\mathbb P(E_3)\geq s-r_a^2.$$</div>
<p>On $\{X\in F\}$, $H_1\in R_c$ and $H_2\in R_b$.</p>
<p><em>Proof.</em> On $X\in F$, denote the three disjoint $X$-clusters by $A,B,C$. The only difference between $S_1$ and $S_3$ is that edges joining $A$ to $C$ are shared in $S_1$ and unshared in $S_3$. These edges are closed in $X$. Likewise $S_2$ adds to $S_3$ the edges joining $A$ to $B$. This follows by assigning each edge incident to the three clusters at its first queried stage.</p>
<p>If $H_3$ connects $a$ to $b$ or $c$, take an open path from $a$ and stop when it first enters $B\cup C$. If it enters $B$, that path avoids $C$, hence uses no edge whose state differs between $H_3$ and $H_1$. It remains open in $H_1$. All edges internal to $B$ are shared in both hybrids, so the path can be continued inside $B$ to $b$. This gives $E_1$. If the first entrance is in $C$, the same argument with $H_2$ gives $E_2$.</p>
<p>In the third scheme every edge incident to $A$ is unshared. Thus $H'_3$ agrees with $X$ on the internal edges and the entire closed boundary of $A$, and its $a$-cluster is exactly $A$. Consequently</p>
<div class="math-display">$$\{X\in F,H_3\in R_a\}\subseteq\{H'_3\in R_a,H_3\in R_a\}.$$</div>
<p>The two complementary hybrids are independent with the original law by Q3MP. The probability on the right is $r_a^2$. Subtracting the left-hand probability from $s$ proves the lower bound on $E_3$. Finally, the first stage of $S_1$ preserves all edges incident to $C$, so $H_1$ has the same $c$-cluster as $X$; this proves $H_1\in R_c$. The argument for $H_2$ is identical.</p>

## The asymmetric separation inequality {#section-separation-inequality}

<a id="tag-VPUL" data-assertion="theorem" data-title="Asymmetric inequality for the five three-vertex cluster partitions"></a>
<p>For independent bond percolation on a countable graph and three distinct vertices, with the partition probabilities defined above,</p>
<div class="math-display">$$s+r_a^2\geq\frac{s^2}{r_b}+\frac{s^2}{r_c}.$$</div>
<p>The two other inequalities obtained by permuting $a,b,c$ also hold. Set $s^2/r=0$ when $r=0$; this case forces $s=0$. Arbitrary edge probabilities in $[0,1]$ are allowed, with no local-finiteness or susceptibility assumption.</p>
<p><em>Proof.</em> First work on a finite graph. In scheme $S_1$, stop after exploring the $c$-cluster. The event $R_c$ is determined at this stop, and $F\subseteq R_c$. The event $F$ is decreasing. Hence the continued-tree form of <a href="/tag/LNMI/">LNMI</a> gives, when $r_c&gt;0$,</p>
<div class="math-display">$$\mathbb P(X\in F,H_1\in F)\geq\frac{s^2}{r_c}.$$</div>
<p>On $X\in F$, the $c$-cluster is preserved, so $H_1$ either has all three marks separate or connects $a$ to $b$. Therefore $\mathbb P(E_1)\leq s-s^2/r_c$. The same reasoning gives $\mathbb P(E_2)\leq s-s^2/r_b$. These bounds include zero denominators under the stated convention. Apply HKLH and the union bound to obtain</p>
<div class="math-display">$$s-r_a^2\leq\mathbb P(E_3)\leq\mathbb P(E_1)+\mathbb P(E_2)
\leq2s-\frac{s^2}{r_c}-\frac{s^2}{r_b}.$$</div>
<p>Rearranging proves the finite statement.</p>
<p>For a countable graph, exhaust the vertices by finite sets containing the three marks and close all edges outside each restriction. Every connection has a finite path witness, so the partition of the three marks eventually agrees, configuration by configuration, with its full-graph partition. Thus all five partition probabilities converge. The ratios also converge: if a limiting denominator is positive this is ordinary continuity, while if it is zero, $0\leq s_n^2/r_n\leq r_n\to0$. Pass to the limit in the finite inequality.</p>
<p>This proves the intended asymmetric form of source Lemma 1.2, with intersections in the definitions of $R_a,R_b,R_c$. The literal unions printed in its statement are all $D^c$ and do not give the partition-probability identities used later in section 7. The <a href="/errata/gladkov-decision-trees-2024/#separation-events-and-directions">provisional repair</a> also reverses the first coupling bound in section 7.1 and keeps the Cauchy–Schwarz steps as inequalities. The three-point product theorem and all earlier tagged statements are unchanged.</p>

## Rare two-cluster partitions {#section-rare-partitions}

<a id="tag-QY7X" data-assertion="corollary" data-title="Quantitative constraints when two-cluster partition probabilities are small"></a>
<p>For the same model,</p>
<div class="math-display">$$t s^2\leq4\max\{x,y\}.$$</div>
<p>In particular, for every $\varepsilon&gt;0$,</p>
<div class="math-display">$$x&lt;\frac{\varepsilon^3}{4},\quad y&lt;\frac{\varepsilon^3}{4}
\quad\Longrightarrow\quad t&lt;\varepsilon\ \text{or}\ s&lt;\varepsilon.$$</div>
<p>There is also the one-sided estimate</p>
<div class="math-display">$$t\leq8\tau(a,c)\tau(b,c)+\sqrt{8x}.$$</div>
<p><em>Proof.</em> Put $m=\max\{x,y\}$. If $s=0$ or $t=1$, the first claim is immediate. Otherwise $s&gt;0$ and $t&lt;1$. Apply VPUL with $b$ as the distinguished mark. Since $r_b=s+y\leq s+m$, $r_c=s+x\leq s+m$ and $r_a=s+z\leq1-t$,</p>
<div class="math-display">$$s+(s+m)^2\geq\frac{s^2}{1-t}+\frac{s^2}{s+m}.$$</div>
<p>Subtract the last term, multiply by $1-t$, and rearrange:</p>
<div class="math-display">$$t(s+m)^2\leq\frac{m s(1-t)}{s+m}+2ms+m^2
\leq m(1-t)+2ms+m^2\leq4m.$$</div>
<p>This proves $t s^2\leq4m$, including $m=0$. If $s,t\geq\varepsilon$, its left side is at least $\varepsilon^3$, giving the stated implication.</p>
<p>For the last bound, let $K=8\tau(a,c)\tau(b,c)\leq8$. The three-point theorem C7UK, with its countable extension 87RB, gives $t^2\leq K\tau(a,b)=K(t+x)$. If $t&gt;K$, then $(t-K)^2\leq t(t-K)\leq Kx\leq8x$; if $t\leq K$, the conclusion is immediate. Thus the small-$x$ implication in source section 7.3 follows with the explicit choice $x&lt;\varepsilon^2/8$.</p>

## Bounding the two extreme partitions {#section-extreme-partition-cap}

<a id="tag-5EMI" data-assertion="corollary" data-title="A cubic bound on the smaller all-connected and all-separated probabilities"></a>
<p>Let $\rho$ be the unique root in $(1/3,1/2)$ of</p>
<div class="math-display">$$P(u)=u^3-42u^2+12u+1.$$</div>
<p>Then $\min\{s,t\}\leq\rho=0.3556691089\ldots$ for every model in VPUL.</p>
<p><em>Proof.</em> Put $m=\min\{s,t\}$. The claim is immediate if $m\leq1/3$, so assume $m&gt;1/3$. Write $R=r_a+r_b+r_c=1+2s-t$ and choose the labels so that $r=r_a$ is the smallest of the three, hence $s\leq r\leq R/3$. By VPUL and the harmonic-mean inequality,</p>
<div class="math-display">$$s+r^2\geq\frac{s^2}{r_b}+\frac{s^2}{r_c}\geq\frac{4s^2}{R-r}.$$</div>
<p>Thus $G(r)=(s+r^2)(R-r)-4s^2\geq0$. On $[s,R/3]$,</p>
<div class="math-display">$$G''(r)=2R-6r\geq0,\qquad
G'(s)=s(1+s-2t)\geq s(3s-1)&gt;0,$$</div>
<p>where $t\leq1-s$ was used. Consequently $G(R/3)\geq0$, or</p>
<div class="math-display">$$s+\frac{R^2}{9}-\frac{6s^2}{R}\geq0.$$</div>
<p>For fixed $s$ the expression on the left increases with $R$. Since $t\geq m$, replace $R$ by $R_m=1+2s-m$ to get $H(s,m)=s+R_m^2/9-6s^2/R_m\geq0$. For $m\leq s\leq1-m$, put $k=s/R_m$. Then $1/4\leq k\leq1/3$ and $R_m\leq2$, so</p>
<div class="math-display">$$\frac{\partial H}{\partial s}
=1+\frac{4R_m}{9}-12k+12k^2
\leq1+\frac89-\frac94=-\frac{13}{36}&lt;0.$$</div>
<p>It follows that $0\leq H(s,m)\leq H(m,m)=P(m)/(9(1+m))$. The polynomial is strictly decreasing on $[1/3,1/2]$, is positive at $1/3$ and negative at $1/2$. Since $m\leq1/2$, the inequality $P(m)\geq0$ gives $m\leq\rho$.</p>
<p>This supplies the optimization behind section 7.3. The symmetric probability vector $s=t=\rho$, $x=y=z=(1-2\rho)/3$ saturates the three inequalities of VPUL, showing that this bound is sharp for those inequalities and probability normalization alone. No claim is made that this vector is realized by a percolation model, or that the bound is the optimal percolation constant.</p>


## Comparing adaptive sampling laws {#section-sampling-comparison}

<a id="tag-9GXY" data-assertion="theorem" data-title="A coordinatewise comparison of sections bounds every predictable sampling tree"></a>
<p>Let $E$ be finite, and for each $e\in E$ let $\mu_e,\nu_e$ be probability laws on a finite alphabet $\Omega_e$. Different types of symbols can be distinguished by labels in this common alphabet. Suppose $A\subseteq\prod_e\Omega_e$ satisfies, for every $e$ and every fixed assignment $z$ off $e$,</p>
<div class="math-display">$$\sum_u\mu_e(u)\mathbf1_A(z,u)\leq\sum_u\nu_e(u)\mathbf1_A(z,u).$$</div>
<p>A predictable tree chooses an unassigned coordinate and one of its two laws from the previously generated values, then draws a fresh value from that law. Suppose every coordinate is assigned exactly once. If $Z$ is the resulting configuration, then</p>
<div class="math-display">$$\left(\bigotimes_e\mu_e\right)(A)\leq\mathbb P(Z\in A)\leq\left(\bigotimes_e\nu_e\right)(A).$$</div>
<p>Independent randomization of the tree is permitted. No monotonicity order on the alphabets is required.</p>
<p><em>Proof.</em> Induct on the number of coordinates still unassigned, with the previously generated values fixed. There is nothing to prove when none remain. Suppose the tree next chooses $e$ and a law $\lambda_e\in\{\mu_e,\nu_e\}$. Conditional on the new value $u$, the induction hypothesis bounds the continuation below by the section probability with every remaining coordinate drawn independently from its $\mu$ law. Average this bound over $\lambda_e$. If $\lambda_e=\mu_e$, it is the required product probability. If $\lambda_e=\nu_e$, integrate the displayed section inequality over the independent $\mu$ values of the other coordinates to obtain the same lower bound. The upper bound follows with all remaining coordinates drawn from their $\nu$ laws and the same section inequality. Sections obtained by fixing earlier coordinates retain the hypothesis, so the induction applies at every node. Finally condition on an independent seed for a randomized tree.</p>
<p>This proves Main Lemma 8.1 without identifying different continuation paths. In the source's deepest-node proof, the replacement difference must have the sign of $\nu_e-\mu_e$ and be averaged over the remaining coordinates; the printed formula reverses those laws. The <a href="/errata/gladkov-decision-trees-2024/#sampling-comparison-sign">provisional correction</a> leaves the lemma's conclusion intact.</p>

## Shared capacities and independent labels {#section-capacity-comparison}

<p>For increasing events $A,B\subseteq\{0,1\}^E$, a pair of open witnesses $I,J$ may be supported by two types of coordinate. An unlabelled capacity $c_e\in\{0,1,2\}$ allows the coordinate in neither witness, in at most one witness, or in both, according to its capacity. A labelled pair $(u_e,v_e)\in\{0,1\}^2$ allows it in $I$ only if $u_e=1$, and in $J$ only if $v_e=1$. Let $A\bowtie B$ mean that such witnesses exist. For finitely many pairs of increasing events, put $F=\bigcup_{i=1}^m(A_i\bowtie B_i)$.</p>

<a id="tag-3CE7" data-assertion="theorem" data-title="The admissible capacity laws for adaptive unions of two-witness events"></a>
<p>At coordinate $e$, let the labelled law consist of two independent Bernoulli$(p_e)$ bits. Let the unlabelled law satisfy</p>
<div class="math-display">$$\mathbb P(c_e=0)=1-a_e,\quad\mathbb P(c_e=1)=a_e-b_e,\quad
\mathbb P(c_e=2)=b_e,\qquad
0\leq b_e\leq a_e\leq p_e,\quad b_e\leq p_e^2.$$</div>
<p>For every predictable tree choosing between these two laws,</p>
<div class="math-display">$$\mathbb P_{\mathrm{cap}}(F)\leq\mathbb P_{\mathrm{tree}}(F)
\leq(\mu\otimes\mu)\!\left(\bigcup_{i=1}^m A_i\times B_i\right),\qquad
\mu=\bigotimes_e\operatorname{Bernoulli}(p_e).$$</div>
<p>The subscript cap means independent capacities at every coordinate. The restrictions $a_e\leq p_e$ and $b_e\leq p_e^2$ are necessary for this comparison to hold for every increasing witness event, already on one coordinate.</p>
<p><em>Proof.</em> Fix all coordinates except $e$. The capacities for which $F$ holds form an upper subset of $\{0,1,2\}$. If it is empty, its probability is zero. If it is $\{2\}$, a successful witness pair is also supported by the labelled state $11$, whose probability $p_e^2$ is at least $b_e$. If it is $\{1,2\}$, a pair witnessing success at capacity one uses $e$ in exactly one witness: using neither would give success at zero, and using both is forbidden. The same pair is therefore supported by $10$ and $11$, or by $01$ and $11$, with total probability $p_e\geq a_e$. This reasoning uses one successful index $i$ and so applies unchanged to the union. Finally, if zero is successful, a witness pair avoiding $e$ succeeds at every labelled state, giving probability one. These are precisely the section comparisons required by 9GXY.</p>
<p>With labelled states everywhere, existence of the two open witnesses is equivalent to membership in $A_i\times B_i$, since the events are increasing. This identifies the upper endpoint. For necessity, take one coordinate, let $A$ require it to be open, and let $B$ be the whole space. The two endpoint probabilities are $a$ and $p$. Taking both events to require the coordinate instead gives endpoint probabilities $b$ and $p^2$.</p>
<p>The choice $a_e=p_e$, $b_e=0$ gives the finite-family BK inequality</p>
<div class="math-display">$$\mu\!\left(\bigcup_i A_i\mathbin{\square}B_i\right)
\leq(\mu\otimes\mu)\!\left(\bigcup_i A_i\times B_i\right).$$</div>
<p>The largest permitted capacity law has probabilities $1-p$, $p(1-p)$ and $p^2$ at $0,1,2$. This is a corrected version of source Theorems 8.2 and 8.4. Their printed probabilities $(1-p)^2$, $2p(1-p)$ and $p^2$ have $a=2p-p^2&gt;p$ for $0&lt;p&lt;1$, so the one-coordinate test disproves the stated comparison. For example, at $p=1/2$ its endpoints are $3/4$ and $1/2$. The <a href="/errata/gladkov-decision-trees-2024/#capacity-law">replacement</a> changes the sampling law; it does not prove the theorem with the printed law.</p>

## Three colour-induced configurations {#section-colour-comparison}

<a id="tag-F2TD" data-assertion="theorem" data-title="Adaptive even-parity sampling preserves pairwise independence and bounds triple increasing events"></a>
<p>At each coordinate of a finite set, choose predictably between the uniform law $\eta$ on $\{000,011,101,110\}$ and the uniform law $\pi$ on all eight bit triples. Write $Z_1,Z_2,Z_3$ for the three resulting Boolean configurations, and let $\mu$ be the fair product law on $\{0,1\}^E$. Each pair $(Z_i,Z_j)$ has law $\mu\otimes\mu$. For increasing events $U,V,W$,</p>
<div class="math-display">$$\eta^{\otimes E}(U\times V\times W)
\leq\mathbb P(Z_1\in U,Z_2\in V,Z_3\in W)
\leq\mu(U)\mu(V)\mu(W).$$</div>
<p><em>Proof.</em> Both coordinate laws have the same uniform marginal on each pair of bits. For an arbitrary event depending only on two configurations, their section probabilities are therefore equal. Applying 9GXY in both directions identifies its probability with that under $\pi^{\otimes E}$, proving the pair law.</p>
<p>For the triple event, fix all other coordinates. Each of the three sections is empty, the whole bit space, or $\{1\}$, by monotonicity. An empty section makes both probabilities zero. Otherwise let $k$ be the number of required ones. For $k=0,1,2$ the probabilities under $\eta$ and $\pi$ agree and are $2^{-k}$. For $k=3$ they are zero and $1/8$. Thus every section has at least as much mass under $\pi$, and 9GXY gives the bounds.</p>
<p>In the lower product law, the third configuration is the coordinatewise exclusive-or of the first two. Equivalently, independently colour each edge with one of four equally likely colours $a,b,c,d$ and take the indicators of its membership in $E_{ab},E_{ac},E_{bc}$; these are exactly the four even-parity triples. The lower-endpoint inequality therefore proves the finite coloured-percolation result in source Theorem 8.5, while the full statement proves its adaptive Theorem 8.6.</p>
<p>The normalized laws put mass $1/4$ on each even-parity state and $1/8$ on each of the eight states. The source's setup interchanges these weights and mislabels the support; its subsequent case calculations use the normalized values. The <a href="/errata/gladkov-decision-trees-2024/#parity-law-normalization">provisional erratum</a> also replaces the section identity by $X_\eta=X_\pi\cap\{000,011,101,110\}$.</p>

## A comparison of triple mixtures {#section-triple-mixtures}

<a id="tag-JOJ1" data-assertion="theorem" data-title="Adaptive comparison of coordinatewise triple mixtures for increasing events"></a>
<p>On one bit triple, define the two probability laws</p>
<div class="math-display">$$\begin{aligned}
\sigma&amp;=\frac23\operatorname{Unif}\{000,111\}+\frac13\operatorname{Unif}\{0,1\}^3,\\
\lambda&amp;=\frac13\operatorname{Unif}\{000,011,100,111\}
+\frac13\operatorname{Unif}\{000,010,101,111\}
+\frac13\operatorname{Unif}\{000,001,110,111\}.
\end{aligned}$$</div>
<p>For increasing events $U,V,W$ on a finite Boolean product and any predictable sampling tree choosing between these laws at each coordinate,</p>
<div class="math-display">$$\sigma^{\otimes E}(U\times V\times W)
\geq\mathbb P_{\mathrm{tree}}(U\times V\times W)
\geq\lambda^{\otimes E}(U\times V\times W).$$</div>
<p><em>Proof.</em> As in the preceding theorem, a nonempty section requires some subset of the three bits to equal one. Its probabilities depend only on the size $k$ of that subset:</p>
<div class="math-display">$$\begin{array}{c|cccc}
k&amp;0&amp;1&amp;2&amp;3\\
\sigma&amp;1&amp;1/2&amp;5/12&amp;3/8\\
\lambda&amp;1&amp;1/2&amp;1/3&amp;1/4
\end{array}$$</div>
<p>For $\sigma$, requiring $k\geq1$ ones has probability $(2/3)(1/2)+(1/3)2^{-k}$. For $\lambda$, each component law has two independent fair bits, with one of the three pairs forced equal. A specified pair of ones has probability $(1/3)(1/2)+(2/3)(1/4)=1/3$, while three ones have probability $1/4$. The table gives the section comparison, so apply 9GXY with the laws in reversed order.</p>
<p>This proves source Theorem 8.7. The mixtures are chosen independently at each coordinate before taking the product. They are not mixtures of whole configurations: if $E$ has two coordinates and $U=V=W$ requires both open, then $\sigma^{\otimes E}(U\times V\times W)=(3/8)^2=9/64$, whereas mixing one fully shared configuration with three independent configurations in proportions $2/3,1/3$ gives $11/64$. Thus this theorem does not by itself prove the distinct three-event inequality discussed in Remark 8.8. The source's historical claims about that inequality and the Richards proof require their own primary-source reconciliation.</p>


## Exploration from a common face {#section-planar-peeling}

<p>Fix a finite plane graph and two distinct vertices $u,v$ incident to a common face. Choose corners at these vertices and take this face to be the outer face. These choices specify a side from which to search. Paths below are simple and may share vertices; disjointness always means disjointness of edges.</p>

<a id="tag-KPT4" data-assertion="proposition" data-title="Outermost exploration removes one unit of edge connectivity at each successful search"></a>
<p>Run the recursive open-edge DFS of VN5Z from $u$, in the cyclic order that follows the chosen outer side, stopping on first reaching $v$. Let $S$ be the queried edges. On success the active stack gives an open $u$–$v$ path $P$. If $\nu(\omega)$ is the maximum number of edge-disjoint open $u$–$v$ paths, then</p>
<div class="math-display">$$\nu(\omega\setminus S)=\nu(\omega)-1.$$</div>
<p>On failure $\nu(\omega)=0$. Repeating the search after deleting all previously queried edges therefore decides $\{\nu\geq k\}$ after at most $k$ searches. At a successful leaf it supplies $k$ disjoint shared paths, and every completion of that leaf with $\nu\geq n\geq k$ has $n-k$ disjoint paths using only unqueried edges.</p>
<p><em>Proof.</em> At each vertex, start immediately after the edge by which the search arrived and examine incident edges from the chosen outer side towards the other side. At the root, start at its chosen face corner. Query an edge only once, descend immediately when it is open and its other endpoint is unvisited, and finish a recursive call before resuming its parent. In particular, neither a closed edge nor a list of neighbours is pushed as an open continuation.</p>
<p>The stack path is the outermost open path on the chosen side. To see this, suppose an open path made a detour on that side between two vertices of $P$. Take a segment of the detour whose interior avoids $P$. At its earlier endpoint along $P$, the edge entering the detour precedes the outgoing edge of $P$ in the search order. The recursive call through that edge would reach the later endpoint and then the open suffix to $v$ before returning. It could not leave the asserted final stack path. This also describes the usual boundary-following proof: thicken vertices to small disks and edges to strips; the search traces the outer frontier, with completed excursions erased from its active stack.</p>
<p>Every queried open edge off $P$ belongs to a completed excursion on this outer side. Such an open excursion meets $P$ at only one vertex: two distinct attachment vertices would give the forbidden outer detour. Consequently no simple $u$–$v$ path uses these edges. All queried closed edges can of course be deleted without changing open paths. The only relevant deletion is therefore $P$ itself.</p>
<p>It remains to show that some maximum family contains $P$. Orient a family of $r=\nu(\omega)$ disjoint paths from $u$ to $v$. In each small vertex disk, reconnect entering and leaving strands without crossing. Such a pairing exists by successively pairing adjacent strands of opposite orientation; conservation gives equally many of each away from the terminals. Discard closed circuits and erase any closed excursion in a resulting path. This gives $r$ noncrossing strands, ordered from the chosen outer side to the other side. Let $R$ be the outermost one. The preceding detour argument puts $P$ on or outside $R$. Thus $P$ uses no edge of the other $r-1$ strands, which are on the inner side of $R$; contacts at vertex disks do not identify edges. Replace $R$ by $P$. Deleting $S$ leaves those $r-1$ paths. Conversely, any family surviving deletion can be joined to $P$, so it has size at most $r-1$.</p>
<p>The same reasoning applies in the residual embedded graph, with the same starting face corners and the deleted edges omitted from the cyclic orders. Deletion only enlarges the outer face. Induction gives the repeated-search statement. A leaf fixes exactly the queried states, so replaying its search on any completion gives the same paths and the same deleted set. This proves the assertion about every completion, not merely about the configuration first used to find the leaf.</p>
<p>Cut vertices and repeated visits on a face boundary cause no ambiguity when corners, rather than just vertex names, specify the starting positions. Equivalently, one may put new terminals on a disk boundary through the chosen face. For connectivity, a deterministically open pendant edge at each mark preserves all marked connection events. For path counts up to $n$, use $n$ disjoint deterministically open spokes at each of the two terminals, subdivided if a simple graph is required. A single pendant edge would incorrectly cap the path count at one. Deleting the spokes recovers the original path family, and appending distinct spokes extends any family of at most $n$ paths.</p>

## Three boundary points {#section-planar-three-point}

<a id="tag-8XA9" data-assertion="theorem" data-title="A common face gives the factor-two three-point bound and its finite-family refinement"></a>
<p>For independent bond percolation on a finite plane graph, let $a,b,c$ be distinct vertices incident to one face. Write $t=\mathbb P(abc)$ and $\tau_{uv}=\mathbb P(u\leftrightarrow v)$. Then</p>
<div class="math-display">$$(1+\max\{\tau_{ab},\tau_{ac},\tau_{bc}\})t^2
\leq 2\tau_{ab}\tau_{ac}\tau_{bc}.$$</div>
<p>In particular, $t^2\leq2\tau_{ab}\tau_{ac}\tau_{bc}$. The same conclusions hold on a countable graph admitting an increasing exhaustion by finite plane subgraphs in which the three marks remain incident to a common face.</p>
<p><em>Proof.</em> We first prove the finite assertion with $1+\tau_{ac}$ on the left. If $\tau_{ac}=0$, then $t=0$. Otherwise search from $a$ to $c$ from the boundary side opposite $b$, and share the queried set $S$. If necessary use the pendant construction above, so that $b$ is a distinct boundary terminal and cannot lie inside the active $a$–$c$ path. Let $X,Y$ be independent configurations and let $H$ agree with $X$ on $S$ and with $Y$ elsewhere. The stopped-search inequality LNMI gives</p>
<div class="math-display">$$\frac{t^2}{\tau_{ac}}\leq J:=\mathbb P(X\in abc,H\in abc).$$</div>
<p>On this joint event the shared stack path $P$ joins $a$ to $c$. Any simple path from $b$ to $P$, stopped on first reaching it, uses only unqueried edges. Indeed, $b$ is on the opposite side of $P$ from the explored excursions. A path cannot enter such an excursion without first meeting its attachment to $P$. This argument also applies to $H$, because queried states agree. Choose one such continuation in $X$ and one in $H$, with attachment vertices $x,y$ on $P$.</p>
<p>If $x$ precedes $y$ along $P$ from $a$ to $c$, use the prefix from $a$ to $x$ with the first continuation, and the suffix from $y$ to $c$ with the second. These witness $ab$ in $X$ and $bc$ in $H$. Their shared edges are disjoint, even if $x=y$; overlap outside $S$ is allowed. If $y$ precedes $x$, use the opposite pair of witnesses, for $bc$ in $X$ and $ab$ in $H$. Hence</p>
<div class="math-display">$$\{X\in abc,H\in abc\}
\subseteq(ab\mathbin{\square}_Sbc)\cup(bc\mathbin{\square}_Sab).$$</div>
<p>Apply 3CE7 with capacity zero or one on queried coordinates, with probabilities $1-p_e,p_e$, and independent labelled bits on the rest. This is a predictable sampling tree: the exploration uses the already generated shared bits, and after stopping it generates independent labels on all remaining coordinates. The finite-family bound gives</p>
<div class="math-display">$$J\leq(\mu\otimes\mu)\bigl[(ab\times bc)\cup(bc\times ab)\bigr]
=2\tau_{ab}\tau_{bc}-t^2.$$</div>
<p>The intersection in the last union is $abc\times abc$, which explains the subtraction. Combine the bounds for $J$ and multiply by $\tau_{ac}$. Relabel the three marks and choose the largest pair probability to obtain the stated denominator. For the countable extension, every connection has a finite path witness. The three pair events and the all-connected event increase along the given exhaustion, and the finite inequalities pass to their probability limits.</p>
<p>This proves source Theorem 6.1 and the improvement indicated in Remark 6.3. The equality sign in source (15) must be a lower-bound sign. On the triangle with all three edge probabilities $1/2$, querying $ac$ first gives $t=1/2$, $\tau_{ac}=5/8$ and $J=13/32&gt;2/5=t^2/\tau_{ac}$. The reversed-attachment case also uses $bc$ and $ab$, as in the source's final displayed union. These corrections and the recursive search convention are recorded in the <a href="/errata/gladkov-decision-trees-2024/#planar-search-and-correlation">provisional erratum</a>.</p>

## Several paths between boundary vertices {#section-planar-multipaths}

<a id="tag-YQEG" data-assertion="theorem" data-title="Three path-count probabilities bound the square of a larger common-face path event"></a>
<p>Let $a,b$ be distinct vertices incident to one face of a finite plane graph, and let $p_j$ be the probability of at least $j$ edge-disjoint open $a$–$b$ paths, with $p_0=1$. For nonnegative integers $k,l,m\leq n$ satisfying $k+l+m=2n$,</p>
<div class="math-display">$$p_n^2\leq p_kp_lp_m.$$</div>
<p>In particular, $p_3^2\leq p_2^3$, and more generally $p_{3r}^2\leq p_{2r}^3$. The assertion extends to countable graphs exhausted by finite plane subgraphs in which $a,b$ remain incident to one face.</p>
<p><em>Proof.</em> The case $n=0$ is equality. If $p_k=0$, then $p_n=0$. Otherwise reveal $k$ outermost paths by KPT4, stopping at failure or after the $k$th success, and share every queried edge. For independent $X,Y$ and the resulting hybrid $H$, LNMI gives</p>
<div class="math-display">$$\frac{p_n^2}{p_k}\leq\mathbb P(\nu(X)\geq n,\nu(H)\geq n).$$</div>
<p>On this event the shared set contains $k$ disjoint open paths. By the completion assertion of KPT4, each of $X$ and $H$ also contains $n-k$ disjoint paths wholly outside the shared set. Give $n-m$ of the shared paths to the first witness and the other $n-l$ to the second; these numbers are nonnegative and sum to $k$. With the unshared paths added, the two witnesses contain respectively</p>
<div class="math-display">$$(n-k)+(n-m)=l,\qquad(n-k)+(n-l)=m$$</div>
<p>disjoint paths. Within either witness all edges are disjoint. Between the witnesses any overlap is unshared. Adaptive BK, 7LLO, therefore bounds the joint event by $p_lp_m$. Multiplication by $p_k$ proves the result. This reasoning includes $k=0$: then $l=m=n$, the shared set is empty, and both bounds are equalities. For a countable exhaustion, a family of any fixed finite number of finite paths is contained in one finite subgraph. Thus every $p_j$ increases to its full-graph value and the inequality passes to the limit.</p>
<p>The common-face condition is used in KPT4 to retain all remaining paths after a boundary search. Planarity alone does not supply that step for two arbitrarily placed vertices. Likewise, the result concerns edge-disjoint paths, not paths with disjoint interiors.</p>

## Pair distances and the diameter {#section-three-point-decay}

<a id="tag-9ZC5" data-assertion="corollary" data-title="Three-point power bounds retain all pair distances unless the marks have controlled separation"></a>
<p>Consider an independent bond model on a countable graph with a metric $d$, and suppose $\tau_{uv}\leq C d(u,v)^\alpha$ for distinct vertices, where $C&gt;0$ and $\alpha\in\mathbb R$. For three distinct marks put $D=\max(d(a,b),d(a,c),d(b,c))$. Then</p>
<div class="math-display">$$\mathbb P(abc)\leq (2C)^{3/2}
\bigl[d(a,b)d(a,c)d(b,c)\bigr]^{\alpha/2}.$$</div>
<p>If $\alpha\geq0$, this is at most $(2C)^{3/2}D^{3\alpha/2}$. If $\alpha&lt;0$ and every pair distance is at least $\eta D$, with $0&lt;\eta\leq1$, it is at most</p>
<div class="math-display">$$(2C)^{3/2}\eta^\alpha D^{3\alpha/2}.$$</div>
<p>Without that separation assumption, writing $s$ for the smallest pair distance gives the valid bound</p>
<div class="math-display">$$\mathbb P(abc)\leq (2C)^{3/2}2^{-\alpha/2}D^\alpha s^{\alpha/2}
\qquad(\alpha&lt;0).$$</div>
<p>Under the common-face exhaustion hypothesis of 8XA9, replace $(2C)^{3/2}$ in these bounds by $\sqrt2\,C^{3/2}$. No transitivity assumption is needed.</p>
<p><em>Proof.</em> Substitute the three two-point bounds into the countable factor-eight theorem 87RB and take a square root. For a nonnegative exponent, every distance is at most $D$. For a negative exponent and controlled separation, one pair distance equals $D$ and the other two are at least $\eta D$, so their product is at least $\eta^2D^3$. Without controlled separation, order the distances as $s\leq r\leq D$. The triangle inequality gives $r\geq D/2$, hence their product is at least $sD^2/2$. Raising these lower bounds to the negative power $\alpha/2$ gives the stated upper bounds. The planar constant follows by using the factor-two theorem instead.</p>
<p>The separation condition cannot simply be dropped for negative exponents, even with the constant in source Corollary 6.5. Take nearest-neighbour bond percolation on $\mathbb Z$ at $p=1/2$. At distance $r\geq1$, $\tau=2^{-r}&lt;(6/5)r^{-2}$: indeed, the maximum of $r^2/2^r$ over positive integers is $9/8$, attained at $r=3$. Beyond $r=3$ the ratio of consecutive terms is $(r+1)^2/(2r^2)&lt;1$. For $a=0,b=1,c=4$, however, $\mathbb P(abc)=1/16$ and $D=4$, whereas the asserted diameter-only bound is $(12/5)^{3/2}/64&lt;1/16$, since $(12/5)^3=1728/125&lt;16$. This disproves the printed corollary with $C=6/5$ and $\alpha=-2$ on an infinite vertex-transitive graph. It does not affect the three-point product theorem. See the <a href="/errata/gladkov-decision-trees-2024/#diameter-decay">provisional erratum</a>.</p>

## The Poisson comparison proposed in the source {#section-poisson-paths}

<a id="tag-TIKW" data-assertion="proposition" data-title="Poisson tails give a well-defined extended parameter for every positive path-count threshold"></a>
<p>For an integer $j\geq1$, define</p>
<div class="math-display">$$Q_j(\lambda)=1-e^{-\lambda}\sum_{i=0}^{j-1}\frac{\lambda^i}{i!},\qquad\lambda\geq0.$$</div>
<p>This is a continuous strictly increasing bijection from $[0,\infty)$ to $[0,1)$. With $Q_j(\infty)=1$, every path probability $p_j\in[0,1]$ therefore has a unique extended parameter $\lambda_j\in[0,\infty]$ satisfying $p_j=Q_j(\lambda_j)$. If $N$ independent parallel routes have individual success probability $\lambda/N$, their number of successful routes has tail probabilities tending to $Q_j(\lambda)$ as $N\to\infty$.</p>
<p><em>Proof.</em> Differentiation telescopes to $Q_j'(\lambda)=e^{-\lambda}\lambda^{j-1}/(j-1)!$, positive for $\lambda&gt;0$. Also $Q_j(0)=0$ and $Q_j(\lambda)\to1$ as $\lambda\to\infty$. These facts prove the inverse statement, including the endpoint values zero and infinity. For the route model the count is binomial with parameters $N,\lambda/N$ (take $N\geq\lambda$). For each fixed $i$,</p>
<div class="math-display">$$\binom Ni(\lambda/N)^i(1-\lambda/N)^{N-i}
\longrightarrow e^{-\lambda}\lambda^i/i!.$$</div>
<p>Sum this convergence for $0\leq i&lt;j$ and take the complement. To realize the model on a simple graph, replace each parallel route by a path with its own interior vertices and choose the product of that path's edge probabilities to be $\lambda/N$. For paths of length two, assigning both edges probability $\sqrt{\lambda/N}$ does this. Assigning both edges probability $\lambda/N$ would describe a different limit.</p>
<p>Section 10 of the 2024 source asks whether these implied parameters are nonincreasing in $j$. This is a proposed comparison, not a consequence of YQEG. The introduction separately proposes log-concavity of $p_j$ and monotonicity of $p_j^{1/j}$. The elementary BK bound $p_{i+j}\leq p_ip_j$ follows by splitting a family of $i+j$ disjoint paths into two witnesses; submultiplicativity alone is weaker than either proposed property. Source Conjecture 10.1, in the partition notation above, asks for a uniform implication $x&lt;\delta\Rightarrow ts-yz&lt;\varepsilon$. QY7X proves the stated two-rare-partition consequence, not this stronger assertion with only $x$ small. These are records of the questions posed in arXiv:2408.08457v1; their present research status has not been established here.</p>


## Fair order of two exits {#section-fair-dfs}

<p>The random search used here is the probabilistic DFS of Gladkov–Pak, <em>Exploring mazes at random</em>. Let $G$ be a finite connected graph of maximum degree three, with distinct leaves $A,B,C$. Fix a cyclic order of the incident edges at each vertex. Starting at $A$, run recursive DFS. On first entering a degree-three vertex, use an independent fair coin to choose which of the two edges other than the arrival edge is examined first. Process that choice recursively before the other. Already visited endpoints do not produce new recursive calls. For the proof, continue through the targets and finish the entire search; its first target is the same as for a search stopped there.</p>

<a id="tag-KRU2" data-assertion="theorem" data-title="The DFS pivot involution exchanges two leaf exits without changing the discovery tree"></a>
<p>The probability that $B$ is discovered before $C$ is $1/2$. More precisely, there is a measure-preserving involution of the finite coin space that preserves the rooted discovery tree and exchanges the two discovery orders. Conditional on that tree, the orders of its two child branches at all branching vertices are independent and fair. No plane embedding is required.</p>
<p><em>Proof.</em> Preassign a fair bit to every degree-three vertex, including bits that turn out to be irrelevant. The discovery edges form a spanning tree $T$ rooted at $A$. An edge of an undirected graph cannot join two different child subtrees of a DFS tree: the subtree searched first would discover the other endpoint before its recursive call finished. Thus every edge not in $T$ joins a vertex to one of its ancestors.</p>
<p>Suppose a vertex $v$ has two children in $T$. Since the root has degree one, $v$ is not the root. Its parent edge and its two child edges account for all three incident edges in $G$. Flipping its bit exchanges the two child searches. There are no edges between their vertex sets, and any edge from either subtree to a strict ancestor of $v$ still has an already visited endpoint. Consequently each child search makes exactly the same discoveries, with the same parents and internal order as before. The visited set after both searches is also unchanged. The entire tree $T$ is therefore preserved.</p>
<p>The paths from $A$ to the two target leaves have a unique last common vertex $v$. It is neither the root nor either target, and its two child subtrees contain $B$ and $C$ separately. Flipping the bit at this vertex reverses their discovery order. Since the tree is unchanged, the same vertex is selected on a second application. This is the required involution; it preserves the uniform measure on all bit assignments.</p>
<p>More generally, fixing the tree and all bits outside its branching vertices leaves a set of assignments invariant under flipping any of the remaining bits. Each nonempty such set is the full Boolean cube on those vertices, with uniform measure. Their child orders are therefore independent and fair, even after conditioning on $T$.</p>
<p>The degree and leaf hypotheses matter for this search rule. Take a triangle with vertices $A,x,y$, attach the exit leaf $B$ to $A$, and attach $C$ to $x$. If the first edge at the degree-three root $A$ is chosen uniformly, $B$ is first with probability $1/3$: either of the other first choices reaches $C$ before returning to $A$. If a target need not be a leaf, the path $A-x-C-y-B$ already gives probability one of reaching $C$ first. Finally, attach entrance and exit leaves $A,B$ to a vertex $x$ of a triangle $x,y,z$, and attach $C$ to $y$. Now $A,B,C$ are leaves but $x$ has degree four; uniform choice among its three forward neighbours again gives probabilities $1/3$ and $2/3$. These examples explain why the general-graph application below changes the graph before applying the theorem.</p>

## The search tree and several targets {#section-dfs-target-law}

<a id="tag-1QSK" data-assertion="corollary" data-title="Conditional target probabilities are determined by branching depths in the reduced DFS tree"></a>
<p>In the same finite graph and search, let $A$ be the entrance leaf and let $L$ consist of $k\geq2$ other leaves. For a discovery tree $T$ and $b\in L$, let $d_T(b)$ be the number of ancestors of $b$ whose two child subtrees both meet $L$. Then</p>
<div class="math-display">$$\mathbb P(b\text{ is the first target}\mid T)=2^{-d_T(b)},\qquad
2^{-(k-1)}\leq\mathbb P(b\text{ is the first target})\leq\frac12.$$</div>
<p>For three exits each probability lies in $[1/4,1/2]$, both endpoints are attained by tree mazes, and no finite maze has exit probability exactly $1/3$.</p>
<p><em>Proof.</em> A child subtree containing no target may delay the search, but cannot change the first target. At an ancestor with targets in both child subtrees, the branch containing $b$ must be searched first for $b$ to be the first target. These conditions are also sufficient, because DFS finishes one child subtree before entering the other. Conditional on $T$, their choices are independent fair bits by KRU2, giving $2^{-d_T(b)}$.</p>
<p>Prune the rooted tree to the paths from $A$ to $L$ and suppress vertices with only one retained child. The resulting binary branching tree has $k$ leaves and $k-1$ branching vertices: counting its edges by children gives $2q=q+k-1$, where $q$ is the number of branching vertices. Every target path passes through at least one and at most $k-1$ of them. This proves the bounds after averaging over $T$.</p>
<p>For three exits, the tree with edges $Ax,Bx,xy,Cy,Dy$ gives probabilities $1/2,1/4,1/4$ for $B,C,D$. Finally, with $N$ degree-three vertices, every outcome is determined by $N$ fair bits, so its probability is an integer divided by $2^N$. Such a number cannot equal $1/3$. This proves both parts of source Exercise 5.</p>

## Which direction an edge is explored {#section-dfs-edge-direction}

<a id="tag-88CG" data-assertion="proposition" data-title="A nonbridge is first explored in either direction with equal probability"></a>
<p>Let the same search run to completion from an entrance leaf $A$, with no stopping targets. For an edge $xy$, record the direction from which it is first examined. If it is not a bridge, each direction has probability $1/2$. If it is a bridge, the first direction goes from the component of $G\setminus\{xy\}$ containing $A$ to the other component, with probability one.</p>
<p><em>Proof.</em> A bridge is the only way to enter the component beyond it, which gives the asserted direction. For a nonbridge, delete $xy$ and replace it by two pendant edges $xB$ and $yC$ to new leaves. The graph remains connected, and its degrees at $x,y$ are unchanged. Put the new pendant edges in the old cyclic positions of $xy$. Couple the search bits in the two graphs. Until the first examination of the old edge, their searches agree, with the two pendant ends still unseen. Examination from $x$ corresponds exactly to discovering $B$ first, and examination from $y$ to discovering $C$ first. Apply KRU2 to the modified graph. In particular the only possible direction probabilities are $0,1/2,1$, with the criterion made explicit; this proves source Exercise 6.</p>

## A balanced search for general bond models {#section-balanced-bond-search}

<a id="tag-04ZU" data-assertion="proposition" data-title="A fixed subcubic expansion gives a balanced stopped exploration for arbitrary finite bond models"></a>
<p>Let $G$ be any finite graph with distinct marks $a,b,c$ and independent bond probabilities in $[0,1]$. There is a fixed auxiliary graph of maximum degree three, with leaf marks $A,B,C$, whose marked connection events have exactly the same probabilities as those of $a,b,c$. Its randomized open-edge DFS, stopped on first reaching $B$ or $C$, has outcomes $R_b,R_c$ satisfying</p>
<div class="math-display">$$\mathbb P_\xi(R_b\mid\omega)=\mathbb P_\xi(R_c\mid\omega)=\frac12
\quad\text{whenever }\omega\in abc,$$</div>
<p>where $\xi$ denotes its independent fair bits. If only $b$ is connected to $a$, the first outcome occurs surely; if only $c$ is connected, the second occurs surely. Consequently, with $t=\mathbb P(abc)$, $x=\mathbb P(ab\mid c)$ and $y=\mathbb P(ac\mid b)$,</p>
<div class="math-display">$$\mathbb P(R_b\cap abc)=\mathbb P(R_c\cap abc)=\frac t2,\qquad
\mathbb P(R_b)=x+\frac t2,\quad\mathbb P(R_c)=y+\frac t2.$$</div>
<p>Here the vertical bars in $ab\mid c$ and $ac\mid b$ denote separate clusters, not conditional probabilities.</p>
<p><em>Proof.</em> Replace each vertex by a fixed finite tree of maximum degree three, with a different leaf port for each incident original edge and, at a marked vertex, one additional port for the marked terminal. Such trees exist for any number of ports: a binary tree suffices, with an edge for one or two ports and an isolated vertex when no port is needed. Unused leaves are harmless. Join the two assigned ports for each original edge and give this edge its original Bernoulli state. Every internal tree edge is deterministically open. A port used by an original edge now has degree two; a terminal port remains a leaf. Thus the full auxiliary graph has maximum degree three, with the three marks as leaves.</p>
<p>Contracting all the deterministic trees recovers $G$. This gives a configuration-by-configuration equivalence of marked connections. The construction, including all ports and cyclic orders, is chosen before sampling any bonds. It is a connectivity construction; the balanced stopping outcomes refer to the new leaf terminals.</p>
<p>Give every degree-three vertex of the auxiliary graph an independent fair bit. On first entering it, this bit orders the two remaining ambient edges before either unknown state is queried. Query each edge once, descend immediately through an open edge to an unvisited vertex, and backtrack only after finishing the recursive call. This is a predictable search. For a fixed bond configuration, ignoring its closed edges gives the probabilistic DFS of the open component: a vertex with two forward open edges has a fair choice, while one with at most one forward open edge has no choice affecting discoveries. If all three terminals are connected, KRU2 applies to their finite open component. If just one exit is reachable, exhaustion of a finite recursive search must reach it first. Averaging these pointwise statements over the bond configuration proves the four identities.</p>
<p>This supplies the general-graph input behind Remark 6.4 of the decision-tree paper. It is a tree-port version of the degree reduction requested in Exercise 7 of the maze paper, and also works without planarity. It does not identify ordinary uniform-neighbour DFS on the original graph with the balanced search.</p>

## The balanced three-point estimate {#section-balanced-three-point}

<a id="tag-TWYR" data-assertion="theorem" data-title="Balanced exploration sharpens the three-point bound using split-cluster probabilities"></a>
<p>For independent bond percolation on a countable graph and distinct $a,b,c$, write</p>
<div class="math-display">$$t=\mathbb P(abc),\quad x=\mathbb P(ab\mid c),\quad y=\mathbb P(ac\mid b),\quad
r_b=x+t/2,\quad r_c=y+t/2,\quad Q_b=\tau_{ac}\tau_{bc},\quad Q_c=\tau_{ab}\tau_{bc}.$$</div>
<p>Then</p>
<div class="math-display">$$(1+4r_b)t^2\leq8r_bQ_b,\qquad(1+4r_c)t^2\leq8r_cQ_c.$$</div>
<p>In particular, these imply the estimate displayed in source Remark 6.4,</p>
<div class="math-display">$$t\leq\sqrt{2Q_b(x+t/2)}+\sqrt{2Q_c(y+t/2)},$$</div>
<p>as well as the one-split consequence</p>
<div class="math-display">$$t\leq2Q_b+\sqrt{4Q_b^2+8Q_bx}.
\qquad\text{If }x=0,\quad
 t\leq\frac{\sqrt{1+32Q_b}-1}{4}\leq4Q_b.$$</div>
<p>The corresponding bounds with $b,c$ interchanged also hold.</p>
<p><em>Proof.</em> First take a finite graph and use the auxiliary search of 04ZU. All connection probabilities are unchanged, so the rest of the argument takes place in that auxiliary model. Share the queried edges and independently resample the unqueried edges to form $H$ from $X$. Include the finite random seed as part of the stopped transcript. Conditional on a seed and a leaf, the two completions have the same independent product law. The leaf-sum argument of LNMI, followed by Cauchy–Schwarz over both leaves and seeds, gives, when $r_b&gt;0$,</p>
<div class="math-display">$$\frac{(t/2)^2}{r_b}\leq J_b:=\mathbb P(R_b,X\in abc,H\in abc).$$</div>
<p>On $R_b$, the stopped path geometry VN5Z supplies either $ac$ in $X$ and $bc$ in $H$, or the reverse pair, with overlap allowed only on unshared edges. For each fixed seed, apply the finite-family adaptive comparison 3CE7 to this union. Its independent endpoint has probability</p>
<div class="math-display">$$(\mu\otimes\mu)\bigl[(ac\times bc)\cup(bc\times ac)\bigr]
=2Q_b-t^2,$$</div>
<p>because the intersection is $abc\times abc$. Average over seeds to get $J_b\leq2Q_b-t^2$. Combining the bounds gives $(1+4r_b)t^2\leq8r_bQ_b$. If $r_b=0$, then $t=0$, and the same inequality holds. The proof for $c$ is identical with the targets interchanged.</p>
<p>Dropping the subtraction in the bound for $J_b$ gives $t/2\leq\sqrt{2r_bQ_b}$, and likewise for $c$; adding proves the source estimate. The same weaker inequality gives $t^2\leq4Q_bt+8Q_bx$. Solving this quadratic for the nonnegative variable $t$ proves the one-split bound. If $x=0$, the stronger inequality gives $t(1+2t)\leq4Q_b$, with the case $t=0$ immediate. Solve again, and use $\sqrt{1+u}\leq1+u/2$ for the last comparison.</p>
<p>For a countable graph, exhaust its edges by finite sets containing the three marks. Pair connection and all-connected probabilities converge by finite path witnesses. Since $x=\tau_{ab}-t$ and $y=\tau_{ac}-t$, the split probabilities and $r_b,r_c$ converge as well. The polynomial inequalities pass to the limit, followed by their displayed consequences. This passage does not require an infinite randomized search to terminate.</p>
<p>The factors $1+4r_b$ and $1+4r_c$ retain the finite-family subtraction and are stronger than the displayed source remark. The proof of that remark itself needs only the balanced search and the separate adaptive BK bounds. No new compiled correspondence is asserted.</p>


## Conditioning a three-function correlation {#section-higher-correlation-conditioning}

<p>The whole-configuration inequality discussed after JOJ1 concerns the functional</p>
<div class="math-display">$$E_3(f_1,f_2,f_3)=2\mathbb E(f_1f_2f_3)-\sum_{\{i,j,k\}=\{1,2,3\},\,i<j}\mathbb E(f_if_j)\mathbb E f_k+\prod_{i=1}^3\mathbb E f_i.$$</div>
<p>Each sum over $\{i,j,k\}=\{1,2,3\}$ below has three terms, one for each unordered pair $\{i,j\}$. For event indicators, this is precisely the three-event expression in Remark 8.8. Its induction requires more than the two-function covariance decomposition.</p>

<a id="tag-ICQP" data-assertion="proposition" data-title="Conditional three-function correlations have an additional covariance term"></a>
<p>Let $f_1,f_2,f_3$ be bounded real random variables and $\mathcal G$ a sub-sigma-algebra. Write $m_i=\mathbb E(f_i\mid\mathcal G)$, $c_{ij}=\mathbb E(f_if_j\mid\mathcal G)-m_im_j$, and let $L$ be the expression defining $E_3$, with every expectation replaced by conditional expectation given $\mathcal G$. Then</p>
<div class="math-display">$$E_3(f_1,f_2,f_3)=\mathbb E L+E_3(m_1,m_2,m_3)+\sum_{\{i,j,k\}=\{1,2,3\},\,i<j}\operatorname{Cov}(c_{ij},m_k).$$</div>
<p>The last sum can be negative even for nonnegative increasing functions of independent fair bits.</p>
<p><em>Proof.</em> Put $q=\mathbb E(f_1f_2f_3\mid\mathcal G)$. Substitution gives $L=2q-2m_1m_2m_3-\sum c_{ij}m_k$. Take expectations, use $\mathbb E(f_if_j)=\mathbb E(m_im_j)+\mathbb E c_{ij}$, and collect terms. This gives the identity without any association assumption.</p>
<p>For the sign, let $X,Z$ be independent fair bits, take $f_1=f_2=X\vee Z$, $f_3=Z$, and condition on $Z$. Then $m_1=m_2=(1+Z)/2$, $m_3=Z$, $c_{12}=(1-Z)/4$, and $c_{13}=c_{23}=0$. Thus the covariance sum is $-1/16$. Here $L=0$, while $E_3(m_1,m_2,m_3)=7/32$ and $E_3(f_1,f_2,f_3)=5/32$. The desired inequality holds in this example; the omitted term has the wrong sign for the proposed induction.</p>
<p>The one-bit calculation itself is valid. If $f_i=a_i+b_iZ$ with $a_i,b_i\geq0$ and $\mathbb P(Z=1)=p$, multilinearity gives</p>
<div class="math-display">$$E_3(f_1,f_2,f_3)=p(1-p)\left(a_1b_2b_3+a_2b_1b_3+a_3b_1b_2+(2-p)b_1b_2b_3\right)\geq0.$$</div>
<p>In Richards, <em>Algebraic methods toward higher-order probability inequalities, II</em>, the calculation (2.6)–(2.13) treats a one-coordinate fibre. The step after (2.13) substitutes an arbitrary remaining set, without establishing that extension. The <a href="/errata/richards-higher-correlation-2004/#conditioning-induction">provisional erratum</a> records this proof gap, not a counterexample to the theorem. The next results give replacements with explicit restrictions. Lieb–Sahi (2022), Introduction, also report gaps in the earlier proofs; their historical status statement does not establish the conjecture's status at a later date.</p>

## Functions with nonnegative Boolean coefficients {#section-cumulation-cone}

<a id="tag-CUE4" data-assertion="proposition" data-title="Nonnegative Boolean coefficients are preserved by products and coordinate differences"></a>
<p>For a finite set $E$, let $\mathcal C_E$ consist of the functions</p>
<div class="math-display">$$f(S)=\sum_{T\subseteq S}a_T,\qquad a_T\geq0\quad(S\subseteq E).$$</div>
<p>The coefficients are unique and satisfy $a_T=\sum_{U\subseteq T}(-1)^{|T\setminus U|}f(U)$. The cone $\mathcal C_E$ is closed under nonnegative linear combinations and pointwise products. For $e\in E$, both restrictions $f^-(S)=f(S)$, $f^+(S)=f(S\cup\{e\})$, and the difference $f^+-f^-$ belong to $\mathcal C_{E\setminus\{e\}}$.</p>
<p><em>Proof.</em> In the proposed inversion, the coefficient of $a_V$ is $\sum_{V\subseteq U\subseteq T}(-1)^{|T\setminus U|}$, which is one for $V=T$ and zero otherwise. If $f,g$ have coefficients $a_T,b_T$, their product has coefficient $\sum_{U\cup V=T}a_Ub_V$ at $T$. The coefficients of $f^-$, $f^+$ and $f^+-f^-$ at $T\subseteq E\setminus\{e\}$ are respectively $a_T$, $a_T+a_{T\cup\{e\}}$ and $a_{T\cup\{e\}}$.</p>
<p>Every function in this cone is nonnegative and increasing. The converse fails: the indicator $f(S)=\mathbf1_{S\neq\varnothing}$ on a two-element set has top coefficient $-1$. In percolation terms, the cone includes nonnegative weighted counts of prescribed open witnesses. A union of witness events need not belong to it. Connectivity indicators therefore require a separate check.</p>

## Eliminating a coordinate in a formal series {#section-correlation-series}

<p>Use finitely many formal variables $t_1,\ldots,t_r$. A series-valued function $F$ on $2^E$ has coefficients in $\mathcal C_E$ if each of its coefficient functions belongs to that cone. Assume that its constant coefficient is zero. All powers, logarithms and exponentials below are formal; no convergence or smallness assumption on the functions is involved.</p>

<a id="tag-ZY1X" data-assertion="theorem" data-title="Bernoulli coordinate elimination preserves nonnegative Boolean coefficients in formal series"></a>
<p>For a Bernoulli product measure $\mu$ on $2^E$, with arbitrary parameters in $[0,1]$, the series</p>
<div class="math-display">$$\Psi_\mu(F)=1-\exp\bigl(\mathbb E_\mu\log(1-F)\bigr)$$</div>
<p>has nonnegative coefficients whenever $F$ has zero constant coefficient and coefficients in $\mathcal C_E$.</p>
<p><em>Proof.</em> Eliminate a coordinate $e$ of parameter $p$. On the remaining coordinates put $A=F^-$ and $D=F^+-F^-$. Define $F_e$ by</p>
<div class="math-display">$$1-F_e=(1-A)^{1-p}(1-A-D)^p.$$</div>
<p>Both $A$ and $D$ have coefficients in the smaller cone, by CUE4. Factoring out $1-A$ and expanding the binomial series gives</p>
<div class="math-display">$$F_e=A+\sum_{j\geq1}c_j(p)D^j(1-A)^{1-j},\qquad c_j(p)=(-1)^{j-1}\binom pj=\frac{p\prod_{h=1}^{j-1}(h-p)}{j!}\geq0.$$</div>
<p>For $j=1$ the final factor is one. For $j\geq2$ its expansion is $\sum_{k\geq0}\binom{j+k-2}{k}A^k$, with nonnegative coefficients. Products preserve the cone, so every coefficient of $F_e$ is in $\mathcal C_{E\setminus\{e\}}$. This series is well defined: $A,D$ have positive total degree, hence only finitely many pairs $(j,k)$ contribute to a fixed monomial. It also has zero constant coefficient.</p>
<p>If $\nu$ is the product law on the remaining coordinates, taking formal logarithms in the defining identity yields $\mathbb E_\nu\log(1-F_e)=\mathbb E_\mu\log(1-F)$. Thus $\Psi_\mu(F)=\Psi_\nu(F_e)$. Repeat until there are no coordinates. At that point $\Psi(F)=F$, whose coefficients are nonnegative. The argument includes $p=0,1$.</p>

## Correlations of arbitrary order {#section-higher-correlation-positive}

<p>For bounded real functions $f_1,\ldots,f_n$ on a probability space and $n\geq1$, define</p>
<div class="math-display">$$E_n(f_1,\ldots,f_n)=\sum_{\pi\in\mathcal P([n])}(-1)^{|\pi|-1}\prod_{B\in\pi}\left((|B|-1)!\,\mathbb E\prod_{i\in B}f_i\right),$$</div>
<p>where $\mathcal P([n])$ is the set of partitions into nonempty blocks. This is symmetric and linear in each argument. It gives the expectation for $n=1$, covariance for $n=2$, and the expression above for $n=3$.</p>

<a id="tag-7ZU5" data-assertion="proposition" data-title="Polarization gives the partition formula and the constant-argument recursion"></a>
<p>The coefficient of $t_1\cdots t_n$ in $\Psi(\sum_i t_if_i)$ is $E_n(f_1,\ldots,f_n)$. For $n\geq2$,</p>
<div class="math-display">$$E_n(f_1,\ldots,f_{n-1},1)=(n-2)E_{n-1}(f_1,\ldots,f_{n-1}).$$</div>
<p>In particular $E_n(1,\ldots,1)=0$ for every $n\geq2$.</p>
<p><em>Proof.</em> The square-free monomial $\prod_{i\in B}t_i$ in $\mathbb E\log(1-\sum_i t_if_i)$ has coefficient $-(|B|-1)!\,\mathbb E\prod_{i\in B}f_i$. On exponentiating, a contribution to $t_1\cdots t_n$ chooses disjoint blocks covering $[n]$. The factorial for ordering those blocks cancels the exponential's factorial. Subtracting the resulting series from one gives exactly the partition formula; terms containing a squared variable cannot contribute.</p>
<p>For the recursion, fix a partition of $[n-1]$. Inserting $n$ into a block $B$ multiplies its coefficient by $|B|$ and leaves its moment unchanged. Making $n$ a singleton changes the sign and adds a factor $\mathbb E1=1$. The total multiplier is $\sum_B|B|-1=n-2$. The last assertion starts with $E_2(1,1)=0$ and follows by induction.</p>

<a id="tag-BXP2" data-assertion="theorem" data-title="All higher correlations are nonnegative for positive Boolean cumulations under a product law"></a>
<p>For every finite $E$, every Bernoulli product measure on $2^E$, every $n\geq1$, and all $f_1,\ldots,f_n\in\mathcal C_E$, one has $E_n(f_1,\ldots,f_n)\geq0$.</p>
<p><em>Proof.</em> The series $F=\sum_i t_if_i$ satisfies ZY1X. Its coefficient of $t_1\cdots t_n$ is nonnegative and, by 7ZU5, equals the claimed correlation.</p>
<p>This proves Sahi's restricted higher-correlation theorem directly with several formal variables. It does not replace membership in $\mathcal C_E$ by ordinary monotonicity, or replace the product measure by an arbitrary FKG measure. For $n\leq5$ the partition coefficients agree with Richards' conjugate cumulants. They already differ at the partition $(3,3)$ of six: the coefficient here is $-4$, whereas the coefficient using only the largest block is $-2$.</p>

## Why ordinary monotonicity does not close this induction {#section-correlation-nonclosure}

<a id="tag-XYDY" data-assertion="proposition" data-title="One-coordinate formal elimination need not preserve coefficientwise monotonicity"></a>
<p>On two independent fair bits, let $F(\varnothing)=0$, $F(\{1\})=t^2$, and $F(\{2\})=F(\{1,2\})=t^2+t^3$. Every coefficient of $F$ is a nonnegative increasing function. Nevertheless, eliminating coordinate two by the formula for $F_e$ above produces a function whose coefficient of $t^5$ is not increasing.</p>
<p><em>Proof.</em> The difference between its values at $\{1\}$ and $\varnothing$ is</p>
<div class="math-display">$$(1-t^2-t^3)^{1/2}\bigl(1-(1-t^2)^{1/2}\bigr).$$</div>
<p>In degree five the only contribution is the product of $-t^3/2$ from the first factor and $t^2/2$ from the second, giving $-1/4$. This is a failure of the intermediate monotonicity property, not a negative coefficient of the final $\Psi_\mu(F)$ and not a counterexample to $E_n\geq0$. It is Sahi's Example 13.</p>

## Three functions on a product of two chains {#section-two-chain-correlation}

<a id="tag-LGXD" data-assertion="theorem" data-title="Three-function correlation is nonnegative on the unit square and on two finite independent chains"></a>
<p>For bounded nonnegative coordinatewise monotone functions $f,g,h$ on $[0,1]^2$ with Lebesgue measure, all monotone in the same direction, $E_3(f,g,h)\geq0$. The same holds on the product of two finite totally ordered probability spaces, with arbitrary marginal weights.</p>
<p><em>Proof.</em> By reversing both coordinates, it is enough to treat decreasing functions. First consider indicators of decreasing unions of cells in an $m$ by $m$ grid. Such a set is specified by integers $m\geq a_1\geq\cdots\geq a_m\geq0$, the heights of its columns. Write $ab$ for coordinatewise minimum, and $\langle a\rangle=m^{-2}\sum_i a_i$ for its area. Moments of indicators become $\langle ab\rangle$, $\langle abc\rangle$, and so on.</p>
<p>Choose a triple minimizing $E_3$, and among those choose one maximizing $\langle a\rangle+\langle b\rangle+\langle c\rangle$. Suppose $a_i>a_{i+1}$. If both $b$ and $c$ are constant across these two columns, replace the two heights of $a$ either by $a_i,a_i$ or by $a_{i+1},a_{i+1}$, obtaining $a^+$ and $a^-$. For each $d=1,b,c,bc$,</p>
<div class="math-display">$$\langle a^+d\rangle+\langle a^-d\rangle=2\langle ad\rangle.$$</div>
<p>Each term of $E_3$ contains exactly one factor involving $a$, so the same average identity holds for $E_3(a^+,b,c)$ and $E_3(a^-,b,c)$. Both are at least the minimum, hence both equal it. The plus choice increases the sum of areas, a contradiction.</p>
<p>Otherwise another sequence, say $b$, descends at the same place. Exchange $a,b$ if necessary so that $b_{i+1}\leq a_{i+1}$. Increase $a_{i+1}$ by one to obtain $a^*$. This is still decreasing and satisfies $a^*b=ab$, hence also $a^*bc=abc$. Direct cancellation gives</p>
<div class="math-display">$$E_3(a,b,c)-E_3(a^*,b,c)=E_2(b,c)\bigl(\langle a^*\rangle-\langle a\rangle\bigr)+\langle b\rangle\bigl(\langle a^*c\rangle-\langle ac\rangle\bigr)\geq0.$$</div>
<p>Here $E_2(b,c)\geq0$ is the two-function product correlation inequality, and the other differences are nonnegative. For completeness, that two-function fact follows by conditioning on one uniform coordinate: the within-column covariance is nonnegative since two decreasing one-variable functions have covariance $\frac12\mathbb E[(u(X)-u(X'))(v(X)-v(X'))]\geq0$, and their column means are again decreasing, so the covariance of the means is nonnegative too. Thus $a^*$ also attains the minimum, again contradicting maximality of the sum of areas.</p>
<p>Consequently all three minimizing sequences are constant. Their sets are nested strips with areas, after relabelling, $\alpha\leq\beta\leq\gamma$. Substitution gives $E_3=\alpha(1-\beta)(2-\gamma)\geq0$. This proves the grid case.</p>
<p>For a measurable decreasing set in the square, round its column-height function down on a uniform grid. The resulting decreasing union of cells differs in area by at most $2/m$: vertical rounding costs at most $1/m$, and the sum of horizontal height drops is at most one. Boundary conventions affect only a null set. Thus its indicator converges in $L^1$; products of up to three such indicators also converge in $L^1$. Passing to the limit proves the inequality for arbitrary decreasing sets. Finally write each bounded nonnegative function as the integral of its level-set indicators. Multilinearity and Fubini integrate the indicator inequality, giving the assertion for functions.</p>
<p>For finite ordered marginal spaces, represent each variable by its increasing quantile function of an independent uniform variable. Pullback preserves the common monotonicity direction and every mixed moment, so the square result applies. The two dimensions here count independent ordered coordinates. They do not refer to the geometric dimension of a percolation graph with many independent bonds.</p>
<p>The perturbation argument is the three-function case of Lieb–Sahi (2022), section 2. Their results for arbitrary numbers of functions on the square, and for rectangular level sets in any dimension, require further arguments. They are not being inferred from this three-function proof.</p>


## Recursion and nested events {#section-correlation-recursion}

<a id="tag-AFJX" data-assertion="proposition" data-title="Insertion of one argument gives a correlation recursion and a nested-event product formula"></a>
<p>For bounded real functions and $n\geq2$,</p>
<div class="math-display">$$E_n(f_1,\ldots,f_{n-1},f)=\sum_{i=1}^{n-1}E_{n-1}(f_1,\ldots,f_if,\ldots,f_{n-1})-(\mathbb Ef)E_{n-1}(f_1,\ldots,f_{n-1}).$$</div>
<p>Consequently, if $A_1\subseteq\cdots\subseteq A_n$ are measurable events with probabilities $a_1\leq\cdots\leq a_n$, then</p>
<div class="math-display">$$E_n(\mathbf1_{A_1},\ldots,\mathbf1_{A_n})=a_1\prod_{j=2}^n(j-1-a_j)\geq0.$$</div>
<p><em>Proof.</em> Each block $B$ in the partition formula can be cyclically ordered in $(|B|-1)!$ ways. Hence that formula is also a sum over permutations, with sign $(-1)^{c-1}$ for a permutation having $c$ cycles and one mixed moment for each cycle. Remove the symbol $n$. If it formed a singleton cycle, removal changes the sign and leaves the factor $\mathbb Ef$. Otherwise it followed a unique symbol $i&lt;n$ in its cycle. Inserting $n$ after that symbol is a bijection from permutations of $[n-1]$ to this class, preserves the cycle count, and replaces $f_i$ in its moment by $f_if$. Summing over the possibilities proves the recursion.</p>
<p>For nested indicators, $f_if_n=f_i$ for every $i&lt;n$. Thus the recursion multiplies $E_{n-1}$ by $n-1-a_n$. Starting from $E_1(f_1)=a_1$ gives the product formula. This argument works on any probability space.</p>

## Rectangular level sets {#section-rectangle-correlations}

<a id="tag-OC4P" data-assertion="theorem" data-title="All higher correlations are nonnegative for anchored rectangles in any finite dimension"></a>
<p>Under Lebesgue measure on $[0,1]^d$, $E_n(f_1,\ldots,f_n)\geq0$ for indicators of rectangles $\prod_{j=1}^d[0,r_j]$, for every $d,n\geq1$. The same conclusion holds for bounded nonnegative measurable functions whose positive upper level sets are such rectangles, up to null sets. Reversing every coordinate gives the corresponding statement for upper rectangles.</p>
<p><em>Proof.</em> Induct on $d$, and within each dimension on $n$. The case $d=1$ is AFJX, since intervals are nested; $n=1$ is immediate. Write each rectangle indicator as $f_i(x,u)=g_i(x)\mathbf1_{[0,a_i]}(u)$, with $g_i$ a rectangle indicator in dimension $d-1$. Relabel so that $a_1\leq\cdots\leq a_n$.</p>
<p>Fix $i&gt;1$. Group the partition formula by the block $B$ containing $i$. For a proper block the contribution is</p>
<div class="math-display">$$-(|B|-1)!\,\mathbb E\prod_{j\in B}f_j\ E_{n-|B|}\bigl((f_j)_{j\notin B}\bigr).$$</div>
<p>For the full block it is $(n-1)!\,\mathbb E\prod_j f_j$. Within the ordering region, the mixed moment for $B$ equals $a_{\min B}\mathbb E\prod_{j\in B}g_j$. A term therefore depends on $a_i$ only if $i=\min B$. Such a block omits index one and is proper. Its coefficient of $a_i$ is nonpositive by the induction hypothesis in $n$; its complementary correlation does not involve $a_i$. The full-block contribution does not depend on $a_i$.</p>
<p>Increasing $a_n$ to one, then $a_{n-1}$ to one, and so on through $a_2$, preserves the ordering and cannot increase $E_n$. At the endpoint, exactly one block of every partition contains index one. Its moment contributes the sole factor $a_1$, so the endpoint value is $a_1E_n(g_1,\ldots,g_n)\geq0$ by the induction hypothesis in $d$. This proves the indicator case. For the stated functions, integrate over the $n$ level parameters. Boundedness permits Fubini in every term of the finite partition sum, and multilinearity gives the conclusion.</p>

## All orders on two independent chains {#section-two-chain-all-orders}

<a id="tag-L3SC" data-assertion="theorem" data-title="Every higher correlation is nonnegative for commonly monotone functions on two independent chains"></a>
<p>For every $n\geq1$, bounded nonnegative functions $f_1,\ldots,f_n$ on $[0,1]^2$ with Lebesgue measure satisfy $E_n(f_1,\ldots,f_n)\geq0$ if they are coordinatewise monotone in the same direction. This also holds on the product of any two finite totally ordered probability spaces.</p>
<p><em>Proof.</em> Use the decreasing grid indicators and notation from LGXD. For each fixed grid we prove positivity by induction on $n$, together with an auxiliary assertion: if $b$ and $a^1,\ldots,a^{n-2}$ are decreasing grid indicators and $S$ is any measurable set disjoint from the set represented by $b$, then</p>
<div class="math-display">$$E_n(a^1,\ldots,a^{n-2},b,\mathbf1_S)\leq0.$$</div>
<p>There is no monotonicity requirement on $S$. Positivity at $n=1$ is immediate. The auxiliary assertion at $n=2$ is $E_2(b,\mathbf1_S)=-(\mathbb Eb)\mathbb P(S)\leq0$.</p>
<p>Suppose positivity and the auxiliary assertion hold at order $n-1$, with $n\geq3$. Apply AFJX with last argument $\mathbf1_S$. The term merging it into $b$ vanishes. Each other merged term replaces $S$ by its intersection with the decreasing set represented by $a^i$; this intersection is still disjoint from $b$, so that term is nonpositive by the auxiliary induction hypothesis. The subtracted term is $\mathbb P(S)E_{n-1}(a^1,\ldots,a^{n-2},b)\geq0$. This proves the auxiliary assertion at order $n$.</p>
<p>To deduce positivity at that order, choose a minimizing $n$-tuple of grid sequences, maximizing the sum of their areas among minimizers. If exactly one sequence descends between adjacent columns, flatten those two heights upward or downward. Every partition term contains only one mixed moment involving that sequence, and all its other factors in that moment are constant across the two columns. The same averaging identity used in LGXD therefore holds for $E_n$. Both flattened tuples must attain the minimum; the upward one increases the sum of areas, a contradiction.</p>
<p>If at least two sequences descend there, call them $b,c$ and arrange $b_{i+1}\leq c_{i+1}$. Raise $c_{i+1}$ by one. The added cell $S$ is disjoint from $b$. By multilinearity, the change in $E_n$ is the auxiliary expression with last argument $\mathbf1_S$, hence is nonpositive. This again contradicts maximality of the sum of areas. Thus all sequences at the chosen minimum are constant. Their sets are nested strips, and AFJX makes their correlation nonnegative. This completes the induction, including $n=2$.</p>
<p>For a fixed finite number of indicators, the grid approximation in LGXD converges in $L^1$ for every mixed product: the difference of two products of indicators is bounded in absolute value by the sum of the individual indicator differences. Every moment in the partition formula therefore converges. Layer cake gives bounded nonnegative functions, coordinate reversal gives increasing functions, and quantile pullback gives the finite-chain statement.</p>
<p>The nested-interval product in AFJX uses $f_if_n=f_i$, and its probabilities lie in $0\leq a_1\leq\cdots\leq a_n\leq1$. Two inconsistent displays in the source are recorded in the <a href="/errata/lieb-sahi-higher-correlation-2022/#nested-display-corrections">provisional erratum</a>. These local corrections preserve the main square and rectangle theorems.</p>

## From correlations back to formal positivity {#section-correlation-equivalence}

<a id="tag-I7RH" data-assertion="proposition" data-title="All-order correlation positivity is equivalent to formal-series positivity for a class containing zero"></a>
<p>Let $\mathcal I$ be a class of bounded real functions on a probability space, containing the zero function. The following are equivalent: $E_n(f_1,\ldots,f_n)\geq0$ for every $n\geq1$ and every tuple from $\mathcal I$; and $\Psi(\sum_{j\geq1}t^jf_j)$ has nonnegative coefficients for every sequence $(f_j)$ from $\mathcal I$. No uniform bound on the entire sequence is needed.</p>
<p><em>Proof.</em> Grouping permutations by their cycle lengths, or directly expanding the formal exponential, gives</p>
<div class="math-display">$$\Psi(uf)=\sum_{n\geq1}\frac{u^n}{n!}E_n(f,\ldots,f).$$</div>
<p>For example, a partition with $m_k$ blocks of size $k$ contributes $n!/\prod_k (k!)^{m_k}m_k!$ times its block weights. After division by $n!$, the magnitude becomes $\prod_k (\mathbb Ef^k)^{m_k}/(k^{m_k}m_k!)$, exactly the coefficient obtained from $\exp(-\sum_{k\geq1}u^k\mathbb Ef^k/k)$. The signs agree after subtraction from one. Substituting $F=\sum_{j\geq1}t^jf_j$ and using multilinearity gives</p>
<div class="math-display">$$\Psi(F)=\sum_{n\geq1}\frac1{n!}\sum_{j_1,\ldots,j_n\geq1}E_n(f_{j_1},\ldots,f_{j_n})t^{j_1+\cdots+j_n}.$$</div>
<p>Only finitely many tuples contribute to each coefficient, so nonnegativity of all correlations implies formal positivity.</p>
<p>Conversely, fix $f_1,\ldots,f_n\in\mathcal I$. Choose distinct primes $p_1,\ldots,p_n$, set $P=\prod_i p_i$, $k_i=P/p_i$, and $N=\sum_i k_i$. Use $F=\sum_i t^{k_i}f_i$, with zero functions at the unused degrees. If nonnegative integers $s_i$ satisfy $\sum_i s_ik_i=N$, reduction modulo $p_i$ shows $s_i\equiv1\pmod{p_i}$, hence $s_i\geq1$. The equality then forces every $s_i=1$. Thus the coefficient of $t^N$ isolates the square-free coefficient in 7ZU5 and equals $E_n(f_1,\ldots,f_n)$. It is nonnegative by the assumed formal positivity.</p>
<p>In particular, L3SC gives formal positivity for series whose coefficients are bounded nonnegative commonly monotone functions on the square. The explicit zero-function hypothesis permits unused degrees in the converse; all cones considered here satisfy it.</p>


## FKG laws on two bits {#section-two-bit-fkg}

<a id="tag-NG3I" data-assertion="theorem" data-title="Every two-bit FKG law has nonnegative higher correlations for increasing functions"></a>
<p>Let $\mu$ assign masses $\delta,\gamma,\beta,\alpha$ to $00,10,01,11$, respectively, where the masses are nonnegative, sum to one, and satisfy $\alpha\delta\geq\beta\gamma$. For every $n\geq1$ and nonnegative increasing functions $f_1,\ldots,f_n$ on the two-bit lattice, $E_n(f_1,\ldots,f_n)\geq0$ under $\mu$. Moreover $\Psi_\mu(F)$ has nonnegative coefficients for any zero-constant formal series whose coefficient functions are nonnegative and increasing on that lattice.</p>
<p><em>Proof.</em> Put $p=\alpha+\gamma$. If $0&lt;p&lt;1$, define</p>
<div class="math-display">$$q_0=\frac{\beta}{1-p},\qquad q_1=\frac{\alpha}{p},\qquad q_1-q_0=\frac{\alpha\delta-\beta\gamma}{p(1-p)}\geq0.$$</div>
<p>Take independent uniform variables $U,V$ on $[0,1]$, and set $X=\mathbf1_{U&gt;1-p}$, $Y=\mathbf1_{V&gt;1-q_X}$. The map $(U,V)\mapsto(X,Y)$ is increasing in both coordinates. Its four probabilities are exactly $\delta,\gamma,\beta,\alpha$, by conditioning on $X$. If $p=0$, take $X=0$ and $Y=\mathbf1_{V&gt;1-\beta}$; if $p=1$, take $X=1$ and $Y=\mathbf1_{V&gt;1-\alpha}$. These maps are increasing too.</p>
<p>Thus each $f_i(X,Y)$ is a bounded nonnegative increasing function of two independent uniforms, with the same joint moments as under $\mu$. Apply L3SC. The class of nonnegative increasing functions contains zero, so I7RH gives the formal-series assertion. For several formal variables, use the same finite coefficient expansion; every coefficient is a nonnegative sum of correlations.</p>
<p>This proves the two-bit case of Sahi's Proposition 15 by a monotone sampling argument using the later square theorem. It replaces the coefficient calculation in Lemma 16 for this conclusion; it does not assume the bits themselves are independent. An FKG law on more bits generally requires more independent sampling coordinates, so this argument does not settle the unrestricted conjecture.</p>


## Widely separated points in the uniqueness regime {#section-supercritical-separation}

<a id="tag-6BFG" data-assertion="theorem" data-title="Separated k-point connectivity tends to the kth power of the infinite-cluster density under uniqueness"></a>
<p>Let independent bond percolation on $\mathbb Z^d$, $d\geq1$, have a translation-invariant law. Suppose there is almost surely at most one infinite open cluster, and write $\theta=\mathbb P(|K_0|=\infty)$. For fixed $k\geq2$ and marks $x_{1,n},\ldots,x_{k,n}$ with all pair distances tending to infinity,</p>
<div class="math-display">$$\mathbb P(x_{1,n},\ldots,x_{k,n}\text{ lie in one open cluster})\longrightarrow\theta^k.$$</div>
<p>If $\theta&gt;0$, the three-point ratio tends to one. The conclusion permits long-range bonds and arbitrary diagonal probabilities.</p>
<p><em>Proof.</em> Put $I_x=\{|K_x|=\infty\}$. By <a href="/tag/DK14/">finite-coordinate approximation</a>, for each $\varepsilon&gt;0$ there is an event $B$ depending on finitely many bonds with $\mathbb P(B\mathbin\triangle I_0)&lt;\varepsilon$. Once the marks are sufficiently separated, the translates of this finite bond set are pairwise disjoint. Their events are independent, and translation invariance gives</p>
<div class="math-display">$$\left|\mathbb P\left(\bigcap_{i=1}^k I_{x_{i,n}}\right)-\theta^k\right|
\leq k\varepsilon+|\mathbb P(B)^k-\theta^k|\leq2k\varepsilon.$$</div>
<p>Let $r_n=\min_{i\ne j}\|x_{i,n}-x_{j,n}\|_\infty$. Uniqueness implies that all the marks on infinite clusters are connected. If instead all marks are connected in a finite cluster, that of $x_{1,n}$ reaches distance at least $r_n$. Hence the difference between the connectivity probability and $\mathbb P(\bigcap_i I_{x_{i,n}})$ lies between zero and</p>
<div class="math-display">$$\mathbb P\bigl(|K_0|&lt;\infty,\ K_0\not\subset B_{r_n-1}(0)\bigr)\longrightarrow0.$$</div>
<p>The limit follows because every finite vertex set is bounded. This uses neither local finiteness of the random graph nor an exponential finite-cluster tail. Let $\varepsilon\downarrow0$. For $k=2,3$ and $\theta&gt;0$, division gives the ratio limit. If $\theta=0$, both connection limits are zero and this division is unavailable.</p>
<p>This justifies the supercritical observation in Gladkov section 6.3 under its intended uniqueness hypothesis. Existence of an infinite cluster alone is insufficient to replace membership in infinite clusters by mutual connection.</p>

## Relative errors for rare connections {#section-rare-coupling-ratio}

<a id="tag-KJWA" data-assertion="proposition" data-title="A successful coupling controls a rare-event ratio when failure probabilities have the same scale"></a>
<p>On a common probability space, let $X,Y,S$ be events with $X\cap S=Y\cap S$ up to null sets. Suppose $\mathbb P(S^c)\leq\varepsilon&lt;1$ and there are $a,c,C&gt;0$ such that</p>
<div class="math-display">$$\mathbb P(X\cap S)\geq ca\mathbb P(S),\qquad
\max\{\mathbb P(X\cap S^c),\mathbb P(Y\cap S^c)\}\leq Ca\mathbb P(S^c).$$</div>
<p>Then $\mathbb P(Y)&gt;0$ and</p>
<div class="math-display">$$\left|\frac{\mathbb P(X)}{\mathbb P(Y)}-1\right|\leq\frac{C\varepsilon}{c(1-\varepsilon)}.$$</div>
<p><em>Proof.</em> The contributions on $S$ cancel. Each remaining contribution lies in $[0,Ca\varepsilon]$, so their difference has absolute value at most $Ca\varepsilon$. The denominator is at least the common success contribution $ca(1-\varepsilon)$.</p>
<p>The common scale $a$ matters when the events become rare. For $0&lt;\varepsilon&lt;1$, take $\mathbb P(S^c)=\varepsilon$, $X=S^c$, and $Y\subset S^c$ of probability $\varepsilon^2$. The events agree on $S$, yet their probability ratio is $1/\varepsilon$. A coupling that succeeds with probability tending to one gives only an additive error without further estimates.</p>
<p>This is the ratio step in <a href="https://arxiv.org/html/1502.04387v3#S3.SS1">Conijn, Proposition 10, (3.12)–(3.17)</a>. There the missing scale control is supplied by one-arm estimates conditional on the explored exterior. The annular coupling and those estimates are cited inputs here; they are not consequences of the elementary proposition alone.</p>

## The boundary factorization constant {#section-boundary-factorization}

<a id="tag-XCYH" data-assertion="proposition" data-title="Boundary and bulk density formulas give a position-independent factorization ratio"></a>
<p>Let $x&lt;y$ be real, $w\in\mathbb H$, $h=\operatorname{Im}w$, $L=y-x$ and $d_x=|w-x|$, $d_y=|w-y|$. For positive constants $A,B,D$, suppose three functions satisfy</p>
<div class="math-display">$$P_2(x,y)=A L^{-2/3},\qquad P_3(u,w)=B h^{11/48}|w-u|^{-2/3}\quad(u\in\{x,y\}),\qquad
P_4(x,y,w)=P_2(x,y)D(\sin\zeta)^{1/3}h^{-5/48},$$</div>
<p>where $\zeta\in(0,\pi)$ is the angle at $w$ in the triangle with vertices $x,y,w$. Then</p>
<div class="math-display">$$\frac{P_4(x,y,w)^2}{P_2(x,y)P_3(x,w)P_3(y,w)}=\frac{AD^2}{B^2}.$$</div>
<p>For the Beliaev–Izyurov normalizations, this constant is</p>
<div class="math-display">$$K_F=\frac{2^7\pi^5}{3^{3/2}\Gamma(1/3)^9},\qquad \sqrt{K_F}=1.0299267867\ldots.$$</div>
<p><em>Proof.</em> The area of the triangle gives $\sin\zeta=Lh/(d_xd_y)$. Therefore $P_4=AD L^{-1/3}h^{11/48}(d_xd_y)^{-1/3}$, and all positional factors cancel in the quotient.</p>
<p>To evaluate the constant, set</p>
<div class="math-display">$$H={}_2F_1(-1/2,-1/3;7/6;1),\quad
K_3=\frac{\sqrt\pi}{\Gamma(1/3)\Gamma(7/6)},\quad K_5=\frac{K_4(\pi/2)^{5/48}}{H}.$$</div>
<p>The source formulas use $A=2^{1/3}K_3$, $B=2^{-5/48}K_4$ and $D=2^{1/3}\pi^{-5/48}K_5$. Thus $AD^2/B^2=2K_3/H^2$. Gauss summation, whose convergence condition here is $7/6+1/2+1/3=2&gt;0$, gives $H=\Gamma(7/6)/(\Gamma(5/3)\Gamma(3/2))$. Use $\Gamma(5/3)=(2/3)\Gamma(2/3)$, $\Gamma(3/2)=\sqrt\pi/2$, and $\Gamma(7/6)=\Gamma(1/6)/6$. The duplication and reflection identities</p>
<div class="math-display">$$\Gamma(1/6)\Gamma(2/3)=2^{2/3}\sqrt\pi\Gamma(1/3),\qquad
\Gamma(1/3)\Gamma(2/3)=\frac{2\pi}{\sqrt3}$$</div>
<p>then give the displayed value.</p>
<p>This proves the algebra in <a href="https://arxiv.org/html/1011.5822v3#S4">Beliaev–Izyurov, Proposition 4.1</a>, conditional on their density formulas. Their SLE derivation is not reproduced. In (20), the second bulk-boundary factor must use the surviving boundary point $u_3$, not the shrinking interval endpoint $u_2$; see the <a href="/errata/beliaev-izyurov-factorization-2012/#surviving-boundary-point">provisional erratum</a>.</p>

<a id="tag-JM5A" data-assertion="theorem" data-title="Two boundary sites and one bulk site have the triangular-lattice factorization limit"></a>
<p>Consider independent site percolation with parameter $1/2$ on a triangular lattice of mesh $\eta$ restricted to the closed upper half-plane, with free boundary. Fix distinct $x,y\in\mathbb R$ and $w\in\mathbb H$, using the containing-hexagon convention for marks. Then</p>
<div class="math-display">$$\lim_{\eta\downarrow0}
\frac{\mathbb P_\eta(x\leftrightarrow y\leftrightarrow w)}
{\sqrt{\mathbb P_\eta(x\leftrightarrow y)\mathbb P_\eta(x\leftrightarrow w)\mathbb P_\eta(y\leftrightarrow w)}}=\sqrt{K_F}.$$</div>
<p><em>Idea of the proof.</em> Small neighbourhoods replace the marks: an interval at each boundary point, and at $w$ the requirement that the conformal radius of the region left by the boundary-attached clusters be small. For neighbourhoods of fixed size the connection probabilities have scaling limits, and for suitably small neighbourhoods the ratio of the limits is close to $K_F$; the <a href="/tag/XCYH/">boundary factorization constant</a> is the algebra that makes this limit independent of the positions. The <a href="/tag/IP6C/">point-completion transfer</a> shows that, under critical triangular-site <a href="/articles/planar-factorization/#section-site-rsw">RSW</a>, completing the neighbourhoods to the marks changes the squared ratio by a factor close to one, uniformly in the mesh. The theorem follows by taking the positive square root.</p>
:::details Proof (from cited results)
<p>The ratio is symmetric in $x$ and $y$, so we may assume $x&lt;y$. All probabilities below refer to independent site percolation with parameter $1/2$ on the triangular lattice of mesh $\eta$ in the closed upper half-plane, with free boundary and the containing-hexagon convention for marks. These are the conventions of the <a href="/tag/IP6C/">point-completion transfer</a>, and its discrete three-point squared ratio is the square of the ratio in the statement.</p>
<p>For $s_x,s_y,t&gt;0$ put $J_x=[x,x+s_x]$ and $J_y=[y-s_y,y+s_y]$, and let $\mathcal C(J)$ be the union of the open clusters meeting $J$. Let $E_{xy}$ be the event that $\mathcal C(J_x)$ meets $J_y$; let $E_{xw}$ be the event that the <a href="/articles/planar-factorization/#section-conformal-radius">conformal radius</a> at $w$ of the component of $w$ in $\mathbb H\setminus\mathcal C(J_x)$ is less than $t$ (it is zero when $w\in\mathcal C(J_x)$); let $E_{yw}$ be the same event for $\mathcal C(J_y)$; and let $E_{xyw}=E_{xy}\cap E_{xw}$. These are the four neighbourhood events of the <a href="/articles/planar-factorization/#section-point-lifting">point-completion transfer</a>, and also the events (2.3) of Conijn with $(u_1,u_2,s_1,s_2,s_3)=(x,y,s_x,s_y,t)$.</p>
<p>The transfer has two hypotheses besides critical triangular-site RSW. First, for fixed positive radii the probabilities of the four events must converge to positive limits $f_{xy},f_{xw},f_{yw},f_{xyw}$ as $\eta\downarrow0$. The limit for $E_{xy}$ exists by Smirnov's theorem on conformal invariance of crossing probabilities, which gives <a href="/articles/continuum-connection-densities/">Cardy's formula</a>; the limits for the events at $w$ exist because the percolation exploration path converges to <a href="/articles/sle-conformal-radius/">SLE$_6$</a>, and these events are determined by exploration paths started at $x+s_x$ and $y+s_y$, as Lawler, Schramm and Werner describe. The limits are positive: for fixed radii each event contains the intersection of finitely many crossing events of fixed rectangles in the half-plane (for $E_{xw}$ and $E_{yw}$, a chain of crossings from the interval to within distance $t/4$ of $w$, which makes the conformal radius less than $t$ by the <a href="/tag/7GOV/">distance comparison</a>), whose probability is bounded below uniformly in $\eta$ by RSW and the Harris inequality. Second, for every $\varepsilon,s_0&gt;0$ there must be radii $s_x,s_y,t\in(0,s_0)$ with</p>
<div class="math-display">$$\left|\frac{f_{xyw}^2}{f_{xy}f_{xw}f_{yw}}-K_F\right|&lt;\varepsilon.$$</div>
<p>This is Conijn's Theorem 3, which he deduces from Proposition 4.1 of Beliaev and Izyurov (their Remark 4); the constant is the one evaluated in the <a href="/tag/XCYH/">boundary factorization constant</a>. The point-completion transfer now gives that the squared lattice ratio tends to $K_F$. The proof of its <a href="/tag/XP8A/">comparison of point completions</a> supplies the uniform conditional one-arm estimates that the <a href="/tag/KJWA/">relative coupling estimate</a> requires. For fixed $\eta$ every probability in the ratio is positive, since a finite open path joins any two marks with positive probability, so the ratio is the positive square root of the squared ratio. Continuity of the square root gives the limit $\sqrt{K_F}$.</p>
:::
<p>The proof uses Smirnov's theorem and is therefore specific to critical site percolation on the triangular lattice. The same transfer gives the <a href="/tag/7O0U/">boundary-interval attachment formula</a>, in which the two marks may lie in different clusters meeting the interval.</p>

## The bulk constant and the choice of cluster colour {#section-bulk-factorization}

<a id="tag-R9NU" data-assertion="theorem" data-title="Critical triangular-site bulk three-point ratios have the Delfino–Viti limit"></a>
<p>For critical site percolation on the full triangular lattice of mesh $\delta$, fix three distinct points $z_1,z_2,z_3\in\mathbb C$ and choose lattice approximations $z_i^\delta\to z_i$. Writing $P_n^\delta$ for the probability that the $n$ specified marks lie in one <em>open</em> cluster, the ratio
</p>
<div class="math-display">$$\frac{P_3^\delta(z_1^\delta,z_2^\delta,z_3^\delta)}{\sqrt{P_2^\delta(z_1^\delta,z_2^\delta)P_2^\delta(z_1^\delta,z_3^\delta)P_2^\delta(z_2^\delta,z_3^\delta)}}$$</div>
<p>converges to</p>
<div class="math-display">$$R_{\mathrm{bulk}}=
\sqrt2\, b^{-1/6}\sqrt{\frac{\Gamma(2/3)}{\Gamma(1/3)}}
\frac{\Upsilon_b(b/8)\Upsilon_b(7b/8)^3}
{\Upsilon_b(b)[\Upsilon_b(3b/4)\Upsilon_b(b/4)]^{3/2}}
=1.022013133\ldots,\qquad b=\sqrt{2/3}.$$</div>
<p>Here, for $0&lt;x&lt;Q=b+b^{-1}$, the normalization of the positive special function is</p>
<div class="math-display">$$\log\Upsilon_b(x)=\int_0^\infty\frac{1}{t}\left[(Q/2-x)^2e^{-t}-\frac{\sinh^2((Q/2-x)t/2)}{\sinh(bt/2)\sinh(t/(2b))}\right]dt.$$</div>
<p>The integral converges: its bracket is $O(t)$ at zero, and both terms decay exponentially at infinity when $0&lt;x&lt;Q$. All the displayed arguments lie in that interval.</p>
<p><em>Idea of the proof (cited result).</em> The proof of Ang, Cai, Sun and Wu has two parts. The first is the passage to the continuum. With $\pi_\delta$ the probability that the origin is connected to the unit circle, the normalized probabilities $\pi_\delta^{-n}P_n^\delta$ converge to conformally covariant limits $P_n$ (Camia). The interfaces between open and closed clusters converge to the conformal loop ensemble CLE$_6$ (Camia–Newman), and Ang–Cai–Sun–Wu, Proposition 1.2, expresses $P_n$ through the $n$-point Green function $G_n$ of the natural measure of Miller and Schoug on the clusters of CLE$_6$; this produces the factor $\sqrt2$. The second part takes place in the continuum. Conformal covariance reduces the ratio to a single constant. That constant is computed by coupling CLE$_6$ with Liouville quantum gravity: conformal welding of quantum surfaces expresses the three-point statistic of CLE$_6$ through structure constants of Liouville theory, and this yields the imaginary DOZZ formula displayed above.</p>
:::details Verification of the colour factor $\sqrt2$ and of the displayed formula
<p>If $\pi_\delta^{-n}P_n^\delta\to P_n$ for $n=2,3$, with positive two-point limits, the powers of $\pi_\delta$ cancel in the ratio, which therefore converges to $P_3/\sqrt{P_2P_2P_2}$, the three factors $P_2$ being evaluated at the three pairs. Ang–Cai–Sun–Wu, Proposition 1.2, identifies $2P_n=\mathfrak C^nG_n$, where $G_n$ counts clusters of both colours. Consequently</p>
<div class="math-display">$$\frac{P_3}{\sqrt{P_2P_2P_2}}=\sqrt2\,\frac{G_3}{\sqrt{G_2G_2G_2}}.$$</div>
<p>The mass normalization $\mathfrak C$ cancels; the colour factor does not. Conformal covariance fixes the dependence on the three pair distances but does not determine this constant.</p>
<p>The displayed formula for $R_{\mathrm{bulk}}$ is the imaginary DOZZ expression of Ang–Cai–Sun–Wu, Theorem 1.1, at $b=\sqrt{2/3}$, simplified by $1/(4b)-b/2=-b/8$ and $b^{-2}-b^2-1=-1/6$.</p>
:::
<p>The theorem concerns critical site percolation on the triangular lattice. For bond percolation on $\mathbb Z^2$ the corresponding ratio is bounded above and below, uniformly over triples, by the <a href="/articles/critical-exponents/#section-planar-three-point-scales">two-scale three-point comparison</a>.</p>

## History and attribution {#section-history}

<p>For two points on the boundary of the half-plane and one inside it, Simmons, Kleban and Ziff (2007) derived the factorization constant by conformal field theory. Beliaev and Izyurov (2012) proved the continuum version for small neighbourhoods of the marks, using SLE$_6$, and Conijn (2015, Theorem 1) proved the limit of the squared lattice ratio for critical triangular-site percolation; the <a href="/tag/JM5A/">boundary factorization limit</a> is its positive square root. The continuum limits of the neighbourhood events rest on Smirnov's proof of conformal invariance and Cardy's formula (2001) and on the convergence of the exploration path to SLE$_6$ (Smirnov 2001; Camia and Newman 2007), through which Lawler, Schramm and Werner (2002) describe the events at the interior point.</p>

<p>For three points in the plane, Delfino and Viti (2010) conjectured the value of the three-point ratio, by an imaginary-coupling version of the DOZZ formula for the structure constants of Liouville theory. Camia (2024) proved that the normalized connection probabilities converge to conformally covariant limits, and Ang, Cai, Sun and Wu (Theorem 1.1) proved the conjecture for critical triangular-site percolation: this is the <a href="/tag/R9NU/">bulk three-point limit</a>. Gladkov (2024), who proves the bound $2\sqrt2$ for the ratio on every graph, records in a footnote that Ang, Cai, Sun and Wu had announced this proof.</p>

## References {#section-references}

<ul>
<li>M. Ang, G. Cai, X. Sun and B. Wu, Integrability of conformal loop ensemble: imaginary DOZZ formula and beyond, <a href="https://arxiv.org/abs/2107.01788">arXiv:2107.01788</a>.</li>
<li>D. Beliaev and K. Izyurov, A proof of factorization formula for critical percolation, <em>Comm. Math. Phys.</em> 310 (2012), 611–623; <a href="https://arxiv.org/abs/1011.5822">arXiv:1011.5822</a>.</li>
<li>F. Camia, Conformal covariance of connection probabilities and fields in 2D critical percolation, <em>Comm. Pure Appl. Math.</em> 77 (2024), 2138–2176; <a href="https://arxiv.org/abs/2203.08167">arXiv:2203.08167</a>.</li>
<li>F. Camia and C. M. Newman, Critical percolation exploration path and SLE$_6$: a proof of convergence, <em>Probab. Theory Related Fields</em> 139 (2007), 473–519; <a href="https://arxiv.org/abs/math/0604487">arXiv:math/0604487</a>.</li>
<li>F. Camia and C. M. Newman, Two-dimensional critical percolation: the full scaling limit, <em>Comm. Math. Phys.</em> 268 (2006), 1–38; <a href="https://arxiv.org/abs/math/0605035">arXiv:math/0605035</a>.</li>
<li>R. Conijn, Factorization formulas for 2D critical percolation, revisited, <a href="https://arxiv.org/abs/1502.04387">arXiv:1502.04387</a>.</li>
<li>G. Delfino and J. Viti, On three-point connectivity in two-dimensional percolation, <em>J. Phys. A</em> 44 (2011), 032001; <a href="https://arxiv.org/abs/1009.1314">arXiv:1009.1314</a>.</li>
<li>N. Gladkov, Percolation inequalities and decision trees, <a href="https://arxiv.org/abs/2408.08457">arXiv:2408.08457</a>.</li>
<li>G. F. Lawler, O. Schramm and W. Werner, One-arm exponent for critical 2D percolation, <em>Electron. J. Probab.</em> 7 (2002), no. 2; <a href="https://arxiv.org/abs/math/0108211">arXiv:math/0108211</a>.</li>
<li>J. J. H. Simmons, P. Kleban and R. M. Ziff, Exact factorization of correlation functions in two-dimensional critical percolation, <em>Phys. Rev. E</em> 76 (2007), 041106; <a href="https://arxiv.org/abs/0706.4105">arXiv:0706.4105</a>.</li>
<li>S. Smirnov, Critical percolation in the plane: conformal invariance, Cardy's formula, scaling limits, <em>C. R. Acad. Sci. Paris Sér. I Math.</em> 333 (2001), 239–244.</li>
</ul>
