---
{
  "id": "countable-reimer",
  "title": "Reimer on a countable edge set",
  "subtitle": "Infinite certificates, outer probability and measurable applications",
  "kind": "theorem",
  "category": "Inequalities",
  "summary": "Finite Reimer extends to the full countable Bernoulli product, even with infinite certificates, as an outer-probability bound. Increasing Borel and G-delta events have measurable disjoint occurrence. Closed-edge certificates give a direct path application.",
  "context": [
    "The coordinate set $E$ is countable and $\\Omega=\\{0,1\\}^E$ has its product topology and independent law $\\mu_q$, with arbitrary $q_e\\in[0,1]$.",
    "Certificates force an event for every completion, including configurations of probability zero. They may record both open and closed coordinates.",
    "The nonmonotone conclusions use the finite Reimer theorem as a cited input. The increasing-event conclusion also has a proof using the existing finite BK theorem alone."
  ],
  "related": [
    "bk-inequality",
    "disjoint-occurrence",
    "intrinsic-geometry",
    "cutoff-hydrodynamics"
  ],
  "sourceIds": [
    "hutchcroft-book",
    "borgs-chayes-randall-1998",
    "arratia-garibaldi-hales-2015",
    "hutchcroft-lin-pims-2025"
  ],
  "aliases": [
    "countable Reimer",
    "infinite witnesses",
    "infinite certificates",
    "outer probability BK",
    "nonmonotone BK"
  ],
  "prototypeUses": []
}
---

## Which disjoint occurrence? {#section-certificates}

<p>For $K\subseteq E$, write $[\omega]_K=\{\eta:\eta|_K=\omega|_K\}$. We distinguish</p>
<div class="math-display">$$A\square_\infty B
=\{\omega:\exists K,L\subseteq E,\ K\cap L=\varnothing,\
[\omega]_K\subseteq A,\ [\omega]_L\subseteq B\}$$</div>
<p>from $A\square_f B$, where $K,L$ must be finite. The latter is the existing wiki convention for $A\circ B$. No existing definition is changed here.</p>
<p>The difference persists in a Bernoulli product. If $E=\mathbb N$ and $A$ is the event that infinitely many coordinates are open, then $A\square_f A=\varnothing$, whereas $A\square_\infty A=A$: partition any infinite set of open coordinates into two infinite subsets. Thus exhaustion of finite certificates alone cannot prove the full-witness statement.</p>
<p>We use the finite nonmonotone Reimer theorem: for arbitrary events in any finite Bernoulli product, disjoint occurrence has probability at most the product of their probabilities. For the fair product we also use its sharper form $|A\square B|\le |A\cap\bar B|$, where $\bar B=\{1-\omega:\omega\in B\}$. These are cited finite results, not consequences of the wiki's increasing-event proof. The first is <a href="https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-98-42.pdf">Theorem 2.1 of Borgs–Chayes–Randall</a>; the second follows from their Lemma 4.1 by choosing disjoint certificates and enlarging one to complement the other.</p>

## Finite certificates on the infinite product {#section-finite-certificates}

<a id="tag-LLAT" data-assertion="proposition" data-title="Finite Reimer extends to countable products with finite certificates"></a>
<p>Assume finite nonmonotone Reimer. For Borel $A,B\subseteq\Omega$, the set $A\square_f B$ is open and</p>
<div class="math-display">$$\mu_q(A\square_f B)\le\mu_q(A)\mu_q(B).$$</div>
<p>For the fair law $\mu_{1/2}$, the sharper finite inequality gives</p>
<div class="math-display">$$\mu_{1/2}(A\square_f B)\le\mu_{1/2}(A\cap\bar B).$$</div>
<p><em>Proof.</em> Exhaust $E$ by finite sets $E_n$. On the finite cube define
$A_n=\{a:\{\omega:\omega|_{E_n}=a\}\subseteq A\}$, and define $B_n$ in the same way. Disjoint occurrence of $A_n,B_n$, lifted to $\Omega$, is exactly the event $D_n$ that certificates for $A,B$ can be chosen inside $E_n$. For example, a certificate for $A_n$ says that every prefix agreeing on its coordinates lies in $A_n$, hence every full configuration agreeing there lies in $A$. The converse follows by restricting a full certificate.</p>
<p>The cylinder sets $D_n$ increase to $A\square_f B$. The lifts of $A_n,B_n$ are contained in $A,B$, respectively. Apply finite Reimer and continuity from below. For the sharper bound, the lift of $A_n\cap\bar B_n$ lies in $A\cap\bar B$, which gives the second conclusion. Finally, finite certificates specify basic open cylinders, so their union $A\square_f B$ is open; this last fact does not even require $A,B$ to be Borel.</p>
<p>This is the Bernoulli specialization of the finite-certificate reduction in <a href="https://arxiv.org/pdf/1508.05337v3">Arratia–Garibaldi–Hales, Section 7, Theorem 9</a>. It does not say that the lifts of $A_n$ exhaust $A$.</p>

## Compactness removes infinite certificates for open events {#section-open-events}

<a id="tag-1NUW" data-assertion="proposition" data-title="An arbitrary certificate for an open Bernoulli event contains a finite certificate"></a>
<p>If $U\subseteq\Omega$ is open and $[\omega]_K\subseteq U$, there is a finite $F\subseteq K$ with $[\omega]_F\subseteq U$. Consequently, for open $U,V$,</p>
<div class="math-display">$$U\square_\infty V=U\square_f V.$$</div>
<p><em>Proof.</em> Otherwise every compact set $[\omega]_{K\cap E_n}$ meets the closed set $U^c$. These nonempty compact intersections are nested, so their intersection is nonempty. A point in it belongs to $[\omega]_K\cap U^c$, a contradiction. Apply the result to each of two disjoint certificates; taking subsets preserves disjointness.</p>
<p>Compactness is used for the space of all completions, not for the event $U$. The finite certificate need not force the original event when $U$ is only an open enlargement of it.</p>

## The full countable extension {#section-outer-bound}

<a id="tag-BBOR" data-assertion="theorem" data-title="Reimer bounds arbitrary infinite certificates in outer probability"></a>
<p>Assume finite nonmonotone Reimer. For any Borel $A,B\subseteq\{0,1\}^E$ and countable $E$,</p>
<div class="math-display">$$\mu_q^*(A\square_\infty B)\le\mu_q(A)\mu_q(B),$$</div>
<p>where $\mu_q^*$ denotes outer probability. Under the fair law, the sharper finite theorem also gives</p>
<div class="math-display">$$\mu_{1/2}^*(A\square_\infty B)
\le\mu_{1/2}(A\cap\bar B).$$</div>
<p>If $A\square_\infty B$ is measurable in the completion, its ordinary probability satisfies the same bound. Neither conclusion requires finite witnesses, local finiteness of a graph, or finite susceptibility.</p>
<p><em>Proof.</em> A Borel probability on the compact metrizable space $\Omega$ is regular. For $\varepsilon>0$, choose open $U\supseteq A$ and $V\supseteq B$ with
$\mu_q(U\setminus A)<\varepsilon$ and $\mu_q(V\setminus B)<\varepsilon$. Certificates forcing $A,B$ force $U,V$, so the preceding two results give</p>
<div class="math-display">$$\mu_q^*(A\square_\infty B)
\le\mu_q(U\square_\infty V)
=\mu_q(U\square_f V)
\le\mu_q(U)\mu_q(V)
\le(\mu_q(A)+\varepsilon)(\mu_q(B)+\varepsilon).$$</div>
<p>Let $\varepsilon$ decrease to zero. For the fair law, apply instead the sharper finite-certificate bound. The bit flip preserves $\mu_{1/2}$, and</p>
<div class="math-display">$$
(U\cap\bar V)\setminus(A\cap\bar B)
\subseteq (U\setminus A)\cup(\bar V\setminus\bar B).
$$</div>
<p>Its measure is less than $2\varepsilon$, proving the sharper conclusion. The bit-flip comparison is asserted only for the fair law.</p>
<p>The argument establishes an upper bound without asserting measurability of an arbitrary full-witness combination. In particular, it does not justify replacing outer probability by probability for all Borel $A,B$.</p>

## When ordinary probability is available {#section-measurability}

<a id="tag-4LXO" data-assertion="proposition" data-title="Increasing Borel and G-delta events have universally measurable full disjoint occurrence"></a>
<p>The set $A\square_\infty B$ is analytic, hence universally measurable, in either of the following cases: $A,B$ are increasing Borel events; or $A,B$ are $G_\delta$ sets. Thus Reimer's outer bound becomes an ordinary probability bound for these classes. For increasing Borel events the product bound can also be proved from finite increasing-event BK alone, without nonmonotone Reimer.</p>
<p><em>Proof.</em> Identify a subset $K\subseteq E$ with its indicator in $\{0,1\}^E$. If $A$ is increasing,</p>
<div class="math-display">$$[\omega]_K\subseteq A
\quad\Longleftrightarrow\quad \omega\cap K\in A,$$</div>
<p>where configurations are identified with their open-coordinate sets. Indeed, $\omega\cap K$ is the least completion agreeing with $\omega$ on $K$. The map $(\omega,K)\mapsto\omega\cap K$ is continuous. Consequently the conditions $\omega\cap K\in A$, $\omega\cap L\in B$, $K\cap L=\varnothing$ define a Borel subset of $\Omega^3$. Its projection onto $\omega$ is the required analytic set.</p>
<p>For an open $U$, the relation $R_U=\{(\omega,K):[\omega]_K\subseteq U\}$ is open: by the compactness lemma it is the union, over finite $F$ and patterns $a$ whose cylinder lies in $U$, of the clopen conditions $F\subseteq K$, $\omega|_F=a$. If $A=\bigcap_n U_n$ is $G_\delta$, then $R_A=\bigcap_n R_{U_n}$ is Borel. Do this for $B$ too, intersect with the closed disjointness condition, and project. No monotonicity is needed for this second case.</p>
<p>To obtain increasing BK without nonmonotone Reimer, begin with any open $U\supseteq A$ and define</p>
<div class="math-display">$$U^\uparrow
=\{\omega:[\omega,1]\subseteq U\},\qquad
[\omega,1]=\{\eta:\eta\supseteq\omega\}.$$</div>
<p>Then $A\subseteq U^\uparrow\subseteq U$. The compactness lemma, applied to the certificate consisting of the open coordinates of $\omega$, expresses $U^\uparrow$ as a union of finite all-open cylinders. Thus it is open and increasing. Its measure can be made arbitrarily close to $\mu_q(A)$ by outer regularity; construct $V^\uparrow$ for $B$ likewise. Their full disjoint occurrence equals their finite-certificate version. Apply existing <a href="/tag/JRCI/">countable finite-witness BK</a> and let the enlargement errors vanish. The analytic-set argument already permits ordinary probability.</p>
<p>For arbitrary Borel events the forcing relation contains a universal quantifier over completions, followed in $\square_\infty$ by an existential quantifier over certificate sets. The preceding Borel projection proofs do not cover that case. The universally measurable classes above and the general outer bound are the precise conclusions proved here.</p>

## A path prefix and all closed edges {#section-closed-edge-application}

<a id="tag-SD39" data-assertion="corollary" data-title="A decreasing constraint can be separated from a path suffix on a countable graph"></a>
<p>Assume finite nonmonotone Reimer. Let $G$ be a countable simple graph with independent, possibly inhomogeneous bonds, and let $D$ be a decreasing Borel event. For vertices $o,w,z$, let $H$ be the event that $D$ holds and some finite simple open path from $o$ to $z$ passes through $w$. Then</p>
<div class="math-display">$$\mathbb P(H)
\le \mathbb P(\{o\leftrightarrow w\}\cap D)\,
\mathbb P(w\leftrightarrow z).$$</div>
<p>The graph may have infinite degrees. The assertion permits $D=\{\sum_v a_v\mathbf1_{\{o\leftrightarrow v\}}\le m\}$ for deterministic $a_v\ge0$ and finite $m$, including the usual cluster-volume cutoff. No finiteness of the cluster or its expectation is assumed.</p>
<p><em>Proof.</em> On $H$, split the chosen simple path at $w$, with edge sets $P_1,P_2$. Put $K=P_1\cup(E\setminus\omega)$ and $L=P_2$. These certificates are disjoint. Every configuration agreeing with $\omega$ on $K$ contains the prefix and is a subset of $\omega$, so it belongs to $\{o\leftrightarrow w\}\cap D$. The suffix forces $w\leftrightarrow z$. Hence</p>
<div class="math-display">$$H\subseteq
(\{o\leftrightarrow w\}\cap D)\square_\infty\{w\leftrightarrow z\}.$$</div>
<p>The event $H$ is Borel, since there are countably many finite paths. Apply the outer bound to this inclusion. For the weighted example, each connection indicator is lower semicontinuous and the nonnegative countable sum is lower semicontinuous, so its sublevel set is closed and decreasing. Empty prefix or suffix certificates cover coincident endpoints whenever the required simple path exists.</p>
<p>This supplies a direct full-edge-set estimate of the kind used in <a href="/tag/X86B/">X86B</a>: an infinite collection of closed edges is a legitimate certificate. The existing finite-restriction proof and its hypotheses remain unchanged. The finite nonmonotone theorem is still a cited input; this countable extension does not constitute a new Lean proof of it or of the downstream hydrodynamic statements.</p>

## An open event makes the full combination Borel {#section-open-partner}

<p>The measurability problem disappears when one of the two events is open. This includes every finite connection event, even on a graph of infinite degree. The other event need not be monotone.</p>

<a id="tag-AWBF" data-assertion="theorem" data-title="Full disjoint occurrence of a Borel event with an open event is Borel"></a>
<p>Let $A\subseteq\Omega$ be Borel and $U\subseteq\Omega$ open. For finite $F\subseteq E$, let $T_{F,b}\omega$ replace the coordinates in $F$ by $b\in\{0,1\}^F$, and put</p>
<div class="math-display">$$A^{\langle F\rangle}=\bigcap_{b\in\{0,1\}^F}T_{F,b}^{-1}(A),\qquad U_F=\{\omega:[\omega]_F\subseteq U\}.$$</div>
<p>Then</p>
<div class="math-display">$$A\square_\infty U=\bigcup_{F\subseteq E\text{ finite}}\left(A^{\langle F\rangle}\cap U_F\right).$$</div>
<p>In particular, $A\square_\infty U$ is Borel. Assuming finite nonmonotone Reimer, its ordinary probability satisfies</p>
<div class="math-display">$$\mu_q(A\square_\infty U)\le\mu_q(A)\mu_q(U).$$</div>
<p>For the fair law, the sharper finite theorem gives the additional bound $\mu_{1/2}(A\square_\infty U)\le\mu_{1/2}(A\cap\bar U)$.</p>
<p><em>Proof.</em> Suppose $K,L$ are disjoint certificates for $A,U$. By <a href="/tag/1NUW/">1NUW</a>, a finite subset $F\subseteq L$ still forces $U$. Since $K\subseteq E\setminus F$, every configuration agreeing with $\omega$ on $E\setminus F$ belongs to $A$. These configurations are precisely the finitely many $T_{F,b}\omega$, so $\omega\in A^{\langle F\rangle}\cap U_F$.</p>
<p>Conversely, membership in this intersection gives the disjoint certificates $E\setminus F$ and $F$. This proves the identity. Each replacement map is continuous, so $A^{\langle F\rangle}$ is Borel. The set $U_F$ is a union of finitely many cylinders specified on $F$, hence clopen. There are countably many finite subsets of $E$; the union is therefore Borel. Apply <a href="/tag/BBOR/">BBOR</a> for the probability bounds.</p>
<p>The certificate $E\setminus F$ may be infinite. The identity does not replace full disjoint occurrence by the finite-certificate operation. For example, on $E=\mathbb N$, let $A$ require infinitely many open coordinates and let $U$ require coordinate $0$ to be open. Then $A\square_\infty U=A\cap U$, whereas $A\square_f U=\varnothing$.</p>

## Increasing and decreasing constraints together {#section-order-convex}

<p>A set $A\subseteq\Omega$ is order-convex if $x,z\in A$ and $x\le y\le z$ imply $y\in A$, with the coordinatewise order. Intersections of increasing and decreasing events have this property. More generally, countably many upper and lower bounds on Borel increasing observables define an order-convex Borel event.</p>

<a id="tag-593F" data-assertion="proposition" data-title="An endpoint test gives measurable full disjoint occurrence for order-convex events"></a>
<p>If $A$ is order-convex, then</p>
<div class="math-display">$$[\omega]_K\subseteq A\quad\Longleftrightarrow\quad \omega\cap K\in A\ \text{ and }\ \omega\cup(E\setminus K)\in A.$$</div>
<p>Thus the forcing relation $R_A=\{(\omega,K):[\omega]_K\subseteq A\}$ is Borel whenever $A$ is order-convex and Borel. If each of $A,B$ is either order-convex Borel or $G_\delta$, then $A\square_\infty B$ is analytic, hence measurable in the completion of every Borel probability. Assuming finite nonmonotone Reimer,</p>
<div class="math-display">$$\mu_q(A\square_\infty B)\le\mu_q(A)\mu_q(B).$$</div>
<p><em>Proof.</em> The two configurations in the displayed test are the least and greatest members of $[\omega]_K$. Necessity follows by choosing those completions; sufficiency follows from order-convexity. Both endpoint maps are continuous, so the test expresses $R_A$ as the intersection of two Borel preimages. For a $G_\delta$ input, the forcing relation is Borel by the proof of <a href="/tag/4LXO/">4LXO</a>. In either case, intersect the two forcing relations with the closed condition $K\cap L=\varnothing$ and project onto $\omega$. The projection is analytic, and BBOR gives the inequality.</p>
<p>For a countable percolation graph this covers, for example, a connection requirement together with upper and lower bounds on weighted cluster volume. Connection is increasing and Borel; the volume is a countable sum of nonnegative connection indicators and is therefore increasing and Borel. In particular, $\{o\leftrightarrow w\}\cap D$ is order-convex Borel for every decreasing Borel $D$, not only for closed volume constraints.</p>

## A countable family of disjoint reasons {#section-countable-family}

<p>For a nonempty finite or countably infinite index set $I$, define simultaneous full disjoint occurrence by</p>
<div class="math-display">$$\mathcal D_I(A_i)=\left\{\omega:\exists(K_i)_{i\in I},\ K_i\cap K_j=\varnothing\ (i\ne j),\ [\omega]_{K_i}\subseteq A_i\ (i\in I)\right\}.$$</div>
<p>This definition requires one jointly disjoint family of certificates. It does not assume that repeated binary disjoint occurrence is associative.</p>

<a id="tag-UFCR" data-assertion="theorem" data-title="Reimer for finite and countable simultaneous families of full certificates"></a>
<p>Assume finite nonmonotone Reimer. For Borel events $(A_i)_{i\in I}$,</p>
<div class="math-display">$$\mu_q^*(\mathcal D_I(A_i))\le\prod_{i\in I}\mu_q(A_i).$$</div>
<p>The countable product is the infimum of the products over finite subsets. If every $A_i$ is either order-convex Borel or $G_\delta$, then $\mathcal D_I(A_i)$ is analytic and the bound holds for ordinary completed probability. For arbitrary Borel inputs, a zero product still implies that $\mathcal D_I(A_i)$ is measurable in the $\mu_q$-completion and has probability zero.</p>
<p><em>Proof.</em> First let $I=\{1,\ldots,r\}$ and all inputs be open. Each certificate can be reduced to a finite subset by 1NUW. The union of the resulting $r$ certificates is finite, so it lies in one set of a finite exhaustion of $E$. At each level, the finite input for $U_i$ consists of prefixes whose whole cylinder lies in $U_i$; its lifted probability is at most $\mu_q(U_i)$. The simultaneous event is exactly the disjoint occurrence of these finite inputs, as in the proof of <a href="/tag/LLAT/">LLAT</a>.</p>
<p>In a finite cube, the product bound follows by induction from binary Reimer: the union of the first $r-1$ certificates forces their simultaneous occurrence and is disjoint from the last certificate. Hence simultaneous $r$-fold occurrence is contained in the binary disjoint occurrence of the first $r-1$ simultaneous event with the last event. Apply binary Reimer and induction, then continuity from below over the exhaustion. This proves the bound for open inputs.</p>
<p>For Borel inputs, choose open $U_i\supseteq A_i$ with $\mu_q(U_i)\le\mu_q(A_i)+\varepsilon$. Monotonicity under enlargement and the open case give</p>
<div class="math-display">$$\mu_q^*(\mathcal D_I(A_i))\le\prod_{i=1}^r(\mu_q(A_i)+\varepsilon).$$</div>
<p>Let $\varepsilon\downarrow0$. For countably infinite $I$, simultaneous occurrence implies occurrence for every finite subfamily. Apply the finite bound and take the infimum. No equality between the infinite event and an intersection of finite-subfamily events is needed.</p>
<p>For the measurability assertion, the witness space $(\{0,1\}^E)^I$ is Polish. Each forcing relation is Borel by the preceding endpoint test or the $G_\delta$ argument. Their countable intersection, together with all pairwise disjointness conditions, is Borel in $\Omega\times(\{0,1\}^E)^I$. Project onto $\Omega$. Finally, if the product is zero, the outer bound puts the event inside a Borel null set, which proves the last assertion by completeness.</p>
<p>For instance, if a Borel event has probability strictly below one, the event that countably many copies occur with pairwise disjoint full certificates has outer probability zero. This conclusion is about a simultaneous family; it uses neither a nesting identity nor a choice of compatible limits of finite witnesses.</p>

## Weighted path truncation on the full graph {#section-full-path-truncation}

<p>Return to a countable simple graph with independent inhomogeneous bonds. For each $z$ connected to $o$, choose a finite simple open path $\gamma_z$ measurably. Such a choice exists by enumerating the paths and taking the first open one. One may instead select a shortest path, then break ties using an enumeration at that length. Put</p>
<div class="math-display">$$\tau(w,z)=\mathbb P(w\leftrightarrow z),\qquad V_a(C_o)=\sum_{w\in C_o}a_w,\qquad L_a(\gamma_z)=\sum_{w\in\gamma_z}a_w,$$</div>
<p>where the deterministic weights $a_w,b_z$ are nonnegative finite numbers. Neither their sums nor the cluster sizes need be finite.</p>

<a id="tag-IQJM" data-assertion="theorem" data-title="A direct weighted path-tail estimate without finite susceptibility"></a>
<p>Assume finite nonmonotone Reimer. For every decreasing Borel event $D$ and every $\ell>0$,</p>
<div class="math-display">$$\mathbb E\left[\mathbf1_D\sum_{z\in C_o}b_z\mathbf1_{\{L_a(\gamma_z)>\ell\}}\right]\le\frac1\ell\sum_{w,z}a_w b_z\,\mathbb P(o\leftrightarrow w,D)\,\tau(w,z).$$</div>
<p>All quantities are interpreted as nonnegative extended sums or expectations. If $D=\{V_a(C_o)\le m\}$ with $0\le m<\infty$ and $\chi_b(w)=\sum_z b_z\tau(w,z)\le M<\infty$ for every $w$, the right side is at most</p>
<div class="math-display">$$\frac M\ell\mathbb E[V_a(C_o);V_a(C_o)\le m]\le\frac{Mm}{\ell}.$$</div>
<p>In particular, for a finite observation set $F$, taking $b_z=\mathbf1_{\{z\in F\}}$ gives</p>
<div class="math-display">$$\mathbb E\left[\mathbf1_D\sum_{z\in C_o\cap F}\mathbf1_{\{L_a(\gamma_z)\le\ell\}}\right]\ge\mathbb E[|C_o\cap F|;D]-\frac{|F|}{\ell}\mathbb E[V_a(C_o);D],\qquad D=\{V_a(C_o)\le m\}.$$</div>
<p>This estimate remains valid at parameters where the ordinary susceptibility is infinite.</p>
<p><em>Proof.</em> Markov's inequality for the path weight and nonnegative Tonelli bound the left side of the first assertion by</p>
<div class="math-display">$$\frac1\ell\sum_{w,z}a_wb_z\,\mathbb P(D,\ o\leftrightarrow z,\ w\in\gamma_z).$$</div>
<p>On each event in the sum, split $\gamma_z$ at $w$. The prefix together with all closed edges forces $A_w=\{o\leftrightarrow w\}\cap D$, and the disjoint suffix forces $U_{w,z}=\{w\leftrightarrow z\}$. The latter event is open. Thus the full disjoint occurrence $A_w\square_\infty U_{w,z}$ is Borel by the open-partner theorem, and its probability is at most $\mathbb P(A_w)\tau(w,z)$. This is also the certificate construction of <a href="/tag/SD39/">SD39</a>. Substitute this bound and sum.</p>
<p>Under the stated bound on $\chi_b$, sum first over $z$, then use $\sum_w a_w\mathbb P(o\leftrightarrow w,D)=\mathbb E[V_a(C_o);D]$. For finite $F$, one has $\chi_b(w)\le|F|$. The total observed count is bounded by $|F|$, so subtracting its bad-path part is legitimate and gives the last inequality. Every passage uses nonnegative sums; there is no subtraction of infinite expectations.</p>
<p>The argument works directly on the full countable edge set. It requires no stabilization of a finite root cluster and no dominated-convergence assumption. Taking unit endpoint weights when susceptibility is finite recovers the Reimer step used in <a href="/tag/X86B/">X86B</a>; the finite observation version remains useful when that finiteness fails. The finite nonmonotone theorem is still a cited input, and these additions do not assert new Lean evidence.</p>

<p>The <a href="/coverage/sources/countable-reimer/">reading map</a> separates the source's finite-certificate statements from these full-certificate deductions. Ordinary measurability for two completely arbitrary Borel inputs remains outside the results proved here.</p>


## The edges left after an infinite exploration {#section-terminal-exploration-law}

<p>Let $X=(X_e)_{e\in E}$ have the independent Bernoulli law $\mu_q$. An exploration chooses one previously unqueried coordinate at each step, or stops. Its choice is a measurable function of its previous queries and answers, and possibly of an independent random seed taking values in a standard Borel space. After stopping, record a halt symbol forever. The exploration may instead make infinitely many queries. Write $\mathcal H_n$ for the information in the seed and the first $n$ steps, $R_n$ for the queried set, and</p>
<div class="math-display">$$
\mathcal H_\infty=\sigma\Bigl(\bigcup_n\mathcal H_n\Bigr),
\qquad R_\infty=\bigcup_nR_n.
$$</div>
<p>The terminal transcript $h$ records the seed and the entire sequence of queries and answers. Let $R(h)$ be its queried set and $a_e(h)$ its answer at $e\in R(h)$. A transcript includes only information obtained by this rule; conditioning on an additional event about unqueried edges is a different operation.</p>

<a id="tag-IH8I" data-assertion="theorem" data-title="Unqueried edges retain their product law after a possibly infinite adaptive exploration"></a>
<p>A regular conditional law of $X$ given $\mathcal H_\infty$ is</p>
<div class="math-display">$$
\kappa_h=\bigotimes_{e\in E}\nu_e^h,\qquad
\nu_e^h=
\begin{cases}
\delta_{a_e(h)},&e\in R(h),\\
\operatorname{Bernoulli}(q_e),&e\notin R(h).
\end{cases}
$$</div>
<p>Thus, given the whole transcript, the unqueried coordinates are independent with their original parameters. This holds for infinite queried and unqueried sets, and permits $q_e=0$ or $1$. No integrability or finite stopping-time assumption is required.</p>

<p><em>Proof.</em> At a finite stage, induction on the number of queries gives the displayed product law with $R_n$ in place of $R_\infty$. The next coordinate is chosen from the information already available, so revealing its value fixes just that coordinate in the remaining product. The independent seed may be included in the initial information.</p>
<p>To pass to the terminal information, fix a finite $F\subseteq E$ and a pattern $b\in\{0,1\}^F$. Put</p>
<div class="math-display">$$
C_{F,b}=\{X|_F=b\},\qquad
p_{F,b}=\prod_{e\in F}q_e^{b_e}(1-q_e)^{1-b_e}.
$$</div>
<p>Here the factor means $q_e$ when $b_e=1$ and $1-q_e$ when $b_e=0$, including the endpoint parameters. If $g$ is bounded and $\mathcal H_n$-measurable, the finite-stage law gives, for every $m\ge n$,</p>
<div class="math-display">$$
\mathbb E\!\left[g\,\mathbf1_{\{F\cap R_m=\varnothing\}}
                         \mathbf1_{C_{F,b}}\right]
=p_{F,b}\,
 \mathbb E\!\left[g\,\mathbf1_{\{F\cap R_m=\varnothing\}}\right].
$$</div>
<p>Let $m\to\infty$ by bounded convergence. For a bounded $\mathcal H_\infty$-measurable $g$, replace it first by $\mathbb E[g\mid\mathcal H_n]$ and then let $n\to\infty$ in $L^1$. The same identity holds with $R_\infty$ and every such $g$.</p>
<p>For a cylinder on any finite $F$, partition according to $J=F\cap R_\infty$ and the observed answers on $J$. On each part, agreement with $b$ on $J$ is already known. Apply the preceding identity to $F\setminus J$, inserting the indicator of that part into $g$. It follows that</p>
<div class="math-display">$$
\mathbb P(C_{F,b}\mid\mathcal H_\infty)
=\prod_{e\in F\cap R_\infty}\mathbf1_{\{a_e=b_e\}}
 \prod_{e\in F\setminus R_\infty}q_e^{b_e}(1-q_e)^{1-b_e}
\quad\text{almost surely}.
$$</div>
<p>The functions $h\mapsto\mathbf1_{\{e\in R(h)\}}$ and the observed answers are Borel. Hence the displayed products define a Borel probability kernel on cylinders, and therefore on the countable product. Cylinder probabilities determine a probability measure; the monotone-class theorem identifies this kernel as the conditional law on every Borel event. $\square$</p>

## Reimer conditional on the entire transcript {#section-conditional-full-reimer}

<p>For a transcript $h$, put $U(h)=E\setminus R(h)$ and</p>
<div class="math-display">$$
\Omega_h=\{\omega:\omega_e=a_e(h)\text{ for }e\in R(h)\}.
$$</div>
<p>For fixed Borel events $A,B\subseteq\Omega$, let $D_h(A,B)$ be the configurations in $\Omega_h$ for which there are disjoint $K,L\subseteq U(h)$ satisfying</p>
<div class="math-display">$$
\{\eta\in\Omega_h:\eta|_K=\omega|_K\}\subseteq A,\qquad
\{\eta\in\Omega_h:\eta|_L=\omega|_L\}\subseteq B.
$$</div>
<p>The observed edges are background information shared by the two events. Their new certificates must be disjoint only among the unqueried edges. Forcing still tests every completion in $\Omega_h$, including completions of conditional probability zero.</p>

<a id="tag-RO0R" data-assertion="theorem" data-title="Full-certificate Reimer holds conditionally after a countable adaptive exploration"></a>
<p>Assume finite nonmonotone Reimer. For every transcript $h$,</p>
<div class="math-display">$$
\kappa_h^*(D_h(A,B))\le\kappa_h(A)\kappa_h(B).
$$</div>
<p>If each of $A,B$ is either order-convex Borel or $G_\delta$, the joint set
$\{(h,\omega):\omega\in D_h(A,B)\}$ is analytic. If one event is open and the other is Borel, that joint set is Borel. In either case, writing $H$ for the random terminal transcript, ordinary completed conditional probability is available and</p>
<div class="math-display">$$
\mathbb P\bigl(X\in D_H(A,B)\mid\mathcal H_\infty\bigr)
\le
\mathbb P(X\in A\mid\mathcal H_\infty)\,
\mathbb P(X\in B\mid\mathcal H_\infty)
\quad\text{almost surely}.
$$</div>
<p>When $q_e=1/2$ for every unqueried coordinate, let $\theta_h:\Omega_h\to\Omega_h$ fix the observed answers and flip all unqueried bits. The fair finite theorem gives the sharper bound
$\kappa_h^*(D_h(A,B))\le\kappa_h(A\cap\theta_h(B\cap\Omega_h))$, with the same ordinary conditional-probability interpretation in the measurable cases.</p>

<p><em>Proof.</em> For fixed $h$, the space $\Omega_h$ is naturally the countable cube $\{0,1\}^{U(h)}$, with its original product parameters by IH8I. The restrictions of $A,B$ are Borel. Apply <a href="/tag/BBOR/">BBOR</a> on this cube. Its bit flip is precisely $\theta_h$. This proves the outer bounds, including when $U(h)$ is finite or empty.</p>
<p>It remains to justify measurability jointly with the transcript; measurability separately for each $h$ would not suffice. Identify a candidate certificate with a point of $\{0,1\}^E$ and impose $K\subseteq U(h)$, a Borel condition. The least and greatest completions respecting $h$ and $K$ are Borel functions of $(h,\omega,K)$: they use the observed answer on $R(h)$, the value of $\omega$ on $K$, and respectively zero or one elsewhere. For an order-convex Borel input, testing these two completions tests the whole certificate, as in <a href="/tag/593F/">593F</a>.</p>
<p>For an open input $V$, a certificate together with the observed answers forces $V$ exactly when some finite $F\subseteq R(h)\cup K$ already forces it in the original cube. Indeed the full set of fixed coordinates is a certificate for $V$, so <a href="/tag/1NUW/">1NUW</a> applies. This is a countable union over finite $F$ and bit patterns whose cylinders lie in $V$, with Borel conditions on $(h,\omega,K)$. It is therefore Borel. For a fixed $G_\delta$ input, intersect these relations over a representation by open sets.</p>
<p>Intersect the resulting two Borel forcing relations with $K,L\subseteq U(h)$, $K\cap L=\varnothing$ and $\omega\in\Omega_h$, then project out $K,L$. The witness spaces are Polish, giving the asserted analytic joint set.</p>
<p>If $B$ is open and $A$ is arbitrary Borel, reduce the certificate for $B$ inside the residual cube to a finite $F\subseteq U(h)$. Enlarge the other certificate to $U(h)\setminus F$. It forces $A$ if and only if all finitely many replacements of $\omega$ on $F$ lie in $A$. The condition that $F$ forces $B$ relative to $h$ is Borel by the preceding open-input argument. A countable union over finite $F$ gives a Borel description of the joint event, just as in <a href="/tag/AWBF/">AWBF</a>. Symmetry covers an open first event.</p>
<p>Analytic sets are universally measurable. Apply disintegration to the joint law of $(H,X)$, using the kernel in IH8I and completed probabilities. Equivalently, choose a Borel version of the analytic joint event under this law; its sections agree with the original sections for almost every transcript under $\kappa_h$. The conditional probability is consequently $\kappa_H(D_H(A,B))$ almost surely. The pointwise outer bound gives the desired inequality. The same reasoning gives the fair bound. $\square$</p>

<p>After averaging, the bound is
$\mathbb P(X\in D_H(A,B))\le
\mathbb E[\mathbb P(A\mid\mathcal H_\infty)\mathbb P(B\mid\mathcal H_\infty)]$.
The right side is generally not $\mathbb P(A)\mathbb P(B)$. For example, reveal one edge $e$ and take $A=B=\{X_e=1\}$ with $0<q_e<1$. When it is open, both residual events have the empty certificate. Thus the explored disjoint-occurrence event has probability $q_e$, rather than at most $q_e^2$. This does not contradict Reimer: the definition now permits both events to use the same observed information.</p>
<p>The result applies to a countable percolation graph without a degree bound and to an exploration that never terminates. The rule must still reveal only the next edge chosen from its existing information. It does not allow an arbitrary random edge set selected by inspecting the whole configuration, nor does it settle full-witness measurability for two arbitrary Borel inputs. Finite nonmonotone Reimer remains a cited input; no source correction or new Lean verification is asserted.</p>


## The finite combinatorial input {#section-finite-reimer-counting}

<p>The preceding sections take finite Reimer as an input. We now supply its proof in prose, following the linear-algebra approach in <a href="https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/tr-98-42.pdf">Borgs–Chayes–Randall, Sections 3–5</a>. The earlier tagged statements are retained. Their finite premise can now be discharged within the written argument; their formal status is unchanged.</p>
<p>In this section $\Omega_n=\{0,1\}^n$, $\bar x=1-x$, and a bar over a set denotes its bitwise image. For $X\subseteq\Omega_n$, choose a set $S_x\subseteq[n]$ for each $x\in X$, and define</p>
<div class="math-display">$$
U=\bigcup_{x\in X}[x]_{S_x},\qquad
V=\bigcup_{x\in X}[x]_{S_x^c}.
$$</div>

<a id="tag-43BU" data-assertion="proposition" data-title="Reimer's complementary-cylinder counting inequality"></a>
<p>For every such choice, including $n=0$,</p>
<div class="math-display">$$|X|\le |U\cap\bar V|.$$</div>

<p><em>Proof.</em> In $(\mathbb R^2)^{\otimes n}$, with its usual inner product, put</p>
<div class="math-display">$$
v(x,S)=\bigotimes_{i=1}^n
\begin{cases}
(1,x_i),&i\in S,\\
(x_i,-1),&i\notin S.
\end{cases}
$$</div>
<p>First, for any assignment of $S_x$ to all $x\in\Omega_n$, these $2^n$ integer vectors are linearly independent. To see this, reduce them modulo two and use the basis $e=(1,0)$, $f=(1,1)$ of $\mathbb F_2^2$. Write $Z_x=\{i:x_i=0\}$ and let $b_J$ be the tensor with $e$ in the coordinates of $J$ and $f$ elsewhere, in the original coordinate order. Then</p>
<div class="math-display">$$
v(x,S_x)\bmod2
=\sum_{\substack{J\subseteq Z_x\\Z_x\cap S_x\subseteq J}} b_J
=b_{Z_x}+
  \sum_{\substack{J\subsetneq Z_x\\Z_x\cap S_x\subseteq J}}b_J.
$$</div>
<p>Indeed a coordinate with $x_i=1$ contributes $f$; a zero coordinate contributes $e$ if $i\in S_x$ and $e+f$ otherwise. Order the subsets by increasing cardinality, using the same order for rows and columns. Every proper subset precedes its superset, so this coefficient matrix is triangular with diagonal one. The original integer matrix therefore has odd determinant and is invertible over $\mathbb R$. The empty tensor is the scalar one, which also covers $n=0$.</p>
<p>Consider the following three indexed families of real vectors:</p>
<div class="math-display">$$
\bigl(v(y,\varnothing)\bigr)_{y\in\overline{U^c}},\qquad
\bigl(v(z,[n])\bigr)_{z\in U\cap\overline{V^c}},\qquad
\bigl(v(x,S_x)\bigr)_{x\in X}.
$$</div>
<p>Each family is independent by the preceding argument, extending the assignment outside its index set if necessary. The families are pairwise orthogonal. For the first and second, $\bar y\notin U$ and $z\in U$ imply $y_i=z_i$ for some $i$, giving the zero factor
$\langle(y_i,-1),(1,z_i)\rangle=y_i-z_i$.
For the first and third, $\bar y\notin[x]_{S_x}$ gives $y_i=x_i$ for some $i\in S_x$. For the second and third, $\bar z\notin[x]_{S_x^c}$ gives $z_i=x_i$ for some $i\notin S_x$. The corresponding inner-product factors again vanish. Tensor inner products are products of the coordinate inner products.</p>
<p>The three spans consequently form a direct sum inside a space of dimension $2^n$. Thus</p>
<div class="math-display">$$
|U^c|+|U\cap\overline{V^c}|+|X|\le2^n.
$$</div>
<p>Since $\overline{V^c}=(\bar V)^c$, the first two terms sum to $2^n-|U\cap\bar V|$. This proves the claim. $\square$</p>

## Finite Reimer for arbitrary product probabilities {#section-finite-reimer-proof}

<a id="tag-7GDN" data-assertion="theorem" data-title="The finite nonmonotone Reimer inequality and its fair bit-flip bound"></a>
<p>Let $\Omega=\prod_{i=1}^n\Omega_i$, where every $\Omega_i$ is a nonempty finite set, and let $\mu=\bigotimes_i\mu_i$ be any product probability. For arbitrary $A,B\subseteq\Omega$, with disjoint occurrence defined by full coordinate certificates,</p>
<div class="math-display">$$\mu(A\square B)\le\mu(A)\mu(B).$$</div>
<p>On the binary cube with uniform law, one also has
$|A\square B|\le|A\cap\bar B|$.</p>

<p><em>Proof.</em> First work on $\Omega_n$ and put $X=A\square B$. For each $x\in X$, enlarge one of its two disjoint certificates so that they partition $[n]$, and call them $S_x,S_x^c$. The sets $U,V$ in 43BU satisfy $U\subseteq A$ and $V\subseteq B$. Therefore
$|X|\le|U\cap\bar V|\le|A\cap\bar B|$.</p>
<p>To get the product bound, let $F$ range over all faces of the cube, including the whole cube and the singleton faces. Write $\iota_F$ for the involution which flips the free coordinates of $F$. For $x\in X\cap F$, restrict $S_x$ and $S_x^c$ to these free coordinates. They force $A\cap F$ and $B\cap F$ inside the face. Applying 43BU in that smaller cube gives</p>
<div class="math-display">$$
|X\cap F|\le |(A\cap F)\cap\iota_F(B\cap F)|.
$$</div>
<p>Each ordered pair $(a,b)\in A\times B$ determines exactly one face whose fixed coordinates are those where $a_i=b_i$ and whose fixed values are their common values. In that face $b=\iota_F(a)$. Also, each $x\in\Omega_n$ belongs to exactly $2^n$ faces, one for each choice of fixed coordinates. Summing the preceding inequality therefore gives</p>
<div class="math-display">$$
2^n|A\square B|
=\sum_F|X\cap F|
\le\sum_F|(A\cap F)\cap\iota_F(B\cap F)|
=|A|\,|B|.
$$</div>
<p>Now suppose the probabilities on the finite alphabets have a common dyadic denominator $2^m$. Partition $\{0,1\}^m$ into cells of sizes $2^m\mu_i(a)$ and let $f_i$ map each cell to its label $a\in\Omega_i$. The product map $f=(f_i)_i$ sends the uniform law on $nm$ bits to $\mu$. Moreover,</p>
<div class="math-display">$$
f^{-1}(A\square B)\subseteq f^{-1}(A)\square f^{-1}(B).
$$</div>
<p>For if disjoint original coordinate sets certify the two events, their disjoint unions of whole bit blocks certify the two preimages. The inclusion is all that is needed; equality is not assumed. The uniform binary result gives the desired inequality after taking preimages.</p>
<p>Finally approximate every $\mu_i$ by probabilities with a common dyadic denominator. Each event probability is a finite sum of products of atom probabilities, hence is continuous in those probabilities. Passing to the limit proves the result, including zero-probability atoms and degenerate coordinates. The certificate definition is unchanged during this approximation. $\square$</p>

## The countable proof with its finite premise discharged {#section-full-reimer-completed-proof}

<a id="tag-7ZTB" data-assertion="corollary" data-title="Full countable-edge Reimer follows without an unproved finite combinatorial premise in the written argument"></a>
<p>For countable $E$, arbitrary $q_e\in[0,1]$, and Borel events $A,B\subseteq\{0,1\}^E$,</p>
<div class="math-display">$$
\mu_q^*(A\square_\infty B)\le\mu_q(A)\mu_q(B).
$$</div>
<p>For $q_e=1/2$ the stronger bound is
$\mu_{1/2}^*(A\square_\infty B)\le\mu_{1/2}(A\cap\bar B)$.
For order-convex Borel or $G_\delta$ inputs, and for a Borel input with an open partner, these are ordinary completed-probability inequalities. The simultaneous-family conclusion of UFCR and the terminal-exploration conclusion of RO0R likewise hold with their stated measurability conditions.</p>
<p><em>Proof.</em> Theorem 7GDN supplies both finite inequalities used in <a href="/tag/LLAT/">LLAT</a> and <a href="/tag/BBOR/">BBOR</a>. Their exhaustion, compactness and outer-regularity arguments give the two displayed bounds. Measurability is supplied by <a href="/tag/593F/">593F</a> and <a href="/tag/AWBF/">AWBF</a>; apply <a href="/tag/UFCR/">UFCR</a> and <a href="/tag/RO0R/">RO0R</a> for the last assertions. $\square$</p>
<p>This completes the informal finite-to-countable argument, with arbitrary infinite certificates. It does not assert measurability for two completely arbitrary Borel inputs. The older passages that name finite Reimer as an external premise record the earlier stage of the argument; 7GDN now supplies that premise in prose. No Lean proof, formal status, correspondence review or source-author confirmation is inferred from this addition.</p>



## Exponential path bounds with a volume constraint {#section-weighted-path-moments-link}

<p>The <a href="/articles/intrinsic-geometry/#section-decreasing-path-moments">weighted path-moment theorem</a> marks a simple path repeatedly while retaining a decreasing Borel test on the first segment. Full closed-edge certificates and simultaneous Reimer give all moments and an exponential tail under two weighted two-point row bounds. A soft volume weight $e^{-hV_a}$ gives an explicit $1/(eh)$ factor. The <a href="/articles/intrinsic-geometry/#section-exponential-averaged-paths">averaged-path corollary</a> strengthens the earlier truncation error at scales above $\min\{\chi,|B|\}$. These deductions use the completed finite proof above; no new source correction or formal verification is asserted.</p>



## Independent edge marks on the full countable product {#section-real-edge-marks}

<p>A single independent uniform mark on each edge couples percolation at all parameters. To use Reimer in this coupling, a certificate must specify whole edge marks. The next result permits infinitely many such marks in each certificate.</p>

<a id="tag-FYBM" data-assertion="theorem" data-title="Full-certificate Reimer for independent real edge marks, with a uniform reflection bound"></a>
<p>Let $E$ be countable, let $\Omega=[0,1]^E$, and let $\mu=\bigotimes_{e\in E}\mu_e$ for arbitrary Borel probability measures $\mu_e$. For $\omega\in\Omega$ and $K\subseteq E$, put</p>
<div class="math-display">$$
[\omega]_K=\{\eta\in\Omega:\eta_e=\omega_e\text{ for every }e\in K\}.
$$</div>
<p>A certificate $K$ for $A$ means $[\omega]_K\subseteq A$, with every completion tested, including null configurations. For a nonempty finite or countable index set $I$, let $D_I(A_i)$ be the set of configurations admitting pairwise disjoint certificates $K_i$ for all $A_i$ simultaneously. If every $A_i$ is Borel, then</p>
<div class="math-display">$$
\mu^*\bigl(D_I(A_i)\bigr)\le\prod_{i\in I}\mu(A_i),
$$</div>
<p>where an infinite product is the infimum of its finite subproducts. For two inputs write $A\square_\infty B=D_{\{1,2\}}(A,B)$. If all $\mu_e$ are uniform, the sharper reflection bound holds:</p>
<div class="math-display">$$
\mu^*(A\square_\infty B)\le\mu(A\cap\bar B),
\qquad \bar B=\{1-\omega:\omega\in B\}.
$$</div>
<p>The reflection assertion uses uniform marginals; the product assertion has no such restriction.</p>

<p><em>Proof.</em> Give each edge its own countable block of fair bits. On $\Xi=\{0,1\}^{E\times\mathbb N_{\ge1}}$ with fair product law $\nu$, define</p>
<div class="math-display">$$
U_e(b)=\sum_{j\ge1}2^{-j}b_{e,j}.
$$</div>
<p>These variables are independent and uniform on $[0,1]$. A Borel inverse-distribution map $Q_e$ sends a uniform variable to $\mu_e$; its values at zero and one may be assigned arbitrarily. Thus the Borel map $\Phi(b)_e=Q_e(U_e(b))$ satisfies $\Phi_*\nu=\mu$. For uniform marginals take $\Phi_e=U_e$.</p>
<p>We will use the following outer-probability fact. If a Borel map $\Phi$ between standard Borel probability spaces sends $\nu$ to $\mu$, then for every subset $D$ of the target,</p>
<div class="math-display">$$
\mu^*(D)=\nu^*(\Phi^{-1}D).
$$</div>
<p>Pulling back Borel covers gives $\nu^*(\Phi^{-1}D)\le\mu^*(D)$. For the other direction, disintegrate $\nu$ over $\Phi$, writing $\kappa_y$ for a regular conditional law on the source. There is one Borel $\mu$-null set $N$ such that $\kappa_y(\Phi^{-1}\{y\})=1$ for every $y\notin N$. Indeed, apply the conditional identity $\kappa_y(\Phi^{-1}G)=\mathbf1_G(y)$ to a countable separating Borel generator of the target, discard the union of the exceptional null sets, and intersect the resulting probability-one sets.</p>
<p>If $H$ is Borel and contains $\Phi^{-1}D$, then $\kappa_y(H)=1$ for $y\in D\setminus N$. Consequently $C=\{y:\kappa_y(H)=1\}\cup N$ is a Borel cover of $D$ and</p>
<div class="math-display">$$
\mu(C)\le\int\kappa_y(H)\,\mu(dy)=\nu(H).
$$</div>
<p>Taking the infimum over $H$ proves the fact. This argument does not require $D$ to be measurable or $\Phi$ to be onto.</p>
<p>Now set $\widetilde A_i=\Phi^{-1}A_i$. A mark certificate $K_i$ lifts to the whole bit blocks $K_i\times\mathbb N_{\ge1}$: every bit configuration agreeing on those blocks maps to a mark configuration agreeing on $K_i$. Disjoint mark sets therefore give disjoint bit sets, and</p>
<div class="math-display">$$
\Phi^{-1}\bigl(D_I(A_i)\bigr)\subseteq D_I(\widetilde A_i).
$$</div>
<p>Only this inclusion is asserted; bit certificates may split an edge's block. Apply the full Bernoulli bound <a href="/tag/UFCR/">UFCR</a>, whose finite premise was discharged in <a href="/tag/7ZTB/">7ZTB</a>, and the outer-probability fact to obtain</p>
<div class="math-display">$$
\mu^*\bigl(D_I(A_i)\bigr)
\le\nu^*\bigl(D_I(\widetilde A_i)\bigr)
\le\prod_i\nu(\widetilde A_i)=\prod_i\mu(A_i).
$$</div>
<p>In the uniform case, $\Phi(1-b)=1-\Phi(b)$ pointwise, including the two binary endpoint expansions. Hence $\overline{\Phi^{-1}B}=\Phi^{-1}\bar B$. The fair bit-flip bound <a href="/tag/BBOR/">BBOR</a> gives the reflected inequality in the same way. $\square$</p>

<p>For example, common uniform marks give configurations $\omega_t(e)=\mathbf1_{\{U_e\le q_e(t)\}}$ at different parameters. Borel events involving any finite or countable collection of these configurations are Borel events of the marks. The theorem applies when their certificates use disjoint sets of edges, each fixing the entire mark. The configurations at different parameters are coupled, not independent; splitting the binary encoding of one edge between two certificates would not meet this hypothesis. No finite-cluster or finite-susceptibility assumption enters the argument.</p>

## Measurability for real-valued marks {#section-mark-measurability}

<a id="tag-WXC1" data-assertion="proposition" data-title="Measurable full mark certificates and the coanalytic open-partner boundary"></a>
<p>In $\Omega=[0,1]^E$ with its product topology, suppose each member of a finite or countable family is either $G_\delta$ or order-convex Borel. Then its simultaneous full disjoint occurrence is analytic. If $A$ is Borel and $U$ is open, $A\square_\infty U$ is coanalytic, but need not be Borel. Both conclusions give universal measurability, so the outer bounds of FYBM become inequalities for completed probabilities. Order-convexity uses the coordinatewise order and includes increasing events, decreasing events, and their intersections.</p>

<p><em>Proof.</em> First consider the forcing relation $R_U=\{(\omega,K):[\omega]_K\subseteq U\}$ for open $U$. If $K$ forces $U$, compactness gives a finite $F\subseteq K$ that already forces it: otherwise the closed sets $U^c$ and $\{\eta:\eta_e=\omega_e\}$, $e\in K$, would have the finite-intersection property and a common point.</p>
<p>For finite $F$, the set</p>
<div class="math-display">$$
V_F=\{a\in[0,1]^F:\text{every extension of }a\text{ belongs to }U\}
$$</div>
<p>is open, because its complement is the projection of the compact set $U^c$. Thus $R_U$ is the union, over finite $F\subseteq E$, of the open conditions $F\subseteq K$ and $\omega_F\in V_F$. For a $G_\delta$ input the forcing relation is a countable intersection of such relations, hence Borel.</p>
<p>For an order-convex Borel input, test the least and greatest completions, which agree with $\omega$ on $K$ and take respectively zero and one outside $K$. They both belong to the input exactly when the whole interval $[\omega]_K$ does. Both completion maps are continuous on $\Omega\times\{0,1\}^E$, so this forcing relation is also Borel. For the stated family, pairwise disjointness and all the forcing conditions define a Borel subset of $\Omega\times(\{0,1\}^E)^I$. Its projection is analytic.</p>
<p>For an open partner there is a more precise identity. Let $T_{F,b}\omega$ replace the coordinates in $F$ by $b\in[0,1]^F$, and put</p>
<div class="math-display">$$
A^{\langle F\rangle}=\{\omega:T_{F,b}\omega\in A\text{ for every }b\in[0,1]^F\},
\qquad U_F=\{\omega:[\omega]_F\subseteq U\}.
$$</div>
<p>Then</p>
<div class="math-display">$$
A\square_\infty U=\bigcup_{F\Subset E}\bigl(A^{\langle F\rangle}\cap U_F\bigr).
$$</div>
<p>Indeed, reduce a certificate for $U$ to a finite $F$. A disjoint certificate for $A$ is contained in $E\setminus F$, so every change on $F$ stays in $A$. Conversely, membership in the displayed summand supplies the certificates $E\setminus F$ and $F$.</p>
<p>The complement of $A^{\langle F\rangle}$ is the projection of the Borel set $\{(\omega,b):T_{F,b}\omega\notin A\}$, and is therefore analytic. Since $U_F$ is open, each summand is coanalytic, as is the countable union. Analytic and coanalytic subsets of a Polish space are measurable for the completion of every Borel probability.</p>
<p>The Borel conclusion from the Boolean case <a href="/tag/AWBF/">AWBF</a> cannot be retained. To see the obstruction already with two marks, take a Borel set $R\subseteq[0,1]^2$ whose projection $C$ onto the second coordinate is analytic and non-Borel. Such Borel sets exist by the standard projection representation of analytic sets. Put $A=[0,1]^2\setminus R$ and $U=(0,1)\times[0,1]$. Any certificate for $U$ includes the first coordinate. A disjoint certificate for $A$ must therefore be contained in the second coordinate, and testing all first-coordinate completions gives</p>
<div class="math-display">$$
A\square_\infty U=(0,1)\times([0,1]\setminus C).
$$</div>
<p>This is not Borel, since its section at first coordinate $1/2$ is not Borel. The difference is that even a finite set of real marks has uncountably many completions. $\square$</p>

<p>The proof uses standard Borel disintegration and the usual projection and universal-measurability theorems. It does not settle measurability for two arbitrary Borel full-certificate inputs. These are extensions of the written countable Reimer argument; they do not change any existing theorem, erratum classification or Lean verification status.</p>



## Partial observations of independent marks {#section-partial-mark-exploration}

<p>An exploration need not reveal an edge's whole mark. Testing whether it lies below a chosen threshold reveals only one bit of information, and the same edge may be tested again. Conditional independence survives such adaptive queries, including an infinite sequence of them.</p>

<a id="tag-VUSG" data-assertion="theorem" data-title="Independent marks retain a product conditional law after countably many adaptive single-coordinate observations"></a>
<p>Let $X=(X_e)_{e\in E}$ have any product Borel law on $[0,1]^E$, with $E$ countable. An independent seed takes values in a standard Borel space. At step $n$, the previous transcript chooses a coordinate $Q_n\in E$ and a Borel observation of $X_{Q_n}$, or halts. More precisely, the answer has the form $g_n(H_n,X_{Q_n})$ in a standard Borel space, where $g_n$ is Borel and $H_n$ records the seed and the first $n$ queries and answers. A queried coordinate may be chosen repeatedly. After halting, the transcript records a halt symbol forever.</p>
<p>Write $\mathcal H_n=\sigma(H_n)$ and $\mathcal H_\infty=\sigma(\bigcup_n\mathcal H_n)$, and let $H$ be the entire transcript. If $\kappa_{e,h}$ is a regular conditional law of $X_e$ given $H=h$, then</p>
<div class="math-display">$$
\kappa_h=\bigotimes_{e\in E}\kappa_{e,h}
$$</div>
<p>is a regular conditional law of $X$ given $\mathcal H_\infty$. In particular, the marks are conditionally independent after all queries, although their conditional marginal laws may have changed. On the event that $e$ is never queried, its conditional marginal is its original law. There is no assumption that the number of queries is finite.</p>

<p><em>Proof.</em> Conditional on a finite transcript, the marks have a product law. This follows by induction: the next coordinate and observation rule are already determined, and conditioning a product on an observation of one coordinate changes only that coordinate's marginal. The seed is independent at the initial stage. Regular conditional laws exist because all the spaces are standard Borel.</p>
<p>Fix a finite $F\subseteq E$ and nonnegative integers $k_e$, $e\in F$. The finite-stage factorisation gives</p>
<div class="math-display">$$
\mathbb E\!\left[\prod_{e\in F}X_e^{k_e}\,\middle|\,\mathcal H_n\right]
=\prod_{e\in F}\mathbb E[X_e^{k_e}\mid\mathcal H_n].
$$</div>
<p>Bounded martingale convergence sends each side to the same expression with $\mathcal H_\infty$ in place of $\mathcal H_n$. There are only countably many choices of $F$ and the integer powers, so these identities hold outside one null set of transcripts. Polynomials determine probability measures on every finite cube $[0,1]^F$, by uniform approximation of continuous functions. Thus the conditional law on each finite set of coordinates is the product of its conditional marginals. Finite-dimensional laws determine a measure on the countable product, proving the claim. The displayed product is a Borel kernel, since its cylinder probabilities are products of Borel functions of $h$.</p>
<p>If $e$ has not been queried by time $n$, the same finite-stage induction leaves its marginal unchanged. On the event that it is never queried, every conditional moment in the preceding convergence is consequently its original moment. Moment determination on $[0,1]$ gives the last assertion. $\square$</p>

## Threshold queries and the remaining intervals {#section-threshold-posterior}

<a id="tag-CKK8" data-assertion="corollary" data-title="Adaptive threshold observations leave independent uniform intervals, possibly collapsed to points"></a>
<p>Suppose the original marks $U_e$ are independent and uniform on $[0,1]$, and each query returns $\mathbf1_{\{U_{Q_n}\le t_n\}}$, where $t_n\in[0,1]$ is chosen from the preceding transcript. For a terminal transcript $h$, put</p>
<div class="math-display">$$
\ell_e(h)=\sup\bigl(\{0\}\cup\{t_n:Q_n=e,\ \text{answer }0\}\bigr),\qquad
r_e(h)=\inf\bigl(\{1\}\cup\{t_n:Q_n=e,\ \text{answer }1\}\bigr).
$$</div>
<p>Almost surely $\ell_e(H)\le U_e\le r_e(H)$ for all $e$. Given the entire transcript, the marks are independent, with conditional laws</p>
<div class="math-display">$$
\kappa_{e,h}=
\begin{cases}
\operatorname{Unif}[\ell_e(h),r_e(h)],&\ell_e(h)&lt;r_e(h),\\
\delta_{\ell_e(h)},&\ell_e(h)=r_e(h).
\end{cases}
$$</div>
<p>Thus countably many comparisons can determine a mark exactly, as in binary search. An unqueried edge keeps the interval $[0,1]$.</p>

<p><em>Proof.</em> At each finite stage, outside a null set of histories, the query cuts the chosen edge's current interval at the chosen threshold, retaining the side indicated by its answer. Its conditional law is uniform on the retained interval, and the other marginals stay unchanged. Almost surely all these finite-stage intervals have positive length: a zero-length retained side has zero conditional probability, and there are only countably many steps.</p>
<p>For a fixed edge, their lower endpoints increase to $\ell_e$ and their upper endpoints decrease to $r_e$. For every continuous $f:[0,1]\to\mathbb R$, its averages on these intervals converge to its average on $[\ell_e,r_e]$ when the limiting length is positive, and to $f(\ell_e)$ when the length is zero. Martingale convergence identifies these limits with the terminal conditional expectations. Apply this to a countable determining family, such as the monomials, and then use VUSG for conditional independence. The bounds on $U_e$ follow directly from all its recorded comparisons. $\square$</p>

<p>The conditional law of a positive-length interval is unaffected by including its endpoints. Certificate statements require a separate convention about these null boundary values. In the next result, every completion in the <em>closed</em> interval is tested, even if one of the recorded strict inequalities excluded an endpoint.</p>

## Reimer after adaptive threshold exploration {#section-threshold-conditional-reimer}

<p>For the interval endpoints above, define the closed posterior box and its nonconstant coordinates by</p>
<div class="math-display">$$
\Omega_h=\prod_{e\in E}[\ell_e(h),r_e(h)],\qquad
J(h)=\{e:\ell_e(h)&lt;r_e(h)\}.
$$</div>
<p>Fix Borel events $A_i\subseteq[0,1]^E$, indexed by a nonempty finite or countable set $I$. Let $D_h(A_i)$ consist of those $x\in\Omega_h$ for which there are pairwise disjoint $K_i\subseteq J(h)$ with</p>
<div class="math-display">$$
\{y\in\Omega_h:y|_{K_i}=x|_{K_i}\}\subseteq A_i
\quad\text{for every }i.
$$</div>
<p>The posterior intervals are common background information. A new certificate fixes whole marks on its own coordinates, and all boundary completions in the box remain part of the test. Coordinates whose intervals have collapsed are already fixed and need no new certificate.</p>

<a id="tag-GIFB" data-assertion="theorem" data-title="Conditional full-certificate Reimer in the closed posterior box of an infinite threshold exploration"></a>
<p>For every transcript with $\ell_e\le r_e$ for all $e$, let $\kappa_h$ be the product law specified in CKK8. Then</p>
<div class="math-display">$$
\kappa_h^*\bigl(D_h(A_i)\bigr)\le\prod_i\kappa_h(A_i).
$$</div>
<p>For two inputs $A,B$, reflection in the posterior intervals gives the sharper bound</p>
<div class="math-display">$$
\kappa_h^*\bigl(D_h(A,B)\bigr)
\le\kappa_h\{x\in\Omega_h:x\in A,\ \theta_hx\in B\},
\qquad (\theta_hx)_e=\ell_e+r_e-x_e.
$$</div>
<p>If each $A_i$ is either order-convex Borel or $G_\delta$, the joint set $\{(h,x):x\in D_h(A_i)\}$ is analytic. For a pair consisting of a Borel event and an open event it is coanalytic. In these cases completed conditional probability is available, and almost surely</p>
<div class="math-display">$$
\mathbb P\bigl(U\in D_H(A_i)\mid\mathcal H_\infty\bigr)
\le\prod_i\mathbb P(U\in A_i\mid\mathcal H_\infty).
$$</div>
<p>The reflected bound has the analogous conditional interpretation for a pair in these measurable classes.</p>

<p><em>Proof.</em> For fixed $h$, omit the constant coordinates and write each remaining mark as $x_e=\ell_e+(r_e-\ell_e)z_e$. This is a homeomorphism from $[0,1]^{J(h)}$ onto $\Omega_h$, and sends independent uniforms to $\kappa_h$. It preserves full coordinate certificates and their disjointness, including infinite certificates. Apply <a href="/tag/FYBM/">FYBM</a>. The uniform reflection $z\mapsto1-z$ becomes $\theta_h$. This also covers finite or empty $J(h)$.</p>
<p>We check joint measurability, since sectionwise measurability alone would not justify conditioning. The interval endpoints and the condition $K\subseteq J(h)$ are Borel in the transcript. For $x\in\Omega_h$, let $c(h,x,K,t)$ agree with $x$ on $K$ and take the value $\ell_e+(r_e-\ell_e)t_e$ elsewhere, for $t\in[0,1]^E$. This map is Borel in all its variables and continuous in $t$ for fixed $(h,x,K)$. Its image is exactly the closed set of completions under consideration.</p>
<p>For an open input $V$, that compact image is contained in $V$ exactly when its distance from the closed set $V^c$ is positive, using any compatible metric on the compact cube. The minimum distance equals the infimum over a fixed countable dense set of $t$'s, so this forcing condition is Borel in $(h,x,K)$. When $V$ is the whole cube the condition is automatic. A fixed $G_\delta$ input is treated by intersecting the forcing conditions for its open factors. For an order-convex Borel input, the two completions $c(h,x,K,0)$ and $c(h,x,K,1)$ test the entire interval, again giving a Borel condition. Add $x\in\Omega_h$, the certificate constraints and pairwise disjointness, then project out the finite or countable family of witnesses in $(\{0,1\}^E)^I$. This proves analyticity.</p>
<p>Now let $B=V$ be open and $A$ be Borel. Compactness of $\Omega_h$ reduces any certificate for $V$ to a finite $F\subseteq J(h)$. The other certificate may be enlarged to $J(h)\setminus F$. It forces $A$ exactly when every replacement of the coordinates in $F$ by values $\ell_e+(r_e-\ell_e)t_e$, $t\in[0,1]^F$, belongs to $A$. The exceptional replacements form a Borel set in $(h,x,t)$, so the universal replacement condition is coanalytic. The condition that $F$ forces $V$ is Borel by the distance argument. Taking the countable union over finite $F$, while imposing $F\subseteq J(h)$ and $x\in\Omega_h$, proves the coanalytic assertion.</p>
<p>Analytic and coanalytic sets are universally measurable. Under the joint law of $(H,U)$, choose a Borel version of the joint event and a Borel null cover of their difference. Disintegration shows that their sections agree for $\kappa_h$-almost every mark configuration for almost every $h$. CKK8 therefore identifies the conditional probability with $\kappa_H(D_H(A_i))$ almost surely. Apply the pointwise outer bound, or its reflected form. $\square$</p>

<p>After averaging, the right side is the expectation of the product of the conditional probabilities. It generally cannot be replaced by the product of the original probabilities. For example, query whether one uniform mark is at most $1/2$ and let $A=B$ be that event. On answer one, both events have the empty certificate in the posterior box $[0,1/2]$; on answer zero, neither can occur. Thus the explored disjoint-occurrence event has probability $1/2$, whereas $\mathbb P(A)\mathbb P(B)=1/4$.</p>
<p>The closed-box convention is part of the theorem. It tests more completions than the exact set of configurations satisfying every recorded strict inequality. No equivalence between those two certificate conventions is asserted, nor is general full-certificate measurability for two arbitrary Borel inputs. The exploration must observe one coordinate at a time, with its choices based only on the information already obtained; inspecting two marks in one answer can destroy the product conditional law. These are further written deductions, with independent mathematical review and Lean formalisation still pending.</p>



## The exact constraints left by threshold answers {#section-observed-mark-constraints}

<p>The closed posterior box in GIFB can include an endpoint ruled out by a strict comparison. We now use the exact set of marks consistent with every answer. The outer Reimer bound survives this change. Measurability needs its own argument because the new space need not be compact.</p>

<p>Keep the threshold protocol and endpoints $\ell_e(h),r_e(h)$ from CKK8. Let $b_e(h)=1$ if some answer zero at edge $e$ was obtained at the threshold $\ell_e(h)$, and let $b_e(h)=0$ otherwise. These are Borel functions of the transcript. The exact admissible interval is</p>
<div class="math-display">$$
I_e(h)=
\begin{cases}
(\ell_e(h),r_e(h)],&b_e(h)=1,\\
[\ell_e(h),r_e(h)],&b_e(h)=0.
\end{cases}
$$</div>
<p>Indeed an answer zero requires $U_e&gt;t_n$, so the supremum of those thresholds is excluded exactly when it was attained. Answers one give non-strict upper bounds, so their infimum is included. The endpoint defaults zero and one impose no extra strict comparison. For every realised transcript all intervals are nonempty: $U_e\in I_e(H)$ for every $e$. In particular, a collapsed interval has $b_e=0$.</p>
<p>Write $\Gamma_h=\prod_e I_e(h)$ and retain $J(h)=\{e:\ell_e&lt;r_e\}$. A certificate now tests every completion in $\Gamma_h$. For fixed Borel events $A_i\subseteq[0,1]^E$, let $D_h^{\mathrm{obs}}(A_i)$ consist of the $x\in\Gamma_h$ admitting pairwise disjoint $K_i\subseteq J(h)$ such that</p>
<div class="math-display">$$
\{y\in\Gamma_h:y|_{K_i}=x|_{K_i}\}\subseteq A_i
\quad\text{for all }i.
$$</div>
<p>The product law $\kappa_h$ from CKK8 gives $\Gamma_h$ probability one: the removed endpoints are null on each positive-length interval, and there are only countably many coordinates. This does not make the two certificate conventions equivalent; forcing is a pointwise condition.</p>

<a id="tag-28O4" data-assertion="theorem" data-title="Full-certificate Reimer on the exact admissible intervals of a threshold transcript"></a>
<p>For every transcript with nonempty admissible intervals, and every nonempty finite or countable Borel family $(A_i)_{i\in I}$,</p>
<div class="math-display">$$
\kappa_h^*\bigl(D_h^{\mathrm{obs}}(A_i)\bigr)\le\prod_i\kappa_h(A_i).
$$</div>
<p>For two inputs, define an involution on $\Gamma_h$ by</p>
<div class="math-display">$$
(\vartheta_hx)_e=
\begin{cases}
r_e,&b_e=1\text{ and }x_e=r_e,\\
\ell_e+r_e-x_e,&\text{otherwise}.
\end{cases}
$$</div>
<p>Thus an interior point is reflected in its interval, the endpoints of a closed interval are exchanged, and the lone included endpoint of a half-open interval is fixed. Collapsed intervals are fixed as well. Then</p>
<div class="math-display">$$
\kappa_h^*\bigl(D_h^{\mathrm{obs}}(A,B)\bigr)
\le\kappa_h\{x\in\Gamma_h:x\in A,\ \vartheta_hx\in B\}.
$$</div>

<p><em>Proof.</em> Fix $h$. Sample independent uniform variables $z_e$, $e\in J(h)$. For a closed interval use $\Phi_h(z)_e=\ell_e+(r_e-\ell_e)z_e$. For a half-open interval use the same formula on $0&lt;z_e&lt;1$, but send both $z_e=0$ and $z_e=1$ to $r_e$. On a collapsed interval set $\Phi_h(z)_e=\ell_e$.</p>
<p>This Borel map takes every input into $\Gamma_h$, sends the uniform product to $\kappa_h$, and satisfies the pointwise identity</p>
<div class="math-display">$$\Phi_h(1-z)=\vartheta_h\Phi_h(z).$$</div>
<p>The exceptional endpoint assignments are needed for this identity on all configurations. A certificate in $\Gamma_h$ lifts to the same coordinate set in the uniform cube, so</p>
<div class="math-display">$$
\Phi_h^{-1}\bigl(D_h^{\mathrm{obs}}(A_i)\bigr)
\subseteq D_I(\Phi_h^{-1}A_i).
$$</div>
<p>The outer-probability transport proved in <a href="/tag/FYBM/">FYBM</a> applies to the Borel target $\Gamma_h$, which is a standard Borel space even when it is not compact. Apply FYBM on the uniform source cube to the preimage events, then use the displayed identity for its reflection bound. Only the certificate inclusion is required; the sampling map need not be injective. $\square$</p>

## Measurable events under the exact constraints {#section-observed-mark-measurability}

<a id="tag-JISV" data-assertion="proposition" data-title="Measurable exact-constraint Reimer for closed and decreasing events, finite boundary sets, and finite-coordinate Borel families"></a>
<p>The joint set $\{(h,x):x\in D_h^{\mathrm{obs}}(A_i)\}$ has the following measurability properties. Each family may be finite or countable.</p>
<ul>
<li>If each $A_i$ is either closed in $[0,1]^E$ or decreasing Borel, the joint set is analytic.</li>
<li>On the Borel set of transcripts for which $B(h)=\{e:b_e(h)=1\}$ is finite, the joint set is analytic when each $A_i$ is either $G_\delta$ or order-convex Borel.</li>
<li>If each $A_i$ is Borel and depends on a fixed finite set of coordinates $F_i$, the joint set is coanalytic, with no finiteness assumption on $B(h)$.</li>
</ul>
<p>Consequently the bounds of 28O4 are ordinary completed conditional-probability bounds in these cases. The second case gives the bounds on the indicated set of transcripts; if $B(H)$ is finite almost surely, they hold almost surely without restriction.</p>

<p><em>Proof.</em> Fix $x\in\Gamma_h$ and a candidate $K\subseteq J(h)$. The completions in $\Gamma_h$ agreeing with $x$ on $K$ are dense in the completions in the closed posterior box agreeing on $K$. Hence a closed input contains all exact completions if and only if it contains all closed-box completions. This is a Borel condition: test the closed input on the images of a fixed countable dense set of parameters under the closed-box completion map from GIFB. For a decreasing Borel input, it suffices to test the greatest completion, which keeps $x$ on $K$ and uses $r_e$ elsewhere. Every upper endpoint is admissible. This completion is Borel in $(h,x,K)$.</p>
<p>For the second case, the set of transcripts with finite $B(h)$ is Borel, since it is the union over finite $F\subseteq E$ of the conditions $b_e(h)=0$ for all $e\notin F$. On this set, exhaust the exact completions by compact boxes: for $m\ge1$, keep $x$ on $K$, and at a free coordinate use</p>
<div class="math-display">$$
\begin{cases}
[\ell_e+(r_e-\ell_e)/(m+1),r_e],&b_e=1,\\
[\ell_e,r_e],&b_e=0.
\end{cases}
$$</div>
<p>These boxes increase and cover all exact completions. The covering assertion uses finiteness of $B(h)\setminus K$: any admissible completion has a positive minimum of the finitely many relative distances from the excluded lower endpoints.</p>
<p>For an open input, each compact box is contained in it exactly when the minimum distance from its complement is positive. Parametrize the box by $[0,1]^E$ and compute that minimum as an infimum over a fixed countable dense parameter set. This makes the condition Borel jointly with $(h,x,K)$, as in GIFB. Intersect over $m$, and over the open factors of a fixed $G_\delta$ representation when needed. For an order-convex Borel input, test the least and greatest points of each compact box instead. The resulting forcing conditions are again Borel.</p>
<p>In either of the first two cases, combine these relations with $x\in\Gamma_h$, $K_i\subseteq J(h)$ and pairwise disjointness, then project out the witnesses in $(\{0,1\}^E)^I$. This proves the analytic assertions.</p>
<p>For the third case, a certificate for $A_i$ may be intersected with $F_i$: all other coordinates are irrelevant to its membership test. For a fixed choice $K_i\subseteq F_i$, failure to force $A_i$ is the existence of a point in the finite product $\prod_{e\in F_i}I_e(h)$ that agrees with $x$ on $K_i$ and lies outside the finite-coordinate event. These conditions are Borel in the transcript, $x$ and the finite-dimensional completion. Their projection is analytic, so the forcing relation is coanalytic. For finitely many inputs there are only finitely many choices of the $K_i$; impose $K_i\subseteq J(h)$ and disjointness, then take the finite union. This proves coanalyticity for every finite subfamily.</p>
<p>Enumerate a countable family. Its simultaneous occurrence is exactly the intersection of the occurrences of its finite initial subfamilies. Only the reverse inclusion needs proof. For fixed $(h,x)$, each witness $K_i$ ranges over the finite set $2^{F_i}$. In the compact product $\prod_i2^{F_i}$, requiring a witness to force its event, to lie in $J(h)$, and to be disjoint from another witness gives closed conditions. Any finitely many of them are satisfied by the witnesses for a sufficiently large initial subfamily. Compactness supplies compatible witnesses for the whole family. Countable intersections of coanalytic sets are coanalytic, proving the claim. This compatibility argument uses the finite coordinate sets; it is not an assertion of associativity for general disjoint occurrence.</p>
<p>Finally, analytic and coanalytic sets are universally measurable. The completed disintegration argument from GIFB applies to these joint events, restricting to the finite-$B(h)$ transcript set in the second case. The pointwise outer inequalities in 28O4 then give the asserted conditional bounds. $\square$</p>

<p>The restriction in the second case is needed by the compact-exhaustion argument: a countable collection of positive distances from excluded endpoints need not have a positive minimum. Even an increasing open event can lose the finite-subcertificate property. For example, in the ambient cube $[0,1]\times[0,1]^{\mathbb N_{\ge1}}$, put</p>
<div class="math-display">$$
\Gamma=(0,1]\times[0,1]^{\mathbb N_{\ge1}},\qquad
C=\{(y,z):y+z_n\le1+1/n\text{ for every }n\ge1\},\qquad V=C^c.
$$</div>
<p>The set $C$ is closed and decreasing, so $V$ is open and increasing. At $(y,\mathbf1)$ with $y&gt;0$, fixing all coordinates $z_n$ to one forces $V$ inside $\Gamma$: otherwise $y\le1/n$ for every $n$. For a finite subset $F$ of that certificate, set $z_n=1$ on $F$ and zero elsewhere, and choose $0&lt;y\le\min(\{1\}\cup\{1/n:n\in F\})$. This is an admissible completion in $C$ agreeing with the fixed values on $F$. Thus no finite subset of the original certificate forces $V$, and the earlier Borel/open-partner reduction cannot be transferred merely by replacing the closed box by $\Gamma$.</p>
<p>These results remove the closed-box enlargement from the outer Reimer bound and from the listed measurable cases. They leave unrestricted arbitrary-Borel full-certificate measurability unresolved, including any further exact-constraint open-partner result. No earlier statement or source erratum is changed; independent mathematical review and Lean formalisation remain pending.</p>



## Thresholded percolation after an exploration {#section-threshold-percolation-reimer}

<p>Percolation events depend on whether a mark crosses a threshold, rather than on its exact value. Passing to these binary coordinates recovers a compact certificate space, even when the admissible mark intervals are half-open. In particular, the Borel/open-partner result is available for events defined by a thresholded configuration.</p>

<p>Keep the exact intervals $I_e(h)$, their product $\Gamma_h$, and the conditional product law $\kappa_h$ from 28O4. Choose thresholds $p_e(h)\in[0,1]$ as Borel functions of the terminal transcript, and put</p>
<div class="math-display">$$
(\pi_hx)_e=\mathbf1_{\{x_e\le p_e(h)\}},\qquad W=\pi_HU.
$$</div>
<p>Thus thresholds may be chosen from the information obtained by the exploration. The conditional open probabilities are</p>
<div class="math-display">$$
q_e(h)=
\begin{cases}
\min\{1,\max\{0,(p_e-\ell_e)/(r_e-\ell_e)\}\},&\ell_e&lt;r_e,\\
\mathbf1_{\{\ell_e\le p_e\}},&\ell_e=r_e.
\end{cases}
\qquad \nu_h=\bigotimes_e\operatorname{Bernoulli}(q_e(h)).
$$</div>
<p>By CKK8, $\nu_H$ is a conditional law of $W$ given the whole transcript. Separate the edges whose binary value is forced by every admissible completion from those whose value can still vary:</p>
<div class="math-display">$$
O_h=\{e:p_e\ge r_e\},\qquad
Z_h=\{e:p_e&lt;\ell_e\text{ or }(p_e=\ell_e\text{ and }b_e=1)\},\qquad
R_h=E\setminus(O_h\cup Z_h).
$$</div>
<p>The possible binary configurations form the compact space</p>
<div class="math-display">$$
\mathcal X_h=\{w\in\{0,1\}^E:w|_{O_h}=1,\ w|_{Z_h}=0\}.
$$</div>
<p>For Borel events $A_i$ in the binary cube, define $D_h^{\mathrm{bit}}(A_i)$ using simultaneous disjoint certificates contained in $R_h$, testing every completion in $\mathcal X_h$. Write $B_i(h)=\{x\in\Gamma_h:\pi_hx\in A_i\}$ for the corresponding mark events.</p>

<a id="tag-AEFA" data-assertion="theorem" data-title="Exact threshold certificates give conditional Reimer with binary measurability classes"></a>
<p>For every admissible transcript and every nonempty finite or countable Borel family,</p>
<div class="math-display">$$
D_h^{\mathrm{obs}}(B_i(h))
=\pi_h^{-1}\bigl(D_h^{\mathrm{bit}}(A_i)\bigr),\qquad
\kappa_h^*\bigl(D_h^{\mathrm{obs}}(B_i(h))\bigr)
=\nu_h^*\bigl(D_h^{\mathrm{bit}}(A_i)\bigr)
\le\prod_i\nu_h(A_i).
$$</div>
<p>The joint event with the transcript is analytic if each fixed $A_i$ is either order-convex Borel or $G_\delta$ in the binary cube. For a fixed Borel event paired with a fixed open event, it is Borel. In these cases,</p>
<div class="math-display">$$
\mathbb P\bigl(U\in D_H^{\mathrm{obs}}(B_i(H))\mid\mathcal H_\infty\bigr)
\le\prod_i\nu_H(A_i)
\quad\text{almost surely}.
$$</div>
<p>The analytic conclusion and conditional bound also hold for history-dependent inputs $A_i(h)$ when $\{(h,w):w\in A_i(h)\}$ is Borel and every section $A_i(h)$ is order-convex. In this case replace $A_i$ on the right by $A_i(H)$.</p>

<p><em>Proof.</em> The formulas for $O_h,Z_h$ follow from the endpoints and their inclusion conventions. On an edge of $R_h$, both binary values occur on admissible marks. An open representative is $(\ell_e+p_e)/2$ and a closed representative is $(p_e+r_e)/2$. The first equals the lower endpoint only when $p_e=\ell_e$, in which case membership in $R_h$ ensures that endpoint is included. On edges outside $R_h$, the midpoint of the interval is an admissible representative of its forced value. These choices are Borel in $h$ and give a coordinatewise section of $\pi_h:\Gamma_h\to\mathcal X_h$.</p>
<p>Suppose $K\subseteq J(h)$ is a mark certificate for $B_i(h)$ at $x$. Put $L=K\cap R_h$ and $w=\pi_hx$. Given any $w'\in\mathcal X_h$ agreeing with $w$ on $L$, lift it using the preceding representatives outside $K$, and retain $x$ on $K$. The lift belongs to $\Gamma_h$, agrees with $x$ on $K$, and maps to $w'$. Thus $w'\in A_i$, proving that $L$ is a binary certificate. Conversely, a binary certificate $L\subseteq R_h$ lifts to a mark certificate on the same edge set. Both operations preserve pairwise disjointness, proving the set identity.</p>
<p>The map $\pi_h$ sends $\kappa_h$ to $\nu_h$. Apply the outer-probability transport from FYBM to obtain the equality of outer probabilities. On $\mathcal X_h$, omit the forced coordinates and apply <a href="/tag/7ZTB/">7ZTB</a> and <a href="/tag/UFCR/">UFCR</a> to the countable Bernoulli product on $R_h$. This proves the outer bound.</p>
<p>For measurability, the sets $O_h,Z_h,R_h$ are Borel in $h$. A candidate binary certificate $L\subseteq R_h$ has Borel least and greatest completions: keep the specified values on $L$, fix the forced coordinates, and use respectively zero or one on $R_h\setminus L$. Testing these two completions gives a Borel forcing relation for an order-convex input. This also works for jointly Borel history-dependent inputs with order-convex sections.</p>
<p>For a fixed open input, a certificate together with the forced coordinates forces the event exactly when some finite subset of those fixed coordinates already does. This follows from compactness of the full binary cube. Enumerating finite sets and their bit patterns gives a Borel forcing relation jointly with the transcript. Intersect over an open representation for a fixed $G_\delta$ input. The simultaneous disjoint-certificate conditions are then Borel; projecting out the witness sets gives the analytic assertion.</p>
<p>For a Borel input $A$ and an open input $V$, compactness of $\mathcal X_h$ reduces the certificate for $V$ to a finite $F\subseteq R_h$. The other certificate can be enlarged to $R_h\setminus F$. It forces $A$ exactly when every binary replacement on $F$ stays in $A$. There are only finitely many such replacements. Together with the Borel condition that $F$ forces $V$, a countable union over finite $F$ proves that the joint binary event is Borel, as in RO0R. The joint map $(h,x)\mapsto(h,\pi_hx)$ is Borel, so the same measurability conclusions hold for the mark event. Apply completed disintegration with the conditional law from CKK8 to obtain the displayed conditional bound. $\square$</p>

<p>A coordinate in $R_h$ can have $q_e(h)=0$. For example, if $I_e=[\ell_e,r_e]$ has positive length and $p_e=\ell_e$, the edge can be open at the null boundary value $\ell_e$. It must remain in the certificate space. For the pair $A=B=\{w_e=0\}$, each certificate must fix that edge, so their disjoint occurrence is empty. Deleting the coordinate merely because its conditional open probability is zero would instead give two empty certificates. This illustrates why $R_h$ is defined by possible completions, not by the condition $0&lt;q_e(h)&lt;1$.</p>
<p>The theorem restores the Borel/open-partner conclusion for thresholded binary events. It does not assert that conclusion for arbitrary Borel events of the real marks on a noncompact admissible space.</p>

## Disjoint connections after observing edges {#section-explored-disjoint-connections}

<a id="tag-8LB5" data-assertion="theorem" data-title="Conditional disjoint-path bounds on a countable graph with forced-open edges as shared background"></a>
<p>Let $G=(V,E)$ be a countable graph, with independent uniform edge marks explored by the threshold protocol above. Choose the percolation thresholds $p_e(H)$ and endpoints $u_i(H),v_i(H)\in V$ as Borel functions of the terminal transcript. For a nonempty finite or countable index set $I$, let $\mathcal P_I$ be the event that there are finite open paths $\gamma_i:u_i(H)\leftrightarrow v_i(H)$ whose sets of edges in $R_H$ are pairwise disjoint. Paths may share edges of $O_H$, which are open for every admissible completion. Put $\tau_h(u,v)=\nu_h(u\leftrightarrow v)$. Then</p>
<div class="math-display">$$
\mathbb P(\mathcal P_I\mid\mathcal H_\infty)
\le\prod_{i\in I}\tau_H(u_i(H),v_i(H))
\quad\text{almost surely}.
$$</div>
<p>The path event is Borel for finite $I$ and analytic for countable $I$, so its probability is understood in the completion in the latter case. No degree bound, finite susceptibility or finite exploration time is assumed.</p>

<p><em>Proof.</em> Conditional on the transcript, the open-edge law is $\nu_h$. The event $A_i(h)=\{u_i(h)\leftrightarrow v_i(h)\}$ is increasing, hence order-convex, in the binary configuration. It is Borel jointly with $h$: enumerate the finite paths in the countable graph and test their endpoints and edge states.</p>
<p>A path supplies a certificate consisting of its edges in $R_h$; its other open edges belong to $O_h$ and are common background information. Conversely, given a certificate $L_i\subseteq R_h$ for a connection, close every edge of $R_h\setminus L_i$ while retaining the forced open edges and the specified values on $L_i$. This is an allowed binary completion, even when some coordinate values have probability zero. Since the certificate forces a connection, this completion contains a finite open path. Every edge of that path in $R_h$ lies in $L_i$. Thus simultaneous full-certificate occurrence is exactly $\mathcal P_I$.</p>
<p>Apply the history-dependent order-convex case of AEFA. For finite $I$, countably many tuples of finite paths give an explicit Borel union. For countable $I$, witnesses lie in a countable product of countable discrete path spaces; the endpoint, openness and pairwise-disjointness conditions are Borel, so their projection is analytic. No limit of separately chosen witnesses for finite subfamilies is assumed. $\square$</p>

<p>Equivalently, contract each connected component of the forced-open subgraph $O_h$, retaining the labels of all remaining edges, including parallel edges. The event asks for open paths on this quotient with pairwise disjoint edge sets. Projecting an original path and erasing loops gives a quotient path; a quotient path lifts using finite paths inside the forced-open components. The original paths can share those forced-open edges, so the asserted disjointness is precisely on $R_h$.</p>
<p>After averaging, the bound is $\mathbb P(\mathcal P_I)\le\mathbb E[\prod_i\tau_H(u_i(H),v_i(H))]$. The conditional factors cannot generally be replaced by unconditional connection probabilities. These are deductions from the written countable Reimer argument, with independent mathematical review and Lean formalisation still pending; no source error is alleged.</p>



## Restoring the exterior of an infinite cluster {#section-cluster-restoration}

<p>The terminal exploration law also supplies the restoration argument left open in the <a href="/articles/harris-inequality/#section-cluster-interface">cluster-correlation discussion</a>. The cluster need not be finite. What matters is that an exploration can reveal every edge touching it without looking at any edge of its exterior.</p>

<p>Let $G=(V,E)$ be a countable graph, let $\mu_q$ be independent bond percolation with arbitrary probabilities $q_e\in[0,1]$, and fix $x\in V$. Write $K_x(\omega)$ for its open cluster. For two configurations define</p>
<div class="math-display">$$
\mathcal R_x(\omega,\eta)_e=
\begin{cases}
\omega_e,&e\cap K_x(\omega)\ne\varnothing,\\
\eta_e,&e\cap K_x(\omega)=\varnothing.
\end{cases}
$$</div>
<p>Thus the first configuration supplies every edge touching its root cluster, including its closed boundary, and the second supplies all edges with both endpoints outside. Connectivity means existence of a finite path. No degree bound or susceptibility assumption is imposed.</p>

<a id="tag-NNNN" data-assertion="theorem" data-title="Cluster restoration preserves product measure and gives the exterior law without a finite-cluster assumption"></a>
<p>The map $\mathcal R_x$ is Borel and, for every pair of configurations,</p>
<div class="math-display">$$K_x(\mathcal R_x(\omega,\eta))=K_x(\omega).$$</div>
<p>If $\omega,\eta$ are independent with law $\mu_q$, then $\mathcal R_x(\omega,\eta)$ has law $\mu_q$. More precisely, there is a Borel cluster-exploration transcript $H=H(\omega)$ such that, conditional on $H$, the configurations $\omega$ and $\mathcal R_x(\omega,\eta)$ are independent and have the same conditional law. In particular their joint law is exchangeable. For bounded Borel functions $f,g$ on configurations,</p>
<div class="math-display">$$
\mathbb E[f(\omega)g(\mathcal R_x(\omega,\eta))]
=\mathbb E\!\left[\mathbb E(f(\omega)\mid H)\,\mathbb E(g(\omega)\mid H)\right].
$$</div>
<p>The exterior product law remains true when conditioning only on the cluster vertex set. To state it on a fixed coordinate space, put $C=K_x(\omega)$ and let $T_c\zeta$ agree with $\zeta$ on edges with both endpoints outside $c$, and be zero on all other edges. For every bounded Borel function $\varphi$ on $\{0,1\}^V\times\{0,1\}^E$,</p>
<div class="math-display">$$
\mathbb E[\varphi(C,T_C\omega)\mid C]
=\int\varphi(C,T_C\zeta)\,d\mu_q(\zeta)
\quad\text{almost surely}.
$$</div>

<p><em>Proof.</em> Fix an injection $\iota:E\to\mathbb N$. Starting with $D_0=\{x\}$, query the unqueried edge of least priority incident to the discovered set. An open answer adds its endpoints to that set. Halt only when no such edge remains, and then record a halt symbol forever. This is the <a href="/tag/28UY/">priority exploration</a> without a size cutoff. Each choice is Borel and depends only on the finite history.</p>
<p>Every discovered vertex lies in $K_x$. Once an edge becomes eligible, it remains eligible until queried, and only finitely many edges have smaller priority. Hence it is queried at a finite later time. Induction along any finite open path from $x$ now shows that every vertex of $K_x$ is discovered. The final discovered set is therefore $K_x$, and the set $Q$ of queried edges is exactly</p>
<div class="math-display">$$Q=\{e:e\cap K_x\ne\varnothing\}.$$</div>
<p>This holds on every configuration, even if the exploration never halts. For example, on an infinite star with all edges closed it queries forever although the cluster consists only of its root. Completing the exploration means taking its whole transcript, not assuming a finite stopping time.</p>
<p>The transcript $H$ determines $C$, $Q$ and every answer on $Q$. By <a href="/tag/IH8I/">IH8I</a>, the conditional law $\kappa_H$ of $\omega$ freezes those answers and leaves independent Bernoulli coordinates of parameters $q_e$ on $E\setminus Q$. The independent configuration $\eta$ supplies another such family there. Conditional on $H$, it is independent of $\omega$, while the values used by $\mathcal R_x$ on $Q$ are already fixed. Thus the conditional joint law is $\kappa_H\otimes\kappa_H$. Integrating proves both preservation of $\mu_q$ and the displayed identity, and symmetry of this product proves exchangeability.</p>
<p>The cluster is preserved pointwise: every vertex of $C$ has an internal finite open path from $x$, all of whose edges are retained, and every edge leaving $C$ was closed and is retained closed. No path can reach its complement. Also, $\{v\in K_x\}$ is a countable union of finite-path events. Hence $K_x$, the coordinate choices in $\mathcal R_x$, and the masking map $(c,\zeta)\mapsto T_c\zeta$ are Borel.</p>
<p>Finally, the conditional law given $H$ yields</p>
<div class="math-display">$$
\mathbb E[\varphi(C,T_C\omega)\mid H]
=\int\varphi(C,T_C\zeta)\,d\mu_q(\zeta).
$$</div>
<p>The right side is a Borel function of $C$ alone. Take conditional expectation given $C$ to obtain the exterior-law identity. No positive-probability cluster atoms are required. The identity holds almost surely in the cluster variable; it does not prescribe a conditional law at every exceptional null value. $\square$</p>

## The two-cluster comparison without finiteness {#section-unrestricted-cluster-gap}

<a id="tag-UXBN" data-assertion="theorem" data-title="Distinct-cluster product and covariance bounds without finite clusters or finite susceptibility"></a>
<p>In the preceding countable product model, fix $x,y\in V$. Let $F,G:2^V\to[0,\infty]$ have Borel cluster evaluations $F(K_x)$ and $G(K_y)$, and suppose $G$ is increasing under inclusion. Then</p>
<div class="math-display">$$
\mathbb E[F(K_x)G(K_y)\mathbf1_{\{x\not\leftrightarrow y\}}]
\le \mathbb E[F(K_x)\mathbf1_{\{x\not\leftrightarrow y\}}]\,\mathbb E G(K_y)
\le \mathbb E F(K_x)\,\mathbb E G(K_y).
$$</div>
<p>The first functional need not be increasing. All expectations may be infinite, with the convention $0\cdot\infty=0$. If $F$ is also increasing, then</p>
<div class="math-display">$$
\mathbb E F(K_x)\,\mathbb E G(K_y)
\le\mathbb E[F(K_x)G(K_y)]
\le\mathbb E F(K_x)\,\mathbb E G(K_y)
+\mathbb E[F(K_x)G(K_y)\mathbf1_{\{x\leftrightarrow y\}}].
$$</div>
<p>When the product expectation and the two marginal expectations are finite, this gives the covariance form</p>
<div class="math-display">$$
0\le\operatorname{Cov}(F(K_x),G(K_y))
\le\mathbb E[F(K_x)G(K_y)\mathbf1_{\{x\leftrightarrow y\}}].
$$</div>

<p><em>Proof.</em> Take independent $\omega,\eta$ with law $\mu_q$, put $C=K_x(\omega)$, and set $\xi=\mathcal R_x(\omega,\eta)$. By NNNN, $\xi$ has law $\mu_q$ and $K_x(\xi)=C$. On $y\notin C$, every open path from $y$ in $\xi$ stays outside $C$, where all edge states come from $\eta$. Consequently</p>
<div class="math-display">$$K_y(\xi)\subseteq K_y(\eta)\qquad\text{on }\{y\notin C\}.$$</div>
<p>Monotonicity of $G$ and preservation of the law therefore give</p>
<div class="math-display">$$
\begin{aligned}
\mathbb E[F(K_x)G(K_y)\mathbf1_{\{x\not\leftrightarrow y\}}]
&=\mathbb E[F(C)G(K_y(\xi))\mathbf1_{\{y\notin C\}}]\\
&\le\mathbb E[F(C)\mathbf1_{\{y\notin C\}}\,G(K_y(\eta))]\\
&=\mathbb E[F(K_x)\mathbf1_{\{x\not\leftrightarrow y\}}]\,\mathbb E G(K_y).
\end{aligned}
$$</div>
<p>The last equality is independence of $\omega$ and $\eta$, justified for nonnegative variables by Tonelli or bounded truncation and monotone convergence. The second bound follows by discarding the indicator. Only the original cluster evaluations need be Borel: the evaluation at $\xi$ is their composition with the Borel restoration map, so no joint measurability assumption on an arbitrary family of induced subgraphs is being added.</p>
<p>If $F$ is increasing, both cluster evaluations are increasing observables of the edge configuration. <a href="/tag/E9HR/">Extended Harris association</a> gives the lower product bound. Split their product expectation over the connected and disconnected events, and apply the first bound on the latter to obtain the upper bound. This uses addition of nonnegative integrals; the finite covariance assertion then follows by subtraction. $\square$</p>

<p>This removes the almost-sure finite-cluster hypothesis from the earlier written result <a href="/tag/1AC7/">1AC7</a> and establishes the law of its restoration map. It applies at criticality with infinite susceptibility and in the presence of infinite clusters. The existing statement, source inventory and formal-status records are preserved. The new proofs still require independent mathematical review and Lean formalisation; they do not assert a new error in a source.</p>



## Several distinct clusters {#section-several-distinct-clusters}

<p>The full-certificate inequality gives a direct extension of the two-cluster comparison. Distinct clusters have disjoint sets of internal open edges, even when the clusters are infinite. One event may also use all edges touching its cluster, including its closed boundary.</p>

<a id="tag-39JJ" data-assertion="theorem" data-title="Product bounds for functionals of several distinct clusters, with one nonmonotone factor allowed"></a>
<p>Consider independent bond percolation on a countable graph. Fix roots $x_1,\ldots,x_k$, where $k\ge1$, and functions $F_i:2^V\to[0,\infty]$ whose cluster evaluations are Borel. Assume $F_2,\ldots,F_k$ are increasing under inclusion; no monotonicity is required of $F_1$. Let $\mathcal D_k$ be the event that the clusters of the roots are pairwise distinct. Then</p>
<div class="math-display">$$
\mathbb E\!\left[\mathbf1_{\mathcal D_k}\prod_{i=1}^k F_i(K_{x_i})\right]
\le\prod_{i=1}^k\mathbb E F_i(K_{x_i}).
$$</div>
<p>Extended nonnegative expectations are allowed, with $0\cdot\infty=0$. No finite-cluster or finite-susceptibility assumption is needed. For a countable sequence of roots and functions satisfying the same measurability and monotonicity conditions, with every $F_i$ taking values in $[0,1]$, one also has</p>
<div class="math-display">$$
\mathbb E\!\left[\mathbf1_{\mathcal D_\infty}\prod_{i\ge1}F_i(K_{x_i})\right]
\le\prod_{i\ge1}\mathbb E F_i(K_{x_i}),
$$</div>
<p>where both products are limits of their finite initial products, and $\mathcal D_\infty$ requires all root clusters to be distinct.</p>

<p><em>Proof.</em> Fix positive levels $t_i$ and put $A_i=\{F_i(K_{x_i})&gt;t_i\}$. On $\mathcal D_k\cap\bigcap_i A_i$, write $C_i=K_{x_i}$. For the first event, use every edge touching $C_1$ as a certificate, retaining its actual state. Every internal finite connection from $x_1$ is then retained, and every boundary edge stays closed. Thus any agreeing completion has root cluster exactly $C_1$ and still belongs to $A_1$.</p>
<p>For $i\ge2$, use just the open edges with both endpoints in $C_i$. Any agreeing completion retains a finite open path from $x_i$ to each vertex of $C_i$, so its root cluster contains $C_i$. Monotonicity of $F_i$ makes this a certificate for $A_i$. The clusters $C_i$ are disjoint; hence these certificates are pairwise disjoint, including the larger first certificate. They need not be finite.</p>
<p>Consequently the measurable event $\mathcal D_k\cap\bigcap_i A_i$ is contained in the simultaneous full disjoint occurrence of the Borel events $A_i$. Apply the outer-probability bound <a href="/tag/UFCR/">UFCR</a>, whose finite premise is supplied by <a href="/tag/7ZTB/">7ZTB</a>, to obtain</p>
<div class="math-display">$$
\mathbb P\!\left(\mathcal D_k\cap\bigcap_i\{F_i(K_{x_i})&gt;t_i\}\right)
\le\prod_i\mathbb P(F_i(K_{x_i})&gt;t_i).
$$</div>
<p>Only the event on the left needs to be measurable. It is Borel because connections and all the cluster evaluations are Borel. The full disjoint-occurrence set may be larger; its outer-probability bound is sufficient. In particular, no general measurability theorem for arbitrary Borel full-certificate events is being assumed.</p>
<p>Integrate over the positive levels using Tonelli. The level sets form a rectangle of volume $\prod_iF_i(K_{x_i})$ at each configuration, with zero volume when any factor vanishes, giving the finite-family inequality. For a countable family, the bounded variables $\mathbf1_{\mathcal D_k}\prod_{i=1}^kF_i(K_{x_i})$ decrease to the variable in the assertion. Bounded convergence and the finite-family inequality prove the result. $\square$</p>

<p>Allowing two arbitrary functionals would be false. On a graph with two vertices joined by one bond of opening probability $p\in(0,1)$, take both functionals to indicate a singleton cluster. Their distinct-cluster product has expectation $1-p$, whereas the product of their expectations is $(1-p)^2$. The monotonicity restriction is therefore substantive.</p>
<p>The argument also covers repeated roots: the distinct-cluster event is then empty as soon as a repetition occurs. It gives the <a href="/articles/cluster-partitions/#section-large-cluster-counts">large-cluster counting bound</a> by taking increasing volume-threshold indicators. This is a further written deduction, with independent mathematical review and Lean formalisation pending.</p>
