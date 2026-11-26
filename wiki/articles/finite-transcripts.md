---
{
  "id": "finite-transcripts",
  "title": "Finite exploration transcripts",
  "subtitle": "Conditioning on answers to adaptive queries",
  "kind": "method",
  "category": "Methods",
  "summary": "A fixed adaptive transcript is a cylinder event. Its probability factors over the queried coordinates, and the remaining coordinates keep their product law whenever conditioning is defined.",
  "context": [
    "An arbitrary coordinate set $I$ with product Bernoulli law $\\mathbb P_q$.",
    "A deterministic query rule whose next coordinate depends only on previous answers.",
    "Finitely many queries, with distinct coordinates along the transcript under consideration."
  ],
  "related": [
    "exploration",
    "product-model",
    "connectivity",
    "russo-formula"
  ],
  "sourceIds": [
    "mathlib",
    "hutchcroft-book",
    "perclib-configuration-conditioning",
    "perclib-block-independence",
    "perclib-boundary-wiring",
    "perclib-exploration-transcripts",
    "perclib-determined-events",
    "perclib-symmetry-associations",
    "perclib-finite-energy",
    "perclib-product-associations",
    "hutchcroft-lrp-3"
  ],
  "aliases": [
    "transcript",
    "adaptive queries",
    "decision tree",
    "deferred decisions",
    "unrevealed coordinates"
  ],
  "prototypeUses": []
}
---

## A fixed transcript {#section-fixed}

<p>Let $e_0,\ldots,e_{n-1}$ be coordinates and let $b=(b_0,\ldots,b_{n-1})\in\{0,1\}^n$. The transcript event is</p><div class="math-display">$$T(e,b)=\{\omega:\mathbf1_{\{e_k\in\omega\}}=b_k\text{ for every }k&lt;n\}.$$</div><p>Write $S=\{e_0,\ldots,e_{n-1}\}$, and set $w_i(1)=q_i$ and $w_i(0)=1-q_i$. This notation includes probabilities zero and one without powers of zero.</p>

<a id="tag-EE11" data-assertion="proposition" data-title="Finite transcript probability and factorization"></a><p>If $e_0,\ldots,e_{n-1}$ are distinct, the transcript has probability</p><div class="math-display">$$\mathbb P_q(T(e,b))=\prod_{k=0}^{n-1}w_{e_k}(b_k).$$</div><p>For every measurable event $B$ on the coordinates $I\setminus S$, with restriction map $\rho_{I\setminus S}$,</p><div class="math-display">$$\mathbb P_q\bigl(T(e,b)\cap\rho_{I\setminus S}^{-1}(B)\bigr)=\mathbb P_q(T(e,b))\,\mathbb P_{q|_{I\setminus S}}(B).$$</div><p><em>Proof.</em> The first equality is the finite cylinder formula. For the second, the two events use disjoint coordinate sets. Product factorization proves the equality first when $B$ is a cylinder. The collection of measurable $B$ for which it holds is a Dynkin system containing the cylinder pi-system, so it contains the product sigma-algebra. No division by the transcript probability is needed.</p><p>When $n=0$, the transcript is the whole space and the empty product is one. Distinctness is essential to the product formula: querying one coordinate twice and receiving two open answers has probability $q_i$, not $q_i^2$.</p>

<p>Bond-coordinate transcripts may include diagonal pairs. For example, observing the loop $\{x,x\}$ open and the distinct pair $\{x,y\}$ closed, with $y\ne x$, has probability $q_{\{x,x\}}(1-q_{\{x,y\}})$. This concerns the full configuration law; discarding loops from the simple graph does not erase them from the product probability space.</p>

## Why adaptive queries give cylinders {#section-adaptive}

<p>For each $k&lt;n$, let $a_k:\{0,1\}^k\to I$ choose the next coordinate from the preceding answers. The actual answers are defined recursively by</p><div class="math-display">$$B_k(\omega)=\mathbf1_{\{a_k(B_0(\omega),\ldots,B_{k-1}(\omega))\in\omega\}}.$$</div><p>For a fixed proposed answer string $b$, all its queries are fixed coordinates: put $e_k(b)=a_k(b_0,\ldots,b_{k-1})$.</p>

<a id="tag-86IX" data-assertion="proposition" data-title="Adaptive transcript cylinder identity"></a><p>For every $b\in\{0,1\}^n$,</p><div class="math-display">$$\{\omega:(B_0(\omega),\ldots,B_{n-1}(\omega))=b\}=T(e(b),b).$$</div><p>This identity does not require distinct queries. If the coordinates $e_k(b)$ are distinct, the probability and factorization formulas above therefore apply to the adaptive transcript.</p><p><em>Proof.</em> On the event that the answers equal $b$, the recursion queries $e_k(b)$ at every step and sees $b_k$, giving one inclusion. Conversely, suppose all the prescribed coordinate values hold. The zeroth query has no history and returns $b_0$. If the first $k$ answers agree with $b$, the next query is $e_k(b)$ and returns $b_k$. Induction gives the entire answer string.</p><p>The no-repeat condition is needed only along the fixed string in question. One need not assume that the query coordinates selected on different branches are disjoint. A stopping rule determined by the observed answers is handled at each terminal string by taking $n$ to be its length; the event of reaching that leaf is exactly its transcript cylinder. The statement does not cover a stopping rule that secretly inspects unrevealed coordinates.</p>

## The conditional law and its limits {#section-conditioning}

<a id="tag-56TE" data-assertion="corollary" data-title="Conditional product law after a positive-probability transcript"></a><p>Fix a transcript $b$ with distinct queries and positive probability. Given that transcript, the restriction to its unqueried coordinates has product Bernoulli law with the original parameters:</p><div class="math-display">$$\mathbb P_q\bigl(\rho_{I\setminus S(b)}(\omega)\in B\mid (B_0,\ldots,B_{n-1})=b\bigr)=\mathbb P_{q|_{I\setminus S(b)}}(B)$$</div><p>for every measurable $B$, where $S(b)=\{e_k(b):k&lt;n\}$. This is the factorization formula divided by the positive transcript probability. For a zero-probability transcript, factorization still holds, but this division does not define a conditional law.</p><p>This makes the <a href="/tag/GSLG/">deferred-decision principle</a> precise for deterministic finite queries. It does not say that the random set of queried coordinates is independent of the answers. For example, query coordinate $1$, then query $2$ if the first answer is open and $3$ otherwise. The queried set itself reveals the first answer.</p><p>An independently randomized query rule can be treated by fixing its auxiliary randomness and applying the deterministic argument, then integrating where the requisite measurability holds. The formulas here concern deterministic rules and do not assert a regular conditional distribution for arbitrary auxiliary spaces. Infinite runs likewise need a separate limiting argument; finitely many queries do not justify conditioning on a completed infinite exploration.</p>

<p>This conditional Bernoulli law enters the entropy chain rule for adaptive exploration. The entropy inequality requires additional estimates; it is not a consequence of transcript factorization alone.</p>

## Countable configuration spaces {#section-standard-borel}

<a id="tag-784S" data-assertion="theorem" data-title="Countable configuration spaces are standard Borel"></a>
<p>If $I$ is countable, the configuration space $\{0,1\}^I$, with the sigma-algebra generated by its coordinate maps, is a standard Borel space. In particular this applies to bond configurations on a countable vertex set, including diagonal coordinates.</p>
<p><em>Proof.</em> Choose an injection $j:I\to\mathbb N$ and put</p>
<div class="math-display">$$d(\omega,\eta)=\sum_{i\in I}2^{-j(i)-1}|\omega_i-\eta_i|.$$</div>
<p>This metric induces the product topology. Agreement on all coordinates with $j(i)&lt;m$ makes the distance at most $2^{-m}$, whereas a sufficiently small metric ball fixes any prescribed finite set of coordinates. A Cauchy sequence eventually stabilizes at each coordinate. Its coordinatewise limit is its metric limit, by splitting the sum into finitely many coordinates and a uniformly small tail; thus the metric is complete. Configurations with finite open support form a countable dense set. The finite cylinders are a countable topological base, so the Borel sigma-algebra is exactly the coordinate sigma-algebra. This is a Polish realization of the given measurable space. The empty index set gives a one-point space.</p>
<p>The countability here is a condition on the index set, not on the set of configurations. The latter is uncountable when $I$ is countably infinite. No claim about arbitrary uncountable index sets is needed.</p>

## Conditioning on a fixed coordinate set {#section-fixed-kernel}

<a id="tag-D9KI" data-assertion="theorem" data-title="An explicit conditional kernel for a fixed set of observed coordinates"></a>
<p>Let $I$ be countable, let $S\subseteq I$ be deterministic, and write $\mu_S=\mathbb P_{q|_S}$ and $\mu_{S^c}=\mathbb P_{q|_{I\setminus S}}$. For $\eta\in\{0,1\}^S$ and $\xi\in\{0,1\}^{I\setminus S}$, let $\eta\oplus\xi$ be their combined configuration. Then</p>
<div class="math-display">$$K(\eta,A)=\int\mathbf1_A(\eta\oplus\xi)\,\mu_{S^c}(d\xi)$$</div>
<p>is a probability kernel from the observed configurations to full configurations, and for every measurable $A\subseteq\{0,1\}^I$ and $B\subseteq\{0,1\}^S$,</p>
<div class="math-display">$$\mathbb P_q\bigl(\omega\in A,\ \omega|_S\in B\bigr)=\int_B K(\eta,A)\,\mu_S(d\eta).$$</div>
<p>Thus $K$ is a version of the conditional law of the full configuration given its restriction to $S$. It fixes the observed coordinates and leaves the complement with its original product law, for finite or infinite $S$.</p>
<p><em>Proof.</em> The assembly map $(\eta,\xi)\mapsto\eta\oplus\xi$ is measurable because each output coordinate is a coordinate of one of its arguments. For fixed $\eta$, its pushforward of $\mu_{S^c}$ is a probability measure. The integral defining $K(\eta,A)$ is measurable in $\eta$ by the measurable-parameter integration theorem, so $K$ is a kernel. The full product law is the pushforward of $\mu_S\otimes\mu_{S^c}$ under assembly: both measures have the same probabilities on finite cylinders. Fubini applied to $\mathbf1_B(\eta)\mathbf1_A(\eta\oplus\xi)$ gives the displayed identity.</p>
<p>This formula specifies a kernel even at observed configurations of probability zero; it does not divide by their probabilities. With $S$ finite and a positive-probability observation, it reduces to the transcript conditional law above. At $S=\varnothing$ it is the original law, and at $S=I$ it is the point mass at the observed configuration.</p>
<p>The set $S$ is fixed before sampling. For an adaptive exploration, a particular finite transcript fixes such a set, as proved above, but the random queried set cannot simply be substituted into this theorem. A completed infinite adaptive exploration requires its own measurability and conditional-law argument. Standard-Borel structure supplies a setting for conditional distributions; it does not supply that independence argument.</p>

## Independence of fixed coordinate blocks {#section-blocks}

<a id="tag-DYU8" data-assertion="theorem" data-title="Measurable observables of disjoint blocks are independent"></a>
<p>Let $I$ be any coordinate set and let $S,T\subseteq I$ be disjoint deterministic subsets, possibly infinite. Under $\mathbb P_q$, the restrictions $\rho_S(\omega)=\omega\cap S$ and $\rho_T(\omega)=\omega\cap T$ are independent random configurations with their respective product sigma-algebras. In particular, for measurable events $A\subseteq2^S$ and $B\subseteq2^T$,</p>
<div class="math-display">$$\mathbb P_q(\rho_S\in A,\rho_T\in B)=\mathbb P_{q|_S}(A)\mathbb P_{q|_T}(B).$$</div>
<p>More generally, if $f:2^S\to X$ and $g:2^T\to Y$ are measurable maps to measurable spaces, then $f(\rho_S)$ and $g(\rho_T)$ are independent. The coordinate membership variables are mutually independent, meaning that every finite subfamily has its product law.</p>
<p><em>Proof.</em> Restriction is measurable because each output coordinate is an original coordinate. Finite cylinders determine its product law, even when the block is infinite. For cylinders $A$ and $B$, their coordinate sets are disjoint, so the joint probability is the product of their probabilities. Fix a cylinder $A$. The measurable $B$ satisfying this equality form a Dynkin system containing the cylinder pi-system on $T$; hence the equality holds for every measurable $B$. Now fix any such $B$ and repeat the argument on $S$. This proves independence of the restrictions. Apply the factorization to inverse images of measurable sets under $f$ and $g$ for independence of their observables. The finite-cylinder formula also gives the asserted mutual independence of individual coordinates.</p>
<p>For instance, the negative and nonnegative integer coordinates give two independent infinite blocks, for any inhomogeneous profile. An empty block is deterministic; coordinates with probability zero or one cause no exception. Neither the ambient index set nor either block needs to be countable. Measurability in the product sigma-algebras is essential.</p>
<p>The blocks here are fixed sets. Independence does not follow merely because two random queried sets happen to be disjoint; the choice of a set can reveal coordinate values. The earlier transcript factorization accounts for that choice by first fixing the transcript.</p>

## Families of disjoint blocks {#section-block-families}

<a id="tag-QH7Q" data-assertion="proposition" data-title="Injective coordinate sampling, independent block families and countable closed products"></a>
<p>Let $I,J$ be arbitrary sets, let $q\in[0,1]^I$, and let $e:J\to I$ be injective. The sampled configuration $\{j:e(j)\in\omega\}$ is measurable and has product law with profile $q\circ e$. If $(S_b)_{b\in B}$ is any pairwise disjoint family of coordinate subsets, their restrictions are mutually independent: every finite family of measurable block events has joint probability equal to the product of its probabilities. The same is true of measurable observables of these blocks.</p>
<p>For a countable $T\subseteq I$,</p>
<div class="math-display">$$\mathbb P_q(\omega\cap T=\varnothing)=\prod_{i\in T}(1-q_i),$$</div>
<p>where the product is the limit of finite products along any increasing finite exhaustion. If $q_i=1-e^{-\beta J_i}$ on $T$, with finite $\beta\geq0$, nonnegative $J_i$ and $\sum_{i\in T}J_i&lt;\infty$, this probability is $\exp(-\beta\sum_{i\in T}J_i)$.</p>
<p><em>Proof.</em> Sampling is measurable coordinate by coordinate. Injectivity means that distinct sampled coordinates read distinct original coordinates, so every finite cylinder has the required product probability. Cylinder uniqueness identifies the sampled law.</p>
<p>For finitely many blocks, prove the factorization by induction. One block is disjoint from the union of all the others; by <a href="/tag/DYU8/">fixed-block independence</a>, its event is independent of the intersection of the other events, which is a measurable event of their union block. The induction hypothesis factors that intersection. Measurable observables preserve the factorization by taking inverse images. Since mutual independence is defined through finite subfamilies, this covers arbitrary $B$.</p>
<p>For countable $T$, the finite all-closed events decrease to $\{\omega\cap T=\varnothing\}$. Continuity from above and finite independence give the product formula. In the exponential case, each finite product equals the exponential of the corresponding negative intensity sum; summability and continuity give its limit. The empty product is one, and a coordinate of probability one makes the closed product zero.</p>
<p>With one vertex $x$ fixed, the map $y\mapsto\{x,y\}$ is injective, even when $y=x$ is allowed. Thus the closed-product formula applies to any countable collection of such pairs. If the targets include $x$, the diagonal coordinate participates in that configuration event, although it never contributes an edge to the simple graph. Boundary wiring uses the special case $x\in S$, with targets in $V\setminus S$, so no such diagonal occurs.</p>


## Events determined by coordinate blocks {#section-determined-events}

<p>An ambient event $A\subseteq2^I$ is <em>determined by</em> $S\subseteq I$ if membership in $A$ is unchanged whenever two configurations agree on $S$. This condition is often more convenient to check than an explicit formula for the event on $2^S$.</p>

<a id="tag-FH29" data-assertion="proposition" data-title="Measurable determination yields a measurable event on the coordinate block"></a>
<p>If $A$ is measurable and determined by $S$, there is a measurable $A_S\subseteq2^S$ such that</p>
<div class="math-display">$$A=\{\omega:\omega\cap S\in A_S\}.$$</div>
<p>Consequently, if $A_1,\ldots,A_m$ are measurable and determined by pairwise disjoint fixed blocks $S_1,\ldots,S_m$, then</p>
<div class="math-display">$$\mathbb P_q\left(\bigcap_{j=1}^m A_j\right)=\prod_{j=1}^m\mathbb P_q(A_j).$$</div>
<p>The ambient set and the blocks may be uncountable.</p>
<p><em>Proof.</em> Extend a configuration $\eta\subseteq S$ to $I$ by keeping every coordinate outside $S$ closed; call this map $j_S$. It is measurable coordinate by coordinate. Set $A_S=j_S^{-1}(A)$, which is measurable. The configurations $\omega$ and $j_S(\omega\cap S)$ agree on $S$, so determination gives the asserted identity. Apply <a href="/tag/DYU8/">independence of block restrictions</a> and its <a href="/tag/QH7Q/">finite-family form</a> to the events $A_{j,S_j}$.</p>
<p>Equivalently, one can prove the finite-family formula by induction: the intersection of the first $m-1$ events is measurable and determined by $S_1\cup\cdots\cup S_{m-1}$, which is disjoint from $S_m$. Empty blocks yield constant events, and the empty family has intersection the whole space and product one. For the deterministic representation alone, measurability of $A$ is unnecessary; it is needed to conclude that $A_S$ is measurable and to apply the probability formula.</p>
<p>This criterion concerns determination by a fixed block for every configuration. It does not say that two events are independent merely because one can find disjoint witnesses for them in a realized configuration. Nor does it make randomly selected blocks independent. A fixed adaptive transcript is already a cylinder on its fixed list of queried coordinates; its event on the unqueried complement therefore fits this criterion, including transcripts of probability zero. Only conditional division requires positive transcript probability.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-product-blocks/">32-contract product and block inventory</a> links the product-law construction, finite cylinders, block independence, determined events, transcript laws and relabelling to their existing arguments. Earlier source pins and records are preserved; no new compiled correspondence is asserted.</p>

## Scope of the tagged configuration statements {#section-configuration-associations}

<p>The source statement for <a href="/tag/784S/">784S</a> supplies the standard Borel property for the existing coordinate sigma-algebras on subsets of a countable index set and on bond configurations over countable vertices. It changes neither measurable space. The empty index set is included.</p>
<p>The statement for <a href="/tag/DYU8/">DYU8</a> has no countability premise. It bundles independence of restrictions to two fixed disjoint coordinate sets, their measurable-event factorization under the restricted product profiles, independence of measurable block observables, and mutual independence of coordinate membership variables. Both blocks can be infinite. This result supplies no independence claim for random blocks selected from the configuration. The <a href="/coverage/sources/perclib-22d8485-associations/">two source contracts</a> retain these quantifiers, with the negative and nonnegative integers as a witness involving two infinite blocks.</p>


## Overwriting a fixed block {#section-overwrite}

<a id="tag-DL0X" data-assertion="theorem" data-title="Fixed overwrites preserve the product law with modified marginals"></a>
<p>Let $I$ be arbitrary, fix $a\subseteq F\subseteq I$, and define $T(\omega)=(\omega\setminus F)\cup a$. Under $\mathbb P_q$, the law of $T(\omega)$ is $\mathbb P_r$, where</p>
<div class="math-display">$$r_i=\begin{cases}1,&amp;i\in a,\\0,&amp;i\in F\setminus a,\\q_i,&amp;i\notin F.\end{cases}$$</div>
<p>Neither $F$ nor $I$ needs to be countable. If $F$ is finite and $A\subseteq2^I$ is measurable, its image $T(A)$ is measurable and</p>
<div class="math-display">$$\mathbb P_q(T(A))=w_q(a;F)\,\mathbb P_{q|_{F^c}}(S_A)\geq w_q(a;F)\,\mathbb P_q(A),\qquad
w_q(a;F)=\prod_{i\in a}q_i\prod_{i\in F\setminus a}(1-q_i),$$</div>
<p>where $S_A$ is the set of outside configurations that admit at least one assignment on $F$ belonging to $A$.</p>
<p><em>Proof.</em> Each output coordinate of $T$ is either a fixed bit or an unchanged input bit, so $T$ is measurable. Its probabilities on finite cylinders are the products with parameters $r_i$. Uniqueness on the cylinder pi-system gives the pushforward identity.</p>
<p>Now let $F$ be finite. For each $b\subseteq F$, the section $A_b=\{\xi\subseteq F^c:\xi\cup b\in A\}$ is measurable, since assembly with a fixed assignment is measurable. Hence $S_A=\bigcup_{b\subseteq F}A_b$ is measurable. The image $T(A)$ consists exactly of the configurations with outside part in $S_A$ and assignment $a$ on $F$. The <a href="/tag/EE11/">finite assignment factorization</a> gives its probability. Finally $A\subseteq\{\omega:\omega\setminus F\in S_A\}$, proving the inequality.</p>
<p>Thus a positive-probability event remains of positive probability after this finite modification whenever $q_i&gt;0$ on $a$ and $q_i&lt;1$ on $F\setminus a$. Requiring every block probability to lie strictly between zero and one is sufficient for every assignment, but unnecessary when only inserting edges. In particular, forcing a finite set of positive-probability bonds open allows probability-one bonds. This is the precise step used in the <a href="/tag/6GNC/">infinite-cluster trichotomy</a>.</p>
<p>For a measurable event $B$ unchanged by modifications inside $F$, <a href="/tag/FH29/">determination by the complement</a> and factorization give $\mathbb P_q(B,\omega\cap F=a)=\mathbb P_q(B)w_q(a;F)$. This identity also holds when a factor vanishes; division to form a conditional law then does not. Inserting or deleting a single bond changes its marginal to one or zero, even for a diagonal pair. Its graph has no loop, but its coordinate law still changes.</p>
<p>The <a href="/sources/perclib-finite-energy/">finite-energy source</a> proves the overwrite law, the finite assignment identities and their positive-probability consequence for strictly interior block parameters. The image formula and its weaker assignment-specific positivity condition are deductions proved here. The image argument uses finiteness of $F$; the arbitrary-block pushforward alone does not assert measurability of images of arbitrary events or positive probability for an infinite prescribed assignment.</p>


## Splicing complete clusters {#section-cluster-splicing}

<a id="tag-DR5Q" data-assertion="theorem" data-title="Sequential cluster splicing preserves the product law"></a>
<p>Let $V$ be countable and let $\mathbb P_q$ be an independent bond law under which every cluster is finite almost surely. Diagonal coordinates may be included; they do not affect connectivity. Fix an ordered list of roots $v_1,\ldots,v_m$, and take independent configurations $\omega_1,\ldots,\omega_m,\omega_*$ with law $\mathbb P_q$. The copies have distinct labels even when some roots coincide. Starting with $U_0=\varnothing$, define</p>
<div class="math-display">$$D_i=K_{v_i}\bigl(\omega_i|_{V\setminus U_{i-1}}\bigr),\qquad
U_i=U_{i-1}\cup D_i,$$</div>
<p>where the cluster is empty when its root has been deleted. For each edge $e$, set $\eta(e)=\omega_i(e)$ for the least $i$ such that $e$ has an endpoint in $D_i$; if there is no such $i$, set $\eta(e)=\omega_*(e)$. Then $\eta$ has law $\mathbb P_q$. Every nonempty $D_i$ is a full cluster of $\eta$, and</p>
<div class="math-display">$$D_i\subseteq K_{v_i}(\omega_i).$$</div>
<p>If $v_i\in U_{i-1}$, its cluster in $\eta$ is the previously retained cluster containing it. These conclusions allow probabilities zero and one.</p>
<p><em>Proof.</em> First fix a deterministic remaining vertex set $W$ and a root $v\in W$. For a finite set $S\subseteq W$ containing $v$, the event that its cluster is exactly $S$, together with a specified assignment on all internal coordinates of $S$, is determined by the edges of $W$ incident to $S$. The internal assignment must connect $S$, and every edge from $S$ to $W\setminus S$ must be closed. The event uses no coordinate with both endpoints in $W\setminus S$.</p>
<p>By <a href="/tag/DYU8/">independence of fixed coordinate blocks</a>, its joint probability with any measurable exterior event factors. This is an identity without division, so it also holds for records of probability zero. There are only countably many possible finite sets and internal assignments. Summing over these records shows that a completed finite-cluster observation leaves its exterior with the original product law.</p>
<p>Apply this observation successively, conditioning on the preceding records, for which $W=V\setminus U_{i-1}$ is fixed. The next independent copy supplies exactly the cluster-record law of a single product configuration on that remainder. Filling the final exterior from $\omega_*$ therefore reconstructs the product law. Each restricted cluster is contained in the corresponding full cluster, so the finiteness assumption justifies every step. All constructions are measurable: connectivity is a countable union of finite-path events, and each output coordinate is selected by measurable cluster-membership tests.</p>
<p>The pieces are disjoint. Inside $D_i$ the edges come from $\omega_i$. An edge from $D_i$ to an earlier piece is closed by that earlier piece's boundary record; an edge from $D_i$ to the remaining vertices is closed by its own record. Thus $D_i$ is exactly a component of $\eta$. The argument observes a finite cluster with a possibly infinite incident edge set; it does not rely on completing that observation in finitely many edge queries.</p>
<p>For the three-root construction in Part III, use roots $0,x,y$ and write</p>
<div class="math-display">$$A=K_0(\omega_0),\qquad C=K_x(\omega_x),\qquad
B=K_x(\omega_x|_{V\setminus A}),\qquad H=K_y(\omega_y).$$</div>
<p>Then $B\subseteq C$ and $A\cap B=\varnothing$. The assembled configuration retains $A$ and, on $x\notin A$, retains $B$ as its $x$-cluster. Its $y$-cluster, when $y\notin A\cup B$, is $K_y(\omega_y|_{V\setminus(A\cup B)})$. The two-root constructions similarly give restrictions off $A$ and off $C$. Filling other exterior edges differently does not change any of these retained clusters.</p>
<p>Define the cut event, in the third independent configuration, by</p>
<div class="math-display">$$\mathcal D_S(y,a)=\{y\leftrightarrow a\text{ in }\omega_y\}
\setminus\{y\leftrightarrow a\text{ in }\omega_y|_{V\setminus S}\}.$$</div>
<p>A connection in a graph with a deleted endpoint is false. Consequently the three cut events used in the source coupling are exactly $\mathcal D_A$, $\mathcal D_C$, and $\mathcal D_{A\cup B}$. In particular $\mathcal D_A\subseteq\mathcal D_{A\cup B}$, and the triple-cluster loss has the pointwise representation</p>
<div class="math-display">$$\sum_a\mathbf1_{\mathcal D_{A\cup B}(y,a)}
=|H|-\mathbf1_{\{y\notin A\cup B\}}|K_y(\eta)|.$$</div>
<p>The analogous identities hold for the two single cuts. They include coincident roots and targets. They justify the cut-event representation in III.6.35–III.6.37; independence applies to the original copies, not to the assembled clusters.</p>
