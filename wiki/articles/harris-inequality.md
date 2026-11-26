---
{
  "id": "harris-inequality",
  "title": "The Harris inequality",
  "subtitle": "Positive association under a product law",
  "kind": "theorem",
  "category": "Foundations",
  "summary": "Increasing events under a product Bernoulli law are positively associated; finite witnesses connect this inequality to paths, escape and infinite clusters. On a finite configuration space, the lattice condition gives FKG association and Holley comparison for dependent measures.",
  "context": [
    "An index set $I$ and a profile $q:I\\to[0,1]$.",
    "Configurations $\\omega\\subseteq I$, with the product sigma-algebra and product Bernoulli law.",
    "Countability is imposed only for the finite-witness and graph applications."
  ],
  "related": [
    "product-model",
    "connectivity",
    "susceptibility"
  ],
  "sourceIds": [
    "hutchcroft-book",
    "grimmett",
    "mathlib",
    "perclib-open-event-harris",
    "perclib-harris-decreasing",
    "mathlib-four-functions",
    "perclib-fkg",
    "perclib-bond-harris-decreasing",
    "perclib-bond-harris-local",
    "perclib-harris-associations",
    "perclib-layer-cake-product",
    "perclib-cluster-correlation-interface",
    "hutchcroft-lrp-1",
    "hutchcroft-lrp-2"
  ],
  "aliases": [
    "Harris",
    "FKG",
    "positive association",
    "increasing events",
    "finite open witnesses",
    "decreasing events",
    "mixed monotonicity",
    "layer cake",
    "monotone functions",
    "four functions theorem",
    "Holley comparison",
    "lattice condition"
  ],
  "prototypeUses": [
    "product-model"
  ]
}
---

## Increasing events {#section-increasing}

<a id="tag-H4OA" data-assertion="definition" data-title="Increasing events and observables"></a><p>Order configurations by inclusion: $\omega\leq\omega'$ if every coordinate open in $\omega$ is also open in $\omega'$. An event $A$ is <em>increasing</em> if $\omega\in A$ and $\omega\leq\omega'$ imply $\omega'\in A$. A real-valued observable $f$ is increasing if $f(\omega)\leq f(\omega')$ whenever $\omega\leq\omega'$.</p><p>Connection events are increasing: opening more edges preserves every existing open path. Measurability is a separate requirement. On an infinite product space, it must be established before applying a probability inequality.</p>

## Positive association {#section-harris}

<a id="tag-X5SS" data-assertion="theorem" data-title="Harris inequality for product Bernoulli measures"></a><p>Let $I$ be any index set and let $\mathbb P_q$ be the product Bernoulli law with profile $q:I\to[0,1]$. If $A$ and $B$ are increasing measurable events, then</p><div class="math-display">$$\mathbb P_q(A\cap B)\geq\mathbb P_q(A)\mathbb P_q(B).$$</div><p>No coordinate probability is required to lie strictly between zero and one. The finite-coordinate proof uses the corresponding inequality for bounded increasing real-valued functions.</p><p><em>Proof.</em> For one coordinate with open probability $p$, direct expansion gives</p><div class="math-display">$$\mathbb E[fg]-\mathbb E[f]\mathbb E[g]=p(1-p)\bigl(f(1)-f(0)\bigr)\bigl(g(1)-g(0)\bigr)\geq0.$$</div><p>For finitely many coordinates, integrate out all but one. The induction hypothesis bounds the conditional average of $fg$ below by the product of the two conditional averages. Those averages are increasing functions of the remaining coordinate, since the other coordinates are integrated against the same product law at both values. The one-coordinate inequality completes the induction.</p><p>For an arbitrary index set, put $f=\mathbf1_A$ and $g=\mathbf1_B$. For finite $F\subseteq I$, average over the coordinates outside $F$, writing the resulting functions as $f_F$ and $g_F$. They are measurable increasing functions of the coordinates in $F$, and their expectations equal those of $f$ and $g$.</p><p>Bounded cylinder functions are dense in $L^1$ of the product sigma-algebra. Indeed, the events approximable in measure by finite-coordinate events form a sigma-algebra containing the cylinder algebra. If a cylinder function $h$ depends on $F_0$ and $F\supseteq F_0$, contraction of conditional averaging gives</p><div class="math-display">$$\|f_F-f\|_1\leq\|(f-h)_F\|_1+\|h-f\|_1\leq2\|f-h\|_1.$$</div><p>Thus, given $\varepsilon>0$, one finite set $F$ makes both $\|f_F-f\|_1$ and $\|g_F-g\|_1$ smaller than $\varepsilon$. Since all four functions take values in $[0,1]$,</p><div class="math-display">$$\bigl|\mathbb E[f_Fg_F]-\mathbb E[fg]\bigr|\leq\|f_F-f\|_1+\|g_F-g\|_1.$$</div><p>Apply the finite-coordinate inequality to $f_F,g_F$ and let $\varepsilon$ decrease to zero. This gives the event inequality. This argument uses finite subsets of $I$, not an enumeration, so countability is unnecessary. The integration and conditional-averaging steps use the usual product-measure and Fubini theorems.</p><a id="tag-22S9" data-assertion="corollary" data-title="Positive association for finitely many increasing events"></a><p>For increasing measurable events $A_1,\ldots,A_n$,</p><div class="math-display">$$\mathbb P_q\!\left(\bigcap_{j=1}^n A_j\right)\geq\prod_{j=1}^n\mathbb P_q(A_j).$$</div><p>Apply Harris inductively, since an intersection of increasing measurable events is again increasing and measurable. For $n=0$, both sides are one.</p>

## Finite open witnesses {#section-witnesses}

<a id="tag-5CN6" data-assertion="proposition" data-title="Measurability from finite open witnesses"></a><p>Suppose $I$ is countable and $A$ is increasing. Assume that every $\omega\in A$ contains a finite set $F\subseteq\omega$ such that the configuration consisting of exactly the open coordinates in $F$ belongs to $A$. Then $A$ is measurable.</p><p>For a finite set $F$, write $U_F=\{\omega:F\subseteq\omega\}$. The witness assumption and monotonicity give</p><div class="math-display">$$A=\bigcup_{\substack{F\subseteq I\text{ finite}\\F\in A}}U_F.$$</div><p>There are countably many finite subsets of $I$, and each $U_F$ is a cylinder event. This proves measurability. Consequently Harris applies to two such events without an additional measurability assumption. Countability is used in this measurability argument, although it was not needed in Harris itself.</p><p>For bond percolation on a countable vertex set, an open path supplies a finite witness for connection. The event that $x$ connects to some vertex outside a set $S$ likewise has a finite witness: retain the edges of one path to a vertex outside $S$. The path need not remain in $S$ before its endpoint, and no finiteness assumption on $S$ is needed.</p>

## Connection and escape {#section-connections}

<a id="tag-UPFU" data-assertion="corollary" data-title="Three-point lower bound from positive association"></a><p>For bond percolation on a countable vertex set and any vertices $x,y,z$, the two-point function satisfies</p><div class="math-display">$$\tau_q(x,z)\geq\tau_q(x,y)\tau_q(y,z).$$</div><p>Both connection events are increasing and measurable, so Harris bounds the probability of their intersection below by the product. Their intersection is contained in $\{x\leftrightarrow z\}$, by concatenating the two paths. Distinctness of the vertices is not required.</p><p>Write $E_S(x)=\{x\leftrightarrow V\setminus S\}$. Each $E_S(x)$ is increasing and measurable by the finite-witness argument. The infinite-cluster event is</p><div class="math-display">$$\{|K_x|=\infty\}=\bigcap_{\substack{S\subseteq V\text{ finite}}}E_S(x).$$</div><p>An infinite cluster meets the complement of every finite set; a finite cluster fails the escape event for $S=K_x$. Since $V$ is countable, the displayed intersection is countable. Thus the infinite-cluster event is also increasing and measurable, and Harris applies to pairs of these events as well as to connection and escape events.</p><p>Escaping one finite set is not the same as having an infinite cluster. On a graph with just one edge $\{x,y\}$, the cluster of $x$ escapes $\{x\}$ whenever that edge is open, but it is always finite. Harris supplies positive association between increasing events; it does not assert their independence.</p>

## Complementing the configuration {#section-complement}

<a id="tag-CW1V" data-assertion="proposition" data-title="Complementing Bernoulli coordinates complements their probabilities"></a>
<p>On any coordinate set $I$, let $C(\omega)=I\setminus\omega$. This is a measurable involution, and</p>
<div class="math-display">$$C_*\mathbb P_q=\mathbb P_{1-q},\qquad \mathbb P_q(C^{-1}A)=\mathbb P_{1-q}(A)$$</div>
<p>for every measurable event $A$. In particular, $\mathbb P_q=C_*\mathbb P_{1-q}$. Parameters zero and one are included.</p>
<p><em>Proof.</em> Each output coordinate is the complement of its input, so its probability of being open is $1-q_i$. Distinct outputs remain independent. The probabilities of all finite cylinders therefore agree with those of $\mathbb P_{1-q}$, which identifies the product law. Coordinatewise complementation is measurable and applying it twice is the identity. The event formula is the definition of pushforward.</p>
<p>For a single Bernoulli variable taking values $x,y$, exchanging the two values likewise exchanges the weights $q,1-q$; this is the one-coordinate form of the same identity. Complementing a configuration is different from taking the complement of an event. If $A$ is decreasing, then $C^{-1}A$ is increasing because $\omega\subseteq\omega'$ implies $C(\omega')\subseteq C(\omega)$.</p>

## Decreasing events and opposite monotonicities {#section-decreasing}

<a id="tag-F4CV" data-assertion="theorem" data-title="Harris inequalities for decreasing and oppositely monotone events"></a>
<p>Let $A,B$ be measurable events under a Bernoulli product law on any coordinate set. If both are decreasing, then</p>
<div class="math-display">$$\mathbb P_q(A\cap B)\geq\mathbb P_q(A)\mathbb P_q(B).$$</div>
<p>If $A$ is increasing and $B$ decreasing, then instead</p>
<div class="math-display">$$\mathbb P_q(A\cap B)\leq\mathbb P_q(A)\mathbb P_q(B).$$</div>
<p><em>Proof.</em> In the first case $C^{-1}A,C^{-1}B$ are increasing. Apply <a href="/tag/X5SS/">Harris</a> under $\mathbb P_{1-q}$ and transport the result by $C$. In the second case $A$ and $B^c$ are increasing, so</p>
<div class="math-display">$$\mathbb P_q(A\cap B)=\mathbb P_q(A)-\mathbb P_q(A\cap B^c)\leq\mathbb P_q(A)-\mathbb P_q(A)\mathbb P_q(B^c)=\mathbb P_q(A)\mathbb P_q(B).$$</div>
<p>Every term is a finite real number, so this subtraction is legitimate. These are the same inequalities whether probabilities are represented as real or extended nonnegative numbers.</p>
<p>For $\mathbb P_q(B)>0$, the mixed inequality says $\mathbb P_q(A\mid B)\leq\mathbb P_q(A)$. For example, conditioning on a specified vertex having a finite cluster cannot increase the probability of a measurable increasing event. This does not make the conditioned coordinates independent. The inequalities also do not extend to arbitrary events: opposite outcomes of the same nondegenerate coordinate have zero intersection but a positive product of probabilities.</p>

## Integrating the level sets {#section-layer-cake}

<a id="tag-KM1K" data-assertion="theorem" data-title="Layer-cake identities for nonnegative observables and their product"></a>
<p>Let $\mu$ be an s-finite measure, meaning a countable sum of finite measures, and let $f,g$ be measurable functions with values in $[0,\infty]$. Then</p>
<div class="math-display">$$\int f\,d\mu=\int_0^\infty\mu(f>s)\,ds,$$</div>
<div class="math-display">$$\int fg\,d\mu=\int_0^\infty\!\int_0^\infty\mu(f>s,\ g>t)\,ds\,dt,$$</div>
<div class="math-display">$$\left(\int f\,d\mu\right)\left(\int g\,d\mu\right)=\int_0^\infty\!\int_0^\infty\mu(f>s)\mu(g>t)\,ds\,dt.$$</div>
<p>All integrals are nonnegative extended integrals, with $0\cdot\infty=0$. No integrability hypothesis is needed.</p>
<p><em>Proof.</em> For every $a\in[0,\infty]$, the set $\{s>0:s<a\}$ has Lebesgue measure $a$. Hence</p>
<div class="math-display">$$f(\omega)=\int_0^\infty\mathbf1_{\{s<f(\omega)\}}\,ds,\qquad f(\omega)g(\omega)=\int_0^\infty\!\int_0^\infty\mathbf1_{\{s<f(\omega),\ t<g(\omega)\}}\,ds\,dt.$$</div>
<p>The level-set indicators are jointly measurable. Tonelli gives the first two identities. For the third, apply the first identity separately to $f,g$ and factor the integral on the two level variables. The maps $s\mapsto\mu(f>s)$ and $t\mapsto\mu(g>t)$ are nonincreasing, hence measurable. This last measurability observation holds for any measure, using outer measure for nonmeasurable superlevel sets, without a measurability assumption on $f$ or $g$; the integral identities do require those functions to be measurable and $\mu$ s-finite.</p>
<p>Consequently, a comparison of $\mu(f>s,g>t)$ with $\mu(f>s)\mu(g>t)$ for every pair of levels transfers to the corresponding comparison between $\int fg\,d\mu$ and $\int f\,d\mu\int g\,d\mu$. Both directions follow by integrating a pointwise inequality.</p>

## Nonnegative monotone observables {#section-extended-functions}

<a id="tag-E9HR" data-assertion="theorem" data-title="Harris association for extended nonnegative monotone observables"></a>
<p>Let $f,g:\{0,1\}^I\to[0,\infty]$ be measurable. If both are increasing or both decreasing, then</p>
<div class="math-display">$$\mathbb E_q[f]\mathbb E_q[g]\leq\mathbb E_q[fg].$$</div>
<p>If one is increasing and the other decreasing, then</p>
<div class="math-display">$$\mathbb E_q[fg]\leq\mathbb E_q[f]\mathbb E_q[g].$$</div>
<p>The coordinate set may be arbitrary, and either expectation may be infinite.</p>
<p><em>Proof.</em> A strict superlevel set of an increasing function is increasing; a strict superlevel set of a decreasing function is decreasing. For instance, $f(\omega)>s$ and $\omega\subseteq\omega'$ imply $f(\omega')\geq f(\omega)>s$ in the increasing case. These superlevel assertions use only the order and hold for functions taking values in any preordered set. Measurability of $f,g$ makes their real-threshold events measurable. Apply the appropriate event inequality at every pair of finite positive levels and integrate using the layer-cake identities.</p>
<p>The assertion is an inequality of nonnegative extended quantities. It is not a covariance formula when that formula would subtract infinities. If one expectation is zero and the other infinite, the product is zero by the extended nonnegative convention; there is no division by either expectation. Constant functions and deterministic product profiles require no exception.</p>

## Signed bounded observables {#section-bounded-functions}

<a id="tag-T6WJ" data-assertion="corollary" data-title="Covariance signs for bounded real monotone observables"></a>
<p>For bounded measurable real functions $f,g$ on any Bernoulli product space,</p>
<div class="math-display">$$\mathbb E_q[fg]-\mathbb E_q[f]\mathbb E_q[g]\geq0$$</div>
<p>when the functions have the same monotonicity, and the inequality reverses when their monotonicities are opposite. Finite-coordinate dependence is not required.</p>
<p><em>Proof.</em> Choose a finite $M\geq0$ with $|f|,|g|\leq M$. The functions $f+M,g+M$ are nonnegative, bounded and retain their monotonicities. Apply the preceding theorem. Every expectation is finite, so expanding both sides cancels the terms $M\mathbb E_q[f]+M\mathbb E_q[g]+M^2$ and gives the assertion.</p>
<p>The finite-coordinate ordered-product inequality is already recorded in <a href="/tag/9U6I/">the general association theorem</a>. The argument here removes the finite-dependence restriction for bounded Bernoulli observables by integrating level sets. Boundedness can be weakened under suitable integrability hypotheses, but the signed statement above makes no claim where $\mathbb E_q[fg]$ or the covariance is undefined. Its <a href="/coverage/sources/perclib-5d6efa8-harris-functions/">source inventory</a> separates the general measure identities, product-event inequalities and function forms, including their endpoint cases.</p>


## The four-functions inequality {#section-four-functions}

<p>The finite FKG inequality replaces the product-law hypothesis by an inequality for the masses of individual configurations. Its proof rests on the following finite-sum inequality, which also gives comparison between different measures.</p>

<a id="tag-EZJ7" data-assertion="theorem" data-title="Four-functions inequality on a finite Boolean lattice"></a>
<p>Let $E$ be finite and let $a,b,c,d:2^E\to[0,\infty)$ satisfy</p>
<div class="math-display">$$a(S)b(T)\leq c(S\cap T)d(S\cup T)\qquad(S,T\subseteq E).$$</div>
<p>Then</p>
<div class="math-display">$$\left(\sum_{S\subseteq E}a(S)\right)\left(\sum_{S\subseteq E}b(S)\right)
\leq\left(\sum_{S\subseteq E}c(S)\right)\left(\sum_{S\subseteq E}d(S)\right).$$</div>
<p>The four functions have finite nonnegative real values. They need not be monotone, normalized or strictly positive.</p>
<p><em>Proof.</em> First consider one coordinate. The assumptions give</p>
<div class="math-display">$$a_0b_0\leq c_0d_0,\qquad a_1b_1\leq c_1d_1,\qquad
u:=a_0b_1\leq A:=c_0d_1,\qquad v:=a_1b_0\leq A.$$</div>
<p>Also $uv=(a_0b_0)(a_1b_1)\leq AB$, where $B=c_1d_0$. If $A=0$, then $u=v=0$. If $A&gt;0$, the inequality $(A-u)(A-v)\geq0$ gives</p>
<div class="math-display">$$A(u+v)\leq A^2+uv\leq A(A+B),$$</div>
<p>so in either case $u+v\leq A+B$. Together with the two diagonal bounds this proves $(a_0+a_1)(b_0+b_1)\leq(c_0+c_1)(d_0+d_1)$.</p>
<p>Induct on $|E|$. The empty-set case is the assumed inequality for $S=T=\varnothing$. Otherwise choose $e\in E$ and, for $S\subseteq E\setminus\{e\}$, put $\bar a(S)=a(S)+a(S\cup\{e\})$, with analogous definitions for the other functions. Fix $S,T\subseteq E\setminus\{e\}$. Apply the one-coordinate inequality to the two values of $a$ above $S$, the two values of $b$ above $T$, those of $c$ above $S\cap T$, and those of $d$ above $S\cup T$. Its four hypotheses are exactly the original assumption for the four choices of whether $e$ is present. Thus</p>
<div class="math-display">$$\bar a(S)\bar b(T)\leq\bar c(S\cap T)\bar d(S\cup T).$$</div>
<p>The induction hypothesis applies on $E\setminus\{e\}$. Each collapsed sum is the corresponding original sum, proving the result.</p>

## FKG for a finite dependent law {#section-finite-fkg}

<a id="tag-TKDC" data-assertion="theorem" data-title="The finite lattice condition implies positive association"></a>
<p>Let $\mu$ be a probability measure on $2^E$, with $E$ finite, and write $w(S)=\mu(\{S\})$. Suppose</p>
<div class="math-display">$$w(S)w(T)\leq w(S\cap T)w(S\cup T)\qquad(S,T\subseteq E).$$</div>
<p>For increasing nonnegative real functions $f,g$ on $2^E$,</p>
<div class="math-display">$$\mathbb E_\mu[f]\mathbb E_\mu[g]\leq\mathbb E_\mu[fg].$$</div>
<p>In particular $\mu(A)\mu(B)\leq\mu(A\cap B)$ for increasing events $A,B$. Every function on this finite space is measurable and every real-valued function is integrable.</p>
<p><em>Proof.</em> Apply the four-functions inequality with $a=wf$, $b=wg$, $c=w$ and $d=wfg$. Indeed, the lattice condition and monotonicity give</p>
<div class="math-display">$$w(S)f(S)w(T)g(T)
\leq w(S\cap T)w(S\cup T)f(S\cup T)g(S\cup T).$$</div>
<p>Since $\sum_S w(S)=1$, the conclusion is the asserted expectation inequality. Indicators give the event form. Shifting $f$ and $g$ separately by constants to make them nonnegative and then cancelling the added terms also gives the covariance inequality for arbitrary increasing real-valued functions on this finite space. This last extension is an additional deduction; the source's function theorem states the nonnegative version.</p>
<p>Zero masses are allowed. On two coordinates, the law giving mass $1/2$ to each of $\varnothing$ and $E$ satisfies the lattice condition, but its coordinates are perfectly correlated. By contrast, the uniform law on the two singleton configurations fails the condition for those two configurations: its left-hand side is $1/4$ and its right-hand side is zero. The two coordinate-opening events then have intersection probability zero and marginal product $1/4$.</p>

## Holley comparison {#section-holley}

<a id="tag-KB49" data-assertion="theorem" data-title="Holley's finite lattice condition compares increasing expectations"></a>
<p>Let $E$ be finite and let $\mu,\nu$ be probability measures on $2^E$, with masses $u(S),v(S)$. If</p>
<div class="math-display">$$u(S)v(T)\leq u(S\cap T)v(S\cup T)\qquad(S,T\subseteq E),$$</div>
<p>then $\mathbb E_\mu[f]\leq\mathbb E_\nu[f]$ for every increasing real function $f$. In particular, $\mu(A)\leq\nu(A)$ for every increasing event $A$. Neither measure is assumed to have full support.</p>
<p><em>Proof.</em> First take $f\geq0$. In the four-functions inequality use $a=uf$, $b=v$, $c=u$ and $d=vf$. The required pointwise bound follows from the displayed condition and $f(S)\leq f(S\cup T)$. The total masses of $u$ and $v$ are both one, so the conclusion is precisely $\mathbb E_\mu[f]\leq\mathbb E_\nu[f]$. For a general real $f$, add a constant to make it nonnegative and cancel that constant from the expectations. The PercLib measure export states the increasing-event case; the observable form here follows by this same finite argument.</p>
<p>For Bernoulli product masses $w_p$, the lattice condition holds with equality: at each coordinate the two configurations contain the same number of open states as their intersection and union. If $p\leq q$ coordinatewise, the Holley condition for $w_p,w_q$ likewise reduces to a coordinatewise calculation. The only nontrivial case is a coordinate in $S\setminus T$, where it reads</p>
<div class="math-display">$$p_e(1-q_e)\leq(1-p_e)q_e,$$</div>
<p>which is equivalent to $p_e\leq q_e$. Multiplication over the finite coordinate set gives the required condition, including parameters zero and one. Thus finite Harris association and monotone product comparison are recovered without dividing by a configuration mass. For an empty coordinate set there is one configuration and both conclusions reduce to equality.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-association/">association inventory</a> distinguishes arbitrary-product Harris, countable finite-witness applications and the finite FKG/Holley statements. The four-functions proof above is the Boolean-lattice specialization of the theorem in the pinned mathlib dependency. An infinite dependent law requires a separate passage from suitable finite marginals or another approximation argument; the finite lattice condition is not applied directly to its singleton masses.</p>


## Non-connections and cluster volume {#section-bond-correlation}

<p>On a countable bond vertex set, non-connection events are decreasing and measurable. The <a href="/tag/F4CV/">decreasing and mixed Harris inequalities</a> give</p>
<div class="math-display">$$\mathbb P_q(x\not\leftrightarrow y,\ u\not\leftrightarrow v)
\geq(1-\tau_q(x,y))(1-\tau_q(u,v)),$$</div>
<div class="math-display">$$\mathbb P_q(x\leftrightarrow y,\ u\not\leftrightarrow v)
\leq\tau_q(x,y)(1-\tau_q(u,v)).$$</div>
<p>The cluster volume $|K_x|$ is an increasing measurable nonnegative observable, so <a href="/tag/E9HR/">extended Harris association</a>, applied with the connection indicator, also gives</p>
<div class="math-display">$$\chi_q(x)\tau_q(u,v)\leq\mathbb E_q\bigl[|K_x|\mathbf1_{\{u\leftrightarrow v\}}\bigr].$$</div>
<p>This is an extended nonnegative inequality, with $0\cdot\infty=0$. It allows infinite susceptibility and does not subtract two infinite terms to form a covariance. Repeated endpoints cause no exception: connection of a vertex to itself is certain and its non-connection event is empty. On two vertices with their bond open with probability $p$, the last inequality reads $(1+p)p\leq2p$.</p>

## Association inside a domain and escape transfer {#section-local-escape}

<p>Continue to assume $V$ countable. Fix $S\subseteq V$ and write $\tau_q^S(x,y)$ for connection using only vertices of $S$. These internal connection events are increasing and measurable by <a href="/tag/7BMQ/">the countable-domain argument</a>. Harris therefore applies to them, and concatenation gives $\tau_q^S(x,y)\tau_q^S(y,z)\leq\tau_q^S(x,z)$ for $x,y,z\in S$. The <a href="/tag/22S9/">finite-family inequality</a> likewise bounds the joint probability of any finitely many internal connections below by the product of their probabilities; the paths need not be disjoint.</p>
<a id="tag-EWMP" data-assertion="corollary" data-title="A connection transfers an escape probability between its endpoints"></a>
<p>For a deterministic $F\subseteq V$, let $E_F^S(x)$ be the event that $x$ connects inside $S$ to some vertex in $S\setminus F$. For $x,y\in S$,</p>
<div class="math-display">$$\tau_q^S(x,y)\mathbb P_q(E_F^S(y))\leq\mathbb P_q(E_F^S(x)).$$</div>
<p>Taking $S=V$ gives the full-graph inequality $\tau_q(x,y)\mathbb P_q(y\leftrightarrow F^c)\leq\mathbb P_q(x\leftrightarrow F^c)$.</p>
<p><em>Proof.</em> The escape event is the countable union, over $z\in S\setminus F$, of the internal connection events from its root to $z$. It is therefore measurable and increasing. Harris bounds the intersection of $\{x\leftrightarrow_S y\}$ and $E_F^S(y)$ below by the product in the display. Concatenating their paths shows that this intersection is contained in $E_F^S(x)$.</p>
<p>No finiteness of $F$ or $S$, positive lower bound on bond probabilities, or disjointness of the two witnesses is required. If $y\in S\setminus F$, its own escape event is certain by the length-zero path, and the bound becomes $\tau_q^S(x,y)\leq\mathbb P_q(E_F^S(x))$. If $S\subseteq F$, both escape events are empty. The argument uses association, not independence or disjoint occurrence.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-harris-associations/">source inventory</a> records the two bond-correlation modules and the existing product, Harris and Russo tag wrappers. It distinguishes grouped source statements from a completed correspondence review.</p>


## Restricting a product to an event {#section-restricted-layer-source}

<p>The new product layer-cake source keeps a measurable event $C$ inside the identity. For an S-finite measure and measurable nonnegative real functions $f,g$, Tonelli gives</p>
<div class="math-display">$$\int_C fg\,d\mu
=\int_0^\infty\!\int_0^\infty
\mu\bigl(C\cap\{f&gt;s\}\cap\{g&gt;t\}\bigr)\,ds\,dt.$$</div>
<p>At a fixed point of $C$, the contributing levels form the rectangle $(0,f)\times(0,g)$, of area $fg$; outside $C$ the contribution is zero. If its measure at every pair of positive levels is at most $\mu(f&gt;s)\mu(g&gt;t)$, integrating and factoring the latter product gives $\int_Cfg\,d\mu\leq\int f\,d\mu\int g\,d\mu$. Reversing the level-set inequality with $C$ the whole space gives the corresponding lower bound. These arguments permit infinite integrals, with the convention $0\cdot\infty=0$.</p>
<p>This source implements the finite-valued version of the <a href="/tag/KM1K/">layer-cake argument</a>. It assumes the indicator inequality to be integrated; the two-cluster or association argument establishing that inequality remains a separate obligation. Its one-dimensional restricted identity is stated for any measure, while the two-dimensional interchange retains S-finiteness. The <a href="/coverage/sources/perclib-3978a2f-tails/">detailed inventory</a> preserves those distinctions and the port attribution.</p>


## Cluster functionals and restoration {#section-cluster-interface}

<p>The <a href="/coverage/sources/perclib-f51f639-interfaces/">cluster-correlation interface</a> states the disjoint-cluster, Harris and upper covariance comparisons for increasing nonnegative cluster functionals whose compositions with the random cluster are measurable. Infinite integrals are allowed. In particular the upper comparison is expressed as a bound on the product expectation by the product of expectations plus the connected-cluster contribution; it does not subtract two possibly infinite expectations.</p>
<p>For the restoration map, take two configurations and retain the first on every pair touching its root cluster, and the second on all other pairs. At each fixed pair, the choice is a measurable event when the vertex set is countable, so the resulting configuration is measurable. This is what the interface proves about the map. Establishing its law, or using it in the general two-cluster gap inequality, requires a further argument. The general correlation comparisons are targets in this file, not consequences of measurability alone.</p>


## Separating two finite clusters {#section-finite-cluster-gap}

<a id="tag-1AC7" data-assertion="theorem" data-title="The correlation gap is supported on the common-cluster event when the first cluster is finite"></a>
<p>Let independent bond percolation be given on a countable vertex set, and suppose $K_x$ is finite almost surely. Let $F,G$ be nonnegative increasing functions of vertex sets, with measurable cluster evaluations. Then</p>
<div class="math-display">$$\mathbb E[F(K_x)G(K_y)\mathbf1_{\{x\not\leftrightarrow y\}}]
\leq\mathbb EF(K_x)\,\mathbb EG(K_y).$$</div>
<p>Extended nonnegative expectations are allowed. If the two expectations on the right and $\mathbb E[F(K_x)G(K_y)]$ are finite, then also</p>
<div class="math-display">$$0\leq\mathbb E[F(K_x)G(K_y)]-\mathbb EF(K_x)\,\mathbb EG(K_y)
\leq\mathbb E[F(K_x)G(K_y)\mathbf1_{\{x\leftrightarrow y\}}].$$</div>
<p>Equivalently, the distinct-cluster expectation lies between the product of expectations minus the common-cluster contribution and the product of expectations.</p>
<p><em>Proof.</em> Condition on $K_x=S$, for a finite set $S$ of positive probability. This event depends only on edges touching $S$: internally $x$ connects to every vertex of $S$, and every edge from $S$ to its complement is closed. Edges with both endpoints outside $S$ therefore retain their independent law. If $y\notin S$, its conditional cluster is the cluster in this outside graph. Adding independent edges touching $S$ couples it as a subset of a full-law cluster at $y$, so monotonicity of $G$ gives</p>
<div class="math-display">$$\mathbb E[G(K_y)\mathbf1_{\{y\notin K_x\}}\mid K_x=S]\leq\mathbb EG(K_y).$$</div>
<p>If $y\in S$ the left side is zero. Multiply by $F(S)$ and sum over the countably many finite sets $S$; the almost-sure finiteness assumption makes their probabilities sum to one. Tonelli, or bounded truncation followed by monotone convergence, covers infinite values. This proves the first inequality; it does not require $F$ to be increasing.</p>
<p>For the second assertion, increasing $F,G$ make their cluster evaluations increasing observables. <a href="/tag/E9HR/">Harris</a> gives the lower covariance bound. Split the product expectation according to whether $x$ and $y$ are connected and use the first inequality on the disconnected part for the upper bound. The finiteness assumptions justify the subtractions.</p>
<p>This finite-cluster proof supplies the comparison used for cutoff moment errors in Part II. It does not establish the unrestricted interface theorem when $K_x$ may be infinite; that extension requires its own exploration or restoration argument. In particular, the measurable restoration map discussed above is not being identified as measure preserving here.</p>


## A certificate comparison with BKR {#section-bkr-comparison}

<p>On a finite coordinate set, let $A$ be increasing and $D$ decreasing. Then $A\circ D=A\cap D$. Indeed, at $\omega\in A\cap D$, the set of open coordinates of $\omega$ certifies $A$: any agreeing configuration contains every open coordinate of $\omega$. The complementary set of closed coordinates certifies $D$: any agreeing configuration is contained in $\omega$. These certificates are disjoint. The reverse inclusion holds for every pair of events.</p>
<p>Consequently, taking the finite BKR inequality for arbitrary events as an input gives</p>
<div class="math-display">$$\mathbb P(A\cap D)\le\mathbb P(A)\mathbb P(D).$$</div>
<p>For increasing $A,B$, substitute $D=B^c$ and subtract from $\mathbb P(A)$ to recover the finite Harris inequality X5SS. This is the implication requested in Heydenreich–van der Hofstad Exercise 1.5. It does not prove the nonmonotone BKR input, and the independent proof of Harris above does not require that input. On infinitely many coordinates these full open and closed sets need not be finite certificates, so the finite-set argument is not asserted there.</p>
