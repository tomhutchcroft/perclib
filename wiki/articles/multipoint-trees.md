---
{
  "id": "multipoint-trees",
  "title": "Multipoint tree-graph bounds",
  "subtitle": "Tree-graph upper bounds and multiscale lower bounds",
  "kind": "theorem",
  "category": "Inequalities",
  "summary": "Disjoint tree witnesses give cluster-moment upper bounds. Sweep geometry organizes planar and long-range lower bounds; localization and small-cluster negligibility supply the mass needed for long-range joining.",
  "context": [
    "Independent bond percolation on a nonempty countable vertex set $V$.",
    "The profile may be inhomogeneous and may take the values zero and one; loops are discarded.",
    "$\\tau(x,y)=\\mathbb P(x\\leftrightarrow y)$, with $\\tau(x,x)=1$."
  ],
  "related": [
    "connectivity",
    "disjoint-occurrence",
    "susceptibility",
    "sharpness",
    "mesoscopic-tail-transfer",
    "cutoff-localization",
    "size-biased-laws"
  ],
  "sourceIds": [
    "hutchcroft-book",
    "hutchcroft-lrp-2",
    "perclib-branch-point",
    "perclib-tree-moments",
    "perclib-heavy-second-moment",
    "perclib-multipoint-interface",
    "hutchcroft-lrp-3",
    "hutchcroft-lrp-1"
  ],
  "aliases": [
    "multipoint connection",
    "tree-graph moment inequality",
    "binary tree topologies",
    "double-factorial moments",
    "multiscale cluster gluing",
    "long-range multipoint lower bound"
  ],
  "prototypeUses": []
}
---

## The tree shapes {#section-shapes}

<a id="tag-SO5J" data-assertion="proposition" data-title="Counting leaf-labelled trivalent tree shapes"></a>
<p>For an integer $k\geq2$, let $\mathcal T_k$ consist of isomorphism classes of finite unrooted trees whose leaves have the distinct labels $1,\ldots,k$ and whose other vertices all have degree three. Isomorphisms preserve the leaf labels. For $k=2$ the tree is a single edge. Every such tree has $k-2$ internal vertices and $2k-3$ edges, and</p>
<div class="math-display">$$|\mathcal T_k|=(2k-5)!!,$$</div>
<p>where $(-1)!!=1$.</p>
<p><em>Proof.</em> If there are $j$ internal vertices, the degree sum gives $k+3j=2(k+j-1)$, hence $j=k-2$ and the stated edge count. For $k\geq3$, remove the leaf labelled $k$ and suppress its now degree-two neighbour. This gives a tree in $\mathcal T_{k-1}$ together with the edge on which the leaf was attached. Conversely, subdividing any edge and attaching the new leaf reverses the operation. The smaller tree has $2k-5$ edges, so $|\mathcal T_k|=(2k-5)|\mathcal T_{k-1}|$. Starting from $|\mathcal T_2|=1$ proves the formula.</p>
<p>Choose one representative of each shape and an arbitrary enumeration of its internal vertices. This enumeration is only for writing the sums below; internal vertices are not extra labelled shapes.</p>

## The multipoint inequality {#section-multipoint}

<a id="tag-AFH6" data-assertion="theorem" data-title="Multipoint tree-graph inequality on a countable bond model"></a>
<p>For $k\geq2$ and vertices $x_1,\ldots,x_k$, not necessarily distinct,</p>
<div class="math-display">$$\mathbb P(x_1,\ldots,x_k\text{ lie in one open cluster})\leq\sum_{T\in\mathcal T_k}\ \sum_{z\in V^{\operatorname{Int}(T)}}\ \prod_{\{u,v\}\in E(T)}\tau(\xi_u,\xi_v),$$</div>
<p>where $\xi_i=x_i$ at the labelled leaves and $\xi_v=z_v$ at internal vertices. The sums are nonnegative extended sums; no susceptibility or transitivity assumption is imposed.</p>
<p><em>Proof from finite-coordinate BK.</em> First allow only finitely many bonds to be open. A connection of the marked vertices has a finite open tree witness: take paths joining them, choose a spanning tree of their union, and prune branches containing no marked vertex. Attach a separate labelled pendant leaf at each occurrence of a marked vertex, assigning it the same position as that vertex and an empty path to it. This includes repeated marked vertices. Suppress all unlabelled degree-two vertices, concatenating the corresponding paths. No unlabelled leaves remain.</p>
<p>Replace each vertex of degree greater than three by a tree of degree-three vertices joining its incident branches, assigning every new vertex the old position and every inserted edge an empty path. Such a replacement can be made by successively separating two incident branches; each step reduces the remaining excess degree by one. The result is a shape in $\mathcal T_k$ with a position assigned to every vertex. Each of its edges carries an open path between its assigned endpoints. The nonempty paths have pairwise disjoint edge sets, since they partition edges of the original tree. Empty paths have empty witnesses and require no open loop.</p>
<p>For a fixed shape and internal positions, these paths witness disjoint occurrence of the $2k-3$ connection events. Finite-coordinate BK for increasing events, iterated using <a href="/tag/HP3X/">associativity of disjoint occurrence</a>, bounds this event by the product of its two-point probabilities. Finite BK is the standard probability input to this proof. A union bound over the finitely many shapes and countably many position assignments gives the result for the restricted graph.</p>
<p>Now exhaust the non-loop bonds by increasing finite sets. Every simultaneous connection has a finite path witness, so the restricted probabilities on the left increase to the full probability. Each restricted two-point factor is bounded by its full-model value, giving the same right side at every stage. Passing to the limit proves the displayed inequality.</p>
<p>For $k=2$ the bound is equality. For $k=3$ there is one shape and one branch position, giving the familiar three-point tree-graph bound. For $k=4$ there are three shapes. The construction remains valid when all marked positions coincide: every path may then be empty. It never replaces edge-disjointness by vertex-disjointness.</p>

## The three-point product inequality {#section-gladkov}

<a id="tag-87RB" data-assertion="theorem" data-title="Gladkov three-point inequality and countable finite-witness extension"></a>
<p>For independent bond percolation on a countable vertex set and any three vertices $x,y,z$,</p>
<div class="math-display">$$\mathbb P(x,y,z\text{ lie in one cluster})^2\leq8\tau(x,y)\tau(y,z)\tau(z,x).$$</div>
<p>The finite-graph theorem for distinct vertices is the cited input: Gladkov, <a href="https://arxiv.org/html/2408.08457v1#S6">Percolation Inequalities and Decision Trees</a>, arXiv:2408.08457v1, Theorem 1.1 and §6, Theorem 6.2. Its proof uses the decision-tree inequalities developed in that paper; it is not supplied by the tree-graph estimate above.</p>
<p><em>Extension from the finite theorem.</em> Exhaust the vertex set by finite sets containing the marked vertices, and close all edges outside the induced finite model. A finite complete host with zero probabilities for absent edges puts each restriction within the finite theorem. Endpoint probabilities also follow by continuity of finite-product probabilities. Every pair connection, and every simultaneous connection of the three marked vertices, has a finite collection of path witnesses. Their probabilities therefore increase to the corresponding full-model probabilities. Pass to the limit in the finite inequality. No local finiteness or susceptibility assumption is needed for this passage.</p>
<p>If two marked vertices coincide, the inequality reduces to $\tau(x,z)^2\leq8\tau(x,z)^2$ after relabelling; if all coincide it reads $1\leq8$. Thus repetitions are also allowed. This is the countable-model interpretation, with the finite cited input and the exhaustion argument distinguished.</p>

<a id="tag-5PHR" data-assertion="proposition" data-title="Independent continuations do not imply ordinary disjoint connection witnesses"></a>
<p>Two independent continuations of a stopped cluster search can both reach a target even though the underlying graph admits no edge-disjoint connections from the two previously connected marked vertices to that target.</p>
<p><em>Proof.</em> Take the path $y-x-z$. Give $xy$ probability one and $xz$ probability $q\in(0,1)$. Start at $x$, query $xy$ first, and stop on reaching $y$. Independently resample the unqueried edge $xz$ in two continuations. Both continuations reach $z$ with probability $q^2&gt;0$. But every $x$--$z$ path and every $y$--$z$ path in the original graph use the same edge $xz$. Hence ordinary disjoint occurrence of these two connections is impossible, even in the fully open configuration.</p>
<p>The two copies of $xz$ are distinct coordinates in the continuation product space. Projecting them back to a single edge destroys that distinction. The example does not contradict the three-point inequality: here its left side is $q^2$ and its right side is $8q^2$. It explains why an exploration argument needs a precisely formulated decision-tree inequality and cannot be completed by claiming ordinary edge-disjointness of the two continuations. A full account of the adaptive coupling remains separate.</p>

## The four-point matching expression {#section-four-point}

<a id="tag-2GTM" data-assertion="proposition" data-title="Conditional four-point bound retains the maximum over matchings"></a>
<p>Fix four distinct marked vertices $A=\{x_1,x_2,x_3,x_4\}$ in a countable independent bond model. Write $t_{ij}=\tau(x_i,x_j)$ and $t_B$ for the probability that all vertices of $B$ lie in one cluster. Assume the four-point case of a higher-order Gladkov inequality:</p>
<div class="math-display">$$t_A^2\leq108\max_{A=A_1\sqcup A_2\sqcup A_3}t_{A_1\cup A_2}t_{A_2\cup A_3}t_{A_3\cup A_1},$$</div>
<p>where the parts are nonempty. Then</p>
<div class="math-display">$$t_A^4\leq746496\left(\prod_{i&lt;j}t_{ij}\right)\max\{t_{12}t_{34},t_{13}t_{24},t_{14}t_{23}\}.$$</div>
<p>Replacing the maximum by the sum gives a symmetric sum bound. The maximum cannot in general be replaced by a single prescribed matching with a universal constant.</p>
<p><em>Proof.</em> Every partition has part sizes $1,1,2$. For singleton vertices $a,b$ and doubleton $\{c,d\}$, its product is $t_{ab}t_{acd}t_{bcd}$. Apply the <a href="/tag/87RB/">three-point inequality</a> to the last two factors and square:</p>
<div class="math-display">$$\bigl(t_{ab}t_{acd}t_{bcd}\bigr)^2\leq64t_{ab}^2t_{cd}^2t_{ac}t_{ad}t_{bc}t_{bd}=64\left(\prod_{i&lt;j}t_{ij}\right)t_{ab}t_{cd}.$$</div>
<p>Square the assumed inequality and maximize over the partitions. The unordered complementary singleton pairs produce precisely the three matchings, and $108^2\cdot64=746496$. The argument uses no division and includes zero connection probabilities.</p>
<p>To see why the maximum matters, take deterministic edges $x_1x_2$ and $x_3x_4$, and join $x_2$ to $x_3$ by a bond of probability $q\in(0,1)$, with no other edges. Then $t_A=q$, $t_{12}=t_{34}=1$, and the four cross-pair probabilities equal $q$. The product of all six probabilities is $q^4$. Choosing the prescribed matching $13|24$ would bound $q^4$ by a universal constant times $q^6$, which is impossible as $q\downarrow0$. The maximum correctly selects $12|34$. This example also satisfies the assumed higher-order inequality, whose maximal partition product is $q^2$.</p>
<p>This supplies the algebra for the four-point bound. A fixed partition produces a term in the maximum; it does not by itself produce a bound for the full four-point probability. The higher-order inequality with constant $108$ is an explicit input here, not a consequence of the cited three-point theorem alone.</p>

## All cluster moments {#section-moments}

<a id="tag-Y84V" data-assertion="corollary" data-title="All cluster moments under uniform finite susceptibility"></a>
<p>Write $\chi_x=\sum_y\tau(x,y)$ and suppose $M=\sup_x\chi_x&lt;\infty$. Then, for every root $o$ and integer $m\geq1$,</p>
<div class="math-display">$$\mathbb E|K_o|^m\leq(2m-3)!!\,\chi_o M^{2m-2}\leq(2m-3)!!\,M^{2m-1}.$$</div>
<p>If susceptibility has the same finite value $\chi$ at every vertex, this is the bound $(2m-3)!!\chi^{2m-1}$. In particular, it holds in an invariant transitive model with finite susceptibility.</p>
<p><em>Proof.</em> Counting ordered tuples, with repetitions allowed, and using Tonelli gives</p>
<div class="math-display">$$\mathbb E|K_o|^m=\sum_{x_1,\ldots,x_m}\mathbb P(o,x_1,\ldots,x_m\text{ lie in one cluster}).$$</div>
<p>Apply the multipoint inequality with $k=m+1$. For each shape there are $2m-1$ edges; only the position of the leaf corresponding to $o$ is fixed. Sum successively over the position of a leaf different from this root, and delete that leaf. Its single incident factor has sum at most $M$. Continue until only the root and its neighbour remain. The last sum is $\chi_o$, so this shape contributes at most $\chi_oM^{2m-2}$. The tree count gives $(2m-3)!!$ shapes. When $m=1$ there is just the last edge and the identity is $\mathbb E|K_o|=\chi_o$.</p>
<p>Finite susceptibility at the chosen root alone is not the uniform hypothesis used in this summation. Every intermediate vertex requires a row bound. Equal susceptibilities, for example by transitivity, allow the bound to be written in terms of the single number $\chi$.</p>

## A finite root mean need not control its second moment {#section-root-counterexample}

<a id="tag-HRS7" data-assertion="proposition" data-title="A countable bond model with root susceptibility two and infinite second moment"></a>
<p>There is an independent bond model on a countable connected host graph with a root $o$ such that</p>
<div class="math-display">$$\mathbb E|K_o|=2,\qquad \mathbb E|K_o|^2=\infty.$$</div>
<p>Its root cluster is finite almost surely, but $\mathbb E e^{t|K_o|}=\infty$ for every $t&gt;0$. The susceptibilities of other vertices are not uniformly bounded.</p>
<p><em>Proof.</em> Take disjoint finite paths $C_k$, $k\geq1$, with $|C_k|=2^k$, and add one edge from $o$ to an endpoint of each path. Open every internal path edge with probability one. Independently open the edge from $o$ to $C_k$ with probability $4^{-k}$; all other pairs have probability zero. If $B_k$ is the indicator of that edge, then</p>
<div class="math-display">$$|K_o|=1+\sum_{k\geq1}2^k B_k,\qquad \mathbb E|K_o|=1+\sum_{k\geq1}2^{-k}=2.$$</div>
<p>Tonelli justifies the expectation, and its finiteness implies that $K_o$ is finite almost surely. On the other hand, $|K_o|^2\geq\sum_{k\geq1}4^kB_k$, whose expectation is infinite. Since $e^{tx}\geq t^2x^2/2$ for $x\geq0$, every positive exponential moment is infinite as well. A vertex in $C_k$ always belongs to a cluster of size at least $2^k$, so the susceptibility supremum is infinite.</p>
<p>Thus the uniform row bound in the preceding moment theorem cannot be replaced by finiteness at the chosen root. In this example the formula $\mathbb E|K_o|^2\leq\chi_o^3$ would read $\infty\leq8$. The example does not concern transitive models, where a finite root susceptibility is automatically uniform.</p>

## Dilation of a continuum multipoint limit {#section-continuum-dilation}

<a id="tag-5PBL" data-assertion="proposition" data-title="Regularly varying normalization fixes the dilation exponent"></a>
<p>For a fixed bond law on $\mathbb Z^d$ and an integer $k\geq2$, write $\tau_k(z_1,\ldots,z_k)$ for the probability that the marked vertices lie in one cluster. Let $f$ be eventually positive and regularly varying at infinity with index $\sigma\in\mathbb R$: for each $c&gt;0$, $f(c\lambda)/f(\lambda)\to c^\sigma$. Suppose the finite limit</p>
<div class="math-display">$$T_k(x_1,\ldots,x_k)=\lim_{\lambda\to\infty}f(\lambda)^k\tau_k(\lfloor\lambda x_1\rfloor,\ldots,\lfloor\lambda x_k\rfloor)$$</div>
<p>exists for every tuple of pairwise distinct points in $\mathbb R^d$, with $\lambda$ tending to infinity through positive real values and floors taken coordinatewise. Then, for every $c&gt;0$,</p>
<div class="math-display">$$T_k(cx_1,\ldots,cx_k)=c^{-k\sigma}T_k(x_1,\ldots,x_k).$$</div>
<p><em>Proof.</em> Put $s=c\lambda$. Before taking the limit, the expression defining the left side equals</p>
<div class="math-display">$$\left[\frac{f(s/c)}{f(s)}\right]^k f(s)^k\tau_k(\lfloor sx_1\rfloor,\ldots,\lfloor sx_k\rfloor).$$</div>
<p>The bracket tends to $c^{-\sigma}$ and the remaining factor to the assumed finite limit. There is no rounding error: $\lfloor\lambda(cx_i)\rfloor=\lfloor sx_i\rfloor$ exactly.</p>
<p>This proves the continuum multipoint dilation rule once the limits and regular variation are supplied. Slowly varying factors, including logarithms, are absorbed in $f$ without changing this rule. The proposition allows the zero limit; it proves neither existence nor nontriviality. Convergence only along integer scales is a weaker hypothesis and does not justify the real reparametrization used here without further control. Translation, rotation and conformal covariance are not established by this dilation argument. The classification below assumes the full covariance law.</p>

## Two and three points under conformal covariance {#section-conformal-forms}

<a id="tag-N76U" data-assertion="theorem" data-title="Mobius covariance determines two- and three-point functions"></a>
<p>Let $d\geq2$ and $\sigma\in\mathbb R$. For $k=2,3$, let $T_k$ be a finite nonnegative function on ordered tuples of $k$ distinct points in $\mathbb R^d$. Suppose that for every Mobius transformation $\phi$, whenever the marked points and their images are finite,</p>
<div class="math-display">$$T_k(\phi(x_1),\ldots,\phi(x_k))=\left(\prod_{i=1}^k\lambda_\phi(x_i)^{-\sigma}\right)T_k(x_1,\ldots,x_k),$$</div>
<p>where $\lambda_\phi(x)&gt;0$ is the local length-scaling factor. Here the Mobius group is generated by Euclidean similarities, including reflections, and sphere inversions, acting on the one-point compactification. Then there are constants $C_2,C_3\geq0$ such that</p>
<div class="math-display">$$T_2(x_1,x_2)=C_2\|x_1-x_2\|^{-2\sigma},\qquad T_3(x_1,x_2,x_3)=C_3\prod_{1\leq i&lt;j\leq3}\|x_i-x_j\|^{-\sigma}.$$</div>
<p>No continuity, permutation symmetry or strict positivity of $T_k$ is assumed. If, in addition,</p>
<div class="math-display">$$T_3(x,y,z)^2\leq8T_2(x,y)T_2(y,z)T_2(z,x)$$</div>
<p>for all distinct triples, then $C_3^2\leq8C_2^3$.</p>
<p><em>Proof.</em> The Mobius distance identity is</p>
<div class="math-display">$$\|\phi(x)-\phi(y)\|=\lambda_\phi(x)^{1/2}\lambda_\phi(y)^{1/2}\|x-y\|.$$</div>
<p>It follows by direct calculation for similarities and inversions and then by composition. If an intermediate image is infinite, approximate the finite endpoints by points avoiding the finitely many intermediate poles and pass to the limit in this identity. The final map is smooth with positive length factor at the endpoints under consideration. This argument concerns the map and the distance identity; it assumes no continuity of $T_k$.</p>
<p>The covariance factors therefore cancel in</p>
<div class="math-display">$$R_2(x,y)=T_2(x,y)\|x-y\|^{2\sigma},\qquad R_3(x,y,z)=T_3(x,y,z)\bigl(\|x-y\|\|y-z\|\|z-x\|\bigr)^\sigma.$$</div>
<p>Similarities act transitively on ordered pairs of distinct points, so $R_2$ is constant. To see the corresponding fact for triples, take two ordered triples $(x_1,x_2,x_3)$ and $(y_1,y_2,y_3)$. Write</p>
<div class="math-display">$$I_a(z)=\frac{z-a}{\|z-a\|^2},\qquad I_a(a)=\infty,\qquad I_a(\infty)=0.$$</div>
<p>A similarity $S$ sends the ordered pair $(I_{x_3}(x_1),I_{x_3}(x_2))$ to $(I_{y_3}(y_1),I_{y_3}(y_2))$. Hence the single Mobius transformation $\phi=I_{y_3}^{-1}\circ S\circ I_{x_3}$ sends each $x_i$ to $y_i$. Its final images are finite, including $\phi(x_3)=y_3$. If $S(z)=cUz+v$, direct expansion near $x_3$ gives $\phi(x_3+h)=y_3+c^{-1}Uh+O(\|h\|^2)$, so the length factor there is $c^{-1}&gt;0$. The assumed covariance therefore applies to this map. We never evaluate $T_3$ at an infinite point. Thus $R_3$ is constant as well, proving both formulas. Substitution into the additional inequality cancels the positive product of distance powers and gives $C_3^2\leq8C_2^3$.</p>
<p>The additional inequality holds, in particular, if $T_2$ and $T_3$ are finite continuum limits with the same positive normalization $f$: multiply the discrete <a href="/tag/87RB/">Gladkov inequality</a> by $f(\lambda)^6$ and pass to the limit at a fixed distinct triple, whose lattice approximations are distinct for all sufficiently large scales. This implication uses the cited finite three-point theorem through 87RB; the classification of covariant functions does not. The zero three-point limit is allowed.</p>
<p>This proves the conditional continuum two- and three-point classification. It does not establish existence, nontriviality or conformal covariance of a percolation limit. For four points, the ratio $\|x_1-x_2\|\|x_3-x_4\|/(\|x_1-x_3\|\|x_2-x_4\|)$ is unchanged by the distance identity and takes different values on different configurations. The group is consequently not transitive on ordered quadruples, so the same constancy argument no longer applies.</p>

## Recursive distance geometry {#section-recursive-geometry}

<a id="tag-Y4H4" data-assertion="definition" data-title="Recursive three-part distance quantity"></a>
<p>For a finite set $A\subset\mathbb R^d$ of at least two distinct points, define $S(A)$ recursively by</p>
<div class="math-display">$$S(\{x,y\})=\|x-y\|_2^2,\qquad S(A)=\min_{A=A_1\sqcup A_2\sqcup A_3}\sqrt{S(A_1\cup A_2)S(A_2\cup A_3)S(A_3\cup A_1)}\quad(|A|\geq3),$$</div>
<p>where all three parts are nonempty. Each pairwise union has between two and $|A|-1$ points, so the recursion terminates. There are finitely many partitions and every base distance is positive; consequently $0&lt;S(A)&lt;\infty$ and the minimum is attained. No value on singletons is needed.</p>

<a id="tag-9YE6" data-assertion="proposition" data-title="Explicit small-set formulas and covariance of the recursive distance quantity"></a>
<p>For three points, $S(\{x,y,z\})=\|x-y\|_2\|y-z\|_2\|z-x\|_2$. For four points $A=\{a,b,c,d\}$, it is the minimum over the three unordered pairings of the expressions</p>
<div class="math-display">$$\|a-b\|_2\|c-d\|_2\sqrt{\|a-c\|_2\|a-d\|_2\|b-c\|_2\|b-d\|_2}.$$</div>
<p>More generally, suppose $\phi$ is injective on $A$ and positive numbers $\lambda(x)$ satisfy</p>
<div class="math-display">$$\|\phi(x)-\phi(y)\|_2^2=\lambda(x)\lambda(y)\|x-y\|_2^2\qquad(x,y\in A).$$</div>
<p>Then $S(\phi(A))=S(A)\prod_{x\in A}\lambda(x)$. In particular, for a similarity $\phi(x)=cUx+v$ with $c&gt;0$ and orthogonal $U$, one has $S(\phi(A))=c^{|A|}S(A)$.</p>
<p><em>Proof.</em> A three-point partition consists of three singletons. For four points every partition has sizes $1,1,2$; insert the three-point formula into the recursion to obtain the displayed pairing term. Interchanging the singleton pair and its complement leaves that term unchanged, giving precisely three possibilities.</p>
<p>The covariance identity holds for two points by assumption. Suppose it holds for all proper subsets of $A$ of size at least two. In any three-part partition, each point belongs to exactly two pairwise unions. The product of their three covariance factors is therefore $\prod_{x\in A}\lambda(x)^2$. Its square root is independent of the partition, so it factors out of the minimum. Injectivity makes partitions of $A$ correspond bijectively to partitions of $\phi(A)$, completing the induction. For a similarity take $\lambda(x)=c$.</p>
<p>Inversion $\phi(x)=x/\|x\|_2^2$ on nonzero points satisfies the same distance identity with $\lambda(x)=\|x\|_2^{-2}$, as direct expansion of the squared distance shows. The identity is preserved under composition, multiplying the factors at successive images. Thus the covariance also applies to compositions of similarities and inversions whenever all points and images are finite and avoid the relevant poles. This is a property of $S$, not a claim of conformal covariance for percolation probabilities.</p>

<a id="tag-C4A5" data-assertion="proposition" data-title="Higher-point product inequalities imply the recursive geometric bound"></a>
<p>Let $A\subset\mathbb R^d$ be finite, $n=|A|\geq2$, and let $t(B)\geq0$ be specified for every subset $B\subseteq A$ with at least two points. Suppose $\sigma,C_2&gt;0$ and constants $K_m&gt;0$, $3\leq m\leq n$, satisfy</p>
<div class="math-display">$$t(\{x,y\})\leq C_2\|x-y\|_2^{-2\sigma},\qquad t(B)^2\leq K_{|B|}\max_{B=B_1\sqcup B_2\sqcup B_3}\prod_{i&lt;j}t(B_i\cup B_j)\quad(|B|\geq3),$$</div>
<p>with nonempty parts. Set $D_2=C_2$ and recursively</p>
<div class="math-display">$$D_m=\left[K_m\max_{\substack{a,b,c\geq1\\a+b+c=m}}D_{a+b}D_{b+c}D_{c+a}\right]^{1/2}.$$</div>
<p>Then $t(A)\leq D_n S(A)^{-\sigma}$.</p>
<p><em>Proof.</em> The pair case is the assumed bound. At each larger set, apply induction to the three proper pairwise unions. Their constants are bounded by the maximum in $D_m$, while their distance factors obey</p>
<div class="math-display">$$\max_{B=B_1\sqcup B_2\sqcup B_3}\left[\prod_{i&lt;j}S(B_i\cup B_j)\right]^{-\sigma/2}=S(B)^{-\sigma}.$$</div>
<p>This identity uses $\sigma&gt;0$: taking a negative power turns the maximum into the minimum defining $S$. Taking the square root of the product inequality completes the induction. All constants depend only on the cardinality and the given input constants.</p>
<p>For connection probabilities, a higher-order Gladkov input has $K_m=4(m-1)^2(2^{m-2}-1)$. With a two-point estimate of exponent $d-2+\eta&gt;0$, take $2\sigma=d-2+\eta$. The proposition gives the stated recursive bound once those inputs hold. This covers the recursion and covariance; it proves neither the higher-order probability inequality nor the separate comparison with arborescence sweep products or planar RSW lower bounds.</p>

## Comparing the recursion with sweep trees {#section-sweep}

<a id="tag-CS13" data-assertion="definition" data-title="Sweep product on a finite metric space"></a>
<p>Let $(A,d)$ be a finite metric space with $n\geq2$. Use the recursion of <a href="/tag/Y4H4/">Y4H4</a> with pair values $d(x,y)^2$ to define $S_d(A)$. For a tree on $A$ directed toward a root, let $A_x$ consist of $x$, its parent and all its descendants when $x$ is not the root; set $A_{\rm root}=A$. Define</p>
<div class="math-display">$$\operatorname{Sweep}_d(A)=\min_T\prod_{x\in A}\operatorname{diam}_d(A_x),$$</div>
<p>where the minimum ranges over all rooted trees on $A$. The root factor is included. Both quantities are positive, are nondecreasing in each distance, and multiply by $c^n$ when every distance is multiplied by $c&gt;0$. For $S_d$ these facts follow by induction through the recursion; for the sweep product they hold for every tree before taking the minimum.</p>

<a id="tag-ESZG" data-assertion="theorem" data-title="Exact recursive and sweep products for an ultrametric"></a>
<p>Suppose $d$ is an ultrametric on $A$, meaning $d(x,z)\leq\max\{d(x,y),d(y,z)\}$. If $T$ is a spanning tree of minimum edge-length product, then</p>
<div class="math-display">$$S_d(A)=\operatorname{Sweep}_d(A)=\operatorname{diam}_d(A)\prod_{e\in T}d(e).$$</div>
<p><em>Proof.</em> Denote the expression on the right by $U(A)$. For any subset $B$ of at least two points, let $c_t(B)$ count its equivalence classes under $d(x,y)\leq t$. Kruskal's construction joins each such class internally before using larger edges, so its minimum-product spanning tree has $|B|-c_t(B)$ edges of length at most $t$. Minimum-product optimality follows by the usual exchange argument: replacing a longer edge by a shorter edge across its cut decreases the product. Put $f(1)=0$ and $f(k)=k$ for $k\geq2$. For $R=\operatorname{diam}(A)$, integrating the logarithms of the tree edges and the extra diameter factor gives</p>
<div class="math-display">$$\log U(B)=|B|\log R-\int_0^R\bigl(|B|-f(c_t(B))\bigr)\,\frac{dt}{t}.$$</div>
<p>The integrand vanishes below the smallest positive distance in $B$. The extra subtraction when $c_t(B)=1$ accounts for the diameter factor.</p>
<p>Fix a three-part partition of $A$ and $0&lt;t&lt;R$, so $c=c_t(A)\geq2$. Each $t$-class meets either one part, contributing two to the sum of the three union class counts, or several parts, contributing three. Thus that sum is $2c+h$, where $h$ counts classes meeting several parts. At most one pairwise union can have only one class: two such unions would force all of $A$ into one class. If there is one, its class meets two parts, so $h\geq1$. Consequently</p>
<div class="math-display">$$\sum_{i&lt;j}f(c_t(A_i\cup A_j))\geq2c_t(A).$$</div>
<p>Insert this inequality into the integral formula to get $U(A)\leq\sqrt{\prod_{i&lt;j}U(A_i\cup A_j)}$.</p>
<p>When $|A|\geq3$, a partition attaining equality can be chosen simultaneously at every threshold. Consider the maximal blocks of diameter less than $R$. If there are at least three, divide whole blocks into three nonempty groups. Every smaller threshold class lies in one part, and each pairwise union meets at least two maximal blocks, so equality holds. If there are exactly two maximal blocks, one has at least two points. Split that block into two groups of its own maximal subblocks, and use the other block as the third part. Below the first block's diameter, each class lies in one part. Above that diameter and below $R$, exactly one class meets two parts and exactly one pairwise union has one class. Again equality holds. Since $U$ agrees with $d^2$ on pairs, induction now gives $S_d=U$.</p>
<p>For any rooted tree, each nonroot set $A_x$ contains its parent edge. Its sweep product is therefore at least $\operatorname{diam}(A)$ times the product of its edge lengths, hence at least $U(A)$. To attain this bound, choose a root in one maximal ultrametric block, construct such trees recursively inside all blocks, and attach the root of every other block directly to the chosen root. Every nonroot descendant set together with its parent has diameter exactly the length of its parent edge. The connecting edges have length $R$, and the resulting edge product is minimal by the same block decomposition. Its sweep product is $U(A)$.</p>

<a id="tag-WDGK" data-assertion="theorem" data-title="Recursive and sweep geometry are comparable with explicit cardinality constants"></a>
<p>For every finite metric space $(A,d)$ with $n\geq2$,</p>
<div class="math-display">$$(n-1)^{-n}\operatorname{Sweep}_d(A)\leq S_d(A)\leq(n-1)^n\operatorname{Sweep}_d(A).$$</div>
<p><em>Proof.</em> Take a minimum-product spanning tree $T$ for $d$, set $u(x,x)=0$, and for distinct $x,y$ let $u(x,y)$ be the largest edge length on its unique $x$--$y$ path. This is an ultrametric: the $x$--$z$ path is contained in the union of the $x$--$y$ and $y$--$z$ paths. Also $u(x,y)\leq d(x,y)$, since otherwise replacing a largest path edge by $xy$ would decrease the tree product. The triangle inequality along the path gives the reverse comparison</p>
<div class="math-display">$$u(x,y)\leq d(x,y)\leq(n-1)u(x,y).$$</div>
<p>Monotonicity and degree-$n$ homogeneity place both $S_d(A)$ and $\operatorname{Sweep}_d(A)$ between $S_u(A)=\operatorname{Sweep}_u(A)$ and $(n-1)^n$ times that common value. Comparing the two intervals gives the result.</p>
<p>This proves the fixed-cardinality sweep comparison by ultrametric reduction. It includes the two-point case exactly and retains the root factor in the sweep definition. The comparison is deterministic; it supplies neither the higher-order percolation inequality nor an RSW gluing argument.</p>

## Planar arm-and-circuit gluing {#section-planar-gluing}

<a id="tag-FAT3" data-assertion="theorem" data-title="A planar multipoint lower bound from circuit and two-point inputs"></a>
<p>Consider homogeneous nearest-neighbour bond percolation on $\mathbb Z^2$. Write $B_r(x)=x+[-r,r]^2$ for the lattice box. Suppose $a,c,s&gt;0$ satisfy:</p>
<ul><li>$\tau(x,y)\geq a\|x-y\|_2^{-2s}$ for distinct lattice vertices;</li><li>for every integer $r\geq1$, the probability of an open simple circuit contained in $B_{4r}(0)\setminus B_{2r}(0)$ and surrounding $B_{2r}(0)$ is at least $c$.</li></ul>
<p>Then every set $A$ of $k\geq2$ distinct lattice vertices satisfies</p>
<div class="math-display">$$\mathbb P(A\text{ lies in one cluster})\geq\bigl(c\sqrt a\,48^{-s}\bigr)^k\operatorname{Sweep}(A)^{-s},$$</div>
<p>where sweep diameters use Euclidean distance. If the two-point upper bound and higher-point product hypotheses of <a href="/tag/C4A5/">C4A5</a> also hold with exponent $s$, then the connection probability is comparable, with fixed-cardinality constants, to both $S(A)^{-s}$ and $\operatorname{Sweep}(A)^{-s}$.</p>
<p><em>Proof.</em> Let $\pi(r)$ be the probability of an arm from zero to the vertex boundary of $B_r(0)$, using edges inside the box. The event $0\leftrightarrow3re_1$ forces an arm inside each of the disjoint boxes $B_r(0)$ and $B_r(3re_1)$. Those arm events depend on disjoint edge coordinates and have the same probability. Thus, for integer $r\geq1$,</p>
<div class="math-display">$$\pi(r)^2\geq\tau(0,3re_1)\geq a(3r)^{-2s},\qquad\pi(r)\geq\sqrt a\,(3r)^{-s}.$$</div>
<p>Choose a rooted tree attaining the sweep minimum, deterministically from the marked points. Put $R_x=\operatorname{diam}(A_x)$ and $r_x=\lceil R_x\rceil$. Distinct lattice points give $R_x\geq1$, so $r_x\leq2R_x$. If $y$ has parent $x$, then $A_y\subseteq A_x$, hence $r_y\leq r_x$, and $\|x-y\|_\infty\leq R_y\leq r_y$.</p>
<p>For each marked point $x$, require an arm from $x$ to $\partial B_{8r_x}(x)$ and an open circuit in $B_{4r_x}(x)\setminus B_{2r_x}(x)$ surrounding the inner box. All these events are increasing. Harris association and the two hypotheses give their joint probability at least</p>
<div class="math-display">$$\prod_{x\in A}c\pi(8r_x)\geq\prod_{x\in A}c\sqrt a\,(24r_x)^{-s}\geq\bigl(c\sqrt a\,48^{-s}\bigr)^k\prod_{x\in A}R_x^{-s}.$$</div>
<p>No independence between the arms and circuits is assumed.</p>
<p>It remains to check the deterministic gluing. For a child $y$ with parent $x$, both vertices are inside the inner box surrounded by the circuit at $y$. The arm from $y$ exits its outer box. The endpoint $v$ of the parent's arm also lies outside that outer box, since</p>
<div class="math-display">$$\|v-y\|_\infty\geq8r_x-\|x-y\|_\infty\geq8r_x-r_y\geq7r_y&gt;4r_y.$$</div>
<p>Each arm therefore crosses the child's circuit. In the planar nearest-neighbour embedding such crossings share lattice vertices, so the two arms are connected through the open circuit. This joins every child to its parent, and hence all marked points. The product of the $R_x$ is the sweep minimum, proving the lower bound. The conditional upper bound is C4A5; <a href="/tag/WDGK/">the deterministic sweep comparison</a> identifies the two geometric quantities up to constants.</p>
<p>This supplies the gluing argument, with integer radii and the crossing geometry explicit. At $p=1/2$, the uniform circuit lower bound is the RSW input, which is not proved here. The two-point power law and higher-order product inequalities likewise remain hypotheses where used. Only a lower arm estimate is needed, and the two-disjoint-box argument supplies it without a full two-point/one-arm comparison theorem.</p>

## Growth from a revealed cluster {#section-cluster-extension}

<a id="tag-F4RR" data-assertion="proposition" data-title="An independent added layer bounds growth conditional on the original cluster"></a>
<p>Let $\omega$ and $\xi$ be independent bond configurations on a countable vertex set. Write $C=K_o(\omega)$ and $K_o^+=K_o(\omega\cup\xi)$. Suppose the union law has uniformly bounded susceptibility $\sup_v\mathbb E|K_v^+|\leq\chi_+&lt;\infty$, and the added-edge probabilities satisfy</p>
<div class="math-display">$$\sup_u\sum_{v\ne u}\mathbb P(\{u,v\}\in\xi)\leq\varepsilon&lt;\infty.$$</div>
<p>Then almost surely</p>
<div class="math-display">$$\mathbb E\bigl[|K_o^+|\mid C\bigr]\leq(1+\varepsilon\chi_+)|C|.$$</div>
<p>In particular, for every nonnegative function $f$ of the original cluster,</p>
<div class="math-display">$$\mathbb E\bigl[|K_o^+|f(C)\bigr]\leq(1+\varepsilon\chi_+)\mathbb E\bigl[|C|f(C)\bigr],$$</div>
<p>with extended expectations allowed.</p>
<p><em>Proof.</em> The cluster $C$ is finite almost surely. Conditional on $C=S$, all original boundary bonds are closed, while original bonds with both endpoints outside $S$ keep their independent law. No added bond has been revealed. If $x\in K_o^+\setminus S$, take a finite open path to $x$ and its last exit from $S$. That exit uses an added bond $\{u,v\}$, with $u\in S$ and $v\notin S$, followed by a path lying entirely outside $S$. Its added bond is independent of the outside configuration. The expected size of the outside union cluster at $v$ is at most $\chi_+$ by domination by the full union law. Summing over $x,u,v$ gives</p>
<div class="math-display">$$\mathbb E\bigl[|K_o^+|\mid C=S\bigr]\leq |S|+\sum_{u\in S}\sum_{v\notin S}\mathbb P(\{u,v\}\in\xi)\chi_+\leq(1+\varepsilon\chi_+)|S|.$$</div>
<p>Tonelli justifies the sums. Multiplication by $f(S)$ and averaging proves the last assertion. The last-exit choice is useful here: the remaining path uses no revealed boundary bond, even if the original path left and re-entered $S$ several times.</p>

## Mass at one scale and at smaller scales {#section-multiscale-mass}

<a id="tag-D6CQ" data-assertion="proposition" data-title="Localized moments and mesoscopic negligibility supply the mass events for gluing"></a>
<p>Let $K^{(r)}$ be random sets containing a root $o$ in a countable metric space, for $r\geq1$. Put $X_r=|K^{(r)}|$, $Y_{r,\lambda}=|K^{(r)}\cap B_{\lambda r}(o)|$, and $m_q(r)=\mathbb E X_r^q$. Fix $0&lt;\alpha&lt;\theta$. Assume positive constants $C_1,c_2,C_3$ satisfy</p>
<div class="math-display">$$m_1(r)\leq C_1r^\alpha,\qquad m_2(r)\geq c_2r^{\alpha+\theta},\qquad m_3(r)\leq C_3r^{\alpha+2\theta}.$$</div>
<p>Assume the first two moments localize: for every $\eta&gt;0$ a single $\lambda\geq1$ gives $m_q(r)\leq(1+\eta)\mathbb E Y_{r,\lambda}^q$ for $q=1,2$ and every $r\geq1$. Assume also <a href="/tag/QMN5/">mesoscopic negligibility</a> at scale $r^\theta$. Then there are fixed $a,b&gt;0$ and $\lambda_0\geq1$ such that</p>
<div class="math-display">$$\mathbb P(Y_{r,\lambda_0}\geq ar^\theta)\geq br^{\alpha-\theta}\qquad(r\geq1).$$</div>
<p>Moreover, for each $\eta&gt;0$ there are $\delta&gt;0$ and $\lambda\geq1$ such that</p>
<div class="math-display">$$\mathbb E\bigl[X_r;Y_{r,\lambda}\leq\delta r^\theta\bigr]\leq\eta r^\alpha\qquad(r\geq1).$$</div>
<p><em>Proof.</em> Choose $\lambda_0$ with $\mathbb E Y_{r,\lambda_0}^2\geq m_2(r)/2$, and set $a=c_2/(4C_1)$. Writing $Y=Y_{r,\lambda_0}$, the contribution of $Y&lt;ar^\theta$ to its second moment is at most $ar^\theta\mathbb E Y\leq c_2r^{\alpha+\theta}/4$. Hence Hölder's inequality gives</p>
<div class="math-display">$$\frac{c_2}{4}r^{\alpha+\theta}\leq\mathbb E[Y^2;Y\geq ar^\theta]\leq(\mathbb E Y^3)^{2/3}\mathbb P(Y\geq ar^\theta)^{1/3}.$$</div>
<p>Cubing and using $\mathbb E Y^3\leq m_3(r)$ proves the probability bound, for example with $b=(c_2/4)^3/C_3^2$.</p>
<p>For the second assertion, choose $\lambda$ so that $\mathbb E(X_r-Y_{r,\lambda})\leq\eta r^\alpha/2$ uniformly. For every $h&gt;0$,</p>
<div class="math-display">$$X_r\mathbf1_{\{Y_{r,\lambda}\leq h\}}\leq X_r-Y_{r,\lambda}+(X_r\wedge h).$$</div>
<p>Mesoscopic negligibility and the mean upper bound give a $\delta&gt;0$ for which $\mathbb E(X_r\wedge\delta r^\theta)\leq\eta r^\alpha/2$ at all sufficiently large radii, say $r\geq r_0$. Decrease $\delta$ further until $\delta r_0^\theta&lt;1$. At $1\leq r&lt;r_0$ the bad event is empty, since $Y_{r,\lambda}\geq1$. This extends the estimate to every radius without interchanging the two limits in mesoscopic negligibility.</p>

<a id="tag-JC24" data-assertion="proposition" data-title="Large-scale local mass makes small-scale local mass conditionally likely"></a>
<p>Consider a translation-invariant increasing family of independent bond laws on $\mathbb Z^d$, coupled by independent Poisson edge increments. Suppose $\chi_R\leq C R^\alpha$ and, for $1\leq r\leq R$, the added layer from $r$ to $R$ has off-diagonal probability row at most $C r^{-\alpha}$. Let $0&lt;\alpha&lt;\theta$. Suppose fixed $a,b&gt;0$, $\lambda_0\geq1$ give events</p>
<div class="math-display">$$E_R=\{|K_o^{(R)}\cap B_{\lambda_0R}(o)|\geq aR^\theta\},\qquad\mathbb P(E_R)\geq bR^{\alpha-\theta},$$</div>
<p>and suppose the localized small-mass estimate in <a href="/tag/D6CQ/">D6CQ</a> holds for every $\eta&gt;0$. Then for every $\varepsilon&gt;0$ there exist $\delta&gt;0$ and $\lambda\geq1$ such that, simultaneously for all $1\leq r\leq R$,</p>
<div class="math-display">$$\mathbb P\bigl(|K_o^{(r)}\cap B_{\lambda r}(o)|\leq\delta r^\theta\mid E_R\bigr)\leq\varepsilon.$$</div>
<p><em>Proof.</em> Write $D_r$ for the event being conditioned against. It depends only on the smaller cluster. The <a href="/tag/F4RR/">cluster-extension bound</a> gives</p>
<div class="math-display">$$\mathbb E[|K_o^{(R)}|;D_r]\leq(1+C^2r^{-\alpha}R^\alpha)\eta r^\alpha\leq(1+C^2)\eta R^\alpha.$$</div>
<p>On $E_R$, the larger cluster has at least $aR^\theta$ vertices. Therefore</p>
<div class="math-display">$$\mathbb P(D_r\mid E_R)\leq\frac{\mathbb E[|K_o^{(R)}|;D_r]}{aR^\theta\mathbb P(E_R)}\leq\frac{(1+C^2)\eta}{ab}.$$</div>
<p>Choose $\eta\leq\varepsilon ab/(1+C^2)$. The constants $a,b$ of the conditioning event stay fixed while its conditional error is made arbitrarily small.</p>

## Joining at separated scales {#section-long-range-gluing}

<a id="tag-L5IG" data-assertion="theorem" data-title="Multiscale local mass and fresh edges imply a sweep lower bound"></a>
<p>Let $d\geq1$, $0&lt;\alpha&lt;d$, $\theta=(d+\alpha)/2$ and $s=\theta-\alpha$. Consider a translation-invariant bond process $(\omega_r)_{r\geq1}$ on $\mathbb Z^d$, with independent Poisson increments on each unordered non-loop edge, and let $\omega_\infty=\bigcup_r\omega_r$. Suppose the events $E_R$ and the uniform conditional conclusion of <a href="/tag/JC24/">JC24</a> hold. Suppose also that for every $D\geq1$ there is $c_D&gt;0$ such that the added Poisson intensity between radii $r$ and $2Dr$ on each edge of length at most $Dr$ is at least $c_Dr^{-d-\alpha}$, uniformly for $r\geq1$. Then for every integer $n\geq2$ there is $c_n&gt;0$ such that every set $A$ of $n$ distinct lattice vertices satisfies</p>
<div class="math-display">$$\mathbb P(A\text{ lies in one cluster of }\omega_\infty)\geq c_n\operatorname{Sweep}(A)^{-s}.$$</div>
<p>Diameters and balls use Euclidean distance. Constants may depend on $n$ and the stated uniform inputs, but not on the positions of the marked vertices.</p>
<p><em>Proof.</em> Choose a rooted tree attaining the <a href="/tag/CS13/">sweep minimum</a>. Enumerate its vertices $a_1,\ldots,a_n$ so that $R_i=\operatorname{diam}(A_{a_i})$ is nondecreasing and every parent has larger index than its child. This is possible because $A_x\subseteq A_{\operatorname{parent}(x)}$; break equal-radius ties with children first. The root is $a_n$, and each $R_i\geq1$.</p>
<p>Apply conditional persistence with $\varepsilon=1/(2n)$, obtaining $\delta,\lambda$. Set $D=2\lambda+1$, $L=2D$, and $r_i=L^iR_i$. Thus $r_{i+1}\geq Lr_i$. For each $j$, let $F_j$ require</p>
<div class="math-display">$$|K_{a_j}^{(r_i)}\cap B_{\lambda r_i}(a_j)|&gt;\delta r_i^\theta\qquad(1\leq i\leq j).$$</div>
<p>Conditional on the translated event $E_{r_j}$, a union bound over its $j$ scales gives $\mathbb P(F_j\mid E_{r_j})\geq1-j/(2n)\geq1/2$. Consequently $\mathbb P(F_j)\geq(b/2)r_j^{-s}$. All $F_j$ are increasing in the Poisson coordinates, so Harris association gives</p>
<div class="math-display">$$\mathbb P\left(\bigcap_{j=1}^nF_j\right)\geq(b/2)^n\prod_{j=1}^nr_j^{-s}.$$</div>
<p>Reorder the same requirements by scale. Let $A_i$ require the local-mass bound at radius $r_i$ for every $a_j$ with $j\geq i$, so that $\mathcal A=\bigcap_i A_i=\bigcap_jF_j$. Let $\mathcal F_i$ reveal all increments up to $r_i$. For $i&lt;n$, write $\sigma(i)&gt;i$ for the parent index and let $G_i$ be the event that $a_i$ and $a_{\sigma(i)}$ are connected by radius $Lr_i$.</p>
<p>On $A_i$, both clusters have more than $\delta r_i^\theta$ vertices in their respective $\lambda r_i$ balls. If the clusters already agree, $G_i$ holds. Otherwise these two sets are disjoint, and every edge between them has length at most</p>
<div class="math-display">$$2\lambda r_i+|a_i-a_{\sigma(i)}|\leq(2\lambda+1)r_i=Dr_i.$$</div>
<p>The fresh increments on these edges are independent given $\mathcal F_i$. Since $2\theta=d+\alpha$, the conditional probability that at least one appears by $Lr_i$ is at least $q=1-\exp(-c_D\delta^2)&gt;0$. Hence $\mathbb P(G_i\mid\mathcal F_i)\geq q\mathbf1_{A_i}$.</p>
<p>The later mass events and $G_i$ are increasing in the unexposed independent increments. Conditional Harris therefore implies</p>
<div class="math-display">$$\mathbb P\left(G_i\cap\bigcap_{j&gt;i}A_j\mid\mathcal F_i\right)\geq q\mathbf1_{A_i}\mathbb P\left(\bigcap_{j&gt;i}A_j\mid\mathcal F_i\right).$$</div>
<p>Every earlier $G_j$ is $\mathcal F_i$-measurable because $Lr_j\leq r_i$. Multiply by $\mathbf1_{\cap_{j\leq i}A_j\cap\cap_{j&lt;i}G_j}$ and average. This gives the correctly indexed recurrence</p>
<div class="math-display">$$\mathbb P\left(\mathcal A\cap\bigcap_{j\leq i}G_j\right)\geq q\mathbb P\left(\mathcal A\cap\bigcap_{j&lt;i}G_j\right).$$</div>
<p>After $n-1$ steps, all tree links hold with probability at least $q^{n-1}\mathbb P(\mathcal A)$. They connect all marked vertices in $\omega_\infty$. Finally,</p>
<div class="math-display">$$\prod_{i=1}^nr_i^{-s}=L^{-s n(n+1)/2}\prod_{i=1}^nR_i^{-s}=L^{-s n(n+1)/2}\operatorname{Sweep}(A)^{-s}.$$</div>
<p>This proves the claim with $c_n=q^{n-1}(b/2)^nL^{-s n(n+1)/2}$. No independence between the mass events and the joining events was used. Conditional association is applied only after revealing the earlier increments.</p>

<a id="tag-2BBE" data-assertion="corollary" data-title="The power-law cutoff criterion yields the long-range multipoint lower bound"></a>
<p>Under the hypotheses of the <a href="/tag/YJ5E/">power-law cutoff criterion</a>, with $d/3&lt;\alpha&lt;d$, let $\tau_\beta(A)$ denote the full-model connection probability of a finite marked set $A\subset\mathbb Z^d$. For every fixed $n\geq2$,</p>
<div class="math-display">$$\tau_\beta(A)\succeq_n\operatorname{Sweep}(A)^{-(d-\alpha)/2}\asymp_n S(A)^{-(d-\alpha)/2}\qquad(|A|=n).$$</div>
<p>If the pair upper bound and higher-point product inequalities in <a href="/tag/C4A5/">C4A5</a> also hold with $\sigma=(d-\alpha)/2$, then $\tau_\beta(A)\asymp_n S(A)^{-(d-\alpha)/2}$. The first conclusion requires no pointwise two-point lower bound.</p>
<p><em>Proof.</em> The cutoff criterion gives $m_q(r)\asymp r^{\alpha+(q-1)\theta}$ for $q=1,2,3$, where $\theta=(d+\alpha)/2$, and mesoscopic negligibility. Its localization hypothesis includes the first two moments. These moment comparisons, initially stated for large $r$, extend to $r\geq1$ by adjusting constants: the cluster contains its root and is dominated on any bounded radius interval by the cluster at the interval's upper endpoint. Thus D6CQ supplies both local-mass estimates.</p>
<p>Couple the soft cutoffs by independent Poisson processes on the edges. The <a href="/tag/C4E9/">omitted-intensity row bound</a> bounds the added probability row from $r$ to $R$ by $Cr^{-\alpha}$. Together with $\chi_R\preceq R^\alpha$, this verifies JC24. For $p=d+\alpha$, an edge of length $\ell\leq Dr$ receives between $r$ and $2Dr$ the intensity</p>
<div class="math-display">$$\beta A\left[\bigl(\ell^{-p}-(2Dr)^{-p}\bigr)_+-\bigl(\ell^{-p}-r^{-p}\bigr)_+\right]\geq\beta A\bigl(D^{-p}-(2D)^{-p}\bigr)r^{-p}.$$</div>
<p>For $\ell\leq r$ subtract the two powers of the cutoff radii; for $r&lt;\ell\leq Dr$ the second positive part vanishes. The coefficient is positive. L5IG now gives the lower bound, and <a href="/tag/WDGK/">the sweep comparison</a> replaces sweep by $S$. C4A5 supplies the stated conditional upper bound.</p>
<p>This completes a conditional route to the lower bound. The assumptions of YJ5E—cutoff susceptibility order, weak localization and rooted damping—remain explicit. A two-point estimate alone is not the input to the lower-bound argument supplied here. For the more general kernels of <a href="https://arxiv.org/html/2508.18808v1">Critical LRP II</a>, Proposition II.5.9 uses the paper's weak-localization theory, and Lemma II.5.11 supplies the corresponding scale-persistence step. The argument above isolates those mechanisms with fixed conditioning thresholds and separated joining radii; it does not identify the full set of kernels satisfying the paper's localization hypotheses.</p>

## Source scope {#section-source}

<p>This supplies the general combinatorial and summation arguments. The finite-coordinate BK inequality is the input; the refinement into trivalent shapes, repeated-vertex convention and shape count are given explicitly here. The <a href="/tag/XLWI/">exponential-moment consequence</a> retains the root mean and the uniform susceptibility scale separately. Identifying finite susceptibility with the whole subcritical phase is a separate sharpness theorem.</p>


## Splitting at the first branch {#section-branch-recursion}

<p>The moment bound <a href="/tag/Y84V/">Y84V</a> also has a direct recursive proof. Let $I$ be a finite set of at least two labels, with positions $x_i$, and suppose a finite open edge set $F$ joins $o$ to every $x_i$. The positions need not be distinct. We seek a vertex $z$, a nontrivial split $I=A\sqcup B$, and three pairwise disjoint subsets of $F$ witnessing the connections from $o$ to $z$, from $z$ to all targets in $A$, and from $z$ to all targets in $B$.</p>
<p>Induct on $|F|$. If some $x_i=o$, take $z=o$, $A=\{i\}$ and empty witnesses for the first two connections. Otherwise delete all edges incident to $o$, obtaining $F'$. Every target is reachable in $F'$ from some neighbour of $o$: take a simple path from $o$ and remove its first edge. Choose one such neighbour $c$. If all targets lie in its $F'$-component, apply induction in $F'$ with root $c$, and add the edge $oc$ to the witness from the original root to the new branch point. That edge belongs to none of the other witnesses, since it was deleted in $F'$.</p>
<p>If targets lie in more than one $F'$-component, split them according to membership in the component of $c$ and take $z=o$. One witness uses that component's edges together with $oc$; the other uses the remaining edges of $F$. Each target outside the chosen component has a path from another neighbour of $o$ staying in a different component. The two witnesses are therefore edge-disjoint. The witness from $o$ to $z$ is empty. This proves the split without assuming that $F$ is a tree.</p>
<p>Any finite family of open connections has such a finite edge witness. Fix one label $i_0\in I$ and name the two parts so that $i_0\in A$. A union bound over branch points and splits, followed by BK twice, gives</p>
<div class="math-display">$$\begin{aligned}
&amp;\mathbb P(o\leftrightarrow x_i\text{ for all }i\in I)\\
&amp;\quad\leq\sum_z\tau(o,z)
\sum_{\substack{A\subsetneq I\\i_0\in A}}
\mathbb P(z\leftrightarrow x_i\text{ for all }i\in A)
\mathbb P(z\leftrightarrow x_i\text{ for all }i\in I\setminus A).
\end{aligned}$$</div>
<p>The three finite witnesses give the nested disjoint occurrence needed for the two BK applications. They may meet at vertices. The prescribed label chooses one orientation of each split; it is not an assumption of independence between the two connection events. Taking two labels recovers <a href="/tag/L82Q/">the three-point inequality</a>.</p>

## Summing the recursion {#section-moment-recursion}

<p>Write $H_m(o)=\mathbb E|K_o|^m$, with $H_0(o)=1$. Sum the preceding inequality over all ordered $m$-tuples of targets, taking $I=\{1,\ldots,m\}$ and $i_0=1$. For a fixed split $A\sqcup B=I$, the target coordinates in the two probability factors are disjoint sets of summation variables. Tonelli gives</p>
<div class="math-display">$$\sum_{x_1,\ldots,x_m}
\mathbb P(z\leftrightarrow x_i\text{ for all }i\in A)
\mathbb P(z\leftrightarrow x_i\text{ for all }i\in B)
=H_{|A|}(z)H_{|B|}(z).$$</div>
<p>Repetitions of target positions are allowed, so these are ordinary powers of cluster size, not falling factorials. No independence assertion about events in one configuration is used in this factorization. We obtain, for $m\geq2$,</p>
<div class="math-display">$$H_m(o)\leq\sum_z\tau(o,z)
\sum_{\substack{A\subsetneq\{1,\ldots,m\}\\1\in A}}
H_{|A|}(z)H_{m-|A|}(z).$$</div>
<p>Set $t_1=1$ and $t_m=(2m-3)!!$ for $m\geq2$. The coefficients satisfy</p>
<div class="math-display">$$t_m=\sum_{a=1}^{m-1}\binom{m-1}{a-1}t_a t_{m-a}.$$</div>
<p>To see this from <a href="/tag/SO5J/">the tree shapes</a>, distinguish the root leaf of a tree with $m$ other labelled leaves. Removing the adjacent branch vertex splits those labels into two nonempty parts. Designate the part containing label one as $A$. There are $\binom{m-1}{a-1}$ choices of a part of size $a$, and $t_a t_{m-a}$ choices for the two rooted subtrees. Gluing reverses this decomposition.</p>
<p>The source derives the same count algebraically from Catalan numbers. Writing $C_k$ for the $k$th Catalan number, it uses $(k+1)!C_k=2^k t_{k+1}$ and</p>
<div class="math-display">$$2\sum_{k=0}^n(k+1)C_kC_{n-k}=(n+2)C_{n+1}.$$</div>
<p>The latter identity follows by reflecting the sum through $k\mapsto n-k$ and adding: the two coefficients sum to $n+2$, after which the Catalan convolution applies. Substituting the factorial identity yields the displayed recursion for $t_m$. Thus both counts include $t_1=1$, as needed when one part consists of a single label.</p>
<p>Now suppose $\chi(z)\leq M&lt;\infty$ at every vertex. The case $m=1$ is $H_1(o)=\chi(o)$. Strong induction gives, for $1\leq a&lt;m$, $H_a(z)\leq t_a\chi(z)M^{2a-2}\leq t_aM^{2a-1}$. Every split therefore contributes at most $t_a t_{m-a}M^{2m-2}$. The coefficient identity and $\sum_z\tau(o,z)=\chi(o)$ yield</p>
<div class="math-display">$$H_m(o)\leq t_m\chi(o)M^{2m-2},$$</div>
<p>which proves Y84V directly. In particular the first two nontrivial bounds are $H_2(o)\leq\chi(o)M^2$ and $H_3(o)\leq3\chi(o)M^4$.</p>
<p>All tuple identities and the recursion hold as nonnegative extended sums, without finite moments. The source consequently allows any extended upper bound $M$. When $M=\infty$ and $m\geq2$, its conclusion is the trivial upper bound infinity, since a rooted bond cluster contains its root and $\chi(o)\geq1$. At $m=1$ the exponent is zero and the statement remains the susceptibility identity. The informative finite-moment conclusion still needs a finite uniform bound. Diagonal probabilities and endpoints of the profile impose no extra restriction.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-tree-moments/">21-contract inventory</a> records the branch decomposition, tuple factorization, combinatorial coefficient and induction. These modules supply the three-point bound and the all-moment estimate. They do not themselves export the full shape-indexed multipoint formula AFH6, the root-only counterexample HRS7, or the later continuum and gluing assertions.</p>


## The root-mean example in the source {#section-root-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-models/">source for HRS7</a> implements the construction above with component index $k\geq0$ and path size $2^{k+1}$. Its connection identities hold on the probability-one event where every path edge is open and every edge outside the host is closed. This simultaneous restriction uses countability.</p>
<p>Finite mean is established before replacing extended cluster cardinality by a real variable. The source's finite-cardinality function is zero on an infinite set, so that replacement is justified only after excluding infinite root clusters almost surely. The second-moment divergence then transfers to every positive exponential moment. Deterministic path edges and the infinite-degree root are part of the example; it does not change the moment bounds for transitive models or for models with uniformly bounded susceptibility.</p>


## What the shape interface proves {#section-shape-interface}

<p>The <a href="/coverage/sources/perclib-f51f639-interfaces/">multipoint interface</a> defines shapes by quotienting finite trivalent trees by isomorphisms that fix the leaf labels. It proves that there is one shape with two leaves and one with three. The general enumeration <a href="/tag/SO5J/">SO5J</a> and the inequality <a href="/tag/AFH6/">AFH6</a> remain separate proof obligations. The source defines a weight using a chosen representative; it does not yet prove that changing representatives leaves that weight unchanged.</p>
<p>The same file defines the recursive three-part distance and the sweep product, and proves that each equals $d(x,y)^2$ on a two-point set, with distinctness assumed for the sweep calculation. In a sweep rooted at $r$, the factor at $r$ is the diameter of the whole set. At a non-root vertex, the diameter is taken over that vertex, its parent and its descendants. The source includes the vertex itself by allowing zero iterations of the parent map. The pair calculations verify these conventions; the general geometric comparison and its multipoint consequences require additional proofs.</p>


## Spread and insertion distances {#section-spread}

<p>The spread of a finite metric space is the least product of edge lengths among its spanning trees. This completes the comparison with the sweep used in §II.3.1 of <a href="https://arxiv.org/html/2508.18808v1">Long-range II</a>, without relying on the displayed insertion product in that proof.</p>

<a id="tag-0VKF" data-assertion="proposition" data-title="Spread, insertion distances and sweep with cardinality constants"></a>
<p>Let $(A,d)$ be a finite metric space with $n\geq2$, and define</p>
<div class="math-display">$$\operatorname{Spread}_d(A)=\min_T\prod_{e\in T}d(e).$$</div>
<p>For every enumeration $a_1,\ldots,a_n$ of its distinct points, put $P_d=\prod_{i=2}^n d(a_i,\{a_1,\ldots,a_{i-1}\})$. Then</p>
<div class="math-display">$$\operatorname{Spread}_d(A)\leq P_d\leq(n-1)^{n-1}\operatorname{Spread}_d(A),$$</div>
<div class="math-display">$$\operatorname{diam}_d(A)\operatorname{Spread}_d(A)
\leq\operatorname{Sweep}_d(A)
\leq(n-1)^n\operatorname{diam}_d(A)\operatorname{Spread}_d(A).$$</div>
<p>In particular, insertion products from any two enumerations are comparable with constants depending only on $n$.</p>
<p><em>Proof.</em> Joining each $a_i$, $i\geq2$, to a nearest earlier point gives a spanning tree with product $P_d$, proving the first lower bound. Every nonroot sweep factor contains its parent edge, and the root factor is the full diameter. Minimizing over rooted trees gives the second lower bound.</p>
<p>For the upper bounds, take the ultrametric $u$ constructed from a minimum-product tree in <a href="/tag/WDGK/">WDGK</a>. It satisfies $u\leq d\leq(n-1)u$. In an ultrametric, $P_u=\operatorname{Spread}_u(A)$ for every enumeration: at threshold $t$, the edge from a point to its nearest predecessor has length at most $t$ precisely when its $t$-equivalence class has already appeared. Thus the insertion tree has $n-c_t$ edges of length at most $t$, where $c_t$ is the number of classes. These are exactly the edge counts of a minimum-product tree, obtained by joining each class internally before joining distinct classes. Equality of the finite edge-length multisets gives equality of their products.</p>
<p>It follows that $P_d\leq(n-1)^{n-1}P_u=(n-1)^{n-1}\operatorname{Spread}_u(A)\leq(n-1)^{n-1}\operatorname{Spread}_d(A)$. Finally, monotonicity of every sweep factor and <a href="/tag/ESZG/">the ultrametric identity</a> give</p>
<div class="math-display">$$\operatorname{Sweep}_d(A)\leq(n-1)^n\operatorname{Sweep}_u(A)
=(n-1)^n\operatorname{diam}_u(A)\operatorname{Spread}_u(A)
\leq(n-1)^n\operatorname{diam}_d(A)\operatorname{Spread}_d(A).$$</div>
<p>The distance in an insertion product is always to the <em>earlier</em> points. Including $a_i$ makes that distance zero, whereas the spread of distinct points is positive.</p>

## The geometric source formulas {#section-geometric-source}

<p>The <a href="/coverage/sources/long-range-II-2508.18808v1/">Part II reading map</a> now separates the probability inequality, deterministic geometry and covariance argument in §II.3. The higher-order probability inequality in Theorem II.3.1 uses BK for coupled decision-tree explorations. Ordinary disjoint occurrence in one configuration does not replace that input; the conditional upper bounds above retain it.</p>
<p>For the geometric induction, write $s=(d-2+\eta)/2&gt;0$. If the three pairwise-union probabilities are bounded by constants times their sweeps to power $-s$, their product followed by a square root has exponent $-s/2$ on the product of the three sweeps. Thus <a href="/tag/C4A5/">C4A5</a> and <a href="/tag/WDGK/">WDGK</a> give the intended power $-s$ on the sweep of the full set. The intermediate display in Corollary II.3.8 instead gives the raw product exponent $-s$; the <a href="/errata/hutchcroft-lrp-2/">provisional correction</a> restores the square root. For $s\leq0$ on distinct lattice points, the claimed upper bound is already implied by $\tau(A)\leq1$ and $\operatorname{Sweep}(A)\geq1$; no reversal of a maximum and minimum is needed.</p>
<p>For covariance, use the standard inversion $I(x)=x/\|x\|^2$. If $v=x/\|x\|$, then $DI(x)=\|x\|^{-2}(\mathrm{Id}-2vv^{\mathsf T})$, so $\det DI(x)=-\|x\|^{-2d}$ and its local length factor is $\|x\|^{-2}$. In the complex plane this map is $z\mapsto1/\overline z$. Composing with $x\mapsto-x$ instead gives determinant $(-1)^{d-1}\|x\|^{-2d}$ and planar expression $-1/\overline z$. The source mixes these signed formulas. All have the same absolute Jacobian and distance scaling, so <a href="/tag/9YE6/">the recursive covariance proof</a> is unaffected. For a Möbius transformation with finite marked points and finite images, the distance identity justified in <a href="/tag/N76U/">N76U</a> applies directly, including when an intermediate factorization passes through infinity.</p>


## The regular multigraph expansion {#section-regular-multigraphs}

<p>Repeated use of the three-part inequality produces a finite sum of pair-probability monomials. The regular degree in (II.3.3) is forced by the fact that each marked point belongs to exactly two of the three pairwise unions.</p>

<a id="tag-L3HA" data-assertion="proposition" data-title="Three-part product inequalities yield the regular multigraph bound"></a>
<p>Let $A$ have $n\geq2$ elements, and let $t(B)$ be a finite nonnegative number for every $B\subseteq A$ with $|B|\geq2$. Assume, for $|B|\geq3$,</p>
<div class="math-display">$$t(B)^2\leq K_{|B|}\max_{B=B_1\sqcup B_2\sqcup B_3}
\prod_{i&lt;j}t(B_i\cup B_j),$$</div>
<p>where all parts are nonempty and each $K_m&gt;0$. Put $D_n=2^{n-2}$ and let $\mathcal G_n(A)$ be the set of connected loopless multigraphs on $A$ having degree $D_n$ at every vertex. Parallel edges are allowed. If $q_{xy}$ is the multiplicity of the edge $\{x,y\}$ in $Q$, then</p>
<div class="math-display">$$t(A)^{D_n}\leq C_n\sum_{Q\in\mathcal G_n(A)}
\prod_{\{x,y\}\subseteq A}t(\{x,y\})^{q_{xy}},$$</div>
<p>where $C_n$ depends only on $n$ and $K_3,\ldots,K_n$. Factors of exponent zero equal one, including when their base is zero. Equivalently, up to constants with the same dependencies, the upper bound on $t(A)$ is either the $D_n$th root of this sum or</p>
<div class="math-display">$$\sum_{Q\in\mathcal G_n(A)}
\prod_{\{x,y\}\subseteq A}t(\{x,y\})^{q_{xy}/D_n}.$$</div>

<p><em>Proof.</em> For $n=2$, the only graph is the single edge, so the assertion is an equality. Suppose $n\geq3$ and the result holds on smaller sets. Raise the assumed three-part bound to power $D_n/2$. A pairwise union $B=A_i\cup A_j$ has size $m\leq n-1$, and</p>
<div class="math-display">$$\frac{D_n}{2}=D_m\,2^{n-m-1}.$$</div>
<p>The second factor is a positive integer. Apply induction to $t(B)^{D_m}$, raise the resulting finite sum to that integer power and expand it. Each term is the pair-weight monomial of a union of $2^{n-m-1}$ graphs on $B$, each of degree $D_m$. Every vertex of $B$ therefore receives degree $D_n/2$ from this pairwise union.</p>
<p>Now multiply the three expanded sums. Each vertex lies in exactly two pairwise unions, so every resulting graph on $A$ has degree $D_n$. It is connected: each pairwise union carries a connected graph, and these three vertex sets intersect pairwise in the nonempty parts of the partition. No loops are introduced. Thus every monomial belongs to a graph in $\mathcal G_n(A)$. There are only finitely many partitions and choices of constituent graphs, with their numbers depending only on $n$. Replace the maximum by their sum and bound the multiplicities of identical resulting graphs by this finite number. Absorbing the inductive constants gives the stated $C_n$.</p>
<p>Finally, for $M$ nonnegative terms and $D\geq1$,</p>
<div class="math-display">$$\left(\sum_{j=1}^M w_j\right)^{1/D}
\leq\sum_{j=1}^M w_j^{1/D}
\leq M^{1-1/D}\left(\sum_{j=1}^M w_j\right)^{1/D}.$$</div>
<p>The first inequality follows by subadditivity of the power $1/D$ and the second by Hölder. Apply this with the finite number of graphs in $\mathcal G_n(A)$. No positive pair probability or division by a connection probability was required.</p>
<p>For percolation, take $t(B)$ to be the probability that all points of $B$ are connected. This proves the algebraic implication in (II.3.3) once Theorem II.3.1 is supplied. It does not prove that decision-tree inequality. For $n=3$ the only graph is the triangle; for $n=4$ the degree is four, consistent with the four-point matching expression above.</p>


## Summing the multigraph bound {#section-multigraph-moments}

<a id="tag-1EWL" data-assertion="proposition" data-title="Rapid two-point decay and higher-point inequalities control volume and spatial moments"></a>
<p>Consider translation-invariant bond percolation laws on $\mathbb Z^d$, indexed by $r\geq1$, and write $\tau_r(A)$ for the probability that all points of a finite set $A$ lie in one cluster. Fix $0&lt;\alpha\leq d$ and put $\theta=(d+\alpha)/2$. Suppose the three-part inequalities in <a href="/tag/L3HA/">L3HA</a> hold with constants depending only on the number of marked points, uniformly in $r$. Suppose also that</p>
<div class="math-display">$$\tau_r(0,x)\leq C\|x\|_\infty^{-d+\alpha}h(\|x\|_\infty/r)\qquad(x\ne0),$$</div>
<p>where $h:(0,\infty)\to(0,1]$ is nonincreasing and $\sup_{s\geq1}s^Nh(s)&lt;\infty$ for every $N&gt;0$. If $X=|K_0|$, then, for every integer $p\geq1$,</p>
<div class="math-display">$$M_p(r):=\mathbb E_rX^p\leq C_p r^{\alpha+(p-1)\theta},\qquad
W_p(r):=\mathbb E_r\left[X^{p-1}\sum_{x\in K_0}\|x\|_\infty^2\right]\leq C_p r^{2+\alpha+(p-1)\theta}.$$</div>
<p>Moreover $M_3(r)\leq C r^\theta M_2(r)$. None of these conclusions assumes finiteness of the moments in advance.</p>

<p><em>Proof.</em> Shell summation, treating $x=0$ separately, gives for each $0&lt;\eta\leq1$</p>
<div class="math-display">$$S_\eta:=\sum_x\tau_r(0,x)^\eta\leq C_\eta r^{d-\eta(d-\alpha)},\qquad
T_\eta:=\sum_x\|x\|_\infty^2\tau_r(0,x)^\eta\leq C_\eta r^{2+d-\eta(d-\alpha)}.$$</div>
<p>Indeed, inside radius $r$ the relevant powers have positive radial exponents, since $d-\eta(d-\alpha)\geq\alpha&gt;0$; outside that radius choose a sufficiently large power in the decay of $h$. The same calculation applies when $\alpha=d$.</p>
<p>Fix a connected loopless $D$-regular multigraph $Q$ on $k\geq2$ labels, with $D=2^{k-2}$, and write</p>
<div class="math-display">$$F_Q(x_1,\ldots,x_k)=\prod_{i&lt;j}\tau_r(x_i,x_j)^{q_{ij}/D}.$$</div>
<p>Enumerate its vertices starting at the pinned vertex so that every initial segment is connected. Then $Q_\ell=\sum_{i&lt;\ell}q_{i\ell}$ satisfies $1\leq Q_\ell\leq D$ for $\ell\geq2$. Eliminate the variables in reverse order. Hölder and translation invariance give, with $\eta_\ell=Q_\ell/D$,</p>
<div class="math-display">$$\sum_z\prod_{i&lt;\ell}\tau_r(x_i,z)^{q_{i\ell}/D}
\leq\prod_{i:q_{i\ell}&gt;0}\left(\sum_z\tau_r(x_i,z)^{\eta_\ell}\right)^{q_{i\ell}/Q_\ell}
=S_{\eta_\ell}.$$</div>
<p>Each edge is counted once in $\sum_{\ell=2}^kQ_\ell=kD/2$. Consequently</p>
<div class="math-display">$$\sum_{x_2,\ldots,x_k}F_Q(0,x_2,\ldots,x_k)
\leq C_k r^{d(k-1)-(d-\alpha)k/2}
=C_k r^{\alpha+(k-2)\theta}.$$</div>
<p>The connected ordering matters: arbitrary labels can give $Q_\ell=0$, for which $S_0$ is infinite.</p>
<p>For a spatial weight $\|x_1-x_j\|_\infty^2$, take a simple path in $Q$ from $1$ to $j$. The triangle inequality and Cauchy–Schwarz bound this weight by $k-1$ times the sum of squared edge lengths along the path. For each resulting edge $uv$, translate the whole tuple to pin $x_u=0$, label its other endpoint second, and extend this edge to a connected ordering. Translation is a bijection of rooted tuples: the inverse subtracts the coordinate of the formerly pinned vertex. Eliminate all vertices except these first two as before, and use $T_{q_{uv}/D}$ for the last sum. This gives the same power of $r$ with an additional factor $r^2$. It also explains why one cannot simply assume the originally marked pair is an edge of $Q$.</p>
<p>Expand $M_p$ as the sum of $(p+1)$-point connection probabilities. First partition the labels according to which positions coincide. For a pattern with $k$ distinct positions, apply L3HA on those $k$ points, and then drop the distinctness restriction when summing each nonnegative graph monomial. The bounds just proved apply. Patterns with $k=1$ contribute one to the unweighted sum and zero to the weighted sum; all other patterns have $k\leq p+1$. Since $r\geq1$ and $\theta&gt;0$, their powers are bounded by the asserted one. There are finitely many patterns. The identical argument, with one marked displacement, proves the bound on $W_p$. All expansions are justified by Tonelli; in particular the resulting finite bounds establish moment finiteness.</p>
<p>For the third-moment ratio use the four-point inequality before expanding it into pair weights. It bounds the four-point probability by a constant times the sum, over permutations of the four labels, of</p>
<div class="math-display">$$\sqrt{\tau_r(x_1,x_2)\tau_r(x_1,x_3,x_4)\tau_r(x_2,x_3,x_4)}.$$</div>
<p>This also holds for repeated positions: put a coincident pair first, so that one term equals the original connection probability. After summing rooted tuples, every permutation has the same sum by relabelling and translating its first position to zero. Cauchy–Schwarz in the last two variables therefore gives</p>
<div class="math-display">$$M_3\leq C\sum_x\sqrt{\tau_r(0,x)}
\sqrt{\sum_{y,z}\tau_r(0,y,z)\sum_{y,z}\tau_r(x,y,z)}
=C M_2 S_{1/2}\leq C r^\theta M_2.$$</div>
<p>The higher-order probability inequality remains a hypothesis. The summation argument alone is not a proof of the decision-tree inequality.</p>


## Connected mass in two separated windows {#section-separated-window-mass}

<a id="tag-9ZEL" data-assertion="proposition" data-title="A four-point bound controls already-connected mass in separated windows"></a>
<p>Let $d\geq1$ and $0&lt;\alpha\leq d$. For each $r\geq1$, consider independent bond percolation on $\mathbb Z^d$. Suppose its two-point function satisfies, uniformly over distinct $u,v$ and $r$,</p>
<div class="math-display">$$\tau_r(u,v)\leq C\|u-v\|_\infty^{-d+\alpha}h(\|u-v\|_\infty/r),$$</div>
<p>where $h:(0,\infty)\to(0,1]$ is nonincreasing and decays faster than every power. Assume also the four-point inequality in the conclusion of <a href="/tag/2GTM/">2GTM</a> for every four distinct marked vertices, with a uniform constant. Then there are $C'&lt;\infty$ and a nonincreasing, faster-than-any-power function $H:(0,\infty)\to(0,1]$ such that, for $R=\|x-y\|_\infty\geq4r$,</p>
<div class="math-display">$$\mathbb E_r\left[|K_x\cap B_r(x)|\,|K_y\cap B_r(y)|\mathbf1_{\{x\leftrightarrow y\}}\right]
\leq C'r^{d+\alpha}R^{-d+\alpha}H(R/r).$$</div>
<p>The second observation window is centered at $y$. Connections use the full cutoff configuration, not the induced graphs on the windows.</p>
<p><em>Proof.</em> Put $\gamma=(d-\alpha)/2$, and take $a\in B_r(x)$ and $b\in B_r(y)$. Write $u=1\vee\|x-a\|_\infty$ and $v=1\vee\|y-b\|_\infty$. All four distances between the two windows lie between $R/2$ and $3R/2$. The short-pair probabilities are at most $Cu^{-2\gamma}$ and $Cv^{-2\gamma}$, while every cross-pair probability is at most $CR^{-2\gamma}h(R/(2r))$.</p>
<p>For four distinct points, the product of the six pair probabilities is therefore at most $Cu^{-2\gamma}v^{-2\gamma}R^{-8\gamma}h(R/(2r))^4$. Each of the three matching products is at most $Cu^{-2\gamma}v^{-2\gamma}$: for a cross matching use $u,v\leq r\leq R$. Taking the fourth root in 2GTM gives</p>
<div class="math-display">$$\mathbb P_r(x,a,y,b\text{ lie in one cluster})
\leq C u^{-\gamma}v^{-\gamma}R^{-2\gamma}h(R/(2r)).$$</div>
<p>The windows are disjoint, so repetitions can only be $a=x$ or $b=y$. With one repetition the same estimate follows from the <a href="/tag/87RB/">three-point product inequality</a>, using its two cross-pair factors. With both repetitions it is the assumed two-point estimate. Thus the bound covers every summand without assigning a negative power to zero distance.</p>
<p>Sum over the two windows. Since $0\leq\gamma&lt;d$, lattice shell counting gives $\sum_{z\in B_r}(1\vee\|z\|_\infty)^{-\gamma}\leq C r^{d-\gamma}$. The product of the sums is $O(r^{d+\alpha})$, proving the claim with $H(t)=h(t/2)$. No lower two-point bound is used.</p>
<p>This is the separated-window estimate needed in Part II, Lemma II.6.5. Its printed statement uses $B_r(x)$ twice, whereas its proof and application use the two separate centers. The <a href="/errata/hutchcroft-lrp-2/#two-point-joining-windows">provisional source entry</a> records that mismatch and the small-radius qualification in the subsequent joining argument. The four-point inequality remains an explicit probability input; it is not inferred from ordinary BK alone.</p>


## Retaining one three-point connection {#section-mixed-third-moment}

<a id="tag-9WYX" data-assertion="proposition" data-title="A mixed tree-graph bound retains the second cluster moment"></a>
<p>For independent bonds on a countable vertex set, suppose $M=\sup_x\chi_x&lt;\infty$. Then</p>
<div class="math-display">$$\mathbb E|K_o|^3\leq3M^2\mathbb E|K_o|^2.$$</div>
<p>In particular, transitivity gives $m_3\leq3\chi^2m_2$.</p>
<p><em>Proof.</em> A finite tree connecting four marked vertices $o,x_1,x_2,x_3$ has a branch position $z$ and a choice of $i\in\{1,2,3\}$ such that the three events</p>
<div class="math-display">$$\{o,x_i,z\text{ lie in one cluster}\},\qquad\{z\leftrightarrow x_j\},\qquad\{z\leftrightarrow x_k\},\qquad\{i,j,k\}=\{1,2,3\},$$</div>
<p>have pairwise edge-disjoint witnesses. Indeed, in the four-leaf tree of <a href="/tag/AFH6/">the multipoint construction</a>, choose the branch adjacent to the pair of leaves on the side not containing $o$. The remaining subtree connects $o,x_i,z$. Repeated marked positions and degenerate branches give empty paths, so this construction also covers coincidences. Taking a union over $i,z$ and applying BK to the three increasing events yields</p>
<div class="math-display">$$\mathbb P(o,x_1,x_2,x_3\text{ lie in one cluster})
\leq\sum_{i=1}^3\sum_z\mathbb P(o,x_i,z\text{ lie in one cluster})\tau(z,x_j)\tau(z,x_k).$$</div>
<p>Sum over the three marked positions. The two pair factors each have row sum at most $M$, while the remaining sum over $x_i,z$ is $\mathbb E|K_o|^2$. Tonelli gives the claim. This leaves a genuine three-point probability intact, rather than replacing it by its tree upper bound; that distinction supplies the mixed moment needed by the good-scale argument.</p>

## A mixed moment in a spatial window {#section-gladkov-window}

<a id="tag-BIXQ" data-assertion="proposition" data-title="The three-point product inequality bounds a mixed window moment"></a>
<p>For a transitive countable independent bond model with finite susceptibility $\chi$, every finite vertex set $W$ and every root $x$ satisfy</p>
<div class="math-display">$$\mathbb E[|K_x|\,|K_x\cap W|]\leq2^{3/2}\chi\sqrt{|W|\,\mathbb E|K_x\cap W|}.$$</div>
<p><em>Proof.</em> Expand the product as a sum over $y$ and $z\in W$. The <a href="/tag/87RB/">three-point product inequality</a>, including its repeated-vertex cases, gives</p>
<div class="math-display">$$\begin{aligned}
\mathbb E[|K_x|\,|K_x\cap W|]
&\leq\sqrt8\sum_{z\in W}\sqrt{\tau(x,z)}\sum_y\sqrt{\tau(x,y)\tau(y,z)}\\
&\leq\sqrt8\chi\sum_{z\in W}\sqrt{\tau(x,z)}
\leq\sqrt8\chi\sqrt{|W|\sum_{z\in W}\tau(x,z)}.
\end{aligned}$$</div>
<p>The first Cauchy–Schwarz inequality uses symmetry and the common row sum $\chi$; the second is over the finite set $W$. The empty window gives zero on both sides. This proves (III.3.1) in the transitive setting used there. Gladkov's finite three-point theorem remains the cited input of 87RB; this summation does not prove that theorem.</p>

## The finite three-point input is supplied {#section-finite-gladkov-proof}

<p>The finite theorem used in <a href="/tag/87RB/">87RB</a> is now proved in <a href="/tag/C7UK/">C7UK</a>. The argument keeps overlaps only on independently resampled coordinates, proves the needed adaptive BK inequality, and constructs witnesses from a stopped DFS path. Thus it also explains precisely why <a href="/tag/5PHR/">the independent-continuation counterexample</a> is compatible with the correct proof. The countable extension and repeated-vertex cases in 87RB are unchanged.</p>

## The higher-order probability input is supplied {#section-higher-gladkov-proof}

<p><a href="/tag/5BQO/">5BQO</a> now proves the higher-order Gladkov inequality on countable independent bond models. Its stopped DFS leaves one mark unvisited; the discovery tree splits into two connected subtrees with nonempty marked parts, and the two continuations provide mixed witnesses. This supplies the probability premise in <a href="/tag/2GTM/">the four-point matching estimate</a> and <a href="/tag/C4A5/">the recursive geometric bound</a>. The smaller coefficient in the completed proof also gives <a href="/tag/MTVN/">a sharper four-point prefactor</a>, while the earlier constants and statements are preserved.</p>


## First-connection weights in a radial cutoff {#section-radial-first-connection}

<a id="tag-FMUH" data-assertion="proposition" data-title="Stopped spatial moments have an exact radial merger formula"></a>
<p>Retain the normalized radial model of <a href="/tag/C0OR/">C0OR</a>, at intensity $\beta_c$, and couple its cutoffs by independent exponential edge clocks with cumulative intensity $k_r(a,b)=\beta_c J_r(a,b)$. Write $K_y^r$ for its clusters. Fix $x\neq0$, let $R(x)=\inf\{r:0\leftrightarrow_r x\}$, and put</p>
<div class="math-display">$$W_p(C)=\sum_{y\in C}\|y\|^p,\qquad
F_{q,p}(t,x)=\mathbb E\left[\mathbf1_{\{R(x)\leq t\}}R(x)^{-q}W_p(K_0^{R(x)})\right]$$</div>
<p>for integers $p\geq0$ and real $q\geq0$. Use $\|0\|^0=1$ and set the payoff to zero when the first connection has not occurred. Let $\ell=\min_{z\neq0}\|z\|&gt;0$ and choose $0&lt;r_0&lt;\ell$. For every finite $t\geq r_0$,</p>
<div class="math-display">$$\begin{aligned}
F_{q,p}(t,x)=\beta_c\int_{r_0}^t |j'(s)|s^{-q}
\mathbb E\left[\mathbf1_{\{0\nleftrightarrow_s x\}}
W_p(K_0^s\cup K_x^s)
\sum_{a\in K_0^s}\sum_{b\in K_x^s}\mathbf1_{\{\|a-b\|\leq s\}}\right]ds.
\end{aligned}$$</div>
<p>All terms are finite. In particular, $F_{q,p}(\,cdot\,,x)$ is locally absolutely continuous and its derivative is the displayed integrand almost everywhere. The two stopped quantities used below are $\mathfrak S_t(x;p)=F_{0,p}(t,x)$ and $\mathfrak R_t(x;p)=F_{\alpha,p}(t,x)$.</p>
<p><em>Proof.</em> The kernel vanishes below $\ell$, so no two distinct vertices connect there. In a finite induced box containing $0,x$, apply <a href="/tag/88ZH/">the first-connection identity</a> to $g(s,C)=s^{-q}W_p(C)$, starting at $r_0$. The edge rate is</p>
<div class="math-display">$$a_{\{a,b\}}(s)=\beta_c|j'(s)|\mathbf1_{\{\|a-b\|\leq s\}}\qquad\text{for almost every }s.$$</div>
<p>Indeed $J_s(a,b)=(j(\|a-b\|)-j(s))_+$; monotonicity and continuous differentiability of $j$ give this derivative, including its flat intervals.</p>
<p>To pass to the lattice, fix a terminal radius $T\geq t$. By <a href="/tag/DR1W/">finite-cutoff moment finiteness</a>, the terminal clusters of $0$ and $x$ are almost surely finite and have moments of every order. Once a box contains both terminal vertex sets, their entire histories through $T$ agree with the full-model histories: every earlier connecting path lies in the corresponding terminal cluster. Thus the first-connection payoff and the integrand eventually stabilize, almost surely. The distinctness indicator is not monotone under exhaustion, so this passage requires domination.</p>
<p>Put $X_0=|K_0^T|$ and $X_x=|K_x^T|$. Every open edge at radius at most $T$ has length at most $T$. A simple path inside a terminal cluster therefore gives</p>
<div class="math-display">$$W_p(K_0^s)\leq T^pX_0^{p+1},\qquad
W_p(K_x^s)\leq(\|x\|+T)^pX_x^{p+1}\qquad(s\leq T).$$</div>
<p>The crossing-pair count is at most $X_0X_x$. On $[r_0,T]$ the deterministic factors $|j'(s)|s^{-q}$ are bounded. Cauchy–Schwarz and the terminal moment bounds make the resulting dominating random variable integrable, uniformly over boxes and times. The stopped payoff is bounded by $r_0^{-q}T^pX_0^{p+1}$. Dominated convergence on the probability space and on its product with $[r_0,T]$ proves the integral identity. Local absolute continuity follows from the same integrable bound.</p>
<p>This argument starts below the smallest nonzero lattice distance and does not require that distance to be one. It supplies the exact derivative underlying (III.5.3)–(III.5.6); quantitative estimates for that derivative are additional steps.</p>

## From the merger cluster to the terminal cluster {#section-radial-stopped-growth}

<a id="tag-JDX7" data-assertion="theorem" data-title="Stopped spatial moments control the weighted three-point sum"></a>
<p>In the radial model of <a href="/tag/FMUH/">FMUH</a>, define</p>
<div class="math-display">$$U_j(t)=\mathbb E_t\sum_{z\in K_0}(t+\|z\|)^j\qquad(j\geq0).$$</div>
<p>There is a finite constant $C$, depending only on the model, such that for every finite $t\geq\ell$, $x\neq0$ and integer $p\geq0$,</p>
<div class="math-display">$$\mathbb E_t\left[\mathbf1_{\{0\leftrightarrow x\}}W_p(K_0)\right]
\leq\mathfrak S_t(x;p)
+C\sum_{k=0}^p\binom pk\mathfrak R_t(x;k)U_{p-k}(t).$$</div>
<p>All the expectations are finite. No hydrodynamic limit, spatial moment asymptotic or dimension restriction beyond C0OR is needed for this inequality.</p>
<p><em>Proof.</em> The <a href="/tag/NE2Q/">omitted-row estimate</a> at modification parameter zero gives, for large $s$,</p>
<div class="math-display">$$\sum_{z\neq0}\bigl(\beta_cJ(0,z)-k_s(0,z)\bigr)\leq Cs^{-\alpha}.$$</div>
<p>Enlarging $C$ extends this to every $s\geq\ell$: on a bounded interval the left side is at most the finite row $\beta_c\sum_{z\neq0}J(0,z)$. Consequently, for $\ell\leq s\leq t$ and every $a$,</p>
<div class="math-display">$$\sum_{b\neq a}(k_t(a,b)-k_s(a,b))\leq Cs^{-\alpha}.$$</div>
<p>Work first in a finite induced box containing $0,x$. On the event of connection by $t$, write $R$ for its first connection radius and $H$ for the root component then. Apply <a href="/tag/DTOX/">the stopped weighted growth bound</a> with weight $w(z)=\|z\|^p$. A boundary edge with a nonzero intensity increment has $\|a-b\|\leq t$. For any vertex $z$ in its exterior component, the triangle inequality and binomial formula give</p>
<div class="math-display">$$\|z\|^p\leq(\|a\|+t+\|z-b\|)^p
=\sum_{k=0}^p\binom pk\|a\|^k(t+\|z-b\|)^{p-k}.$$</div>
<p>Adding back the deleted vertices and all vertices outside the finite box can only enlarge the exterior component. Translation by $-b$ then bounds its expected last factor by $U_{p-k}(t)$ in the full cutoff law. Sum over boundary edges and use the preceding row bound at $s=R$. Conditional on the stopped history, the terminal weighted volume is at most</p>
<div class="math-display">$$W_p(H)+CR^{-\alpha}\sum_{k=0}^p\binom pk W_k(H)U_{p-k}(t).$$</div>
<p>Multiply by the event of connection by $t$ and average. This gives the desired inequality with the finite-box stopped quantities on the right and the full-model $U_j(t)$. Finally exhaust the lattice. The terminal cluster at $t$ is finite almost surely, so the stopped histories stabilize whenever connection has occurred. The bounded-jump moment estimates in FMUH dominate each stopped term and the terminal weighted volume; also $R\geq\ell$. Dominated convergence gives the result. The same estimates prove finiteness of every $U_j(t)$.</p>
<p>This is the stopped-growth estimate (III.5.7). It separates the weighted mass already present at first connection from the mass acquired later. To deduce the averaged three-point bound in Lemma III.5.2, one still needs the spatial mixed-moment estimates retaining $V_r=m_2(r)/\chi(r)^3$, rapid spatial tails, and the corresponding bounds on $\mathfrak R$ and $\mathfrak S$. The crude multigraph estimate <a href="/tag/1EWL/">1EWL</a> does not supply the missing vertex factor. No such asymptotic conclusion is asserted here.</p>


## A common rapid tail for weighted cluster sums {#section-rapid-weighted-tail}

<a id="tag-3M2Y" data-assertion="proposition" data-title="Mixed spatial moments give a positive decreasing rapid-tail envelope"></a>
<p>Under the hypotheses of <a href="/tag/AR3F/">AR3F</a> for a fixed integer $n\geq1$, fix an integer $p\geq0$. There are a finite constant $C_{n,p}$ and a nonincreasing function $h_{n,p}:(0,\infty)\to(0,1]$ such that $\lambda^q h_{n,p}(\lambda)\to0$ as $\lambda\to\infty$ for every $q\geq0$, and</p>
<div class="math-display">$$\mathbb E_r\left[\sum_{\substack{x_1\in K_0\setminus\Lambda_{\lambda r}\\x_2,\ldots,x_n\in K_0}}
\prod_{i=1}^n\|x_i\|^{p_i}\right]
\leq C_{n,p}V_r^{n-1}r^{(2n-1)\alpha+p}h_{n,p}(\lambda)$$</div>
<p>for every $r\geq1$, $\lambda&gt;0$ and sequence of nonnegative integers $p_1,\ldots,p_n$ with sum $p$. Here $\Lambda_s=\{z:\|z\|\leq s\}$; when $n=1$ there are no further marked vertices.</p>
<p><em>Proof.</em> For every integer $k\geq0$,</p>
<div class="math-display">$$\mathbf1_{\{\|x_1\|&gt;\lambda r\}}\leq(\lambda r)^{-k}\|x_1\|^k.$$</div>
<p>Apply AR3F with the first degree increased by $k$. After division by $B_{n,p}(r)=V_r^{n-1}r^{(2n-1)\alpha+p}$, the left side is at most $C_{n,p,k}\lambda^{-k}$. The bound with $k=0$ is uniform in $\lambda$.</p>
<p>Let $F(\lambda)$ be the supremum of these normalized expectations over $r\geq1$ and all degree assignments of total $p$. It is nonnegative and nonincreasing, and satisfies $F(\lambda)\leq C_{n,p,k}\lambda^{-k}$ for every integer $k\geq0$. Set $D=\max\{1,C_{n,p,0}\}$ and</p>
<div class="math-display">$$h_{n,p}(\lambda)=\frac12\left(e^{-\lambda}+\frac{F(\lambda)}D\right).$$</div>
<p>This is positive, nonincreasing and at most one. For every real $q\geq0$, choose an integer $k&gt;q$ to see that $\lambda^q h_{n,p}(\lambda)\to0$. Also $F\leq2Dh_{n,p}$, proving the bound after enlarging its constant. Positivity is supplied by the exponential term; an infimum of polynomial bounds alone could vanish.</p>
<p>Setting $p_1=0$ gives the form used in (III.5.2):</p>
<div class="math-display">$$\mathbb E_r\left[|K_0\setminus\Lambda_{\lambda r}|
\sum_{x_2,\ldots,x_n\in K_0}\prod_{i=2}^n\|x_i\|^{p_i}\right]
\leq C_{n,p}V_r^{n-1}r^{(2n-1)\alpha+p}h_{n,p}(\lambda).$$</div>
<p>The product starts at two because the first marked vertex has already been counted by the outside volume; the <a href="/errata/hutchcroft-lrp-3/#weighted-tail-product-index">provisional source erratum</a> records the printed mismatch. For $n=1,p=0$, empty products and the sum over no further vertices are one, giving a rapid tail for the first spatial moment with no additional volume-moment premise. For higher $n$, the volume input of AR3F remains explicit.</p>


## Retaining several three-point factors {#section-generalized-tree-moments}

<a id="tag-65MV" data-assertion="theorem" data-title="Independent internal stars retain second moments in the tree-graph bound"></a>
<p>Consider a countable independent bond model whose probability-preserving automorphisms act transitively on the vertices. Suppose $\chi=\mathbb E|K_o|&lt;\infty$, and write $m_j=\mathbb E|K_o|^j$. For integers $p\geq2$ and $0\leq k\leq\lceil(p-1)/2\rceil$,</p>
<div class="math-display">$$m_p\leq(2p-3)!!\,m_2^k\chi^{2p-1-3k}.$$</div>
<p>In particular, $m_6\leq945m_2^2\chi^5$.</p>
<p><em>Proof.</em> Use the finite tree witnesses of <a href="/tag/AFH6/">AFH6</a> for the root and $p$ labelled marked vertices. Each resulting trivalent tree has $p-1$ internal vertices and $2p-1$ edges, and there are $(2p-3)!!$ shapes. The subgraph on its internal vertices is a tree, so one of its two bipartite classes contains at least $\lceil(p-1)/2\rceil$ vertices. Select $k$ of them. No two selected vertices are adjacent; hence their three-edge stars are pairwise edge-disjoint, although two stars may share an unselected endpoint.</p>
<p>For a fixed shape, retain the positions of its leaves and unselected internal vertices. Each selected star supplies a connection of its three neighbouring positions. Its centre need no longer be specified or summed over. The remaining $2p-1-3k$ edges supply pair connections. The original witness paths give disjoint edge witnesses for all these events, so BK bounds their joint occurrence by a product of $k$ three-point probabilities and $2p-1-3k$ two-point probabilities. Coincident positions give empty paths where needed, exactly as in AFH6.</p>
<p>Sum this product over all retained positions except the pinned root. Its incidence graph is a tree: a selected centre is now a three-point factor, each remaining edge is a two-point factor, and all other vertices carry positions. Root this tree at the pinned leaf and sum from its leaves inwards. A two-point factor, after its descendants have been summed, contributes</p>
<div class="math-display">$$\sum_y\tau(x,y)=\chi,$$</div>
<p>independently of its parent position $x$. A three-point factor contributes</p>
<div class="math-display">$$\sum_{y,z}\mathbb P(x,y,z\text{ lie in one cluster})=m_2,$$</div>
<p>again independently of $x$. At a position shared by several descendant branches, their constant contributions multiply. Thus the sum for the shape is exactly $m_2^k\chi^{2p-1-3k}$. Tonelli justifies each summation. Multiplying by the number of shapes proves the bound. The finite-witness exhaustion in AFH6 proves the same inequality on the countable model; the ordinary tree-graph estimate already makes all moments finite when $\chi&lt;\infty$.</p>
<p>This proves Lemma I.4.16 and extends <a href="/tag/9WYX/">9WYX</a>. Keeping a whole three-point event, rather than separately summing over its branch point, is what preserves a second-moment factor.</p>


## Bounds for the cluster at first connection {#section-critical-stopped-moments}

<a id="tag-7GBI" data-assertion="theorem" data-title="Critical stopped spatial moments have near and far scale bounds"></a>
<p>Assume the normalized radial model C0OR, $d=3\alpha$, $0&lt;\alpha&lt;2$, and</p>
<div class="math-display">$$\chi_r\sim\frac\alpha{\beta_c}r^\alpha,\qquad \widetilde M_0(r)=o(r^{2\alpha}).$$</div>
<p>Let $V_r=m_2(r)/\chi_r^3$, $\ell=\min_{z\neq0}\|z\|$, and $\rho=\min\{1,\ell/16\}$. For $x\neq0$ put $D=\|x\|$ and use the stopped quantities $\mathfrak R,\mathfrak S$ of <a href="/tag/FMUH/">FMUH</a>. For each integer $p\geq0$ there are $C_p&lt;\infty$ and a positive nonincreasing function $h_p\leq1$, decaying faster than every power, such that for every $r\geq\rho$,</p>
<div class="math-display">$$\begin{aligned}
\mathfrak R_r(x;p)&\leq C_p
\begin{cases}
V_r r^{-\alpha}D^p h_p(D/r),&r\leq D/8,\\
\displaystyle\int_{D/16}^r V_s s^{p-\alpha}\,\frac{ds}{s},&r\geq D/8,
\end{cases}\\
\mathfrak S_r(x;p)&\leq C_p
\begin{cases}
V_r D^p h_p(D/r),&r\leq D/8,\\
\displaystyle\int_{D/16}^r V_s s^p\,\frac{ds}{s},&r\geq D/8.
\end{cases}
\end{aligned}$$</div>
<p>The hypotheses are supplied by <a href="/tag/BCKB/">BCKB</a> conditionally on finite nonmonotone Reimer through L3TC. All constants below depend on the model and indicated degrees, not on $x$ or the radii.</p>
<p><em>Proof.</em> The moment bound <a href="/tag/AR3F/">AR3F</a> and the rapid tail <a href="/tag/3M2Y/">3M2Y</a> have their volume premise supplied by RM79. They hold uniformly for $s\geq\rho$: on the additional compact interval below one, every needed moment is bounded by DR1W and the bounded-jump estimate, while $V_s$ is positive and continuous. The same degree-increment proof gives the rapid tails there. Also <a href="/tag/121D/">121D</a>, extended over that compact interval, gives for every $\eta&gt;0$</p>
<div class="math-display">$$\frac{V_s}{V_t}\leq C_\eta\max\{(s/t)^\eta,(t/s)^\eta\}\qquad(s,t\geq\rho).$$</div>
<p>Write $A=K_0^s$, $B=K_x^s$, and $W_p(C)=\sum_{y\in C}\|y\|^p$. The exact derivative in FMUH and the bound on the crossing-pair count give</p>
<div class="math-display">$$\mathfrak R_s'(x;p)
\leq C s^{-5\alpha-1}
\mathbb E_s[\mathbf1_{\{A\neq B\}}(W_p(A)+W_p(B))|A||B|]
\leq C_p V_s s^{-\alpha-1}(s^p+D^p).$$</div>
<p>For the second inequality, <a href="/tag/1AC7/">the distinct-cluster comparison</a> separates the increasing functionals of $A$ and $B$. AR3F with two marked vertices bounds $\mathbb E_s[|A|W_p(A)]$ by $C_pV_s s^{3\alpha+p}$. Translation and $\|x+y\|^p\leq C_p(D^p+\|y\|^p)$ bound the corresponding expectation for $B$ by $C_pV_s s^{3\alpha}(D^p+s^p)$. The other component contributes $\chi_s\leq Cs^\alpha$.</p>
<p>If $s\leq D/8$, a pair $a\in A,b\in B$ with $\|a-b\|\leq s$ must have $\|a\|&gt;D/4$ or $\|b-x\|&gt;D/4$. Thus its count is at most</p>
<div class="math-display">$$|A\setminus\Lambda_{D/4}|\,|B|+|A|\,|B\setminus(x+\Lambda_{D/4})|.$$</div>
<p>Multiply by $W_p(A)+W_p(B)$ and apply 1AC7 to each of the four terms. The factor with a far vertex is controlled by 3M2Y, with one or two marked vertices according to whether it also carries the spatial weight. For example the two terms with weight in $A$ are bounded by</p>
<div class="math-display">$$\mathbb E_s[W_p(A)|A\setminus\Lambda_{D/4}|]\chi_s
+\mathbb E_s[W_p(A)|A|]\,\mathbb E_s|K_0\setminus\Lambda_{D/4}|.$$</div>
<p>For the other two terms, translate $B$ by $-x$ and use the preceding bound on the shifted weight. Taking a maximum of the finitely many rescaled rapid envelopes gives a positive nonincreasing $\psi_p\leq1$ with</p>
<div class="math-display">$$\mathfrak R_s'(x;p)\leq C_p V_s s^{-\alpha-1}D^p\psi_p(D/s)\qquad(s\leq D/8).$$</div>
<p>All derivative inequalities hold almost everywhere, and $\mathfrak S_s'=s^\alpha\mathfrak R_s'$ by FMUH.</p>
<p>Both stopped quantities vanish below $\ell$. For $r\leq D/8$, integrate their derivatives from below $\ell$ and use $V_s/V_r\leq C_\eta(r/s)^\eta$ when $s\leq r$. With $u=s/r$, the bound for $\mathfrak R_r$ is</p>
<div class="math-display">$$C_pV_r r^{-\alpha}D^p
\int_0^1u^{-\alpha-\eta-1}\psi_p((D/r)/u)\,du.$$</div>
<p>The bound for $\mathfrak S_r$ has prefactor $C_pV_rD^p$ and the smaller weight $u^{-\eta-1}$. The displayed integral is positive and nonincreasing as a function of $D/r\geq8$, and decays faster than every power: use $\psi_p(t)\leq C_Nt^{-N}$ with $N$ arbitrarily large. Extend this function constantly below eight and normalize it to be at most one. This gives the common $h_p$ in the two far bounds.</p>
<p>For $r\geq D/8$, put $a=D/16$. If $a&lt;\ell$, the stopped quantities at $a$ are zero. Otherwise their far bounds give $\mathfrak R_a\leq C_pV_a a^{p-\alpha}$ and $\mathfrak S_a\leq C_pV_a a^p$. The ratio estimate for $V$ shows that these are bounded by constant multiples of the respective integrals over $[a,2a]$. On $[a,r]$, the coarse derivative estimate has $D^p+s^p\leq C_ps^p$. Integrating it and absorbing the value at $a$ proves both near bounds. All lower integration endpoints are positive and at least $\rho$; no contribution from radii below one has been dropped.</p>
<p>These are the critical-dimension forms of (III.5.3)–(III.5.6).</p>

## The averaged weighted three-point bound {#section-critical-averaged-three-point}

<a id="tag-2CQ5" data-assertion="theorem" data-title="The critical weighted three-point sum retains the vertex factor"></a>
<p>Under the hypotheses and notation of <a href="/tag/7GBI/">7GBI</a>, for each integer $p\geq0$ there are $C_p&lt;\infty$ and a positive nonincreasing rapid-decay function $h_p:(0,\infty)\to(0,1]$ such that</p>
<div class="math-display">$$\mathbb E_r\left[\mathbf1_{\{0\leftrightarrow x\}}\sum_{y\in K_0}\|y\|^p\right]
\leq C_p r^{p+\alpha}V_{\|x\|}\|x\|^{-\alpha}h_p(\|x\|/r)
\qquad(x\neq0, r\geq\rho).$$</div>
<p><em>Proof.</em> Put $D=\|x\|$ and denote the left side by $Q_p(r,x)$. It is zero for $r&lt;\ell$. For $r\geq\ell$, <a href="/tag/JDX7/">the stopped-growth inequality</a> and <a href="/tag/YU52/">the spatial moment bound</a> give</p>
<div class="math-display">$$Q_p(r,x)\leq\mathfrak S_r(x;p)
+C_p\sum_{k=0}^p\mathfrak R_r(x;k)r^{p-k+\alpha}.$$</div>
<p>For $r\geq D/8$, substitute the near bounds of 7GBI. The $\mathfrak S$ term is absorbed into the term $k=p$, since $s^\alpha\leq r^\alpha$ under the integral. Hence</p>
<div class="math-display">$$Q_p(r,x)\leq C_p\sum_{k=0}^p r^{p-k+\alpha}
\int_{D/16}^r V_s s^{k-\alpha}\,\frac{ds}{s}.$$</div>
<p>Choose $0&lt;\eta&lt;\alpha$. The ratio bound for $V$ gives $V_s\leq C V_D(s/D)^\eta$ for $s\geq D/16$, after enlarging the constant on $[D/16,D]$. Thus, using $s^k\leq r^k$,</p>
<div class="math-display">$$\int_{D/16}^r V_s s^{k-\alpha}\,\frac{ds}{s}
\leq C r^k V_D D^{-\alpha}
\int_{1/16}^{\infty}v^{-\alpha+\eta}\,\frac{dv}{v}
\leq C' r^k V_D D^{-\alpha}.$$</div>
<p>This yields $Q_p(r,x)\leq C_p r^{p+\alpha}V_DD^{-\alpha}$. The strictly negative exponent in the integral also handles $k=0$ without a logarithmic loss.</p>
<p>For $r\leq D/8$, the far bounds of 7GBI give, with a common rapid envelope $h$,</p>
<div class="math-display">$$Q_p(r,x)\leq C_pV_rD^p h(D/r).$$</div>
<p>Indeed $r^{p-k}D^k\leq D^p$ for every term in the stopped-growth sum. Dividing by $r^{p+\alpha}V_DD^{-\alpha}$ and applying the ratio bound for $V_r/V_D$ gives at most</p>
<div class="math-display">$$C_p(D/r)^{p+\alpha+\eta}h(D/r).$$</div>
<p>This has every polynomial decay rate. Together with the uniform near bound, it produces the asserted positive nonincreasing envelope by the construction in 3M2Y: take the supremum of the normalized expectations over all pairs with $\|x\|/r\geq t$, normalize its finite bound, and add a positive multiple of $e^{-t}$. The supremum is nonincreasing and has every polynomial tail.</p>
<p>This proves Lemma III.5.2 at $d=3\alpha$, $\alpha&lt;2$, under the explicit hydrodynamic/susceptibility hypotheses. Those inputs, including the necessary volume moments, are supplied by the preceding conditional chain. The factor $V_{\|x\|}$ has been retained throughout.</p>

## Three marked vertices at critical dimension {#section-critical-three-point-bound}

<a id="tag-8JMB" data-assertion="theorem" data-title="The critical three-point function has the vertex factor and rapid cutoff decay"></a>
<p>Under the hypotheses of 7GBI, let $x,y,z$ be distinct vertices, and put</p>
<div class="math-display">$$\delta=\min\{\|x-y\|,\|x-z\|,\|y-z\|\},\qquad
D=\max\{\|x-y\|,\|x-z\|,\|y-z\|\}.$$</div>
<p>Write $\tau_r(x,y,z)$ for the probability that all three vertices lie in one cutoff cluster. There are $C&lt;\infty$ and a positive nonincreasing rapid-decay function $h:(0,\infty)\to(0,1]$ such that</p>
<div class="math-display">$$\tau_r(x,y,z)\leq C V_\delta\delta^{-\alpha}D^{-2\alpha}h(D/r)
\qquad(r\geq\rho).$$</div>
<p>For the full critical model,</p>
<div class="math-display">$$\tau_{\beta_c}(x,y,z)\leq C V_\delta\delta^{-\alpha}D^{-2\alpha}.$$</div>
<p>Since $d=3\alpha$, the two distance powers are $\delta^{-d+2\alpha}D^{-d+\alpha}$, as in Proposition III.5.1. BCKB and L3TC supply the stated hypotheses conditionally on finite nonmonotone Reimer.</p>
<p><em>Proof.</em> At a merger that first connects all three marks, precisely two of them were in one component and the third was in another. For a pair $\{u,v\}$ of marked vertices and the remaining vertex $w$, set</p>
<div class="math-display">$$J_r(u,v;w)=\mathbb E_r\left[\mathbf1_{\{u\leftrightarrow v,\ u\nleftrightarrow w\}}
\sum_{a\in K_u}\sum_{b\in K_w}\mathbf1_{\{\|a-b\|\leq r\}}\right].$$</div>
<p>The exact derivative is</p>
<div class="math-display">$$\frac{d}{dr}\tau_r(x,y,z)
=\beta_c|j'(r)|\bigl(J_r(x,y;z)+J_r(x,z;y)+J_r(y,z;x)\bigr)
\qquad\text{a.e.}$$</div>
<p>To justify it, first differentiate in a finite induced box. A single edge cannot connect three previously distinct components, and a merger after all marks are connected contributes zero. If exactly two marked components remain, each crossing edge is counted once in exactly one of the displayed terms. At a fixed finite terminal radius, the three full root clusters are finite by DR1W. Once the box contains their vertex sets, their earlier histories and the integrands agree with those of the full process. The crossing counts are bounded by products of terminal cluster sizes, with finite expectation. The rate is bounded on compact positive radius intervals. Integrating before exhausting the lattice therefore proves local absolute continuity and the displayed a.e. identity.</p>
<p>Dropping the distance condition in $J_r$ and applying 1AC7 gives</p>
<div class="math-display">$$J_r(u,v;w)\leq
\mathbb E_r[\mathbf1_{\{u\leftrightarrow v\}}|K_u|]\chi_r
\leq C r^{2\alpha}V_{\|u-v\|}\|u-v\|^{-\alpha},$$</div>
<p>where <a href="/tag/2CQ5/">2CQ5</a> is used with $p=0$ after translating $u$ to zero. The ratio estimate with an exponent $\eta&lt;\alpha$ bounds the last distance factor by $C V_\delta\delta^{-\alpha}$, uniformly over the three pairings.</p>
<p>Suppose now that $r\leq D/8$. In any pairing, at least one of its two vertices is at distance at least $D/2$ from the singleton $w$; otherwise the triangle inequality would make all three pair distances less than $D$. Name this vertex $u$. If a crossing pair has $\|a-b\|\leq r$, then $\|a-u\|&gt;D/8$ or $\|b-w\|&gt;D/8$. The same distinct-cluster comparison bounds $J_r$ by</p>
<div class="math-display">$$\begin{aligned}
&\mathbb E_r[\mathbf1_{\{u\leftrightarrow v\}}|K_u\setminus(u+\Lambda_{D/8})|]\chi_r\\
&\qquad+\mathbb E_r[\mathbf1_{\{u\leftrightarrow v\}}|K_u|]
\mathbb E_r|K_w\setminus(w+\Lambda_{D/8})|.
\end{aligned}$$</div>
<p>For every integer $q\geq0$, Markov's pointwise bound on the far vertex, followed by 2CQ5 at degree $q$, bounds the first term by</p>
<div class="math-display">$$C_q r^{2\alpha}V_{\|u-v\|}\|u-v\|^{-\alpha}(r/D)^q.$$</div>
<p>The second has the same bound by 2CQ5 at degree zero and YU52 at degree $q$. Replace the paired distance by $\delta$ as above. Thus the normalized sum of the three $J_r$ is uniformly bounded and has every polynomial tail in $D/r$. The supremum-and-exponential construction used in 3M2Y supplies a positive nonincreasing rapid envelope $\psi$ such that</p>
<div class="math-display">$$0\leq\tau_r'(x,y,z)
\leq C V_\delta\delta^{-\alpha}r^{-2\alpha-1}\psi(D/r)\qquad\text{a.e.}$$</div>
<p>Here $\beta_c|j'(r)|\leq Cr^{-4\alpha-1}$ uniformly for $r\geq\rho$; compact radii are absorbed into the constant.</p>
<p>At radius $\rho&lt;\ell$ all clusters are singletons, so $\tau_\rho(x,y,z)=0$. Integrating and substituting $t=D/s$ gives</p>
<div class="math-display">$$\tau_r(x,y,z)\leq C V_\delta\delta^{-\alpha}D^{-2\alpha}
\int_{D/r}^{\infty} t^{2\alpha-1}\psi(t)\,dt.$$</div>
<p>The integral is finite even when its lower endpoint is zero, because $\alpha&gt;0$ and $\psi\leq1$ near zero. Its tail is positive, nonincreasing and faster than every power. Normalize it by its value at zero to obtain $h$ and the finite-cutoff bound.</p>
<p>Finally, the cutoff intensities increase to the full critical kernel. Almost surely, every edge open in the full exponential-clock coupling is open at some finite cutoff; equality of a clock with its limiting intensity has probability zero, simultaneously over the countable edge set. Any connection of the three marks has a finite path witness. Hence the cutoff connection events increase to the full event, and monotone convergence proves the final bound. No full-model susceptibility bound is used in this passage.</p>
<p>This completes the critical-dimension proof of Proposition III.5.1, with finite-cutoff rapid decay and the full-model limit. The general above-critical assembly, the value of the vertex-factor asymptotic, and the later refinements in Section III.5 remain separate.</p>


## The spatial size of a three-point tree {#section-three-point-convolution}

<a id="tag-54OK" data-assertion="theorem" data-title="The three-point tree convolution has two separation scales"></a>
<p>Fix a norm on $\mathbb R^d$ and $0&lt;\alpha&lt;d/2$. Put $\langle u\rangle=\max\{1,\|u\|\}$ and $k(u)=\langle u\rangle^{-d+\alpha}$. For distinct $x,y,z\in\mathbb Z^d$, let $\delta$ and $D$ be the minimum and maximum of the three regularized pair distances. Then</p>
<div class="math-display">$$\sum_{w\in\mathbb Z^d}k(x-w)k(y-w)k(z-w)
\asymp \delta^{-d+2\alpha}D^{-d+\alpha}.$$</div>
<p>The constants depend only on the norm, $d$ and $\alpha$. The diagonal terms use $k(0)=1$. Since nonzero lattice distances have a positive minimum, removing the regularization from the two distances on the right changes only the constants.</p>
<p><em>Proof.</em> Write $q=d-\alpha$. Lattice ball counting and dyadic summation give</p>
<div class="math-display">$$\sum_{\|u\|\leq R}k(u)\asymp R^\alpha\qquad(R\geq1).$$</div>
<p>Indeed a norm ball contains and is contained in fixed Euclidean cubes, so its lattice count is comparable to $R^d$. Dyadic shells give the upper bound, and the ball of radius $R/2$, where $k\geq C R^{-q}$, gives the lower bound. The root term handles bounded radii.</p>
<p>Relabel so that $xy$ is a shortest pair and $xz$ a longest pair. The regularized distance from $y$ to $z$ lies between $D/2$ and $D$. Partition the summation points by a nearest marked vertex, assigning ties arbitrarily. On the part nearest $x$, put $t=\langle w-x\rangle$. The triangle inequality and the nearest-vertex condition give</p>
<div class="math-display">$$\langle w-y\rangle\geq\tfrac12\max\{t,\delta\},\qquad
\langle w-z\rangle\geq\tfrac12\max\{t,D\}.$$</div>
<p>For $t\leq\delta$, the sum is at most $C\delta^{-q}D^{-q}\delta^\alpha$. For $\delta&lt;t\leq D$, a dyadic shell of radius $R$ contributes at most $C D^{-q}R^{d-2q}$; the sum is bounded by $C D^{-q}\delta^{d-2q}$ because $d-2q=-d+2\alpha&lt;0$. The shells beyond $D$ contribute at most $C D^{d-3q}$. This last quantity is also bounded by $C\delta^{-d+2\alpha}D^{-d+\alpha}$.</p>
<p>The part nearest $y$ has the same bounds, since its distances to the other marks are $\delta$ and a quantity comparable to $D$. On the part nearest $z$, both other marks are at distance comparable to $D$. The inner ball and the outer shells each contribute at most $C D^{d-3q}$, already bounded as required.</p>
<p>For the lower bound, retain only $\|w-x\|\leq\delta/4$. On this ball, $k(y-w)\geq c\delta^{-q}$ and $k(z-w)\geq cD^{-q}$, while the sum of $k(x-w)$ is at least $c\delta^\alpha$. The same root-term adjustment covers bounded $\delta$. This proves both comparisons.</p>
<p>At $d=3\alpha$, the result becomes</p>
<div class="math-display">$$\sum_w k(x-w)k(y-w)k(z-w)
\asymp\delta^{-\alpha}D^{-2\alpha}
\asymp\bigl(k(x-y)k(y-z)k(z-x)\bigr)^{1/2}.$$</div>
<p>Thus, when the two-point function is bounded by a constant times $k$, the upper expressions furnished by <a href="/tag/AFH6/">the tree-graph inequality</a> and <a href="/tag/87RB/">the three-point product inequality</a> have the same spatial order. The bound 8JMB additionally retains the vertex factor at the smaller separation. This is the comparison in Remark III.5.3, with finite diagonal values and arbitrary norm balls made explicit.</p>


## Local mass at the critical volume scale {#section-critical-local-mass}

<a id="tag-3N3Q" data-assertion="theorem" data-title="Critical cluster mass localizes and persists across scales"></a>
<p>Assume the hypotheses of 7GBI, and put $X_r=|K_0^r|$, $\zeta_r=m_2(r)/(4\chi_r)$ and $Y_{r,L}=|K_0^r\cap\Lambda_{Lr}|$. There are fixed $L_0\geq1$ and $c&gt;0$ such that, with $E_r=\{Y_{r,L_0}\geq\zeta_r\}$,</p>
<div class="math-display">$$c\frac{\chi_r}{\zeta_r}\leq\mathbb P(E_r)
\leq\frac{\chi_r}{\zeta_r}\qquad(r\geq1).$$</div>
<p>For every $\eta&gt;0$ there exist $b&gt;0$ and $L\geq L_0$ such that</p>
<div class="math-display">$$\mathbb E[X_r;Y_{r,L}\leq b\zeta_r]\leq\eta\chi_r
\qquad(r\geq1).$$</div>
<p>Consequently, for every $\varepsilon&gt;0$ there are $b\in(0,1)$ and $L\geq L_0$, independent of $r,R$, for which the monotone cutoff coupling satisfies</p>
<div class="math-display">$$\mathbb P(Y_{r,L}\leq b\zeta_r\mid E_R)\leq\varepsilon
\qquad(1\leq r\leq R).$$</div>
<p>The conditioning event keeps the same $L_0$ and threshold $\zeta_R$ as the error is decreased.</p>
<p><em>Proof.</em> The rapid tails 3M2Y at one and two marked vertices, with zero spatial degrees, imply</p>
<div class="math-display">$$\mathbb E(X_r-Y_{r,L})\leq C\chi_r h(L),\qquad
\mathbb E[X_r(X_r-Y_{r,L})]\leq C m_2(r)h(L),$$</div>
<p>where $h(L)\to0$ and both bounds are uniform for $r\geq1$. Choose $L_0$ so that $\mathbb E Y_{r,L_0}^2\geq m_2(r)/2$, using $X_r^2-Y_{r,L_0}^2\leq2X_r(X_r-Y_{r,L_0})$. The contribution from $Y_{r,L_0}&lt;\zeta_r$ to its second moment is at most $\zeta_r\chi_r=m_2(r)/4$. Hölder gives</p>
<div class="math-display">$$\frac{m_2(r)}4\leq
\mathbb E[Y_{r,L_0}^2;E_r]
\leq m_3(r)^{2/3}\mathbb P(E_r)^{1/3}.$$</div>
<p>RM79 bounds $m_3(r)$ by $C\chi_r(m_2(r)/\chi_r)^2$, uniformly including compact radii. Cubing proves the lower bound for $\mathbb P(E_r)$. Markov gives the upper bound.</p>
<p>For the small-mass estimate use the pointwise inequality</p>
<div class="math-display">$$X_r\mathbf1_{\{Y_{r,L}\leq b\zeta_r\}}
\leq X_r-Y_{r,L}+\min(X_r,b\zeta_r).$$</div>
<p>First choose $L$ to make the expectation of the first term at most $\eta\chi_r/2$. Then choose $b$ using <a href="/tag/326J/">326J</a>, with $m_2/\chi=4\zeta$, to control the second term uniformly. This proves the second assertion.</p>
<p>For persistence, write $D_r=\{Y_{r,L}\leq b\zeta_r\}$. The omitted-edge row is at most $Cr^{-\alpha}$ by NE2Q. Apply <a href="/tag/F4RR/">the independent-layer extension bound</a> to the added layer from $r$ to $R$:</p>
<div class="math-display">$$\mathbb E[X_R;D_r]
\leq(1+Cr^{-\alpha}\chi_R)\mathbb E[X_r;D_r]
\leq C'\eta\chi_R.$$</div>
<p>The last step uses $\chi_s\asymp s^\alpha$ and $r\leq R$. On $E_R$, $X_R\geq\zeta_R$, while $\zeta_R\mathbb P(E_R)\geq c\chi_R$. Thus $\mathbb P(D_r\mid E_R)\leq C'\eta/c$. Choose $\eta$ accordingly and decrease $b$ below one.</p>
<p>This gives the local-mass and persistence inputs of the proof of Proposition III.5.4 with a fixed dilated ball $\Lambda_{L_0r}$. The paper's display (III.5.12) uses $\Lambda_r$ and invokes its spatial scaling limit. The dilation here is sufficient for the lower bound and is retained explicitly; no unit-ball mass limit is asserted.</p>

## The matching critical three-point lower bound {#section-critical-three-point-lower}

<a id="tag-KBOM" data-assertion="theorem" data-title="The critical three-point function has matching upper and lower bounds"></a>
<p>Under the hypotheses of 7GBI, for every distinct $x,y,z\in\mathbb Z^d$,</p>
<div class="math-display">$$\tau_{\beta_c}(x,y,z)
\asymp V_\delta\delta^{-\alpha}D^{-2\alpha},\qquad
\delta=\min\{\|x-y\|,\|x-z\|,\|y-z\|\},\quad
D=\max\{\|x-y\|,\|x-z\|,\|y-z\|\}.$$</div>
<p>The lower bound already holds in the cutoff model at radius $C\max\{1,D\}$ for a fixed model-dependent $C$. Sharp susceptibility and ordinary hydrodynamics are the hypotheses; their derivation through BCKB retains the finite nonmonotone Reimer premise.</p>
<p><em>Proof.</em> The upper bound is 8JMB. Relabel so that $\|x-y\|=\delta$ and $\|x-z\|=D$. Use 3N3Q with $\varepsilon=1/2$, and denote its constants by $b,L,L_0$. Put $r=\max\{1,\delta\}$. We first record a uniform fact about fresh edges. For each fixed $H\geq1$, there are $T_H&gt;1$ and $c_H&gt;0$ such that every edge of length at most $Hs$ receives added intensity at least $c_Hs^{-d-\alpha}$ between cutoffs $s$ and $T_Hs$, for every $s\geq1$.</p>
<p>To see this, choose $s_0\geq1$ beyond which $\beta_c|j'(t)|\geq c t^{-d-\alpha-1}$. For an edge of length at most $Hs$, integrate this derivative from $u=\max\{Hs,s_0\}$ to $2u$. The interval lies above its length and inside $[s,2\max\{H,s_0\}s]$. Its integral is at least a fixed positive multiple of $s^{-d-\alpha}$. This also covers bounded radii, where the kernel need not be strictly decreasing.</p>
<p>Take $T=T_{2L+1}$, enlarging it to at least two, and put $R=T\max\{1,D\}$. Let $S_v$ be the event that $K_v^r$ has more than $b\zeta_r$ vertices in $v+\Lambda_{Lr}$, and let $E_v$ be the translated event that $K_v^R$ has at least $\zeta_R$ vertices in $v+\Lambda_{L_0R}$. Define</p>
<div class="math-display">$$A=S_x\cap S_y\cap E_x\cap E_z.$$</div>
<p>Harris association in the independent edge-increment coupling and 3N3Q give</p>
<div class="math-display">$$\mathbb P(A)\geq\mathbb P(S_y)\mathbb P(S_x\cap E_x)\mathbb P(E_z)
\geq c\frac{\chi_r\chi_R^2}{\zeta_r\zeta_R^2}.$$</div>
<p>Here the conditional persistence bound gives $\mathbb P(S_x\mid E_x)\geq1/2$. Also $S_y$ contains the corresponding mass event at radius $r$, because $L\geq L_0$ and $b&lt;1$.</p>
<p>Let $\mathcal F_s$ reveal all increments up to cutoff $s$, and set $G_1=\{x\leftrightarrow y\text{ at cutoff }Tr\}$. On $S_x\cap S_y$, either the two radius-$r$ clusters agree already, or their local vertex sets are disjoint, have more than $b\zeta_r$ vertices each, and lie within mutual distance $(2L+1)r$. Conditional on $\mathcal F_r$, the fresh crossing edges are independent. Hence</p>
<div class="math-display">$$\mathbb P(G_1\mid\mathcal F_r)
\geq q_r\mathbf1_{S_x\cap S_y},\qquad
q_r=c_1\zeta_r^2r^{-d-\alpha}.$$</div>
<p>Choose $c_1$ small enough that $q_r\leq1$. This linear lower bound follows from $1-e^{-t}$ because $\zeta_r^2r^{-d-\alpha}$ is uniformly bounded: at $d=3\alpha$, $\zeta_r=V_r\chi_r^2/4$, $V_r\leq1$ and $\chi_r\leq Cr^\alpha$.</p>
<p>Given $\mathcal F_r$, the events $G_1$ and $E_x\cap E_z$ are increasing functions of the remaining independent increments. Conditional Harris therefore gives</p>
<div class="math-display">$$\mathbb P(A\cap G_1\mid\mathcal F_r)
\geq q_r\mathbf1_{S_x\cap S_y}\mathbb P(E_x\cap E_z\mid\mathcal F_r),$$</div>
<p>and averaging yields $\mathbb P(A\cap G_1)\geq q_r\mathbb P(A)$. No independence between the mass events and the joining event is assumed.</p>
<p>Now $Tr\leq R$, so $A\cap G_1$ is $\mathcal F_R$-measurable. On $E_x\cap E_z$, the same fresh-edge argument, with $H=2L_0+1$, joins the two large-scale clusters by cutoff $UR$, where $U=T_{2L_0+1}$, with conditional probability at least $c_2\zeta_R^2R^{-d-\alpha}$. The distance $\|x-z\|\leq R$ is included in this choice of $H$. Thus</p>
<div class="math-display">$$\begin{aligned}
\tau_{UR}(x,y,z)&\geq c\zeta_r^2r^{-d-\alpha}\zeta_R^2R^{-d-\alpha}\mathbb P(A)\\
&\geq c'\zeta_r\chi_r\chi_R^2r^{-d-\alpha}R^{-d-\alpha}\\
&\asymp V_r r^{-\alpha}R^{-2\alpha}.
\end{aligned}$$</div>
<p>Since $R=T\max\{1,D\}$, this has the asserted large-distance scale. If $\delta&lt;1$, positivity and continuity of $V$ on the compact interval between the shortest lattice distance and one compare $V_r r^{-\alpha}$ with $V_\delta\delta^{-\alpha}$. The same bounded-distance adjustment applies to $D$. Domination by the full model completes the proof.</p>
<p>This proves Proposition III.5.4 at critical dimension using dilated local balls, and combines it with the critical upper bound. It does not require the full spatial superprocess limit. The explicit logarithmic equivalent of $V$ and the general higher-point lower bound in Remark III.5.6 remain separate.</p>


## A critical lower bound for finitely many marked vertices {#section-critical-marked-set}

<a id="tag-3K2W" data-assertion="theorem" data-title="Critical multipoint lower bounds retain every sweep vertex factor"></a>
<p>Assume the hypotheses of <a href="/tag/7GBI/">7GBI</a>: the normalized radial model, $d=3\alpha$, $0&lt;\alpha&lt;2$, sharp susceptibility and ordinary hydrodynamics. Let $A\subset\mathbb Z^d$ have $n\geq2$ distinct vertices and diameter $D$. For any tree on $A$ directed toward a root, use the sets $A_x$ of <a href="/tag/CS13/">CS13</a> and put $R_x=\operatorname{diam}(A_x)$. Thus the root has radius $D$, and a nonroot set includes its parent. There are constants $c_n&gt;0$ and $C_n&lt;\infty$, depending only on $n$ and the model, such that</p>
<div class="math-display">$$\begin{aligned}
\tau_{C_n\max\{1,D\}}(A)
&\geq c_n\frac{D^{4\alpha}}{\zeta_D^2}
       \prod_{x\in A}\zeta_{R_x}R_x^{-3\alpha},
&\qquad \zeta_s&=\frac{m_2(s)}{4\chi_s},\\
\frac{D^{4\alpha}}{\zeta_D^2}
       \prod_{x\in A}\zeta_{R_x}R_x^{-3\alpha}
&\asymp_n\frac1{V_D^2}\prod_{x\in A}V_{R_x}R_x^{-\alpha},
& V_s&=\frac{m_2(s)}{\chi_s^3}.
\end{aligned}$$</div>
<p>Here $\tau_s(A)$ is the probability that all marks lie in one cluster at cutoff $s$ and intensity $\beta_c$. The same lower bound therefore holds for the full model. It holds uniformly over the rooted tree, in particular for a tree attaining the sweep minimum. Its critical-model application retains the finite nonmonotone Reimer premise through BCKB.</p>
<p><em>Proof.</em> Enumerate the marks as $a_1,\ldots,a_n$ in nondecreasing order of $R_i:=R_{a_i}$, breaking ties with descendants before ancestors. This is possible because $A_x\subseteq A_{\operatorname{parent}(x)}$. The root is $a_n$, $R_n=D$, and the parent of $a_i$ has index $\sigma(i)&gt;i$ and lies at distance at most $R_i$.</p>
<p>Apply <a href="/tag/3N3Q/">conditional mass persistence</a> with error $1/(2n)$, obtaining $b\in(0,1)$ and $L\geq L_0$. The fresh-edge estimate in <a href="/tag/KBOM/">KBOM</a> gives a fixed $B\geq2$ such that every edge of length at most $(2L+1)s$ receives intensity at least $c s^{-4\alpha}$ between cutoffs $s$ and $Bs$, for all $s\geq1$. Set</p>
<div class="math-display">$$t_i=B^i\max\{1,R_i\}.$$</div>
<p>Then $Bt_i\leq t_{i+1}$. For each $j$, let $F_j$ require that the cluster of $a_j$ at cutoff $t_i$ contain more than $b\zeta_{t_i}$ vertices in $a_j+\Lambda_{Lt_i}$, for every $i\leq j$. Conditional on the translated event $E_{t_j}$ of 3N3Q, a union bound gives $\mathbb P(F_j\mid E_{t_j})\geq1-j/(2n)\geq1/2$. Hence</p>
<div class="math-display">$$\mathbb P(F_j)\geq c\frac{\chi_{t_j}}{\zeta_{t_j}},\qquad
\mathbb P(\mathcal M)\geq c^n\prod_{j=1}^n\frac{\chi_{t_j}}{\zeta_{t_j}},
\quad \mathcal M=\bigcap_{j=1}^n F_j.$$</div>
<p>The second inequality is Harris association: each $F_j$ is increasing in the independent Poisson increments defining the cutoff coupling.</p>
<p>Write the same event as $\mathcal M=\bigcap_i H_i$, where $H_i$ requires the local-mass bound at cutoff $t_i$ for every mark $a_j$ with $j\geq i$. Let $\mathcal F_{t_i}$ reveal all increments up to $t_i$, and, for $i&lt;n$, put $G_i=\{a_i\leftrightarrow a_{\sigma(i)}\text{ at cutoff }Bt_i\}$. On $H_i$, either the two clusters already agree or they have disjoint local sets of more than $b\zeta_{t_i}$ vertices each. Every edge between these sets has length at most $2Lt_i+R_i\leq(2L+1)t_i$. The fresh-edge estimate therefore gives</p>
<div class="math-display">$$\mathbb P(G_i\mid\mathcal F_{t_i})\geq q_i\mathbf1_{H_i},
\qquad q_i=c_1\zeta_{t_i}^2t_i^{-4\alpha}.$$</div>
<p>The constant $c_1&gt;0$ is uniform and may be chosen so that $q_i\leq1$. Indeed $\zeta_s^2s^{-4\alpha}$ is uniformly bounded by $V_s\leq1$ and $\chi_s\asymp s^\alpha$; the probability of a fresh crossing is at least $1-\exp(-c b^2\zeta_s^2s^{-4\alpha})$.</p>
<p>Conditional on $\mathcal F_{t_i}$, both $G_i$ and the remaining mass event $\bigcap_{j&gt;i}H_j$ are increasing in the unexposed increments. Conditional Harris gives</p>
<div class="math-display">$$\mathbb P\left(G_i\cap\bigcap_{j&gt;i}H_j\mid\mathcal F_{t_i}\right)
\geq q_i\mathbf1_{H_i}
\mathbb P\left(\bigcap_{j&gt;i}H_j\mid\mathcal F_{t_i}\right).$$</div>
<p>All previous joins are already measurable, since $Bt_j\leq t_i$ for $j&lt;i$. Multiply by the indicator of the previous joins and of $\bigcap_{j\leq i}H_j$, then average. It follows that</p>
<div class="math-display">$$\mathbb P\left(\mathcal M\cap\bigcap_{j\leq i}G_j\right)
\geq q_i\mathbb P\left(\mathcal M\cap\bigcap_{j&lt;i}G_j\right).$$</div>
<p>Iterating joins all tree edges by cutoff $t_n$. Thus</p>
<div class="math-display">$$\begin{aligned}
\tau_{t_n}(A)&\geq c_n
\prod_{i=1}^{n-1}\bigl(\zeta_{t_i}^2t_i^{-4\alpha}\bigr)
\prod_{i=1}^n\frac{\chi_{t_i}}{\zeta_{t_i}}\\
&\asymp_n\frac{t_n^\alpha}{\zeta_{t_n}}
       \prod_{i=1}^{n-1}\zeta_{t_i}t_i^{-3\alpha}
=\frac{t_n^{4\alpha}}{\zeta_{t_n}^2}
       \prod_{i=1}^n\zeta_{t_i}t_i^{-3\alpha}.
\end{aligned}$$</div>
<p>The second line uses $\chi_s\asymp s^\alpha$. Let $\ell$ be the shortest nonzero lattice distance in the chosen norm. All $R_i\geq\ell$, and $1\leq t_i/R_i\leq B^n\max\{1,\ell^{-1}\}$. The ratio bounds in <a href="/tag/121D/">121D</a>, extended over compact positive radii, therefore compare $\zeta_{t_i}$ with $\zeta_{R_i}$ uniformly. Since $t_n=B^n\max\{1,D\}$, this proves the first inequality. Finally $\zeta_s\asymp V_s s^{2\alpha}$ for $s\geq\ell$, which gives the second expression.</p>
<p>For two marks both radii equal $D$, so the vertex factors cancel and the bound is $c_2D^{-2\alpha}$. For three marks take the path from a closest-pair endpoint through its partner to the third mark. Its radii are $\delta,D,D$, giving $c_3V_\delta\delta^{-\alpha}D^{-2\alpha}$, as in KBOM. This proves the critical case of Remark III.5.6. A matching upper bound for arbitrary finite marked sets, and the case $d&gt;3\alpha$, are separate assertions.</p>


## A summable product of three-point functions {#section-critical-three-point-product}

<a id="tag-BX1G" data-assertion="theorem" data-title="The spatially weighted double three-point diagram has a vanishing critical factor"></a>
<p>Under the hypotheses of <a href="/tag/7GBI/">7GBI</a>, put</p>
<div class="math-display">$$T_r(u,v,w)=\mathbb P_r(u\leftrightarrow v\leftrightarrow w),\qquad
Q_s(r,u)=\sum_y T_r(0,u,y)\|y\|^s.$$</div>
<p>Repeated vertices are allowed, and zero powers are one. For every integer $s\geq0$ and all sufficiently large $r$,</p>
<div class="math-display">$$S_s(r):=\sum_u Q_0(r,u)Q_s(r,u)
\leq C_s\bigl(r^{2\alpha+s}+V_r^2r^{3\alpha+s}\bigr)
=o(r^{3\alpha+s}).$$</div>
<p>Using $A,C$ from <a href="/tag/SE64/">SE64</a>, for all integers $p,q\geq0$, $s=p+q$, one consequently has</p>
<div class="math-display">$$\begin{aligned}
\mathcal T_{p,q}(r)&:=\sum_{x,y,a,b,c,z}
A(b)C(x,c,z)T_r(y,b,c)T_r(a,b,c)\|y\|^p\|z\|^q\\
&\leq C_{p,q}V_r^3r^{11\alpha+s}(V_r^2+r^{-\alpha})
=o(|B_r|V_r^3r^s\chi_r^8).
\end{aligned}$$</div>
<p><em>Proof.</em> The term $u=0$ is $\chi_r\mathbb E_r\sum_{y\in K_0}\|y\|^s=O(r^{2\alpha+s})$ by <a href="/tag/YU52/">YU52</a>. For $u\ne0$, apply <a href="/tag/2CQ5/">2CQ5</a> twice and take a common nonincreasing rapid envelope $h$ to obtain</p>
<div class="math-display">$$Q_0(r,u)Q_s(r,u)
\leq C_s r^{2\alpha+s}V_{\|u\|}^2\|u\|^{-2\alpha}h(\|u\|/r).$$</div>
<p>Choose $0&lt;\eta&lt;\alpha/2$. The ratio estimate of <a href="/tag/121D/">121D</a>, extended over the fixed compact interval down to the shortest nonzero lattice distance, gives</p>
<div class="math-display">$$V_D^2\leq C_\eta V_r^2
\begin{cases}(r/D)^{2\eta},&D\leq r,\\(D/r)^{2\eta},&D\geq r.
\end{cases}$$</div>
<p>The lattice count $|\{u:\|u\|\leq R\}|\leq C R^d$ for $R$ at least that shortest distance follows from equivalence of norms. In dyadic annuli below $r$, it bounds the sum of $D^{-2\alpha}(r/D)^{2\eta}$ by $C r^{d-2\alpha}$, since $d-2\alpha-2\eta=\alpha-2\eta&gt;0$. Above $r$, the rapid decay of $h$ makes the corresponding annular sum finite with the same bound. Therefore</p>
<div class="math-display">$$\sum_{u\ne0}V_{\|u\|}^2\|u\|^{-2\alpha}h(\|u\|/r)
\leq C V_r^2r^\alpha.$$</div>
<p>This proves the estimate for $S_s$. Its little-o conclusion uses $\alpha&gt;0$ and $V_r\to0$ from <a href="/tag/5J3U/">5J3U</a>. In particular no singular off-diagonal estimate has been applied at $u=0$.</p>
<p>For the second assertion use the four-weight bound from SE64. Keep its notation $U_{k,s}=\mathbb E_r[|K_0|^{k-1}\sum_{v\in K_0}\|v\|^s]$. The four resulting sums, for weights on $b$, $y-b$, $y-c$, and $z-c$, are respectively</p>
<div class="math-display">$$U_{2,s}m_3S_0,\qquad m_2m_3S_s,\qquad
m_2m_3S_s,\qquad m_2U_{3,s}S_0.$$</div>
<p>Indeed, after summing $x,z$ as in SE64, translate by $-b$ and write $u=c-b$. Summation over $a-b$ gives $Q_0(r,u)$, and summation over $y-b$ gives either $Q_0(r,u)$ or $Q_s(r,u)$. For the weight on $y-c$, the reflection $v\mapsto u-v$ exchanges the two fixed roots and preserves the radial law, so it gives the same $Q_s(r,u)$. All changes of order are justified by Tonelli.</p>
<p>Finally $U_{2,s}\leq C_sV_rr^{3\alpha+s}$ and $U_{3,s}\leq C_sV_r^2r^{5\alpha+s}$ by AR3F with its volume input supplied by RM79. Substitute the bound for $S_s$ or $S_0$ into each of the four expressions. This gives the quantitative estimate for $\mathcal T_{p,q}$ and proves its finiteness.</p>
<p>This proves the analytic diagram estimate used in Lemma III.6.16 at the critical dimension, for every spatial-weight placement. The combinatorial assertion that a particular coupled cut event has two edge-disjoint three-point witnesses is a separate obligation. Neither that assertion nor the interception and final decoupling steps of Lemma III.6.11 are inferred from this estimate.</p>


## A connection cut only by two sets together {#section-joint-cut-witnesses}

<a id="tag-RIH3" data-assertion="proposition" data-title="A joint vertex cut supplies two disjoint three-point witnesses"></a>
<p>Let $G$ be any graph, let $A,B$ be disjoint vertex sets, and suppose that $y$ is connected to $a$ in both $G\setminus A$ and $G\setminus B$, but not in $G\setminus(A\cup B)$. There exist $b\in A$, $c\in B$, and finite connected subgraphs $H_y,H_a$ containing $\{y,b,c\}$ and $\{a,b,c\}$, respectively, such that</p>
<div class="math-display">$$V(H_y)\cap V(H_a)=\{b,c\},\qquad E(H_y)\cap E(H_a)=\varnothing.$$</div>
<p><em>Proof.</em> Choose one finite path avoiding $A$ and another avoiding $B$, and let $G_0$ be their union. Choose an inclusion-minimal subset $T$ of $(A\cup B)\cap V(G_0)$ whose deletion separates $y$ from $a$ in $G_0$. Neither $T\subseteq A$ nor $T\subseteq B$ is possible, because the corresponding avoiding path would survive. Hence $T$ contains vertices $b\in A$ and $c\in B$.</p>
<p>Let $U_y,U_a$ be the distinct components of $y,a$ in $G_0\setminus T$. Every $t\in T$ has a neighbour in each of $U_y$ and $U_a$. Indeed, minimality provides a $y$–$a$ path after deleting $T\setminus\{t\}$; it must pass through $t$, and its two portions outside $t$ lie in those components. Join $y$ inside $U_y$ to neighbours of $b,c$, then add the two edges to $b,c$. This gives $H_y$. The same construction inside $U_a$ gives $H_a$. Their only common vertices are $b,c$, and they use no common edge.</p>
<p>The argument applies to infinite graphs because $G_0$ is finite. The hypotheses themselves exclude deleted endpoints and $y=a$. Applied to an open graph, it gives disjoint finite witnesses for the two increasing three-point events, which is exactly the form needed by BK.</p>

<a id="tag-1P14" data-assertion="theorem" data-title="The coupled joint-cut error is negligible at critical dimension"></a>
<p>Assume <a href="/tag/7GBI/">7GBI</a>, and for each $x,y$ use the independent copies and sets $A,B,C$ from <a href="/tag/DR5Q/">DR5Q</a>. Set</p>
<div class="math-display">$$\mathcal J(y,a)=\mathcal D_{A\cup B}(y,a)
\setminus\bigl(\mathcal D_A(y,a)\cup\mathcal D_C(y,a)\bigr),\qquad
W_q(S)=\sum_{z\in S}\|z\|^q.$$</div>
<p>For integers $p,q\geq0$, with zero powers equal to one,</p>
<div class="math-display">$$\begin{aligned}
&\sum_{x\in B_r}\sum_{y,a}\|y\|^p\,
\mathbf E_r\!\left[\mathbf1_{\{x\notin A\}}|A|\,|B|W_q(B)
\mathbf1_{\mathcal J(y,a)}\right]\\
&\qquad\leq\mathcal T_{p,q}(r)
\leq C_{p,q}V_r^3r^{11\alpha+p+q}(V_r^2+r^{-\alpha})
=o\bigl(|B_r|V_r^3r^{p+q}\chi_r^8\bigr),
\end{aligned}$$</div>
<p>where $\mathcal T_{p,q}$ is the finite diagram in <a href="/tag/BX1G/">BX1G</a>. Each expectation uses the three independent copies for the indicated roots.</p>
<p><em>Proof.</em> On $\mathcal J(y,a)$ there is a path in $\omega_y$ avoiding $A$ and another avoiding $C$. The second also avoids $B$, since $B\subseteq C$. Deleting $A\cup B$ destroys the connection. RIH3 therefore supplies $b\in A$, $c\in B\subseteq C$ and edge-disjoint three-point witnesses from $y$ and $a$ to $b,c$.</p>
<p>Replace $|B|W_q(B)$ by its upper bound $|C|W_q(C)$, drop the restriction on $x$, and sum over possible $b,c$ and over $z\in C$. The first two independent copies contribute the factors</p>
<div class="math-display">$$\mathbb E_r[|K_0|\mathbf1_{\{b\in K_0\}}],\qquad
\mathbb E_r[|K_x|\mathbf1_{\{c,z\in K_x\}}].$$</div>
<p>In the third copy, BK bounds the disjoint occurrence by $T_r(y,b,c)T_r(a,b,c)$. Countable approximation by finite edge witnesses justifies the same inequality on the lattice. Independence and Tonelli now give exactly $\mathcal T_{p,q}(r)$, including both spatial weights. BX1G proves the remaining estimates.</p>
<p>This proves the critical, $\alpha&lt;2$ case of Lemma III.6.16. The source's first sentence repeats the same path-avoidance condition twice; the <a href="/errata/hutchcroft-lrp-3/">provisional erratum</a> gives the two different conditions used here. The disjointness needed for BK is disjointness of edges; the witnesses share their marked vertices $b,c$. This argument does not address the interception event or the final decoupling estimates.</p>


## Root-cluster powers in the joint-cut bound {#section-powered-joint-cut}

<a id="tag-CWM1" data-assertion="theorem" data-title="The critical joint-cut estimate holds with arbitrary root-cluster powers"></a>
<p>Under <a href="/tag/7GBI/">7GBI</a>, let $i,j,p,q\geq0$ be integers, put $s=p+q$ and $n=i+j+1$, and use $A_i,C_j$ from <a href="/tag/DVHL/">DVHL</a>. Then</p>
<div class="math-display">$$\begin{aligned}
\mathcal T^{i,j}_{p,q}(r)
&:=\sum_{x,y,a,b,c,z}A_i(b)C_j(x,c,z)T_r(y,b,c)T_r(a,b,c)\|y\|^p\|z\|^q\\
&\leq C_{i,j,p,q}V_r^n r^{(2n+5)\alpha+s}(V_r^2+r^{-\alpha})
=o\bigl(|B_r|V_r^n r^s\chi_r^{2n+2}\bigr).
\end{aligned}$$</div>
<p>In the coupling of DR5Q, with $\mathcal J=\mathcal D_{A\cup B}\setminus(\mathcal D_A\cup\mathcal D_C)$, this diagram bounds</p>
<div class="math-display">$$\sum_{x\in B_r}\sum_{y,a}\|y\|^p\,
\mathbf E_r\!\left[\mathbf1_{\{x\notin A\}}|A|^i|B|^jW_q(B)
\mathbf1_{\mathcal J(y,a)}\right].$$</div>
<p><em>Proof.</em> In the notation of <a href="/tag/BX1G/">BX1G</a>, the four spatial-weight sums are</p>
<div class="math-display">$$U_{i+1,s}m_{j+2}S_0,\qquad
m_{i+1}m_{j+2}S_s,\qquad
m_{i+1}m_{j+2}S_s,\qquad
m_{i+1}U_{j+2,s}S_0.$$</div>
<p>The identities follow by the same fixed-root summations as in DVHL, with the two three-point functions replacing the path event. BX1G gives $S_s\leq C_s r^{3\alpha+s}(V_r^2+r^{-\alpha})$. Combine this with the moment bounds in DVHL. The result is finite and has the claimed order, including when a root-cluster exponent is zero.</p>
<p>On the coupled joint-cut event, <a href="/tag/RIH3/">RIH3</a> gives edge-disjoint three-point witnesses with $b\in A$ and $c\in B\subseteq C$. Monotonicity of the nonnegative cluster weight, independence, and BK give the diagram exactly as in <a href="/tag/1P14/">1P14</a>. This proves the coupled bound. No extra factor from the third cluster is included in this assertion.</p>



## Products of higher marked kernels {#section-higher-marked-kernels}

<a id="tag-RT01" data-assertion="theorem" data-title="Higher marked-kernel products retain two extra vertex factors"></a>
<p>Assume <a href="/tag/7GBI/">7GBI</a>. Write $X=|K_0|$, $W_s(K)=\sum_{v\in K}\|v\|^s$, with $W_0(K)=|K|$, and set</p>
<div class="math-display">$$Q_{a,s}(u)=\mathbb E_r[X^a\mathbf1_{\{u\in K_0\}}W_s(K_0)]
\qquad(a,s\geq0\text{ integers}).$$</div>
<p>For every fixed real $2\leq q&lt;3$ and integer $s\geq0$,</p>
<div class="math-display">$$\sum_u Q_{0,s}(u)^q\leq C_{q,s}V_r^q r^{3\alpha+qs}.$$</div>
<p>Consequently, for every fixed pair of nonnegative integers $a,b$,</p>
<div class="math-display">$$\mathcal S_{a,b;s}(r):=\sum_u Q_{a,s}(u)Q_{b,0}(u)
\leq C_{a,b,s}V_r^{a+b+2}r^{(2a+2b+3)\alpha+s}.$$</div>
<p>These bounds hold for all sufficiently large $r$, with constants depending on the fixed orders. In particular the term $u=0$ is included.</p>
<p><em>Proof.</em> For $u\ne0$, put $D=\|u\|$. By <a href="/tag/2CQ5/">2CQ5</a>,</p>
<div class="math-display">$$Q_{0,s}(u)\leq C_s r^{\alpha+s}V_DD^{-\alpha}h_s(D/r),$$</div>
<p>where $h_s$ has every polynomial decay rate. Choose $\eta&gt;0$ so that $q(\alpha+\eta)&lt;3\alpha$. The ratio bound <a href="/tag/121D/">121D</a> gives $V_D\leq C V_r(r/D)^\eta$ below $r$ and $V_D\leq C V_r(D/r)^\eta$ above $r$. As in BX1G, the constant can absorb distances between the shortest nonzero lattice distance and a fixed large radius. Summing in dyadic annuli, using $d=3\alpha$, yields</p>
<div class="math-display">$$\sum_{u\ne0}Q_{0,s}(u)^q
\leq C V_r^q r^{q(\alpha+s)}r^{3\alpha-q\alpha}
=C V_r^q r^{3\alpha+qs}.$$</div>
<p>The strict inequality in the choice of $\eta$ makes the inner annuli summable; the rapid envelope handles the outer annuli. At $u=0$, YU52 gives $Q_{0,s}(0)=O(r^{\alpha+s})$. Since <a href="/tag/5J3U/">5J3U</a> gives $V_r\geq c/\sqrt{\log(2+r)}$ and $(3-q)\alpha&gt;0$, this diagonal contribution also satisfies the claimed bound.</p>
<p>Put $T=a+b$, choose an integer $k&gt;2T$, and let</p>
<div class="math-display">$$q=\frac{2k-T}{k-T}\in[2,3),\qquad
B(u)=Q_{0,0}(u)+r^{-s}Q_{0,s}(u).$$</div>
<p>The first bound implies $\sum_u B(u)^q\leq C V_r^q r^{3\alpha}$. Hölder under the measure $\mathbf1_{\{u\in K_0\}}W_s(K_0)\,d\mathbb P_r$ gives</p>
<div class="math-display">$$Q_{a,s}(u)\leq Q_{0,s}(u)^{1-a/k}Q_{k,s}(u)^{a/k}.$$</div>
<p>Use the analogous inequality for $Q_{b,0}$. Hölder in the vertex variable, with reciprocal exponents $1-T/k$, $a/k$ and $b/k$, then gives</p>
<div class="math-display">$$\begin{aligned}
\mathcal S_{a,b;s}
&\leq r^{s(1-a/k)}
\left(\sum_u B(u)^q\right)^{1-T/k}
\left(\sum_u Q_{k,s}(u)\right)^{a/k}
\left(\sum_u Q_{k,0}(u)\right)^{b/k}.
\end{aligned}$$</div>
<p>A factor with exponent zero is omitted. The higher kernels enter through their sums, for which Tonelli gives the exact identity</p>
<div class="math-display">$$\sum_u Q_{k,s}(u)=\mathbb E_r[X^{k+1}W_s(K_0)]
\leq C_{k,s}V_r^{k+1}r^{(2k+3)\alpha+s}.$$</div>
<p>The inequality is <a href="/tag/AR3F/">AR3F</a> with its volume input supplied by <a href="/tag/RM79/">RM79</a>. Substitution gives the vertex-factor exponent</p>
<div class="math-display">$$q(1-T/k)+(k+1)T/k=T+2,$$</div>
<p>and the radius exponent $(2T+3)\alpha+s$, as required. For $a=b=0$, the same calculation has $q=2$ and uses only the first bound. All orders, including $k$, are fixed before taking $r\to\infty$.</p>

## Cluster weights on disjoint witnesses {#section-weighted-disjoint-witnesses}

<a id="tag-AK2E" data-assertion="proposition" data-title="Extra cluster marks split between two disjoint connected witnesses"></a>
<p>Consider independent bond percolation on a countable graph, with finite clusters almost surely. For vertices $y,a,b,c$, let</p>
<div class="math-display">$$\mathcal E(y,a;b,c)=\{y\leftrightarrow b\leftrightarrow c\}
\circ\{a\leftrightarrow b\leftrightarrow c\},\qquad
G_t(y;b,c)=\mathbb E[|K_y|^t\mathbf1_{\{b,c\in K_y\}}].$$</div>
<p>Disjoint occurrence requires finite edge-disjoint witnesses. Vertices in this display may coincide. For every integer $t\geq0$,</p>
<div class="math-display">$$\mathbb E[|K_y|^t\mathbf1_{\mathcal E(y,a;b,c)}]
\leq\sum_{l=0}^t\binom tl G_l(y;b,c)G_{t-l}(a;b,c),$$</div>
<p>as an inequality of nonnegative integrals; the moments need not be finite.</p>
<p><em>Proof.</em> On $\mathcal E$, choose finite connected open witnesses $F_1,F_2$ for the two events. They have disjoint edge sets and share at least $b$. Given any ordered tuple $d_1,\ldots,d_t\in K_y$, take a finite connected open graph containing both witnesses and these marks. Contract $V(F_1)\cup V(F_2)$ to a single root and choose a spanning tree. On lifting the tree, its edges outside the witnesses form branches, each attached to their union at exactly one vertex. Assign each branch to a witness containing its attachment vertex; at a shared vertex either choice is allowed. A mark already in the witness union is assigned to a witness containing it.</p>
<p>Adding the assigned branches leaves each witness connected and their edge sets disjoint. Thus, for some subset $I\subseteq\{1,\ldots,t\}$, the configuration belongs to</p>
<div class="math-display">$$\{y,b,c,d_i\ (i\in I)\text{ lie in one cluster}\}
\circ
\{a,b,c,d_i\ (i\notin I)\text{ lie in one cluster}\}.$$</div>
<p>Repeated marks cause no problem: their labels can all be assigned to the same branch or witness. The union over all labelled subsets $I$ includes this assignment. The construction also permits singleton witnesses, whose edge sets are empty.</p>
<p>Apply a union bound over $I$ and <a href="/tag/JRCI/">countable BK</a> to each pair of enlarged connection events. Sum over all ordered tuples. For $|I|=l$, the two sets of summation variables separate, and their probability sums are exactly $G_l(y;b,c)$ and $G_{t-l}(a;b,c)$. There are $\binom tl$ such subsets. Tonelli justifies every step, including infinite sums. At $t=0$ this reduces to ordinary BK.</p>

## Joint cuts of target tuples {#section-tuple-joint-cuts}

<a id="tag-B9Z5" data-assertion="theorem" data-title="The critical joint-cut gain holds for every target-tuple power"></a>
<p>Assume <a href="/tag/7GBI/">7GBI</a>. Use $A_i,C_j$ from <a href="/tag/DVHL/">DVHL</a>, and set</p>
<div class="math-display">$$F_t(y,a;b,c)=\mathbb E_r[|K_y|^t\mathbf1_{\mathcal E(y,a;b,c)}].$$</div>
<p>For fixed integers $i,j,t,p,q\geq0$, put $s=p+q$ and $n=i+j+t+1$. Then</p>
<div class="math-display">$$\begin{aligned}
\mathcal J^{i,j,t}_{p,q}(r)
&:=\sum_{x,y,a,b,c,z}A_i(b)C_j(x,c,z)F_t(y,a;b,c)\|y\|^p\|z\|^q\\
&\leq C_{i,j,t,p,q}V_r^{n+2}r^{(2n+5)\alpha+s}
=o\bigl(|B_r|V_r^n r^s\chi_r^{2n+2}\bigr).
\end{aligned}$$</div>
<p>All sums are finite. In the coupling of <a href="/tag/DR5Q/">DR5Q</a>, this diagram bounds the single-target joint-cut term</p>
<div class="math-display">$$\sum_{x\in B_r}\sum_{y,a}\|y\|^p\,
\mathbf E_r\!\left[\mathbf1_{\{x\notin A\}}|A|^i|B|^jW_q(B)|H|^t
\mathbf1_{\mathcal J(y,a)}\right],\qquad
\mathcal J=\mathcal D_{A\cup B}\setminus(\mathcal D_A\cup\mathcal D_C).$$</div>
<p>More generally, for $m\geq1$ let $\mathcal D_S^{[m]}(y,\mathbf a)$ be the event that $\mathbf a\in H^m$ but $\mathbf a\notin H_S^m$, where $H_S$ is the third cluster after deleting $S$. Define</p>
<div class="math-display">$$\mathcal J^{[m]}=\mathcal D_{A\cup B}^{[m]}
\setminus(\mathcal D_A^{[m]}\cup\mathcal D_C^{[m]}).$$</div>
<p>With $N=i+j+m$, the full tuple contribution satisfies</p>
<div class="math-display">$$\begin{aligned}
&\sum_{x\in B_r}\sum_{y,\mathbf a}\|y\|^p\,
\mathbf E_r\!\left[\mathbf1_{\{x\notin A\}}|A|^i|B|^jW_q(B)
\mathbf1_{\mathcal J^{[m]}(y,\mathbf a)}\right]\\
&\qquad\leq C_{i,j,m,p,q}V_r^{N+2}r^{(2N+5)\alpha+s}
=o\bigl(|B_r|V_r^N r^s\chi_r^{2N+2}\bigr).
\end{aligned}$$</div>
<p><em>Proof.</em> By <a href="/tag/AK2E/">AK2E</a>, replace $F_t$ by the sum of $\binom tl G_l(y;b,c)G_{t-l}(a;b,c)$. Fix $l$ and write $h=t-l$. The four-weight inequality of SE64 reduces the spatial factor to a constant times</p>
<div class="math-display">$$\|b\|^s+\|y-b\|^s+\|y-c\|^s+\|z-c\|^s.$$</div>
<p>Indeed $y=b+(y-b)$ and $z=b+(y-b)-(y-c)+(z-c)$; the triangle inequality and the power-mean bound give this estimate also when one or both exponents are zero. Put $m_k=\mathbb E_rX^k$ and $U_{k,s}=\mathbb E_r[X^{k-1}W_s(K_0)]$. The four resulting sums are</p>
<div class="math-display">$$U_{i+1,s}m_{j+2}\mathcal S_{l,h;0},\qquad
m_{i+1}m_{j+2}\mathcal S_{l,h;s},\qquad
m_{i+1}m_{j+2}\mathcal S_{l,h;s},\qquad
m_{i+1}U_{j+2,s}\mathcal S_{l,h;0}.$$</div>
<p>To see the kernel factors, translate $b$ to zero and write $u=c-b$. Summing $y-b$ in $G_l$ gives $Q_{l,0}(u)$, or $Q_{l,s}(u)$ when that mark carries the weight. Summing $a-b$ gives $Q_{h,0}(u)$. For the weight on $y-c$, exchange the two fixed roots and use reflection invariance of the radial law. The remaining root sums give $m_{i+1},m_{j+2}$ or their weighted versions. These are identities of nonnegative sums, so their use does not presuppose convergence.</p>
<p>The moment estimates give $m_k=O(V_r^{k-1}r^{(2k-1)\alpha})$ and $U_{k,s}=O(V_r^{k-1}r^{(2k-1)\alpha+s})$. By <a href="/tag/RT01/">RT01</a>, the kernel product is $O(V_r^{t+2}r^{(2t+3)\alpha+s})$. Each displayed term is therefore $O(V_r^{i+j+t+3}r^{(2i+2j+2t+7)\alpha+s})$. Summing the finitely many binomial terms proves the diagram bound and finiteness. Since $|B_r|\asymp r^{3\alpha}$, $\chi_r\asymp r^\alpha$ and $V_r\to0$, it also proves the little-o assertion.</p>
<p>On a coupled single-target joint cut, <a href="/tag/RIH3/">RIH3</a> supplies edge-disjoint three-point witnesses with $b\in A$ and $c\in B\subseteq C$. Replace $|B|^jW_q(B)$ by $|C|^jW_q(C)$, sum over $b,c,z$, and use independence of the three copies. Keeping $|H|^t$ inside the third-copy expectation gives exactly the diagram above. No independent replacement of this factor is made.</p>
<p>Finally, on $\mathcal J^{[m]}$ every coordinate survives each separate deletion, while at least one coordinate fails after deleting $A\cup B$. That coordinate belongs to the single-target event $\mathcal J$. Hence, pointwise,</p>
<div class="math-display">$$\sum_{\mathbf a\in H^m}\mathbf1_{\mathcal J^{[m]}(y,\mathbf a)}
\leq m|H|^{m-1}\sum_{a\in H}\mathbf1_{\mathcal J(y,a)}.$$</div>
<p>This counts labelled positions and allows repeated targets. Apply the single-target estimate with $t=m-1$ to finish the proof.</p>
<p>Together with <a href="/tag/6IJQ/">6IJQ</a>, this controls both redundancy and joint cuts for every cluster power in the transported interaction JG0C, including the source case $(p_1,p_2,p_3)=(0,1,2)$. The additional factor is $O(V_r^2)$. Interception and final decoupling are still needed to derive the deficit equations in ENWJ; those equations remain explicit hypotheses there.</p>
