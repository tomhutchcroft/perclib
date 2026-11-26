---
{
  "id": "binary-tree-percolation",
  "title": "Percolation on the rooted binary tree",
  "subtitle": "Exact cluster laws and critical asymptotics",
  "kind": "model",
  "category": "Models",
  "summary": "The root cluster is a Binomial(2,p) family tree. Its finite-size law is Catalan, giving exact critical volume and intrinsic-arm asymptotics. The finite-branching extension gives depth recursions and retains the deterministic one-child exception.",
  "context": [
    "The infinite rooted tree in which every vertex has two distinguished children.",
    "Independent bond percolation with homogeneous parameter $p\\in[0,1]$.",
    "The root cluster $K$ includes the root.",
    "The final sections allow a finite number k of children; the preceding binary-tree statements retain k=2."
  ],
  "related": [
    "branching-processes",
    "connectivity",
    "susceptibility",
    "exploration"
  ],
  "sourceIds": ["hutchcroft-book", "perclib-regular-tree", "perclib-tree-recursion", "perclib-train5-binary-tree", "perclib-train5-binary-arm", "perclib-train5-binary-catalan", "perclib-binary-tree-asymptotics", "perclib-abelian-sums", "perclib-binary-tree-moments", "perclib-binary-tree-moment-law"],
  "aliases": [
    "binary tree",
    "Catalan",
    "critical tree",
    "intrinsic one arm",
    "mean field",
    "regular rooted tree",
    "finite branching",
    "depth recursion",
    "deterministic critical exception"
  ],
  "prototypeUses": []
}
---

## The branching representation {#section-branching}

<a id="tag-CQYY" data-assertion="proposition" data-title="Binary-tree cluster law and its phase transition"></a><p>The generation sizes of the root cluster form a Galton–Watson process with offspring law $\operatorname{Bin}(2,p)$. Consequently the root critical probability is $1/2$, and</p><div class="math-display">$$\mathbb P_p(|K|=\infty)=\begin{cases}0,&amp;0\leq p\leq\tfrac12,\\1-\left(\frac{1-p}{p}\right)^2,&amp;\tfrac12&lt;p\leq1.\end{cases}$$</div><p>For $p&lt;1/2$, $\mathbb E_p|K|=(1-2p)^{-1}$; for $p\geq1/2$ this expectation is infinite.</p><p><em>Proof.</em> The two child edges of each vertex are independent, and different vertices have disjoint sets of child edges. Every reached vertex therefore has an independent $\operatorname{Bin}(2,p)$ number of reached children. Its mean is $2p$, so the extinction and expectation statements follow from <a href="#/branching-processes">branching-process theory</a>. The offspring generating function is $\phi(s)=(1-p+ps)^2$. For $p&gt;0$, its fixed points are $1$ and $((1-p)/p)^2$; the extinction probability is the smaller fixed point in $[0,1]$. At $p=0$ the cluster is the singleton root.</p><p>This is the rooted tree with two children at every vertex, not a tree where the root has three neighbours. Changing the root degree changes the root-cluster distribution and its constants.</p>

## The finite-cluster distribution {#section-catalan}

<a id="tag-9K6O" data-assertion="proposition" data-title="Catalan law for finite root clusters"></a><p>For every integer $n\geq1$,</p><div class="math-display">$$\mathbb P_p(|K|=n)=\frac1{n+1}\binom{2n}{n}p^{n-1}(1-p)^{n+1}.$$</div><p>At the endpoints the formula uses $0^0=1$.</p><p><em>Proof.</em> A fixed connected subtree containing the root and having $n$ vertices has $n-1$ internal edges. Its vertices have $2n$ child slots altogether, of which $n-1$ lead to vertices of the subtree; hence it has $n+1$ child edges leaving it. It is exactly the open root cluster when the internal edges are open and those boundary edges are closed, an event of probability $p^{n-1}(1-p)^{n+1}$.</p><p>Let $C_n$ count these subtrees and put $C(z)=\sum_{n\geq1}C_nz^n$. Decomposition at the two distinguished children, allowing either subtree to be empty, gives</p><div class="math-display">$$C(z)=z(1+C(z))^2,\qquad C(z)=\frac{1-2z-\sqrt{1-4z}}{2z}.$$</div><p>The branch with zero constant term is forced. Expanding the square root by the binomial series gives $C_n=(n+1)^{-1}\binom{2n}{n}$. The cluster events for different subtrees are disjoint, so summing their common probability proves the formula.</p>

<a id="tag-AAZS" data-assertion="corollary" data-title="Exact critical binary-tree volume asymptotics"></a><p>At $p=1/2$, as $n\to\infty$,</p><div class="math-display">$$\mathbb P_{1/2}(|K|=n)\sim\frac1{\sqrt\pi}n^{-3/2},\qquad\mathbb P_{1/2}(|K|\geq n)\sim\frac2{\sqrt\pi}n^{-1/2}.$$</div><p><em>Proof.</em> The exact mass is $C_n4^{-n}$, and Stirling's formula gives $C_n\sim4^n/(\sqrt\pi n^{3/2})$. Critical extinction excludes an atom at infinite size. Summing the asymptotic masses and using $\sum_{k\geq n}k^{-3/2}\sim2n^{-1/2}$ gives the tail equivalent.</p>

## Intrinsic distance and connection probabilities {#section-distance}

<a id="tag-NDIC" data-assertion="proposition" data-title="Binary-tree critical intrinsic arm and two-point formula"></a><p>Let $r_n$ be the probability at $p=1/2$ that the root cluster reaches generation $n$. Then $r_0=1$ and</p><div class="math-display">$$r_{n+1}=r_n-\frac14r_n^2,\qquad r_n\sim\frac4n.$$</div><p>For any two vertices $x,y$ and any $p\in[0,1]$, their connection probability is $p^{d(x,y)}$, where $d$ is distance in the underlying tree and $p^0=1$.</p><p><em>Proof.</em> Each of the two child edges is open and continues for $n$ more generations with probability $r_n/2$, independently of the other child. Thus $r_{n+1}=1-(1-r_n/2)^2$. The critical offspring variance is $1/2$, so the branching-process survival asymptotic gives $r_n\sim4/n$. Finally, the unique path from $x$ to $y$ has $d(x,y)$ edges, and connection occurs exactly when all of them are open.</p><p>For a reached vertex, its distance from the root inside the cluster equals its distance in the underlying tree, because the path is unique. These intrinsic statements are not Euclidean spatial decay estimates.</p><p>The near-critical cutoff below specifies a joint-limit regime for these asymptotics.</p>

## The near-critical cutoff {#section-cutoff}

<a id="tag-V5OZ" data-assertion="proposition" data-title="Binary-tree finite-cluster cutoff with an explicit joint-limit regime"></a><p>For $0&lt;p&lt;1$ and large $n$,</p><div class="math-display">$$\mathbb P_p(|K|=n)\sim\frac{1-p}{p\sqrt\pi}\,n^{-3/2}[4p(1-p)]^n,$$</div><p>with relative error depending only on $n$, hence uniformly in $p\in(0,1)$. In particular, if $p_n=1/2+\varepsilon_n$, $\varepsilon_n\to0$, and $n\varepsilon_n^4\to0$, then</p><div class="math-display">$$\mathbb P_{p_n}(|K|=n)\sim\frac1{\sqrt\pi}n^{-3/2}\exp(-4n\varepsilon_n^2).$$</div><p><em>Proof.</em> The exact Catalan law can be written as</p><div class="math-display">$$\mathbb P_p(|K|=n)=C_n4^{-n}\frac{1-p}{p}[4p(1-p)]^n.$$</div><p>The first asymptotic follows from $C_n4^{-n}\sim n^{-3/2}/\sqrt\pi$, whose relative error is independent of $p$. For the second, use $4p_n(1-p_n)=1-4\varepsilon_n^2$ and</p><div class="math-display">$$n\log(1-4\varepsilon_n^2)=-4n\varepsilon_n^2+O(n\varepsilon_n^4).$$</div><p>The error tends to zero by hypothesis, and $(1-p_n)/p_n\to1$. The exponential factor becomes appreciably smaller when $n$ is of order $|p-1/2|^{-2}$, giving the finite-cluster cutoff scale. These are unconditional probabilities of finite cluster sizes; on the supercritical side the remaining mass is at infinite size.</p>

## Moments across the cutoff {#section-moments}

<a id="tag-GGVG" data-assertion="proposition" data-title="Near-critical finite-cluster moments on the rooted binary tree"></a>
<p>For $s\geq0$ and $0&lt;p&lt;1$, define the finite-cluster moment by the sum</p>
<div class="math-display">$$M_s(p)=\sum_{n\geq1}n^s\mathbb P_p(|K|=n).$$</div>
<p>Put $\lambda(p)=-\log[4p(1-p)]$. As $p\to1/2$ with $p\neq1/2$, from either side,</p>
<div class="math-display">$$M_s(p)\sim\frac{\Gamma(s-1/2)}{\sqrt\pi}\lambda(p)^{-(s-1/2)}\quad(s&gt;1/2),\qquad M_{1/2}(p)\sim\frac1{\sqrt\pi}\log\frac1{\lambda(p)}.$$</div>
<p>For $0\leq s&lt;1/2$, instead $M_s(p)\to M_s(1/2)&lt;\infty$. Since $\lambda(p)\sim4(p-1/2)^2$, for every fixed $s&gt;1/2$ we also have</p>
<div class="math-display">$$\frac{M_{s+1}(p)}{M_s(p)}\sim\frac{s-1/2}{4(p-1/2)^2}.$$</div>
<p><em>Proof.</em> Write $a_n=C_n4^{-n}$, so $a_n\sim n^{-3/2}/\sqrt\pi$. The exact Catalan law gives</p>
<div class="math-display">$$M_s(p)=\frac{1-p}{p}\sum_{n\geq1}n^sa_ne^{-\lambda(p)n}.$$</div>
<p>For $s&gt;1/2$, set $a=s-1/2&gt;0$. The elementary Laplace sum has asymptotic</p>
<div class="math-display">$$\lambda^a\sum_{n\geq1}n^{a-1}e^{-\lambda n}=\lambda\sum_{n\geq1}(\lambda n)^{a-1}e^{-\lambda n}\longrightarrow\int_0^\infty t^{a-1}e^{-t}\,dt=\Gamma(a).$$</div>
<p>To justify the improper Riemann sum, first restrict to $\delta\leq\lambda n\leq R$. The omitted portion near zero is bounded by a constant times $\delta^a$, using $\sum_{n\leq N}n^{a-1}\leq C_aN^a$. The portion above $R$ tends uniformly to zero as $R\to\infty$, by exponential decay. On the middle interval ordinary Riemann sums apply. For any $\varepsilon&gt;0$, the asymptotic for $a_n$ bounds all sufficiently large summands between $(1\pm\varepsilon)n^{s-3/2}/\sqrt\pi$; finitely many remaining terms are negligible compared with $\lambda^{-a}$. Let $\varepsilon\downarrow0$ and use $(1-p)/p\to1$.</p>
<p>At $s=1/2$, the same comparison uses the exact sum $\sum_{n\geq1}e^{-\lambda n}/n=-\log(1-e^{-\lambda})\sim\log(1/\lambda)$. For $s&lt;1/2$, the bound $a_n\leq Cn^{-3/2}$ makes $\sum n^sa_n$ summable, so dominated convergence gives the finite limit. Finally $4p(1-p)=1-4(p-1/2)^2$, and $\Gamma(s+1/2)=(s-1/2)\Gamma(s-1/2)$ gives the moment-ratio equivalent.</p>
<p>Below criticality these are ordinary moments of $|K|$. Above criticality, $M_s$ omits the atom at infinite size; for every $s&gt;0$ the unconditional moment is infinite. Conditioning on a finite cluster divides every $M_s$ by the extinction probability, which tends to one, and leaves ratios of consecutive moments unchanged. In particular, the subcritical ratio $M_2/M_1\sim[8(p-1/2)^2]^{-1}$ gives a precise moment interpretation of the gap exponent two. This is a tree-model computation, not a proof of a percolation exponent in Euclidean space.</p>


## A finite number of children {#section-regular-tree}

<p>Let $k\geq0$ be an integer. Represent the rooted tree with $k$ distinguished children at each vertex by finite words over $\{1,\ldots,k\}$, with the empty word $o$ as root and children $aw$ of a word $w$. Depth is word length, and deleting initial letters gives the ancestral chain. The root has degree $k$, and every other vertex has degree $k+1$. For $k=0$ the root is the only vertex.</p>
<p>Give every tree edge opening probability $p\in[0,1]$, every other non-diagonal pair probability zero, and diagonal pairs arbitrary probabilities. Let $A_n$ be the event that the root is connected to a word of length $n$, and write $r_n=\mathbb P_p(A_n)$.</p>

<a id="tag-GGH2" data-assertion="proposition" data-title="Ancestral witnesses give measurable depth events and their tree union bound"></a>
<p>On a configuration whose open graph lies in this tree, a word is connected to the root exactly when every edge of its ancestral chain is open. The root cluster is infinite exactly when it reaches every depth. Under the stated product law,</p>
<div class="math-display">$$r_0=1,\qquad r_n\leq(kp)^n,\qquad
\mathbb P_p(|K(o)|=\infty)=\lim_{n\to\infty}r_n.$$</div>
<p>In particular, $kp&lt;1$ implies almost-sure finiteness of the root cluster. The convention at $n=0$ is $(kp)^0=1$, including $kp=0$.</p>
<p><em>Proof.</em> The tree has a unique path from the root to a word, namely its ancestral chain. Opening those edges suffices for connection in any configuration; when the open graph lies in the tree, every root connection must use them. Each bounded collection of levels is finite. An infinite root cluster therefore reaches arbitrarily deep words, whose ancestral paths pass through every earlier level. Conversely, reaching every level supplies infinitely many vertices in the cluster.</p>
<p>The vertex set is countable, so $A_n$ is measurable by the finite-path description of connection. Let $B_n$ be the event that at least one word of length $n$ has its ancestral chain open. This event depends on finitely many tree-edge coordinates and is a measurable cylinder. Almost surely the open graph lies in the tree by <a href="/tag/XHFN/">the support argument</a>, so $A_n=B_n$ almost surely. There are $k^n$ possible words, each with $n$ distinct ancestral edges. The union bound gives $r_n\leq k^np^n$. Finally $B_{n+1}\subseteq B_n$, and their intersection is the infinite-root-cluster event on the support event. Continuity from above gives the limit; the bound tends to zero when $kp&lt;1$.</p>
<p>Diagonal coordinates are irrelevant throughout. The source's deterministic path statements use a configuration contained in the raw tree edge set; erasing its loops gives the graph-containment version used here. Neither the tree profile nor this comparison imposes a condition on the original diagonal marginals.</p>

## Depth recursion and the endpoint exception {#section-tree-recursion}

<a id="tag-UHVH" data-assertion="theorem" data-title="Finite-branching depth recursion and the complete rooted-tree percolation criterion"></a>
<p>For every $k\geq0$ and $p\in[0,1]$,</p>
<div class="math-display">$$r_{n+1}=1-(1-pr_n)^k.$$</div>
<p>For $k\geq1$,</p>
<div class="math-display">$$\mathbb P_p(|K(o)|=\infty)&gt;0
\quad\Longleftrightarrow\quad kp&gt;1\ \text{ or }\ p=1.$$</div>
<p>Thus the critical bond probability is $1/k$. At that probability the root cluster is finite almost surely for $k\geq2$, while for $k=1$ and $p=1$ the entire ray is open. When $k=0$, the root cluster is always a singleton.</p>
<p><em>Proof.</em> A word of length $n+1$ is uniquely $ua$, where $|u|=n$ and $a$ is its last letter. Its ancestral path consists of the edge from $o$ to $a$ and the image of the ancestral path of $u$ under $v\mapsto va$. This injection preserves and reflects tree edges, so the subtree rooted at $a$ has the same product law as the whole tree after relabelling. The root edge is distinct from its internal edges.</p>
<p>For each of the $k$ children, opening its root edge and then reaching depth $n$ in its subtree has probability $pr_n$. These events depend on disjoint coordinate blocks for distinct children. Taking the probability that all fail gives $(1-pr_n)^k$, proving the recursion. For $k=0$ this empty product is one. The law calculation may be made after <a href="/tag/LNKT/">diagonal erasure</a>, leaving the original graph events unchanged.</p>
<p>Put $g(s)=1-(1-ps)^k$ and $\theta=\lim r_n$. Since $g$ is continuous, $\theta=g(\theta)$. The map is increasing on $(-\infty,1]$: if $s\leq t\leq1$, then $1-ps\geq1-pt\geq0$. Every fixed point in $[0,1]$ lies below all $r_n$, by induction from $r_0=1$, so $\theta$ is the largest such fixed point.</p>
<p>Suppose first that $p&lt;1$ and $kp\leq1$. For $k=1$, $g(s)=ps&lt;s$ when $s&gt;0$. For $k\geq2$ and $p&gt;0$, strict Bernoulli gives</p>
<div class="math-display">$$(1-ps)^k&gt;1-kps\qquad(0&lt;s\leq1),$$</div>
<p>hence $g(s)&lt;kps\leq s$. One way to see the strict inequality is to integrate the positive derivative $k[1-(1-x)^{k-1}]$ of $(1-x)^k-1+kx$ on $0&lt;x\leq1$. At $p=0$, $g=0$ directly. In every case zero is the only fixed point and $\theta=0$.</p>
<p>Now let $m=kp&gt;1$. For $0\leq x\leq1$,</p>
<div class="math-display">$$(1-x)^k\leq e^{-kx}\leq1-kx+\frac{(kx)^2}{2}.$$</div>
<p>The first inequality follows from $1-x\leq e^{-x}$; the second follows from the integral remainder $e^{-t}=1-t+\int_0^t(t-u)e^{-u}\,du$. Therefore $g(s)\geq ms-m^2s^2/2$ on $[0,1]$. Choose</p>
<div class="math-display">$$c=\min\left\{1,\frac{m-1}{m^2}\right\}&gt;0.$$</div>
<p>Then $g(c)\geq c$. Since $g$ is increasing and $r_0=1\geq c$, induction gives $r_n\geq c$ for every $n$, and $\theta\geq c&gt;0$. Finally, when $p=1$ and $k\geq1$, all tree edges are simultaneously open almost surely and the root cluster is infinite. This includes the deterministic one-child case at mean one.</p>
<p>This agrees with the <a href="/tag/BFM4/">branching-process extinction criterion</a>: the offspring law is $\operatorname{Bin}(k,p)$, whose only deterministic-one case is $k=1,p=1$. The <a href="/tag/UKY4/">generation expectation formula</a> also gives root susceptibility $(1-kp)^{-1}$ for $kp&lt;1$ and infinity for $kp\geq1$. These susceptibility conclusions are consequences of the existing branching theorem, not additional exports of the two tree modules.</p>
<p>For $k\geq2$ at $p=1/k$, the offspring variance is $1-1/k$. The existing <a href="/tag/8WO7/">critical survival asymptotic</a> therefore gives $r_n\sim2k/((k-1)n)$, recovering <a href="/tag/NDIC/">$4/n$ for the binary tree</a>. This asymptotic is an additional consequence; the source modules export the exact recursion and percolation criterion, not that asymptotic.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-trees/">23-contract inventory</a> records the deterministic word geometry, depth measurability, subtree transport, scalar inequalities and threshold result. The earlier binary-tree laws, constants and source occurrences are unchanged. The general statements retain both $k=0$ and the exceptional endpoint $k=1,p=1$ where applicable, and all new source correspondences await independent review and compiled association.</p>


## Summing the tree two-point function {#section-tree-sums}

<p>The word model gives a direct proof of the connection and susceptibility formulas, without first identifying the cluster as a branching process. Deleting the edge from $w$ to $bw$ separates the words ending in $bw$ from the rest of the tree: every other parent-child edge has both endpoints on the same side. Thus every edge is a bridge. Deleting initial letters connects each word to the root, so the graph is connected and acyclic, including the singleton case $k=0$.</p>
<p>Under the profile specified in the finite-branching section, the open graph lies in this tree almost surely. The <a href="/tag/8KVE/">unique-path formula</a> therefore gives, for every pair of vertices,</p>
<div class="math-display">$$\tau_p(x,y)=p^{d(x,y)}.$$</div>
<p>The distance from the root to a word is its length. There are $k^n$ words of length $n$, so grouping the nonnegative susceptibility sum by depth gives</p>
<div class="math-display">$$\chi_p(o)=\sum_w p^{|w|}=\sum_{n\geq0}(kp)^n
=\begin{cases}(1-kp)^{-1},&amp;kp&lt;1,\\\infty,&amp;kp\geq1.\end{cases}$$</div>
<p>No convergence assumption is needed for grouping a nonnegative sum. More generally, the same word count gives $\sum_w r^{|w|}=\sum_{n\geq0}(kr)^n$ for a nonnegative weight $r$. At $k=0$, only the empty word exists and the sum is one. These are root susceptibilities; the root has a different degree from the other vertices when $k\geq1$.</p>
<p>The binary survival formula can also be read directly from the depth recursion. Its decreasing sequence has a limit $\theta$ satisfying $\theta=1-(1-p\theta)^2$. For $p&gt;1/2$, put $c=(2p-1)/p^2$. Then $0&lt;c\leq1$ and $c$ is a fixed point of the recursion. Since the recursion map is increasing on $[0,1]$, induction from $r_0=1$ gives $r_n\geq c$. The limiting fixed-point equation is</p>
<div class="math-display">$$\theta\bigl(p^2\theta-(2p-1)\bigr)=0.$$</div>
<p>The lower bound excludes zero, so $\theta=c=1-((1-p)/p)^2$. The critical and subcritical cases follow from the finite-branching criterion above. Thus at $p=1/2$ the root cluster is finite almost surely but has infinite expectation; at $p=1$ the survival probability is one.</p>

## A direct critical-arm argument {#section-arm-reciprocals}

<p>The asymptotic in <a href="/tag/NDIC/">NDIC</a> follows from its scalar recursion alone. Suppose $x_0=1$ and $x_{n+1}=x_n-x_n^2/4$. Induction gives $0&lt;x_n\leq1$. Taking reciprocals yields</p>
<div class="math-display">$$\frac1{x_{n+1}}-\frac1{x_n}=\frac1{4-x_n},\qquad
\frac1{x_n}=1+\sum_{j=0}^{n-1}\frac1{4-x_j}.$$</div>
<p>Each summand lies between $1/4$ and $1/3$. Inverting the resulting bounds gives</p>
<div class="math-display">$$\frac3{n+3}\leq x_n\leq\frac4{n+4},$$</div>
<p>so $x_n\to0$. The summands consequently tend to $1/4$, and their Cesàro averages give $1/(nx_n)\to1/4$ as $n\to\infty$. Inversion proves $nx_n\to4$.</p>
<p>Apply this to the critical binary depth probabilities. The initial values are $r_1=3/4$ and $r_2=39/64$. The finite ancestral-path cylinders used in the source agree almost surely with the depth events by tree support; diagonal coordinates do not affect either event. This proves the binary constant directly. The finite-branching asymptotic with constant $2k/(k-1)$ stated above still uses the separate branching-process theorem.</p>

## Cluster shapes as sets of words {#section-word-shapes}

<p>Every finite root-cluster vertex set in the binary tree is nonempty and closed under deleting the first letter. Conversely, any finite set $C$ with these properties can be realized as a root cluster by opening its internal edges and closing its boundary. This is a statement about configurations; at $p=0$ or $p=1$, some of these configurations have probability zero. Closure forces the empty word into $C$. If $|C|=n$, its internal edges are the $n-1$ pairs joining each non-root word to its parent. Of its $2n$ child slots, exactly $n-1$ lead back into $C$, leaving $n+1$ boundary edges.</p>
<p>On the event that the open graph is contained in the tree, the root cluster equals $C$ exactly when all these internal edges are open and all boundary edges are closed. The forward implication follows from unique paths. For the converse, the internal paths reach every vertex of $C$, and any path leaving $C$ must first cross a boundary edge. The two edge sets are disjoint, and each slot determines a distinct edge because its endpoints have different lengths. Independence therefore gives the single-shape probability $p^{n-1}(1-p)^{n+1}$, including $p=0,1$. Arbitrary diagonal probabilities are allowed: erasing diagonal coordinates leaves every cluster unchanged.</p>
<p>Here is the correspondence behind the Catalan count in <a href="/tag/9K6O/">9K6O</a>. Associate the empty set to the empty ordered binary tree. For a node with left and right subtrees $L,R$, put</p>
<div class="math-display">$$\Phi(\operatorname{node}(L,R))
=\{o\}\cup\{u0:u\in\Phi(L)\}\cup\{u1:u\in\Phi(R)\}.$$</div>
<p>Appending the last letter places a word in the subtree of the corresponding child of the root, because parenthood deletes the first letter. The displayed union is disjoint and has one more element than the two subtree sets together. The map preserves the node count and produces a set closed under deleting first letters. Conversely, partition a nonempty such set into the root and the two last-letter classes, remove their last letters, and repeat. Both smaller sets have the same closure property. Induction on cardinality gives a unique ordered binary tree, proving the bijection.</p>
<p>Thus there are $C_n$ possible shapes of size $n$, and their disjoint cluster events all have the same probability. This recovers the Catalan law with no conditioning on finiteness. For example, the size-one probability is $(1-p)^2$, and the size-two probability is $2p(1-p)^3$. At $p=0$ the root is the entire cluster; at $p=1$ every finite-size probability is zero. Above criticality the sum of the finite-size masses is the extinction probability, not one.</p>
<p>The <a href="/coverage/sources/perclib-caed44f-trees/">twenty-declaration inventory</a> records the three newer tree modules separately from the earlier geometry and recursion sources. They include the exact binary laws and the critical arm limit. The critical volume asymptotics, joint near-critical cutoff and finite-cluster moment asymptotics proved earlier in this article are further deductions, not exports of these three modules. Their formal correspondence requires separate evidence.</p>


## An exact critical tail {#section-asymptotics-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-models/">asymptotic source</a> obtains the critical tail without estimating a sum of asymptotic terms. Put $b_n=\binom{2n}{n}4^{-n}$. The Catalan recurrence gives</p>
<div class="math-display">$$C_k4^{-k}=2(b_k-b_{k+1}).$$</div>
<p>Stirling's formula implies $b_n\sqrt n\to1/\sqrt\pi$, so $b_n\to0$. Telescoping therefore gives, for $n\geq1$,</p>
<div class="math-display">$$\mathbb P_{1/2}(|K|\geq n)=\sum_{k\geq n}C_k4^{-k}=2b_n\sim\frac2{\sqrt\pi}n^{-1/2}.$$</div>
<p>Critical extinction is needed in the first equality. The algebraic series identity also holds at $n=0$, but its value there is two: the formal Catalan term at zero is not the probability of an empty root cluster.</p>
<p>For the joint limit in <a href="/tag/V5OZ/">V5OZ</a>, the source uses the quantitative remainder $|\log(1-x)+x|\leq2x^2$ for $0\leq x\leq1/2$. With $x=4\varepsilon_n^2$, the error in the exponent is at most $32n\varepsilon_n^4$. This explains why $\varepsilon_n\to0$ alone does not suffice for the displayed Gaussian approximation. By contrast, the full Catalan approximation retains $[4p(1-p)]^n$ exactly; its relative error is independent of $p$, even when $p$ approaches an endpoint.</p>


## Identifying the moment series in the source {#section-abelian-source}

<p>The <a href="/coverage/sources/perclib-f51f639-binary-moments/">new moment sources</a> prove both the analytic equivalents in <a href="/tag/GGVG/">GGVG</a> and their identification with the finite-cluster law. Off criticality, the Catalan factor is at most one and $4p(1-p)&lt;1$, so a polynomial times a geometric sequence dominates the series for every real exponent. This convergence justifies converting the nonnegative integral over finite clusters into the displayed real series. The integral is set to zero on infinite clusters; it is not the unconditional positive moment above criticality, nor the moment conditional on extinction.</p>
<p>For the analytic step, the source compares coefficients with the binomial series for $(1-x)^{-a}$. Euler's Gamma limit gives its coefficient asymptotic, and $1-e^{-\lambda}\sim\lambda$ then gives the power-law Abelian limit. The borderline exponent uses the logarithm series; below it, absolute summability gives dominated convergence. The finite-limit theorem in the source allows every real $s&lt;1/2$. Both sides of the critical parameter are included, and no Tauberian converse is used.</p>
