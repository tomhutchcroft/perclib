---
{
  "id": "lattice-path-growth",
  "title": "Lattice paths and the connective constant",
  "subtitle": "Submultiplicativity measures the exponential cost of avoiding intersections",
  "kind": "theorem",
  "category": "Models & geometry",
  "summary": "Self-avoiding path counts on the nearest-neighbour lattice have an exponential growth rate. Its reciprocal gives a sufficient small-parameter condition for finite bond susceptibility.",
  "context": ["The nearest-neighbour graph on $\\mathbb Z^d$, with $d$ a nonnegative integer.", "Paths are oriented vertex sequences with distinct vertices; their length is the number of edges.", "The connective-constant and percolation statements assume $d\\geq1$."],
  "related": ["directional-correlation-length", "bounded-degree-paths", "connectivity", "susceptibility", "subcritical-bound", "site-percolation"],
  "sourceIds": ["perclib-lattice", "perclib-connective-constant"],
  "aliases": ["self-avoiding walk", "SAW", "connective constant", "Fekete", "nearest-neighbour lattice", "lattice degree"],
  "prototypeUses": ["bounded-degree-paths"]
}
---

## Nearest-neighbour geometry {#section-geometry}

<a id="tag-6RWC" data-assertion="definition" data-title="The nearest-neighbour lattice graph"></a>
<p>The nearest-neighbour graph on $\mathbb Z^d$ joins $x$ to $y$ when $y-x=\pm e_i$ for some coordinate vector $e_i$. Equivalently, $\|y-x\|_1=1$, where $\|z\|_1=\sum_{i=1}^d|z_i|$. We write $B_n(x)$ for its closed graph ball of integer radius $n\geq0$.</p>

<a id="tag-8QCR" data-assertion="proposition" data-title="Degree, distance and symmetries of the lattice"></a>
<p>Every vertex has degree $2d$, the graph is connected, and</p>
<div class="math-display">$$d_{\mathbb Z^d}(x,y)=\|y-x\|_1.$$</div>
<p>Every ball is finite; in dimension one, $|B_n(x)|=2n+1$. Translations, coordinate permutations and independent changes of coordinate signs are graph automorphisms. These statements include $d=0$, when the graph consists of one vertex and has no edges.</p>
<p><em>Proof.</em> The $2d$ vectors $\pm e_i$ are distinct, giving the degree. Each step changes one coordinate by one, so any walk from $x$ to $y$ has length at least $\sum_i|y_i-x_i|$. Changing the coordinates successively towards those of $y$ attains this bound. The ball lies in the finite box $\prod_i[x_i-n,x_i+n]\cap\mathbb Z^d$; in dimension one it is exactly that interval. Each stated symmetry preserves the $\ell^1$ distance and hence adjacency.</p>

## Self-avoiding paths {#section-paths}

<a id="tag-RSRP" data-assertion="definition" data-title="Rooted self-avoiding path counts"></a>
<p>A self-avoiding path of length $n$ from $x$ is a sequence $(x_0,\ldots,x_n)$ of distinct vertices with $x_0=x$ and consecutive vertices adjacent. Let $c_n(x)$ count these paths, including the single length-zero path, and put $c_n=c_n(0)$. The endpoint is unrestricted, and different paths to the same endpoint are counted separately.</p>

<a id="tag-7DGG" data-assertion="proposition" data-title="Root invariance and submultiplicativity of lattice path counts"></a>
<p>The counts are finite, $c_0=1$, and $c_n(x)=c_n$ for every root. For all integers $n,m\geq0$,</p>
<div class="math-display">$$c_{n+m}\leq c_nc_m.$$</div>
<p>If $d\geq1$, then $c_n\geq1$ for every $n$ and</p>
<div class="math-display">$$c_n\leq2d(2d-1)^{n-1}\qquad(n\geq1).$$</div>
<p>For $d=0$, instead, $c_n=0$ for every $n\geq1$.</p>
<p><em>Proof.</em> There are at most $(2d)^n$ walks of positive length $n$ from a fixed root. Translation gives a bijection between paths from any two roots. Cut a path of length $n+m$ after its $n$th edge and translate its final segment so that the cut vertex becomes the origin. Both pieces are self-avoiding. Their ordered pair determines the original path: translate the second piece back to the endpoint of the first and concatenate, counting the joining vertex once. This is an injection into the pairs counted by $c_nc_m$. Some such pairs intersect after concatenation, which is why the inequality need not be an equality.</p>
<p>When $d\geq1$, the straight path $(0,e_1,\ldots,ne_1)$ supplies the lower bound. There are $2d$ choices for the first step and at most $2d-1$ for each subsequent step, since immediate reversal is forbidden. This gives the upper bound. In dimension zero no positive-length path exists.</p>

## The connective constant {#section-connective-constant}

<a id="tag-F3YB" data-assertion="theorem" data-title="Existence and bounds for the lattice connective constant"></a>
<p>For $d\geq1$, the limit</p>
<div class="math-display">$$\mu_d=\lim_{n\to\infty}c_n^{1/n}=\inf_{n\geq1}c_n^{1/n}$$</div>
<p>exists and satisfies $1\leq\mu_d\leq2d-1$. It is called the connective constant of $\mathbb Z^d$. In particular, $\mu_1=1$.</p>
<p><em>Proof.</em> Set $a_n=\log c_n$, so $a_0=0$ and $a_{n+m}\leq a_n+a_m$. Fix $k\geq1$ and write $n=qk+r$, with $0\leq r&lt;k$. Then</p>
<div class="math-display">$$a_n\leq q a_k+a_r,\qquad \limsup_{n\to\infty}\frac{a_n}{n}\leq\frac{a_k}{k}.$$</div>
<p>The remainder is bounded as $n$ varies because it ranges over finitely many indices. On the other hand, every $a_n/n$ with $n\geq1$ is at least $\inf_{k\geq1}a_k/k$. Taking the infimum in the upper bound proves convergence to this infimum; exponentiation gives the formula for $\mu_d$. The path bounds give $1\leq\mu_d\leq2d-1$, which force $\mu_1=1$.</p>
<p>The infimum formula gives the lower bound $c_n\geq\mu_d^n$, not an upper bound of that form. For every $\lambda&gt;\mu_d$, convergence does give $c_n\leq\lambda^n$ for all sufficiently large $n$. This distinction is what matters when summing path probabilities.</p>

## A bond-percolation consequence {#section-percolation}

<a id="tag-H35T" data-assertion="corollary" data-title="Finite susceptibility below the inverse connective constant"></a>
<p>Let $d\geq1$. Open nearest-neighbour bonds of $\mathbb Z^d$ independently, with probabilities $q_e\leq p\in[0,1]$, and give every other non-loop pair probability zero. If $p\mu_d&lt;1$, then for every root $x$,</p>
<div class="math-display">$$\chi_q(x)\leq\sum_{n\geq0}c_np^n&lt;\infty,$$</div>
<p>and almost surely every open cluster is finite. For homogeneous nearest-neighbour bond percolation, this implies $p_c\geq\mu_d^{-1}$, where $p_c=\inf\{p\in[0,1]:\mathbb P_p(|K(0)|=\infty)&gt;0\}$.</p>
<p><em>Proof.</em> Countability gives almost-sure containment of the simple open graph in the lattice host. Every connection has a self-avoiding open path as a witness. Its edges are distinct, so a path of length $n$ has probability at most $p^n$ of being open. Sum the union bound first over paths and then over endpoints. Each path has one endpoint, and the length-zero path accounts for the root, giving the susceptibility bound by Tonelli.</p>
<p>For $p=0$ the series is one. Otherwise choose $\mu_d&lt;\lambda&lt;p^{-1}$. For all sufficiently large $n$, $c_np^n\leq(p\lambda)^n$, so the series converges. Finite expected cluster volume excludes an infinite cluster at each root; countability makes this simultaneous at all roots. In the homogeneous model the set defining $p_c$ is nonempty because the full lattice is connected and infinite at $p=1$. Every $p&lt;\mu_d^{-1}$ lies below that set, proving the threshold bound.</p>
<p>Since $\mu_d\leq2d-1$, this criterion includes the <a href="/tag/YP44/">bounded-degree criterion</a>. At $p=\mu_d^{-1}$ the path series diverges, because $c_np^n\geq1$ for every $n$. Divergence of this upper bound says nothing about susceptibility or percolation at that parameter.</p>
<p>The pinned <a href="/sources/perclib-lattice/">lattice module</a> and <a href="/sources/perclib-connective-constant/">path-counting module</a> provide the deterministic results used here. The susceptibility and threshold corollary is an expository deduction, not a theorem exported by those modules. Their source inspection does not create a compiled tag association or an independent correspondence review. The latter module cites Hammersley–Morton and Madras–Slade but marks its literature locators as unchecked; no edition-specific attribution is inferred here.</p>
