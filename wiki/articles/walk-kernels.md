---
{
  "id": "walk-kernels",
  "title": "Walk kernels and intensity bounds",
  "subtitle": "Nonnegative sums before their percolation application",
  "kind": "method",
  "category": "Foundations",
  "summary": "Uniform row sums control the total weight of vertex sequences for arbitrary nonnegative kernels. Removing the diagonal gives the percolation application, including finite intensities with nonzero diagonal weights. A doubling comparison also controls an off-diagonal convolution by the original displacement kernel. Retaining return weights turns an off-diagonal convolution bound into a two-point estimate.",
  "context": [
    "An arbitrary vertex set $V$ and a kernel $a:V\\times V\\to[0,\\infty]$ for the deterministic statements.",
    "Nonnegative sums mean suprema of finite subsums; products use $0\\cdot\\infty=0$ and the empty product is one.",
    "The probability applications assume countable $V$ and independent unordered-pair coordinates. Intensities and their parameter are finite; thresholds may be infinite."
  ],
  "related": [
    "subcritical-bound",
    "product-symmetries",
    "susceptibility",
    "criticality",
    "bounded-degree-paths",
    "displacement-kernels"
  ],
  "sourceIds": ["perclib-walk-sums", "perclib-row-sum", "perclib-intensity-definitions", "perclib-intensity-bounds", "perclib-finite-graphs", "perclib-doubling-convolution", "perclib-convolution-return-bound", "perclib-row-sum-decay", "perclib-subcritical-associations", "perclib-boundary-forest-associations"],
  "aliases": [
    "walk kernel",
    "nonnegative matrix",
    "geometric row bound",
    "off-diagonal mask",
    "zero intensity row",
    "doubling kernel",
    "power-kernel convolution",
    "off-diagonal convolution"
  ],
  "prototypeUses": []
}
---

## Sequence weights {#section-weights}

<a id="tag-O357" data-assertion="definition" data-title="Nonnegative sequence weights, walk sums and diagonal removal"></a>
<p>For a root $v_0=v$ and a sequence $(v_1,\ldots,v_n)\in V^n$, its weight is</p>
<div class="math-display">$$w_a(v;v_1,\ldots,v_n)=\prod_{i=1}^n a(v_{i-1},v_i),\qquad W_n^a(v)=\sum_{(v_1,\ldots,v_n)\in V^n}w_a(v;v_1,\ldots,v_n).$$</div>
<p>The unique empty sequence has weight one, so $W_0^a(v)=1$. Sequences may repeat vertices or edges, and diagonal entries may be nonzero. Define the diagonal-removed kernel by $a^\circ(v,w)=a(v,w)$ when $v\ne w$, and $a^\circ(v,v)=0$.</p>
<p>These are deterministic weights. Even when the entries of $a$ are bond probabilities, the product along a sequence with repeated edges is not generally the probability that its edges are open.</p>

## The row estimate {#section-row-estimate}

<a id="tag-HDHT" data-assertion="theorem" data-title="Extended nonnegative walk sums satisfy the geometric row bound"></a>
<p>For every nonnegative extended kernel,</p>
<div class="math-display">$$W_{n+1}^a(v)=\sum_{u\in V}a(v,u)W_n^a(u).$$</div>
<p>If $\sum_u a(v,u)\leq m$ for all $v$, with $m\in[0,\infty]$, then $W_n^a(v)\leq m^n$. If $m&lt;1$, then</p>
<div class="math-display">$$\sum_{n=0}^\infty W_n^a(v)\leq\frac1{1-m}&lt;\infty.$$</div>
<p>The same bounds apply to $a^\circ$ whenever its off-diagonal rows are bounded by $m$, with no restriction on the original diagonal entries of $a$.</p>
<p><em>Proof.</em> Split a sequence according to its first vertex $u$. Its weight is $a(v,u)$ times the weight of its remaining sequence rooted at $u$. Rearrangement and distributivity of nonnegative sums give the recurrence, with no symmetry or countability assumption. Inducting from $W_0^a(v)=1$ gives</p>
<div class="math-display">$$W_{n+1}^a(v)\leq\sum_u a(v,u)m^n=m^n\sum_u a(v,u)\leq m^{n+1}.$$</div>
<p>All operations take place in the extended nonnegative reals, so the estimate also covers $m=0$ and $m=\infty$, with $m^0=1$. For $m&lt;1$, sum over lengths and use the finite geometric series limit. Applying this result to $a^\circ$ proves the final assertion.</p>
<p>On a one-point space with kernel value $r$, there is exactly one sequence of each length and $W_n=r^n$, including $r=1$ and $r=\infty$. Thus the bound can be exact. If the original kernel is infinite on the diagonal and zero elsewhere, its diagonal-removed kernel is zero: its total walk weight is one, entirely from length zero. This illustrates why a hypothesis on the original diagonal would be inappropriate in the graph application.</p>

## From simple paths to sequence sums {#section-bonds}

<p>For a countable bond model with pair profile $q$, take $a(v,w)=q(\{v,w\})$ and remove its diagonal. A connection has a vertex-simple open path witness. Independence applies to that path because its edges are distinct, giving its open probability as the product of their probabilities. The countable union bound and the susceptibility identity yield</p>
<div class="math-display">$$\chi_q(v)\leq\sum_y\sum_{\gamma:v\to y\text{ simple}}\prod_{e\in\gamma}q(e)\leq\sum_{n=0}^\infty W_n^{a^\circ}(v).$$</div>
<p>For the second inequality, a simple path together with its endpoint is determined by the ordered list of vertices after $v$. Its edge product is precisely the weight of that sequence. Distinct paths therefore give distinct terms when the path sum is enlarged to all sequences. This is a comparison of deterministic nonnegative sums, with no independence assertion for repeated edges. The length-zero path supplies the root contribution one. The ordered edge-product identity and recovery of a path from its continuation list are deterministic facts and need no countability assumption.</p>
<p>The <a href="/tag/53Z9/">row-sum susceptibility theorem</a> follows whenever $\sum_{w\ne v}q(\{v,w\})\leq m&lt;1$ uniformly. Equivalently, apply that theorem after <a href="/tag/EYCQ/">removing the diagonal parameters</a>, which leaves graph observables unchanged. Finite expected cluster volume implies almost-sure finiteness at a fixed root, and countability gives one probability-one event on which all clusters are finite. If every off-diagonal probability is zero, the open graph is empty almost surely and $\chi_q(v)=1$, regardless of diagonal parameters.</p>

<p>For a finite host graph of maximum degree $\Delta$, probabilities at most $p$ on its edges and zero on other non-diagonal pairs give row sums at most $\Delta p$. Thus the same theorem gives $\chi_q(v)\leq(1-\Delta p)^{-1}$ when $\Delta p&lt;1$, with arbitrary diagonal probabilities. For the complete graph on $n\geq1$ vertices with constant off-diagonal probability $p$, the row is exactly $(n-1)p$. The bound holds at every root, and averaging it gives <a href="/tag/MIQ7/">the finite random graph estimate</a>. At $n=1$ the susceptibility is exactly one even if the loop coordinate is always open; at $n=0$ there is no root to evaluate. On three vertices at $p=1/4$, or on two vertices at $p=1/2$, the estimate is $\chi_q(v)\leq2$. Finite graphs have finite clusters at every parameter, so the row criterion is sufficient for this estimate and is not a criterion for finiteness of their clusters.</p>

## Finite intensities and possibly infinite thresholds {#section-intensity}

<a id="tag-BPR6" data-assertion="corollary" data-title="Off-diagonal intensity rows give susceptibility and threshold bounds"></a>
<p>Let $V$ be countable, let $J$ be a finite nonnegative symmetric pair intensity, and put $q_\beta(e)=1-e^{-\beta J(e)}$ for finite $\beta\geq0$. Suppose</p>
<div class="math-display">$$\sum_{w\ne v}J(\{v,w\})\leq M&lt;\infty\qquad\text{for every }v.$$</div>
<p>No restriction is imposed on diagonal intensities. If $\beta M&lt;1$, then</p>
<div class="math-display">$$1\leq\chi_\beta(v)\leq\frac1{1-\beta M}&lt;\infty,$$</div>
<p>and almost surely every cluster is finite. For $M&gt;0$, every rooted critical intensity and the global critical intensity are at least $M^{-1}$. If $M=0$, each susceptibility is one at every finite parameter and all these thresholds are infinite. Independently of a row bound, $\chi_0(v)=1$.</p>
<p>The thresholds here are the infima of finite parameters giving positive probability of an infinite cluster at the chosen root, or somewhere in the graph, respectively, with $\inf\varnothing=\infty$. They are not defined through divergence of susceptibility, and their definition supplies no percolation claim at the infimum.</p>
<p><em>Proof.</em> The profile starts at zero, increases with $\beta$, and satisfies $1-e^{-\beta J(e)}\leq\beta J(e)$. Therefore</p>
<div class="math-display">$$\sum_{w\ne v}q_\beta(\{v,w\})\leq\beta M.$$</div>
<p>Apply the preceding row bound and simultaneous finiteness argument. If $M&gt;0$, no finite parameter below $M^{-1}$ belongs to either percolating-parameter set; their infima are therefore at least $M^{-1}$, including when the sets are empty.</p>
<p>If $M=0$, nonnegativity forces every off-diagonal intensity to vanish. The same is true of the corresponding opening probabilities at every finite parameter. Countability makes all non-diagonal coordinates closed simultaneously almost surely, so every cluster is a singleton and both percolating-parameter sets are empty. Diagonal intensities may still be positive. At $\beta=0$, every coordinate probability is zero for any finite intensity profile, giving the last assertion without a row assumption.</p>
<p>On a finite vertex set every infinite-cluster threshold is infinite, even with nonzero intensities; on the empty vertex set the global percolation event is empty and there are no rooted thresholds to evaluate. The lower bound does not assert finiteness of a threshold or decide percolation at $\beta M=1$.</p>


## Doubling kernels and one convolution {#section-doubling-convolution}

<p>Let $G$ be an Abelian group, written additively, and let $\rho:G\to[0,\infty)$ satisfy $\rho(u+v)\leq\rho(u)+\rho(v)$. Neither $\rho$ nor the kernel below is required to be symmetric.</p>

<a id="tag-4Q21" data-assertion="theorem" data-title="A doubling comparison controls the off-diagonal convolution by the kernel"></a>
<p>Let $k:G\to[0,\infty]$ vanish at zero, and suppose $D,M\in[0,\infty]$ satisfy</p>
<div class="math-display">$$\sum_zk(z)\leq M,\qquad k(u)\leq Dk(w)\quad\text{whenever }u,w\ne0\text{ and }\rho(w)\leq2\rho(u).$$</div>
<p>Then, for every $x\ne y$,</p>
<div class="math-display">$$\sum_zk(z-x)k(y-z)\leq2DM\,k(y-x).$$</div>
<p>All sums and products are in the extended nonnegative reals with $0\cdot\infty=0$. The group need not be countable, and no finiteness assumption on $D$ or $M$ is needed for this inequality.</p>
<p><em>Proof.</em> The terms with $z=x$ or $z=y$ vanish. For every other $z$, subadditivity gives</p>
<div class="math-display">$$\rho(y-x)\leq\rho(z-x)+\rho(y-z).$$</div>
<p>At least one term on the right is at least $\rho(y-x)/2$. Apply the kernel comparison to that displacement, obtaining in either case</p>
<div class="math-display">$$k(z-x)k(y-z)\leq Dk(y-x)\bigl(k(z-x)+k(y-z)\bigr).$$</div>
<p>Both maps $z\mapsto z-x$ and $z\mapsto y-z$ are bijections of the group. Thus each translated sum on the right is at most $M$. Summing the pointwise inequality proves the claim. Rearrangement and distributivity are valid for nonnegative extended sums, so the argument also covers infinite weights and an uncountable group.</p>

## The norm-power specialization {#section-power-convolution}

<a id="tag-ZXLF" data-assertion="corollary" data-title="Origin-deleted norm powers satisfy the convolution bound under an explicit mass bound"></a>
<p>On a normed Abelian group, let $s\geq0$, set $k_s(0)=0$ and $k_s(z)=\|z\|^{-s}$ for $z\ne0$, and suppose $\sum_zk_s(z)\leq M\in[0,\infty]$. Then, for every $x\ne y$,</p>
<div class="math-display">$$\sum_zk_s(z-x)k_s(y-z)\leq2^{s+1}M\|y-x\|^{-s}.$$</div>
<p><em>Proof.</em> If $w\ne0$ and $\|w\|\leq2\|u\|$, then $\|u\|&gt;0$ and</p>
<div class="math-display">$$\|u\|^{-s}\leq2^s\|w\|^{-s}.$$</div>
<p>This is the doubling comparison with $D=2^s$; the triangle inequality supplies subadditivity. Apply 4Q21.</p>
<p>On $\mathbb Z^d$ with the supremum norm, taking $s=d+\alpha$, $\alpha\geq0$, gives the constant $2^{d+\alpha+1}M$. When $d\geq1$ and $\alpha&gt;0$, <a href="/tag/6VNM/">power-kernel summability</a> supplies a finite $M$. At $\alpha=0$ the mass is infinite in positive dimension; the convolution theorem retains its explicit mass hypothesis and supplies no finite bound from that endpoint. For $d=0$ there are no distinct vertices to which the inequality could apply. The exponent $s=0$ is allowed in the doubling comparison, although its origin-deleted kernel has infinite mass on an infinite group.</p>
<p>For example, $k(z)=|z|^{-2}$ on $\mathbb Z\setminus\{0\}$ has mass $\pi^2/3$, so its convolution at a nonzero displacement $w$ is at most $8\pi^2/(3|w|^2)$. The origin is different: there the convolution is $\sum_z k(z)k(-z)$, which is positive for every nonzero even kernel although $k(0)=0$. Consequently 4Q21 is not a pointwise bound on the whole group that can simply be iterated. The result is a deterministic comparison of nonnegative sums; it makes no independence assertion about repeated edges in a walk.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-convolution/">five-contract inventory</a> keeps the general gauge, the raw norm-power comparison, deletion of the origin, the normed-group estimate and its lattice specialization separate. Earlier row estimates and source records are preserved; the new correspondences await independent review and compiled association.</p>


## Retaining returns in the two-point bound {#section-convolution-returns}

<p>For $t\in[0,\infty]$, write $H(t)=\sum_{n\geq0}t^n$. Thus $H(t)=(1-t)^{-1}$ for $t&lt;1$ and $H(t)=\infty$ for $t\geq1$. Products of extended nonnegative quantities still use $0\cdot\infty=0$.</p>

<a id="tag-9L60" data-assertion="theorem" data-title="An off-diagonal convolution bound gives a two-point estimate with a return factor"></a>
<p>Let $a:V\times V\to[0,\infty]$, let $b=a^\circ$ be its diagonal removal, and suppose $m,\kappa\in[0,\infty]$ satisfy</p>
<div class="math-display">$$\sum_z b(x,z)\leq m\quad(x\in V),\qquad \sum_z b(x,z)b(z,y)\leq\kappa a(x,y)\quad(x\ne y).$$</div>
<p>Let $F_n(x,y)$ be the total weight of length-$n$ vertex sequences starting at $x$ and ending at $y$, using the kernel $b$. For $x\ne y$ and $n\geq0$,</p>
<div class="math-display">$$F_{n+1}(x,y)\leq c_{n+1}a(x,y),\qquad c_{n+1}=\sum_{j=0}^n\kappa^j m^{n-j},$$</div>
<p>and consequently</p>
<div class="math-display">$$\sum_{n\geq0}F_n(x,y)\leq a(x,y)H(\kappa)H(m).$$</div>
<p>If $V$ is countable and the independent bond probabilities satisfy $q_{x,y}\leq a(x,y)$ for every $x\ne y$, then</p>
<div class="math-display">$$\tau_q(x,y)\leq a(x,y)H(\kappa)H(m).$$</div>
<p>In particular, for $m,\kappa&lt;1$, the right side is $a(x,y)/[(1-\kappa)(1-m)]$. No symmetry, countability or probability hypothesis is needed for the deterministic sequence bounds.</p>
<p><em>Proof.</em> The empty sequence gives $F_0(x,y)=\mathbf1_{\{x=y\}}$. Splitting at the first step gives</p>
<div class="math-display">$$F_{n+1}(x,y)=\sum_z b(x,z)F_n(z,y).$$</div>
<p>Restriction to an endpoint only removes terms from the unrestricted walk sum. By <a href="/tag/HDHT/">the row estimate</a>, $F_n(y,y)\leq W_n^b(y)\leq m^n$.</p>
<p>We have $c_1=1$ and $F_1(x,y)=a(x,y)$ off the diagonal. If the claimed bound holds at length $n+1$, separate $z=y$ in the first-step recursion. The return term is bounded by $a(x,y)m^{n+1}$. For the remaining terms use the off-diagonal induction hypothesis and then the convolution bound. This gives</p>
<div class="math-display">$$F_{n+2}(x,y)\leq\bigl(m^{n+1}+\kappa c_{n+1}\bigr)a(x,y)=c_{n+2}a(x,y).$$</div>
<p>The scalar recurrence follows by separating the $j=0$ term in $c_{n+2}$. Summing over lengths and regrouping the nonnegative double series yields</p>
<div class="math-display">$$\sum_{n\geq0}c_{n+1}=\sum_{i,j\geq0}\kappa^i m^j=H(\kappa)H(m).$$</div>
<p>For $x\ne y$, the length-zero term is zero, so this proves the total sequence bound. The induction in fact needs only the identity initial condition, the first-step recursion, the off-diagonal convolution inequality and the diagonal estimate $F_n(y,y)\leq m^n$. For any family satisfying these four conditions it works without a row hypothesis or a zero-diagonal assumption on its recursion kernel.</p>
<p>For the probability conclusion, each connection has a vertex-simple path witness. Its distinct edges are independent, and its open probability is at most the product of the corresponding $b$-entries. The continuation list after $x$ determines the path and retains its endpoint $y$, so simple paths inject into the sequences counted by the $F_n(x,y)$. Apply the countable union bound and then the deterministic estimate. Repeated-edge sequence weights are used only as a majorant, never as joint opening probabilities.</p>
<p>The factor $H(m)$ accounts for returns that an off-diagonal convolution estimate cannot control by $a(y,y)$. For example, a kernel supported on disjoint paired vertices has zero off-diagonal two-step convolution but nonzero return weights. At $x=y$, connection is certain and the displayed off-diagonal conclusion is not asserted. The <a href="/coverage/sources/perclib-5d6efa8-return-bound/">eight-contract inventory</a> records the scalar identities, abstract recursion, endpoint sequence sums, path injection and final probability comparison.</p>


## Connection mass beyond a support ball {#section-support-decay}

<p>Consider a countable bond model satisfying $\sum_{z\ne v}q(\{v,z\})\leq m&lt;1$ at every vertex. Let $G_q$ be the simple graph of positive-probability bonds. For an integer $k\geq0$, let $S_k(x)$ consist of the vertices $y$ for which every $G_q$-walk from $x$ to $y$ has length at least $k$. This includes vertices in other components. Within the component of $x$, it is the set at graph distance at least $k$.</p>
<a id="tag-VYCM" data-assertion="theorem" data-title="A row bound controls connection mass beyond a support-graph ball"></a>
<p>Then</p>
<div class="math-display">$$\sum_{y\in S_k(x)}\tau_q(x,y)\leq\frac{m^k}{1-m}.$$</div>
<p>In particular, $\tau_q(x,y)\leq m^k/(1-m)$ for $y\in S_k(x)$, and $\tau_q(x,y)=0$ if $y$ is disconnected from $x$ in $G_q$. The convention is $m^0=1$, including at $m=0$.</p>
<p><em>Proof.</em> A simple path from $x$ to $y\in S_k(x)$ of length less than $k$ must contain a bond of probability zero. Its cylinder product is therefore zero. In the path union bound we may retain only paths of length at least $k$. Each path together with its endpoint has a distinct continuation list, so summing over $y\in S_k(x)$ and then enlarging to all lists gives</p>
<div class="math-display">$$\sum_{y\in S_k(x)}\tau_q(x,y)
\leq\sum_{n\geq k}W_n^{a^\circ}(x)
\leq\sum_{n\geq k}m^n=\frac{m^k}{1-m},\qquad a(v,z)=q(\{v,z\}).$$</div>
<p>The second inequality is the <a href="/tag/HDHT/">row estimate</a>. All sums are nonnegative. For a disconnected endpoint every finite path contains a zero-probability bond, so the original path bound is zero.</p>
<p>At $k=0$ this recovers the full susceptibility bound, including the root term one. At $m=0$, positive-length terms vanish and every cluster is a singleton almost surely. No finite-degree or transitivity hypothesis is needed. In a long-range model with every off-diagonal bond probability positive, $G_q$ is complete and distinct vertices have support distance one. The displayed estimate then gives no decay with Euclidean separation; the <a href="/tag/23RT/">power-law example</a> illustrates the distinction.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-path-decay/">nine-contract source inventory</a> includes both the individual two-point bound and this summed tail. It states the result using lower bounds on walk lengths, so disconnected vertices are handled without assigning them a finite distance. The deterministic tail estimate and path-to-list identities hold on arbitrary vertex types; countability enters the percolation event and susceptibility arguments.</p>
