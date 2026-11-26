---
{
  "id": "critical-arm-bounds",
  "title": "Critical intrinsic and extrinsic arms",
  "subtitle": "Ball moments, annuli and the dimension obstruction",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Linear intrinsic volume and a three-branch moment bound give the lower intrinsic arm estimate. The volume-tail bootstrap supplies the upper estimate. Spatial two-point bounds give a conditional extrinsic lower bound and a simple obstruction below dimension six.",
  "context": [
    "Independent Bernoulli bonds on transitive graphs; the lattice conclusions specify nearest-neighbour bonds.",
    "An intrinsic arm is measured in open-path distance. It is not an increasing event under edge addition.",
    "Spatial two-point estimates are explicit hypotheses where needed; the extrinsic upper bound is a separate result."
  ],
  "related": [
    "intrinsic-geometry",
    "green-free-triangle",
    "triangle-susceptibility",
    "correlation-length-fourier"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "intrinsic one-arm exponent",
    "annulus second moment",
    "extrinsic arm lower bound",
    "upper critical dimension obstruction"
  ],
  "prototypeUses": []
}
---

## A three-branch moment bound {#section-ball-second}

<p>Write $B(o,r)=\{x:d_\omega(o,x)\le r\}$ and $b(r)=\mathbb E|B(o,r)|$. Distances and balls are always taken in the open graph.</p>
<a id="tag-RP0G" data-assertion="proposition" data-title="The second moment of an intrinsic ball is at most the cube of its mean"></a>
<p>For an invariant transitive independent-bond law on a countable graph and integer $r\ge0$,</p>
<div class="math-display">$$\mathbb E|B(o,r)|^2\le b(r)^3,$$</div>
<p>with extended nonnegative values allowed.</p>
<p><em>Proof.</em> If $x,y\in B(o,r)$, choose consistent shortest paths from $o$ to these vertices in a shortest-path tree of the open root cluster. Their common initial segment ends at a vertex $z$. The three tree segments from $z$ to $o,x,y$ are edge-disjoint and each has length at most $r$. Empty segments are allowed when marks coincide. Thus</p>
<div class="math-display">$$\{x,y\in B(o,r)\}\subseteq\bigcup_z
\{d_\omega(o,z)\le r\}\circ\{d_\omega(z,x)\le r\}\circ\{d_\omega(z,y)\le r\}.$$</div>
<p>The three events are increasing and have finite path witnesses. Apply iterated BK, first on finite edge sets and then by finite-witness approximation, and sum over $x,y,z$. The two sums rooted at $z$ equal $b(r)$ by transitivity; the remaining sum is another $b(r)$. Tonelli justifies the sums even before finiteness is known.</p>
<p>A shortest-path tree can be constructed on a countable cluster by choosing, for each nonroot vertex, a neighbour whose distance from the root is one less, breaking ties with a fixed enumeration. Distances decrease along parent edges, so this is a tree. Only its finite paths to $x$ and $y$ are used in the inclusion.</p>

## An annulus reaches its inner radius {#section-annulus}

<a id="tag-9TXI" data-assertion="proposition" data-title="Linear expected intrinsic volume gives a reciprocal-radius arm lower bound"></a>
<p>In the setting of RP0G, suppose $0<c\le C<\infty$ and</p>
<div class="math-display">$$cr\le b(r)\le Cr\qquad(r\ge1).$$</div>
<p>Choose an integer $L\ge2C/c$. Then, for every integer $n\ge1$,</p>
<div class="math-display">$$\mathbb P\bigl(S(o,n)\ne\varnothing\bigr)\ge\frac{c^2}{4C^3L}\,\frac1n.$$</div>
<p><em>Proof.</em> Put $Z=|B(o,Ln)\setminus B(o,n)|$. Since the means are finite,</p>
<div class="math-display">$$\mathbb EZ=b(Ln)-b(n)\ge(cL-C)n\ge\tfrac12cLn,
\qquad \mathbb EZ^2\le b(Ln)^3\le C^3L^3n^3.$$</div>
<p>Cauchy–Schwarz applied to $Z\mathbf1_{\{Z>0\}}$ gives $\mathbb P(Z>0)\ge(\mathbb EZ)^2/\mathbb EZ^2$. If $Z>0$, some vertex has distance greater than $n$ and at most $Ln$; a shortest path to it passes through distance exactly $n$. Hence $\{Z>0\}\subseteq\{S(o,n)\ne\varnothing\}$, proving the bound.</p>
<p>Nonemptiness of this annulus does not force a vertex at distance $Ln$. The proof needs the inner radius, which already gives the desired estimate for every $n$. The <a href="/errata/heydenreich-hofstad/#intrinsic-annulus-radius">provisional annulus entry</a> corrects that event inclusion in the manuscript.</p>

## The intrinsic exponent in large dimension {#section-intrinsic}

<a id="tag-W73R" data-assertion="theorem" data-title="Critical nearest-neighbour intrinsic balls and arms have linear and reciprocal-linear scales"></a>
<p>There are absolute $d_0,C<\infty$ such that, for nearest-neighbour percolation on $\mathbb Z^d$ with $d\ge d_0$ and every integer $n\ge1$,</p>
<div class="math-display">$$n+1\le\mathbb E_{p_c}|B(0,n)|\le8n,\qquad
\frac1{32768n}\le\mathbb P_{p_c}(S(0,n)\ne\varnothing)\le\frac Cn.$$</div>
<p>The upper arm bound also holds uniformly over deterministic subgraphs, retaining their inherited bond probabilities.</p>
<p><em>Proof.</em> The completed bootstrap gives $qp_c\ge1$ and a neighbouring critical triangle at most $1/2$ for all sufficiently large $d$, where $q=2d$; see <a href="/tag/93RC/">93RC</a>. Thus <a href="/tag/0Y4K/">0Y4K</a> gives $\chi(p)\le2/[q(p_c-p)]$ below criticality. Independently thin each open critical bond with retention probability $p/p_c$. On $\{x\in B(0,n)\}$, choose a shortest open path of length at most $n$. Its chance of surviving the thinning is at least $(p/p_c)^n$. Consequently</p>
<div class="math-display">$$\mathbb E_{p_c}|B(0,n)|\le(p_c/p)^n\chi(p).$$</div>
<p>Take $p=p_c(1-1/(2n))$. Bernoulli's inequality gives $(1-1/(2n))^n\ge1/2$. Hence the right side is at most $8n/(qp_c)\le8n$. The argument includes $n=1$ and the empty path to the root.</p>
<p>Critical susceptibility is infinite by <a href="/tag/JQLC/">JQLC</a>, and the opening-probability row is finite. The renewal bound <a href="/tag/R5XZ/">R5XZ</a> therefore gives $b(n)\ge n+1$. Apply 9TXI with $c=1$, $C=8$ and $L=16$ to obtain the displayed lower arm constant.</p>
<p>For the upper bound, <a href="/tag/74SS/">74SS</a> supplies a critical cluster-volume tail at most an absolute constant times $N^{-1/2}$. Express the same nearest-neighbour model with unit edge weights and intensity $\beta=-\log(1-p)$. Susceptibility is finite below the finite critical intensity by sharpness. The hypotheses of <a href="/tag/KEO7/">KEO7</a> hold with $\delta=2$ and a dimension-independent tail constant, so its intrinsic-arm bound is $C/n$, uniformly over deterministic subgraphs. Its stopping-layer conditioning and endpoint convergence do not use monotonicity of intrinsic spheres under edge addition.</p>
<p>The lower bound uses infinite susceptibility and the upper expected-volume estimate. It does not require pointwise spatial asymptotics of the two-point function.</p>

## A spatial second moment {#section-extrinsic}

<p>For the following conditional result write $\Lambda_n=[-n,n]^d\cap\mathbb Z^d$ and let $\partial\Lambda_n$ denote its vertex boundary.</p>
<a id="tag-CGM9" data-assertion="proposition" data-title="Mean-field spatial two-point bounds imply an extrinsic arm lower bound"></a>
<p>Consider translation-invariant nearest-neighbour Bernoulli bond percolation on $\mathbb Z^d$, where $d>3$. Suppose that for some $0<c_0\le C_0<\infty$ and all vertices $x$,</p>
<div class="math-display">$$c_0(1+|x|)^{2-d}\le\tau(x)\le C_0(1+|x|)^{2-d}.$$</div>
<p>Then there is $c_1>0$, depending only on these constants and $d$, such that</p>
<div class="math-display">$$\mathbb P(0\leftrightarrow\partial\Lambda_n)\ge c_1n^{-2}\qquad(n\ge1).$$</div>
<p><em>Proof.</em> Set $A_n=\Lambda_{2n}\setminus\Lambda_n$ and $Z=\sum_{x\in A_n}\mathbf1_{\{0\leftrightarrow x\}}$. Counting lattice points in the annulus and using the lower two-point bound gives $\mathbb EZ\ge c_2n^2$.</p>
<p>If $0,x,y$ are connected, a finite open tree connecting them has a branch vertex $z$ and three edge-disjoint paths to those marks. BK and a union bound give</p>
<div class="math-display">$$\mathbb EZ^2\le\sum_z\tau(z)\left(\sum_{x\in A_n}\tau(x-z)\right)^2.$$</div>
<p>On $\Lambda_{4n}$, the inner sum is at most $C_2n^2$, uniformly in $z$, by summing $(1+|u|)^{2-d}$ over a ball of radius $O_d(n)$. Also $\sum_{z\in\Lambda_{4n}}\tau(z)\le C_3n^2$. This part of the second moment is at most $C_4n^6$.</p>
<p>If $z\notin\Lambda_{4n}$ and $x\in A_n$, then $|x-z|\ge |z|/(2\sqrt d)$. Since $|A_n|\le C_dn^d$, the remaining part is at most</p>
<div class="math-display">$$C_5n^{2d}\sum_{z\notin\Lambda_{4n}}|z|^{6-3d}\le C_6n^6.$$</div>
<p>The last estimate follows by summing dyadic shells; their contributions have ratio $2^{6-2d}<1$. This is where $d>3$ is used. Thus Cauchy–Schwarz gives $\mathbb P(Z>0)\ge c_3n^{-2}$. A nearest-neighbour path from zero to a vertex outside $\Lambda_n$ must meet $\partial\Lambda_n$, proving the claim. This supplies only the lower arm bound; the matching upper bound requires an additional argument.</p>

## The dimension obstruction {#section-dimension}

<a id="tag-2RZH" data-assertion="proposition" data-title="Mean-field spatial decay and an extrinsic arm upper bound require dimension at least six"></a>
<p>In translation-invariant nearest-neighbour Bernoulli bond percolation on $\mathbb Z^d$, suppose that for some $c,C>0$ and every sufficiently large integer $n$,</p>
<div class="math-display">$$\tau(3ne_1)\ge cn^{2-d},\qquad
\mathbb P(0\leftrightarrow\partial\Lambda_n)\le Cn^{-2}.$$</div>
<p>Then $d\ge6$.</p>
<p><em>Proof.</em> A connection from zero to $3ne_1$ supplies a path from each endpoint to the boundary of its radius-$n$ box. Stop each path at its first boundary visit. The two resulting events depend only on bonds within $\Lambda_n$ and $3ne_1+\Lambda_n$, respectively. These boxes have disjoint vertex sets, so their bond sets are disjoint and the events are independent. Translation invariance gives them the same probability. Therefore</p>
<div class="math-display">$$cn^{2-d}\le\tau(3ne_1)\le
\mathbb P(0\leftrightarrow\partial\Lambda_n)^2\le C^2n^{-4}.$$</div>
<p>Multiplication by $n^4$ gives $cn^{6-d}\le C^2$ for arbitrarily large $n$, forcing $d\ge6$. The separation $3n$ makes the independent coordinate sets immediate. The same conclusion follows from the corresponding logarithmic exponent statements by inserting their $o(1)$ powers.</p>
<p>The <a href="/errata/heydenreich-hofstad/#dimension-obstruction-power">provisional power entry</a> restores $n^{2-d}$ in the source comparison. This obstruction does not prove mean-field behavior above six, rule out logarithmic corrections at six, or establish either hypothesis by itself. The <a href="/coverage/sources/heydenreich-hofstad-2017-arms/">completed Chapter 11 reading map</a> keeps the extrinsic upper bound and the spatial two-point theorem as distinct tasks.</p>


## The logarithmic boundary for spatial diagrams {#section-log-diagram-link}

<p>The <a href="/articles/infrared-diagrams/#section-marginal-diagrams">spatial diagram calculation</a> makes a separate distinction at dimension six. Conditional on two-sided decay of order $|x|^{-4}(\log|x|)^a$, the bubble is finite for every fixed $a$, whereas the triangle is finite exactly for $a&lt;-1/3$ and has double-logarithmic growth at equality. This determines diagram integrability from a spatial estimate; the two-point estimate and the extrinsic arm upper bound remain separate hypotheses.</p>
