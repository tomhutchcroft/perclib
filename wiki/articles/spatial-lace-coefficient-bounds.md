---
{
  "id": "spatial-lace-coefficient-bounds",
  "title": "Spatial bounds for the first lace coefficients",
  "subtitle": "Two long edges and four summable diagrams",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A spatial two-point bound gives the same squared decay for the zeroth and first lace coefficients. The first-coefficient proof reduces to four summation patterns in dimension greater than six.",
  "context": [
    "Nearest-neighbour Bernoulli bond percolation on $\\mathbb Z^d$, with $d>6$.",
    "The spatial two-point bound is an explicit hypothesis, not a consequence of a Fourier bound.",
    "Write $\\langle x\\rangle=\\max\\{1,|x|\\}$ with Euclidean norm."
  ],
  "related": [
    "spatial-convolution-asymptotics",
    "lace-coefficient-diagrams",
    "completed-fourier-bootstrap"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "Exercise 11.4",
    "first lace coefficient spatial decay"
  ],
  "prototypeUses": []
}
---

## The first-coefficient diagram {#section-diagram}

<a id="tag-4CGW" data-assertion="proposition" data-title="The eight-edge first-coefficient diagram has squared Green decay above dimension six"></a>
<p>Let $d>6$, $s=d-2$ and $H(x)=\langle x\rangle^{-s}$. Then</p>
<div class="math-display">$$\mathcal D(x)=\sum_{u,w,z,t}H(u)H(w)H(u-w)H(z-w)H(t-u)H(z-t)H(x-t)H(x-z)
\le C_d\langle x\rangle^{-2s}.$$</div>
<p>All sums here and below are over $\mathbb Z^d$.</p>
<p><em>Proof.</em> Put $A=H*H$ and $B=H*H*H$. The power-convolution bound <a href="/tag/IDIL/">IDIL</a> gives</p>
<div class="math-display">$$A(x)\le C_d\langle x\rangle^{-(d-4)},\qquad
B(x)\le C_d\langle x\rangle^{-(d-6)}.$$</div>
<p>Both convolutions are absolutely convergent because $d>6$. In particular $B$ is bounded. Also $HA$ is summable, since $2d-6>d$, and $A\in\ell^3$, since $3(d-4)>d$.</p>
<p>For $x\ne0$, set $R=|x|$. The route $0,w,z,x$ contains an edge of length at least $R/3$, as does the route $0,u,t,x$. Number the three edges of each route from $0$ to $x$. A pair of choices covers each summand in $\mathcal D(x)$. The two chosen factors are at most $3^sR^{-s}$ each. Remove them and then drop the restrictions on the remaining variables. The nine resulting sums reduce to four types by interchanging the routes and reversing them through the change of variables $v\mapsto x-v$:</p>
<table>
<thead><tr><th>Removed edge positions</th><th>Remaining sum</th><th>Uniform bound</th></tr></thead>
<tbody>
<tr><td>$(1,1)$ or $(3,3)$</td><td>$\sum_v H(v)B(v)A(v)$</td><td>$\|B\|_\infty\|HA\|_1$</td></tr>
<tr><td>$(1,2),(2,1),(2,3),(3,2)$</td><td>$(B*(HA))(x)$</td><td>$\|B\|_\infty\|HA\|_1$</td></tr>
<tr><td>$(1,3)$ or $(3,1)$</td><td>$(A*A^2)(x)$</td><td>$\|A\|_3^3$</td></tr>
<tr><td>$(2,2)$</td><td>$B(0)^2$</td><td>$B(0)^2$</td></tr>
</tbody>
</table>
<p>Here $HA$ and $A^2$ denote pointwise products. To check the first row, sum over $u,w$ along the three-edge chain from $t$ to $z$, giving $B(z-t)$; the sum over the common translate of $z,t$ gives $A(z-t)$. In the second row, sum over $w,u$ to obtain $B(z)$, and over $t$ to obtain $A(x-z)$; the remaining edge contributes $H(x-z)$. In the third row the sums over $w$ and $t$ each give $A(u-z)$, while the two outside edges convolve to $A$. Hölder with exponents $3$ and $3/2$ gives its displayed bound. Removing the two middle edges in the last row separates two triangles, each with sum $B(0)$. These calculations can first be made for finite partial sums and then passed to the limit by Tonelli.</p>
<p>The four bounds are finite and independent of $x$, so summing the nine choices proves the assertion for $x\ne0$. At $x=0$, use $H\le1$ to discard the two middle-route factors directly. The remaining sum is again $B(0)^2$.</p>

## The first two coefficients and their moments {#section-coefficients}

<a id="tag-P8KQ" data-assertion="proposition" data-title="A spatial bootstrap bound controls the zeroth and first lace coefficients and their moments"></a>
<p>Consider nearest-neighbour Bernoulli bond percolation in dimension $d>6$, at a parameter $p$ for which clusters are finite almost surely. Suppose</p>
<div class="math-display">$$\tau_p(x)\le\Gamma\langle x\rangle^{-(d-2)}\quad\text{for every }x,\qquad j=2dp.$$</div>
<p>For the nonnegative lace coefficients defined in <a href="/articles/lace-coefficient-diagrams/">the coefficient expansion</a>, there is a constant depending only on $d$ such that</p>
<div class="math-display">$$\Pi_p^{(0)}(x)\le\Gamma^2\langle x\rangle^{-2(d-2)},\qquad
\Pi_p^{(1)}(x)\le C_d j\Gamma^8\langle x\rangle^{-2(d-2)}.$$</div>
<p>Consequently, for $n=0,1$ and every $0\le\beta<d-4$,</p>
<div class="math-display">$$\sum_x\langle x\rangle^\beta\Pi_p^{(n)}(x)<\infty.$$</div>
<p><em>Proof.</em> BK bounds double connection by $\tau_p(x)^2$ off the origin, and $\Pi_p^{(0)}(0)=0$. This proves the first inequality. Let $D$ be the uniform nearest-neighbour step distribution and put $\widetilde\tau_p=jD*\tau_p$. Since $\langle x-e\rangle\ge\langle x\rangle/2$ for every nearest-neighbour step $e$,</p>
<div class="math-display">$$\widetilde\tau_p(x)\le 2^{d-2}j\Gamma\langle x\rangle^{-(d-2)}.$$</div>
<p>The independently sampled cutting-event witnesses in <a href="/tag/SJIL/">SJIL</a> give the pointwise bound</p>
<div class="math-display">$$\Pi_p^{(1)}(x)\le\sum_{u,w,z,t}
\tau_p(u)\tau_p(w)\tau_p(u-w)\tau_p(z-w)\widetilde\tau_p(t-u)
\tau_p(z-t)\tau_p(x-t)\tau_p(x-z).$$</div>
<p>Insert the seven bounds for $\tau_p$ and the one for $\widetilde\tau_p$, then apply 4CGW. Absorb $2^{d-2}$ into $C_d$. This also covers $p=0$, when the first coefficient vanishes. Finally the moment sum is bounded by a constant times $\sum_x\langle x\rangle^{-(2d-4-\beta)}$, which converges precisely in the asserted range by shell counting.</p>
<p>In particular, these two coefficients have a finite absolute $(2+\varepsilon)$-moment for every $0<\varepsilon<d-6$. This does not establish that moment for the full alternating coefficient series: the estimates above contain no summable bound in the order $n$. Nor does the proof establish its spatial bootstrap hypothesis. At sufficiently large critical dimension, almost-sure finiteness is supplied by <a href="/tag/F7N7/">F7N7</a>; the spatial hypothesis still requires the separate spatial argument.</p>

## The full coefficient series {#section-pointwise-followup}

<p>The subsequent theorem <a href="/tag/8F9A/">8F9A</a> bounds all orders by extracting two long edges from the expanded planar diagrams. The remaining connector norms give a geometric order tail. <a href="/tag/KF2I/">KF2I</a> then proves the required critical spatial bound in sufficiently large dimension and obtains the full-series coefficient exponent $2(d-2)$ uniformly for $p\le p_c$. This is a qualitative dimension result; the earlier tagged statements and their hypotheses are unchanged.</p>
