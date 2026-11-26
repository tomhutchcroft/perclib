---
{
  "id": "tilted-susceptibility",
  "title": "Tilted susceptibility and exponential correlation length",
  "subtitle": "Finite-box bounds identify the divergence point",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A finite-box contraction makes the domain of tilted summability open. Its axial boundary is the exponential mass, with divergence at the boundary and continuous dependence on the bond probability.",
  "context": [
    "Independent nearest-neighbour bond percolation on $\\mathbb Z^d$, $d\\ge1$, with common bond probability $0<p<p_c$.",
    "$\\tau_p(x)=\\mathbb P_p(0\\leftrightarrow x)$ and $\\chi_p(h)=\\sum_xe^{h\\cdot x}\\tau_p(x)$ for $h\\in\\mathbb R^d$.",
    "The mass is defined by axial exponential decay. No tilted lace-coefficient estimate is assumed except in the final, explicitly conditional application."
  ],
  "related": ["correlation-length-fourier", "fourier-bootstrap", "triangle-susceptibility"],
  "sourceIds": ["hara-correlation-1990", "heydenreich-hofstad"],
  "aliases": ["mass and tilted susceptibility", "boundary divergence", "exponential correlation length"],
  "prototypeUses": []
}
---

## The domain of summability {#section-domain}

<a id="tag-9LN2" data-assertion="proposition" data-title="Tilted summability is open in the bond probability and the tilt"></a>
<p>The set</p>
<div class="math-display">$$\mathcal U=\{(p,h)\in(0,1)\times\mathbb R^d:\chi_p(h)<\infty\}$$</div>
<p>is open. For $0<p<p_c$, its section $\mathcal D_p=\{h:\chi_p(h)<\infty\}$ is a convex, centrally symmetric neighbourhood of zero, contained in $\{h:|h_i|< -\log p\text{ for every }i\}$.</p>
<p><em>Proof.</em> Fix $(p,h)\in\mathcal U$ and let $S=[-R,R]^d\cap\mathbb Z^d$ for integer $R\ge1$. Write $\tau_{S,p}(0,u)$ for connection using only edges of the induced graph on $S$, and put</p>
<div class="math-display">$$b_{S,p}(x)=\mathbf1_{\{x\in S\}}\tau_{S,p}(0,x),\qquad
K_{S,p}(v)=\mathbf1_{\{v\notin S\}}\sum_{\substack{u\in S\\u\sim v}}p\tau_{S,p}(0,u).$$</div>
<p>Let $B_{S,p}(h)$ and $\kappa_{S,p}(h)$ be their respective sums against $e^{h\cdot x}$. Both are finite sums of continuous functions of $(p,h)$. If $\partial_{\mathrm{in}}S$ is the inner vertex boundary, then</p>
<div class="math-display">$$\kappa_{S,p}(h)\le p\left(\sum_{e\sim0}e^{h\cdot e}\right)
\sum_{u\in\partial_{\mathrm{in}}S}e^{h\cdot u}\tau_p(u)\longrightarrow0.$$</div>
<p>Choose $S$ so that $\kappa_{S,p}(h)<1$. A simple open path either stays in $S$ or has a first exit edge. Its prefix, exit edge and suffix are disjoint witnesses, so the first-exit argument of <a href="/tag/8LOF/">8LOF</a> gives</p>
<div class="math-display">$$\tau_p\le b_{S,p}+K_{S,p}*\tau_p.$$</div>
<p>The box is symmetric, hence $K_{S,p}$ is even and $\|K_{S,p}\|_1\le\kappa_{S,p}(h)$, by pairing opposite vertices and using $\cosh(h\cdot v)\ge1$. Iteration leaves a remainder bounded pointwise by $\|K_{S,p}\|_1^{n+1}$, since $\tau_p\le1$. It follows that</p>
<div class="math-display">$$\tau_p\le\sum_{n\ge0}K_{S,p}^{*n}*b_{S,p},\qquad
\chi_p(h)\le\frac{B_{S,p}(h)}{1-\kappa_{S,p}(h)}.$$</div>
<p>The same fixed box has $\kappa_{S,p'}(h')<1$ throughout a neighbourhood of $(p,h)$. Its kernel is still even, so the argument applies there too. This proves openness without subtracting an infinite tilted sum from itself.</p>
<p>Subcritical finiteness follows from <a href="/tag/JQLC/">sharpness</a>, so openness puts zero in the interior of $\mathcal D_p$. Reflection gives central symmetry, and Hölder's inequality gives convexity. Finally, the straight path to $ne_i$ has probability $p^n$. The corresponding terms force divergence whenever $h_i\ge-\log p$; the negative axis gives the other boundary.</p>

## The mass and its boundary {#section-mass}

<a id="tag-JQOQ" data-assertion="theorem" data-title="Axial decay and box escape have the same positive mass, and the tilted susceptibility diverges there"></a>
<p>For $0<p<p_c$, the limit</p>
<div class="math-display">$$m(p)=\lim_{n\to\infty}-\frac1n\log\tau_p(ne_1)
=\inf_{n\ge1}-\frac1n\log\tau_p(ne_1)$$</div>
<p>exists and satisfies $0<m(p)\le-\log p$. For every $x\in\mathbb Z^d$,</p>
<div class="math-display">$$\tau_p(x)\le e^{-m(p)\|x\|_\infty}.$$</div>
<p>For integers $R\ge1$, let $E_R$ be the event that zero is connected to a vertex with sup norm $R$. Then</p>
<div class="math-display">$$\lim_{R\to\infty}-\frac1R\log\mathbb P_p(E_R)=m(p),\qquad
\chi_p(te_1)<\infty\ \Longleftrightarrow\ |t|<m(p).$$</div>
<p>Moreover $\chi_p(te_1)\to\infty$ as $t\uparrow m(p)$. Thus the inverse exponential correlation length is exactly the axial boundary of tilted summability.</p>
<p><em>Proof.</em> Harris's inequality applied to connections from $0$ to $ne_1$ and from $ne_1$ to $(n+k)e_1$ gives $\tau_p((n+k)e_1)\ge\tau_p(ne_1)\tau_p(ke_1)$. Subadditivity of the negative logarithm proves the limit and infimum formula. The straight path bounds the mass above. It is positive by the subcritical exponential moment in <a href="/tag/BT9V/">BT9V</a>.</p>
<p>Fix a coordinate $i$. The connection events from $0$ to $x$ and from $x$ to $2x_i e_i$ each have probability $\tau_p(x)$, by translation and coordinate reflections. Their intersection connects $0$ to $2x_i e_i$, so</p>
<div class="math-display">$$\tau_p(x)^2\le\tau_p(2x_i e_i)\le e^{-2m(p)|x_i|}.$$</div>
<p>Choose a coordinate of maximal absolute value. The pointwise bound follows. The shell of radius $R\ge1$ has $(2R+1)^d-(2R-1)^d$ vertices, and hence</p>
<div class="math-display">$$\tau_p(Re_1)\le\mathbb P_p(E_R)
\le\bigl[(2R+1)^d-(2R-1)^d\bigr]e^{-m(p)R}.$$</div>
<p>Taking logarithms proves the escape-rate identity. Shell summation also gives $\chi_p(te_1)<\infty$ when $|t|<m(p)$. If $t>m(p)$, the terms $e^{tn}\tau_p(ne_1)$ grow exponentially by the defining limit, so their sum diverges. Reflection treats negative $t$.</p>
<p>If the sum were finite at $t=m(p)$, openness of $\mathcal U$ would make it finite at a larger tilt, a contradiction. Finally, reflection rewrites the sum as $\sum_x\cosh(tx_1)\tau_p(x)$. Its terms increase for $t\ge0$, so monotone convergence gives divergence as the boundary is approached.</p>

## Dependence on the parameters {#section-continuity}

<a id="tag-OYWM" data-assertion="proposition" data-title="The mass is continuous below criticality and the tilted sum is analytic inside its domain"></a>
<p>The function $m$ is nonincreasing and continuous on $(0,p_c)$, and $m(p)\downarrow0$ as $p\uparrow p_c$. On $\mathcal U$, every derivative of $\chi_p(h)$ with respect to $h$ is jointly continuous in $(p,h)$ and is obtained by differentiating the series. For each fixed $p$, the function of $h$ is real analytic on $\mathcal D_p$.</p>
<p><em>Proof.</em> Monotonicity of connection probabilities makes $m$ nonincreasing. By <a href="/tag/8LOF/">8LOF</a>, each positive $\tau_p(ne_1)$ is continuous below criticality. The infimum formula makes $m$ upper semicontinuous. For $0\le t<m(p)$, openness of $\mathcal U$ gives $\chi_{p'}(te_1)<\infty$, and hence $m(p')>t$, for every sufficiently close $p'$. Letting $t\uparrow m(p)$ proves lower semicontinuity.</p>
<p>If the decreasing critical limit were $c>0$, the pointwise bound would give $\tau_p(x)\le e^{-c\|x\|_\infty}$ for every $p<p_c$. Finite path witnesses and the uniform-edge coupling give $\tau_p(x)\uparrow\tau_{p_c}(x)$. The same summable bound would therefore hold at criticality, contradicting <a href="/tag/8ZGG/">infinite critical susceptibility</a>.</p>
<p>For the regularity assertion, fix $(p_0,h_0)\in\mathcal U$. Evenness implies $\chi_p(0)\le\chi_p(h)$, so such a $p_0$ is subcritical. Choose $p_+>p_0$ and $\varepsilon>0$ small enough that all $2^d$ points $(p_+,h_0+\varepsilon\sigma)$, $\sigma\in\{-1,1\}^d$, remain in $\mathcal U$. Then</p>
<div class="math-display">$$\sum_x\tau_{p_+}(x)e^{h_0\cdot x+\varepsilon\|x\|_1}
\le\sum_{\sigma\in\{-1,1\}^d}\chi_{p_+}(h_0+\varepsilon\sigma)<\infty.$$</div>
<p>For $p\le p_+$ near $p_0$ and $\|h-h_0\|_\infty<\varepsilon/2$, this dominates every differentiated series after absorbing its polynomial factor into the unused half of the exponential. Pointwise continuity in $p$ and dominated convergence prove joint continuity. Expanding $e^{(h-h_0)\cdot x}$ and using the same bound permits absolute summation of its power series, which proves real analyticity in $h$. No analyticity in $p$ is asserted.</p>

## The pole in the lace equation {#section-pole}

<a id="tag-XZX4" data-assertion="proposition" data-title="Endpoint coefficient summability identifies the lace pole at the actual mass"></a>
<p>Fix $0<p<p_c$ and write $m=m(p)$, $j=2dp$ and $D(x)=(2d)^{-1}\mathbf1_{\{x\sim0\}}$. Suppose an even kernel $\Pi$ satisfies</p>
<div class="math-display">$$\tau=\delta_0+\Pi+jD*(\delta_0+\Pi)*\tau,\qquad
\sum_xe^{m|x_1|}|\Pi(x)|<\infty.$$</div>
<p>Set $b_t=1+\sum_xe^{tx_1}\Pi(x)$ and $D_t=1+(\cosh t-1)/d$. Then</p>
<div class="math-display">$$jD_mb_m=1,\qquad
\frac1{\chi_p(0)}=j\left[D_m-1+D_m\frac{b_m-b_0}{b_0}\right].$$</div>
<p>In particular, if $m\le1$, $1/2\le j\le2$, $1/2\le b_0\le3/2$ and $|b_m-b_0|\le m^2/(16d)$, then the actual exponential length $\xi(p)=1/m(p)$ satisfies</p>
<div class="math-display">$$\frac d2\xi(p)^2\le\chi_p(0)\le8d\xi(p)^2.$$</div>
<p>If, in addition, $\sum_x|x_1|e^{m|x_1|}|\Pi(x)|<\infty$ and</p>
<div class="math-display">$$A=j\left[\frac{\sinh m}{d}b_m+D_m b'_m\right]>0,$$</div>
<p>then</p>
<div class="math-display">$$\lim_{t\uparrow m}(m-t)\chi_p(te_1)=\frac{b_m}{A}.$$</div>
<p>A sufficient condition for $A>0$ is $|b'_m|\le b_m\sinh(m)/(2dD_m)$.</p>
<p><em>Proof.</em> For $0\le t<m$, absolute summability gives $(1-jD_tb_t)\chi_p(te_1)=b_t$. At $t=0$ this rearranges to $b_0=\chi_p(0)/(1+j\chi_p(0))>0$. The preceding mass theorem supplies both interior finiteness and endpoint divergence. Dominated convergence gives $b_t\to b_m$, so division by $\chi_p(te_1)$ and passage to the boundary give $jD_mb_m=1$. The reciprocal identity and the quantitative bounds now follow from <a href="/tag/1BG0/">1BG0</a>, with its mass hypotheses discharged.</p>
<p>The additional weighted first moment makes $b$ continuously differentiable up to $m$ from the left. Therefore</p>
<div class="math-display">$$1-jD_tb_t=A(m-t)+o(m-t).$$</div>
<p>Since $b_m=(jD_m)^{-1}>0$, the quotient proves the limit when $A>0$. The sufficient condition bounds the second term in $A$ by half the positive first term.</p>
<p>The mass identification and boundary divergence are unconditional subcritical lattice results. The final proposition separates them from its coefficient hypotheses. The <a href="/articles/tilted-fourier-bootstrap/#section-closure">completed tilted bootstrap</a> now supplies the endpoint exponential moment, quantitative tilt difference and derivative estimate in sufficiently large dimension, with the <a href="/articles/tilted-fourier-bootstrap/#section-length">near-critical range stated explicitly</a>. The <a href="/errata/heydenreich-hofstad/#mass-susceptibility-reciprocal">reciprocal erratum</a> records that completion and its remaining numerical-threshold limitation. These are written proofs, with no new Lean association.</p>
