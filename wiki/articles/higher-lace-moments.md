---
{
  "id": "higher-lace-moments",
  "title": "Higher moments of the full lace series",
  "subtitle": "Polynomial weights and continuity at criticality",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A spatial two-point estimate and a small weighted triangle give summable polynomial moments at every lace order. The argument also gives weighted continuity at criticality and a quantitative quadratic Fourier expansion.",
  "context": [
    "Nearest-neighbour Bernoulli bond percolation on $\\mathbb Z^d$.",
    "The spatial two-point estimate is a hypothesis. The pointwise bound on the full lace coefficient is a separate task.",
    "All coefficient estimates concern the nonnegative orders before alternating summation."
  ],
  "related": ["spatial-lace-coefficient-bounds", "weighted-lace-coefficients", "signed-kernel-moments", "signed-kernel-gaussian-asymptotics"],
  "sourceIds": ["heydenreich-hofstad", "hara-nearest-neighbour-2008"],
  "aliases": ["higher lace moments", "weighted critical continuity", "polynomial diagram weights"],
  "prototypeUses": []
}
---

## Polynomial weights in the chain {#section-chain}

<p>Use the nonnegative kernels $A,B_1,B_2$ of <a href="/tag/SJIL/">SJIL</a>, with $\widetilde\tau=J*\tau$, $j=\sum J$, $\Delta=\sup_x\tau^{*3}(x)$, $T=\sup_x(\tau^{*2}*\widetilde\tau)(x)$ and $r=2T\Delta$. For $\beta>0$, put $w(x)=|x|^\beta$, $a_\beta=\max\{\beta-1,0\}$ and</p>
<div class="math-display">$$W_{\beta,0}=\sum_xw(x)\widetilde\tau(x)\tau(x),\qquad W_\beta=\sup_y\sum_xw(x)\widetilde\tau(x)\tau(x-y).$$</div>
<p>Let $H_\beta$ be the supremum of the marked diagram in <a href="/tag/09JN/">09JN</a>, with $h(t-u)$ replaced by $w(t-u)$.</p>

<a id="tag-KFUM" data-assertion="proposition" data-title="Polynomial displacement weights give all-order lace moment bounds"></a>
<p>Suppose clusters are finite almost surely and $\Delta,T,W_\beta,H_\beta<\infty$. Writing $M_\beta^{(N)}=\sum_x|x|^\beta\Pi^{(N)}(x)$, one has</p>
<div class="math-display">$$\begin{aligned}
M_\beta^{(0)}&\le W_{\beta,0},\\
M_\beta^{(1)}&\le3^{a_\beta}W_\beta(\Delta^2+2T\Delta),\\
M_\beta^{(N)}&\le(2N+1)^{a_\beta}\bigl[\Delta W_\beta\{2T+(1+j)N\Delta\}r^{N-1}\\
&\hspace{40mm}+(N-1)\Delta^2(T^2W_\beta+H_\beta)r^{N-2}\bigr]\quad(N\ge2).
\end{aligned}$$</div>
<p>In particular, if $r<1$, then $\sum_NM_\beta^{(N)}<\infty$.</p>
<p><em>Proof.</em> For any $m$ displacements,</p>
<div class="math-display">$$\left|\sum_{i=1}^m x_i\right|^\beta\le m^{a_\beta}\sum_{i=1}^m|x_i|^\beta.$$</div>
<p>For $\beta\le1$ this is subadditivity; for $\beta\ge1$ it is the triangle inequality followed by Hölder. Also $w(0)=0$, so the first-step comparison gives $w\tau\le w\widetilde\tau$.</p>
<p>At order zero use the double-connection bound off the origin. At order one, split $x$ along the three displacements in <a href="/tag/NJT0/">NJT0</a>. The middle marked sum is at most $W_\beta\Delta^2$ and each end sum is at most $W_\beta T\Delta$. This proves the first two estimates.</p>
<p>At order $N\ge2$, follow the $2N+1$ displacements of 09JN. Its summations apply to the new nonnegative weight: the two end marks contribute $2T\Delta W_\beta r^{N-1}$; the connector marks contribute at most $N(1+j)\Delta^2W_\beta r^{N-1}$; and the intermediate marks contribute at most $(N-1)\Delta^2(T^2W_\beta+H_\beta)r^{N-2}$. The sums from either end are those of <a href="/tag/RZML/">RZML</a>. Evenness of $w$ permits the reflected marked displacement; its vanishing at zero removes the constrained displacement in the second intermediate diagram. No other property of the cosine weight is used. Multiply the sum of these contributions by $(2N+1)^{a_\beta}$.</p>
<p>For $0<r<1$, each bound is a polynomial in $N$ times a geometric sequence. If $r=0$, then $j=0$: indeed $T\ge\sup_xJ(x)$ since $\tau\ge\delta_0$. This is $p=0$, where all the coefficients vanish. Thus no negative power of zero is needed.</p>

## The marked core is a weighted triangle {#section-core}

<p>Set $K=\tau*\widetilde\tau$ and $L_\beta=\sum_q|q|^\beta\tau(q)\tau^{*2}(q)$. The following bound avoids a separate Fourier estimate for the marked core.</p>
<a id="tag-1VDI" data-assertion="proposition" data-title="A spatial two-point bound makes the polynomially marked diagrams finite"></a>
<p>For any $\beta>0$ for which $T,L_\beta$ are finite,</p>
<div class="math-display">$$H_\beta\le\|K\|_\infty T L_\beta\le T^2L_\beta.$$</div>
<p>If $d>6$ and $\tau(x)\le\Gamma\langle x\rangle^{-(d-2)}$, where $\langle x\rangle=\max\{1,|x|\}$, then $W_\beta,H_\beta$ are finite for every $0<\beta<d-6$. More precisely,</p>
<div class="math-display">$$W_\beta\le C_{d,\beta}j\Gamma^2,\qquad L_\beta\le C_{d,\beta}\Gamma^3,\qquad H_\beta\le C_{d,\beta}T^2\Gamma^3.$$</div>
<p><em>Proof.</em> Expand the second intermediate diagram, calling its internal vertex $z$. Sum the outgoing endpoint and then the common translation of the remaining vertices. With $q=t-u$, $a=u-z$ and $b=z-s$, the marked core at shifts $a_1,a_2$ becomes exactly</p>
<div class="math-display">$$\sum_{q,a,b}|q|^\beta\tau(q)\tau(a)\tau(b)\tau(q+a)
K(a+b+a_1)K(q+a+b-a_2).$$</div>
<p>Bound the first $K$ by its supremum. The sum over $b$ in the remaining $\tau(b)K(q+a+b-a_2)$ is at most $T$. The sum over $a$ is $\tau^{*2}(q)$, giving the asserted bound. Finally $\|K\|_\infty\le T$ because $\tau\ge\delta_0$. All these are nonnegative rearrangements, valid before finiteness is established.</p>
<p>Write $s=d-2$. Nearest-neighbour comparability gives $\widetilde\tau(x)\le2^s j\Gamma\langle x\rangle^{-s}$. Thus $W_\beta$ is bounded by $2^s j\Gamma^2$ times the supremum of the convolution of $\langle x\rangle^{-(s-\beta)}$ and $\langle x\rangle^{-s}$. The power-convolution estimate <a href="/tag/IDIL/">IDIL</a> applies whenever $\beta<d-4$; its resulting decay exponent is $d-4-\beta>0$, so its supremum is finite. Further, $\tau^{*2}(q)\le C_d\Gamma^2\langle q\rangle^{-(d-4)}$. Therefore</p>
<div class="math-display">$$L_\beta\le C_d\Gamma^3\sum_{q\ne0}\langle q\rangle^{-(2d-6-\beta)}<\infty\qquad(\beta<d-6).$$</div>
<p>The last strict inequality is exactly the summability condition from lattice shell counting. It proves the stated range; no endpoint estimate is inferred.</p>

## Uniform moments and the critical limit {#section-critical}

<a id="tag-JJJN" data-assertion="theorem" data-title="A spatial critical bound and a small triangle give higher moments and weighted continuity of the entire lace series"></a>
<p>Suppose $d>6$ and</p>
<div class="math-display">$$\tau_{p_c}(x)\le\Gamma\langle x\rangle^{-(d-2)},\qquad r_c=2T_c\Delta_c<1.$$</div>
<p>For every $0<\beta<d-6$,</p>
<div class="math-display">$$\sup_{0\le p\le p_c}\sum_{N\ge0}\sum_x(1+|x|^\beta)\Pi_p^{(N)}(x)<\infty,$$</div>
<p>and, as $p\uparrow p_c$,</p>
<div class="math-display">$$\sum_{N\ge0}\sum_x(1+|x|^\beta)\left|\Pi_p^{(N)}(x)-\Pi_{p_c}^{(N)}(x)\right|\longrightarrow0.$$</div>
<p>In particular the alternating sum converges in this weighted norm. When $d>8$, it has an absolute $(2+\varepsilon)$-moment for every $0<\varepsilon<d-8$, uniformly in $p\le p_c$.</p>
<p><em>Proof.</em> The spatial hypothesis gives $\Delta_c<\infty$ by IDIL and $T_c\le j_c\Delta_c<\infty$. A finite critical triangle gives almost-sure finiteness of all clusters by <a href="/tag/5W46/">5W46</a>. The preceding proposition makes the critical marked diagrams finite. The chain estimate and SJIL now give a summable bound on both the mass and the $\beta$-moment at each order. Every diagram at $p\le p_c$ is bounded by its critical diagram, even though the lace coefficients themselves need not be monotone. This proves uniform summability. It also gives tails in the order $N$ tending to zero uniformly in $p$.</p>
<p>For each fixed order, use the uniform-edge coupling from <a href="/tag/3W22/">3W22</a>. Almost surely the finitely many critical clusters relevant to any fixed bond tuple are finite, and none of their incident edge variables equals $p_c$. Consequently its cutting events and deleted clusters stabilize as $p\uparrow p_c$. The probability of that tuple converges.</p>
<p>The critical witness diagram bounds each tuple's probability. Multiplying its summands by $1+|x|^\beta$ still gives a summable envelope: this is precisely the weighted diagram sum just proved finite, before alternating or summing over the bond tuples. Dominated convergence over tuples and targets therefore proves convergence in weighted norm at each fixed order. At order zero use the envelope $(1+|x|^\beta)\tau_{p_c}(x)^2$ off the origin, which is summable since $\beta<d-6<d-4$. The uniform order tail then proves the displayed convergence of the entire series. The assertion for the alternating sum follows by the triangle inequality.</p>
<p>This supplies higher moments of all orders in the expansion, rather than only the zeroth and first coefficients. Its spatial two-point hypothesis remains explicit. The estimate is a weighted summability result, not the pointwise bound $|\Pi(x)|=O(\langle x\rangle^{-2(d-2)})$ required by the spatial Gaussian theorem.</p>

## A quantitative quadratic Fourier term {#section-fourier}

<a id="tag-JO75" data-assertion="proposition" data-title="Higher absolute moments give a Hölder Hessian and a quantitative critical Fourier pole"></a>
<p>Let $f$ be a real even kernel on $\mathbb Z^d$ and $0<\alpha\le1$, with $\sum_x(1+|x|^{2+\alpha})|f(x)|<\infty$. Put $M_{2+\alpha}(f)=\sum_x|x|^{2+\alpha}|f(x)|$ and $S(f)=\sum_xxx^{\mathsf T}f(x)$. Then $\widehat f$ is twice continuously differentiable,</p>
<div class="math-display">$$|\partial_i\partial_j\widehat f(k)-\partial_i\partial_j\widehat f(\ell)|
\le2|k-\ell|^\alpha M_{2+\alpha}(f),$$</div>
<p>and</p>
<div class="math-display">$$\widehat f(k)=\widehat f(0)-\tfrac12k^{\mathsf T}S(f)k
+O\!\left(M_{2+\alpha}(f)|k|^{2+\alpha}\right).$$</div>
<p>Under the critical hypotheses of JJJN, choose $0<\alpha\le1$ with $\alpha<d-8$. Write $\Pi=\Pi_{p_c}$, $j=2dp_c$, $Q=jD*(\delta_0+\Pi)$ and $a=1+j\sum_x|x|^2\Pi(x)$. If $a>0$, then</p>
<div class="math-display">$$1-\widehat Q(k)=\frac a{2d}|k|^2+O(|k|^{2+\alpha}),\qquad
\frac{1+\widehat\Pi(k)}{1-\widehat Q(k)}
=\frac{2d}{ja|k|^2}\,[1+O(|k|^\alpha)]\quad(k\to0,\ k\ne0).$$</div>
<p><em>Proof.</em> Absolute second moments justify differentiating the Fourier series twice. In the Hessian difference use $|e^{iu}-e^{iv}|\le2|u-v|^\alpha$ and $|x_ix_j|\le|x|^2$. This gives the displayed Hölder estimate. Alternatively, the scalar inequality</p>
<div class="math-display">$$|\cos u-1+u^2/2|\le C_\alpha|u|^{2+\alpha}$$</div>
<p>follows from Taylor's formula for $|u|\le1$ and the quadratic bound for $|u|>1$. Summing it against $|f(x)|$ gives the expansion directly.</p>
<p>For the application take $\beta=2+\alpha$ in JJJN. Convolution with the finitely supported $D$ preserves this absolute moment. The critical mass identity in 3W22 gives $\sum Q=1$. Coordinate reflections and permutations, together with the convolution moment calculation in <a href="/tag/22TW/">22TW</a>, give $S(Q)=aI/d$. The expansion for $Q$ is therefore the first asserted formula. Since $a>0$, division is valid near zero. The numerator is $1+\widehat\Pi(k)=1/j+O(|k|^2)$, which gives the second formula.</p>
<p>The positivity condition on $a$ is separate; the sufficient small-moment criterion in 22TW is one way to supply it. The expansion concerns the lace quotient. Identifying it with a critical transform and obtaining a spatial asymptotic require the additional arguments already stated in the <a href="/articles/signed-kernel-gaussian-asymptotics/">Gaussian article</a>. Higher moments alone do not replace its pointwise kernel hypothesis. No source error or new Lean proof is asserted here.</p>
