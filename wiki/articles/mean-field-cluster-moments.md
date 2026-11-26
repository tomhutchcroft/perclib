---
{
  "id": "mean-field-cluster-moments",
  "title": "Mean-field cluster moments and the volume cutoff",
  "subtitle": "Gap exponents, fractional moments and the density of large finite clusters",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A cubic second moment fixes every higher moment and the susceptibility-squared volume scale. In sufficiently high dimensions this yields the gap exponent, a critical-window tail bound, and the logarithmic borderline at moment order one half.",
  "context": [
    "The lattice application is nearest-neighbour independent bond percolation on $\\mathbb Z^d$, with vertex cluster size $T_p=|C_0|$ and $q=2d$.",
    "All parameter limits are subcritical. Constants are uniform for $d\\ge d_0$ and $p_c/2\\le p<p_c$, unless dependence on a fixed moment order or cutoff is indicated.",
    "The notation $\\asymp$ denotes two-sided bounds, not convergence of a ratio to one. No numerical value of $d_0$ is asserted."
  ],
  "related": ["cutoff-scaling", "stopped-exploration", "multipoint-trees", "green-free-triangle", "triangle-susceptibility", "correlation-length-fourier"],
  "sourceIds": ["nguyen-gap-1987", "heydenreich-hofstad"],
  "aliases": ["gap exponent", "fractional cluster moments", "subcritical volume cutoff", "large cluster density"],
  "prototypeUses": []
}
---

## From the second moment to every higher moment {#section-moment-comparison}

<p>The essential lower bound is at order two. Once it is known, size bias puts a definite amount of mass at the susceptibility-squared scale; the tree-graph bounds keep that mass from escaping to larger scales.</p>

<a id="tag-2DZD" data-assertion="proposition" data-title="A cubic second moment and tree-graph upper bounds determine all higher moments"></a>
<p>Let $T$ be positive integer-valued, with $\chi=\mathbb ET<\infty$. Suppose $0<\alpha\le1$ and</p>
<div class="math-display">$$\mathbb ET^2\ge\alpha\chi^3,\qquad
\mathbb ET^k\le(2k-3)!!\,\chi^{2k-1}\quad(k=1,2,\ldots).$$</div>
<p>Put $a=\mathbb ET^2/\chi$ and $B=24/\alpha^2$. Then</p>
<div class="math-display">$$\mathbb P(a/2\le T\le B\chi^2)\ge\frac{\alpha^4}{576\chi}.$$</div>
<p>For every fixed real $r\ge1$,</p>
<div class="math-display">$$\mathbb ET^r\asymp_{\alpha,r}\chi^{2r-1},\qquad
\frac{\mathbb ET^{r+1}}{\mathbb ET^r}\asymp_{\alpha,r}\chi^2.$$</div>
<p><em>Proof.</em> Under the <a href="/tag/6L9Z/">size-biased law</a>, $\widehat{\mathbb E}T=a\in[\alpha\chi^2,\chi^2]$ and $\widehat{\mathbb E}T^2\le3\chi^4$. Paley–Zygmund and Markov give</p>
<div class="math-display">$$\widehat{\mathbb P}(T\ge a/2)\ge\frac{\alpha^2}{12},\qquad
\widehat{\mathbb P}(T>B\chi^2)\le\frac1B=\frac{\alpha^2}{24}.$$</div>
<p>On the remaining band, undoing size bias costs at most $B\chi$: since $\mathbb P(A)=\chi\widehat{\mathbb E}[T^{-1}\mathbf1_A]$, its probability is at least $\alpha^2/(24B\chi)$. This proves the first assertion. Its lower endpoint is at least $\alpha\chi^2/2$, so the band also gives the required lower bound for each moment.</p>
<p>For the upper bound, $r=1$ is the definition of $\chi$. If $r>1$, choose an integer $k\ge r$, $k\ge2$, and apply the monotonicity of power means under size bias:</p>
<div class="math-display">$$\mathbb ET^r=\chi\widehat{\mathbb E}T^{r-1}
\le\chi\left(\widehat{\mathbb E}T^{k-1}\right)^{(r-1)/(k-1)}
\le\bigl((2k-3)!!\bigr)^{(r-1)/(k-1)}\chi^{2r-1}.$$</div>
<p>Dividing the two-sided moment bounds proves the ratio assertion. This argument needs no pointwise lower tree-graph inequality and no assumed limiting law for $T/\chi^2$.</p>

## The lattice gap exponent {#section-lattice-gap}

<a id="tag-36ZQ" data-assertion="theorem" data-title="The high-dimensional lattice has a dimension-uniform cubic moment and gap scale"></a>
<p>There is $d_0<\infty$ such that nearest-neighbour bond percolation in every $d\ge d_0$ satisfies, for $p_c/2\le p<p_c$,</p>
<div class="math-display">$$\frac18\chi(p)^3\le\mathbb E_pT_p^2\le\chi(p)^3,\qquad
\frac1{q(p_c-p)}\le\chi(p)\le\frac2{q(p_c-p)}.$$</div>
<p>Consequently, for every fixed real $r\ge1$,</p>
<div class="math-display">$$\mathbb E_pT_p^r\asymp_r\chi(p)^{2r-1}
\asymp_r[q(p_c-p)]^{-(2r-1)},\qquad
\frac{\mathbb E_pT_p^{r+1}}{\mathbb E_pT_p^r}\asymp_r[q(p_c-p)]^{-2}.$$</div>
<p>For each such fixed dimension, the subcritical gap exponent is therefore two, in the bounded-ratio sense.</p>
<p><em>Proof.</em> The completed bootstrap and <a href="/tag/C2V4/">C2V4</a> give $qp_c\ge1$ and, after increasing $d_0$,</p>
<div class="math-display">$$\delta=\max_{e\sim0}\Delta_{p_c}(e)\le\frac12.$$</div>
<p><a href="/tag/0Y4K/">0Y4K</a> gives the displayed susceptibility bounds. In the intensity variable $\beta=-\log(1-p)$, the weighted row sum is $q$ and the same small-triangle argument gives $d\chi/d\beta\ge q(1-\delta)\chi^2$ almost everywhere. The <a href="/tag/4GNM/">exploration-score bound</a> therefore implies</p>
<div class="math-display">$$\mathbb E_pT_p^2\ge\beta q(1-\delta)^2\chi(p)^3\ge\frac18\chi(p)^3$$</div>
<p>almost everywhere on the stated interval: $\beta\ge p\ge p_c/2\ge1/(2q)$. Sharpness gives finite susceptibility, and <a href="/tag/Y84V/">Y84V</a> supplies every finite moment and its upper bound. The coupling argument in <a href="/tag/IK5Y/">IK5Y</a>, applied on any compact subcritical interval, makes the first and second moments continuous. The lower inequality thus extends from almost every parameter to every parameter, including $p_c/2$. Apply the preceding proposition with $\alpha=1/8$.</p>
<p>This supplies the gap-exponent conclusion of the <a href="/coverage/sources/heydenreich-hofstad-2017-correlation-fourier/">Chapter 11 map</a> in the sufficiently-large-dimension regime proved by the classical bootstrap. The manuscript's numerical threshold $d\ge11$, and the general implication from mere finiteness of the critical triangle, require their separate inputs. The second-moment and moment-comparison steps above do not supply those inputs.</p>

## The cutoff tail and fractional moments {#section-cutoff-tail}

<a id="tag-76EV" data-assertion="theorem" data-title="The susceptibility-squared cutoff gives real moment orders and the half-order logarithm"></a>
<p>In the preceding lattice regime there are absolute $c,C>0$ such that, for every integer $n\ge1$,</p>
<div class="math-display">$$\mathbb P_p(T_p\ge n)\le Cn^{-1/2}\exp\!\left[-\frac{n}{4\chi(p)^2}\right],\qquad
\mathbb P_p(T_p\ge n)\ge cn^{-1/2}\quad\left(n\le\frac{\chi(p)^2}{16}\right).$$</div>
<p>For every fixed real $r>0$, these imply</p>
<div class="math-display">$$\mathbb E_pT_p^r\asymp_r
\begin{cases}
\chi(p)^{2r-1},&r>1/2,\\
\log(e\chi(p)),&r=1/2,\\
1,&0<r<1/2.
\end{cases}$$</div>
<p>For $0<r<1/2$ and fixed $d\ge d_0$, these moments converge to the finite critical moment as $p\uparrow p_c$. In particular the gap comparison with $\chi^2$ holds for every $r>1/2$. At $r=1/2$ the ratio instead has order $\chi^2/\log(e\chi)$, and for $0<r<1/2$ it has order $\chi^{2r+1}$.</p>
<p><em>Proof.</em> The critical tail bound <a href="/tag/74SS/">74SS</a> and monotonicity give $\mathbb P_p(T_p\ge n)\le C_0n^{-1/2}$. The weighted exponential estimate <a href="/tag/0BQB/">0BQB</a>, with exponent $1/(4\chi^2)$, gives</p>
<div class="math-display">$$\mathbb P_p(T_p\ge n)\le\frac{\sqrt2\chi}{n}e^{-n/(4\chi^2)}.$$</div>
<p>For $n\ge\chi^2$, its prefactor is at most $\sqrt2/\sqrt n$. For $n\le\chi^2$, the critical upper bound implies the asserted estimate with constant $C_0e^{1/4}$. This proves the upper bound without optimizing over moment order.</p>
<p>For the lower bound write $a(p)=\mathbb E_pT_p^2/\chi(p)$ and $p_0=p_c/2$. The preceding proposition, with $\alpha=1/8$, gives</p>
<div class="math-display">$$\mathbb P_p(T_p\ge a(p)/2)\ge\frac{c_0}{\chi(p)},\qquad
\frac18\chi(p)^2\le a(p)\le\chi(p)^2,\qquad c_0=\frac1{1536^2}.$$</div>
<p>Also $\chi(p_0)\le4$, and $a$ is continuous. If $a(p_0)/2\le n\le\chi(p)^2/16$, then $a(p)\ge2n$. The intermediate value theorem supplies $p'\in[p_0,p]$ with $a(p')=2n$. No monotonicity of $a$ is needed. At this parameter $\chi(p')\le4\sqrt n$, and monotonicity of the cluster event gives $\mathbb P_p(T_p\ge n)\ge c_0/(4\sqrt n)$. If $n<a(p_0)/2$, use the band bound at $p_0$ instead: it gives at least $c_0/4$, which is sufficient. This proves the lower estimate with $c=c_0/4$.</p>
<p>For the moments use the exact tail-sum identity</p>
<div class="math-display">$$\mathbb E_pT_p^r=\sum_{n\ge1}\bigl[n^r-(n-1)^r\bigr]\mathbb P_p(T_p\ge n).$$</div>
<p>For fixed $r>0$, the increment is comparable to $n^{r-1}$. Summation up to order $\chi^2$ gives a power when $r>1/2$, a logarithm when $r=1/2$, and a bounded sum when $r<1/2$. The exponential upper tail bounds the remaining sum by the same order. The lower bound uses $n\le\chi^2/16$; bounded values of $\chi$ are covered by $T_p\ge1$. For $r<1/2$, the critical square-root tail makes $\mathbb E_{p_c}T_{p_c}^r$ finite. Under the uniform-edge coupling, finite path witnesses give $T_p\uparrow T_{p_c}$ almost surely, so monotone convergence identifies the limit. Dividing the resulting moment estimates proves the final ratio statements.</p>
<p>The lower tail estimate stops at a fixed lower multiple of the cutoff. It does not assert an exponential lower bound beyond it or an asymptotic tail profile.</p>

## Counting large finite clusters {#section-large-cluster-density}

<a id="tag-EKKI" data-assertion="proposition" data-title="A fixed lower cutoff has root probability of order inverse susceptibility and cluster density of cubic order"></a>
<p>In the same lattice regime, fix $0<u\le1/16$. Then</p>
<div class="math-display">$$\mathbb P_p(T_p\ge u\chi(p)^2)\asymp_u\chi(p)^{-1},\qquad
\mathbb E_p[T_p^{-1};\ T_p\ge u\chi(p)^2]\asymp_u\chi(p)^{-3}.$$</div>
<p>The second quantity is the expected number per vertex of clusters of size at least $u\chi(p)^2$, with each finite cluster counted once. It therefore has order $[q(p_c-p)]^3$.</p>
<p><em>Proof.</em> In the band of the first proposition, with $\alpha=1/8$, one has</p>
<div class="math-display">$$u\chi^2\le a/2\le T\le1536\chi^2,$$</div>
<p>and the band has probability at least $c_0/\chi$. This proves the probability lower bound and, after multiplying by $(1536\chi^2)^{-1}$, the inverse-volume lower bound. The critical upper tail gives $\mathbb P_p(T_p\ge u\chi^2)\le C u^{-1/2}\chi^{-1}$, with the same conclusion when $u\chi^2<1$ by increasing $C$. On the selected event, $T_p^{-1}\le(u\chi^2)^{-1}$, proving the other upper bound.</p>
<p>For the counting interpretation, choose the lexicographically least vertex of each finite cluster. Each vertex of an eligible cluster sends mass $1/T_p$ to this representative. The outgoing mass at the origin is the inverse-volume quantity; the incoming mass is one exactly when the origin represents an eligible cluster. Translation invariance and Tonelli equate their expectations. All clusters are finite below criticality.</p>
<p>The cutoff here is a fixed sufficiently small multiple of $\chi^2$. The proof does not replace it by the exact moment ratio $a(p)$, nor identify the truncated cluster count with the singular part of the full free energy. The <a href="/coverage/sources/nguyen-gap-1987/">primary-source map</a> records these distinctions. All four assertions are written arguments; they claim no new Lean proof.</p>

<p>A separate <a href="/tag/9TAI/">quantified cutoff theorem</a> now gives these moment regimes for every $d\ge10^{11}$ and $p_c/2\le p<p_c$. Its explicit estimates include $\mathbb E|C_0|^2\ge\chi^3/3$ and a lower tail up to $\chi^2/6$; the older existentially stated results and their tags are unchanged.</p>


## Moments and the cutoff under a finite triangle {#section-finite-triangle-cutoff}

<p>The dimension restrictions in the earlier lattice results arise from obtaining a small triangle with uniform constants. For a fixed model, the corrected boundary inequality supplies the needed lower derivative from a merely finite triangle.</p>

<a id="tag-7T8L" data-assertion="theorem" data-title="A finite critical triangle gives cubic moments, the susceptibility-squared cutoff and all positive moment orders"></a>
<p>In the normalized transitive model of <a href="/tag/ADWR/">ADWR</a>, let $b$ be its finite susceptibility threshold and $D=T_b^3(o,o)<\infty$. Set</p>
<div class="math-display">$$\beta_0=\max\left\{\frac b2,b-\frac1{2D}\right\},\qquad
\alpha=\min\left\{1,\frac1{288b^3D^4}\right\}.$$</div>
<p>For every $\beta_0\le\beta<b$, writing $N=|K_o|$ and $\chi=\chi(\beta)$,</p>
<div class="math-display">$$\alpha\chi^3\le\mathbb E_\beta N^2\le\chi^3.$$</div>
<p>There are $c,C>0$, depending on the model, such that for every such $\beta$ and every integer $n\ge1$,</p>
<div class="math-display">$$\mathbb P_\beta(N\ge n)\le Cn^{-1/2}e^{-n/(4\chi^2)},\qquad
\mathbb P_\beta(N\ge n)\ge cn^{-1/2}\quad\left(n\le\frac\alpha2\chi^2\right).$$</div>
<p>Consequently, for each fixed real $r>0$, uniformly on this parameter interval,</p>
<div class="math-display">$$\mathbb E_\beta N^r\asymp_r
\begin{cases}
\chi^{2r-1},&r>1/2,\\
\log(e\chi),&r=1/2,\\
1,&0<r<1/2.
\end{cases}$$</div>
<p>The ratio $\mathbb E_\beta N^{r+1}/\mathbb E_\beta N^r$ has order $\chi^2$ when $r>1/2$, order $\chi^2/\log(e\chi)$ when $r=1/2$, and order $\chi^{2r+1}$ when $0<r<1/2$. At criticality, $\mathbb E_bN^r<\infty$ holds exactly for $0<r<1/2$, and these finite moments are the limits of the subcritical ones.</p>
<p>For every fixed $0<u\le\alpha/2$, there are also the cutoff comparisons</p>
<div class="math-display">$$\mathbb P_\beta(N\ge u\chi^2)\asymp_u\chi^{-1},\qquad
\mathbb E_\beta[N^{-1};\ N\ge u\chi^2]\asymp_u\chi^{-3}.$$</div>
<p>Constants in these assertions may depend on $b,D$ and the model, as well as the displayed subscripts. For a lattice model satisfying the finite triangle condition, <a href="/tag/I23O/">I23O</a> converts $\chi$ to order $(p_c-p)^{-1}$. In particular the subcritical gap exponent is two without a small-triangle hypothesis.</p>
<p><em>Proof.</em> ADWR gives $\chi(\beta)\ge(b-\beta)^{-1}\ge2D$ for $\beta\ge\beta_0$. The corrected quadratic bound therefore implies</p>
<div class="math-display">$$\chi'(\beta)\ge\frac{\chi(\beta)^2}{12b^2D^2}$$</div>
<p>almost everywhere on $(\beta_0,b)$. The weight row is one. Apply the <a href="/tag/4GNM/">exploration-score inequality</a> with $c_*=1/(12b^2D^2)$ to obtain</p>
<div class="math-display">$$\mathbb E_\beta N^2\ge\beta c_*^2\chi(\beta)^3
\ge\frac{\chi(\beta)^3}{288b^3D^4}$$</div>
<p>almost everywhere. The <a href="/tag/Y84V/">tree-graph bounds</a> give all upper moments, and <a href="/tag/IK5Y/">subcritical moment continuity</a> extends the lower inequality to every parameter in the stated interval, including $\beta_0$.</p>
<p>Put $a(\beta)=\mathbb E_\beta N^2/\chi(\beta)$, $B=24/\alpha^2$ and $c_0=\alpha^4/576$. The <a href="/tag/2DZD/">size-biased band estimate</a> gives</p>
<div class="math-display">$$\alpha\chi(\beta)^2\le a(\beta)\le\chi(\beta)^2,\qquad
\mathbb P_\beta\bigl(a(\beta)/2\le N\le B\chi(\beta)^2\bigr)\ge\frac{c_0}{\chi(\beta)}.$$</div>
<p>If $a(\beta_0)/2\le n\le\alpha\chi(\beta)^2/2$, continuity supplies $\beta'\in[\beta_0,\beta]$ with $a(\beta')=2n$. At that parameter $\chi(\beta')\le\sqrt{2n/\alpha}$. Monotonicity of the cluster event yields the lower tail with constant $c_0\sqrt{\alpha/2}$. For $n<a(\beta_0)/2$, the band estimate at $\beta_0$ gives a lower bound $c_0/\chi(\beta_0)$, which suffices after reducing $c$. No monotonicity of the moment ratio $a$ is assumed.</p>
<p>ADWR and monotonicity give $\mathbb P_\beta(N\ge n)\le C_0n^{-1/2}$. The <a href="/tag/0BQB/">weighted exponential estimate</a> gives the additional bound</p>
<div class="math-display">$$\mathbb P_\beta(N\ge n)\le\frac{\sqrt2\chi}{n}e^{-n/(4\chi^2)}.$$</div>
<p>Use this for $n\ge\chi^2$ and the critical bound for $n\le\chi^2$; $C=\max\{\sqrt2,C_0e^{1/4}\}$ works. Summing the tails with increments $n^r-(n-1)^r\asymp_r n^{r-1}$ now gives the three moment regimes: the sum up to order $\chi^2$ is a power, a logarithm or a bounded sum according as $r$ is above, at or below $1/2$, and the exponential tail bounds the remainder. Bounded values of $\chi$ are covered by $N\ge1$. Dividing these comparisons gives the ratios. The two-sided critical square-root tail gives the stated criterion for finite critical moments; finite path witnesses and monotone convergence identify their subcritical limits.</p>
<p>Finally, for $u\le\alpha/2$ the entire size-biased band lies in $\{N\ge u\chi^2\}$. It gives the probability lower bound and, using $N\le B\chi^2$, the inverse-volume lower bound. The critical upper tail gives the probability upper bound of order $u^{-1/2}\chi^{-1}$, while $N^{-1}\le(u\chi^2)^{-1}$ on this event gives the other upper bound. On the lattice the inverse-volume expectation is the large-cluster count per vertex by the mass-transport argument in <a href="/tag/EKKI/">EKKI</a>.</p>
<p>The lower tail is proved only up to a fixed lower multiple of the cutoff. These estimates do not identify a limiting cutoff profile or the singular part of the free energy. Their model-dependent constants are distinct from the uniform high-dimensional constants in the earlier statements.</p>
