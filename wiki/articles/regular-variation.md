---
{
  "id": "regular-variation",
  "title": "Regular variation and Karamata's Tauberian theorem",
  "subtitle": "Regularly varying tails and the Gamma constant in their Laplace transforms",
  "kind": "method",
  "category": "Methods",
  "summary": "Karamata's Tauberian theorem: a tail that varies regularly with index between minus one and zero corresponds exactly to a regularly varying Laplace transform, with a Gamma-function constant. In percolation it converts cluster-volume tails into magnetization asymptotics and back.",
  "context": [],
  "related": ["ghost-fields", "branching-processes", "binary-tree-percolation", "susceptibility"],
  "sourceIds": ["hutchcroft-book", "perclib-train10-analysis-regularvariation-defs"],
  "aliases": ["Karamata", "Tauberian", "slowly varying", "regular variation", "Laplace", "Gamma constant"],
  "prototypeUses": []
}
---

<p>A regularly varying function behaves like a power $x^\rho$ up to a slowly varying factor, such as a power of $\log x$. Regular variation is the class of tail behaviours that is stable under integration, Laplace transformation and inversion, and so the setting in which exact constants survive these operations. Its central result is Karamata's Tauberian theorem, which in probabilistic form states that, for a nonnegative random variable $X$, $0&lt;\alpha&lt;1$ and a slowly varying function $L$, $\mathbb P(X&gt;t)\sim t^{-\alpha}L(t)$ as $t\to\infty$ if and only if $1-\mathbb E e^{-hX}\sim\Gamma(1-\alpha)h^\alpha L(1/h)$ as $h\downarrow0$ (Karamata, 1931; Feller, Vol. II, XIII.5).</p>

<p>In percolation, $1-\mathbb E e^{-h|K|}$ is the <a href="/tag/VF24/">magnetization</a> $M(h)$ at <a href="/articles/ghost-fields/">ghost-field</a> intensity $h$, where $K$ is the cluster of the origin. The theorem therefore translates a cluster-volume tail into the small-field behaviour of the magnetization, and back, with the exact constant. The standard example is the <a href="/tag/PVM9/">exact progeny tail</a> $\mathbb P(T\geq n)\sim\sqrt{2/(\pi\sigma^2)}\,n^{-1/2}$ of a critical <a href="/articles/branching-processes/">Galton–Watson process</a>. For bounds up to constants by a pure power, the same translation holds without regular variation (<a href="/tag/3C2F/">two-sided version</a>); in this form the <a href="/articles/triangle-condition/">mean-field</a> value $\delta=2$ of the <a href="/tag/U5MC/">volume-tail exponent</a> appears both as $\mathbb P(|K|\geq n)\asymp n^{-1/2}$ and as $M(h)\asymp h^{1/2}$. Regularly varying tails and their transforms are also the language of the scaling analysis of critical long-range percolation (Hutchcroft, 2025).</p>

## Definitions and setting {#section-definition}

<a id="tag-3491" data-assertion="definition" data-title="Slow and regular variation at infinity"></a><p>A function $L$, defined, positive and measurable on some half-line $[a,\infty)$, is slowly varying at infinity if $L(\lambda x)/L(x)\to1$ for every fixed $\lambda&gt;0$. A function $f$, defined, positive and measurable on some half-line $[a,\infty)$, is regularly varying with index $\rho$ if $f(x)=x^\rho L(x)$ for such an $L$; equivalently, $f(\lambda x)/f(x)\to\lambda^\rho$ for every fixed $\lambda&gt;0$.</p><p>Powers of $\log x$ and $\log\log x$, restricted to sufficiently large $x$, are slowly varying. Thus $x^{-\alpha}(\log x)^a$ has index $-\alpha$, even though its ratio to $x^{-\alpha}$ need not approach a positive constant.</p>
:::details Verification of the equivalence of the two forms
<p><a id="section-tail-interface"></a>For $c,x&gt;0$, division by the power gives</p>
<div class="math-display">$$\frac{f(cx)/(cx)^\rho}{f(x)/x^\rho}=c^{-\rho}\frac{f(cx)}{f(x)}.$$</div>
<p>Hence $f(cx)/f(x)\to c^\rho$ for every $c&gt;0$ if and only if $L(x)=f(x)/x^\rho$ satisfies $L(cx)/L(x)\to1$ for every $c&gt;0$. If $f$ is positive and measurable on $[a,\infty)$, then $L=f/x^\rho$ is positive and measurable on $[b,\infty)$ for every $b\geq a$ with $b&gt;0$, since $x\mapsto x^\rho$ is positive and continuous on $(0,\infty)$.</p>
:::
<p>Following Feller, this article writes $L$ for a slowly varying function; other articles of the wiki write $\ell$, as Bingham, Goldie and Teugels do. Only the values on a half-line matter: two functions that agree on some $[b,\infty)$ are both regularly varying with the same index, or neither is. A function $g$, defined, positive and measurable on some interval $(0,b]$, is regularly varying at zero with index $\rho$ if $x\mapsto g(1/x)$ is regularly varying at infinity with index $-\rho$; equivalently, $g(\lambda h)/g(h)\to\lambda^\rho$ as $h\downarrow0$, for every $\lambda&gt;0$.</p>
<h3 id="section-normalization">Laplace transforms and tails</h3>
<p>For a nonnegative random variable $X$, finite almost surely, write $M_X(h)=\mathbb E[1-e^{-hX}]$ for $h&gt;0$, one minus the Laplace transform of the law of $X$. When $X=|K|$ is the volume of a percolation cluster, $M_X$ is the <a href="/tag/VF24/">magnetization</a> of the ghost field. It is an average of the tail of $X$.</p>
<a id="tag-LTJ1" data-assertion="proposition" data-title="Tail integral for one minus the Laplace transform"></a><p>Let $X$ be a nonnegative random variable, finite almost surely, and $M_X(h)=\mathbb E[1-e^{-hX}]$. For every $h&gt;0$,</p><div class="math-display">$$M_X(h)=h\int_0^\infty e^{-ht}\mathbb P(X&gt;t)\,dt=\int_0^\infty e^{-u}\mathbb P(X&gt;u/h)\,du.$$</div>
:::details Proof
<p>Integrate $he^{-ht}$ from zero to $X$, then apply Tonelli's theorem to the nonnegative integrand. The second equality is the change of variables $u=ht$.</p>
:::
<p>For integer-valued $X$ the tail is a step function, and the identity becomes the <a href="/tag/0NVH/">discrete tail transform</a> of the ghost-field article.</p>

## Statement {#section-karamata}

<a id="tag-SLGY" data-assertion="theorem" data-title="Karamata's Tauberian theorem for regularly varying tails"></a><p>Let $X$ be a nonnegative random variable, finite almost surely, and $M_X(h)=\mathbb E[1-e^{-hX}]$. Let $0&lt;\alpha&lt;1$ and let $L$ be positive, measurable and slowly varying at infinity. Then</p><div class="math-display">$$\mathbb P(X&gt;t)\sim t^{-\alpha}L(t)\quad(t\to\infty)$$</div><p>if and only if</p><div class="math-display">$$M_X(h)\sim\Gamma(1-\alpha)h^\alpha L(1/h)\quad(h\downarrow0).$$</div><p>For integer-valued $X$, one may equivalently write $\mathbb P(X\geq n)\sim n^{-\alpha}L(n)$.</p>
<p>The implication from the tail to the transform is the Abelian half of the theorem, and the converse the Tauberian half. The statement is given for $0&lt;\alpha&lt;1$. It also holds at $\alpha=0$, where $\Gamma(1)=1$, by the <a href="#section-general-tauberian">Tauberian theorem for measures</a>. For $\alpha\geq1$ the leading term of $M_X(h)$ is <a href="#section-large-index">governed by the mean</a> of $X$, or by a truncated mean when $\alpha=1$.</p>
:::details Verification of the integer-valued form
<p>The two forms of the tail condition are equivalent because $\mathbb P(X&gt;t)=\mathbb P(X\geq\lfloor t\rfloor+1)$ for real $t$ and $\mathbb P(X\geq n)=\mathbb P(X&gt;n-\tfrac12)$ for integers $n$, while $s^{-\alpha}L(s)\sim t^{-\alpha}L(t)$ as $t\to\infty$ with $s/t\to1$, by the <a href="#section-uniform-convergence">uniform convergence theorem</a>.</p>
:::

## Examples and non-examples {#section-examples}

<p>A constant multiple $cx^\rho$, $c&gt;0$, is regularly varying with index $\rho$, and so is $x^\rho(\log x)^a(\log\log x)^b$ for all real $a,b$, restricted to large $x$. A slowly varying function need not converge or be eventually monotone: $L(x)=\exp\{(\log x)^{1/3}\cos((\log x)^{1/3})\}$ is slowly varying, because the derivative of $y\mapsto y^{1/3}\cos(y^{1/3})$ tends to zero as $y\to\infty$, yet $\liminf_{x\to\infty}L(x)=0$ and $\limsup_{x\to\infty}L(x)=\infty$ (Bingham, Goldie and Teugels, 1.3.3).</p>
<p>A function of power order need not be regularly varying. For $0&lt;\alpha&lt;1$ let $f(x)=x^{-\alpha}\bigl(1+\tfrac\alpha2\sin\log x\bigr)$. Then $\tfrac12x^{-\alpha}\leq f(x)\leq\tfrac32x^{-\alpha}$, but</p>
<div class="math-display">$$\frac{f(\lambda x)}{f(x)}=\lambda^{-\alpha}\,\frac{1+\frac\alpha2\sin(\log x+\log\lambda)}{1+\frac\alpha2\sin\log x}$$</div>
<p>has no limit as $x\to\infty$ unless $\log\lambda\in2\pi\mathbb Z$, and the same holds along the integers, whose logarithms are dense modulo $2\pi$. There is an integer-valued random variable $X$ with $\mathbb P(X\geq n)=f(n)$. Then $M_X(h)\asymp h^\alpha$ by the <a href="/tag/3C2F/">two-sided equivalence for power orders</a>, but $M_X$ is not regularly varying at zero; for such $X$ the tail and $M_X$ are related only up to constants.</p>
:::details Verification
<p>The derivative $f'(x)=x^{-\alpha-1}\bigl(-\alpha-\frac{\alpha^2}2\sin\log x+\frac\alpha2\cos\log x\bigr)$ is negative, since the bracket is at most $-\alpha+\frac\alpha2\sqrt{1+\alpha^2}&lt;0$, and $f(1)=1$, so $\mathbb P(X\geq n)=f(n)$ defines a random variable with values in $\{1,2,\dots\}$. The <a href="/tag/3C2F/">two-sided equivalence</a> gives $M_X(h)\asymp h^\alpha$. If $M_X$ were regularly varying at zero, its index would be $\alpha$, since it is bounded above and below by multiples of $h^\alpha$; then $L(x)=x^\alpha M_X(1/x)/\Gamma(1-\alpha)$ would be slowly varying, and the <a href="/tag/SLGY/">theorem</a> would make the tail regularly varying, which it is not.</p>
:::

## Idea of the proof {#section-idea}

<p>Write $F(t)=\mathbb P(X&gt;t)$ and $x=1/h$. By the <a href="/tag/LTJ1/">tail-integral formula</a>, $M_X(1/x)/F(x)=\int_0^\infty e^{-u}F(ux)/F(x)\,du$. For the Abelian half, regular variation gives $F(ux)/F(x)\to u^{-\alpha}$ for each $u&gt;0$, dyadic bounds of Potter type dominate the integrand by an integrable function of $u$, and dominated convergence gives the limit $\int_0^\infty e^{-u}u^{-\alpha}\,du=\Gamma(1-\alpha)$.</p>
<p>The Tauberian half needs one more ingredient, because asymptotics of a transform only determine limits of rescaled measures. Evaluating $M_X$ at the points $(n+1)/x$, $n=0,1,2,\dots$, gives the polynomial moments of the measures $e^{-u}F(xu)\,du/a(x)$, $a(x)=x^{-\alpha}L(x)$, after the substitution $z=e^{-u}$; Weierstrass approximation identifies their limit and gives convergence of the averages $\int_r^sF(xu)\,du/a(x)$. The tail $F$ is nonincreasing, and this monotonicity turns convergence of averages into convergence of $F(x)/a(x)$ itself. Monotonicity is the Tauberian condition; since every tail is monotone, no further hypothesis appears in the statement.</p>

## Proof {#section-proof}

:::details Proof of the forward implication (Abelian half)
<p>Write $F(t)=\mathbb P(X&gt;t)$ and $x=1/h$. The tail assumption gives $F(ux)/F(x)\to u^{-\alpha}$ for every $u&gt;0$. We need an integrable bound to pass to the limit in</p>
<div class="math-display">$$\frac{M_X(1/x)}{F(x)}=\int_0^\infty e^{-u}\frac{F(ux)}{F(x)}\,du.$$</div>
<p>Choose $0&lt;\varepsilon&lt;\min\{\alpha,1-\alpha\}$. Since $F(2t)/F(t)\to2^{-\alpha}$, there is $x_0&gt;0$ such that $F(t)&gt;0$ and</p>
<div class="math-display">$$2^{-\alpha-\varepsilon}\leq\frac{F(2t)}{F(t)}\leq2^{-\alpha+\varepsilon}\qquad(t\geq x_0).$$</div>
<p>Iteration on dyadic scales, together with monotonicity of $F$, gives a constant $C$ such that, whenever $x\geq x_0$ and $ux\geq x_0$,</p>
<div class="math-display">$$\frac{F(ux)}{F(x)}\leq C\begin{cases}u^{-\alpha-\varepsilon},&amp;0&lt;u\leq1,\\u^{-\alpha+\varepsilon},&amp;u\geq1.\end{cases}$$</div>
<p>Indeed, for $u\geq1$ iterate the upper ratio bound from $x$ to the last dyadic point below $ux$. For $u\leq1$, iterate the lower bound from $ux$ to the first dyadic point at or above $x$, then use monotonicity there. The same lower bound, iterated from $x_0$, shows $xF(x)\to\infty$: on $2^kx_0\leq x&lt;2^{k+1}x_0$,</p>
<div class="math-display">$$xF(x)\geq2^kx_0F(2^{k+1}x_0)\geq x_0F(x_0)\,2^{-\alpha-\varepsilon}\,2^{k(1-\alpha-\varepsilon)}\longrightarrow\infty.$$</div>
<p>The part of the integral with $ux&lt;x_0$ is at most $x_0/(xF(x))$, which tends to zero. On the remaining part, the displayed bound times $e^{-u}$ is integrable: $\alpha+\varepsilon&lt;1$ controls zero and the exponential controls infinity. Dominated convergence now gives</p>
<div class="math-display">$$\frac{M_X(1/x)}{F(x)}\longrightarrow\int_0^\infty e^{-u}u^{-\alpha}\,du=\Gamma(1-\alpha).$$</div>
<p>Substituting $F(x)\sim x^{-\alpha}L(x)$ gives $M_X(h)\sim\Gamma(1-\alpha)h^\alpha L(1/h)$.</p>
:::
:::details Proof of the converse (Tauberian half)
<p>Suppose $M_X(h)\sim\Gamma(1-\alpha)h^\alpha L(1/h)$ as $h\downarrow0$, and put $a(x)=x^{-\alpha}L(x)$. Define finite measures on $[0,\infty)$ by</p>
<div class="math-display">$$d\mu_x(u)=e^{-u}\frac{F(xu)}{a(x)}\,du,\qquad d\mu(u)=e^{-u}u^{-\alpha}\,du.$$</div>
<p>For each integer $n\geq0$, the tail integral and slow variation give</p>
<div class="math-display">$$\int_0^\infty e^{-nu}\,d\mu_x(u)=\frac{M_X((n+1)/x)}{(n+1)a(x)}\longrightarrow\Gamma(1-\alpha)(n+1)^{\alpha-1}=\int_0^\infty e^{-nu}\,d\mu(u).$$</div>
<p>Push these measures forward by $z=e^{-u}$ to $[0,1]$. The displayed limits give convergence of every polynomial moment, including the total mass at $n=0$. Uniform polynomial approximation on $[0,1]$ therefore gives convergence of integrals of every continuous function. The limit measure has no atoms. For $0&lt;r&lt;s&lt;\infty$, we may consequently also integrate the bounded function $z^{-1}\mathbf1_{[e^{-s},e^{-r}]}(z)$, defined to be zero outside that interval: approximate it by continuous functions across its two endpoints. Undoing the change of variables yields</p>
<div class="math-display">$$\int_r^s\frac{F(xu)}{a(x)}\,du\longrightarrow\int_r^s u^{-\alpha}\,du.$$</div>
<p>Monotonicity of $F$ now recovers its value at $x$. For $0&lt;\delta&lt;1$,</p>
<div class="math-display">$$\frac1\delta\int_1^{1+\delta}\frac{F(xu)}{a(x)}\,du\leq\frac{F(x)}{a(x)}\leq\frac1\delta\int_{1-\delta}^1\frac{F(xu)}{a(x)}\,du.$$</div>
<p>Take the lower and upper limits as $x\to\infty$, then let $\delta\downarrow0$. Both bounding averages tend to one, so $F(x)\sim a(x)$, as required.</p>
:::

## Consequences and applications {#section-consequences}

<h3 id="section-progeny">The critical progeny constant</h3>
<a id="tag-PVM9" data-assertion="corollary" data-title="Exact critical total-progeny tail constant"></a><p>For a <a href="/articles/branching-processes/">Galton–Watson process</a> started from one individual with offspring mean one and variance $0&lt;\sigma^2&lt;\infty$, its total progeny satisfies</p><div class="math-display">$$\mathbb P(T\geq n)\sim\sqrt{\frac{2}{\pi\sigma^2}}\,n^{-1/2}.$$</div>
:::details Proof
<p><a href="/tag/BFM4/">Critical extinction</a> gives $T&lt;\infty$ almost surely. The <a href="/tag/OVG9/">critical generating-function asymptotic</a> $1-\mathbb E[s^T]\sim\sqrt{2(1-s)/\sigma^2}$ as $s\uparrow1$, taken at $s=e^{-h}$, and $1-e^{-h}\sim h$ give $\mathbb E[1-e^{-hT}]\sim\sqrt{2/\sigma^2}\,h^{1/2}$. Apply the <a href="/tag/SLGY/">theorem</a> with $\alpha=1/2$ and $\Gamma(1/2)=\sqrt\pi$.</p>
:::
<p>For critical percolation on the rooted binary tree the root cluster is a Galton–Watson tree with offspring law $\operatorname{Bin}(2,1/2)$, so $\sigma^2=1/2$ and the constant is $2/\sqrt\pi$, the value of the <a href="/tag/AAZS/">exact binary-tree asymptotics</a> obtained directly from the <a href="/tag/9K6O/">Catalan law</a>.</p>
<h3 id="section-cluster-tails">Cluster tails and magnetization</h3>
<p>When the cluster $K$ of the origin is finite almost surely, the theorem with $X=|K|$ states that $\mathbb P(|K|&gt;t)\sim t^{-\alpha}L(t)$ if and only if the <a href="/tag/VF24/">magnetization</a> satisfies $M(h)\sim\Gamma(1-\alpha)h^\alpha L(1/h)$. Exact volume-tail asymptotics are obtained this way from field asymptotics: in the passage from cutoff to full laws in <a href="/articles/size-biased-laws/">size-biased laws</a>, a limit of ghost transforms at a fixed cutoff scale is shown to be regularly varying at zero, and the theorem converts it into the <a href="/tag/9PSJ/">full tail equivalent</a>. When only bounds up to constants are available, the <a href="/tag/3C2F/">two-sided version</a> takes its place, as in the <a href="/articles/mesoscopic-tail-transfer/">transfer from cutoff mass to a full volume tail</a>.</p>

## Variants and generalisations {#section-variants}

<p><a id="section-general-tauberian"></a>Karamata's theorem holds for measures. Let $U$ be nondecreasing and right-continuous on $[0,\infty)$, with $\hat U(\lambda)=\int_{[0,\infty)}e^{-\lambda t}\,dU(t)$ finite for $\lambda&gt;0$; let $\rho\geq0$ and let $L$ be slowly varying. Then $U(t)\sim t^\rho L(t)$ as $t\to\infty$ if and only if $\hat U(\lambda)\sim\Gamma(1+\rho)\lambda^{-\rho}L(1/\lambda)$ as $\lambda\downarrow0$ (Feller, Vol. II, XIII.5, Theorem 2; Bingham, Goldie and Teugels, Theorem 1.7.1). For $U(t)=\int_0^t\mathbb P(X&gt;s)\,ds$ the <a href="/tag/LTJ1/">tail-integral formula</a> gives $\hat U(\lambda)=M_X(\lambda)/\lambda$, so the theorem with $\rho=1-\alpha$ turns the asymptotic of $M_X$ into $U(t)\sim t^{1-\alpha}L(t)/(1-\alpha)$, and the monotone density theorem (Bingham, Goldie and Teugels, Theorem 1.7.2), which applies because the tail is monotone, recovers $\mathbb P(X&gt;t)\sim t^{-\alpha}L(t)$. This route also covers $\alpha=0$.</p>
<p><a id="section-large-index"></a>For $\alpha\geq1$, $M_X$ is governed by the mean. If $0&lt;\mathbb EX&lt;\infty$, then $M_X(h)\sim h\,\mathbb EX$; for $X=|K|$ this is the <a href="/tag/8B62/">susceptibility slope</a> $M(h)/h\to\chi$, where $\chi$ is the <a href="/articles/susceptibility/">susceptibility</a>. At $\alpha=1$ the general theorem with $\rho=0$ gives $M_X(h)\sim h\int_0^{1/h}\mathbb P(X&gt;t)\,dt$, a truncated mean from which the tail cannot be recovered. For $\alpha&gt;1$ the tail index appears in the lower-order terms of $M_X$ (Bingham, Goldie and Teugels, Chapter 8).</p>
<p>A tail equivalent concerns $\mathbb P(X&gt;t)$ only; point probabilities and densities need a local argument. If $X$ has an eventually monotone density $g$ and $\mathbb P(X&gt;t)\sim t^{-\alpha}L(t)$ with $\alpha&gt;0$, then $g(t)\sim\alpha t^{-\alpha-1}L(t)$, by the monotone density theorem. For the total progeny $T$ of a critical <a href="/articles/branching-processes/">Galton–Watson process</a> with offspring variance $0&lt;\sigma^2&lt;\infty$, the hitting-time identity $\mathbb P(T=n)=n^{-1}\mathbb P(\xi_1+\dots+\xi_n=n-1)$ for independent offspring numbers $\xi_i$ (Dwass, 1969) and the lattice local limit theorem give $\mathbb P(T=n)\sim d\,(2\pi\sigma^2)^{-1/2}n^{-3/2}$ as $n\to\infty$ through $n\equiv1\pmod d$, where $d$ is the greatest common divisor of the support of the offspring law, and $\mathbb P(T=n)=0$ for all other $n$. For offspring zero or two with equal probabilities, $\sigma^2=1$ and $d=2$: the total progeny is always odd, yet the tail equivalent $\mathbb P(T\geq n)\sim\sqrt{2/\pi}\,n^{-1/2}$ holds, as the <a href="/tag/AGPB/">exact periodic progeny law</a> also shows.</p>
<p>The proofs above use special cases of the basic theorems on regularly varying functions (Bingham, Goldie and Teugels, Chapter 1). <a id="section-uniform-convergence"></a>For measurable slowly varying $L$, $L(\lambda x)/L(x)\to1$ uniformly for $\lambda$ in compact subsets of $(0,\infty)$ (uniform convergence theorem, Theorem 1.2.1). If $f$ is regularly varying with index $\rho$, then for every $A&gt;1$ and $\delta&gt;0$ there is $x_0$ such that $f(y)/f(x)\leq A\max\{(y/x)^{\rho+\delta},(y/x)^{\rho-\delta}\}$ for all $x,y\geq x_0$ (Potter's bounds, Theorem 1.5.6); the dyadic bound in the proof of the forward implication is a form of these. If $L$ is slowly varying and locally bounded on $[a,\infty)$ and $\beta&gt;-1$, then $\int_a^xt^\beta L(t)\,dt\sim x^{\beta+1}L(x)/(\beta+1)$ (Karamata's integral theorem, Proposition 1.5.8).</p>
<p><a id="section-log-error-interface"></a>Regular variation passes to inverses. If $f$ is regularly varying with index $\rho&gt;0$ and locally bounded on $[a,\infty)$, then $f(x)\to\infty$, and the generalized inverse $f^{\leftarrow}(y)=\inf\{x\geq a:f(x)\geq y\}$ is regularly varying with index $1/\rho$ and satisfies $f(f^{\leftarrow}(y))\sim y$ and $f^{\leftarrow}(f(x))\sim x$ (Theorem 1.5.12). Inverse functions of this kind set the scales in the <a href="/tag/9PSJ/">cutoff-to-full tail theorem</a>.</p>

## History and attribution {#section-history}

<p>Tauberian theorems go back to Tauber (1897) and to Hardy and Littlewood (1914), who proved converses of Abel's theorem for power series with nonnegative coefficients. In 1930 Karamata gave the short proof of the Hardy–Littlewood theorem by polynomial approximation, the method of the converse above, and introduced regularly varying functions. In 1931 he extended the Tauberian theorem to Laplace–Stieltjes transforms with slowly varying factors. Feller's textbook (Vol. II, 1966; 2nd ed. 1971) made regular variation a standard tool of probability theory, and the monograph of Bingham, Goldie and Teugels (1987) is the reference for the theory. In percolation the theorem links the volume-tail exponent with the field exponent of the magnetization; regularly varying tails and transforms are used throughout Hutchcroft's analysis of critical long-range percolation (2025). Parts of this exposition follow T. Hutchcroft, book in preparation.</p>

## References {#section-references}

<ul>
<li>N. H. Bingham, C. M. Goldie and J. L. Teugels, <em>Regular Variation</em>, Cambridge University Press, 1987.</li>
<li>M. Dwass, The total progeny in a branching process and a related random walk, <em>J. Appl. Probab.</em> 6 (1969), 682–686.</li>
<li>W. Feller, <em>An Introduction to Probability Theory and Its Applications</em>, Vol. II, 2nd ed., Wiley, 1971, Sections VIII.8 and XIII.5.</li>
<li>G. H. Hardy and J. E. Littlewood, Tauberian theorems concerning power series and Dirichlet's series whose coefficients are positive, <em>Proc. London Math. Soc.</em> (2) 13 (1914), 174–191.</li>
<li>T. Hutchcroft, Critical long-range percolation I, <a href="https://arxiv.org/abs/2508.18807v1">arXiv:2508.18807</a> (2025).</li>
<li>J. Karamata, Über die Hardy–Littlewoodschen Umkehrungen des Abelschen Stetigkeitssatzes, <em>Math. Z.</em> 32 (1930), 319–320.</li>
<li>J. Karamata, Sur un mode de croissance régulière des fonctions, <em>Mathematica (Cluj)</em> 4 (1930), 38–53.</li>
<li>J. Karamata, Neuer Beweis und Verallgemeinerung der Tauberschen Sätze, welche die Laplacesche und Stieltjessche Transformation betreffen, <em>J. Reine Angew. Math.</em> 164 (1931), 27–39.</li>
<li>E. Seneta, <em>Regularly Varying Functions</em>, Lecture Notes in Mathematics 508, Springer, 1976.</li>
<li>A. Tauber, Ein Satz aus der Theorie der unendlichen Reihen, <em>Monatsh. Math. Phys.</em> 8 (1897), 273–277.</li>
</ul>
