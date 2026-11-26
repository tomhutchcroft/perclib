---
{
  "id": "characteristic-field-growth",
  "title": "Characteristic field growth",
  "subtitle": "A polynomial repair of the supercritical lower bound",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Following a characteristic of the magnetization inequality gives a lower bound from the finite zero-field susceptibility. This removes the logarithmic loss and yields matching supercritical tail bounds with an explicit polynomial error.",
  "context": [
    "Finite connected simple vertex-transitive graphs, independent bond percolation and independent vertex marks.",
    "The characteristic lower bound requires no triangle estimate; its tail consequences state their reference and strong-triangle hypotheses separately.",
    "The proof uses a finite zero-field derivative, not an exchange of finite and infinite volume limits."
  ],
  "related": [
    "sharp-supercritical-field",
    "sharp-upper-field",
    "finite-supercritical-clusters",
    "finite-triangle-window"
  ],
  "sourceIds": [
    "hofstad-nachmias-hypercube",
    "borgs-chayes-finite-window"
  ],
  "aliases": [
    "characteristic magnetization lower bound",
    "supercritical polynomial tail error",
    "lower field rectangle repair"
  ],
  "prototypeUses": []
}
---

## A characteristic starting at zero field {#section-characteristic}

<p>Let $G$ be a finite connected simple vertex-transitive graph of degree $m\ge1$. Write</p>
<div class="math-display">$$M(p,\gamma)=\mathbb E_p[1-(1-\gamma)^{|C_o|}],\qquad H=\chi(p_0),\qquad r_i=mp_i,$$</div>
<p>where $0<p_0<p_1<1$. The field marks vertices independently with probability $\gamma$. The sharpened differential inequality <a href="/tag/BJU4/">BJU4</a> will supply the whole argument:</p>
<div class="math-display">$$M\le\gamma M_\gamma+\left(\frac{mp}{2}M+\gamma\right)(M+pM_p).$$</div>
<p>Using a characteristic curve instead of a rectangle keeps the field and bond parameters in their valid ranges. In particular, no lower-bound seed is transported to a displacement below its regime.</p>

<a id="tag-5ZBS" data-assertion="theorem" data-title="A finite characteristic lower bound from the zero-field susceptibility"></a>
<p>Put $A=r_0H$ and define</p>
<div class="math-display">$$\gamma_* =\frac{2\log(r_1/r_0)}{A+2},\qquad B=\frac{A\gamma_*}{r_1}.$$</div>
<p>For every $0\le\gamma\le1$,</p>
<div class="math-display">$$M(p_1,\gamma)\ge\frac A{r_1}\min\{\gamma,\gamma_*\}.$$</div>
<p>Thus $M(p_1,\gamma)\ge B$ whenever $\gamma_*\le\gamma\le1$. No triangle bound is assumed.</p>
<p><em>Proof.</em> Take $0<\gamma<1$; the endpoints follow by continuity. Set $f(r,g)=M(r/m,g)$. The quotient $f(r,g)/g$ extends smoothly to $g=0$, with value $\chi(r/m)$: for a cluster of size $s$ the quotient is $\sum_{j=0}^{s-1}(1-g)^j$, and the finite expectation is polynomial. Starting at $r(0)=r_0$, solve</p>
<div class="math-display">$$r'(g)=r(g)\left(1+\frac{r(g)f(r(g),g)}{2g}\right)$$</div>
<p>until $g=\gamma$ or the first time $r(g)=r_1$. The smooth extension defines the vector field at zero. It is bounded and locally Lipschitz on the compact rectangle, so the stopped solution exists; also $r'(g)>0$.</p>
<p>Along the curve put $y(g)=r(g)f(r(g),g)$. For $g>0$, the differential inequality gives</p>
<div class="math-display">$$y'(g)=r f_g+r'(f+rf_r)=\frac r g\left[g f_g+\left(\frac{rf}{2}+g\right)(f+rf_r)\right]\ge\frac{rf}{g}=\frac yg.$$</div>
<p>It follows that $y(g)/g$ is nondecreasing. Its limit at zero is $r_0H=A$, so $y/g\ge A$. Moreover, since $r'=r(1+y/(2g))$,</p>
<div class="math-display">$$\frac{dy}{dr}=\frac{y'}{r'}\ge\frac{2}{r(1+2g/y)}\ge\frac{2A}{(A+2)r}.$$</div>
<p>If the curve reaches $r_1$, integrate this inequality from $r_0$ to $r_1$, using $y(0)=0$. At its hitting field $g_1\le\gamma$, this yields $r_1M(p_1,g_1)\ge2A\log(r_1/r_0)/(A+2)=r_1B$. Monotonicity in the field gives the same bound at $\gamma$.</p>
<p>If the curve has not reached $r_1$ by field $\gamma>0$, then monotonicity in $p$ and $r(\gamma)\le r_1$ give</p>
<div class="math-display">$$M(p_1,\gamma)\ge f(r(\gamma),\gamma)=\frac{y(\gamma)}{r(\gamma)}\ge\frac{A\gamma}{r_1}.$$</div>
<p>These two alternatives prove the minimum bound. At $\gamma=0$ both sides are zero. The passage from zero field is on a fixed finite graph; no infinite-volume limit or assertion about a critical infinite cluster is used.</p>

## The sharp lower field scale {#section-field}

<p>Take a reference parameter $0<p_c<p=p_c+\varepsilon/m<1$, and write $\rho=mp_c$ and $H=\chi(p_c)$. Define</p>
<div class="math-display">$$g_* =\frac{2\log(1+\varepsilon/\rho)}{\rho H+2},\qquad B_* =\frac{2\rho H}{(\rho+\varepsilon)(\rho H+2)}\log(1+\varepsilon/\rho).$$</div>

<a id="tag-BFAM" data-assertion="corollary" data-title="The leading supercritical field lower bound without a logarithmic error"></a>
<p>If $g_*\le\gamma\le1$, then</p>
<div class="math-display">$$M(p,\gamma)\ge B_*\ge\frac{2\varepsilon}{(\rho+\varepsilon)^2}\frac{\rho H}{\rho H+2}.$$</div>
<p>In particular, consider a sequence with fixed $\lambda>0$, $H=\lambda N^{1/3}$, $\rho\to1$, $\varepsilon\to0$ and $Q=\varepsilon^3N\to\infty$. For every fixed $0<\alpha<1/3$, eventually</p>
<div class="math-display">$$M(p,\varepsilon^2Q^{-\alpha})\ge2\varepsilon\left[1-O\left(\varepsilon+|\rho-1|+H^{-1}\right)\right].$$</div>
<p><em>Proof.</em> Apply the characteristic bound with $p_0=p_c$, $p_1=p$. The elementary inequality $\log(1+x)\ge x/(1+x)$ gives the second bound. For the asymptotic claim,</p>
<div class="math-display">$$g_*\le\frac{2\varepsilon}{\rho(\rho H+2)}=O(\varepsilon/H)=O(\varepsilon^2Q^{-1/3}),\qquad \frac{g_*}{\varepsilon^2Q^{-\alpha}}=O(Q^{\alpha-1/3})\longrightarrow0.$$</div>
<p>The target field therefore lies above $g_*$ and below one eventually. Expanding the explicit positive factors proves the result. In this regime $H^{-1}=\varepsilon/(\lambda Q^{1/3})=O(\varepsilon)$, so it may be absorbed in the first error term. This replaces the earlier logarithmic-error rectangle without changing that earlier statement.</p>

## Transferring the bound to the tail {#section-tail}

<p>For this step assume the finite reference hypotheses used in <a href="/tag/1T2M/">1T2M</a>:</p>
<div class="math-display">$$0<p_c\le\frac12,\qquad H=\lambda N^{1/3}\ge100,\qquad T_{p_c}^3(x,y)\le\mathbf1_{\{x=y\}}+a,\qquad a\le\frac1{100}.$$</div>
<p>Let $0<\varepsilon\le1$, $p=p_c+\varepsilon/m\le1/2$ and $Q=\varepsilon^3N\ge1$. A real cluster cutoff means its ceiling.</p>

<a id="tag-AQPE" data-assertion="theorem" data-title="A polynomial-error lower bound for the supercritical root-cluster tail"></a>
<p>For every real $k\ge\varepsilon^{-2}$,</p>
<div class="math-display">$$\mathbb P_p(|C_o|\ge k)\ge B_*-212\varepsilon k g_*.$$</div>
<p>Consequently, for a sequence with fixed $\lambda$, $\rho\to1$, $\varepsilon\to0$ and $Q\to\infty$, every fixed $0<\alpha<1/3$ satisfies</p>
<div class="math-display">$$\mathbb P_p(|C_o|\ge\varepsilon^{-2}Q^\alpha)\ge2\varepsilon\left[1-O\left(\varepsilon+|\rho-1|+H^{-1}+Q^{\alpha-1/3}\right)\right].$$</div>
<p><em>Proof.</em> The susceptibility bound <a href="/tag/F5Y5/">F5Y5</a> gives $\rho\ge1-H^{-1}\ge99/100$. Thus $0<g_*<1$, since $\log(1+\varepsilon/\rho)\le\varepsilon/\rho$ and $H\ge100$. Marking at this field and splitting according to $|C_o|<k$ gives</p>
<div class="math-display">$$M(p,g_*)\le\mathbb P_p(|C_o|\ge k)+g_*\,\mathbb E_p[|C_o|;\,|C_o|<k].$$</div>
<p>The truncated-field estimate <a href="/tag/E4NT/">E4NT</a> bounds the expectation by $2kM(p,1/k)$. The coarse upper field bound gives $M(p,1/k)\le10k^{-1/2}+96\varepsilon\le106\varepsilon$. For $k\ge2$ this is 1T2M; for $1\le k<2$ it follows from $M\le1$. Since $M(p,g_*)\ge B_*$, the finite assertion follows.</p>
<p>At $k=\varepsilon^{-2}Q^\alpha$, the preceding estimate for $g_*$ gives $kg_*=O(Q^{\alpha-1/3})$. Combine it with the explicit lower bound for $B_*$. The same proof works uniformly for $k=c_N\varepsilon^{-2}Q^\alpha$ when $c_N$ stays in a fixed compact subset of $(0,\infty)$; then $k\ge\varepsilon^{-2}$ eventually.</p>
<p>The proof uses the coarse upper estimate only. It does not depend on the repaired sharp upper-field route or on a pre-existing lower-tail seed.</p>

## A polynomial error on both sides {#section-matching}

<p>Work with a sequence satisfying the preceding reference hypotheses, with fixed $\lambda$, $\rho\to1$, $\varepsilon\to0$ and $Q\to\infty$. In addition, assume $m\to\infty$ and the strong triangle hypothesis of <a href="/tag/6SGU/">6SGU</a>: for fixed $C_0$ and $a_N\to0$,</p>
<div class="math-display">$$\max_{x,y}\{T_u^3(x,y)-\mathbf1_{\{x=y\}}\}\le a_N+C_0\frac{\chi(u)^3}{N}\qquad(0\le u\le p_c).$$</div>

<a id="tag-YHLB" data-assertion="corollary" data-title="Matching supercritical tail bounds with an explicit polynomial error"></a>
<p>Under these hypotheses, for fixed $0<\alpha<1/3$ and $k=c_N\varepsilon^{-2}Q^\alpha$, where $c_N$ is bounded above and away from zero,</p>
<div class="math-display">$$\mathbb P_p(|C_o|\ge k)=2\varepsilon\left[1+O\left(\varepsilon+|\rho-1|+m^{-1}+a_N+Q^{-c_\alpha}\right)\right],\qquad c_\alpha=\min\left\{\frac\alpha2,\frac13-\alpha\right\}.$$</div>
<p>In particular, $\alpha=2/9$ gives $c_\alpha=1/9$.</p>
<p><em>Proof.</em> The lower bound has just been proved, and $H^{-1}=O(\varepsilon)$ here. For the upper bound put $L=\varepsilon^2k=c_NQ^\alpha$ and mark at $\gamma=\varepsilon^2L^{-1/2}$. Then $\gamma k=\sqrt L$, so</p>
<div class="math-display">$$\mathbb P_p(|C_o|\ge k)\le\frac{M(p,\gamma)}{1-e^{-\sqrt L}}\le2\varepsilon\left[1+O\left(\varepsilon+|\rho-1|+m^{-1}+a_N+Q^{-1/4}+L^{-1/2}\right)\right].$$</div>
<p>This is the sharp field bound 6SGU, with $\sqrt\gamma\le\varepsilon$ eventually and $\sqrt{1+2L^{-1/2}}=1+O(L^{-1/2})$. The marking denominator contributes a smaller error. Since $\alpha/2<1/6$, the $Q^{-1/4}$ term is absorbed by $Q^{-\alpha/2}$. Combine the two sides.</p>
<p>If $a_N=K_1/m$ and $C_0=K_2$ with fixed constants and $K_2\lambda^3<1$, the reference expansion <a href="/tag/UF7P/">UF7P</a> gives $|\rho-1|=O(m^{-1}+N^{-1/3})$. Thus the error reduces to $O(\varepsilon+m^{-1}+Q^{-c_\alpha})$, subject to the same small reference-triangle hypothesis.</p>
<p>For example, the hypotheses hold along complete graphs with $\lambda=1/10$ and $\varepsilon=N^{-1/4}$, once $N$ is large enough. Choose $p_c$ by $\chi(p_c)=\lambda N^{1/3}$; existence and uniqueness follow from strict monotonicity of finite susceptibility. The complete-graph identity <a href="/tag/R2Y7/">R2Y7</a> gives the strong triangle bound with $K_1=0,K_2=1$, and UF7P gives $mp_c\to1$. Also $Q=N^{1/4}\to\infty$. This is a written family satisfying the hypotheses, not a compiled witness.</p>

## The repaired appendix argument {#section-source}

<p>The <a href="/errata/hofstad-nachmias-hypercube/#supercritical-field-rectangle">rectangle erratum</a> is now labelled “fix found / substantial”. The replacement starts at a finite graph's actual zero-field susceptibility, follows a smooth characteristic and stops at the target parameter or field. It proves the lower-field and lower-tail estimates with polynomial errors without the invalid rectangle choices. The <a href="/errata/hofstad-nachmias-hypercube/#tail-field-ratio-sign">field-ratio sign correction</a> remains local.</p>
<p>The paper writes $p=p_c(1+e)$, whereas here $\varepsilon=m(p-p_c)=\rho e$. Its cutoff becomes $\rho^{2-3\alpha}\varepsilon^{-2}Q^\alpha$. This factor tends to one and is covered by the uniform cutoff statement above; converting the leading $2\varepsilon$ to $2e$ costs $O(|\rho-1|)$, already retained. These formulas keep the reference-parameter approximation explicit.</p>
<p>The earlier logarithmic-error results and all their tags remain valid. The new argument strengthens their conclusions; it does not prove uniqueness or the size of a giant component, establish the infinite-graph remark, or recover every stronger upper-field error claimed in the source. All source corrections remain provisional. The <a href="/coverage/sources/characteristic-field-growth/">reading map</a> records the checked passages and the new proof. No new formal verification is claimed.</p>
