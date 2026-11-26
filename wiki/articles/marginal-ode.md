---
{
  "id": "marginal-ode",
  "title": "A marginal ODE and its logarithmic correction",
  "subtitle": "An integrating-factor argument with an explicit error condition",
  "kind": "method",
  "category": "Methods",
  "summary": "A nonlinear correction to power-law growth produces a logarithmic factor. An integrable multiplicative error preserves the leading constant, while an error of order 1/log r can introduce another logarithm.",
  "context": ["The marginal equation $g'(r)=\\frac ar[1-(C+\\varepsilon(r))(r^{-a}g(r))^\\gamma+\\delta(r)]g(r)$ has positive constants $a,\\gamma,C$ and a positive continuously differentiable solution $g$ on $[r_0,\\infty)$, with $r_0>1$.", "In the marginal equation the perturbations $\\varepsilon,\\delta$ are continuous and the error $\\varepsilon$ in the nonlinear coefficient tends to zero.", "This is an analytic statement. Applying it to percolation requires a separately justified differential equation."],
  "related": ["cutoff-families", "susceptibility", "triangle-condition"],
  "sourceIds": ["hutchcroft-book", "hutchcroft-lrp-1", "perclib-riccati-comparison", "perclib-logarithmic-corrections", "perclib-double-factorial-convolution", "perclib-shared-elementary", "perclib-moment-hierarchy"],
  "aliases": ["marginal ODE", "logarithmic correction", "integrating factor", "Bernoulli equation", "critical dimension"],
  "prototypeUses": []
}
---

## A signed linear equation with regularly varying forcing {#section-signed-forcing}

<p>The first two sections treat the linear equation $rf'=af+Ah$ with a regularly varying forcing term $h$ whose index $b$ exceeds $a$. There the forcing dominates, $f/h$ converges, and no logarithm appears. The <a href="/tag/09N5/">marginal equation</a> of the later sections has no such index gap, and a logarithmic factor appears.</p>
<a id="tag-2KB9" data-assertion="theorem" data-title="Regularly varying forcing determines a signed linear asymptotic"></a>
<p>Let $a,b,A\in\mathbb R$ with $b&gt;a$. Let $h$ be a positive measurable, locally integrable function on $[r_0,\infty)$, regularly varying with index $b$. Suppose $f$ is locally absolutely continuous and, almost everywhere,</p>
<div class="math-display">$$rf'(r)=(a+\varepsilon(r))f(r)+(A+\delta(r))h(r),$$</div>
<p>where $\varepsilon,\delta$ are locally bounded measurable functions tending to zero. Then</p>
<div class="math-display">$$\frac{f(r)}{h(r)}\longrightarrow\frac{A}{b-a}.$$</div>
<p>No sign condition on $f$ or $A$, and no prior bound $|f|=O(h)$, is needed.</p>
<p><em>Proof.</em> Define $H(r)=\exp\{\int_{r_0}^r(a+\varepsilon(t))\,dt/t\}$. For each fixed $\lambda&gt;0$, the integral of $\varepsilon(t)/t$ between $r$ and $\lambda r$ tends to zero, so $H$ is regularly varying with index $a$. Variation of constants gives</p>
<div class="math-display">$$f(r)=H(r)\left[f(r_0)+\int_{r_0}^r\frac{(A+\delta(t))h(t)}{tH(t)}\,dt\right].$$</div>
<p>Put $q=h/H$. Its index is $b-a&gt;0$, and hence</p>
<div class="math-display">$$\int_{r_0}^r\frac{q(t)}t\,dt\sim\frac{q(r)}{b-a}.$$</div>
<p>One may see this directly by setting $t=ru$: on compact subintervals of $(0,1]$ the normalized integrand tends to $u^{b-a-1}$. A regular-variation bound by $Cu^{b-a-1-\eta}$, with $0&lt;\eta&lt;b-a$, controls the part where $ru$ is large; the remaining fixed initial interval contributes $o(q(r))$. Integration gives the displayed equivalent.</p>
<p>The integral containing $\delta$ is $o(q(r))$: after a fixed large threshold its absolute value is bounded by $\sup_{t\geq T}|\delta(t)|$ times the positive integral just estimated, and the initial interval is negligible. Also $H(r)/h(r)=1/q(r)\to0$. Divide the variation-of-constants formula by $h(r)$ to obtain the claim, including when $A=0$.</p>
<p>This gives the signed ODE step used for spatial monomials in T. Hutchcroft, <a href="https://arxiv.org/abs/2508.18807v1"><em>Critical long-range percolation I: High effective dimension</em></a> (2025), Lemma I.5.26, with local absolute continuity sufficient. It does not differentiate a slowly varying normalization, and it does not require the error multiplying $f$ to be integrable: the positive index gap $b-a$ makes the forcing dominant.</p>

## An asymptotic equation with a dominant driving term {#section-driving-term}

<p>The following form of the <a href="/tag/2KB9/">signed linear theorem</a> has the asymptotic relation $f'\sim(af+h)/r$ as its hypothesis in place of an exact equation with vanishing errors, and requires no integrability or absolute continuity.</p>
<a id="tag-B5SL" data-assertion="theorem" data-title="An asymptotic linear equation with dominant regularly varying driving term"></a>
<p>Let $a&gt;0$, and let $h:(0,\infty)\to(0,\infty)$ be a measurable function, <a href="/tag/3491/">regularly varying</a> with index $b&gt;0$. Suppose that $f:(0,\infty)\to\mathbb R$ is differentiable and</p>
<div class="math-display">$$f'(r)\sim\frac{af(r)+h(r)}{r}\qquad(r\to\infty),$$</div>
<p>that is, the ratio of the left side to the right side tends to $1$. If $b&gt;a$, then</p>
<div class="math-display">$$f(r)\sim\frac{h(r)}{b-a}\qquad(r\to\infty).$$</div>
<p>In particular, $f$ is eventually positive and its restriction to some half-line $[r_2,\infty)$ is <a href="/tag/3491/">regularly varying</a> with index $b$.</p>
<p>This is Lemma I.4.21 of Hutchcroft's <a href="https://arxiv.org/abs/2508.18807v1"><em>Critical long-range percolation I</em></a> (2025), where the term $h$ is called the driving term. Hutchcroft applies it to the <a href="/tag/K3DB/">higher moments of cutoff cluster volumes</a>, whose driving terms have a larger index than their linear terms.</p>
<p><em>Idea of the proof.</em> Write the asymptotic relation as an exact equation $rf'=(1-\theta)(af+h)$ with a relative error $\theta(r)\to0$. This is the equation of the signed linear theorem with both errors proportional to $\theta$, once one checks the hypotheses that theorem needs: $h$ is locally integrable, by the uniform convergence theorem for regularly varying functions, and $f$ is locally absolutely continuous, since $f'$ is locally bounded. The index gap $b-a&gt;0$ then makes the driving term determine the limit of $f/h$, and regular variation of $f$ is inherited from $h$.</p>
:::details Proof
<p><em>Step 1 (an exact equation).</em> By hypothesis the ratio $\rho(r)=rf'(r)/(af(r)+h(r))$ is defined for all large $r$ and tends to $1$. Choose $r_1&gt;0$ such that $af(r)+h(r)\neq0$ and $|\rho(r)-1|\leq\tfrac12$ for every $r\geq r_1$, and put $\theta(r)=1-\rho(r)$ there. Then, for every $r\geq r_1$,</p>
<div class="math-display">$$rf'(r)=(1-\theta(r))\bigl(af(r)+h(r)\bigr)=\bigl(a+\varepsilon(r)\bigr)f(r)+\bigl(1+\delta(r)\bigr)h(r),\qquad\varepsilon=-a\theta,\quad\delta=-\theta.$$</div>
<p>The function $f$ is differentiable, hence continuous, and $f'$ is the pointwise limit of the continuous functions $r\mapsto n\bigl(f(r+1/n)-f(r)\bigr)$, hence measurable. As $h$ is measurable, $\theta$ is measurable on $[r_1,\infty)$. It satisfies $|\theta|\leq\tfrac12$ and $\theta(r)\to0$, so $\varepsilon$ and $\delta$ are bounded measurable functions tending to zero.</p>
<p><em>Step 2 (local boundedness of $h$).</em> By the uniform convergence theorem for measurable regularly varying functions (Bingham, Goldie and Teugels, Regular Variation, Theorem 1.5.2), $h(\lambda x)/h(x)\to\lambda^b$ uniformly in $\lambda\in[1,2]$ as $x\to\infty$. Choose $X&gt;0$ such that $h(\lambda x)\leq(2^b+1)h(x)$ for all $x\geq X$ and $\lambda\in[1,2]$. Then $h\leq(2^b+1)h(2^kX)$ on $[2^kX,2^{k+1}X]$ for every integer $k\geq0$, so $h$ is bounded on every compact subinterval of $[X,\infty)$. Being measurable, it is integrable on each such interval.</p>
<p><em>Step 3 (absolute continuity of $f$).</em> Put $r_0=\max(r_1,X,1)$ and fix $R&gt;r_0$. On $[r_0,R]$ the continuous function $f$ is bounded, $h$ is bounded by Step 2, and $r\geq1$, so by Step 1</p>
<div class="math-display">$$|f'(r)|\leq\tfrac32\bigl(a|f(r)|+h(r)\bigr)\leq M_R\qquad(r_0\leq r\leq R)$$</div>
<p>for a constant $M_R$. By the mean value theorem, $|f(s)-f(t)|\leq M_R|s-t|$ for $s,t\in[r_0,R]$. Thus $f$ is Lipschitz, hence absolutely continuous, on every compact subinterval of $[r_0,\infty)$, and the equation of Step 1 holds at every point of $[r_0,\infty)$.</p>
<p><em>Step 4 (the limit).</em> On $[r_0,\infty)$ all hypotheses of the <a href="/tag/2KB9/">signed linear theorem</a> hold with the given $a$ and $b$, the constant $A=1$ and the errors $\varepsilon,\delta$ of Step 1: $b&gt;a$; $h$ is positive, measurable, locally integrable (Step 2) and regularly varying with index $b$; $f$ is locally absolutely continuous (Step 3); $\varepsilon$ and $\delta$ are locally bounded, measurable and tend to zero. That theorem gives $f(r)/h(r)\to1/(b-a)$, which is the claim.</p>
<p><em>Step 5 (regular variation).</em> Since $h&gt;0$ and $f/h$ tends to the positive limit $1/(b-a)$, there is $r_2\geq r_0$ with $f(r)&gt;0$ for all $r\geq r_2$. On $[r_2,\infty)$ the function $f$ is positive and continuous, hence measurable. Fix $\lambda&gt;0$. As $r\to\infty$ also $\lambda r\to\infty$, so</p>
<div class="math-display">$$\frac{f(\lambda r)}{f(r)}=\frac{f(\lambda r)}{h(\lambda r)}\cdot\frac{h(\lambda r)}{h(r)}\cdot\frac{h(r)}{f(r)}\longrightarrow\frac1{b-a}\cdot\lambda^b\cdot(b-a)=\lambda^b.$$</div>
<p>Hence $f$, restricted to $[r_2,\infty)$, is regularly varying with index $b$.</p>
:::

## The asymptotic {#section-asymptotic}

<a id="tag-09N5" data-assertion="theorem" data-title="Marginal ODE asymptotic with integrable multiplicative error"></a><p>Let $a,\gamma,C&gt;0$, $r_0&gt;1$, and let $g:[r_0,\infty)\to(0,\infty)$ be continuously differentiable. Suppose continuous functions $\varepsilon,\delta$ satisfy $\varepsilon(r)\to0$ and</p><div class="math-display">$$\int_{r_0}^\infty\frac{|\delta(r)|}{r}\,dr&lt;\infty,$$</div><p>and that</p><div class="math-display">$$g'(r)=\frac ar\left[1-(C+\varepsilon(r))(r^{-a}g(r))^\gamma+\delta(r)\right]g(r).$$</div><p>Then</p><div class="math-display">$$g(r)\sim r^a(a\gamma C\log r)^{-1/\gamma}\qquad(r\to\infty).$$</div><p><em>Proof.</em> Put $t=\log r$, $t_0=\log r_0$, and $u(t)=e^{-at}g(e^t)$. Removing the leading power gives</p><div class="math-display">$$\frac{u'(t)}{u(t)}=-a(C+\varepsilon(e^t))u(t)^\gamma+a\delta(e^t).$$</div><p>Since $u&gt;0$, set $w=u^{-\gamma}$. The equation becomes linear:</p><div class="math-display">$$w'(t)+a\gamma\delta(e^t)w(t)=a\gamma(C+\varepsilon(e^t)).$$</div><p>Its integrating factor</p><div class="math-display">$$H(t)=\exp\!\left(a\gamma\int_{t_0}^t\delta(e^s)\,ds\right)$$</div><p>has a finite positive limit $H_\infty$, by the absolute integrability assumption. Consequently</p><div class="math-display">$$w(t)=\frac{w(t_0)+a\gamma\int_{t_0}^tH(s)(C+\varepsilon(e^s))\,ds}{H(t)}.$$</div><p>The integrand tends to $H_\infty C$, so its average over $[t_0,t]$ tends to the same limit. Dividing by $t$ gives $w(t)/t\to a\gamma C$. Taking the negative $1/\gamma$ power and returning to $r=e^t$ proves the assertion.</p><p>The positive limit of the integrating factor cancels from the leading coefficient. No rate of convergence or integrability is required of $\varepsilon$: it appears as a vanishing error in the forcing term of the linear equation. The error $\delta$ multiplies $w$, so it is controlled differently.</p>

## Cancellation in the moment ratio {#section-ratio}

<a id="tag-OP8F" data-assertion="theorem" data-title="A marginal deficit gap determines the logarithmic second moment"></a>
<p>Let $\alpha,a_0,c,\nu,K&gt;0$. Let $m,f$ be positive locally absolutely continuous functions on $[r_0,\infty)$, with $r_0&gt;1$, and let $a,b$ be positive measurable functions. Suppose</p>
<div class="math-display">$$m(r)\sim cr^\alpha,\qquad a(r)\sim a_0r^{-\alpha-1},\qquad b(r)\sim\nu r^{3\alpha}.$$</div>
<p>Suppose measurable functions $e_1,e_2\in[0,1]$ satisfy, almost everywhere,</p>
<div class="math-display">$$m'=am^2(1-e_1),\qquad f'=3amf(1-e_2),$$</div>
<p>and that $e_2-e_1=(K+\varepsilon(r))f^2/(bm^3)$ almost everywhere, where $\varepsilon(r)\to0$. Then</p>
<div class="math-display">$$\frac{f(r)}{m(r)^3}\sim\left(\frac{6Ka_0c^4}{\nu}\log r\right)^{-1/2},\qquad f(r)\sim c\sqrt{\frac{\nu}{6Ka_0}}\,\frac{r^{3\alpha}}{\sqrt{\log r}}.$$</div>
<p><em>Proof.</em> Put $v=f/m^3$. The two exact equations give</p>
<div class="math-display">$$(\log v)'=3am(e_1-e_2).$$</div>
<p>Thus $w=v^{-2}$ is locally absolutely continuous and satisfies</p>
<div class="math-display">$$w'=6am(e_2-e_1)v^{-2}=6(K+\varepsilon)\frac{am^4}{b}\sim\frac{6Ka_0c^4}{\nu r}\quad\text{a.e.}$$</div>
<p>Integrate after bounding the last coefficient above and below by $1\pm\eta$ times its limit, beyond a radius depending on $\eta$. This gives $w(r)/\log r\to6Ka_0c^4/\nu$. Take the inverse square root and substitute $m(r)\sim cr^\alpha$.</p>
<p>The common first-moment contribution cancels before any asymptotic expansion. In particular, the theorem needs neither a second-order equivalent for $m/(cr^\alpha)-1$ nor an integrability bound on that error. It does require the asymptotic <em>difference</em> of the deficits; an upper bound on each deficit is insufficient.</p>
<p>The analytic assumptions have an explicit witness when $a_0=\alpha/c$. Take $m=cr^\alpha$, $a=(\alpha/c)r^{-\alpha-1}$, $b=\nu r^{3\alpha}$, and</p>
<div class="math-display">$$v(r)=\left[D+\frac{6K\alpha c^3}{\nu}\log\frac r{r_0}\right]^{-1/2},\qquad f=m^3v,\qquad e_1=0,\qquad e_2=\frac{Kc^3}{\nu}v^2,$$</div>
<p>where $D\geq Kc^3/\nu$. Then $0\leq e_2\leq1$ and both equations hold. This is a witness for the scalar system, not a percolation realization.</p>
<p>For example, if $e_1\sim I_3R$ and $e_2\sim(I_3+2I_4)R$ with $I_3,I_4&gt;0$ and $R=f^2/(bm^3)$, then their difference has $K=2I_4$. The common $I_3$ term cancels. When $a_0c=\alpha$, the second-moment coefficient is $\sqrt{\nu c^3/(12\alpha I_4)}$. The spatial estimates producing $I_3,I_4$ remain inputs; the result proves their analytic consequence only.</p>

## The power-log cutoff scale and the full tail {#section-tail}

<a id="tag-QKHV" data-assertion="corollary" data-title="Power-log cutoff scales give the normalized full volume tail"></a>
<p>Suppose the hypotheses of the <a href="/tag/9PSJ/">cutoff-to-full asymptotic transfer theorem</a> hold with $a=2$, size-biased limit the square of a standard normal variable, and scale</p>
<div class="math-display">$$s(r)=r^{2\alpha}(\log r)^{-\sigma},\qquad \alpha&gt;0,\quad\sigma\in\mathbb R,$$</div>
<p>restricted to a sufficiently large interval where it is strictly increasing. In particular, the cutoff mean and second-to-first moment ratio satisfy $m_r\sim A_1r^\alpha$ and $b_r\sim A_2s(r)$, with $A_1,A_2&gt;0$, and the multiplicative ghost comparison in that theorem is assumed. Then</p>
<div class="math-display">$$\mathbb P(T&gt;t)\sim A_1\sqrt{\frac{2}{\pi A_2}}(2\alpha)^{-\sigma/2}t^{-1/2}(\log t)^{\sigma/2}.$$</div>
<p>For integer-valued $T$, the same equivalent holds with $\mathbb P(T\geq n)$.</p>
<p><em>Proof.</em> Let $F=s^{-1}$. The equation $t=s(r)$ gives</p>
<div class="math-display">$$\log t=2\alpha\log r-\sigma\log\log r\sim2\alpha\log r,\qquad F(t)^\alpha=t^{1/2}(\log F(t))^{\sigma/2}.$$</div>
<p>Consequently $F(t)^\alpha\sim(2\alpha)^{-\sigma/2}t^{1/2}(\log t)^{\sigma/2}$. Substitute this into the transfer theorem, using its coefficient $c_*=A_1\sqrt{2/A_2}$ and $\Gamma(1/2)=\sqrt\pi$.</p>
<p>The choice $\sigma=0$ gives the high-dimensional constant when $A_1=\alpha/\beta_c$ and $A_2=A$. The choice $\sigma=1/2$ gives the marginal factor $(\log t)^{1/4}$. In the latter case the second-moment coefficient from the preceding theorem, divided by the first-moment coefficient, determines $A_2$; the factor $(2\alpha)^{-1/4}$ comes from inverting the scale and cannot be dropped. The <a href="/tag/0N85/">squared-normal moment criterion</a> supplies the required size-biased convergence when the full double-factorial moment asymptotics are available. A first and second moment equivalent alone does not supply that convergence.</p>

## Higher moments from the closed hierarchy {#section-higher-moments}

<a id="tag-5O1G" data-assertion="theorem" data-title="Double-factorial moment asymptotics from a closed power-law hierarchy"></a>
<p>Fix an integer $P\geq3$ and constants $r_0,\alpha,B,C&gt;0$. Let $m_1,\ldots,m_P$ be positive locally absolutely continuous functions on $[r_0,\infty)$, let $a$ be positive and measurable, and suppose</p>
<div class="math-display">$$m_1(r)\sim Br^\alpha,\qquad m_2(r)\sim Cr^{3\alpha},\qquad a(r)\sim\frac\alpha B r^{-\alpha-1}.$$</div>
<p>For each $3\leq p\leq P$, assume a measurable error $\varepsilon_p(r)\to0$ such that, almost everywhere,</p>
<div class="math-display">$$m_p'(r)=(1+\varepsilon_p(r))a(r)\sum_{\ell=0}^{p-1}\binom p\ell m_{\ell+1}(r)m_{p-\ell}(r).$$</div>
<p>Then, for $1\leq p\leq P$, with $(-1)!!=1$,</p>
<div class="math-display">$$m_p(r)\sim(2p-3)!!\,\left(\frac{m_2(r)}{m_1(r)}\right)^{p-1}m_1(r).$$</div>
<p>No integrability or rate of decay of the errors is required. The first two equivalents, including the finite positive second-moment amplitude $C$, are hypotheses.</p>
<p><em>Proof.</em> Put $D_p=C^{p-1}B^{2-p}$ and $A_1=A_2=1$. Suppose inductively that $m_j(r)\sim A_jD_jr^{(2j-1)\alpha}$ for $j&lt;p$. The terms containing $m_p$ have total coefficient $(p+1)(1+\varepsilon_p)a m_1$. The remaining terms use only lower moments. Since $D_jD_{p+1-j}=BD_p$, the equation becomes</p>
<div class="math-display">$$m_p'=\frac{q(r)}r m_p+D_p r^{(2p-1)\alpha-1}h(r),\qquad q(r)\longrightarrow(p+1)\alpha,\quad h(r)\longrightarrow\alpha S_p,$$</div>
<p>where</p>
<div class="math-display">$$S_p=\sum_{j=2}^{p-1}\binom p{j-1}A_jA_{p+1-j}=\sum_{j=2}^{p-1}\binom pj A_jA_{p+1-j}.$$</div>
<p>The second equality reindexes $j$ as $p+1-j$. Set $t=\log r$ and $y(t)=m_p(e^t)/(D_pe^{(2p-1)\alpha t})$. Then</p>
<div class="math-display">$$y'=-\bigl((p-2)\alpha+o(1)\bigr)y+\alpha S_p+o(1)\quad\text{a.e.}$$</div>
<p>The positive gap $g=(p-2)\alpha$ forces $y\to S_p/(p-2)$. Indeed, for each sufficiently small $\eta&gt;0$ and all sufficiently large $t$, positivity of $y$ bounds its derivative between $-(g+\eta)y+\alpha S_p-\eta$ and $-(g-\eta)y+\alpha S_p+\eta$. Multiplying these two differential inequalities by their exponential integrating factors gives</p>
<div class="math-display">$$\frac{\alpha S_p-\eta}{g+\eta}\leq\liminf y\leq\limsup y\leq\frac{\alpha S_p+\eta}{g-\eta}.$$</div>
<p>Let $\eta\downarrow0$. Thus $A_p=S_p/(p-2)$, independently of the initial value of $m_p$.</p>
<p>To solve this recurrence, let $b_n=(2n-3)!!$ for $n\geq1$. Its exponential generating series is $F(z)=\sum_{n\geq1}b_nz^n/n!=1-\sqrt{1-2z}$. The identity $FF'=F'-1$ gives</p>
<div class="math-display">$$\sum_{j=1}^p\binom pj b_jb_{p+1-j}=b_{p+1}=(2p-1)b_p.$$</div>
<p>Removing the terms $j=1,p$ leaves $(p-2)b_p$. Hence the $b_p$ obey the same recurrence and initial values as the $A_p$, completing the induction. Finally $D_pr^{(2p-1)\alpha}\sim(m_2/m_1)^{p-1}m_1$.</p>
<p>This proves the coefficient calculation in the higher-moment induction. If the hypotheses hold at every fixed order for actual moments of nonnegative random variables, <a href="/tag/0N85/">0N85</a> gives the squared-normal limit under volume bias. A finite number of moment equivalents does not give that conclusion. The <a href="/tag/XXTP/">collision estimate</a> is one route to the required closed equations, but its moment assumptions must be proved independently. The case $p=2$ has zero gap, which is why this argument cannot supply its amplitude or replace the separate marginal analysis.</p>

## Propagating a slowly varying second-moment factor {#section-slow-moments}

<a id="tag-OBTO" data-assertion="theorem" data-title="A slowly varying second-moment factor propagates through the hierarchy"></a>
<p>Retain the hypotheses of <a href="/tag/5O1G/">5O1G</a>, except replace its second-moment equivalent by</p>
<div class="math-display">$$m_2(r)\sim Cr^{3\alpha}L(r),$$</div>
<p>where $L$ is positive and continuously differentiable for sufficiently large $r$, and $rL'(r)/L(r)\to0$. Then, for every $1\leq p\leq P$,</p>
<div class="math-display">$$m_p(r)\sim(2p-3)!!\,C^{p-1}B^{2-p}r^{(2p-1)\alpha}L(r)^{p-1}\sim(2p-3)!!\left(\frac{m_2(r)}{m_1(r)}\right)^{p-1}m_1(r).$$</div>
<p>In particular, $L(r)=(\log r)^{-\sigma}$ is admissible for every real $\sigma$. The marginal value $\sigma=1/2$ gives the factor $(\log r)^{-(p-1)/2}$ in the $p$th moment.</p>
<p><em>Proof.</em> The first two cases are the assumed equivalents. At step $p\geq3$, the products in the lower-moment forcing contain the common factor $L^{p-1}$: their exponents are $(j-1)+(p-j)=p-1$. Thus, with $D_p=C^{p-1}B^{2-p}$ and $S_p$ as in the preceding proof,</p>
<div class="math-display">$$m_p'=\frac{q(r)}r m_p+D_pr^{(2p-1)\alpha-1}L(r)^{p-1}h(r),\qquad q(r)\to(p+1)\alpha,\quad h(r)\to\alpha S_p.$$</div>
<p>Normalize by setting $t=\log r$ and $y(t)=m_p(e^t)/[D_pe^{(2p-1)\alpha t}L(e^t)^{p-1}]$. Its equation is</p>
<div class="math-display">$$y'=\left[q(e^t)-(2p-1)\alpha-(p-1)\frac{e^tL'(e^t)}{L(e^t)}\right]y+h(e^t).$$</div>
<p>The coefficient tends to $-(p-2)\alpha&lt;0$. The two integrating-factor comparisons in the proof of 5O1G therefore give the same limit $A_p=S_p/(p-2)$ and the same double-factorial recurrence. This completes the induction.</p>
<p>The regularity condition implies that $L$ is slowly varying: for each fixed $c&gt;0$, integrate $L'/L=o(1/r)$ between $r$ and $cr$ to obtain $\log[L(cr)/L(r)]\to0$. Slow variation alone does not imply the derivative condition used here. For example, $L(r)=1+r^{-1}\sin(r^2)$ is positive for $r&gt;1$ and tends to one, but $rL'(r)/L(r)$ does not tend to zero. The theorem asserts a sufficient condition, not a characterization of slowly varying factors.</p>
<p>This gives the analytic propagation after the marginal second-moment calculation. If the closed equations and moment hypotheses hold at every fixed order for cluster volumes, <a href="/tag/0N85/">0N85</a> identifies the volume-biased limit after normalization by $m_2/m_1$. For $\sigma=1/2$ its scale is $(C/B)r^{2\alpha}/\sqrt{\log r}$. Passing to the full-cluster tail still requires the omitted-edge comparison in <a href="/tag/9PSJ/">9PSJ</a>; the resulting inversion constant is recorded in <a href="/tag/QKHV/">QKHV</a>.</p>

## An exact solution {#section-exact}

<a id="tag-SR9U" data-assertion="proposition" data-title="Exact unperturbed marginal ODE solution"></a><p>For $\varepsilon=\delta=0$ and initial value $g(r_0)=g_0&gt;0$, the unique positive solution on $[r_0,\infty)$ is</p><div class="math-display">$$g(r)=r^a\left[r_0^{a\gamma}g_0^{-\gamma}+a\gamma C\log\frac r{r_0}\right]^{-1/\gamma}.$$</div><p><em>Proof.</em> The transformed equation is $w'=a\gamma C$, with $w(t_0)=r_0^{a\gamma}g_0^{-\gamma}$. Integrating gives the formula. The bracket stays positive for $r\geq r_0$, so the solution exists on the entire stated interval. The invertible transformation and uniqueness of this linear equation also give uniqueness among positive solutions.</p><p>This formula shows directly that the initial condition affects only a lower-order additive constant in $w$. In particular, setting $\gamma=2$ gives the factor $(\log r)^{-1/2}$. Identifying $a$, $C$, or $g$ with a percolation quantity is an additional step.</p>

## A vanishing error that changes the answer {#section-error}

<a id="tag-63GS" data-assertion="proposition" data-title="A nonintegrable error produces a second logarithmic factor"></a><p>Keep $a,\gamma,C&gt;0$ and $r_0&gt;1$, set $\varepsilon=0$, and take</p><div class="math-display">$$\delta(r)=-\frac1{a\gamma\log r}.$$</div><p>For every positive initial value, the corresponding positive solution satisfies</p><div class="math-display">$$g(r)\sim r^a\bigl(a\gamma C\log r\,\log\log r\bigr)^{-1/\gamma}.$$</div><p><em>Proof.</em> With $t=\log r$ and $w=(r^{-a}g)^{-\gamma}$, the equation is $w'-w/t=a\gamma C$. Thus</p><div class="math-display">$$w(t)=t\left[\frac{w(t_0)}{t_0}+a\gamma C\log\frac t{t_0}\right].$$</div><p>The bracket is positive for $t\geq t_0&gt;0$, and $w(t)\sim a\gamma C\,t\log t$. Transforming back proves the asymptotic.</p><p>Here $\delta(r)\to0$, but $\int_{r_0}^\infty|\delta(r)|\,dr/r=\infty$. Thus merely replacing the integrability hypothesis by $\delta=o(1)$ would make the first theorem false. The example does not say that absolute integrability is necessary for every individual solution to have the first asymptotic; it shows why some additional control is needed.</p>

<p>The first result above is the marginal ODE lemma, with regularity made explicit. Obtaining a cutoff logarithm from it requires a separately derived moment equation. That application must supply the constants, the differential equation and its error bounds. Passing from a cutoff moment asymptotic to a full cluster-volume tail requires still further comparison and Tauberian input; the ODE by itself establishes none of those probabilistic steps.</p>


## Reciprocal comparison on a terminal interval {#section-riccati}

<a id="tag-DUWG" data-assertion="proposition" data-title="Riccati comparisons without a continuous derivative"></a>
<p>Let $A,\alpha,r_0&gt;0$, and let $f$ be positive and differentiable on $[r_0,\infty)$. If</p>
<div class="math-display">$$f'(r)\geq Ar^{-\alpha-1}f(r)^2\qquad(r\geq r_0),$$</div>
<p>then $f(r)\leq(\alpha/A)r^\alpha$ throughout that interval. If instead the differential inequality is reversed and $f(r)\to\infty$, then $f(r)\geq(\alpha/A)r^\alpha$. Neither implication assumes that $f'$ is continuous.</p>
<p><em>Proof.</em> Put $H(r)=f(r)^{-1}-(A/\alpha)r^{-\alpha}$. In the first case $H'\leq0$, so for $R\geq r$ one has $H(r)\geq H(R)\geq-(A/\alpha)R^{-\alpha}$. Letting $R\to\infty$ gives $H(r)\geq0$. In the second case $H'\geq0$ and $H(R)\to0$, so $H(r)\leq0$. Taking reciprocals gives both claims.</p>
<p>Positivity on the whole terminal interval is essential to the first argument. The second also uses divergence: a positive constant function satisfies its differential inequality but not the claimed growing lower bound.</p>

## The exact reciprocal remainder {#section-riccati-remainder}

<a id="tag-K58A" data-assertion="proposition" data-title="Exact tail remainder for a perturbed Riccati equation"></a>
<p>Under the same positivity and differentiability assumptions, suppose $h$ is measurable and bounded on $[r_0,\infty)$ and</p>
<div class="math-display">$$f'(r)=A(1-h(r))r^{-\alpha-1}f(r)^2.$$</div>
<p>For $r_0\leq r\leq R$,</p>
<div class="math-display">$$\frac1{f(r)}=\frac1{f(R)}+\frac A\alpha(r^{-\alpha}-R^{-\alpha})-A\int_r^R h(s)s^{-\alpha-1}\,ds.$$</div>
<p>If also $f(R)\to\infty$, then</p>
<div class="math-display">$$f(r)=\frac{(\alpha/A)r^\alpha}{1-\alpha r^\alpha\int_r^\infty h(s)s^{-\alpha-1}\,ds},$$</div>
<p>and the denominator is strictly positive. If in addition $h(r)\to0$, this gives $f(r)\sim(\alpha/A)r^\alpha$.</p>
<p><em>Proof.</em> The reciprocal has derivative $-A(1-h(r))r^{-\alpha-1}$, bounded on each compact subinterval. It is therefore Lipschitz there, so the fundamental theorem gives the finite identity. Boundedness of $h$ and $\alpha&gt;0$ make the improper remainder absolutely integrable. Let $R\to\infty$ and rearrange. The denominator equals $(\alpha/A)r^\alpha/f(r)&gt;0$. Finally,</p>
<div class="math-display">$$\left|\alpha r^\alpha\int_r^\infty h(s)s^{-\alpha-1}\,ds\right|\leq\sup_{s\geq r}|h(s)|,$$</div>
<p>which tends to zero under the extra hypothesis.</p>
<p>The <a href="/coverage/sources/perclib-3978a2f-odes/">six-result source inventory</a> records the comparisons and exact remainder at merged main. The asymptotic with vanishing $h$ above is a consequence of that formula. The source retains attribution to the contributor's pinned Riccati port; its inspection is separate from compiled tag association.</p>


## What the deficit cancellation uses {#section-deficit-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-scales/">source proof of OP8F</a> retains the exact difference $e_2-e_1$ before taking limits. It does not require the separate deficits to lie in $[0,1]$ or to tend to zero, and it allows any real $\alpha$. Those extra restrictions in the article describe the intended moment application; the analytic cancellation only needs the displayed identities, the coefficient equivalents and positivity of $m,f,b$.</p>
<p>After setting $w=m^6/f^2$, absolute continuity justifies integrating the almost-everywhere identity for $w'$. The asymptotic inputs make $rw'(r)$ approach $L=6Ka_0c^4/\nu$ in the following precise sense: for every $\eta&gt;0$, beyond one radius, $|rw'(r)-L|\leq\eta$ almost everywhere. Integration between that radius and $R$, followed by division by $\log R$, gives $w(R)/\log R\to L$. This does not replace the needed deficit difference by separate upper bounds on its two terms.</p>


## The factorial convolution by Pascal's rule {#section-factorial-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-moments/">factorial source</a> gives an algebraic proof of the convolution used in <a href="/tag/5O1G/">5O1G</a>. Put $d_0=1$, $d_{n+1}=(2n+1)d_n$, and $S_n=\sum_{k=0}^{n-1}\binom nk d_kd_{n-1-k}$. Pascal's rule, followed by the recurrence for $d$, gives</p>
<div class="math-display">$$S_{n+1}=\sum_{k=0}^{n-1}\binom nk\bigl(d_kd_{n-k}+d_{k+1}d_{n-1-k}\bigr)+d_n=2nS_n+d_n.$$</div>
<p>Since $S_1=d_1=1$, induction yields $S_n=d_n$ for $n\geq1$. Specializing to $d_n=(2n-1)!!$, with $d_0=(-1)!!=1$, gives Lemma I.4.23. The source represents the negative endpoint index using truncated natural subtraction, hence $0!!=1$; no negative-index factorial is evaluated. At $n=0$ the convolution is empty and is not equal to $d_0$.</p>
<p>To compare with the earlier notation $b_j=(2j-3)!!$, write $d_k=b_{k+1}$ and reindex $j=k+1$. The resulting binomial coefficient is $\binom n{j-1}$; replacing $j$ by $n+1-j$ gives the displayed $\binom nj$ convolution in 5O1G. This coefficient identity alone does not prove the moment equivalents or their differential equations.</p>


## Absolute continuity in the hierarchy argument {#section-hierarchy-source}

<p>The <a href="/coverage/sources/perclib-f51f639-moments/">hierarchy source</a> now supplies the analytic implications of <a href="/tag/5O1G/">5O1G</a> and <a href="/tag/OBTO/">OBTO</a>. Its linear comparison assumes that $S$ is nonnegative and absolutely continuous on each compact interval, with $S'=uS+g$ almost everywhere. If $ru(r)\to q$, $g(r)/r^{\beta-1}\to c$ and $q&lt;\beta$, then $S(r)/r^\beta\to c/(\beta-q)$. Comparing with the factors $r^{-(q\pm\eta)}$ gives both bounds without a convergence rate for either error.</p>
<p>At order $p\geq3$, the hierarchy's two end terms give coefficient $(p+1)\alpha/r$, while the expected moment exponent is $(2p-1)\alpha$. Their gap $(p-2)\alpha&gt;0$ is what makes the lower-order forcing determine the leading constant. The finite convolution gives the double factorial, and induction reaches every order up to the specified $P$. The slowly varying extension assumes a positive factor $L$ that is eventually continuously differentiable and satisfies $rL'/L\to0$; dividing by $L^{p-1}$ then reduces to the same comparison. The percolation moment equations and control of their relative errors are hypotheses of this analytic theorem.</p>


## Inverting the critical logarithmic scale {#section-inverse-log-source}

<p>For the choice $\sigma=1/2$ in <a href="/tag/QKHV/">QKHV</a>, the second-to-first moment ratio has order $r^{2\alpha}/\sqrt{\log r}$. The sign of the logarithm in its inverse is easy to track explicitly. Suppose $s$ is eventually continuous and strictly increasing, with</p>
<div class="math-display">$$s(r)\sim A r^{2\alpha}(\log r)^{-1/2},\qquad A,\alpha&gt;0.$$</div>
<p>For its eventual inverse $g$,</p>
<div class="math-display">$$g(n)\sim A^{-1/(2\alpha)}(2\alpha)^{-1/(4\alpha)}n^{1/(2\alpha)}(\log n)^{1/(4\alpha)}.$$</div>
<p>Indeed, the logarithm of the expression on the right is asymptotic to $(\log n)/(2\alpha)$, and substitution into $s$ gives $n(1+o(1))$. Substituting fixed multiples $1-\varepsilon$ and $1+\varepsilon$ gives limiting ratios $(1-\varepsilon)^{2\alpha}$ and $(1+\varepsilon)^{2\alpha}$. Monotonicity traps the inverse between these multiples, proving the equivalent.</p>
<p>If the inverse is written as $g(n)=(A_n^*)^{-1/(2\alpha)}n^{1/(2\alpha)}$, it follows that</p>
<div class="math-display">$$A_n^*\sim A\sqrt{2\alpha}(\log n)^{-1/2}.$$</div>
<p>The negative half-power in $A_n^*$ produces the positive quarter-power in the volume tail. With the source's first-moment coefficient $\alpha/b$, QKHV gives</p>
<div class="math-display">$$\mathbb P(T\geq n)\sim\frac{\alpha}{b}\sqrt{\frac{2}{\pi A\sqrt{2\alpha}}}\,n^{-1/2}(\log n)^{1/4},$$</div>
<p>under its cutoff-to-full transfer assumptions. This agrees with (III.1.19). The intervening prose after (III.1.18), and Remark I.1.16, instead print a positive half-power in $A_n^*$. The former passage also prints a positive half-power in the function being inverted. The <a href="/errata/hutchcroft-lrp-3/#critical-inverse-log-signs">Part III erratum</a> and <a href="/errata/hutchcroft-lrp-1/#critical-inverse-log-sign">Part I erratum</a> record these provisional sign corrections. They concern the introductory substitution, not a refutation of the stated positive-quarter-power tail theorem.</p>
