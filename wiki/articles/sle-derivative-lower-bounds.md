---
{
  "id": "sle-derivative-lower-bounds",
  "title": "Lower bounds for SLE derivative moments",
  "subtitle": "A tilted diffusion controls the height-crossing time",
  "kind": "method",
  "category": "General theory",
  "summary": "The derivative martingale changes the ratio diffusion into one with a strong inward drift. A small exponential moment bounds the physical crossing time and the terminal ratio, yielding the fixed-time lower estimate and the sharp threshold for expected localized grid sums.",
  "context": [
    "We use ordinary chordal SLE with positive kappa, Loewner coefficient two, and the reverse-flow notation of the derivative-estimates article. No trace theorem is needed.",
    "Girsanov's theorem, Ito calculus and Brownian exponential moments are the probabilistic inputs. The martingale used to change measure has already been proved to be a true martingale on bounded height-clock intervals.",
    "The lower estimate allows negative moment orders. The comparison from a height-crossing time to a fixed physical time uses the absolute log-derivative bound, not derivative monotonicity.",
    "The grid result concerns expectation. Infinite expected sums do not establish almost-sure divergence or a Hausdorff lower bound; comparison with the global Whitney sum remains separate."
  ],
  "related": ["sle-derivative-estimates", "sle-hull-boundary", "sle-conformal-radius"],
  "sourceIds": ["rohde-schramm-basic-sle-2005"],
  "aliases": ["SLE derivative lower moment", "tilted SLE ratio diffusion", "SLE critical grid sum"],
  "prototypeUses": []
}
---

## An inward drift controls the physical clock {#section-clock-moment}

<p>Consider the diffusion</p>
<div class="math-display">$$dV_s=\sqrt{\kappa/2}\,dB_s-\beta\tanh(V_s)\,ds,
\qquad V_0=v,$$</div>
<p>where $\kappa&gt;0$ and $\beta&gt;1$. Its drift is bounded and globally Lipschitz. For $L\geq0$, define</p>
<div class="math-display">$$I_L=\frac12\int_0^L e^{2(s-L)}\cosh^2(V_s)\,ds.$$</div>

<a id="tag-CUBE" data-assertion="proposition" data-title="An inward hyperbolic drift gives uniform fractional moments of an exponentially weighted physical clock"></a>
<p>There are $r\in(0,1)$ and $A&lt;\infty$, depending only on $\kappa,\beta$, such that</p>
<div class="math-display">$$\mathbb E_v[\cosh^r(V_L)]+\mathbb E_v[I_L^{r/2}]\leq A
\qquad\text{whenever }e^{-L}\cosh v\leq1.$$</div>
<p>Consequently there are finite $C,R\geq1$, independent of $L,v$ in this range, for which</p>
<div class="math-display">$$\mathbb P_v\bigl(I_L\leq C,\ \cosh(V_L)\leq R\bigr)\geq\frac12.$$</div>
<p><em>Proof.</em> Choose</p>
<div class="math-display">$$0&lt;r&lt;\min\left\{1,\frac{4(\beta-1)}\kappa\right\},
\qquad r&lt;m&lt;r\beta-\frac{\kappa r^2}{4},
\qquad \Phi(v)=\cosh^r v.$$</div>
<p>The generator $\mathcal L=(\kappa/4)\partial_v^2-\beta\tanh v\,\partial_v$ satisfies</p>
<div class="math-display">$$\frac{\mathcal L\Phi(v)}{\Phi(v)}
=\frac{\kappa r}{4}\operatorname{sech}^2v
+\left(\frac{\kappa r^2}{4}-\beta r\right)\tanh^2v.$$</div>
<p>Its limit at either end of the real line is less than $-m$. Thus $\mathcal L\Phi\leq A_0-m\Phi$ for a finite $A_0$. Ito's formula and Gronwall's inequality give</p>
<div class="math-display">$$\mathbb E_v[\Phi(V_s)]\leq e^{-ms}\Phi(v)+A_0/m.$$</div>
<p>The bounded drift and Gaussian exponential moments justify taking expectations here, by localization or directly on each bounded time interval.</p>
<p>The same estimate controls the maximum on a unit interval. Since $\log\cosh$ is one-Lipschitz and the drift has absolute value at most $\beta$,</p>
<div class="math-display">$$\sup_{0\leq u\leq1}\Phi(V_{j+u})
\leq\Phi(V_j)\exp\left(r\beta+r\sqrt{\kappa/2}
\sup_{0\leq u\leq1}|B_{j+u}-B_j|\right).$$</div>
<p>The Brownian factor is independent of $V_j$ and has finite expectation. It follows that the expected maximum is at most $A_1(e^{-mj}\Phi(v)+1)$.</p>
<p>Set $q=r/2&lt;1$ and split the clock integral into intervals $[j,(j+1)\wedge L]$. Subadditivity of the $q$th power gives</p>
<div class="math-display">$$\begin{aligned}
\mathbb E_v[I_L^q]
&\leq A_2\sum_{j=0}^{\lfloor L\rfloor}
e^{r(j-L)}\bigl(1+e^{-mj}\Phi(v)\bigr)\\
&\leq A_3\bigl(1+e^{-rL}\Phi(v)\bigr)\leq2A_3.
\end{aligned}$$</div>
<p>Both geometric sums converge uniformly because $m&gt;r&gt;0$. Also $e^{-mL}\Phi(v)\leq e^{-(m-r)L}\leq1$, which bounds the terminal moment. Markov's inequality, with each of the two exceptional probabilities at most one quarter, proves the final assertion.</p>

## The derivative-martingale change of measure {#section-tilted-crossing}

<p>For reverse Loewner flow started at $z=x+iy$, write $Z_t=X_t+iY_t=H_t(z)-U_t$, $D_t=|H_t'(z)|$, and $\tau_1=\inf\{t:Y_t=1\}$. We use $|z|\leq1$, so $y\leq1$. For a real parameter</p>
<div class="math-display">$$b&lt;\frac14+\frac1\kappa,$$</div>
<p>put</p>
<div class="math-display">$$a=2b+\frac{\kappa b(1-b)}2,
\qquad \lambda=4b+\frac{\kappa b(1-2b)}2.$$</div>

<a id="tag-G4U8" data-assertion="proposition" data-title="A uniformly positive part of the derivative moment reaches height one in bounded physical time with bounded terminal ratio"></a>
<p>There are constants $C,R\geq1$ and $c_0&gt;0$, depending only on $\kappa,b$, such that for every $z\in\mathbb H$ with $|z|\leq1$,</p>
<div class="math-display">$$\mathbb E\!\left[D_{\tau_1}^a
\mathbf1_{\{\tau_1\leq C,\ \sqrt{1+X_{\tau_1}^2}\leq R\}}\right]
\geq c_0\left(1+\frac{x^2}{y^2}\right)^b y^{\lambda-a}.$$</div>
<p><em>Proof.</em> Let $s=\log(Y_t/y)$, $L=\log(1/y)$ and $V_s=\operatorname{arsinh}(X_{t(s)}/Y_{t(s)})$. The global height clock of <a href="/tag/O0VQ/">O0VQ</a> reaches $L$ at $\tau_1$. Applying Ito's formula to its ratio diffusion gives</p>
<div class="math-display">$$dV_s=\sqrt{\kappa/2}\,dB_s-\left(2+\frac\kappa4\right)\tanh(V_s)\,ds.$$</div>
<p>The positive martingale of <a href="/tag/AXSH/">AXSH</a> is</p>
<div class="math-display">$$M_s=\left(\frac{yD_{t(s)}}{Y_{t(s)}}\right)^a
\cosh^{2b}(V_s)Y_{t(s)}^\lambda,
\qquad \frac{dM_s}{M_s}=\sqrt{2\kappa}\,b\tanh(V_s)\,dB_s.$$</div>
<p>Its stochastic coefficient is bounded. On the clock interval $[0,L]$, define $d\mathbb Q=(M_L/M_0)\,d\mathbb P$. Girsanov's theorem changes the drift of $V$ to</p>
<div class="math-display">$$dV_s=\sqrt{\kappa/2}\,d\widetilde B_s-\beta\tanh(V_s)\,ds,
\qquad \beta=2+\frac\kappa4-\kappa b&gt;1.$$</div>
<p>Moreover, $Y_{t(s)}=e^{s-L}$ and the physical clock is</p>
<div class="math-display">$$\tau_1=\frac12\int_0^L e^{2(s-L)}\cosh^2(V_s)\,ds.
$$</div>
<p>The initial condition obeys $e^{-L}\cosh(V_0)=|z|\leq1$. CUBE therefore gives constants $C,R$ for which the event $A=\{\tau_1\leq C,\ \cosh(V_L)\leq R\}$ has $\mathbb Q$-probability at least one half. At clock time $L$, $Y=1$ and $\cosh(V_L)=\sqrt{1+X_{\tau_1}^2}$. Removing the change-of-measure density gives</p>
<div class="math-display">$$\begin{aligned}
\mathbb E_{\mathbb P}[D_{\tau_1}^a\mathbf1_A]
&=M_0y^{-a}\mathbb E_{\mathbb Q}[\cosh^{-2b}(V_L)\mathbf1_A]\\
&\geq\frac12R^{-2\max\{b,0\}}
\left(1+\frac{x^2}{y^2}\right)^b y^{\lambda-a}.
\end{aligned}$$</div>
<p>This proves the estimate without a sign restriction on $a$ or $b$ beyond the stated bound on $b$.</p>

## The fixed-time lower bound {#section-fixed-time-lower}

<a id="tag-7NGO" data-assertion="theorem" data-title="Inverse SLE derivative moments have the fixed-time lower bound with a positive image-height cutoff throughout the stated parameter range"></a>
<p>For every $\kappa&gt;0$ and $b&lt;1/4+1/\kappa$, with $a,\lambda$ as above, there is $c&gt;0$ such that</p>
<div class="math-display">$$\mathbb E\!\left[|\widehat f_1'(x+iy)|^a
\mathbf1_{\{\operatorname{Im}\widehat f_1(x+iy)\geq c\}}\right]
\geq c\left(1+\frac{x^2}{y^2}\right)^b y^{\lambda-a}
\qquad(x+iy\in\mathbb H,\ |x+iy|\leq c).$$</div>
<p><em>Proof.</em> Use the constants of G4U8. On its event $A$, reverse flow has reached height one by physical time $C$. Thus $Y_C\geq1$, and $Y_C^2\leq1+4(C-\tau_1)\leq1+4C$. The absolute log-derivative comparison O0VQ gives</p>
<div class="math-display">$$D_C^a\geq(1+4C)^{-|a|/2}D_{\tau_1}^a.$$</div>
<p>This inequality is valid for every real $a$. Taking expectations over $A$ and using the reverse/inverse identity <a href="/tag/HHBC/">HHBC</a> yields</p>
<div class="math-display">$$\mathbb E\!\left[|\widehat f_C'(x+iy)|^a
\mathbf1_{\{\operatorname{Im}\widehat f_C(x+iy)\geq1\}}\right]
\geq c_1\left(1+\frac{x^2}{y^2}\right)^b y^{\lambda-a}
\qquad(|x+iy|\leq1).$$</div>
<p>Brownian scaling gives $\widehat f_C(\sqrt C\,w)\overset{\mathrm{law}}=\sqrt C\,\widehat f_1(w)$, including the derivative identity. Substituting $x+iy=\sqrt C\,w$ gives the desired lower bound on $|w|\leq C^{-1/2}$, with image cutoff $C^{-1/2}$ and coefficient $c_1C^{(\lambda-a)/2}$. Choose $c$ no larger than these two constants and one. Decreasing the image cutoff enlarges the event and decreasing the coefficient weakens the lower bound, completing the proof.</p>
<p>This proves Rohde–Schramm Lemma 3.3. CUBE supplies the uniform probability estimate by fractional moments instead of the source's pathwise tube event. The bounded factor above incorporates the <a href="/errata/rohde-schramm-basic-sle-2005/#reverse-derivative-comparison">provisional derivative-comparison repair</a>; no monotonicity of $D_t$ is assumed.</p>

## The exact threshold for expected localized grid sums {#section-critical-grid}

<p>Let $F=\widehat f_1$ and use the dyadic sum $J_{p,h,L}(F)$ and exponent $\delta(\kappa)$ defined in the <a href="/articles/sle-hull-boundary/#section-grid-sums">hull-boundary article</a>. The cutoff $h$ is an image height, and $L$ bounds the real coordinate of the grid before applying $F$.</p>

<a id="tag-T3F8" data-assertion="theorem" data-title="Expected localized inverse-map grid sums have the sharp boundary moment threshold away from kappa four"></a>
<p>For each $\kappa&gt;0$, $\kappa\ne4$, there is $h_0&gt;0$ such that for every $0&lt;h\leq h_0$, $L&gt;0$ and $p&gt;0$,</p>
<div class="math-display">$$\mathbb E[J_{p,h,L}(F)]
\begin{cases}&lt;\infty,&p&gt;\delta(\kappa),\\
=\infty,&0&lt;p\leq\delta(\kappa).
\end{cases}$$</div>
<p><em>Proof.</em> Finiteness above the threshold is <a href="/tag/AVHR/">AVHR</a>. For the reverse direction take $b_* =\min\{1/2,2/\kappa\}$. Since $\kappa\ne4$,</p>
<div class="math-display">$$b_*&lt;\frac14+\frac1\kappa,
\qquad a(b_*)=\delta(\kappa),
\qquad \lambda(b_*)-2b_*-1=0.$$</div>
<p>Let $c$ be the constant from 7NGO and set $h_0=c$. Fix $u&gt;0$ with $2u&lt;\min\{L,c/2\}$. At all sufficiently small grid heights $y=2^{-n}$, the points with $u\leq j y\leq2u$ lie in $\{|z|\leq c\}$, and there are at least $u/(2y)$ of them. For each such point, 7NGO gives</p>
<div class="math-display">$$\mathbb E\!\left[(y|F'(j y+iy)|)^{\delta(\kappa)}
\mathbf1_{\{\operatorname{Im}F(j y+iy)\geq h\}}\right]
\geq c\,u^{2b_*}y^{\lambda(b_*)-2b_*}.$$</div>
<p>The expected contribution from each sufficiently fine level is therefore bounded below by a positive constant independent of $n$. Tonelli's theorem gives $\mathbb E[J_{\delta(\kappa),h,L}(F)]=\infty$. For $0&lt;p&lt;\delta(\kappa)$, Schwarz–Pick and the reverse height bound give $A:=y|F'(j y+iy)|\leq\sqrt5$ at these fine levels. Hence</p>
<div class="math-display">$$A^p\geq5^{(p-\delta(\kappa))/2}A^{\delta(\kappa)},$$</div>
<p>which proves divergence for every smaller positive exponent.</p>
<p>This is a threshold for expected localized grid sums. It does not assert their almost-sure divergence. Transferring it to the global Whitney sum of Theorem 8.3, and then to the expected-covering conclusion of Corollary 8.5, requires the corresponding geometric comparisons.</p>


## Transfer to Whitney sums {#section-whitney-update}

<p><a href="/tag/J0CG/">J0CG</a> now transfers the expected grid threshold to the global Whitney sum near the hull. The upper comparison controls a random horizontal window by the Brownian maximum. For the lower comparison, an upper moment removes the large derivative scales; each remaining image point lies near the hull and belongs to a comparable Whitney square. <a href="/tag/K5PX/">K5PX</a> then gives the expected-covering lower limsup, using squares above height twice the cutoff. These conclusions still concern expectation and do not establish a Hausdorff lower bound.</p>
