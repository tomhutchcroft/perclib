---
{
  "id": "sharp-supercritical-field",
  "title": "Sharp supercritical field growth",
  "subtitle": "A valid field rectangle recovers the leading lower bound",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Counting the two initial marked arms retains the factor one half in the magnetization inequality. A rectangle that stays above the finite window yields the leading supercritical lower bound, with a logarithmic error.",
  "context": [
    "Finite connected simple vertex-transitive graphs, independent bonds of probability p, and independent vertex marks of probability gamma.",
    "The graph consequences use the previously proved coarse finite-triangle bounds.",
    "The repaired lower bound does not establish the source’s stronger power-law error or a giant-component theorem."
  ],
  "related": [
    "finite-supercritical-clusters",
    "finite-magnetization-deletion",
    "finite-triangle-window",
    "hypercube-critical-parameter"
  ],
  "sourceIds": [
    "hofstad-nachmias-hypercube",
    "borgs-chayes-finite-window"
  ],
  "aliases": [
    "sharp magnetization differential inequality",
    "supercritical field rectangle",
    "hypercube tail constant two"
  ],
  "prototypeUses": []
}
---

## Counting the two first bonds {#section-double}

<p>Let the finite graph be connected, simple and vertex-transitive, with degree $m\ge1$ and $N$ vertices. Each bond is open with probability $p$, and each vertex is marked with probability $\gamma$, independently. Write $A_x=\{x\leftrightarrow\mathcal G\}$ and $M=\mathbb P(A_x)$. A marked path includes its terminal mark as a coordinate of its witness. Thus $D_x=A_x\circ A_x$ requires distinct terminal marks, even when one path has length zero.</p>
<p>For a deterministic vertex set $S$, let $M_x^S$ and $D_x^S$ denote the corresponding probability and event in the graph induced by $V\setminus S$. They are zero if $x\in S$.</p>

<a id="tag-ZHGE" data-assertion="proposition" data-title="A double marked connection costs half the incident bond sum"></a>
<p>For every $p,\gamma\in[0,1]$ and every $S\subseteq V$,</p>
<div class="math-display">$$\mathbb P(D_x^S)\le\left(\gamma+\frac{mp}{2}M\right)M_x^S.$$</div>
<p><em>Proof.</em> If $x$ is marked and $D_x^S$ occurs, a connection to a different mark witnesses $A_x$ without using the mark at $x$. BK bounds this contribution by $\gamma M_x^S$. If $x$ is unmarked, the two paths begin with different bonds. Each of these bonds $\{x,y\}$ supplies disjoint witnesses for its opening, $A_y$ and $A_x$, all in the induced graph. Count these choices before applying the union bound: there are at least two on the event in question. BK therefore gives</p>
<div class="math-display">$$\mathbb P(D_x^S,x\notin\mathcal G)\le\frac12\sum_{y\sim x,\ y\notin S}pM_y^SM_x^S\le\frac{mp}{2}MM_x^S.$$</div>
<p>The final inequality uses monotone coupling with the full graph. Adding the marked-root contribution proves the claim.</p>

## The sharpened differential inequality {#section-differential}

<a id="tag-BJU4" data-assertion="theorem" data-title="The finite magnetization inequality with the factor one half"></a>
<p>For $0<p<1$ and $0<\gamma<1$,</p>
<div class="math-display">$$M\le\gamma M_\gamma+\left(\frac{mp}{2}M+\gamma\right)(M+pM_p).$$</div>
<p><em>Proof.</em> The probability that the root cluster contains exactly one mark is $\gamma M_\gamma$. If it contains at least two, either $D_o$ occurs, or there is a last open pivotal bond for a connection from $o$ to the marked set. In the latter case, closing that bond leaves an unmarked root cluster and two disjoint marked arms from its other endpoint. The bond is unique: every connection to a mark crosses all pivotal bonds in the same order, and a later pivotal would prevent those two arms. Equivalently, collapse the marked vertices to a sink, keeping one terminal edge per mark, and apply the edge version of Menger's theorem.</p>
<p>For an oriented edge $(x,y)$, put</p>
<div class="math-display">$$w_{x,S}=\mathbb P_p(C_o=S)(1-\gamma)^{|S|}\qquad(o,x\in S,\ y\notin S).$$</div>
<p>Here the event $C_o=S$ fixes its boundary bonds closed. Conditional on it, bonds and marks in the complement retain their product law. Reopening $\{x,y\}$ multiplies its probability by $p/(1-p)$. The last-pivotal decomposition and finite Russo formula give, respectively,</p>
<div class="math-display">$$\mathbb P(|C_o\cap\mathcal G|\ge2,D_o^c)=\frac p{1-p}\sum_{(x,y)}\sum_{S:\,o,x\in S,\ y\notin S}w_{x,S}\mathbb P(D_y^S),$$</div>
<div class="math-display">$$(1-p)M_p=\sum_{(x,y)}\sum_{S:\,o,x\in S,\ y\notin S}w_{x,S}M_y^S.$$</div>
<p>Both edge sums are oriented. The first identity counts the last pivotal exactly once. The second counts every pivotal; in a closed configuration its orientation points from the unmarked root cluster towards a marked cluster. The preceding double-connection estimate bounds the first expression by $(mpM/2+\gamma)pM_p$, and bounds $\mathbb P(D_o)$ by $(mpM/2+\gamma)M$. Add the contribution from exactly one mark.</p>
<p>This proves (A.7) of the <a href="https://ems.press/content/serial-article-files/32188">2017 paper</a> directly. It does not use the different lower double-connection estimate in its Section A.5.</p>

## Integrating over a valid rectangle {#section-rectangle}

<a id="tag-464C" data-assertion="proposition" data-title="An explicit lower field bound from a rectangle with a uniform differential coefficient"></a>
<p>Let a positive $C^1$ function $M$ be nondecreasing in both variables on $[p_0,p_1]\times[\gamma_0,\gamma_1]$, where $0<p_0<p_1$ and $0<\gamma_0<\gamma_1$. Suppose that, for a constant $A>0$,</p>
<div class="math-display">$$M\le\gamma M_\gamma+\frac A2M^2+\frac A2pMM_p.$$</div>
<p>If $M(p_0,\gamma_0)\ge L>0$ and $M(p_1,\gamma_1)\le U$, then</p>
<div class="math-display">$$M(p_1,\gamma_1)\ge\frac{p_0}{p_1}L+\frac{2(p_1-p_0)}{Ap_1}\left[1-\frac{\log(U/L)}{\log(\gamma_1/\gamma_0)}\right].$$</div>
<p><em>Proof.</em> Divide the differential inequality by $\gamma M$ and rewrite it as</p>
<div class="math-display">$$0\le\partial_\gamma\log M+\frac1\gamma\partial_p\left(\frac A2pM-p\right).$$</div>
<p>Integrating over the rectangle and using monotonicity at its four corners gives, with $M_i=M(p_i,\gamma_i)$ and $\ell=\log(\gamma_1/\gamma_0)>0$,</p>
<div class="math-display">$$0\le(p_1-p_0)\log(M_1/M_0)+\ell\left[\frac A2(p_1M_1-p_0M_0)-(p_1-p_0)\right].$$</div>
<p>Rearrange, then use $M_0\ge L$ and $M_1/M_0\le U/L$. A negative bracket causes no difficulty.</p>

## Staying above the finite window {#section-growth}

<p>Use the reference-point hypotheses of <a href="/tag/UQ45/">UQ45</a>: $0<p_c\le1/2$, $H=\chi(p_c)=\lambda N^{1/3}\ge100$, and $T_{p_c}^3(x,y)\le\mathbf1_{\{x=y\}}+a$ with $a\le1/100$. Put $\rho=mp_c$. Choose $0<\alpha<\beta<1/3$, and let $c_\beta>0,R_\beta$ be the constants in UQ45 with exponent $3\beta$. Set $c=c_\beta/2$.</p>
<p>Our displacement is additive: $\varepsilon=m(p-p_c)$. If the paper's parameter is written as $p=p_c(1+e)$, then $\varepsilon=\rho e$. The two normalizations have the same leading constant when $\rho\to1$.</p>

<a id="tag-7DLQ" data-assertion="theorem" data-title="A finite supercritical field lower bound with a logarithmic error"></a>
<p>Let $0<\varepsilon\le1$, $p=p_c+\varepsilon/m\le1/2$, $Q=\varepsilon^3N>e$, and define</p>
<div class="math-display">$$\delta=\frac1{\log Q},\qquad \gamma=\varepsilon^2Q^{-\alpha},\qquad \ell=(\beta-\alpha)\log Q+(2-3\beta)\log(1/\delta),$$</div>
<div class="math-display">$$A=\rho+\varepsilon+\frac{2\varepsilon Q^{-\alpha}}{c\delta}.$$</div>
<p>If $\delta Q^{1/3}\ge R_\beta$, then</p>
<div class="math-display">$$M(p,\gamma)\ge\frac{2\varepsilon(1-\delta)}{A(\rho+\varepsilon)}\left[1-\frac{\log(106/(c\delta))}{\ell}\right].$$</div>
<p>In particular, for a family with fixed $\lambda,\alpha,\beta$, $\varepsilon\to0$, $Q\to\infty$ and $\rho\to1$,</p>
<div class="math-display">$$M(p,\varepsilon^2Q^{-\alpha})\ge2\varepsilon\left[1-O\left(|\rho-1|+\varepsilon+\frac{\log\log Q}{\log Q}\right)\right].$$</div>
<p><em>Proof.</em> Take</p>
<div class="math-display">$$p_0=p_c+\delta\varepsilon/m,\qquad \gamma_0=(\delta\varepsilon)^2(\delta^3Q)^{-\beta}.$$</div>
<p>The condition on $R_\beta$ allows UQ45 at $p_0$. A cluster at least $1/\gamma_0$ in size is marked with probability at least $1-e^{-1}>1/2$, so $M(p_0,\gamma_0)\ge c\delta\varepsilon$. Also</p>
<div class="math-display">$$\frac\gamma{\gamma_0}=Q^{\beta-\alpha}\delta^{-(2-3\beta)}>1.$$</div>
<p>Both fields lie in $(0,1)$: $\gamma<1$ and $\gamma_0<\gamma$. Everywhere on this rectangle, $M\ge c\delta\varepsilon$, and hence</p>
<div class="math-display">$$mp'+\frac{2\gamma'}{M(p',\gamma')}\le\rho+\varepsilon+\frac{2\varepsilon Q^{-\alpha}}{c\delta}=A.$$</div>
<p>The sharpened differential inequality therefore has the uniform coefficient required by the rectangle lemma. The coarse upper field estimate from <a href="/tag/1T2M/">1T2M</a> gives $M(p,\gamma)\le106\varepsilon$, since $\gamma\le\varepsilon^2$; when $\gamma>1/2$, the deterministic bound $M\le1$ gives the same conclusion. Apply the rectangle lemma with $L=c\delta\varepsilon$, $U=106\varepsilon$, then discard its positive first term. The identity $(p-p_0)/p=\varepsilon(1-\delta)/(\rho+\varepsilon)$ yields the displayed bound.</p>
<p>For the asymptotic statement, $\delta^3Q=Q/(\log Q)^3\to\infty$, so the starting point remains above the window. Also $Q^{-\alpha}\log Q\to0$, $A=\rho+O(\varepsilon)$, and $\log(106/(c\delta))/\ell=O(\log\log Q/\log Q)$. Expanding the remaining positive factors proves the claim. The condition $\rho\to1$ is explicit; a fixed small triangle bound alone is not silently substituted for it.</p>

## From the field to the cluster tail {#section-tail}

<a id="tag-CI72" data-assertion="corollary" data-title="The leading supercritical tail lower bound from separated marking fields"></a>
<p>For a family satisfying the preceding reference-point hypotheses with fixed $\lambda$, $\varepsilon\to0$, $Q=\varepsilon^3N\to\infty$ and $mp_c\to1$, every fixed $0<\alpha<1/3$ satisfies</p>
<div class="math-display">$$\mathbb P_p\left(|C_o|\ge\varepsilon^{-2}Q^\alpha\right)\ge2\varepsilon\left[1-O\left(|mp_c-1|+\varepsilon+\frac{\log\log Q}{\log Q}\right)\right],\qquad p=p_c+\varepsilon/m\le1/2.$$</div>
<p><em>Proof.</em> Choose $\alpha<\beta<\sigma<1/3$. Apply the preceding field bound with exponents $\beta,\sigma$, using $\gamma_1=\varepsilon^2Q^{-\beta}$. Set $\gamma_0=\varepsilon^2Q^{-\alpha}$ and $k=1/\gamma_0$. For an integer $s<k$,</p>
<div class="math-display">$$1-(1-\gamma_1)^s\le\gamma_1s\le2\frac{\gamma_1}{\gamma_0}[1-(1-\gamma_0)^s].$$</div>
<p>Indeed $1-(1-1/k)^s\ge1-e^{-s/k}\ge(1-e^{-1})s/k$ and $(1-e^{-1})^{-1}<2$. Splitting the field expectation at $|C_o|\ge k$ gives</p>
<div class="math-display">$$\mathbb P_p(|C_o|\ge k)\ge M(p,\gamma_1)-2Q^{\alpha-\beta}M(p,\gamma_0)\ge M(p,\gamma_1)-212\varepsilon Q^{\alpha-\beta}.$$</div>
<p>The last error is smaller than the logarithmic error already present. A real cutoff means its ceiling throughout, so no integer convention changes the argument.</p>
<p>This rectangle proof gives the leading constant two with a logarithmic error. The later <a href="/articles/characteristic-field-growth/">characteristic argument</a> supplies a polynomial lower error, and the <a href="/articles/quantitative-supercritical-tails/">quantitative tail estimates</a> give matching bounds. A giant-component lower bound still requires a separate argument.</p>

## A mark at the root is not two marked arms {#section-root}

<a id="tag-E7N9" data-assertion="proposition" data-title="The exact root-mark contribution to a double marked connection"></a>
<p>For $0\le\gamma<1$,</p>
<div class="math-display">$$\mathbb P(D_o)=\frac{\gamma(M-\gamma)}{1-\gamma}+(1-\gamma)\mathbb P(D_o\mid o\notin\mathcal G).$$</div>
<p>In particular the first term cannot be replaced by $\gamma$. At $p=0$ on any nonempty finite graph, $M=\gamma$ and $\mathbb P(D_o)=0$.</p>
<p><em>Proof.</em> Let $B$ be the event that $o$ connects to a mark at another vertex. This event is independent of the root mark, and $M=\gamma+(1-\gamma)\mathbb P(B)$. On the event that $o$ is marked, $D_o$ occurs exactly when $B$ does: the root mark supplies one witness and a path to another mark supplies the other. Thus $\mathbb P(D_o,o\in\mathcal G)=\gamma\mathbb P(B)$. Split according to the root mark and substitute for $\mathbb P(B)$.</p>
<p>The <a href="/errata/hofstad-nachmias-hypercube/#double-mark-root-event">source event distinction</a> affects the lower double-connection route in Section A.5. The sharper upper differential inequality proved above uses the two distinct marks consistently and does not depend on that route.</p>

## Scope of the repair {#section-source}

<p>The <a href="/errata/hofstad-nachmias-hypercube/#supercritical-field-rectangle">rectangle entry</a> records two difficulties in Lemma A.6: its final auxiliary field exceeds the target field, while monotonicity is used in the opposite direction, and its exponentially small starting displacement no longer lies above the critical window. Taking $\delta=1/\log Q$ and separating the two cutoff exponents avoids both problems. The present rectangle proof has a logarithmic error. Its statement remains valid, but the later <a href="/articles/characteristic-field-growth/">characteristic proof</a> removes that loss and completes the polynomial lower-tail repair. The rectangle entry is therefore now labelled “fix found / substantial”.</p>
<p>The field ratio in the subsequent tail argument is $Q^{\alpha-\beta}$ when $\alpha<\beta$; its sign has a separate <a href="/errata/hofstad-nachmias-hypercube/#tail-field-ratio-sign">local correction</a>. The entries remain provisional. The <a href="/coverage/sources/sharp-supercritical-field/">reading map</a> distinguishes the journal passages read from the selected matching preprint passages. No new formal proof or independent audit is claimed.</p>
