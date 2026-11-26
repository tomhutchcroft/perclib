---
{
  "id": "fourier-bootstrap",
  "title": "The Fourier bootstrap functions",
  "subtitle": "Reciprocal differences, subcritical moments and continuity",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "An absolute-value reciprocal estimate handles signed kernels. Finite susceptibility supplies the weighted continuity needed for the bootstrap supremum, including frequencies approaching zero.",
  "context": [
    "Nearest-neighbour percolation on $\\mathbb Z^d$, $d\\ge1$, when percolation is invoked.",
    "The reciprocal estimate is first stated for an arbitrary real even summable kernel.",
    "The quantitative improvement of the bootstrap bound is a separate premise."
  ],
  "related": [
    "weighted-lace-coefficients",
    "signed-kernel-moments",
    "lace-expansion",
    "sharpness-bond-parameter"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "Fourier bootstrap",
    "reciprocal second difference",
    "bootstrap continuity"
  ],
  "prototypeUses": []
}
---

## The reciprocal difference estimate {#section-reciprocal}

<p>For a real even summable kernel $a$, write $\widehat a(q)=\sum_xa(x)\cos(q\cdot x)$ and</p>
<div class="math-display">$$M_a(q)=\sum_x|a(x)|[1-\cos(q\cdot x)].$$</div>
<a id="tag-84XD" data-assertion="theorem" data-title="An absolute-value reciprocal estimate for real even summable kernels"></a>
<p>Fix $k,l$ such that $1-\widehat a$ is nonzero at $l,l-k,l+k$. Put $A_0=(1-\widehat a(l))^{-1}$ and $A_\pm=(1-\widehat a(l\pm k))^{-1}$. Then</p>
<div class="math-display">$$|A_-+A_+-2A_0|
\le(|A_-|+|A_+|)|A_0|M_a(k)
+8|A_-A_0A_+|M_a(l)M_a(k).$$</div>
<p><em>Proof.</em> Set $a_0=\widehat a(l)$, $a_\pm=\widehat a(l\pm k)$. Subtracting reciprocals twice gives the exact identity</p>
<div class="math-display">$$A_-+A_+-2A_0
=\frac{A_0(A_-+A_+)}2(a_-+a_+-2a_0)
+\frac{A_0A_-A_+}2(a_+-a_-)^2.$$</div>
<p>The cosine addition formula and absolute summability give</p>
<div class="math-display">$$|a_-+a_+-2a_0|\le2M_a(k),\qquad
a_+-a_-=-2\sum_xa(x)\sin(l\cdot x)\sin(k\cdot x).$$</div>
<p>Cauchy–Schwarz with the weight $|a(x)|$, followed by $\sin^2t\le2(1-\cos t)$, gives $|a_+-a_-|^2\le16M_a(l)M_a(k)$. Apply these two bounds to the identity, retaining absolute values of the reciprocal factors.</p>
<p>Those absolute values may be omitted when the three reciprocals are positive. Evenness alone does not ensure this. For example, on $\mathbb Z$ take $a(0)=2$, $a(1)=a(-1)=1/4$, and zero elsewhere. Then $\widehat a(q)=2+\tfrac12\cos q$, so every reciprocal is defined and negative. At $k=l=\pi/2$ one has</p>
<div class="math-display">$$A_0=-1,\qquad A_-=-\tfrac23,\qquad A_+=-2,\qquad M_a(k)=M_a(l)=\tfrac12.$$</div>
<p>The left side is $2/3$, while the proposed right side without the absolute values is $-4/3$. The <a href="/errata/heydenreich-hofstad/#reciprocal-fourier-sign">provisional erratum</a> records the missing sign qualification in the dated manuscript's Lemma 8.2. The corrected estimate above keeps the original constant eight.</p>

## The random-walk comparison {#section-walk}

<p>Let $D$ be uniform on the $2d$ nearest neighbours, put $g(k)=1-\widehat D(k)$, and set $C_\lambda(k)=(1-\lambda\widehat D(k))^{-1}$ for $0\le\lambda<1$. These reciprocals are positive.</p>
<a id="tag-TTS1" data-assertion="proposition" data-title="Positive random-walk reciprocals satisfy the bootstrap comparison and difference bounds"></a>
<p>For $k\ne0$ on the torus,</p>
<div class="math-display">$$C_\lambda(k)\le\frac2{1+\lambda}\frac1{g(k)}.$$</div>
<p>For every $k,l$, with $C_0^*=C_\lambda(l)$ and $C_\pm^*=C_\lambda(l\pm k)$,</p>
<div class="math-display">$$|C_-^*+C_+^*-2C_0^*|
\le g(k)\bigl[C_0^*C_-^*+C_0^*C_+^*+8C_-^*C_+^*\bigr].$$</div>
<p><em>Proof.</em> If $t\in[-1,1]$, then</p>
<div class="math-display">$$2(1-\lambda t)-(1+\lambda)(1-t)=(1-\lambda)(1+t)\ge0,$$</div>
<p>which proves the comparison. Apply 84XD with $a=\lambda D$. Here $M_a(q)=\lambda g(q)$, and</p>
<div class="math-display">$$C_\lambda(l)\lambda g(l)\le1,$$</div>
<p>because $1-\lambda\widehat D(l)-\lambda g(l)=1-\lambda\ge0$. The first term in 84XD is at most $g(k)C_0^*(C_-^*+C_+^*)$, and the second is at most $8g(k)C_-^*C_+^*$.</p>
<p>Thus the usual positive majorant</p>
<div class="math-display">$$U_\lambda(k,l)=200g(k)\bigl[C_\lambda(l-k)C_\lambda(l)+C_\lambda(l)C_\lambda(l+k)+C_\lambda(l-k)C_\lambda(l+k)\bigr]$$</div>
<p>dominates the random-walk difference. The sign repair does not change this application.</p>

## Weighted continuity below criticality {#section-moments}

<a id="tag-8LOF" data-assertion="proposition" data-title="Finite susceptibility gives spatial moments and subcritical weighted continuity on the nearest-neighbour lattice"></a>
<p>If $\chi(p)<\infty$, then $\sum_x(1+|x|^2)\tau_p(x)<\infty$. Moreover, on $[0,p_c)$ the map $p\mapsto\tau_p$ is continuous for the norm</p>
<div class="math-display">$$\|f\|_{1,2}=\sum_x(1+|x|^2)|f(x)|.$$</div>
<p><em>Proof.</em> Choose a finite box $S\ni0$ with</p>
<div class="math-display">$$q=\sum_{\substack{u\in S,\ v\notin S\\u\sim v}}p\,\tau_{S,p}(0,u)<1.$$</div>
<p>Such boxes exist: the displayed sum is bounded by $2dp$ times the sum of $\tau_p(u)$ over the inner boundary, and this tends to zero as the box grows. Define $b(x)=\mathbf1_{\{x\in S\}}\tau_{S,p}(0,x)$ and</p>
<div class="math-display">$$K(v)=\mathbf1_{\{v\notin S\}}\sum_{\substack{u\in S\\u\sim v}}p\,\tau_{S,p}(0,u).$$</div>
<p>A simple connection path either stays in $S$ or has a first exit bond $(u,v)$. Its internal prefix, that bond and its remaining segment are edge-disjoint. BK and a union bound give $\tau_p\le b+K*\tau_p$. Since $\|K\|_1=q<1$ and $\tau_p\le1$, iteration yields</p>
<div class="math-display">$$\tau_p\le\sum_{m\ge0}K^{*m}*b.$$</div>
<p>If $S$ lies in the sup-norm ball of radius $R$, the $m$th term has mass $q^m\|b\|_1$ and support in the ball of radius $R+m(R+1)$. Its weighted mass is at most</p>
<div class="math-display">$$\bigl[1+d\{R+m(R+1)\}^2\bigr]q^m\|b\|_1.$$</div>
<p>The sum is finite. This proves the moment assertion, including $q=0$.</p>
<p>By <a href="/tag/JQLC/">sharpness</a>, susceptibility is finite at every $p<p_c$. Under the uniform-edge coupling, the root cluster at a fixed such parameter is finite almost surely. Its finitely many internal and boundary edges have thresholds different from $p$, so the root cluster is unchanged for all sufficiently close parameters, almost surely. Hence $\tau_{p'}(x)\to\tau_p(x)$ for each $x$ by bounded convergence. Choose $b_0$ with $p<b_0<p_c$. The finite weighted sum of $\tau_{b_0}$ dominates the differences for $p'$ near $p$. Dominated convergence gives continuity in $\|\cdot\|_{1,2}$, one-sided at zero.</p>

## Continuity of the bootstrap supremum {#section-continuity}

<p>For $p<p_c$, let $\lambda_p=1-1/\chi(p)$ and define</p>
<div class="math-display">$$f_1(p)=2dp,\quad f_2(p)=\sup_l\frac{\widehat\tau_p(l)}{C_{\lambda_p}(l)},\quad
f_3(p)=\sup_{k\ne0,l}\frac{|\widehat\tau_p(l-k)+\widehat\tau_p(l+k)-2\widehat\tau_p(l)|}{U_{\lambda_p}(k,l)}.$$</div>
<p>The frequency $k=0$ is omitted in $f_3$, since both numerator and denominator then vanish. Equivalently, assign the quotient zero at that frequency; this does not affect its supremum.</p>
<a id="tag-NL05" data-assertion="theorem" data-title="The percolation bootstrap functions are continuous and the forbidden-region argument applies"></a>
<p>The functions $f_1,f_2,f_3$ are finite and continuous on $[0,p_c)$. Their maximum $f$ satisfies $f(0)=1$. Consequently, if $1\le a<b<\infty$ and</p>
<div class="math-display">$$f(p)\le b\ \Longrightarrow\ f(p)\le a\qquad(0<p<p_c),$$</div>
<p>then $f(p)\le a$ throughout $[0,p_c)$.</p>
<p><em>Proof.</em> 8LOF gives local uniform control and continuity in the weighted norm. In particular $\chi$ and $\lambda_p$ are continuous, and $\lambda_p$ is bounded away from one on every compact subinterval of $[0,p_c)$. The Fourier transforms vary uniformly, so $f_2$, the supremum of $\widehat\tau_p(l)(1-\lambda_p\widehat D(l))$, is continuous.</p>
<p>For $f_3$, absolute summability and the cosine addition formula give</p>
<div class="math-display">$$\widehat\tau_p(l-k)+\widehat\tau_p(l+k)-2\widehat\tau_p(l)
=-2\sum_x[1-\cos(k\cdot x)]\cos(l\cdot x)\tau_p(x).$$</div>
<p>Choose representatives $k_i\in[-\pi,\pi]$. Then</p>
<div class="math-display">$$g(k)\ge\frac{2|k|^2}{\pi^2d},\qquad
\frac{1-\cos(k\cdot x)}{g(k)}\le\frac{\pi^2d}4|x|^2\quad(k\ne0).$$</div>
<p>It follows that the numerator divided by $g(k)$ varies uniformly continuously with $p$, uniformly over $k\ne0,l$. Indeed its difference at two parameters is bounded by $\tfrac12\pi^2d\|\tau_p-\tau_{p'}\|_{1,2}$. This estimate handles frequencies arbitrarily close to zero.</p>
<p>Write $U_\lambda=200gV_\lambda$, where $V_\lambda$ is the sum of the three products in TTS1. Since $C_\lambda\ge1/(1+\lambda)\ge1/2$, one has $V_\lambda\ge3/4$. On a compact parameter interval, $V_{\lambda_p}$ varies uniformly continuously and remains bounded. Dividing by it preserves uniform continuity of the ratios. The inequality $|\sup F-\sup G|\le\sup|F-G|$ now proves continuity of $f_3$ without assuming that a maximizing frequency exists. Finiteness follows from the same estimates.</p>
<p>At $p=0$, $\tau_0=\delta_0$, $\chi(0)=1$, and $\lambda_0=0$. Hence $(f_1,f_2,f_3)=(0,1,0)$. Finally, the weak-to-strong implication excludes every value of $f$ in $(a,b]$. A continuous function starting at or below $a$ cannot reach a value above $a$ without taking a value in $(a,b)$, by the intermediate value theorem. This proves the last assertion.</p>
<p>The quantitative weak-to-strong implication is not proved here. It requires the frequency-diagram bounds and the reciprocal estimates applied to the effective lace kernel with all their hypotheses checked. The <a href="/coverage/sources/heydenreich-hofstad-2017-bootstrap/">Chapter 8 reading map</a> distinguishes these remaining steps from the continuity and algebra supplied above.</p>
