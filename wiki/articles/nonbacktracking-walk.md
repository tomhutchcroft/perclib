---
{
  "id": "nonbacktracking-walk",
  "title": "Non-backtracking walks and the matrix resolvent",
  "subtitle": "Critical summation and the algebra behind the expansion",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Counting the first forbidden reversal gives the walk resolvent. Its critical Fourier series requires a summation convention at the bipartite frequency. The conditional matrix reduction retains the correct shifts, signs and connector parameter.",
  "context": [
    "Nearest-neighbour walks on $\\mathbb Z^d$, with $q=2d$ oriented directions.",
    "Fourier transforms use $\\widehat f(k)=\\sum_x f(x)e^{ik\\cdot x}$.",
    "The final matrix identity is conditional on the stated expansion equations; it does not construct their percolation coefficients."
  ],
  "related": [
    "infrared-diagrams",
    "completed-fourier-bootstrap",
    "lace-expansion",
    "bounded-degree-paths"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "non-backtracking Green function",
    "NoBLE matrix equation",
    "bipartite critical Fourier series"
  ],
  "prototypeUses": []
}
---

## Counting the first reversal {#section-counting}

<p>Let $b_n(x)$ count length-$n$ nearest-neighbour paths from $0$ to $x$ with no immediate reversal. Write $D=q^{-1}\mathbf1_{\{|x|_1=1\}}$ and $P=qD$, so $P$ is the adjacency kernel. A path of length zero is allowed.</p>
<a id="tag-0MK8" data-assertion="proposition" data-title="The non-backtracking path recurrence and its absolute convergence domain"></a>
<p>One has</p>
<div class="math-display">$$b_0=\delta_0,\quad b_1=P,\quad b_2=P^{*2}-q\delta_0,\quad
b_n=P*b_{n-1}-(q-1)b_{n-2}\quad(n\ge3).$$</div>
<p>Also $\sum_xb_n(x)=q(q-1)^{n-1}$ for $n\ge1$. Thus $B_z=\sum_{n\ge0}z^nb_n$ converges absolutely in $\ell^1$ when $|z|<(q-1)^{-1}$, with</p>
<div class="math-display">$$\sum_{n,x}|z|^nb_n(x)=\frac{1+|z|}{1-(q-1)|z|}.$$</div>
<p><em>Proof.</em> A first step has $q$ choices and every later step has $q-1$. To obtain the recurrence, prepend one step to a non-backtracking path of length $n-1$. The only new violation is a reversal in the first two steps. For $n\ge3$, after removing this pair, the remaining non-backtracking path has a first direction. There are $q-1$ choices for the removed outgoing step: it must differ from that first direction to keep the original length-$n-1$ suffix non-backtracking. For $n=2$ the remaining path is empty, giving $q$ choices instead. This proves the recurrence and the special second-order term. Sum the path counts geometrically for the norm formula.</p>

## The walk resolvent {#section-resolvent}

<a id="tag-IRTD" data-assertion="theorem" data-title="The non-backtracking resolvent and the directional matrix inverse"></a>
<p>For complex $z$ with $|z|<(q-1)^{-1}$,</p>
<div class="math-display">$$\widehat B_z(k)=\frac{1-z^2}{1+(q-1)z^2-qz\widehat D(k)}.$$</div>
<p>For real $0\le z<(q-1)^{-1}$ this is also the spatial identity</p>
<div class="math-display">$$B_z(x)=a(z)C_{\lambda(z)}(x),\qquad
a(z)=\frac{1-z^2}{1+(q-1)z^2},\quad
\lambda(z)=\frac{qz}{1+(q-1)z^2},$$</div>
<p>where $C_\lambda=\sum_{n\ge0}\lambda^nD^{*n}$ and $0\le\lambda(z)<1$.</p>
<p><em>Proof.</em> Multiply the recurrence in 0MK8 by $z^n$ and sum. Absolute convergence gives</p>
<div class="math-display">$$[\delta_0-zP+(q-1)z^2\delta_0]*B_z=(1-z^2)\delta_0.$$</div>
<p>Fourier transformation gives the quotient. Its denominator cannot vanish in the stated disk, since the transformed convolution identity has nonzero right side $1-z^2$. For real $z$ in the interval,</p>
<div class="math-display">$$1+(q-1)z^2-qz=(1-z)[1-(q-1)z]>0,$$</div>
<p>so $\lambda(z)<1$. The walk Fourier formula and inversion give the spatial identity. For complex $z$, the rational identity remains valid, but no random-walk power series at $\lambda(z)$ is asserted unless that series converges.</p>
<p>The directional formulation yields the same result and fixes the matrix conventions. Index directions by $\iota\in\{\pm1,\ldots,\pm d\}$, put $k_{-\iota}=-k_\iota$, and set</p>
<div class="math-display">$$E(k)_{\iota\kappa}=\mathbf1_{\{\iota=\kappa\}}e^{ik_\iota},\qquad
J_{\iota\kappa}=\mathbf1_{\{\iota=-\kappa\}}.$$</div>
<p>Entrywise multiplication gives $J^2=I$, $E(k)^{-1}=E(-k)$ and $E(k)J=JE(-k)$. Hence</p>
<div class="math-display">$$[E(k)+zJ]^{-1}=\frac{E(-k)-zJ}{1-z^2}.$$</div>
<p>Indeed the product in either order is $(1-z^2)I$ before division. Let $B_z^\iota$ exclude the first step $e_\iota$, while retaining the empty path, and let $v_\iota=\widehat B_z^\iota(k)$. Splitting by the first step gives</p>
<div class="math-display">$$\widehat B_z=1+z\mathbf1^TE(-k)v,\qquad
\widehat B_z\mathbf1=Jv+zE(-k)v.$$</div>
<p>Multiplying the second equation by $J$ and putting $w=E(-k)v$ gives $(E(k)+zJ)w=\widehat B_z\mathbf1$. Substitute into the first equation and use $\mathbf1^TE(-k)\mathbf1=q\widehat D(k)$ and $\mathbf1^TJ\mathbf1=q$. The same quotient follows.</p>

## What converges at criticality {#section-critical}

<a id="tag-NB44" data-assertion="theorem" data-title="Critical non-backtracking transforms have an Abel limit at the bipartite frequency"></a>
<p>Let $d\ge2$, $z_c=(q-1)^{-1}$ and $\alpha=(q-2)/(q-1)$. For every $k\ne0$ on the torus, the radial limit is</p>
<div class="math-display">$$\lim_{z\uparrow z_c}\widehat B_z(k)=\frac\alpha{1-\widehat D(k)}.$$</div>
<p>The ordinary length series $\sum_nz_c^n\widehat b_n(k)$ converges at every frequency other than $0$ and $\boldsymbol\pi=(\pi,\ldots,\pi)$. At both exceptional frequencies its terms fail to tend to zero. In particular its finite radial limit at $\boldsymbol\pi$ is an Abel value, not an ordinary sum.</p>
<p>In space, as nonnegative extended sums, $B_{z_c}(x)=\alpha C_1(x)$. These values are finite exactly when $d>2$. In that case the displayed radial limit is an integrable Fourier density for $B_{z_c}$; its triangle is finite exactly when $d>6$.</p>
<p><em>Proof.</em> Take the radial limit in IRTD. Its denominator tends to a positive multiple of $1-\widehat D(k)$ for $k\ne0$. For the ordinary series, put $t=\widehat D(k)$ and $a_n=z_c^n\widehat b_n(k)$. The recurrence is</p>
<div class="math-display">$$a_n=\frac{qt}{q-1}a_{n-1}-\frac1{q-1}a_{n-2}\quad(n\ge3).$$</div>
<p>If $|t|<1$, both characteristic roots lie strictly inside the unit disk. Nonreal roots have modulus $(q-1)^{-1/2}<1$. For real roots, their product is $1/(q-1)$ and their sum has absolute value less than $1+1/(q-1)$; evaluating the characteristic polynomial at $1$ and $-1$ excludes a root outside the interval $(-1,1)$. Thus $a_n$ is bounded by a polynomial times a geometric sequence, including at a repeated root, and its sum converges. The only frequencies with $t=\pm1$ are $0$ and $\boldsymbol\pi$.</p>
<p>Every nearest-neighbour endpoint has the parity of its path length. The exact path count therefore gives, for $n\ge1$,</p>
<div class="math-display">$$z_c^n\widehat b_n(0)=\frac q{q-1},\qquad
z_c^n\widehat b_n(\boldsymbol\pi)=\frac q{q-1}(-1)^n.$$</div>
<p>Neither sequence tends to zero. The <a href="/errata/heydenreich-hofstad/#nonbacktracking-critical-summation">provisional convergence entry</a> records the needed summation convention.</p>
<p>For the spatial limit, $B_z$ increases termwise with real $z$. Also $\lambda(z)\uparrow1$ and $a(z)\to\alpha>0$, so IRTD and monotone convergence give $B_{z_c}=\alpha C_1$ in the extended sense. <a href="/tag/KCOF/">KCOF</a> gives the finiteness thresholds for the walk Green function and its triangle. When $d>2$, <a href="/tag/TTS1/">TTS1</a> bounds $a(z)\widehat C_{\lambda(z)}$ by $2/(1-\widehat D)$, an integrable function. Dominated convergence in the inverse formula proves the density assertion. It does not assert an absolutely convergent spatial Fourier series at criticality.</p>

## Deleting the previous vertex {#section-deletion}

<a id="tag-WSKG" data-assertion="proposition" data-title="The restricted connection identity depends on the actual deleted set"></a>
<p>Let $u\in A$ and $v,x\notin A$. In one common bond configuration, write $\tau^A(v,x)$ for connection after deleting $A$. Then</p>
<div class="math-display">$$\tau^A(v,x)=\tau^{\{u\}}(v,x)
-\mathbb P\bigl(v\leftrightarrow x\text{ off }u,\ \text{every such open path visits }A\bigr).$$</div>
<p>The same formula holds for each fixed realization of a random set $A$ when the displayed probabilities are evaluated in a separate configuration. An additional independence or conditioning argument is needed before identifying that separate configuration with the one that generated $A$.</p>
<p><em>Proof.</em> Since $u\in A$, the event of connection off $A$ is contained in the event of connection off $u$. Their set difference is exactly the event in the second term. The endpoint restrictions ensure that deletion has the stated meaning, including when $v=x$ and the empty path is present.</p>
<p>If $A$ is the root cluster after closing a proposed cutting bond $(u,v)$, the condition $v\notin A$ holds on the pivotal event. It is not a consequence of the definition of the deleted-bond cluster alone: an alternate open path can still connect its endpoints. The <a href="/errata/heydenreich-hofstad/#nonbacktracking-deleted-set-support">provisional support entry</a> records this distinction in the manuscript's inclusion–exclusion formula.</p>

## Eliminating the directional vector {#section-perturbation}

<p>The following is the algebraic step in a non-backtracking lace equation. Its hypotheses keep separate the probabilistic construction of the coefficients, convergence of their sums, and invertibility of the resulting matrices.</p>
<a id="tag-V49E" data-assertion="proposition" data-title="The conditional matrix lace equation has a minus sign in its correction term"></a>
<p>Fix $k$. Let $t,\xi,\mu\in\mathbb C$, $v,\zeta,r\in\mathbb C^q$, and $P\in\mathbb C^{q\times q}$ satisfy</p>
<div class="math-display">$$t=1+\xi+\mu r^TE(-k)v,\qquad
t\mathbf1=v+\mu E(k)Jv+PE(-k)v+\zeta.$$</div>
<p>Suppose $A=E(k)+\mu J+P$ is invertible. Put</p>
<div class="math-display">$$\Phi=\xi-\mu r^TA^{-1}\zeta,\qquad
s=1-\mu r^TA^{-1}\mathbf1.$$</div>
<p>Then $st=1+\Phi$. If also $s\ne0$,</p>
<div class="math-display">$$t=\frac{1+\xi-\mu r^T[E(k)+\mu J+P]^{-1}\zeta}
{1-\mu r^T[E(k)+\mu J+P]^{-1}\mathbf1}.$$</div>
<p>For example, $|\mu|<1$ and $\|P\|_\infty<1-|\mu|$ ensure matrix invertibility, with</p>
<div class="math-display">$$\|A^{-1}\|_\infty\le\frac1{1-|\mu|-\|P\|_\infty}.$$</div>
<p>They do not by themselves assert that the scalar $s$ is nonzero.</p>
<p><em>Proof.</em> Set $w=E(-k)v$. Since $E(k)JE(k)=J$, the vector equation becomes $Aw=t\mathbf1-\zeta$. Insert $w=A^{-1}(t\mathbf1-\zeta)$ into the scalar equation and collect the terms in $t$. This gives $st=1+\Phi$, including the minus sign. The transpose here is the ordinary transpose, not the conjugate transpose.</p>
<p>For the sufficient norm condition, IRTD gives</p>
<div class="math-display">$$\|[E(k)+\mu J]^{-1}\|_\infty
\le\frac{1+|\mu|}{|1-\mu^2|}\le\frac1{1-|\mu|}.$$</div>
<p>Factor $A$ into $E(k)+\mu J$ times $I+[E(k)+\mu J]^{-1}P$ and sum the convergent Neumann series. This proves the stated inverse bound.</p>
<p>With the Fourier convention fixed above, a spatial term $\tau^{-\iota}(x-e_\iota)$ transforms to $e^{ik_\iota}\widehat\tau^{-\iota}(k)$, explaining $E(k)J$ in the vector equation. A term shifted by $+e_\kappa$ instead gives $E(-k)$. Thus the connector parameter is $\mu$ in both inverses, the scalar feedback term has its factor $\mu$, and $\Phi$ contains a subtraction. The <a href="/errata/heydenreich-hofstad/#nonbacktracking-matrix-algebra">provisional matrix-algebra entry</a> gives the corresponding local corrections.</p>
<p>For a percolation application one must still construct the coefficient arrays, bound their remainders, justify their Fourier transforms and verify both denominator conditions. The <a href="/coverage/sources/heydenreich-hofstad-2017-nonbacktracking/">Chapter 10 map</a> leaves the numerical bootstrap and the claimed dimension threshold with the source; the calculation here does not verify the computer-assisted theorem.</p>
