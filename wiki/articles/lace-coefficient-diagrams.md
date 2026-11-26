---
{
  "id": "lace-coefficient-diagrams",
  "title": "Bounding the lace coefficients",
  "subtitle": "Disjoint witnesses, geometric summation and critical convergence",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Explicit path decompositions give diagram bounds for the lace coefficients. A small weighted triangle makes their norms summable and justifies the critical limit.",
  "context": [
    "Nearest-neighbour bond percolation on $\\mathbb Z^d$, with $p\\le p_c$.",
    "The nonnegative lace coefficients and the cutting event E_A are those of the cutting-bond expansion.",
    "Critical diagram bounds are hypotheses until verified; no infrared estimate is assumed without being stated."
  ],
  "related": [
    "lace-expansion",
    "infrared-diagrams",
    "triangle-susceptibility"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "lace coefficient bounds",
    "weighted triangle",
    "diagrammatic estimates"
  ],
  "prototypeUses": []
}
---

## Disjoint path witnesses {#section-witnesses}

<p>Use the event $E_A(s,x)$ and the deleted-bond cluster from <a href="/tag/F69T/">F69T</a>. A list of pairs below denotes connections with pairwise edge-disjoint open path witnesses. Empty paths are allowed. Paths may meet at vertices.</p>
<a id="tag-NCYU" data-assertion="proposition" data-title="Path witnesses for terminal and intermediate cutting events"></a>
<p>Assume clusters are finite almost surely. If $E_A(v,u)$ occurs, there are $z\in A$ and $t$ with disjoint witnesses for</p>
<div class="math-display">$$(v,t),\ (t,z),\ (t,u),\ (z,u).$$</div>
<p>If also $v\leftrightarrow y$, there are $z\in A$ and $t,w$ for which one of the following two lists has disjoint witnesses:</p>
<div class="math-display">$$\begin{aligned}
&(v,t),\ (t,z),\ (t,w),\ (z,u),\ (w,u),\ (w,y);\\
&(v,w),\ (w,t),\ (t,z),\ (t,u),\ (z,u),\ (w,y).
\end{aligned}$$</div>
<p>Finally, double connection $s\Leftrightarrow u$ together with $s\leftrightarrow y$ gives, for some $w$, disjoint witnesses for $(s,u),(s,w),(w,u),(w,y)$.</p>
<p><em>Proof.</em> Suppose first that $v\ne u$. If there is a pivotal bond for their connection, take the last one in the bridge order, and let $t$ be its head. Its tail is not connected to $v$ through $A$, by the definition of $E_A$. There is therefore a path from $v$ to that tail avoiding $A$. Append the pivotal bond to obtain a simple prefix from $v$ to $t$ that avoids $A$ except possibly at $t$.</p>
<p>No bond is pivotal between $t$ and $u$ in the component beyond this last bridge. The finite cut alternative gives two edge-disjoint paths $P,Q$ from $t$ to $u$, disjoint from the prefix. If there is no pivotal bond at all, use $t=v$ and an empty prefix. Each of $P,Q$ meets $A$: otherwise that path and the prefix would give an $A$-avoiding connection from $v$ to $u$, unless $t\in A$, in which case the assertion already holds. Choose $z\in A$ on one path, split it at $z$, and leave the other path intact. This proves the first list.</p>
<p>For the extra connection, take a path from $y$ to the union of the prefix, $P$ and $Q$, and stop at its first contact $w$. Its remaining segment has no edge in that union. If $w$ is on the prefix, split the prefix at $w$ and choose $z$ on either of the two terminal paths; this gives the second list. If $w$ is on a terminal path, choose $z\in A$ on the other path and split the first at $w$; this gives the first list. A shared vertex of $P,Q$ causes no problem, since their edges are disjoint. When $v=u$, the event requires $v\in A$; take $t=z=v$, using empty paths and the extra connection.</p>
<p>For the final assertion, start with two edge-disjoint $s$–$u$ paths and attach a path from $y$ at its first contact $w$ with their union. Split the path containing $w$ and leave the other intact. If $s=u$, use empty paths and the connection to $y$.</p>
<p>In a lace coefficient, membership of $y$ in a deleted-bond cluster implies the extra root connection used above. Dropping that deletion restriction only enlarges the event. These constructions justify BK within each configuration; independence is used only between the distinct configurations in the coefficient formula.</p>

## A summable bound at every order {#section-mass}

<p>Write $J(x)=p\mathbf1_{\{|x|_1=1\}}$, $j=2dp$, and $\widetilde\tau=J*\tau$. Define</p>
<div class="math-display">$$\Delta=\sup_x\tau^{*3}(x)=\tau^{*3}(0),\qquad
T=\sup_x(\tau*\tau*\widetilde\tau)(x).$$</div>
<p>The equality for $\Delta$ follows from <a href="/tag/ANZF/">Fourier positivity and its spatial critical limit</a>. The coefficient definitions are nonnegative sums, so they make sense before finiteness is established.</p>
<a id="tag-SJIL" data-assertion="theorem" data-title="Geometric mass bounds for all nonnegative lace coefficients"></a>
<p>Assume clusters are finite almost surely and $\Delta,T<\infty$. Then</p>
<div class="math-display">$$\|\Pi^{(0)}\|_1\le T,\qquad
\|\Pi^{(1)}\|_1\le T\Delta^2,\qquad
\|\Pi^{(N)}\|_1\le\Delta(2T\Delta)^N\quad(N\ge1).$$</div>
<p><em>Proof.</em> For $x\ne0$, the first open edge of a simple connection path and its remaining segment are disjoint witnesses. BK gives $\tau(x)\le(J*\tau)(x)=\widetilde\tau(x)$. Double connection gives $\Pi^{(0)}(x)\le\tau(x)^2$ off zero, while $\Pi^{(0)}(0)=0$. Hence</p>
<div class="math-display">$$\sum_x\Pi^{(0)}(x)\le\sum_x\tau(x)\widetilde\tau(x)\le T.$$</div>
<p>The last inequality uses $\tau\ge\delta_0$ to insert one more convolution factor.</p>
<p>For the first coefficient, apply NCYU to the outer double connection and the inner cutting event. Take the union over the marked vertices, use independence of the two configurations, and then BK in each. This gives $\Pi^{(1)}(x)\le D_1(x)$, where</p>
<div class="math-display">$$D_1(x)=\sum_{u,w,z,t}
\tau(u)\tau(w)\tau(u-w)\tau(z-w)\widetilde\tau(t-u)
\tau(z-t)\tau(x-t)\tau(x-z).$$</div>
<p>In the sum over $x$, put $t'=t-z$ and $x'=x-z$. Summing $z$ gives the connector $(\tau*\widetilde\tau)(t'+w-u)\le T$. The remaining sums over $(u,w)$ and $(t',x')$ are each $\Delta$. Thus $\sum_xD_1(x)\le T\Delta^2$.</p>
<p>For the higher orders, introduce the nonnegative kernels</p>
<div class="math-display">$$\begin{aligned}
A(s,u,v)&=\tau(v-s)\tau(u-s)\tau(v-u),\\
B_1(s,t,u,v)&=\widetilde\tau(v-t)\tau(u-s),\\
B_2(u,v,s,t)&=\tau(v-u)\tau(t-u)\tau(s-v)\tau(t-s)\\
&\quad+\mathbf1_{\{v=s\}}\sum_a\tau(a-s)\tau(u-a)\tau(t-a)\tau(t-u).
\end{aligned}$$</div>
<p>The terminal witness list in NCYU gives $A$; its two intermediate lists give the two terms of $B_2$. More precisely, summing the entering bond probability against its first path replaces $J*\tau$ by $\widetilde\tau$. In the first intermediate list the vertex $t$ is retained. In the second, the attaching vertex $w$ becomes the new $t$, while the old $t$ is summed as $a$ in the second term of $B_2$. The remaining path to the next marked vertex supplies the $\tau$ factor in the next $B_1$.</p>
<p>Expanding the nested expectations on independent configurations, applying these witness inclusions backwards from the last configuration, and using BK therefore gives</p>
<div class="math-display">$$\Pi^{(N)}(x)\le
\sum A(0,u_0,w_0)
\prod_{i=1}^{N-1}\!\left[B_1(w_{i-1},u_{i-1},z_i,t_i)B_2(z_i,t_i,w_i,u_i)\right]
B_1(w_{N-1},u_{N-1},z_N,t_N)A(z_N,t_N,x).$$</div>
<p>The sum runs over $u_0,\ldots,u_{N-1}$, $w_0,\ldots,w_{N-1}$, $z_1,\ldots,z_N$ and $t_1,\ldots,t_N$. Each expanded event belongs to its own independent configuration; no factorization of an original cutting event and a cluster-membership event is used. All rearrangements are Tonelli rearrangements. This derivation uses no ratios of connection probabilities, so it also covers $p=0$. At $N=1$ it is exactly $D_1$.</p>
<p>Regard $B_1B_2$ as a transition between pairs of vertices. For every initial pair $(w_0,u_0)$, its total mass is at most $2T\Delta$:</p>
<div class="math-display">$$\sum_{z,t,w,u}B_1(w_0,u_0,z,t)B_2(z,t,w,u)\le2T\Delta.$$</div>
<p>For the first term of $B_2$, the inner sum over $w,u$ is $\tau^{*3}(t-z)\le\Delta$. The remaining sum is</p>
<div class="math-display">$$\sum_{z,t}\widetilde\tau(t-u_0)\tau(z-w_0)\tau(t-z)\le T.$$</div>
<p>For the second term, use $w=t$ and sum $t$ first. The expression becomes</p>
<div class="math-display">$$\sum_{a,z,u}(\widetilde\tau*\tau)(a-u_0)\tau(z-w_0)
\tau(u-z)\tau(z-a)\tau(u-a).$$</div>
<p>Put $a'=a-z$, $u'=u-z$. The sum over $z$ is at most $T$, and the remaining triangle sum over $a',u'$ is $\Delta$. This proves the transition bound.</p>
<p>Finally, $\sum_{u_0,w_0}A(0,u_0,w_0)=\Delta$, and</p>
<div class="math-display">$$\sum_xA(z,t,x)\le\sum_{w,u}B_2(z,t,w,u),$$</div>
<p>because the terms $w=u=x$ in the first part of $B_2$ already give the left side. Replace the terminal factor by this sum and apply the transition bound $N$ times. The result is $\Delta(2T\Delta)^N$.</p>

## The first weighted estimate {#section-weighted}

<p>For a fixed frequency $k$, put $h(x)=1-\cos(k\cdot x)$ and</p>
<div class="math-display">$$W(y;k)=\sum_xh(x)\widetilde\tau(x)\tau(x+y),\qquad W(k)=\sup_yW(y;k).$$</div>
<a id="tag-NJT0" data-assertion="proposition" data-title="Weighted bounds for the zeroth and first lace coefficients"></a>
<p>Under the preceding hypotheses, for every $k$ with $W(k)<\infty$,</p>
<div class="math-display">$$\sum_xh(x)\Pi^{(0)}(x)\le W(0;k),\qquad
\sum_xh(x)\Pi^{(1)}(x)\le3\Delta^2W(k)+6T\Delta W(k).$$</div>
<p><em>Proof.</em> The first bound follows from the pointwise estimate for $\Pi^{(0)}$ above. For the second, use</p>
<div class="math-display">$$h(x)\le3\bigl[h(u)+h(t-u)+h(x-t)\bigr]$$</div>
<p>in $D_1$. More generally $1-\cos(\sum_{i=1}^m s_i)\le m\sum_i(1-\cos s_i)$: telescope $1-e^{i\sum s_i}$, apply Cauchy–Schwarz, and use $|1-e^{is}|^2=2(1-\cos s)$.</p>
<p>The middle weight $h(t-u)$ stays in the connector sum over $z$. In the variables $t'=t-z$, it bounds that sum by $W(k)$ instead of $T$, leaving the two triangle sums. Its contribution before the factor three is at most $W(k)\Delta^2$.</p>
<p>For $h(u)$, shift $w,z,t,x$ by $-u$. The only factors still involving $u$ are $h(u)\tau(u)\tau(u+w')$. Since $h(0)=0$ and $\tau(u)\le\widetilde\tau(u)$ off zero, their sum is at most $W(k)$. The remaining expression is</p>
<div class="math-display">$$\sum_{w',z',t',x'}\tau(w')\tau(z'-w')\widetilde\tau(t')
\tau(z'-t')\tau(x'-t')\tau(x'-z').$$</div>
<p>Sum $w'$, then put $z''=z'-t'$ and $x''=x'-t'$. The sum over $t'$ is $(\tau*\tau*\widetilde\tau)(z'')\le T$, and the remaining sum is $\Delta$. Thus this contribution is at most $W(k)T\Delta$.</p>
<p>The substitution</p>
<div class="math-display">$$(u,w,z,t,x)\longmapsto(x-t,\ x-z,\ x-w,\ x-u,\ x)$$</div>
<p>preserves the diagram and sends $h(x-t)$ to the first weight. It has the same bound. Including the three factors from the cosine inequality proves the claim. At $p=0$ every term is zero.</p>
<p>The sharper first-order weighted estimate and the general weighted coefficient bound require further estimates. They are not consequences of the geometric mass bound alone.</p>

## A concrete convergence criterion at criticality {#section-critical-convergence}

<a id="tag-3W22" data-assertion="theorem" data-title="Small critical weighted triangle gives summable lace coefficients and the critical equation"></a>
<p>Let $d\ge2$ and suppose</p>
<div class="math-display">$$\Delta_c<\infty,\qquad T_c<\infty,\qquad r=2T_c\Delta_c<1.$$</div>
<p>Then the lace coefficients at every $p\le p_c$ have an absolutely summable signed sum $\Pi_p=\sum_{n\ge0}(-1)^n\Pi_p^{(n)}$, with</p>
<div class="math-display">$$\|\Pi_p\|_1\le T_c+\frac{\Delta_c r}{1-r},\qquad
\|\Pi_p-\Pi_{p_c}\|_1\longrightarrow0\quad(p\uparrow p_c).$$</div>
<p>The full spatial lace expansion holds through criticality and</p>
<div class="math-display">$$2dp_c\bigl(1+\widehat\Pi_{p_c}(0)\bigr)=1.$$</div>
<p><em>Proof.</em> Finite $\Delta_c$ gives $\theta(p_c)=0$ by <a href="/tag/5W46/">5W46</a>. By transitivity and countability, all clusters are finite almost surely at every $p\le p_c$. The connection kernels and their nonnegative diagrams increase with $p$, so SJIL gives the uniform bounds</p>
<div class="math-display">$$\|\Pi_p^{(0)}\|_1\le T_c,\qquad
\|\Pi_p^{(n)}\|_1\le\Delta_c r^n\quad(n\ge1).$$</div>
<p>These prove absolute summability and the stated norm bound. At $p_c$, the finite-expansion extension in <a href="/tag/Z84R/">Z84R</a> applies at every order; its uniform remainder bound tends to zero. This already proves the critical spatial identity. Below criticality, sharpness gives finite susceptibility and <a href="/tag/I3PK/">I3PK</a> gives the full identity in the summable norm.</p>
<p>We still need continuity of the coefficients; the cutting events are not monotone. Couple each independent configuration by uniform edge variables. Fix a coefficient order, its finite tuple of oriented bonds, and its target. Almost surely, the finitely many critical clusters relevant to this tuple are finite. They have finitely many incident edges, none with uniform variable exactly $p_c$. For all $p$ sufficiently close to $p_c$, their internal configurations, their deleted-bond clusters and hence the cutting events coincide with their critical versions. This holds successively through the finitely many independent layers, including the random sets passed between them. Bounded convergence gives convergence of the probability attached to the fixed tuple.</p>
<p>For each such tuple and target, the expanded witness diagram at $p_c$, including the bond weight $p_c^n$, bounds the corresponding summand at every smaller parameter. Its sum over all bond tuples, targets and auxiliary witness vertices is finite by the transition estimate in SJIL. It therefore supplies a summable envelope for countable dominated convergence, proving $\|\Pi_p^{(n)}-\Pi_{p_c}^{(n)}\|_1\to0$ for each $n\ge1$. For $n=0$, double connection has finite path witnesses and is dominated off zero by $\tau_{p_c}^2$, whose sum is finite since the triangle contains the bubble. The same conclusion holds.</p>
<p>The geometric bound controls the remaining sum over orders uniformly, giving convergence of $\Pi_p$ in $\ell^1$. Critical susceptibility diverges by <a href="/tag/JQLC/">JQLC</a>. All hypotheses of the critical part of I3PK are now supplied, so it gives the displayed critical equation. This reasoning does not presume monotonicity of the individual lace coefficients.</p>

## Small weighted triangles from a conditional infrared estimate {#section-infrared-smallness}

<a id="tag-AA7H" data-assertion="proposition" data-title="An infrared estimate and a bounded edge mass make the weighted triangle small"></a>
<p>Suppose, over a family of nearest-neighbour models of dimensions $d>6$, that $2dp_c\le B$ and</p>
<div class="math-display">$$\widehat\tau_p(k)\le\frac A{1-\widehat D(k)}\qquad(p<p_c)$$</div>
<p>with fixed finite constants $A,B$. Then $\Delta_c\le C(A)$ and $T_c\le C(A,B)/d$. Consequently $2T_c\Delta_c<1$ in sufficiently large dimensions, and 3W22 applies.</p>
<p><em>Proof.</em> Below criticality, $\tau\le\delta_0+J*\tau$ by the first-step bound, including at zero. Repeatedly apply it to one convolution factor to get the pointwise estimate</p>
<div class="math-display">$$J*\tau^{*3}\le
J+J^{*2}*\tau+J^{*2}*\tau^{*2}+J^{*2}*\tau^{*3}.$$</div>
<p>The left side defines $T$ after taking the supremum. The first term has supremum $p\le B/(2d)$. For $s=1,2,3$, the Fourier transform of $J^{*2}*\tau^{*s}$ is the nonnegative function $j^2\widehat D^{\,2}\widehat\tau^{\,s}$. Its maximum spatial coefficient is therefore at zero and at most</p>
<div class="math-display">$$j^2A^s\int\frac{\widehat D(k)^2}{(1-\widehat D(k))^s}\,\frac{dk}{(2\pi)^d}
\le\frac{B^2A^sK_{1,s}}d$$</div>
<p>by <a href="/tag/RD3X/">RD3X</a>. This proves the uniform bound on $T_p$. The bound on $\Delta_p$ is <a href="/tag/ANZF/">ANZF</a>. Monotone convergence of the spatial sums, followed by the supremum over endpoints, passes both bounds to $p_c$. Their product tends to zero with $d$.</p>
<p>The infrared bound and the bound on $2dp_c$ remain premises. This supplies a consequence needed by the bootstrap; it does not prove those premises or resolve the apparent circularity by itself. The <a href="/coverage/sources/heydenreich-hofstad-2017-diagrams/">Chapter 7 map</a> keeps the remaining weighted estimates and the subsequent bootstrap separate. No new erratum or compiled association is asserted.</p>
