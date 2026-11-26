---
{
  "id": "two-mark-first-coefficients",
  "title": "Two weights on the first lace diagram",
  "subtitle": "Fourth moments without a spatial decay hypothesis",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Two disjoint routes through the first lace diagram let each Fourier derivative carry only half the desired moment. Nine marked sums reduce to weighted bubbles and triangles, giving fourth moments and weighted critical continuity for the first two coefficients.",
  "context": [
    "Nearest-neighbour Bernoulli bond percolation on $\\mathbb Z^d$.",
    "The diagram estimate is stated first for an arbitrary nonnegative even kernel.",
    "The conclusion concerns orders zero and one. Summability over all lace orders requires a further argument."
  ],
  "related": [
    "fourier-spatial-moment-bridge",
    "higher-lace-moments",
    "spatial-lace-coefficient-bounds",
    "lace-coefficient-diagrams"
  ],
  "sourceIds": [
    "hara-nearest-neighbour-2008",
    "heydenreich-hofstad"
  ],
  "aliases": [
    "two marked routes",
    "fourth lace moments",
    "first coefficient moment doubling"
  ],
  "prototypeUses": []
}
---

## The nine marked sums {#section-diagram}

<p>Let $f:\mathbb Z^d\to[0,\infty)$ be even. For $a>0$ put $f_a(x)=|x|^a f(x)$, and put $f_0=f$. All convolutions below are nonnegative sums. Write</p>
<div class="math-display">$$\Delta=\|f*f*f\|_\infty,\qquad W_{a,b}=\|f_a*f_b\|_\infty,\qquad T_a=\|f_a*f*f\|_\infty.$$</div>
<p>Consider the eight-edge diagram</p>
<div class="math-display">$$D_f(x)=\sum_{u,w,z,t}f(u)f(w)f(u-w)f(z-w)f(t-u)f(z-t)f(x-t)f(x-z).$$</div>
<p>Its two routes $0,w,z,x$ and $0,u,t,x$ have displacements</p>
<div class="math-display">$$(a_1,a_2,a_3)=(w,z-w,x-z),\qquad (b_1,b_2,b_3)=(u,t-u,x-t).$$</div>

<a id="tag-5EWK" data-assertion="proposition" data-title="Two marked routes bound a higher moment of the first lace diagram"></a>
<p>Let $\beta,\gamma>0$ and suppose $\Delta,W_{\beta,0},W_{\gamma,0},W_{\beta,\gamma},T_\beta,T_\gamma$ are finite. Set $a(s)=\max\{s-1,0\}$. Then</p>
<div class="math-display">$$\sum_x|x|^{\beta+\gamma}D_f(x)
\le3^{a(\beta)+a(\gamma)}\left[3\Delta^2W_{\beta,\gamma}
+6\Delta\max\{W_{\beta,0}T_\gamma,W_{\gamma,0}T_\beta\}\right].$$</div>
<p>In particular, for $\beta=\gamma=2$, the right-hand side is $27\Delta^2W_{2,2}+54\Delta W_{2,0}T_2$.</p>
<p><em>Proof.</em> Apply the triangle inequality and Hölder separately on the two routes:</p>
<div class="math-display">$$|x|^{\beta+\gamma}\le
3^{a(\beta)+a(\gamma)}\sum_{i,j=1}^3|a_i|^\beta|b_j|^\gamma.$$</div>
<p>Let $I_{ij}$ be the total diagram sum, including the sum over $x$, with the indicated two weights. There are only four calculations. Interchanging the routes transposes $i,j$ and exchanges $\beta,\gamma$; reversing both routes changes $(i,j)$ to $(4-i,4-j)$. These are changes of summation variables, using evenness of $f$.</p>
<p>Put $P=f*f$, $C(v)=f(v)P(v)$ and $B_s=f_s*f$. Thus $\sum C=f^{*3}(0)\le\Delta$ and $\sum_v f(v)B_s(v)=(f_s*f*f)(0)\le T_s$.</p>
<table>
<thead><tr><th>Positions</th><th>Representative bound</th></tr></thead>
<tbody>
<tr><td>$(1,1),(3,3)$</td><td>$I_{11}\le W_{\beta,\gamma}\Delta^2$</td></tr>
<tr><td>$(2,2)$</td><td>$I_{22}\le W_{\beta,\gamma}\Delta^2$</td></tr>
<tr><td>$(1,2),(2,1),(2,3),(3,2)$</td><td>$I_{12}\le W_{\beta,0}T_\gamma\Delta$, with the weights exchanged when required</td></tr>
<tr><td>$(1,3),(3,1)$</td><td>$I_{13}\le W_{\beta,0}T_\gamma\Delta$, with the weights exchanged when required</td></tr>
</tbody>
</table>
<p>For the first row take $v=u-w$, $a=z-w$, $b=t-u$, and sum over $x$ and then $w$. This gives</p>
<div class="math-display">$$I_{11}=\sum_{v,a,b}(f_\beta*f_\gamma)(v)f(v)f(a)f(b)C(a-v-b)
\le W_{\beta,\gamma}\sum_h f^{*3}(h)C(h)\le W_{\beta,\gamma}\Delta^2.$$</div>
<p>For the second row, sum the common translate of the initial vertices and the terminal vertex. With $v=u-w$ and $r=z-t$, the remaining expression is</p>
<div class="math-display">$$I_{22}=\sum_{v,r}C(v)C(r)(f_\beta*f_\gamma)(r+v)
\le W_{\beta,\gamma}\Delta^2.$$</div>
<p>For adjacent positions, the same variables as in the first calculation give</p>
<div class="math-display">$$I_{12}=\sum_{v,a,b}B_\beta(v)f(v)f(a)f_\gamma(b)C(a-v-b).
$$</div>
<p>Bound $B_\beta$ by $W_{\beta,0}$. For fixed $h=a-v-b$, the other three factors sum to $(f*f*f_\gamma)(h)\le T_\gamma$. Summing $C(h)$ proves the third row.</p>
<p>For separated positions, integrate the initial and terminal translates before the two connectors. The result is</p>
<div class="math-display">$$I_{13}=\sum_{v,r}B_\beta(v)f(v)B_\gamma(r)f(r)P(r+v).
$$</div>
<p>Bound $B_\beta$ by $W_{\beta,0}$ and sum over $v$: $(f*P)(r)\le\Delta$. The remaining sum is at most $T_\gamma$, proving the last row. Summing the three diagonal and six off-diagonal bounds proves the assertion. All identities are Tonelli rearrangements; their finite upper bounds establish convergence rather than presupposing it.</p>

## Critical moments of the first two coefficients {#section-critical}

<p>Use the nonnegative lace coefficients of <a href="/tag/SJIL/">SJIL</a>. At criticality write $b=\delta_0+\Pi_{p_c}$ and $Q=j_cD*b$, where $j_c=2dp_c$ and $D$ is the uniform nearest-neighbour step distribution.</p>
<a id="tag-0TO3" data-assertion="theorem" data-title="Critical coefficient moments of even order M give moments of order 2M for the first two lace coefficients"></a>
<p>Let $M\ge2$ be an even integer and $d>2M+4$. Suppose critical clusters are finite almost surely, $b,Q$ are real even kernels with finite absolute $M$th moments, $\sum Q=1$, and</p>
<div class="math-display">$$1-\widehat Q(k)\ge c|k|^2,\qquad
\tau_{p_c}(x)=\int e^{-ik\cdot x}\frac{\widehat b(k)}{1-\widehat Q(k)}\,dk$$</div>
<p>for some $c>0$, with normalized Haar measure. For $n=0,1$,</p>
<div class="math-display">$$\sup_{0\le p\le p_c}\sum_x(1+|x|^{2M})\Pi_p^{(n)}(x)<\infty,\qquad
\sum_x(1+|x|^{2M})|\Pi_p^{(n)}(x)-\Pi_{p_c}^{(n)}(x)|\longrightarrow0
\quad(p\uparrow p_c).$$</div>
<p>In particular, the completed sufficiently-high-dimensional Fourier bootstrap supplies these conclusions with $M=2$: the first two coefficients have uniformly finite fourth moments and are continuous at criticality in the fourth-weighted norm.</p>
<p><em>Proof.</em> Put $\tau=\tau_{p_c}$, $\widetilde\tau=j_cD*\tau$ and $f=\tau+\widetilde\tau$. The finite convolution of the critical inverse integral shows that $f$ is the inverse transform of</p>
<div class="math-display">$$\frac{(1+j_c\widehat D)\widehat b}{1-\widehat Q}.$$</div>
<p>The new numerator kernel $(\delta_0+j_cD)*b$ retains its absolute $M$th moment, because $D$ has finite support. Also $f$ is nonnegative and even. <a href="/tag/BNKQ/">BNKQ</a> therefore gives finite bounds for</p>
<div class="math-display">$$\Delta,\quad W_{M,0},\quad W_{M,M},\quad T_M.$$</div>
<p>The respective Fourier powers are $6$, $4+M$, $4+2M$ and $6+M$. All are strictly less than $d$, since $M\ge2$ and $d>2M+4$. This is the only dimension restriction in the diagram calculation; the separate assumptions supplying the critical quotient have not been removed.</p>
<p>Double connection gives $\Pi_{p_c}^{(0)}(x)\le\tau(x)^2$ off zero, with $\Pi_{p_c}^{(0)}(0)=0$. Its $2M$-moment is at most $(f_M*f_M)(0)$. The pointwise first-coefficient diagram in SJIL has seven $\tau$ factors and one $\widetilde\tau$ factor, hence is bounded by $D_f$. Apply 5EWK with $\beta=\gamma=M$ to obtain its $2M$-moment. Its unweighted mass is also finite: the same first-coefficient summation gives $\sum_xD_f(x)\le\|f*f\|_\infty\Delta^2$, and $\|f*f\|_\infty<\infty$ by BNKQ. Every lower-parameter witness diagram is bounded by this critical diagram, so the bounds are uniform in $p\le p_c$.</p>
<p>For continuity at order one, fix a bond tuple and target in the independent-configuration expansion. In the uniform-edge coupling, its finitely many relevant critical clusters are finite almost surely. Their incident edge sets are finite, and no edge variable equals $p_c$. Thus their configurations, deleted clusters and cutting events stabilize as $p\uparrow p_c$, exactly as in <a href="/tag/3W22/">3W22</a>. Each tuple probability converges. The critical witness diagram, multiplied by $1+|x|^{2M}$ and before summing its auxiliary vertices, is a summable envelope by the bounds just proved. Dominated convergence over tuples and targets gives convergence in the displayed norm. At order zero use the finite witnesses for double connection and the envelope $(1+|x|^{2M})\tau(x)^2$ off zero. Coefficient monotonicity is not needed.</p>
<p>Finally <a href="/tag/F7N7/">F7N7</a> supplies the critical representation, almost-sure cluster finiteness, positive gap and absolute second moments in sufficiently large dimension. Taking $M=2$ proves the stated fourth-moment conclusion.</p>

## What remains at higher orders {#section-higher-orders}

<p>The Fourier estimates also control the one-mark core needed at higher orders. With $T,\widetilde\tau,H_2$ as in <a href="/tag/1VDI/">1VDI</a>, its bound reads</p>
<div class="math-display">$$H_2\le T^2\sum_q |q|^2\tau(q)\tau^{*2}(q)
=T^2(\tau_2*\tau*\tau)(0)<\infty.$$</div>
<p>The last finiteness follows from BNKQ with weights $(2,0,0)$ and $d>8$. Thus the local weighted bubble, weighted triangle and one-mark core are available without a spatial decay hypothesis. What is still needed is a uniform estimate for two marks at arbitrary positions in the full chain, retaining a summable factor in the lace order. Finiteness for orders zero and one does not supply that factor.</p>
<p>Hara's Section 3.4 uses two marked routes for this all-order step. The calculation above supplies the low-order cases explicitly from our eight-edge kernel; it does not claim that the general reduction, the separated-long-segment estimate, or the full $|x|^{2-d}$ spatial asymptotic has been completed. No new source erratum, numerical dimension threshold or Lean proof is asserted.</p>

## Subsequent all-order moment estimate {#section-planar-followup}

<p>The all-order moment step described above is now supplied, in sufficiently large dimension, by <a href="/tag/KOTM/">the planar Fourier estimate</a>. It handles arbitrary positions of two marks and preserves summable decay in the lace order. <a href="/tag/GIN9/">Its application</a> gives higher moments and weighted critical continuity of the entire series without a spatial hypothesis. The sharper dimension range, the separated-long-segment estimate and the full spatial asymptotic remain separate.</p>
