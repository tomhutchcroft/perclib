---
{
  "id": "sharp-upper-field",
  "title": "Sharp upper field bounds",
  "subtitle": "A root-mark correction and the supercritical tail constant",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Separating a marked root from two distinct marked arms repairs the cutting argument. A sharp square-root bound and exact inverse-field transport give the matching leading supercritical tail constant.",
  "context": [
    "Finite connected simple vertex-transitive graphs with independent bonds and independent vertex marks.",
    "The asymptotic result assumes a strong subcritical triangle estimate, growing degree and an explicit finite critical reference point.",
    "The finite coefficient is corrected; the later characteristic argument also supplies a polynomial lower-tail remainder."
  ],
  "related": [
    "sharp-supercritical-field",
    "finite-magnetization-deletion",
    "finite-triangle-window",
    "hypercube-critical-parameter"
  ],
  "sourceIds": [
    "hofstad-nachmias-hypercube",
    "borgs-chayes-finite-window"
  ],
  "aliases": [
    "root mark cutting inequality",
    "sharp magnetization upper bound",
    "supercritical tail constant two",
    "inverse field transport"
  ],
  "prototypeUses": []
}
---

## Keeping the root mark separate {#section-event}

<p>Let $G$ be a finite connected simple vertex-transitive graph, with $N$ vertices and degree $m\ge1$. Bonds open with probability $p<1$, and vertices are marked with probability $\gamma$, independently. Write</p>
<div class="math-display">$$q=1-\gamma,\quad r=mp,\quad T(x,y)=\mathbb P_p(x\leftrightarrow y),\quad M=\mathbb P_{p,\gamma}(o\leftrightarrow\mathcal G),\quad \chi_\gamma=qM_\gamma,$$</div>
<div class="math-display">$$\eta=\max_{x,y}\{T^3(x,y)-\mathbf1_{\{x=y\}}\},\qquad b=(1-\eta)_+^2-\eta.$$</div>
<p>Matrix powers sum over the vertex set. Let $D_v$ be the event that two edge-disjoint paths join $v$ to distinct marked vertices, with the terminal marks included in their witnesses. Define the different event</p>
<div class="math-display">$$J_v=\{v\in\mathcal G\}\cup D_v.$$</div>
<p>A marked root alone belongs to $J_v$, but not necessarily to $D_v$. This distinction is the source of the <a href="/errata/hofstad-nachmias-hypercube/#double-mark-root-event">provisional correction</a>. We retain $D_v$ unchanged and prove the cutting inequality for $J_v$ afresh.</p>

<a id="tag-23RW" data-assertion="proposition" data-title="A Bonferroni lower bound for the root-mark or double-connection event"></a>
<p>For $0\le\gamma\le1$, put</p>
<div class="math-display">$$L=\frac{m(m-1)p^2}{2}b-\frac{r^3}{2}(M+\eta)-\frac{r^4}{8}(M^2+4\eta).$$</div>
<p>Then</p>
<div class="math-display">$$\mathbb P(J_o)\ge\gamma+qM^2L.$$</div>
<p><em>Proof.</em> Delete $o$ and all its incident bonds. For distinct neighbours $e,f$, let $E_{e,f}$ require the two root bonds to be open and the clusters of $e,f$ in the deleted graph to be distinct and marked. These events are independent of the mark at $o$. Their union implies $D_o$ when $o$ is unmarked, and the two-cluster estimate <a href="/tag/CHWM/">CHWM</a> gives $\mathbb P(E_{e,f})\ge p^2M^2b$.</p>
<p>In an intersection $E_{e,f}\cap E_{e,g}$ with three distinct neighbours, either all three deleted clusters are distinct, or the clusters of $f,g$ coincide. The first case has probability at most $p^3M^3$. In the second, a tree joining $f,g$ and a mark has a branch vertex $w$, while the marked cluster of $e$ is separate. BK, including the two distinct terminal marks, bounds its probability by</p>
<div class="math-display">$$p^3M^2\sum_wT(f,w)T(w,g)=p^3M^2T^2(f,g)\le p^3M^2\eta.$$</div>
<p>Here $T^2(f,g)\le T^3(f,g)$, since $T(w,w)=1$, and $f\ne g$. There are $3\binom m3$ unordered pairs of neighbour pairs of this type.</p>
<p>For four distinct neighbours in $E_{e,f}\cap E_{g,h}$, four distinct deleted clusters cost at most $p^4M^4$. Otherwise one of the four cross pairs $(e,g),(e,h),(f,g),(f,h)$ lies in a common cluster. Join that pair to a mark by a tree and use a mark in its original partner's separate cluster. The same branch-vertex bound costs at most $p^4M^2\eta$ for each choice. There are $3\binom m4$ unordered pairs of pairs. Bonferroni therefore subtracts at most</p>
<div class="math-display">$$3\binom m3p^3M^2(M+\eta)+3\binom m4p^4M^2(M^2+4\eta)\le M^2\left[\frac{r^3}{2}(M+\eta)+\frac{r^4}{8}(M^2+4\eta)\right].$$</div>
<p>Sum the single-event lower bounds, multiply the union bound by $q$, and add the independent root-mark probability $\gamma$. The argument permits a negative $L$.</p>

## Cutting with the enlarged event {#section-cutting}

<a id="tag-RX78" data-assertion="theorem" data-title="A finite cutting inequality that includes the root mark and its deletion loss"></a>
<p>For $0\le p<1$ and $0\le\gamma\le1$,</p>
<div class="math-display">$$M\ge rqM_\gamma\left[(1-\eta)\gamma+(qL-p-\eta)M^2\right].$$</div>
<p><em>Proof.</em> The endpoints $p=0$ and $\gamma\in\{0,1\}$ are immediate. For an oriented edge $(u,v)$, close its bond, let $A$ be the resulting cluster of $v$, and let $J^-_v$ be $J_v$ in this configuration. Let $F_{u,v}$ require the bond to be open and pivotal for $o\leftrightarrow\mathcal G$, with $o$ on the $u$ side, and require $J^-_v$.</p>
<p>At most one $F_{u,v}$ can occur. Pivotal bonds have the same order on every path from $o$ to a mark; beyond a bond satisfying $J^-_v$, no later ordinary bond is pivotal. This follows either from the mark at $v$ itself or from the two disjoint marked arms. Thus $M\ge\sum_{(u,v)}\mathbb P(F_{u,v})$.</p>
<p>Write $\tau_\gamma(x,y)=\mathbb P(x\leftrightarrow y,x\not\leftrightarrow\mathcal G)$ and use a superscript $A$ for deletion of $A$. Conditional on $A$, its internal bonds and marks are disjoint coordinates from the outside green-free connection. As in <a href="/tag/60X1/">60X1</a>, this gives</p>
<div class="math-display">$$\mathbb P(F_{u,v})=p\,\mathbb E[\tau_\gamma^A(o,u)\mathbf1_{J^-_v}].$$</div>
<p>Add and subtract the unrestricted two-point function and event. Their sum is $X_1-X_2-X_3$, where</p>
<div class="math-display">$$X_1=r\chi_\gamma\mathbb P(J_o),\qquad X_2=p\sum_{(u,v)}\tau_\gamma(o,u)\mathbb P(J_v\setminus J^-_v).$$</div>
<p>Closing a bond cannot remove a root mark. If it destroys $J_v$, it destroys two distinct marked arms, supplying disjoint witnesses for that open bond and marked connections from its endpoints. BK gives $X_2\le rp\chi_\gamma M^2$.</p>
<p>For the deletion term, first apply the signed bound <a href="/tag/G9X2/">G9X2</a>. Its right side is nonnegative, so the remaining indicator can then be enlarged from $J^-_v$ to $J_v$. The mark-at-$v$ contribution uses independence from the bond cluster, while the double-arm contribution uses the four-witness tree from 60X1. Consequently</p>
<div class="math-display">$$\mathbb P(y\in A,J_v)\le\gamma T(v,y)+M^2\sum_wT(v,w)T(w,y).$$</div>
<p>The first term is essential: enlarging the event also changes its deletion cost. Hence</p>
<div class="math-display">$$X_3\le p\sum_y\tau_\gamma(o,y)\sum_{(u,v)}T(y,u)\left[\gamma T(v,y)+M^2\sum_wT(v,w)T(w,y)\right]\le r\chi_\gamma\eta(\gamma+M^2).$$</div>
<p>For the last step, each inner sum is independent of $y$ by vertex transitivity. Averaging over $y$ gives respectively $N^{-1}\sum_{(u,v)}T^2(u,v)$ and $N^{-1}\sum_{(u,v)}T^3(u,v)$, both at most $m\eta$ because $u\ne v$. Edge transitivity is unnecessary. Substitute the Bonferroni bound for $X_1$ and use $\chi_\gamma=qM_\gamma$.</p>

## The sharp square-root bound {#section-integral}

<a id="tag-14T6" data-assertion="theorem" data-title="A uniform small-error coefficient gives the leading square-root field constant"></a>
<p>Fix $p<1$. Suppose $0<t\le1/100$ and $0<\gamma_*\le t$ satisfy</p>
<div class="math-display">$$|mp-1|\le t,\qquad p\le t,\qquad \eta\le t,\qquad M(p,\gamma_*)\le t.$$</div>
<p>Then, for $0\le\gamma\le\gamma_*$,</p>
<div class="math-display">$$M(p,\gamma)^2\le C_t\gamma,\qquad C_t=\frac{2(1+20t)}{1-20t}.$$</div>
<p><em>Proof.</em> Throughout this field interval, $M,\gamma\le t$. Since $m(m-1)p^2=r^2-rp$ and $b\ge1-3t$, the positive term in $L$ is at least $1/2-3t$. Its two subtractions are at most $2t$ and $t$, respectively: use $r\le1+t$, $M+\eta\le2t$ and $M^2+4\eta\le t^2+4t$. Thus</p>
<div class="math-display">$$L\ge\frac12-6t,\qquad qL-p-\eta\ge\frac12-9t,\qquad rq(qL-p-\eta)\ge\frac12-10t,$$</div>
<p>where $rq\ge(1-t)^2\ge1-2t$. Also $rq(1-\eta)\ge(1-t)^3\ge1-3t$. With $B=1-20t>0$, the cutting inequality implies</p>
<div class="math-display">$$M\ge B\left(\gamma+\frac{M^2}{2}\right)M_\gamma.$$</div>
<p>The finite-graph field function is strictly increasing below field one, so let $g(u)$ be its inverse. Then $g'(u)\ge Bg(u)/u+Bu/2$. Integrating $(g(u)u^{-B})'\ge(B/2)u^{1-B}$ from $s$ to $u$ and discarding the nonnegative initial value gives</p>
<div class="math-display">$$g(u)u^{-B}\ge\frac{B}{2(2-B)}(u^{2-B}-s^{2-B}).$$</div>
<p>Let $s\downarrow0$; $B<2$ and $M(p,0)=0$. Rearrangement gives the stated constant.</p>
<p>The hypotheses are satisfiable. On $K_N$ with $N=10^{15}$ and $mp=999/1000$, the row-sum bound gives $\chi\le1000$. The complete-graph identity <a href="/tag/R2Y7/">R2Y7</a> gives $\eta\le\chi^3/N\le10^{-6}$. At $\gamma_*=10^{-10}$, $M\le\gamma_*\chi\le10^{-7}$. Thus $t=10^{-3}$ works. This is a written finite witness.</p>

## Transporting a level of the field {#section-transport}

<a id="tag-HGND" data-assertion="proposition" data-title="Exact inverse-field transport from a square-root bound"></a>
<p>Let $0\le p_0\le p_1<1$ and $0<\gamma<1$. Put</p>
<div class="math-display">$$\nu=M(p_1,\gamma),\qquad h=-\log(1-\gamma),\qquad K=m\log\frac{1-p_0}{1-p_1}.$$</div>
<p>Suppose $M(p_0,z)^2\le Cz$ for $0\le z\le\gamma_*<1$, and $\nu\le U$. If $h+KU\le-\log(1-\gamma_*)$, then</p>
<div class="math-display">$$\nu\le\frac{CK+\sqrt{C^2K^2+4Ch}}2.$$</div>
<p><em>Proof.</em> The finite Russo upper bound is $(1-p)M_p\le m(1-\gamma)MM_\gamma$; see <a href="/tag/1T2M/">1T2M</a>. In the variable $h$, write $\mathcal M(p,h)=M(p,1-e^{-h})$. It gives $\mathcal M_p\le m\mathcal M\mathcal M_h/(1-p)$. The level $\mathcal M(p,H(p))=\nu$ exists uniquely and satisfies</p>
<div class="math-display">$$H'(p)=-\frac{\mathcal M_p}{\mathcal M_h}\ge-\frac{m\nu}{1-p}.$$</div>
<p>Integrating yields $H(p_0)\le h+K\nu$. Thus $M(p_0,1-e^{-(h+K\nu)})\ge\nu$. The field restriction allows the assumed square-root bound, and $1-e^{-x}\le x$ gives $\nu^2\le C(h+K\nu)$. Solve this quadratic. The logarithmic displacement $K$ is exact; it is only approximated in the next asymptotic statement.</p>

## Matching the supercritical constant {#section-asymptotic}

<p>Consider a sequence of the finite transitive graphs above, with $m\to\infty$. At a reference $p_c\le1/2$, assume</p>
<div class="math-display">$$\chi(p_c)=\lambda N^{1/3}\ge100,\qquad \eta(p_c)\le a\le1/100,\qquad \rho=mp_c\longrightarrow1,$$</div>
<p>where $\lambda>0$ and $a$ are fixed. Assume also the stronger subcritical triangle estimate, with fixed $C_0$ and $a_N\ge0$ tending to zero,</p>
<div class="math-display">$$\eta(p)\le a_N+C_0\frac{\chi(p)^3}{N}\qquad(0\le p\le p_c).$$</div>
<p>Let $p_1=p_c+\varepsilon/m\le1/2$, where $\varepsilon>0$, $\varepsilon\to0$, and $Q=\varepsilon^3N\to\infty$. The displacement is additive; for the paper's $p_1=p_c(1+e)$, it is $\varepsilon=\rho e$.</p>

<a id="tag-6SGU" data-assertion="theorem" data-title="A sharp supercritical field upper bound under the strong triangle estimate"></a>
<p>For every sequence of fields $0<\gamma\to0$,</p>
<div class="math-display">$$M(p_1,\gamma)\le\left(\varepsilon+\sqrt{\varepsilon^2+2\gamma}\right)\left[1+O\left(\varepsilon+\sqrt\gamma+|\rho-1|+m^{-1}+a_N+Q^{-1/4}\right)\right].$$</div>
<p>The constants depend only on the fixed reference and triangle constants.</p>
<p><em>Proof.</em> Set $\sigma=\varepsilon Q^{-1/4}$ and $p_0=p_c-\sigma/m$, which is positive eventually. The susceptibility estimate <a href="/tag/F5Y5/">F5Y5</a> gives $\chi(p_0)\le[(1-a)\sigma]^{-1}$. Therefore</p>
<div class="math-display">$$\eta(p_0)\le a_N+\frac{C_0}{(1-a)^3}Q^{-1/4},\qquad mp_0=\rho-\sigma,\qquad p_0=O(m^{-1}).$$</div>
<p>Put $s=\sqrt\gamma+\varepsilon$ and $\gamma_*=1000s^2$, eventually less than $1/2$. Monotonicity and the reference bound <a href="/tag/KQN9/">KQN9</a> give $M(p_0,\gamma_*)\le\sqrt{48\gamma_*}$. Choose</p>
<div class="math-display">$$t=\max\{|mp_0-1|,p_0,\eta(p_0),\gamma_*,\sqrt{48\gamma_*}\}.$$</div>
<p>Then $0<t\le1/100$ eventually, and $t=O(|\rho-1|+m^{-1}+a_N+Q^{-1/4}+s)$. The sharp square-root bound applies with $C=C_t=2[1+O(t)]$.</p>
<p>It remains to check its field range before transporting it. The coarse bound from 1T2M gives $\nu=M(p_1,\gamma)\le U=10\sqrt\gamma+96\varepsilon$. Also</p>
<div class="math-display">$$K=m\int_{p_0}^{p_1}\frac{du}{1-u}=\varepsilon[1+O(Q^{-1/4}+m^{-1})].$$</div>
<p>For large enough graphs, $K\le2\varepsilon$ and $h\le2\gamma$, so $h+KU\le214s^2\le\gamma_*\le-\log(1-\gamma_*)$. The transport proposition now applies. Insert $C=2[1+O(t)]$, the expression for $K$, and $h=\gamma[1+O(\gamma)]$ in its positive quadratic root. Each positive term changes by a relative $O(t+Q^{-1/4}+m^{-1})$ uniformly in $\gamma/\varepsilon^2$, giving the claim.</p>

<a id="tag-Q6CS" data-assertion="corollary" data-title="The root-cluster tail has leading constant two above the finite window"></a>
<p>Under these hypotheses, for each fixed $0<\alpha<1/3$ and $k=\varepsilon^{-2}Q^\alpha$,</p>
<div class="math-display">$$\mathbb P_{p_1}(|C_o|\ge k)=2\varepsilon\left[1+O\left(|\rho-1|+\varepsilon+m^{-1}+a_N+\frac{\log\log Q}{\log Q}\right)\right].$$</div>
<p>A real cutoff means its ceiling.</p>
<p><em>Proof.</em> More generally, for a cutoff with $L=\varepsilon^2k\to\infty$, choose $\gamma=\varepsilon^2L^{-1/2}$. Then $\gamma k=\sqrt L$, so marking gives</p>
<div class="math-display">$$\mathbb P(|C_o|\ge k)\le\frac{M(p_1,\gamma)}{1-e^{-\sqrt L}}\le2\varepsilon\left[1+O\left(\varepsilon+|\rho-1|+m^{-1}+a_N+Q^{-1/4}+L^{-1/2}\right)\right].$$</div>
<p>Use the sharp field bound and $\sqrt{1+2L^{-1/2}}=1+O(L^{-1/2})$; its $\sqrt\gamma$ term is at most $\varepsilon$. For $L=Q^\alpha$, combine this upper bound with the independent lower bound <a href="/tag/CI72/">CI72</a>. Both powers of $Q$ are smaller than its logarithmic error.</p>

## What this repairs {#section-scope}

<p>The new event, root-deleted pair events and extra $\gamma\eta$ deletion term give a complete replacement for the sharp upper-field route. The <a href="/errata/hofstad-nachmias-hypercube/#double-mark-root-event">event erratum</a> is therefore labelled “fix found”, with a substantial change to the proof. Its corrected finite coefficient is displayed above; the literal printed coefficient in (A.8) is not being asserted.</p>
<p>The separate <a href="/errata/hofstad-nachmias-hypercube/#supercritical-field-rectangle">lower-field rectangle entry</a> is now labelled “fix found / substantial”: the <a href="/articles/characteristic-field-growth/">characteristic argument</a> removes the logarithmic loss. The later <a href="/articles/quantitative-supercritical-tails/">quantitative tail bounds</a> improve the marking error and give a largest-component upper bound under a stronger separation hypothesis. The strongest general published upper-error rate and a giant-component lower bound remain separate obligations. All source corrections remain provisional pending confirmation; the <a href="/coverage/sources/sharp-upper-field/">reading map</a> records the passages checked. These are written proofs, not new Lean evidence.</p>
