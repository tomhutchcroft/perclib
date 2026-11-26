---
{
  "id": "sharpness-bond-parameter",
  "title": "Sharpness in the bond parameter",
  "subtitle": "Boundary multiplicities and the zero-field endpoint",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Finite-set contraction gives exponential decay with an explicit all-radius constant. The probability-parameter derivative gives the sharper density bound. Magnetization calculus retains infinite clusters and the actual domain of its inverse.",
  "context": [
    "Independent nearest-neighbour bond percolation on the integer lattice in dimension d at least one, with common bond probability p.",
    "Boxes use the maximum norm. Every edge leaving a set is counted once, oriented from its endpoint in the set.",
    "Green marks are independent Bernoulli variables with probability gamma. Their zero-field right limit need not equal the literal value at zero.",
    "The inverse and rectangle propositions are analytic implications. The final theorem supplies their percolation hypotheses by finite-torus approximation, without assuming infinite-volume differentiability everywhere."
  ],
  "related": ["finite-size-sharpness", "boundary-laws", "ghost-fields", "russo-formula", "integrated-lower-tails"],
  "sourceIds": ["heydenreich-hofstad"],
  "aliases": ["bond parameter sharpness", "boundary multiplicity", "magnetization inverse", "Aizenman Barsky integration"],
  "prototypeUses": []
}
---

## Contraction at every radius {#section-contraction}

<p>Let $\Lambda_N=[-N,N]^d\cap\mathbb Z^d$, $\partial\Lambda_N=\{x:|x|_\infty=N\}$ and $a_N(p)=\mathbb P_p(0\leftrightarrow\partial\Lambda_N)$, with $a_0=1$. For a finite $S\ni0$, write</p>
<div class="math-display">$$\phi_p(S)=p\sum_{\substack{x\in S,\ y\notin S\\|x-y|_1=1}}\mathbb P_p(0\leftrightarrow_S x).$$</div>

<a id="tag-TVM9" data-assertion="proposition" data-title="Finite-set contraction with an all-radius exponential constant"></a>
<p>Suppose $0<p<1$, $S\subseteq\Lambda_{L-1}$ and $0<\phi:=\phi_p(S)<1$. For every integer $N\ge0$,</p>
<div class="math-display">$$a_N(p)\le\phi^{\lfloor N/L\rfloor}.$$</div>
<p>In particular, for all $N\ge1$, $a_N(p)\le e^{-cN}$, where</p>
<div class="math-display">$$c=\frac1{2L}\min\{-\log\phi,-\log[1-(1-p)^{2d}]\}>0.$$</div>
<p><em>Proof.</em> Reveal the root cluster $C_S$ using only edges internal to $S$. For a fixed possible value $C$, the event $\{C_S=C\}$ requires connectivity inside $C$ and closure of every edge from $C$ to $S\setminus C$. It therefore uses only edges internal to $S$ with at least one endpoint in $C$, as also follows from <a href="/tag/R3I9/">the prescribed-cluster identity</a>.</p>
<p>If the root reaches $\partial\Lambda_{kL}$, follow a path to that boundary and take its last exit from $C_S$. Its exit edge $(x,y)$ has $x\in C_S$ and $y\notin S$: an open edge from $C_S$ to $S\setminus C_S$ would contradict the definition of $C_S$. The remaining path avoids $C_S$. Conditional on $C_S=C$, the exit edge, the event specifying $C$, and the remaining connection off $C$ use disjoint coordinate sets. Deleting $C$ can only decrease the last connection probability. Since $|y|_\infty\le L$, reaching $\partial\Lambda_{kL}$ from $y$ requires reaching distance at least $(k-1)L$ from $y$. Translation invariance, a union bound and summation over $C$ give</p>
<div class="math-display">$$a_{kL}(p)\le p\sum_{(x,y)\in\Delta S}\mathbb P_p(x\in C_S)\,a_{(k-1)L}(p)=\phi a_{(k-1)L}(p).$$</div>
<p>Iteration gives $a_{kL}\le\phi^k$. Monotonicity in the radius gives the floor bound. If $N\ge2L$, then $\lfloor N/L\rfloor\ge N/(2L)$. If $1\le N<2L$, use $a_N\le a_1=1-(1-p)^{2d}$ instead. These two bounds give the stated $c$. At $p=0$ every positive-radius arm probability is zero, so any positive $c$ works.</p>
<p>The cluster event is not determined just by edges with both endpoints in $C$. For example, with $S=\{0,e_1\}$, the event $C_S=\{0\}$ reads the edge between these two vertices, although there is no edge internal to the singleton. Including the closed internal boundary repairs the independence explanation without changing the factorization.</p>
<p>The larger choice $c=L^{-1}\log(1/\phi)$ need not work at every radius. Take $d=2$, $p=1/100$, $S=\Lambda_{20}$ and $L=21$. There are $164$ edges leaving this box. For each boundary vertex, counting self-avoiding paths gives</p>
<div class="math-display">$$\mathbb P_p(0\leftrightarrow_S x)\le\sum_{j\ge20}4\cdot3^{j-1}p^j=\frac{4(3p)^{20}}{3(1-3p)}.$$</div>
<p>Consequently</p>
<div class="math-display">$$0<\phi_p(S)\le\frac{656}{291}\left(\frac3{100}\right)^{20}
<\left[1-\left(\frac{99}{100}\right)^4\right]^{21}<1.$$</div>
<p>The strict middle inequality is an inequality of explicit rational numbers. Thus $\phi_p(S)^{1/21}<a_1(p)$, contradicting the proposed bound at radius one. The existence of a positive exponential rate is unaffected.</p>
<p>The corresponding manuscript errata record the <a href="/errata/heydenreich-hofstad/#internal-cluster-coordinate-support">coordinate-support repair</a> and the <a href="/errata/heydenreich-hofstad/#all-radius-exponential-rate">change to the all-radius rate</a>.</p>

## The derivative and the boundary count {#section-boundary}

<a id="tag-JQLC" data-assertion="theorem" data-title="Bond-parameter density bound and the corrected critical boundary sum"></a>
<p>Let $p_c$ be the nearest-neighbour percolation threshold. Then $\chi(p)<\infty$ and $a_N(p)\le e^{-c(p)N}$ for $0\le p<p_c$, with some $c(p)>0$. Moreover,</p>
<div class="math-display">$$\theta(p)\ge\frac{p-p_c}{p(1-p_c)}\quad(p_c<p<1),\qquad \chi(p_c)=\infty.$$</div>
<p>The first display involving $1-p_c$ is asserted only when its parameter interval is nonempty. No conclusion about $\theta(p_c)$ is made.</p>
<p><em>Proof.</em> Set $\beta=-\log(1-p)$ and give each nearest-neighbour edge intensity one. Then the boundary functional in <a href="/tag/L0TE/">the threshold theorem</a> is exactly $\phi_p$. That theorem and <a href="/tag/RDF0/">its contraction characterization</a> give a contracting finite set and finite susceptibility for every $p<p_c$; TVM9 gives the radius bound. This includes an infinite intensity threshold, corresponding to $p_c=1$.</p>
<p>For the sharper density bound, retain the finite product of edges needed to reach $\partial\Lambda_N$ and identify the boundary vertices with a single target. Distinct boundary edges remain distinct Bernoulli coordinates, even if identification gives parallel edges. Let $U$ be the set of interior vertices not connected to the target. On $U=T$, every boundary edge of $T$ is closed, and every interior vertex outside $T$ already reaches the target off $T$. The event $U=T$ therefore reads no edge internal to $T$.</p>
<p>For $0<p<1$, finite Russo differentiation and closed pivotality give</p>
<div class="math-display">$$a_N'(p)=\frac1{p(1-p)}
\sum_{\substack{T\subseteq\Lambda_{N-1}\\0\in T}}
\mathbb P_p(U=T)\phi_p(T).$$</div>
<p>Indeed, a closed pivotal edge has its unique endpoint $x\in T$ connected internally to the root. Independence factors this internal connection from $U=T$. The conversion from state-independent to closed pivotality supplies $1/(1-p)$; the definition of $\phi_p$ supplies $1/p$. This is the probability-parameter counterpart of <a href="/tag/HATE/">the wired derivative identity</a>.</p>
<p>When $p>p_c$, no finite set contracts. Otherwise the finite-set criterion would exclude percolation at that parameter. Hence</p>
<div class="math-display">$$a_N'(p)\ge\frac{1-a_N(p)}{p(1-p)}.$$</div>
<p>For $p_c<t<p<1$, the derivative of $p(1-a_N(p))/(1-p)$ is nonpositive. Integrating from $t$ and using $a_N(t)\ge0$ yields $a_N(p)\ge(p-t)/(p(1-t))$. First let $t\downarrow p_c$, then $N\to\infty$. The decreasing arm events converge to the event that the root cluster is infinite, proving the density bound. The divided derivative formula is used only on $0<p<1$. Its version multiplied by $p(1-p)$ extends to the endpoints by continuity of finite-product probabilities.</p>
<p>For the critical mean, suppose first that $p_c<1$. The singleton contraction at sufficiently small positive $p$ shows $p_c>0$. Continuity of every finite-set functional and the finite-size criterion give $\phi_{p_c}(S)\ge1$: a strict contraction at $p_c$ would persist at a larger parameter. For $N\ge1$, let $b_N(x)$ be the number of neighbours of $x\in\partial\Lambda_N$ outside $\Lambda_N$. The exact identity is</p>
<div class="math-display">$$\frac{\phi_{p_c}(\Lambda_N)}{p_c}
=\sum_{x\in\partial\Lambda_N}b_N(x)\mathbb P_{p_c}(0\leftrightarrow_{\Lambda_N}x).$$</div>
<p>Since $1\le b_N(x)\le d$,</p>
<div class="math-display">$$\sum_{x\in\partial\Lambda_N}\mathbb P_{p_c}(0\leftrightarrow x)
\ge\frac{\phi_{p_c}(\Lambda_N)}{dp_c}\ge\frac1{dp_c}.$$</div>
<p>Summing disjoint shells proves $\chi(p_c)=\infty$. A bound valid also for $N=0$ uses $2d$ in place of $d$. If $p_c=1$, every lattice edge is open at criticality and the conclusion is immediate.</p>
<p>Dropping $b_N(x)$ reverses the comparison with $\phi_p(\Lambda_N)/p$. In dimension at least two and for $p>0$, a corner has at least two outward edges and positive internal connection probability, so the unweighted sum is strictly smaller than this weighted sum. The degree factor repairs the estimate; divergence survives.</p>
<p>These corrections are recorded under <a href="/errata/heydenreich-hofstad/#probability-derivative-endpoints">derivative endpoints</a> and <a href="/errata/heydenreich-hofstad/#box-boundary-multiplicity">boundary multiplicity</a>.</p>

## The positive-field range {#section-field-range}

<p>For a cluster volume $T\in\{1,2,\ldots,\infty\}$, write $\theta=\mathbb P(T=\infty)$ and $\chi^{\mathrm f}=\mathbb E[T;T<\infty]$. Mark vertices independently with probability $\gamma$. The <a href="/tag/VF24/">ghost formula</a>, with $h=-\log(1-\gamma)$, reads</p>
<div class="math-display">$$m(\gamma)=\theta+\sum_{k\ge1}[1-(1-\gamma)^k]\mathbb P(T=k),\qquad 0<\gamma<1.$$</div>
<p>The literal value at zero is zero, while $m(0+)=\theta$. For positive $\gamma$,</p>
<div class="math-display">$$m'(\gamma)=\sum_{k\ge1}k(1-\gamma)^{k-1}\mathbb P(T=k),\qquad
(1-\gamma)m'(\gamma)\uparrow\chi^{\mathrm f}\quad(\gamma\downarrow0).$$</div>
<p>Dominated differentiation on compact positive-field intervals and monotone convergence prove these statements, as in <a href="/tag/J2TE/">J2TE</a>. Infinite clusters contribute the constant $\theta$, not a derivative. If $\mathbb P(T<\infty)>0$, then $m'>0$, and $m$ maps $(0,1)$ onto $(\theta,1)$. In lattice percolation with $p<1$, the singleton probability $(1-p)^{2d}$ guarantees this strictness. At $p=1$, instead, $m(\gamma)=1$ for every positive $\gamma$.</p>
<p>Omitting $\theta$ from the finite-size series gives the wrong observable in a percolating regime. At $p=1$ that series is zero, whereas the ghost probability is one. The inverse must likewise start at the right limit $\theta$, not at the literal zero-field value.</p>
<p>The <a href="/errata/heydenreich-hofstad/#magnetization-infinite-mass">magnetization erratum</a> records both the missing mass and the strict-monotonicity endpoint.</p>

## Integrating from the actual endpoint {#section-inverse}

<a id="tag-ZDVK" data-assertion="proposition" data-title="Magnetization lower bound with the inverse based at its positive-field limit"></a>
<p>Assume $\mathbb P(T<\infty)>0$ and, for some $A\ge0$,</p>
<div class="math-display">$$m\le\gamma m'+m^2+A m^2m'\qquad(0<\gamma<1).$$</div>
<p>Put $K=A+1$ and $u=1/\chi^{\mathrm f}$, with $1/\infty=0$. Then</p>
<div class="math-display">$$m(\gamma)\ge\sqrt{\frac\gamma K+\left(\frac{u}{2K}\right)^2}-\frac{u}{2K}.$$</div>
<p>If $\chi^{\mathrm f}=\infty$, this is $m(\gamma)\ge\sqrt{\gamma/K}$. The same square-root bound holds whenever $\theta>0$ under the displayed differential inequality, regardless of the finite-cluster mean.</p>
<p><em>Proof.</em> Let $g:(\theta,1)\to(0,1)$ be the inverse of $m$. Its derivative is positive, and division by $m^2m'$ gives</p>
<div class="math-display">$$\frac{d}{ds}\frac{g(s)}s\le A+g'(s).$$</div>
<p>The lower-endpoint limit is</p>
<div class="math-display">$$\alpha:=\lim_{s\downarrow\theta}\frac{g(s)}s
=\begin{cases}0,&\theta>0,\\1/\chi^{\mathrm f},&\theta=0.\end{cases}$$</div>
<p>For $\theta>0$, this follows from $g(s)\to0$. For $\theta=0$, the identity $[1-(1-\gamma)^k]/\gamma=\sum_{j=0}^{k-1}(1-\gamma)^j$ and monotone convergence give $m(\gamma)/\gamma\uparrow\chi^{\mathrm f}$. This also covers an infinite mean.</p>
<p>Integrate first from $s_0>\theta$ to $s=m(\gamma)$, and only then let $s_0\downarrow\theta$. Since $g(s_0)\to0$,</p>
<div class="math-display">$$\frac\gamma m\le\alpha+A(m-\theta)+\gamma\le\alpha+Km.$$</div>
<p>The last step uses $\gamma\le m$, since the root itself can be green. As $0\le\alpha\le u$, we obtain $\gamma\le um+Km^2$. Solving this quadratic gives the bound. If $\theta>0$, retain $\alpha=0$ to get the stronger conclusion.</p>
<p>For the percolation application, the two Aizenman–Barsky inequalities</p>
<div class="math-display">$$(1-p)M_p\le2d(1-\gamma)MM_\gamma,\qquad
M\le\gamma M_\gamma+M^2+pMM_p$$</div>
<p>imply the scalar hypothesis with $A=2dp/(1-p)$ at any fixed $0<p<1$ where these inequalities hold. ZDVK proves that analytic implication and corrects its endpoint even if $\theta(p)>0$. It does not supply the second percolation inequality or promote an almost-everywhere parameter derivative to one at every prescribed $p$.</p>
<p>The <a href="/errata/heydenreich-hofstad/#magnetization-inverse-endpoint">inverse-endpoint erratum</a> distinguishes this local proof repair from a change to the claimed lower bound.</p>

## The parameter rectangle {#section-rectangle}

<a id="tag-7HP2" data-assertion="proposition" data-title="A density bound from a positive-field rectangle inequality"></a>
<p>Fix $0<a<b<1$. Suppose $M:[a,b]\times(0,1)\to(0,1]$ is locally Lipschitz, nondecreasing in both variables, and satisfies</p>
<div class="math-display">$$M\le\gamma M_\gamma+M^2+pMM_p$$</div>
<p>almost everywhere. Suppose also that $M(a,\gamma)\ge c\gamma^\rho$ for all sufficiently small positive $\gamma$, with $c>0$ and $0<\rho<1$. Then</p>
<div class="math-display">$$\lim_{\gamma\downarrow0}M(b,\gamma)\ge(1-\rho)\frac{b-a}{b}.$$</div>
<p><em>Proof.</em> Divide the inequality by $\gamma M$ to obtain</p>
<div class="math-display">$$\partial_\gamma\log M+\frac1\gamma\partial_p(pM-p)\ge0.$$</div>
<p>On a compact rectangle $[a,b]\times[\delta,\varepsilon]$, positivity bounds $M$ away from zero. The chain rule, absolute continuity on lines and Fubini therefore allow integration of both derivatives. Monotonicity bounds the resulting boundary integrals above by their corner values, giving</p>
<div class="math-display">$$0\le(b-a)\log\frac{M(b,\varepsilon)}{M(a,\delta)}
+\log\frac\varepsilon\delta\,[bM(b,\varepsilon)-aM(a,\delta)-(b-a)].$$</div>
<p>Discard the nonpositive term containing $aM(a,\delta)$, divide by $\log(\varepsilon/\delta)$, and let $\delta\downarrow0$. The assumed lower bound at $a$ makes the limsup of the logarithmic ratio at most $\rho$. Hence $bM(b,\varepsilon)\ge(1-\rho)(b-a)$. Let $\varepsilon\downarrow0$; monotonicity gives the limit.</p>
<p>Taking $\rho=1/2$ and the square-root bound from ZDVK gives the factor $1/2$ in the manuscript's alternative sharpness argument. The percolation limit is $\theta(b)$ by the ghost formula. Local Lipschitz regularity in the probability parameter at positive field also follows from <a href="/tag/F7SW/">the sprinkling bound</a> after $\beta=-\log(1-p)$. The next theorem supplies both differential inequalities with the regularity needed here.</p>

## From finite tori to the infinite graph {#section-differential-inequalities}

<a id="tag-G192" data-assertion="theorem" data-title="Aizenman–Barsky inequalities by positive-field finite-torus approximation"></a>
<p>For nearest-neighbour percolation on $\mathbb Z^d$, $M$ is locally Lipschitz on $(0,1)^2$, and</p>
<div class="math-display">$$(1-p)M_p\le2d(1-\gamma)MM_\gamma,\qquad
M\le\gamma M_\gamma+M^2+pMM_p$$</div>
<p>hold almost everywhere there. The combined scalar inequality</p>
<div class="math-display">$$M\le\gamma M_\gamma+M^2+\frac{2dp}{1-p}M^2M_\gamma$$</div>
<p>holds at every $0<p,\gamma<1$. Consequently the lower bound in ZDVK holds at every such $p$, with $K=1+2dp/(1-p)$. If $0<a<1$ and $\chi^{\mathrm f}(a)=\infty$, then</p>
<div class="math-display">$$\theta(b)\ge\frac{b-a}{2b}\qquad(a<b<1).$$</div>
<p>This density conclusion does not require $\theta(a)=0$.</p>
<p><em>Proof.</em> Work first on a finite transitive graph of degree $2d$, with independent marks of probability $\gamma$. Add a target vertex $g$ and represent the mark at $v$ by the edge $\{v,g\}$. Thus disjoint ghost witnesses must use distinct mark coordinates as well as distinct bond coordinates. Write $M$ for the common probability of connection to $g$, $C_o$ for the bond cluster of the root, and $A_y$ for $y\leftrightarrow g$. All derivatives in this finite model are ordinary derivatives of polynomials.</p>
<p>A closed bond $(x,y)$ is pivotal precisely when $x\in C_o$, $C_o$ has no green vertex, and $y$ connects to $g$ off $C_o$. The orientation is unique. For a fixed $C=C_o$, its internal and closed-boundary bond coordinates and the marks in $C$ are independent of the connections and marks off $C$. Hence finite Russo gives the exact identity</p>
<div class="math-display">$$(1-p)M_p=
\sum_{(x,y)}\ \sum_{\substack{C\ni o,x\\y\notin C}}
\mathbb P_p(C_o=C)(1-\gamma)^{|C|}\mathbb P_{p,\gamma}(A_y\text{ off }C).$$</div>
<p>Deleting $C$ decreases the last probability, which is therefore at most $M$. Summing the at most $2d|C|$ outward oriented bonds and using $\mathbb E[|C_o|(1-\gamma)^{|C_o|}]=(1-\gamma)M_\gamma$ proves the first inequality.</p>
<p>For the second inequality, the event that $C_o$ contains exactly one green vertex has probability $\gamma M_\gamma$. The event that the root has two edge-disjoint connections to $g$ has probability at most $M^2$ by finite BK in the augmented product space. It remains to consider configurations with at least two green vertices in $C_o$ and without two disjoint root-to-$g$ paths.</p>
<p>We use the elementary finite edge-cut alternative. Given a simple path from a vertex $v$ to $g$, allow every unused open edge in both directions and each path edge only in the reverse direction. A path from $v$ to $g$ in this residual graph augments the original unit flow to two units; cancelling oppositely used edges and deleting cycles gives two edge-disjoint paths. If there is no residual path, let $R$ be the vertices reachable from $v$. Every open edge leaving $R$ must be a forward edge of the original path. That path cannot re-enter $R$, since a re-entry would give an allowed reverse edge leaving $R$. It therefore crosses this cut exactly once. The unique cut edge separates $v$ from $g$.</p>
<p>Apply this alternative to the residual configuration under consideration. Its open pivotal edges lie in order on any root-to-$g$ path. Let $e=(x,y)$ be the last, oriented towards $g$, and close it. The resulting root cluster $C$ contains no green vertex. There are two edge-disjoint paths from $y$ to $g$ off $C$: otherwise the cut alternative would give a further root-to-$g$ pivotal edge. Moreover, $e$ is a bond edge. A pivotal mark edge would imply that the whole root bond cluster contained only its one marked endpoint.</p>
<p>For a fixed oriented bond $e$ and set $C$, switching $e$ from open to closed multiplies the probability by $(1-p)/p$. A union bound over the possible last bonds therefore bounds the remaining event by</p>
<div class="math-display">$$\frac p{1-p}\sum_{(x,y)}\ \sum_{\substack{C\ni o,x\\y\notin C}}
\mathbb P_p(C_o=C)(1-\gamma)^{|C|}
\mathbb P_{p,\gamma}(A_y\circ A_y\text{ off }C).$$</div>
<p>The two connections include their terminal mark edges. BK bounds their probability by $\mathbb P(A_y\text{ off }C)^2\le M\mathbb P(A_y\text{ off }C)$. The exact closed-pivotal identity above now makes the displayed expression at most $pMM_p$. Adding the three parts proves the second inequality. Combining the two inequalities and dropping the factor $1-\gamma\le1$ gives the scalar inequality at every interior parameter of the finite model.</p>
<p>Now take tori $(\mathbb Z/(2R+1)\mathbb Z)^d$, with $R\to\infty$. Fix an integer $L<R$. Couple the bonds in $\Lambda_L$ with those of the infinite lattice. If the root cluster does not reach $\partial\Lambda_L$, the torus and lattice root clusters agree. Otherwise both have at least $L+1$ vertices. Since the cluster contribution to $M$ is $1-(1-\gamma)^t$, with value one at $t=\infty$,</p>
<div class="math-display">$$|M_R(p,\gamma)-M(p,\gamma)|\le2(1-\gamma)^L.$$</div>
<p>The same coupling applied to the field derivative gives</p>
<div class="math-display">$$|(M_R)_\gamma(p,\gamma)-M_\gamma(p,\gamma)|
\le2\sup_{t\ge L}t(1-\gamma)^{t-1},$$</div>
<p>where the derivative contribution at infinity is zero. Both bounds tend to zero uniformly in $p$ and on compact positive-field intervals. This proves local uniform convergence of $M_R$ and its field derivative.</p>
<p>The first finite inequality bounds $(M_R)_p$ uniformly on every compact rectangle in $(0,1)^2$; the displayed field-derivative formula bounds $(M_R)_\gamma$ there as well. The limit is therefore locally Lipschitz. To pass the second inequality, write it as</p>
<div class="math-display">$$\partial_\gamma\log M_R+\gamma^{-1}\partial_p(pM_R-p)\ge0.$$</div>
<p>Multiply by a nonnegative smooth test function supported in a compact rectangle and integrate by parts. Since $M_R\ge\gamma$, uniform convergence permits passage to the limit in both terms. This gives the distributional inequality for $M$, hence its almost-everywhere form because $M$ is locally Lipschitz. The first inequality passes in the same way: its right-hand side converges uniformly, and the derivative on the left passes distributionally.</p>
<p>Finally, pass directly to the limit in the finite scalar inequality, using convergence of $M_R$ and $(M_R)_\gamma$. No derivative in $p$ appears in that inequality, so it holds at every fixed interior $p$, not merely almost everywhere. Apply ZDVK with the lattice cluster law; its positive singleton probability gives the required strict field derivative. If $\chi^{\mathrm f}(a)=\infty$, the resulting square-root lower bound at $a$ and 7HP2 give the density conclusion. This completes the finite-volume justification of the core Aizenman–Barsky route without assuming continuity at zero field or differentiability in the percolation parameter everywhere.</p>

<p>Source reconciliation: <a href="/coverage/sources/heydenreich-hofstad-2017-sharpness/">Chapter 3 of the dated author manuscript</a>. The map separates repaired arguments, existing proofs and remaining inputs. The new arguments have no compiled Lean association.</p>
