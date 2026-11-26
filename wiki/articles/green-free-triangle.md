---
{
  "id": "green-free-triangle",
  "title": "Green-free clusters and mean-field tails",
  "subtitle": "The triangle differential inequality and extrapolation",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A green-free BK bound controls the loss in a cutting-bond identity. The resulting differential inequality gives square-root critical tails and, by extrapolation on the valid inverse-level domain, linear density on the scale 2d(p-p_c).",
  "context": [
    "Nearest-neighbour bond percolation on $\\mathbb Z^d$ with independent green marks of probability $\\gamma$.",
    "The triangle differential inequality is stated with its finite-diagram hypothesis and a positive-part correction.",
    "Dimension-uniform density estimates use the scale $2d(p-p_c)$."
  ],
  "related": [
    "completed-fourier-bootstrap",
    "sharpness-bond-parameter",
    "triangle-susceptibility",
    "lace-expansion"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "green-free BK",
    "triangle magnetization inequality",
    "critical cluster tails",
    "Barsky Aizenman extrapolation"
  ],
  "prototypeUses": []
}
---

## Retaining a green-free connection {#section-green-free}

<p>Let $G$ be the random set of green vertices. A connection event is <em>green-free</em> when the bond clusters of all its specified endpoints avoid $G$. Disjoint occurrence below refers to bond witnesses; when a connection to $G$ is included, its terminal mark is also part of the witness.</p>
<a id="tag-J3M4" data-assertion="proposition" data-title="BK can retain the green-free condition on one connection event"></a>
<p>Let $E_1,E_2$ be finite intersections of specified pair connections, allowing specified disjoint occurrence of those connections. Then</p>
<div class="math-display">$$\mathbb P_{p,\gamma}(E_1\circ E_2\text{ and green-free})
\le\mathbb P_{p,\gamma}(E_1\text{ and green-free})\,\mathbb P_p(E_2).$$</div>
<p><em>Proof.</em> First work in a finite box. Reveal the set $C$ of vertices connected to a green vertex. Conditional on this set, every crossing bond is closed, every mark outside $C$ is absent, and the bonds with both endpoints outside $C$ retain their independent product law. The event on the left is exactly $E_1\circ E_2$ in the induced graph outside $C$, with a connection declared false if one of its specified endpoints has been removed. BK in that graph bounds its probability by the product of the two separate connection probabilities. Deleting vertices decreases the second factor, so it is at most $\mathbb P_p(E_2)$ in the box. Sum over $C$; the first factor becomes the green-free probability of $E_1$.</p>
<p>Exhaust the lattice by boxes. Every required connection or disjoint connection has finite witnesses. If any specified endpoint is connected to a green vertex, that too has a finite witness. The finite-box indicators therefore converge almost surely to the respective infinite-volume indicators, although the green-free indicators need not be monotone. Bounded convergence proves the claim.</p>

## The triangle differential inequality {#section-differential}

<p>Put $q=2d$, $M=M(p,\gamma)$ and</p>
<div class="math-display">$$\tau_\gamma(x,y)=\mathbb P_{p,\gamma}(x\leftrightarrow y,\ x\not\leftrightarrow G),\quad
\chi_\gamma=\sum_x\tau_\gamma(0,x)=(1-\gamma)M_\gamma,\quad
\eta=\sup_x[\tau_p^{*3}(x)-\mathbf1_{\{x=0\}}].$$</div>
<p>The identity for $\chi_\gamma$ follows by conditioning on the root bond cluster: both sides are $\mathbb E[|C_0|(1-\gamma)^{|C_0|}]$, with infinite clusters contributing zero. In particular it is finite for positive field. Write $t_+=\max\{t,0\}$.</p>
<a id="tag-OB0K" data-assertion="theorem" data-title="A triangle differential inequality with an explicit smallness qualification"></a>
<p>Suppose $0\le p\le p_c$, $p<1$, and $\eta<\infty$. For $0<\gamma<1$,</p>
<div class="math-display">$$M\ge\kappa_*(p)(1-\gamma)M^2M_\gamma,$$</div>
<p>where</p>
<div class="math-display">$$\kappa_*(p)=qp\left[\binom q2p^2(1-p)^{q-2}\{(1-\eta)_+^2-\eta\}-p-\eta\right].$$</div>
<p>If $\eta\le1$, this is the usual polynomial coefficient. The positive part makes the bound valid outside that range; it then has a nonpositive coefficient and is trivial.</p>
<p><em>Proof.</em> The case $p=0$ is immediate. Finiteness of the triangle excludes critical percolation by <a href="/tag/5W46/">5W46</a>; below criticality all clusters are already finite. In dimension one the assumption $p<1$ gives the same conclusion. Thus the cluster decompositions below involve finite sets almost surely.</p>
<p>Write $v\Leftrightarrow G$ for two edge-disjoint paths to distinct green vertices, including their distinct terminal marks. Let $F_{u,v}$ be the event that the bond $\{u,v\}$ is open and pivotal for $0\leftrightarrow G$, oriented towards $v$, with $v\Leftrightarrow G$. At most one such oriented bond occurs: the open pivotal bonds are ordered along any root-to-green path, and only the last can have two disjoint green connections beyond it. Consequently $M\ge\sum_{(u,v)}\mathbb P(F_{u,v})$.</p>
<p>Close $\{u,v\}$ and let $A$ be the bond cluster of $v$. Conditional on $A$, its internal bonds, closed boundary and marks are independent of the bond and mark coordinates outside $A$. The bond $\{u,v\}$ itself was not used to reveal $A$. On the support of an outside connection from $0$ to $u$, both $0,u$ lie outside $A$. The cutting identity is therefore</p>
<div class="math-display">$$\mathbb P(F_{u,v})=p\,\mathbb E\left[\tau_\gamma^A(0,u)\,\mathbf1_{\{v\Leftrightarrow G\}\text{ with }\{u,v\}\text{ closed}}\right],$$</div>
<p>where $\tau_\gamma^A$ is computed after deleting $A$. This includes absence of green connections in the remaining graph, rather than in the original graph.</p>
<p>Add and subtract the unrestricted two-point function and the unrestricted double-green event. The sum of the cutting identities has the form $X_1-X_2-X_3$, where</p>
<div class="math-display">$$X_1=qp\chi_\gamma\mathbb P(0\Leftrightarrow G),$$</div>
<p>$X_2$ is the loss from closing the single bond in the double-green event, and $X_3$ is the loss from replacing $\tau_\gamma$ by $\tau_\gamma^A$. The latter loss can have either sign. These subtractions are legitimate: the sums of the unrestricted nonnegative terms are bounded by $q\chi_\gamma$, and the sum of the restricted terms is the cutting probability divided by $p$.</p>
<p>For $X_1$, force exactly two root bonds, to distinct neighbours $e,f$, to be open. In the graph with the root deleted, require the clusters of $e,f$ to be disjoint and each to contain a green vertex. These events for different unordered pairs are disjoint. Let $M^-(x)$ be the green-connection probability after deleting the root. BK at the first visit to the root gives</p>
<div class="math-display">$$M^-(x)\ge M[1-\tau_p(x)]\ge M(1-\eta)_+\qquad(x\ne0).$$</div>
<p>Reveal the cluster of $e$ in the deleted graph. A green connection from $f$ lost upon deleting this cluster must visit some vertex $y$ of it. BK bounds this loss by $\sum_y\tau_p(f,y)M\mathbf1_{\{e\leftrightarrow y\}}$. The joint event $e\leftrightarrow y$, $e\leftrightarrow G$ has a branch vertex $w$ with three disjoint witnesses, so its probability is at most $M\sum_w\tau_p(e,w)\tau_p(w,y)$. Thus the probability that the two clusters are disjoint and green is at least</p>
<div class="math-display">$$M^-(e)M^-(f)-M^2\sum_{y,w}\tau_p(f,y)\tau_p(e,w)\tau_p(w,y)
\ge M^2\{(1-\eta)_+^2-\eta\}.$$</div>
<p>Here $e\ne f$, so the last triple convolution is at most $\eta$. The forced root bonds now give</p>
<div class="math-display">$$X_1\ge qp\chi_\gamma\binom q2p^2(1-p)^{q-2}M^2\{(1-\eta)_+^2-\eta\}.$$</div>
<p>For $X_2$, a double-green connection destroyed by closing $\{u,v\}$ has disjoint witnesses for that open bond, a green connection from $u$, and a green connection from $v$. BK bounds its probability by $pM^2$. Hence $X_2\le qp^2\chi_\gamma M^2$.</p>
<p>For $X_3$, use the same bond and mark configuration to compare a fixed deleted set $A$ with the full graph. The difference $\tau_\gamma(0,u)-\tau_\gamma^A(0,u)$ is at most the probability that $0\leftrightarrow u$ requires $A$ and the full root cluster is green-free. Indeed the other difference, due only to making the green-free condition easier after deletion, is nonpositive. Split a simple connecting path at a vertex $y\in A$ and apply J3M4. The loss is at most</p>
<div class="math-display">$$\sum_{y\in A}\tau_\gamma(0,y)\tau_p(y,u).$$</div>
<p>This upper bound is nonnegative, so it is now legitimate to replace the deleted-bond double-green indicator by the larger unrestricted one. If $y$ is in the deleted-bond cluster of $v$ and $v\Leftrightarrow G$, follow a path from $y$ until its first intersection $w$ with the union of two disjoint green arms from $v$. Splitting the arm that contains $w$ gives disjoint witnesses for $v\leftrightarrow w$, $w\leftrightarrow y$, $w\leftrightarrow G$ and $v\leftrightarrow G$. BK therefore gives</p>
<div class="math-display">$$\begin{aligned}
X_3&\le pM^2\sum_y\tau_\gamma(0,y)\sum_{(u,v),w}\tau_p(y,u)\tau_p(v,w)\tau_p(y,w)\\
&=pM^2\chi_\gamma\sum_{e\sim0}\tau_p^{*3}(e)
\le qp\eta M^2\chi_\gamma.
\end{aligned}$$</div>
<p>Combine these three estimates and substitute $\chi_\gamma=(1-\gamma)M_\gamma$. The <a href="/errata/heydenreich-hofstad/#triangle-coefficient-scope">provisional scope entry</a> explains why the positive part cannot simply be dropped for arbitrary finite $\eta$.</p>

## The critical magnetization bound {#section-amplitude}

<a id="tag-C2V4" data-assertion="proposition" data-title="The completed bootstrap makes the triangle differential coefficient positive"></a>
<p>In sufficiently large nearest-neighbour dimensions,</p>
<div class="math-display">$$\kappa_*(p_c)=\frac1{2e}+O(1/d),\qquad
\frac13\sqrt\gamma\le M(p_c,\gamma)\le\sqrt{12\gamma}\quad(0\le\gamma\le1).$$</div>
<p>The constants and the dimension threshold are independent of $\gamma$.</p>
<p><em>Proof.</em> A nontrivial triple convolution has at least one nonzero displacement. Applying $\tau(x)\le\widetilde\tau(x)$ on such a displacement and summing gives $\eta\le3T$. <a href="/tag/F7N7/">F7N7</a> therefore supplies $\eta_c=O(1/d)$ and $j_c=qp_c=1+O(1/d)$. Consequently</p>
<div class="math-display">$$\binom q2p_c^2=\tfrac12+O(1/d),\qquad
(1-p_c)^{q-2}=\exp\{(q-2)\log(1-j_c/q)\}=e^{-1}[1+O(1/d)].$$</div>
<p>All remaining factors in $\kappa_*$ tend to one or zero as appropriate, proving its stated asymptotic. Enlarge the dimension threshold so that $\eta_c<1$ and $\kappa_*(p_c)\ge2/11$.</p>
<p>Divide OB0K by $M>0$. Since $\theta(p_c)=0$, integration from a positive field down to zero gives</p>
<div class="math-display">$$M(p_c,\gamma)^2\le\frac2{\kappa_*(p_c)}\log\frac1{1-\gamma}
\le\frac{11\gamma}{1-\gamma}.$$</div>
<p>This is at most $12\gamma$ for $\gamma\le1/12$. For larger $\gamma$, use $M\le1\le\sqrt{12\gamma}$. The lower bound follows from <a href="/tag/ZDVK/">ZDVK</a> and <a href="/tag/G192/">G192</a>: critical susceptibility is infinite, and the scalar constant $1+qp_c/(1-p_c)$ is bounded by nine in sufficiently large dimensions. The endpoints follow by continuity.</p>

## From the generating function to the cluster tail {#section-tails}

<a id="tag-ZK0V" data-assertion="proposition" data-title="Two square-root generating-function bounds give two square-root tail bounds"></a>
<p>Let $N$ be a positive integer-valued random variable and $m(\gamma)=\mathbb E[1-(1-\gamma)^N]$. If $A\sqrt\gamma\le m(\gamma)\le B\sqrt\gamma$ for $0\le\gamma\le1$, where $0<A\le B<\infty$, then for every $n\ge1$,</p>
<div class="math-display">$$\frac{A^2}{4eB\sqrt n}\le\mathbb P(N\ge n)\le\frac{B}{(1-e^{-1})\sqrt n}.$$</div>
<p><em>Proof.</em> On $\{N\ge n\}$, $1-(1-1/n)^N\ge1-e^{-1}$, proving the upper bound. For $0<\gamma\le\widetilde\gamma\le1$, split at $N<n$. Since $1-(1-\gamma)^l\le\gamma l$ and</p>
<div class="math-display">$$\widetilde\gamma l\le e^{\widetilde\gamma l}[1-(1-\widetilde\gamma)^l],$$</div>
<p>one obtains</p>
<div class="math-display">$$\mathbb P(N\ge n)\ge m(\gamma)-\frac\gamma{\widetilde\gamma}e^{\widetilde\gamma n}m(\widetilde\gamma).$$</div>
<p>The elementary inequality used above follows from $e^t-1\ge t$ and $(1-\widetilde\gamma)^l\le e^{-\widetilde\gamma l}$. Take $\widetilde\gamma=1/n$ and $\gamma=A^2/(4e^2B^2n)$. The right side is at least $A^2/(4eB\sqrt n)$. For $n=1$ the same calculation is valid with $\widetilde\gamma=1$; alternatively use $\mathbb P(N\ge1)=1$ and $A\le m(1)=1\le B$.</p>
<p>In particular, C2V4 yields dimension-uniform critical cluster-tail constants. The numerical lower constant obtained here is $1/(36e\sqrt{12})$; the smaller $1/360$ also works. The <a href="/errata/heydenreich-hofstad/#critical-tail-constant">provisional arithmetic entry</a> distinguishes this complete repair from the larger constant claimed at the end of the manuscript calculation.</p>

## Extrapolation along a valid level set {#section-extrapolation}

<p>Write $F(p,h)=M(p,1-e^{-h})$. The inverse in $h$ exists only for levels $m\in(\theta(p),1)$. This domain matters when the final parameter is supercritical.</p>
<a id="tag-JR88" data-assertion="theorem" data-title="A critical square-root bound extrapolates to a linear density bound"></a>
<p>Suppose $0<a<b<1$ and $F(a,h)\le B\sqrt h$ for every $h>0$. Put $L=q/(1-b)$. Then, with $m=F(b,h)$,</p>
<div class="math-display">$$m^2\le B^2[h+L(b-a)m],\qquad
\theta(b)\le B^2L(b-a).$$</div>
<p><em>Proof.</em> G192 and $F_h=(1-\gamma)M_\gamma$ give $0\le F_p\le LFF_h$ almost everywhere on $[a,b]\times(0,\infty)$. At a fixed positive $h$, $F$ is locally Lipschitz and $F_h>0$. For completeness, the finite-cluster formula</p>
<div class="math-display">$$F_h(p,h)=\sum_{n\ge1}ne^{-hn}\mathbb P_p(|C_0|=n)$$</div>
<p>is jointly continuous: each finite-size probability depends on finitely many bonds, and the tail is uniformly bounded by $\sup_{n>R}ne^{-hn}$ on compact positive-field intervals. The singleton event gives a positive lower bound on $F_h$ on each compact subset of $p<1,h>0$.</p>
<p>Fix the level $m=F(b,h)$. It is strictly greater than $\theta(b)$ and hence than or equal to every lower endpoint $\theta(p)$ for $a\le p\le b$. Thus the level has a unique positive inverse $H(p,m)$ throughout this interval. Locally the change of coordinates $(p,h)\mapsto(p,F(p,h))$ is bi-Lipschitz. The almost-everywhere chain rule and Fubini imply, for almost every nearby level,</p>
<div class="math-display">$$0\le-H_p(p,m)=F_p(p,H(p,m))/F_h(p,H(p,m))\le Lm$$</div>
<p>for almost every $p$. Integrate in $p$ and then use continuity in $m$ to extend the bound to the chosen level. This avoids restricting a two-dimensional almost-everywhere inequality to a potentially exceptional curve. Since $H(b,m)=h$, it gives $H(a,m)\le h+L(b-a)m$. Monotonicity in the field and the assumed bound at $a$ yield</p>
<div class="math-display">$$m=F(a,H(a,m))\le F(a,h+L(b-a)m)\le B\sqrt{h+L(b-a)m}.$$</div>
<p>Square and let $h\downarrow0$. If $\theta(b)>0$, divide the resulting inequality by it; if it is zero, the density conclusion is immediate.</p>

## Dimension-uniform scaling of the mean-field bounds {#section-exponents}

<a id="tag-74SS" data-assertion="theorem" data-title="Critical square-root tails and linearly scaled supercritical density in high dimensions"></a>
<p>There are absolute $d_0,c,C>0$ such that, for every $d\ge d_0$, every integer $n\ge1$ and every $p_c\le p\le1$,</p>
<div class="math-display">$$\frac c{\sqrt n}\le\mathbb P_{p_c}(|C_0|\ge n)\le\frac C{\sqrt n},\qquad
c\min\{2d(p-p_c),1\}\le\theta(p)\le C\min\{2d(p-p_c),1\}.$$</div>
<p>Thus the cluster-tail exponent is two and the density exponent is one in the bounded-ratio sense at each such dimension. A bound with dimension-independent constants multiplying the unscaled $p-p_c$ is not asserted.</p>
<p><em>Proof.</em> Critical nonpercolation makes $|C_0|$ finite almost surely. Apply C2V4 and ZK0V for the tail. For the density, choose $d_0$ so that $qp_c\le2$ and $p_c+1/q<1/2$. If $p_c<p\le p_c+1/q$, C2V4 gives $F(p_c,h)\le\sqrt{12h}$, while $L=q/(1-p)\le2q$. JR88 gives $\theta(p)\le24q(p-p_c)$. The probability-parameter sharpness bound <a href="/tag/JQLC/">JQLC</a> gives</p>
<div class="math-display">$$\theta(p)\ge\frac{p-p_c}{p}\ge\tfrac13q(p-p_c)$$</div>
<p>on the same interval. Above $p_c+1/q$, monotonicity gives $\theta(p)\ge1/3$, while $\theta(p)\le1$. These bounds also include $p=1$; at $p=p_c$ use $\theta(p_c)=0$. Taking the smaller lower constant and the larger upper constant from the tail and density estimates proves the simultaneous statement.</p>
<p>The <a href="/errata/heydenreich-hofstad/#density-dimension-scale">provisional normalization entry</a> records the dimension factor: the extrapolation argument bounds density by a constant times $2d(p-p_c)$. For a fixed dimension it yields the usual linear bound with a constant depending on $d$. It does not prove a sharp asymptotic amplitude. The <a href="/coverage/sources/heydenreich-hofstad-2017-green-free/">Chapter 9 map</a> separates those stronger assertions from the bounds proved here.</p>

## An explicit susceptibility comparison {#section-explicit-susceptibility}

<p>The <a href="/tag/7GNW/">explicit bootstrap bound</a> supplies a common numerical dimension range for the mean-field conclusions. Throughout the remainder of this article, $d\ge10^{11}$ and $q=2d$. This range is deliberately coarse; it is not a source claim about the least dimension in which these estimates hold.</p>

<a id="tag-YT0O" data-assertion="proposition" data-title="An explicit small-triangle and susceptibility bound in the quantified bootstrap range"></a>
<p>Put $v_d=189/d$. Then $\eta_c\le v_d<10^{-6}$, and for every $0\le p<p_c$,</p>
<div class="math-display">$$\frac1{q(p_c-p)}\le\chi(p)
\le\frac1{q(1-v_d)\log((1-p)/(1-p_c))}
\le\frac1{q(1-v_d)(p_c-p)}.$$</div>
<p>In particular, $\chi(p_c/2)<3$.</p>
<p><em>Proof.</em> Write $\widetilde\tau=qp_cD*\tau_c$. In each nontrivial triple-convolution summand at least one of its three displacements is nonzero. On that displacement, the first-step inequality gives $\tau_c(y)\le\widetilde\tau(y)$. Summing the three possible choices bounds $\eta_c$ by $3T_c$. The critical passage in 7GNW gives $T_c\le63/d$, proving the first assertion. In particular the neighbouring triangle satisfies $\delta\le v_d<1$. Apply <a href="/tag/0Y4K/">0Y4K</a>, decreasing its coefficient $1-\delta$ to $1-v_d$. At $p=p_c/2$, use $qp_c\ge1$ to obtain $\chi(p_c/2)\le2/(1-v_d)<3$.</p>

## Explicit critical tails and density bounds {#section-explicit-mean-field}

<a id="tag-E5ZR" data-assertion="theorem" data-title="Explicit mean-field constants throughout the quantified dimension range"></a>
<p>For every $d\ge10^{11}$, the differential coefficient in OB0K satisfies $\kappa_*(p_c)\ge2/11$. Consequently, for $0\le\gamma\le1$, every integer $n\ge1$ and every $p_c\le p\le1$,</p>
<div class="math-display">$$\begin{aligned}
\frac13\sqrt\gamma&\le M(p_c,\gamma)\le\sqrt{12\gamma},\\
\frac1{360\sqrt n}&\le\mathbb P_{p_c}(|C_0|\ge n)\le\frac6{\sqrt n},\\
\frac13\min\{q(p-p_c),1\}&\le\theta(p)\le24\min\{q(p-p_c),1\}.
\end{aligned}$$</div>
<p><em>Proof.</em> Set $u=10^{-6}$ and $j_c=qp_c$. The explicit bootstrap and YT0O give</p>
<div class="math-display">$$1\le j_c\le\frac{1001}{1000},\qquad
p_c\le u,\qquad q^{-1}\le u,\qquad\eta_c\le u.$$</div>
<p>For $0\le t<1$, $\log(1-t)\ge-t/(1-t)$. Hence</p>
<div class="math-display">$$(1-p_c)^{q-2}\ge(1-p_c)^q
\ge\exp\!\left(-\frac{j_c}{1-p_c}\right)
\ge e^{-501/500}>\frac{11}{30}.$$</div>
<p>The numerical comparison can be checked without decimal approximations. The exponential series, with its tail from $1/6!$ bounded by a geometric series of ratio $1/7$, gives $e<87/32$. Also $e^{1/500}\le(1-1/500)^{-1}=500/499$, so $e^{501/500}<(87/32)(500/499)<30/11$.</p>
<p>Furthermore $\binom q2p_c^2=(1-q^{-1})j_c^2/2\ge(1-u)/2$. Since $\eta_c\le u<1$, the expression in braces in OB0K is at least $(1-u)^2-u$. It follows that the bracket multiplying $j_c$ there is at least</p>
<div class="math-display">$$\frac{11}{60}(1-u)\bigl[(1-u)^2-u\bigr]-2u
>\frac2{11}.$$</div>
<p>This bracket is positive, so $j_c\ge1$ proves the asserted lower bound on $\kappa_*(p_c)$.</p>
<p>Critical clusters are finite by 7GNW. Divide OB0K by $M>0$ and integrate from zero field to get $M^2\le11\log(1/(1-\gamma))$. For $\gamma\le1/12$, this is at most $12\gamma$; for larger fields use $M\le1$. The lower bound follows from ZDVK and G192 exactly as in C2V4: critical susceptibility is infinite and $1+j_c/(1-p_c)<3<9$. The endpoints follow by continuity.</p>
<p>ZK0V now gives the tail bounds with lower constant $1/(36e\sqrt{12})$ and upper constant $\sqrt{12}/(1-e^{-1})$. The elementary comparisons $8/3<e<87/32$ and $\sqrt{12}<7/2$ make these at least $1/360$ and at most six, respectively.</p>
<p>Finally $p_c+1/q<1/2$. For $p_c<p\le p_c+1/q$, the critical estimate gives $F(p_c,h)\le\sqrt{12h}$. JR88, with $L=q/(1-p)\le2q$, yields $\theta(p)\le24q(p-p_c)$. Sharpness gives $\theta(p)\ge(p-p_c)/p\ge q(p-p_c)/3$, because $qp\le j_c+1<3$. Above this interval use monotonicity for the lower bound and $\theta\le1$ for the upper bound. Critical nonpercolation handles $p=p_c$.</p>

## A quantitative subcritical cutoff {#section-explicit-cutoff}

<p>Write $N_p=|C_0|$ and $\chi=\chi(p)$. The same dimension bound also makes the moment and volume-scale argument numerical.</p>

<a id="tag-9TAI" data-assertion="theorem" data-title="Explicit subcritical second-moment and cluster-tail bounds"></a>
<p>For $d\ge10^{11}$ and $p_c/2\le p<p_c$,</p>
<div class="math-display">$$\frac13\chi^3\le\mathbb E_pN_p^2\le\chi^3.$$</div>
<p>For every integer $n\ge1$,</p>
<div class="math-display">$$\mathbb P_p(N_p\ge n)\le\frac8{\sqrt n}
\exp\!\left[-\frac{n}{4\chi^2}\right],\qquad
\mathbb P_p(N_p\ge n)\ge\frac1{139968\sqrt n}quad\left(n\le\frac{\chi^2}{6}\right).$$</div>
<p>In particular, the fractional-moment regimes and moment-ratio conclusions of <a href="/tag/76EV/">76EV</a> hold throughout this explicit dimension range, with constants independent of $d,p$ at each fixed moment order.</p>
<p><em>Proof.</em> In the intensity parameter $\beta=-\log(1-p)$, the small-triangle derivative bound gives $d\chi/d\beta\ge q(1-v_d)\chi^2$ almost everywhere. The exploration-score inequality <a href="/tag/4GNM/">4GNM</a> implies</p>
<div class="math-display">$$\mathbb E_pN_p^2\ge\beta q(1-v_d)^2\chi^3
\ge\tfrac12(1-10^{-6})^2\chi^3>\tfrac13\chi^3.$$</div>
<p>Here $\beta\ge p\ge p_c/2$ and $qp_c\ge1$. Tree-graph bounds give the upper estimate and all higher moments. Continuity of the first and second moments on compact subcritical intervals, as in the proof of 36ZQ, extends the lower estimate from almost every parameter to every parameter.</p>
<p>Apply <a href="/tag/2DZD/">2DZD</a> with $\alpha=1/3$. If $a(p)=\mathbb E_pN_p^2/\chi(p)$, then</p>
<div class="math-display">$$\frac13\chi(p)^2\le a(p)\le\chi(p)^2,\qquad
\mathbb P_p\bigl(a(p)/2\le N_p\le216\chi(p)^2\bigr)
\ge\frac1{46656\chi(p)}.$$</div>
<p>Put $p_0=p_c/2$. When $a(p_0)/2\le n\le\chi(p)^2/6$, continuity supplies $p'\in[p_0,p]$ with $a(p')=2n$. Thus $\chi(p')\le\sqrt{6n}\le3\sqrt n$, and the band bound followed by monotonicity gives the asserted lower tail. If $n<a(p_0)/2$, use the band at $p_0$ and $\chi(p_0)<3$ instead. No monotonicity of the ratio $a(p)$ is needed.</p>
<p>For the upper tail, E5ZR and monotonicity give $\mathbb P_p(N_p\ge n)\le6/\sqrt n$. The weighted exponential estimate <a href="/tag/0BQB/">0BQB</a> gives the separate bound $(\sqrt2\chi/n)e^{-n/(4\chi^2)}$. For $n\ge\chi^2$, its prefactor is at most $\sqrt2/\sqrt n$. For $n\le\chi^2$, multiply the critical bound by $e^{1/4}e^{-n/(4\chi^2)}\ge1$; since $e^{1/4}<4/3$, the constant eight suffices. These two ranges prove the upper estimate. Tail summation as in 76EV gives its power, logarithmic and bounded-moment regimes, now using the lower cutoff $\chi^2/6$.</p>
<p>These results quantify the existing proof chain. They do not establish a sharp tail profile, an asymptotic moment ratio or the corresponding implications from an arbitrary finite triangle. All earlier tagged statements and provisional source corrections are preserved.</p>

<details><summary>Exact comparisons for the constants</summary>
<p>This standard-library Python certificate checks the rational comparisons used above. The exponential series and the preceding analytic arguments justify the quantities being compared; no floating-point evaluation is used.</p>
<pre id="explicit-mean-field-certificate-code"><code>#!/usr/bin/env python3
# SPDX-License-Identifier: Apache-2.0
&quot;&quot;&quot;Rational comparisons in YT0O, E5ZR and 9TAI; analytic inputs are proved in the wiki.&quot;&quot;&quot;
from fractions import Fraction as F
from math import factorial
import json

d = 10**11
q = 2*d
j = F(1001, 1000)
u = F(1, 10**6)
assert F(189, d) &lt; u
assert j/q &lt; u and F(1, q) &lt; u
assert j/(1-u) &lt; F(501, 500)

# e: retain the terms through 1/5!, then dominate the tail from 1/6!.
e_upper = sum(F(1, factorial(k)) for k in range(6))
e_upper += F(1, factorial(6))/(1-F(1, 7))
assert e_upper &lt; F(87, 32)
assert F(87, 32)*F(500, 499) &lt; F(30, 11)

# The coefficient bracket is positive before multiplying by j_c&gt;=1.
kappa_lower = F(11, 60)*(1-u)*((1-u)**2-u)-2*u
assert kappa_lower &gt; F(2, 11)
assert 1+j/(1-u) &lt; 3
assert sum(F(1, factorial(k)) for k in range(5)) &gt; F(8, 3)
assert 12 &lt; F(7, 2)**2
assert 36*F(87, 32)*F(7, 2) &lt; 360
assert F(7, 2)/(1-F(3, 8)) &lt; 6
assert (j+1)/q &lt; F(1, 2) and j+1 &lt; 3

# Uniform subcritical moment and cutoff constants.
assert F(2)/(1-u) &lt; 3
assert F(1, 2)*(1-u)**2 &gt; F(1, 3)
alpha = F(1, 3)
assert 24/alpha**2 == 216
assert alpha**4/576 == F(1, 46656)
assert F(1, 46656)/3 == F(1, 139968)
assert 6/(1-F(1, 4)) == 8
print(json.dumps({&quot;result&quot;: &quot;passed&quot;, &quot;arithmetic&quot;: &quot;exact rational&quot;,
                  &quot;dimension_at_least&quot;: d, &quot;triangle_upper&quot;: str(F(189, d)),
                  &quot;kappa_lower_above&quot;: &quot;2/11&quot;,
                  &quot;critical_tail_constants&quot;: [&quot;1/360&quot;, &quot;6&quot;],
                  &quot;density_constants&quot;: [&quot;1/3&quot;, &quot;24&quot;],
                  &quot;second_moment_lower&quot;: &quot;1/3&quot;,
                  &quot;subcritical_tail_constants&quot;: [&quot;1/139968&quot;, &quot;8&quot;],
                  &quot;lower_tail_cutoff_multiple&quot;: &quot;1/6&quot;}, indent=2))
</code></pre>
</details>
