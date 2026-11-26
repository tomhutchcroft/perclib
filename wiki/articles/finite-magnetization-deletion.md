---
{
  "id": "finite-magnetization-deletion",
  "title": "Finite magnetization and cluster deletion",
  "subtitle": "Signed deletion losses and the scope of the triangle coefficient",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Conditioning on green-connected vertices controls a signed deletion loss. A two-cluster estimate and the last pivotal bond then give the finite magnetization inequality with its triangle-size restriction explicit.",
  "context": [
    "Bonds and vertex marks are independent on a finite simple graph.",
    "The deletion estimate permits nonuniform bond probabilities; the triangle coefficient uses a connected vertex-transitive graph with a common bond probability.",
    "The early preprint and the later author manuscript have different triangle coefficients."
  ],
  "related": [
    "green-free-triangle",
    "finite-triangle-window",
    "finite-supercritical-clusters",
    "finite-window-susceptibility"
  ],
  "sourceIds": [
    "borgs-chayes-finite-window",
    "heydenreich-hofstad"
  ],
  "aliases": [
    "finite green-free BK",
    "magnetization triangle coefficient",
    "last pivotal bond",
    "signed cluster deletion"
  ],
  "prototypeUses": []
}
---

## Deletion with the green-free condition {#section-deletion}

<p>Let $\mathcal G$ be the set of vertices marked green, each with probability $\gamma$, independently of the bonds and of the other marks. On a finite simple graph write</p>
<div class="math-display">$$T(x,y)=\mathbb P(x\leftrightarrow y),\qquad \tau_\gamma(x,y)=\mathbb P(x\leftrightarrow y,\ x\not\leftrightarrow\mathcal G).$$</div>
<p>For $A\subseteq V$, let $\tau_\gamma^A(x,y)$ be the same probability in the graph induced by $V\setminus A$, with value zero if an endpoint is removed. Both the connection and the absence of a green connection are evaluated in that smaller graph.</p>

<a id="tag-G9X2" data-assertion="proposition" data-title="A signed green-free deletion loss on any finite independent bond graph"></a>
<p>For arbitrary independent bond probabilities and every $A\subseteq V$,</p>
<div class="math-display">$$\tau_\gamma(x,y)-\tau_\gamma^A(x,y)\le\sum_{z\in A}\tau_\gamma(x,z)T(z,y).$$</div>
<p>The left side need not be nonnegative. On a single edge with endpoints $x,z$, bond probability $p$ and $A=\{z\}$, it equals $-p\gamma(1-\gamma)$ when $y=x$.</p>
<p><em>Proof.</em> Couple the full and deleted graphs using the same bonds and marks. A full green-free connection that fails to be a deleted green-free connection must lose its connecting path: deleting vertices cannot create a green connection. Thus the difference is at most the probability of a full green-free connection for which every path from $x$ to $y$ meets $A$. Split a simple such path at a vertex $z\in A$.</p>
<p>For the resulting two disjoint path events, retain the green-free condition on the first factor. To justify this, reveal the set of vertices connected to $\mathcal G$. Conditional on this set, the outside vertices have no marks, all crossing bonds are closed, and bonds entirely outside retain their independent product law. BK in that induced graph bounds the two-path probability by the product of the two connection probabilities. The second is at most $T(z,y)$ by coupling with the full graph. Averaging the first gives $\tau_\gamma(x,z)$. Sum over $z\in A$. Zero-length paths cover coincident endpoints, including an endpoint in $A$.</p>
<p>For the single-edge example, the full probability is $(1-\gamma)(1-p\gamma)$ and the deleted probability is $1-\gamma$. This also explains why one first bounds the deletion loss by a nonnegative expression before multiplying it by a larger indicator.</p>

## Two marked clusters after removing a vertex {#section-two-clusters}

<p>For the rest of the article let the graph be finite, connected, simple and vertex-transitive, of degree $m\ge1$. Bonds open with probability $p<1$. Put</p>
<div class="math-display">$$M=\mathbb E_p[1-(1-\gamma)^{|C_o|}],\qquad \chi_\gamma=\mathbb E_p[|C_o|(1-\gamma)^{|C_o|}]=(1-\gamma)M_\gamma,$$</div>
<div class="math-display">$$\eta=\max_{x,y\in V}\{T^3(x,y)-\mathbf1_{\{x=y\}}\},\qquad b=(1-\eta)_+.$$</div>
<p>Here $t_+=\max(t,0)$ and matrix powers sum over $V$. In particular, $\eta\ge0$ and $T^3(x,y)\le\eta$ when $x\ne y$. Transitivity makes $M$ independent of the root.</p>

<a id="tag-CHWM" data-assertion="proposition" data-title="Two disjoint marked clusters retain a quadratic-minus-linear triangle coefficient"></a>
<p>Delete a vertex $o$, and let $e,f$ be distinct neighbours of $o$. In the resulting graph,</p>
<div class="math-display">$$\mathbb P(C_e\cap C_f=\varnothing,\ e\leftrightarrow\mathcal G,\ f\leftrightarrow\mathcal G)\ge M^2(b^2-\eta).$$</div>
<p>Consequently, if $o\Leftrightarrow\mathcal G$ denotes two edge-disjoint open paths from $o$ to distinct green vertices, including their distinct terminal marks, then</p>
<div class="math-display">$$\mathbb P(o\Leftrightarrow\mathcal G)\ge\binom m2p^2(1-p)^{m-2}M^2(b^2-\eta).$$</div>
<p><em>Proof.</em> Write $M^-(x)$ for the green-connection probability after deleting $o$. A connection lost by this deletion has disjoint witnesses from $x$ to $o$ and from $o$ to a mark. Hence BK and $T(x,o)\le T^3(x,o)\le\eta$ give</p>
<div class="math-display">$$M^-(x)\ge M[1-T(x,o)]\ge Mb\qquad(x\ne o).$$</div>
<p>Reveal $C_e=A$ in the graph with $o$ deleted. Conditional on $A$ and its marks, the remaining bonds and marks retain their product law. Deleting $A$ can remove a marked connection from $f$ only through a vertex $y\in A$. BK bounds this loss by $M\sum_{y\in A}T(f,y)$. Multiplying by the event that $C_e$ is marked, then summing over $A$, shows that the probability in the statement is at least</p>
<div class="math-display">$$M^-(e)M^-(f)-M\sum_yT(f,y)\mathbb P^-(e\leftrightarrow y,\ e\leftrightarrow\mathcal G).$$</div>
<p>A connected triple consisting of $e,y$ and a green vertex has a branch vertex $w$. Its three disjoint witnesses give</p>
<div class="math-display">$$\mathbb P^-(e\leftrightarrow y,\ e\leftrightarrow\mathcal G)\le M\sum_wT(e,w)T(w,y).$$</div>
<p>The subtracted term is therefore at most $M^2T^3(e,f)\le M^2\eta$. The two nonnegative lower bounds $M^-(e),M^-(f)\ge Mb$ give the first conclusion. For the second, force precisely the two root bonds to $e,f$ to be open, with all other root bonds closed. The events for different unordered neighbour pairs are disjoint. Sum their probabilities. If $m=1$, there is no pair and the bound is zero.</p>

## Cutting at the last pivotal bond {#section-cutting}

<a id="tag-60X1" data-assertion="theorem" data-title="A finite triangle differential inequality with a valid coefficient for every triangle size"></a>
<p>For $0\le p<1$ and $0\le\gamma\le1$,</p>
<div class="math-display">$$M\ge\kappa_*(p)M^2\chi_\gamma=\kappa_*(p)(1-\gamma)M^2M_\gamma,$$</div>
<p>where</p>
<div class="math-display">$$\kappa_*(p)=mp\left[\binom m2p^2(1-p)^{m-2}\{(1-\eta)_+^2-\eta\}-p-\eta\right].$$</div>
<p>When $\eta\le1$ the positive part may be omitted. When $\eta\ge1$ this coefficient is nonpositive and the inequality is trivial.</p>
<p><em>Proof.</em> The cases $p=0$ or $\gamma\in\{0,1\}$ are immediate. Otherwise let $F_{u,v}$ be the event that $\{u,v\}$ is open and pivotal for $o\leftrightarrow\mathcal G$, oriented towards $v$, and $v\Leftrightarrow\mathcal G$. At most one such oriented edge occurs. Indeed the pivotal edges are ordered along every path to a mark, and two disjoint marked arms can occur only beyond the last of them. Thus $M\ge\sum_{(u,v)}\mathbb P(F_{u,v})$.</p>
<p>Close $\{u,v\}$ and let $A$ be the cluster of $v$ in that configuration; let $I^-_{u,v}$ indicate a double marked connection from $v$ there. On $\{A=S\}$ the event $I^-_{u,v}$ involves only bonds touching $S$, other than $\{u,v\}$, and marks in $S$. The outside connection from $o$ to $u$ with no outside green connection involves disjoint coordinates. Independence gives the cutting identity</p>
<div class="math-display">$$\mathbb P(F_{u,v})=p\,\mathbb E[\tau_\gamma^A(o,u)I^-_{u,v}].$$</div>
<p>Add and subtract the unrestricted two-point function and unrestricted double-connection indicator. Summing gives $X_1-X_2-X_3$, where</p>
<div class="math-display">$$X_1=mp\chi_\gamma\mathbb P(o\Leftrightarrow\mathcal G),\qquad X_2\le mp^2\chi_\gamma M^2.$$</div>
<p>The bound for $X_2$ follows because a double marked connection destroyed by closing $\{u,v\}$ supplies disjoint witnesses for that open bond and marked connections from both endpoints. The two-cluster bound controls $X_1$.</p>
<p>For $X_3$, first apply the signed deletion estimate with $A$ fixed. Its upper bound is nonnegative, so one may then enlarge $I^-_{u,v}$ to the unrestricted double-connection indicator. If $y\in A$ and $v\Leftrightarrow\mathcal G$, follow a path from $y$ to its first intersection $w$ with two disjoint green arms from $v$. Split the arm containing $w$. This produces four disjoint witnesses, including distinct terminal marks, and gives</p>
<div class="math-display">$$\mathbb P(y\in A,\ v\Leftrightarrow\mathcal G)\le M^2\sum_wT(v,w)T(w,y).$$</div>
<p>Consequently</p>
<div class="math-display">$$X_3\le pM^2\sum_y\tau_\gamma(o,y)\sum_{(u,v),w}T(y,u)T(v,w)T(w,y)\le mp\eta\chi_\gamma M^2.$$</div>
<p>For the last inequality, the inner sum is independent of $y$ by transitivity. Its average over $y$ is $N^{-1}\sum_{(u,v)}T^3(u,v)\le m\eta$, since every edge has distinct endpoints. This finite averaging argument requires no Cayley-graph or edge-transitivity assumption. Combining the three bounds proves the claim.</p>
<p>The finite-window field estimate <a href="/tag/KQN9/">KQN9</a> uses precisely this coefficient in its small-triangle range. The lattice version is <a href="/tag/OB0K/">OB0K</a>.</p>

## Why the coefficient needs a scope restriction {#section-scope}

<a id="tag-EHH4" data-assertion="proposition" data-title="The unrestricted polynomial magnetization coefficient fails on the complete graph with four vertices"></a>
<p>On $K_4$ at $p=\gamma=1/2$,</p>
<div class="math-display">$$\eta=\frac{549}{64},\qquad M=\frac{437}{512},\qquad \chi_\gamma=\frac{21}{64}.$$</div>
<p>If $(1-\eta)_+^2$ is replaced by $(1-\eta)^2$ in the coefficient, the resulting value is $\kappa_{\mathrm{poly}}=908385/65536$, and</p>
<div class="math-display">$$\frac{\kappa_{\mathrm{poly}}M^2\chi_\gamma}{M}=\frac{8336249145}{2147483648}>1.$$</div>
<p>Thus the unqualified polynomial inequality is false.</p>
<p><em>Proof.</em> The root cluster has sizes $1,2,3,4$ with probabilities $4/32,3/32,6/32,19/32$. The first follows by closing the three root bonds. For size two, choose its other vertex and require its internal bond open and four boundary bonds closed. For size three, choose the two other vertices, require their triangle to be connected, an event of probability $1/2$, and close its three boundary bonds. The remaining probability gives size four. Summing yields $\chi=13/4$, $M=1-\mathbb E2^{-|C_o|}=437/512$ and $\chi_\gamma=\mathbb E[|C_o|2^{-|C_o|}]=21/64$.</p>
<p>The <a href="/tag/R2Y7/">complete-graph formula</a> with off-diagonal two-point function $3/4$ gives $T^3(x,y)=549/64$ for $x\ne y$ and $T^3(x,x)-1=243/32$. Their maximum is $549/64$. Substitution proves the displayed ratio.</p>
<p>This is a <a href="/errata/borgs-chayes-finite-window/#magnetization-coefficient-scope">provisional scope correction</a> to the September 2004 author manuscript. Adding $\eta\le1$ leaves its intended small-triangle application unchanged; the positive-part formula gives a statement valid at every $p<1$.</p>

## Integrating a positive coefficient {#section-field}

<a id="tag-NBKI" data-assertion="corollary" data-title="A positive finite triangle coefficient gives field and root-tail upper bounds"></a>
<p>At a fixed $p<1$ for which $\kappa_*(p)>0$,</p>
<div class="math-display">$$M(p,\gamma)^2\le\min\left\{1,\frac2{\kappa_*(p)}\log\frac1{1-\gamma}\right\}\qquad(0\le\gamma<1).$$</div>
<p>For every integer $k\ge2$,</p>
<div class="math-display">$$\mathbb P_p(|C_o|\ge k)\le\min\left\{1,\frac{2}{(1-e^{-1})\sqrt{\kappa_*(p)k}}\right\}.$$</div>
<p><em>Proof.</em> For $0<\gamma<1$, $M>0$. Divide the differential inequality by $M$ and integrate $2MM_\gamma\le2/[\kappa_*(p)(1-\gamma)]$ from field zero, where $M=0$ because the graph is finite. Also $M\le1$. At field $1/k$, a cluster of size at least $k$ is marked with probability at least $1-e^{-1}$. Use $\log(1/(1-1/k))\le2/k$ for $k\ge2$ to obtain the tail bound. The excluded endpoints have $M(p,1)=1$ and $\mathbb P(|C_o|\ge1)=1$.</p>
<p>For the explicit reference-point hypotheses of KQN9, its calculation gives $\kappa_*(p_c)\ge1/12$. Thus this integral recovers its upper field bound. No infinite-volume or zero-field interchange is needed here.</p>

## Comparing the two author versions {#section-versions}

<p>The <a href="https://arxiv.org/pdf/math/0401069">early preprint</a>, dated 6 May 2003 and posted in January 2004, defines the triangle maximum without removing the diagonal contribution and uses a cubic factor in the double-green estimate. Its subtraction step does not justify that factor. The <a href="https://www.microsoft.com/en-us/research/wp-content/uploads/2016/11/Random-Subgraphs-of-Finite-Graphs-I-The-Scaling-Window-Under-the-Triangle-Condition.pdf">14 September 2004 author manuscript</a> already removes the diagonal, retains the upper bound on the subtracted magnetization, changes the coefficient to $(1-\eta)^2-\eta$, and supplies the missing branch-vertex sum explicitly. The <a href="/errata/borgs-chayes-finite-window/#early-magnetization-coefficient">historical entry</a> credits that revision rather than presenting those defects as new journal errors.</p>
<p>The remaining sign issue is separate: multiplying the lower bounds $M^-(x)\ge M(1-\eta)$ requires $1-\eta\ge0$. The positive part handles it, and the complete-graph calculation shows that an unrestricted polynomial statement cannot be retained. These are written finite-graph proofs. The publisher's typeset version and visual PDF layout have not been compared.</p>
