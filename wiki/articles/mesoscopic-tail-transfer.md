---
{
  "id": "mesoscopic-tail-transfer",
  "title": "From cutoff mass to a full volume tail",
  "subtitle": "Small-cluster negligibility and a quantitative ghost comparison",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "Uniform negligibility of small cutoff clusters makes the cutoff-to-full comparison contractive. First and second moment bounds then yield two-sided power bounds for the full cluster tail, without assuming convergence to a limiting cluster law.",
  "context": ["Cutoff sizes $X_r$ are nonnegative with finite first and second moments.", "The cutoff mass scale is $r^\\kappa$, with $0<\\alpha<\\kappa$ and mean of order $r^\\alpha$.", "Negligibility and the cutoff-to-full comparison are explicit inputs, not consequences of moment orders alone."],
  "related": ["cutoff-hydrodynamics", "cutoff-localization", "size-biased-laws", "ghost-fields", "regular-variation"],
  "sourceIds": ["hutchcroft-lrp-3", "hutchcroft-book", "hutchcroft-lrp-2", "perclib-reciprocal-ode", "perclib-mesoscopic-negligibility", "perclib-mass-transport-tuple"],
  "aliases": ["mesoscopic negligibility", "truncated first moment", "tail extraction", "low-dimensional volume tail"],
  "prototypeUses": []
}
---

## The uniform input {#section-input}

<a id="tag-QMN5" data-assertion="definition" data-title="Mesoscopic negligibility relative to the cutoff mass scale"></a>
<p>Let $X_r\geq0$ have finite positive mean $m_1(r)$, for all sufficiently large $r$, and let $\kappa&gt;0$. Mesoscopic negligibility at scale $r^\kappa$ means</p>
<div class="math-display">$$\lim_{\delta\downarrow0}\limsup_{r\to\infty}\frac{\mathbb E\min(X_r,\delta r^\kappa)}{m_1(r)}=0.$$</div>
<p>The large-scale limit is taken before the small-$\delta$ limit. For each fixed $r$, sending $\delta$ to zero would give a trivial assertion and would provide no uniform control on the family. The truncated expectation includes a contribution $\delta r^\kappa$ from every cluster above that size; it is not just $\mathbb E[X_r\mathbf1_{\{X_r\leq\delta r^\kappa\}}]$.</p>

## The finite-model truncated differential inequality {#section-finite-russo}

<a id="tag-MIJ7" data-assertion="proposition" data-title="Truncated Russo bound on a finite transitive bond model"></a>
<p>Let $V$ be a finite nonempty vertex set, and let a group act transitively on $V$. For each unordered pair of distinct vertices, let $\lambda_{xy}(t)\geq0$ be continuously differentiable on an open interval $I$, invariant under the group, with $\lambda_{xy}'(t)\geq0$. Open the pairs independently with probabilities $1-e^{-\lambda_{xy}(t)}$. Fix a root $o$, and put</p>
<div class="math-display">$$a(t)=\sum_{y\ne o}\lambda_{oy}'(t),\qquad T_m(t)=\mathbb E_t\min(|K_o|,m)\quad(m&gt;0).$$</div>
<p>Then $T_m$ is continuously differentiable and</p>
<div class="math-display">$$0\leq T_m'(t)\leq a(t)T_m(t)^2.$$</div>
<p>The row $a(t)$ is independent of the root. The bound holds for real truncations $m&gt;0$, including $m&lt;1$.</p>
<p><em>Proof.</em> Fix $t$ and write $f(s)=\min(s,m)$ and $w_{xy}=\lambda_{xy}'(t)$. Finite-product differentiation gives the expected change from opening each edge, multiplied by $w_{xy}e^{-\lambda_{xy}(t)}$. Equivalently, retain the edge's closed indicator inside the expectation and multiply by $w_{xy}$. An edge matters only when it joins the root cluster to another cluster. Thus</p>
<div class="math-display">$$T_m'(t)=\mathbb E_t\sum_{x\in K_o}\sum_{y\notin K_o}w_{xy}\bigl[f(|K_o|+|K_y|)-f(|K_o|)\bigr].$$</div>
<p>There is no factor of two: each contributing unordered edge has exactly one endpoint in $K_o$. Transitivity and finite double counting move its endpoint to the root:</p>
<div class="math-display">$$T_m'(t)=\mathbb E_t\left[|K_o|\sum_{y\notin K_o}w_{oy}\bigl[f(|K_o|+|K_y|)-f(|K_o|)\bigr]\right].$$</div>
<p>To see the equality directly, average each expression over all roots. In a fixed configuration, a cluster $A$ contributes its boundary sum once for each of its $|A|$ possible roots. Both averages therefore agree configuration by configuration. Invariance makes their expectations independent of the chosen root.</p>
<p>The elementary inequality</p>
<div class="math-display">$$u\bigl[f(u+v)-f(u)\bigr]\leq f(u)f(v)\qquad(u,v\geq0)$$</div>
<p>now bounds the last expectation by $\mathbb E_t[f(|K_o|)\sum_{y\notin K_o}w_{oy}f(|K_y|)]$. Condition on $K_o=A$. The event determining this cluster uses only edges within $A$ and from $A$ to its complement; edges wholly outside $A$ retain their independent laws. For $y\notin A$, its cluster is the cluster in the induced model outside $A$, which is stochastically dominated by its cluster in the full model. Hence</p>
<div class="math-display">$$\mathbb E_t\!\left[\sum_{y\notin K_o}w_{oy}f(|K_y|)\,\middle|\,K_o=A\right]\leq\sum_{y\notin A}w_{oy}T_m(t)\leq a(t)T_m(t).$$</div>
<p>Taking expectations proves the upper bound; every summand in the derivative formula is nonnegative. Continuous differentiability follows from the finite product formula. The merge inequality used above is proved just below.</p>
<p>This finite result does not justify an infinite-volume derivative by itself. Nor does restricting an infinite transitive model to an arbitrary finite box preserve the transitivity used in the double counting. A passage to the cutoff model must supply its own limiting or mass-transport argument and the required domination.</p>

## Passing to a countable model {#section-countable-russo}

<a id="tag-D7A5" data-assertion="theorem" data-title="Countable truncated Russo bound under local summable domination"></a>
<p>Let a group act transitively on a countable nonempty set $V$ and satisfy the <a href="/tag/N0HM/">mass-transport property</a>. On an open interval $I$, let $\lambda_{xy}:I\to[0,\infty)$, for unordered pairs of distinct vertices, be locally absolutely continuous, nondecreasing and invariant under the action. For every compact interval $[u,v]\subset I$, assume there is a symmetric invariant array $W_{xy}\geq0$ such that</p>
<div class="math-display">$$0\leq\lambda_{xy}'(t)\leq W_{xy}\quad\text{for a.e. }t\in[u,v],\qquad R_W=\sum_{y\ne o}W_{oy}&lt;\infty.$$</div>
<p>Open the pairs independently with probabilities $1-e^{-\lambda_{xy}(t)}$, and suppose $\chi(t)=\mathbb E_t|K_o|&lt;\infty$ for every $t\in I$. For each fixed real $m&gt;0$, the function $T_m(t)=\mathbb E_t\min(|K_o|,m)$ is locally absolutely continuous and satisfies</p>
<div class="math-display">$$0\leq T_m'(t)\leq a(t)T_m(t)^2\quad\text{a.e.},\qquad a(t)=\sum_{y\ne o}\lambda_{oy}'(t).$$</div>
<p><em>Proof.</em> Fix $[u,v]\subset I$ and exhaust $V$ by finite sets containing $o$. In the model induced by the $n$th set, write $K_x^{(n)}$ for a cluster, $T_m^{(n)}$ for the truncated mean, and $f(s)=\min(s,m)$. Finite-product differentiation gives the integrated identity</p>
<div class="math-display">$$T_m^{(n)}(t)-T_m^{(n)}(s)=\int_s^t\mathbb E_z\sum_{x\in K_o^{(n)}}\sum_{y\notin K_o^{(n)}}\lambda_{xy}'(z)\bigl[f(|K_o^{(n)}|+|K_y^{(n)}|)-f(|K_o^{(n)}|)\bigr],dz,$$</div>
<p>where both vertices in the sum belong to the finite set. This identity does not require that set to be transitive. Couple all configurations using uniform variables on the edges. At parameter $z\leq v$, the absolute value of each summand is at most</p>
<div class="math-display">$$mW_{xy}\mathbf1_{\{o\leftrightarrow x\text{ at parameter }v\}}.$$</div>
<p>The sum of its expectations is $mR_W\chi(v)&lt;\infty$, uniformly in $z$. At every fixed parameter, finiteness of susceptibility and countability imply that all clusters are finite almost surely. For each fixed pair $x,y$, its summand therefore converges to the full-volume summand: a finite connected cluster is eventually seen inside the exhaustion. Countably many locally absolutely continuous edge intensities also have a common full-measure set of differentiability. Dominated convergence in the edge sum, expectation and parameter integral gives</p>
<div class="math-display">$$T_m(t)-T_m(s)=\int_s^t D_m(z),dz,$$</div>
<p>with</p>
<div class="math-display">$$D_m(z)=\mathbb E_z\sum_{x\in K_o}\sum_{y\notin K_o}\lambda_{xy}'(z)\bigl[f(|K_o|+|K_y|)-f(|K_o|)\bigr].$$</div>
<p>In particular $T_m$ is absolutely continuous on $[u,v]$. It remains to bound its derivative in the transitive full-volume model.</p>
<p>Fix a parameter where the edge derivatives exist. For vertices $p,x$, send from $p$ to $x$ the expected nonnegative mass</p>
<div class="math-display">$$\mathbb E\left[\mathbf1_{\{x\in K_p\}}\sum_{y\notin K_p}\lambda_{xy}'\bigl[f(|K_p|+|K_y|)-f(|K_p|)\bigr]\right].$$</div>
<p>This mass is invariant under the diagonal group action. The total outgoing mass at $o$ is $D_m$; the incoming mass is</p>
<div class="math-display">$$\mathbb E\left[|K_o|\sum_{y\notin K_o}\lambda_{oy}'\bigl[f(|K_o|+|K_y|)-f(|K_o|)\bigr]\right].$$</div>
<p>Mass transport equates them. Apply $a[f(a+b)-f(a)]\leq f(a)f(b)$ and condition on the finite root cluster. Its complement retains its independent edge law, and its clusters are dominated by the full-model clusters. Tonelli and transitivity then give $D_m\leq a(t)T_m(t)^2$, exactly as in the finite proof. All terms are nonnegative, so no subtraction of infinite sums occurs.</p>
<p>For the Euclidean soft cutoff $\lambda_{xy}(r)=\beta\mathbf1_{\{|x-y|\leq r\}}[j(|x-y|)-j(r)]$, with fixed $\beta&gt;0$ and nonincreasing continuously differentiable $j$, the derivative is $-\beta j'(r)\mathbf1_{\{|x-y|&lt;r\}}$ almost everywhere. On a compact radius interval it is dominated by a bounded array of finite range. Provided every cutoff susceptibility on that interval is finite, the theorem applies with</p>
<div class="math-display">$$a(r)=\beta|j'(r)|\,\#\{y\ne o:|y-o|&lt;r\}\leq\beta|j'(r)|\,|B_r|.$$</div>
<p>The count excludes the diagonal. The kernel is continuous when a new distance enters the cutoff because its intensity starts at zero. Thus the truncation inequality follows under these stated regularity and susceptibility assumptions; a finite interaction range alone does not supply the latter. For the normalized power-law cutoff, <a href="/tag/0CUF/">strict domination below the full endpoint</a> provides the relevant finiteness criterion.</p>

## The second moment and its collision correction {#section-second-moment}

<a id="tag-6H7C" data-assertion="theorem" data-title="Second-moment Russo identity and a truncated collision bound"></a>
<p>Under the hypotheses of the countable truncated Russo theorem, suppose also $m_3(t)=\mathbb E_t|K_o|^3&lt;\infty$ for every $t\in I$. Write $m_2(t)=\mathbb E_t|K_o|^2$, $w_{xy}(t)=\lambda_{xy}'(t)$ and $c(t)=\sup_{y\ne o}w_{oy}(t)$, with an empty supremum equal to zero. Then $m_2$ is locally absolutely continuous and, almost everywhere,</p>
<div class="math-display">$$m_2'(t)=3\sum_{y\ne o}w_{oy}(t)\mathbb E_t\bigl[|K_o|^2|K_y|\mathbf1_{\{o\not\leftrightarrow y\}}\bigr].$$</div>
<p>For every fixed $m&gt;0$, this gives</p>
<div class="math-display">$$m_2'(t)\geq3a(t)m_2(t)T_m(t)-3m c(t)m_3(t)\quad\text{a.e.}$$</div>
<p><em>Proof.</em> First justify differentiation by finite exhaustion, as for the truncated mean. On a compact parameter interval $[u,v]$, let $A=|K_o|$ and $B_y=|K_y|$ in the full model at the upper endpoint $v$. A dominating sum for the finite-volume derivative integrands is</p>
<div class="math-display">$$\sum_{x\in K_o}\sum_{y\ne x}W_{xy}(2AB_y+B_y^2).$$</div>
<p>Mass transport, followed by Hölder's inequality and transitivity, bounds its expectation by</p>
<div class="math-display">$$\sum_{y\ne o}W_{oy}\mathbb E_v(2A^2B_y+AB_y^2)\leq3R_Wm_3(v)&lt;\infty.$$</div>
<p>Indeed, move the endpoint $x$ to the root exactly as in the previous proof, and use $\mathbb E(A^2B_y),\mathbb E(AB_y^2)\leq m_3(v)$. Dominated convergence in the integrated finite-volume identity proves local absolute continuity and identifies the derivative with the full boundary sum. No finite box is assumed transitive.</p>
<p>At a fixed parameter, mass transport rewrites that boundary sum as</p>
<div class="math-display">$$\sum_{y\ne o}w_{oy}\mathbb E\bigl[(2A^2B_y+AB_y^2)\mathbf1_{\{o\not\leftrightarrow y\}}\bigr].$$</div>
<p>A second mass transport interchanges the root and $y$. Symmetry of $w$ shows that the summed $AB_y^2$ term equals the summed $A^2B_y$ term, proving the factor-three identity. The preceding domination makes every sum finite.</p>
<p>Replace $B_y$ in that identity by $\min(B_y,m)$. The <a href="/tag/X5SS/">Harris inequality</a>, applied first to bounded increasing truncations and then by monotone convergence, gives</p>
<div class="math-display">$$\mathbb E[A^2\min(B_y,m)]\geq m_2T_m.$$</div>
<p>Subtract the contribution from $\{o\leftrightarrow y\}$, on which $B_y=A$. The total amount subtracted is at most</p>
<div class="math-display">$$m\mathbb E\left[A^2\sum_{y\ne o}w_{oy}\mathbf1_{\{o\leftrightarrow y\}}\right]\leq mc\mathbb E[A^2(A-1)]\leq mc m_3.$$</div>
<p>Multiplying by three proves the lower bound. This argument controls the same-cluster contribution explicitly; it does not assume independence of clusters rooted at two fixed vertices.</p>
<p>For the soft cutoff above, write $N_r=\#\{y\ne o:|y-o|&lt;r\}$. Wherever $N_r&gt;0$, one has $a(r)=\beta|j'(r)|N_r$ and $c(r)=\beta|j'(r)|$. Suppose $N_r\geq v_0r^d$ and $m_3(r)\leq K r^\kappa m_2(r)$ at large radii. When $2\kappa=d+\alpha$, the lower bound becomes</p>
<div class="math-display">$$(\log m_2)'(r)\geq3a(r)\left(T_m(r)-\frac{K}{v_0}m r^{\alpha-\kappa}\right).$$</div>
<p>Thus the collision inequality needed below follows from a uniform third-to-second moment comparison, together with the stated regularity, susceptibility and moment-finiteness hypotheses. Rooted damping and localization are one route to such a comparison, but a largest-cluster quantile estimate alone does not establish it.</p>

## The finite-model moment hierarchy {#section-finite-hierarchy}

<a id="tag-C9Y8" data-assertion="theorem" data-title="All cluster-moment derivatives in a finite transitive intensity model"></a>
<p>Let a group act transitively on a nonempty finite vertex set $V$. On an open interval of parameters, let the finite nonnegative intensities $\lambda_t(u,v)=\lambda_t(v,u)$ be continuously differentiable, nondecreasing and invariant under that action. Give distinct pairs independent bond probabilities $1-e^{-\lambda_t(u,v)}$. Write $w_t(u,v)=\partial_t\lambda_t(u,v)$, $a(t)=\sum_{y\neq o}w_t(o,y)$ and $m_k(t)=\mathbb E_t|K_o|^k$. Then, for every integer $k\geq1$,</p>
<div class="math-display">$$m_k'(t)=\frac12\sum_{y\neq o}w_t(o,y)\,\mathbb E_t\!\left[\mathbf1_{\{o\not\leftrightarrow y\}}\sum_{j=1}^k\binom{k+1}{j}|K_o|^j|K_y|^{k+1-j}\right].$$</div>
<p>Moreover,</p>
<div class="math-display">$$0\leq m_k'(t)\leq\frac{a(t)}2\sum_{j=1}^k\binom{k+1}{j}m_j(t)m_{k+1-j}(t)=a(t)\sum_{\ell=0}^{k-1}\binom{k}{\ell}m_{\ell+1}(t)m_{k-\ell}(t).$$</div>
<p><em>Proof.</em> For each configuration, sum the rooted observable over $V$:</p>
<div class="math-display">$$\sum_{v\in V}|K_v|^k=\sum_{C\text{ a cluster}}|C|^{k+1}.$$</div>
<p>Opening an edge between distinct clusters of sizes $A,B$ changes the right side by $(A+B)^{k+1}-A^{k+1}-B^{k+1}$; an edge within one cluster changes nothing. Finite-coordinate differentiation multiplies this increment by $w_t(u,v)e^{-\lambda_t(u,v)}$, with the edge forced closed. Equivalently, average the increment over the original law with the distinct-cluster indicator: distinct endpoints already force this edge closed, supplying exactly the factor $e^{-\lambda_t(u,v)}$.</p>
<p>Transitivity makes the expectation of the left side $|V|m_k(t)$. Replace the sum over unordered edges by half the sum over ordered distinct pairs. Invariance makes the sum with first endpoint $u$ independent of $u$, cancelling the factor $|V|$. Expanding the merger increment proves the identity.</p>
<p>To bound a summand, condition on $K_o=C$. On $y\notin C$, the cluster of $y$ is determined by the unchanged independent bonds outside $C$. Coupling these bonds to the full model bounds its conditional moment of order $k+1-j$ by $m_{k+1-j}(t)$. Hence</p>
<div class="math-display">$$\mathbb E_t[|K_o|^j|K_y|^{k+1-j}\mathbf1_{\{o\not\leftrightarrow y\}}]\leq m_j(t)m_{k+1-j}(t).$$</div>
<p>Insert this bound and sum the rates. For the last equality, pair the coefficients with indices $j$ and $k+1-j$ and use Pascal's identity. All sums are finite; no infinite-volume differentiation is used.</p>
<p>The first three upper bounds are $m_1'\leq am_1^2$, $m_2'\leq3am_1m_2$ and $m_3'\leq a(4m_1m_3+3m_2^2)$. They explain the binomial coefficients in the moment hierarchy. The exact finite identity does not replace the two-cluster expectation by a product. An infinite-volume hierarchy needs justified differentiation and summation limits; an asymptotically closed hierarchy additionally needs negligible factorization errors.</p>

## The countable moment hierarchy {#section-countable-hierarchy}

<a id="tag-09EI" data-assertion="theorem" data-title="Countable all-order moment flow under summable local domination"></a>
<p>Assume the hypotheses of <a href="/tag/D7A5/">D7A5</a>: a countable transitive model satisfying mass transport, nondecreasing invariant locally absolutely continuous intensities, a symmetric invariant summable derivative envelope on each compact parameter interval, and finite susceptibility. Fix an integer $k\geq1$ and suppose $m_{k+1}(t)=\mathbb E_t|K_o|^{k+1}&lt;\infty$ throughout the interval. Then $m_k$ is locally absolutely continuous and the exact derivative identity and upper bound of <a href="/tag/C9Y8/">C9Y8</a> hold almost everywhere, with the same definitions of $w_t$ and $a(t)$.</p>
<p><em>Proof.</em> Fix a compact parameter interval $[u,v]$ and its envelope $W$, with row sum $R_W$. In a finite induced subgraph, differentiate the root moment and integrate in the parameter. Its derivative integrand is the expectation of</p>
<div class="math-display">$$\sum_{x\in K_o^{(n)}}\sum_{y\notin K_o^{(n)}}w_t(x,y)\left[(|K_o^{(n)}|+|K_y^{(n)}|)^k-|K_o^{(n)}|^k\right],$$</div>
<p>where both endpoints belong to the finite subgraph. This is the finite boundary-edge formula; it does not require the subgraph to be transitive.</p>
<p>Couple the configurations monotonically in volume and parameter. Let $A=|K_o|$ and $B_y=|K_y|$ in the full model at $v$. A dominating sum, independent of the finite subgraph and of $t\in[u,v]$, is</p>
<div class="math-display">$$\sum_{x\in K_o}\sum_{y\neq x}W_{xy}\sum_{j=1}^k\binom{k}{j}A^{k-j}B_y^j.$$</div>
<p>Move $x$ to the receiving root by mass transport, as in D7A5. The expectation of this sum is</p>
<div class="math-display">$$\sum_{y\neq o}W_{oy}\sum_{j=1}^k\binom{k}{j}\mathbb E_v[A^{k-j+1}B_y^j]\leq(2^k-1)R_Wm_{k+1}(v)&lt;\infty.$$</div>
<p>For the inequality, apply Hölder with exponents $(k+1)/(k-j+1)$ and $(k+1)/j$, then use transitivity to identify both moments of order $k+1$.</p>
<p>Finite susceptibility makes every cluster finite almost surely. At each fixed parameter the finite-volume summands therefore converge to the full-volume summands. Countability gives a common almost-everywhere set of differentiability for the intensities. Dominated convergence in the edge sum, expectation and parameter integral yields an integral identity for $m_k$, proving local absolute continuity.</p>
<p>Apply mass transport to its full boundary sum. Writing $A=|K_o|$ and $B_y=|K_y|$ now at the current parameter, the derivative becomes</p>
<div class="math-display">$$\sum_{y\neq o}w_t(o,y)\,\mathbb E_t\!\left[\mathbf1_{\{o\not\leftrightarrow y\}}A\bigl((A+B_y)^k-A^k\bigr)\right].$$</div>
<p>A second mass transport exchanges the endpoints. Symmetry of $w_t$ allows us to average the last expression with the one having $A$ and $B_y$ interchanged. Their averaged polynomial is $[(A+B_y)^{k+1}-A^{k+1}-B_y^{k+1}]/2$, giving the exact hierarchy. The same domination makes the sums finite. Finally, condition on the finite root cluster and dominate each outside-cluster moment by its full-model value, exactly as in C9Y8, to obtain the upper bound.</p>
<p>For the soft cutoff, <a href="/tag/0CUF/">0CUF</a> supplies moment finiteness when its subcritical-susceptibility hypothesis holds; the derivative envelope has finite range on compact radius intervals. This gives the exact countable hierarchy in that setting. It still does not show that the two-cluster terms approach products of moments: the error estimates remain a separate probabilistic input.</p>

## Relative errors in the first two moment equations {#section-moment-errors}

<a id="tag-NJF3" data-assertion="proposition" data-title="Russo moment deficits are controlled by the third and fourth moments"></a>
<p>Under the hypotheses of the countable truncated Russo theorem, suppose $m_4(t)=\mathbb E_t|K_o|^4&lt;\infty$ for every $t\in I$. With $a(t)=\sum_{y\ne o}\lambda_{oy}'(t)$ and $c(t)=\sup_{y\ne o}\lambda_{oy}'(t)$, the first two moments are locally absolutely continuous and satisfy, almost everywhere,</p>
<div class="math-display">$$a m_1^2-cm_3\leq m_1'\leq a m_1^2,\qquad 3a m_1m_2-3cm_4\leq m_2'\leq3a m_1m_2.$$</div>
<p>Both derivatives are nonnegative. Wherever $a&gt;0$, one may therefore write</p>
<div class="math-display">$$m_1'=a m_1^2(1-e_1),\qquad m_2'=3a m_1m_2(1-e_2),$$</div>
<p>where $e_1,e_2\in[0,1]$ and</p>
<div class="math-display">$$e_1\leq\frac{c m_3}{a m_1^2},\qquad e_2\leq\frac{c m_4}{a m_1m_2}.$$</div>
<p><em>Proof.</em> The dominated-exhaustion argument for the second moment also applies to the first: its edge increment is smaller, and the third moment at the upper endpoint of each compact interval already dominates the integrated sums. Mass transport gives, with $A=|K_o|$ and $B_y=|K_y|$,</p>
<div class="math-display">$$m_1'=\sum_{y\ne o}w_{oy}\mathbb E[AB_y\mathbf1_{\{o\not\leftrightarrow y\}}],\qquad m_2'=3\sum_{y\ne o}w_{oy}\mathbb E[A^2B_y\mathbf1_{\{o\not\leftrightarrow y\}}].$$</div>
<p>Condition on $K_o$. Every outside cluster has conditional mean at most $m_1$, so the two expressions are at most $a m_1^2$ and $3a m_1m_2$ respectively. Harris association gives $\mathbb E AB_y\geq m_1^2$ and $\mathbb E A^2B_y\geq m_2m_1$, by truncation if necessary. On the same-cluster event $B_y=A$, and</p>
<div class="math-display">$$\sum_{y\ne o}w_{oy}\mathbb E[A^j\mathbf1_{\{o\leftrightarrow y\}}]\leq c\mathbb E[A^j(A-1)]\leq c m_{j+1}\qquad(j=2,3).$$</div>
<p>Subtract these contributions to obtain the lower bounds. The displayed relative errors follow by division; nonnegativity of the derivative and its upper bound place each error in $[0,1]$.</p>
<p>For a soft cutoff, $c/a=1/N_r$ whenever $a&gt;0$. The <a href="/tag/0WAE/">localized moment ratios</a> therefore imply $e_i(r)\leq DQ(r)^2/[N_r m_1(r)]$. If $N_r\succeq r^d$, $m_1(r)\succeq r^\alpha$ and $Q(r)\leq M_{Cr}$ for fixed $C$, this is precisely an error bound of order $M_{Cr}^2/r^{d+\alpha}$. The same moment-ratio result gives $m_2(r)\preceq M_{Cr}m_1(r)$.</p>

## A collision bound at every order {#section-all-order-errors}

<a id="tag-XXTP" data-assertion="proposition" data-title="All-order moment factorization error from a collision bound"></a>
<p>Under the hypotheses of <a href="/tag/D7A5/">D7A5</a>, fix an integer $k\geq1$ and assume $m_{k+2}(t)&lt;\infty$ throughout the parameter interval. Write $c(t)=\sup_{y\ne o}w_{oy}(t)$, with an empty supremum equal to zero, and set</p>
<div class="math-display">$$H_k(t)=\frac{a(t)}2\sum_{j=1}^k\binom{k+1}{j}m_j(t)m_{k+1-j}(t).$$</div>
<p>Then, almost everywhere,</p>
<div class="math-display">$$0\leq H_k-m_k'\leq(2^k-1)c\bigl(m_{k+2}-m_{k+1}\bigr)\leq(2^k-1)c m_{k+2}.$$</div>
<p>Where $a&gt;0$, the relative error $e_k=1-m_k'/H_k$ belongs to $[0,1]$ and satisfies</p>
<div class="math-display">$$e_k\leq\frac{(2^k-1)c m_{k+2}}{H_k}.$$</div>
<p><em>Proof.</em> Fix a parameter where the <a href="/tag/09EI/">countable hierarchy</a> holds. Put $A=|K_o|$, $B_y=|K_y|$ and $l=k+1-j$. Conditioning on the root cluster gives</p>
<div class="math-display">$$\mathbb E[A^jB_y^l\mathbf1_{\{o\not\leftrightarrow y\}}]\leq m_jm_l.$$</div>
<p>On the other hand, Harris association, first for bounded truncations and then by monotone convergence, gives $\mathbb E A^jB_y^l\geq m_jm_l$. These expectations are finite by Hölder's inequality and the assumed moment bound. On $\{o\leftrightarrow y\}$ one has $B_y=A$, so</p>
<div class="math-display">$$0\leq m_jm_l-\mathbb E[A^jB_y^l\mathbf1_{\{o\not\leftrightarrow y\}}]\leq\mathbb E[A^{k+1}\mathbf1_{\{o\leftrightarrow y\}}].$$</div>
<p>After multiplication by $w_{oy}$ and summation over $y\ne o$, the right side is at most $c\mathbb E[A^{k+1}(A-1)]$. Insert this bound in the exact hierarchy and use $\tfrac12\sum_{j=1}^k\binom{k+1}{j}=2^k-1$. Nonnegativity of $m_k'$ gives $e_k\leq1$; the remaining claims follow by division.</p>
<p>For the soft cutoff, $c/a=1/N_r$ wherever $a&gt;0$. The displayed estimate therefore gives an explicit sufficient condition for factorization at any fixed order. For example, suppose independently that, for $1\leq j\leq k+2$,</p>
<div class="math-display">$$m_j(r)\asymp\chi(r)^{2j-1},\qquad \chi(r)=m_1(r),\qquad N_r\asymp r^d,\qquad\chi(r)\asymp r^\alpha.$$</div>
<p>Then $H_k/a\asymp\chi^{2k}$ and $m_{k+2}\asymp\chi^{2k+3}$, so $e_k(r)=O(r^{3\alpha-d})$ almost everywhere. In particular, if $d&gt;3\alpha$, the hierarchy closes asymptotically at this fixed order. This implication does not establish the moment orders used in its premise; using the closed hierarchy to obtain them would require a separate bootstrap. At $d=3\alpha$ the bound alone gives no vanishing error and no logarithmic asymptotic. The distinction is the one needed in the mean-field moment flow.</p>

## Propagating a truncated mean backwards in scale {#section-truncation}

<a id="tag-OP4X" data-assertion="proposition" data-title="A reciprocal differential inequality propagates a truncated mean"></a>
<p>Let $T$ be positive and locally absolutely continuous on $[r_0,R]$, and suppose $a\geq0$ is integrable there and $T'\leq aT^2$ almost everywhere. Then, for $r_0\leq\ell\leq R$,</p>
<div class="math-display">$$T(\ell)\geq\left(\frac1{T(R)}+\int_\ell^R a(s)\,ds\right)^{-1}.$$</div>
<p>If $\alpha,A,\varepsilon&gt;0$, $a(s)\leq As^{-\alpha-1}$ and $T(R)\geq\varepsilon R^\alpha$, this gives</p>
<div class="math-display">$$T(\ell)\geq\frac{\ell^\alpha}{A/\alpha+(\varepsilon^{-1}-A/\alpha)(\ell/R)^\alpha}.$$</div>
<p>The denominator is positive: it is a convex combination of $A/\alpha$ and $\varepsilon^{-1}$.</p>
<p><em>Proof.</em> The reciprocal is locally absolutely continuous and $(1/T)'=-T'/T^2\geq-a$ almost everywhere. Integrating from $\ell$ to $R$ gives the first inequality. For the second, integrate the power and use the lower bound at $R$.</p>
<p>Apply this to $T_m(r)=\mathbb E\min(|K|,m)$ with the truncation $m$ fixed throughout the interval. The elementary merge inequality behind that application is</p>
<div class="math-display">$$a\bigl(\min(a+b,m)-\min(a,m)\bigr)\leq\min(a,m)\min(b,m)\qquad(a,b,m\geq0).$$</div>
<p>If $a\geq m$, the left side is zero. Otherwise it is $a\min(b,m-a)\leq a\min(b,m)$. The finite transitive proposition above obtains the differential inequality by Russo differentiation and conditioning on the root cluster. The countable theorem supplies the corresponding justification under summable derivative domination and finite susceptibility. One must not differentiate a truncation that changes with $r$ as though it were fixed.</p>

## Negligibility from fixed-truncation differential inequalities {#section-negligibility}

<a id="tag-KKGL" data-assertion="theorem" data-title="Truncated moment inequalities force mesoscopic negligibility"></a>
<p>Let $0&lt;\alpha\leq\kappa&lt;2\alpha$. For $r\geq r_0&gt;0$, let $X_r\geq0$ have finite first and second moments, and write</p>
<div class="math-display">$$m_1(r)=\mathbb E X_r,\qquad m_2(r)=\mathbb E X_r^2,\qquad T_m(r)=\mathbb E\min(X_r,m).$$</div>
<p>Suppose $m_1(r)\asymp r^\alpha$ and, for constants $0&lt;b\leq B&lt;\infty$,</p>
<div class="math-display">$$br^{\alpha+\kappa}\leq m_2(r)\leq Br^{\alpha+\kappa}\qquad(r\geq r_0).$$</div>
<p>Assume $m_2$ and every fixed-truncation function $T_m$, $m&gt;0$, are positive and locally absolutely continuous. Let $a$ be a positive measurable function with $a(r)\sim a_0r^{-\alpha-1}$ for some $a_0&gt;0$. Suppose a constant $C\geq0$, independent of $m$ and $r$, satisfies, for every $m&gt;0$ and almost every $r\geq r_0$,</p>
<div class="math-display">$$T_m'(r)\leq a(r)T_m(r)^2,\qquad (\log m_2)'(r)\geq3a(r)\bigl(T_m(r)-Cm r^{\alpha-\kappa}\bigr).$$</div>
<p>Then mesoscopic negligibility holds at scale $r^\kappa$.</p>
<p><em>Proof.</em> Fix $\varepsilon&gt;0$. We will find $\delta&gt;0$ for which $T_{\delta R^\kappa}(R)&lt;\varepsilon R^\alpha$ at every sufficiently large $R$. Put $k=\alpha+\kappa$ and choose $\eta\in(0,1)$ so that $\mu=3\alpha(1-\eta)^2&gt;k$. Choose positive constants $a_-&lt;a_0&lt;a_+$ close enough that $a_-/a_+&gt;1-\eta$. Beyond a fixed radius,</p>
<div class="math-display">$$a_-t^{-\alpha-1}\leq a(t)\leq a_+t^{-\alpha-1}.$$</div>
<p>Choose $\lambda\in(0,1)$ so small that, with $D=(a_+/\alpha+\varepsilon^{-1}\lambda^\alpha)^{-1}$, one has $a_-D\geq\alpha(1-\eta)$. Next choose $L&gt;1$ with $L^{\mu-k}&gt;B/b$, and put $q=\lambda/L$. Finally choose $\delta&gt;0$ so small that $C\delta q^{-\kappa}\leq\eta D$; if $C=0$, any positive $\delta$ satisfies this last requirement.</p>
<p>Suppose now that $R$ is large and $T_m(R)\geq\varepsilon R^\alpha$ for the fixed number $m=\delta R^\kappa$. The reciprocal estimate, applied with this same $m$ throughout the interval, gives for $qR\leq t\leq\lambda R$,</p>
<div class="math-display">$$\frac1{T_m(t)}\leq\varepsilon^{-1}R^{-\alpha}+\frac{a_+}{\alpha}(t^{-\alpha}-R^{-\alpha})\leq D^{-1}t^{-\alpha}.$$</div>
<p>Consequently $T_m(t)\geq Dt^\alpha$, $a(t)T_m(t)\geq\alpha(1-\eta)/t$, and</p>
<div class="math-display">$$Cm t^{\alpha-\kappa}=C\delta(R/t)^\kappa t^\alpha\leq C\delta q^{-\kappa}t^\alpha\leq\eta T_m(t).$$</div>
<p>The second differential inequality therefore gives $(\log m_2)'(t)\geq\mu/t$ almost everywhere on this interval. Integration and the two moment bounds imply</p>
<div class="math-display">$$B(\lambda R)^k\geq m_2(\lambda R)\geq m_2(qR)L^\mu\geq b(\lambda R)^kL^{\mu-k},$$</div>
<p>contrary to the choice of $L$. All constants were chosen before $R$, and taking $qR$ beyond the fixed radius justifies every estimate. Since truncation is increasing in $\delta$, the conclusion also holds for every smaller $\delta$. Dividing by the lower bound for $m_1(R)$ and then letting $\varepsilon\downarrow0$ proves the stated ordered limit.</p>
<p>The argument starts from one radius with excessive truncated mass; it does not assume that such radii already fill a long interval. The truncation $m=\delta R^\kappa$ is held fixed while differentiating in $t$. Exceptional null sets may depend on this fixed $m$, which suffices for the integration.</p>
<p>The hypotheses have a simple probabilistic witness: for $r\geq1$, let $X_r=r^\kappa$ with probability $r^{\alpha-\kappa}$ and zero otherwise. Then $m_1=r^\alpha$, $m_2=r^{\alpha+\kappa}$ and $T_m=r^{\alpha-\kappa}\min(r^\kappa,m)$. The differential inequalities hold with $a(r)=\alpha r^{-\alpha-1}$ and $C=1$: below the truncation transition the first is an equality, above it $T_m$ is nonincreasing, and the bracket in the second is always nonpositive. This witnesses the analytic assumptions, not their realization by a percolation model.</p>
<p>For $\kappa=(d+\alpha)/2$, the parameter range is $\alpha\leq d&lt;3\alpha$, and the error power $\alpha-\kappa$ is $(\alpha-d)/2$. The <a href="/tag/NS0Q/">all-scale quantile estimate</a>, together with its lower and upper moment comparisons, supplies the required two-sided order of $m_2$. The first truncated differential inequality follows from the countable theorem under its regularity and susceptibility assumptions. The second follows from the preceding collision bound once a uniform third-to-second moment comparison is supplied. Once they are available, the theorem below yields the full tail in the additional range $\alpha&lt;d$.</p>

<a id="tag-J5R6" data-assertion="proposition" data-title="First and second moment orders do not imply mesoscopic negligibility"></a>
<p>For any $0&lt;\alpha&lt;\kappa$ and $r\geq1$, let $p_r=r^{\alpha-\kappa}$ and let $X_r$ equal $r^\kappa$ with probability $p_r$ and $r^\alpha$ with probability $1-p_r$. Then</p>
<div class="math-display">$$\mathbb E X_r=(2-p_r)r^\alpha\sim2r^\alpha,\qquad \mathbb E X_r^2=r^{\alpha+\kappa}+(1-p_r)r^{2\alpha}\sim r^{\alpha+\kappa},$$</div>
<p>but</p>
<div class="math-display">$$\lim_{\delta\downarrow0}\lim_{r\to\infty}\frac{\mathbb E\min(X_r,\delta r^\kappa)}{\mathbb E X_r}=\frac12.$$</div>
<p><em>Proof.</em> For fixed $0&lt;\delta&lt;1$ and sufficiently large $r$, one has $r^\alpha\leq\delta r^\kappa&lt;r^\kappa$. The truncated mean is then $(1+\delta-p_r)r^\alpha$. Divide by $(2-p_r)r^\alpha$ and take the limits in the indicated order. This is a family of random variables, not a percolation counterexample; it identifies information missing from the moment orders alone.</p>

## A two-sided tail bound {#section-transfer}

<a id="tag-ZWQ3" data-assertion="theorem" data-title="Mesoscopic negligibility and a ghost comparison imply a full power-law tail"></a>
<p>Fix $0&lt;\alpha&lt;\kappa$. Suppose $X_r\geq0$, for $r\geq r_0$, has finite first and second moments satisfying, with constants $c_1,C_1,C_2&gt;0$,</p>
<div class="math-display">$$c_1r^\alpha\leq m_1(r)=\mathbb E X_r\leq C_1r^\alpha,\qquad \mathbb E X_r^2\leq C_2r^\kappa m_1(r).$$</div>
<p>Assume mesoscopic negligibility at scale $r^\kappa$. Let $T\in[0,\infty]$, define</p>
<div class="math-display">$$G(h)=\mathbb E[1-e^{-hT}],\qquad G_r(h)=\mathbb E[1-e^{-hX_r}],$$</div>
<p>with $e^{-h\infty}=0$ for $h&gt;0$, and suppose for some $D\geq0$, $h_0&gt;0$ and every $r\geq r_0$, $0&lt;h&lt;h_0$,</p>
<div class="math-display">$$G_r(h)\leq G(h)\leq G_r(h)+Dr^{-\alpha}\mathbb E[X_re^{-hX_r}]G(h).$$</div>
<p>Then $T$ is finite almost surely and, writing $\rho=1-\alpha/\kappa\in(0,1)$,</p>
<div class="math-display">$$G(h)\asymp h^\rho\quad(h\downarrow0),\qquad \mathbb P(T&gt;t)\asymp t^{-\rho}\quad(t\to\infty).$$</div>
<p>For integer-valued $T$, the tail estimate also holds for $\mathbb P(T\geq n)$. These are two-sided bounds, not an assertion that a limiting amplitude exists.</p>
<p><em>Proof.</em> First make the comparison error uniformly smaller than one. For fixed $\delta,\lambda&gt;0$ with $hr^\kappa=\lambda$, split at $X_r=\delta r^\kappa$ to obtain</p>
<div class="math-display">$$\frac{\mathbb E[X_re^{-hX_r}]}{m_1(r)}\leq\frac{\mathbb E\min(X_r,\delta r^\kappa)}{m_1(r)}+e^{-\lambda\delta}.$$</div>
<p>If $D&gt;0$, choose $\delta$ so that the first term is eventually at most $1/(4DC_1)$, and then fix $\lambda$ large enough that $e^{-\lambda\delta}\leq1/(4DC_1)$. For sufficiently small $h$, take $r=(\lambda/h)^{1/\kappa}$; this eventually exceeds the scale required for that fixed $\delta$. The error coefficient is at most $1/2$, so</p>
<div class="math-display">$$G(h)\leq2G_r(h)\leq2h m_1(r)\leq2C_1\lambda^{\alpha/\kappa}h^\rho.$$</div>
<p>If $D=0$, the same upper bound follows directly with $\lambda=1$. In particular $G(h)\to0$, which implies $\mathbb P(T=\infty)=0$ by bounded convergence.</p>
<p>For the lower bound, $1-e^{-u}\geq u/(1+u)$ for $u\geq0$. Under the size-biased law of $X_r$, Jensen's inequality for the convex function $x\mapsto(1+hx)^{-1}$ gives</p>
<div class="math-display">$$G_r(h)\geq\frac{h m_1(r)}{1+h\mathbb E X_r^2/m_1(r)}.$$</div>
<p>Set $r=h^{-1/\kappa}$. The second-moment bound makes the denominator at most $1+C_2$, yielding $G(h)\geq c_1h^\rho/(1+C_2)$.</p>
<p>It remains to pass from transform bounds to tail bounds; no asymptotic Tauberian theorem is needed. Write $q(t)=\mathbb P(T&gt;t)$. The inequality $(1-e^{-1})q(t)\leq G(1/t)$ gives $q(t)\leq C t^{-\rho}$ for large $t$. Enlarge $C$ so that this holds for every $t&gt;0$. Tonelli gives $G(h)=h\int_0^\infty e^{-ht}q(t)\,dt$. For any $a&gt;0$, monotonicity of $q$ therefore gives</p>
<div class="math-display">$$G(h)\leq\frac{C}{1-\rho}a^{1-\rho}h^\rho+e^{-a}q(a/h).$$</div>
<p>Choose $a$ small enough that the first coefficient is less than half the lower coefficient already obtained for $G(h)$. It follows that $q(a/h)\succeq h^\rho$. Since $a$ is fixed, this is the required lower bound for all sufficiently large arguments. Rounding changes no two-sided power bound.</p>
<p>For the long-range scale $\kappa=(d+\alpha)/2$, the exponent is $(d-\alpha)/(d+\alpha)$. The fractional range used in the proof is exactly $\alpha&lt;d$. The additional inequality $d&lt;3\alpha$ belongs to the model-specific derivation of the inputs, not to this analytic transfer.</p>
<p>The <a href="/tag/FJWB/">omitted-edge ghost comparison</a> supplies the comparison hypothesis for a transitive independent-bond model when the omitted-edge row is $O(r^{-\alpha})$ and the retained root cluster is almost surely finite. The <a href="/tag/BEJT/">independent-layer comparison</a> also covers soft intensity cutoffs: <a href="/tag/C4E9/">the power-law row estimate</a> gives the required error bound. Cutoff cluster finiteness remains an explicit prerequisite in both cases.</p>

## A conditional power-law cutoff criterion {#section-power-law-criterion}

<a id="tag-YJ5E" data-assertion="theorem" data-title="Localization and rooted damping give the low-dimensional cutoff-to-tail criterion"></a>
<p>Let $d\geq1$ be an integer, $d/3&lt;\alpha&lt;d$, and $A,\beta&gt;0$. On $\mathbb Z^d$ with Euclidean distance, put $J(x,y)=A|x-y|^{-d-\alpha}$ for $x\ne y$. The full model has independent bond probabilities $1-e^{-\beta J(x,y)}$. For each $r\geq1$, use the soft-cutoff intensities</p>
<div class="math-display">$$\lambda_{xy}(r)=\beta A\bigl(|x-y|^{-d-\alpha}-r^{-d-\alpha}\bigr)_+.$$</div>
<p>Write $K_x^{(r)}$ for a cutoff cluster, $m_q(r)=\mathbb E_r|K_o^{(r)}|^q$, and</p>
<div class="math-display">$$M(r,R)=\min\left\{n\geq1:\mathbb P_r\!\left(\max_x|K_x^{(r)}\cap B_R|\geq n\right)\leq e^{-1}\right\},\qquad M_r=M(r,r).$$</div>
<p>Assume $m_1(r)\asymp r^\alpha$ as $r\to\infty$ and weak cutoff localization of the first four moments. Assume also that fixed constants $A_*,b_*&gt;0$ give the rooted damping estimate</p>
<div class="math-display">$$\mathbb P_r\bigl(|K_o^{(r)}\cap B_R|\geq tM(r,R)\bigr)\leq A_*e^{-b_*t}\mathbb P_r\bigl(|K_o^{(r)}\cap B_R|\geq M(r,R)\bigr)$$</div>
<p>for every $r,R\geq1$ and $t\geq1$. In particular, this damping hypothesis includes windows smaller than the cutoff radius. Let $M_r^*$ be the same window quantile in the full model and put $\kappa=(d+\alpha)/2$. Then</p>
<div class="math-display">$$M_r\asymp M_r^*\asymp r^\kappa,\qquad m_q(r)\asymp r^{\alpha+(q-1)\kappa}\quad(q=1,2,3,4).$$</div>
<p>Moreover $\mathbb E_\beta|K_o\cap B_r|\asymp r^\alpha$, and the cutoff family has mesoscopic negligibility at scale $r^\kappa$. Its full-model root cluster $K_o$ is finite almost surely and satisfies</p>
<div class="math-display">$$\mathbb P_\beta(|K_o|\geq n)\asymp n^{-(d-\alpha)/(d+\alpha)}\qquad(n\to\infty).$$</div>
<p>All comparisons have constants independent of the scale. They are two-sided order bounds, not limiting amplitudes. The theorem does not identify $\beta$ as the critical parameter; an application at criticality must verify these inputs at that parameter.</p>
<p><em>Proof.</em> Couple the cutoff laws by common uniform edge variables. Their clusters and the observation windows increase with $r$, so $M_r$ is nondecreasing and $M(r,Cr)\leq M_{Cr}$ for $C\geq1$. Choose one such $C$ from (wCL) with $\varepsilon=1$. The <a href="/tag/0WAE/">localized damping bounds</a> give, with constants independent of $r$,</p>
<div class="math-display">$$m_2\preceq M_{Cr}m_1,\qquad m_3\preceq M_{Cr}^2m_1,\qquad m_3\preceq M_{Cr}m_2,\qquad m_4\preceq M_{Cr}^2m_2.$$</div>
<p>The fourth moments are finite by (wCL). On each compact radius interval the edge derivatives have bounded finite range, so the countable Russo results apply. Except at the discrete set of lattice distances,</p>
<div class="math-display">$$a(r)=\beta A(d+\alpha)r^{-d-\alpha-1}N_r\sim a_0r^{-\alpha-1},\qquad N_r=\#\{y\ne o:|y|&lt;r\}\asymp r^d,$$</div>
<p>where $a_0=\beta A(d+\alpha)v_d&gt;0$ and $v_d$ is the volume of the Euclidean unit ball. The lattice count follows by comparing the union of unit cubes centered at lattice points with balls whose radii differ by a fixed constant. The <a href="/tag/NJF3/">moment-deficit bounds</a> now supply the two moment equations with errors $e_i(r)\preceq M_{Cr}^2/r^{d+\alpha}$.</p>
<p>The <a href="/tag/LQ6Y/">finite-window quantile bound</a> and $|B_r|\preceq r^d$ give $M_r\preceq r^\kappa$ from the first moment and $m_2(r)\succeq M_r^3/r^d$ from the second. All hypotheses of the <a href="/tag/NS0Q/">all-scale quantile theorem</a> are therefore satisfied. It yields $M_r\asymp r^\kappa$. The displayed moment comparisons give the upper bounds through order four. For the lower bounds, apply the same quantile estimate at order $q$: $m_q(r)\succeq M_r^{q+1}/r^d$, and use $2\kappa-d=\alpha$.</p>
<p>In particular $m_2(r)\asymp r^{\alpha+\kappa}$ and $m_3(r)\preceq r^\kappa m_2(r)$. The <a href="/tag/D7A5/">truncated first-moment inequality</a> and the <a href="/tag/6H7C/">collision bound</a> supply the differential hypotheses of <a href="/tag/KKGL/">the negligibility theorem</a>. Its range $\alpha&lt;\kappa&lt;2\alpha$ is exactly $\alpha&lt;d&lt;3\alpha$. Thus mesoscopic negligibility follows.</p>
<p>Finally, each cutoff cluster is finite almost surely because its mean is finite. The <a href="/tag/C4E9/">omitted-intensity row estimate</a> and <a href="/tag/BEJT/">independent-layer ghost comparison</a> give the comparison used in <a href="/tag/ZWQ3/">the full-tail transfer theorem</a>. The moment bounds and negligibility just proved supply its remaining hypotheses. It gives almost-sure finiteness of the full cluster and the stated exponent $1-\alpha/\kappa=(d-\alpha)/(d+\alpha)$.</p>
<p>It remains to compare the full-model window. Write $Z_r^*=\max_x|K_x\cap B_r|$ and $\rho=(d-\alpha)/(d+\alpha)$. If $Z_r^*\geq n$, at least $n$ vertices of $B_r$ have full-cluster size at least $n$. Transitivity and the full-tail upper bound give</p>
<div class="math-display">$$\mathbb P(Z_r^*\geq n)\leq\frac{|B_r|}{n}\mathbb P(|K_o|\geq n)\preceq r^d n^{-1-\rho}.$$</div>
<p>Since $\kappa(1+\rho)=d$, choosing $n$ a sufficiently large multiple of $r^\kappa$ gives $M_r^*\preceq r^\kappa$. The reverse bound follows by coupling with the cutoff model.</p>
<p>The damping hypothesis passes to the full model at each fixed window radius $R$. Under the increasing coupling, finite paths ensure that all connections between vertices of $B_R$ converge to their full-model values. Hence the window maxima and rooted counts increase to their full-model limits. Their quantiles eventually equal the full quantile: the tail at one less than that quantile is strictly greater than $e^{-1}$, while the cutoff quantiles never exceed it. Pass to the limit in the damping inequality with this eventually fixed integer quantile. This step uses damping for $r&gt;R$, not just $R\geq r$.</p>
<p>Put $M=M_r^*$. For $n\leq M$, the rooted window tail is bounded by the full-volume tail $Cn^{-\rho}$. For $n&gt;M$, the inherited damping bounds it by $C A_* M^{-\rho}e^{-b_*n/M}$. Summing gives</p>
<div class="math-display">$$\mathbb E_\beta|K_o\cap B_r|\preceq M^{1-\rho}\preceq r^\alpha.$$</div>
<p>For the reverse bound, (wCL) at order one gives a fixed $C\geq1$ with $m_1(s)\leq2\mathbb E_s|K_o^{(s)}\cap B_{Cs}|$. Set $s=r/C$ and couple to the full model. For large $r$, this is the required lower bound of order $r^\alpha$.</p>
<p>This criterion leaves three probabilistic inputs visible: cutoff susceptibility of order $r^\alpha$, (wCL), and the uniform rooted damping estimate. It neither proves model-specific localization nor replaces it by a moment-ratio assumption derived from localization itself. The endpoint $\alpha=d$ is outside the fractional-tail conclusion.</p>

## Source scope {#section-source}

<p>Mesoscopic negligibility is the input for extracting the full tail. The reciprocal bound above isolates the fixed-truncation step with its quantifiers. The tail theorem supplies an explicit sufficient transfer argument using the earlier ghost comparison, without assuming a limiting size-biased law. The intervening theorem now derives negligibility from the two fixed-truncation differential inequalities and two-sided moment orders, with explicit control of the interval. The first differential inequality is justified above for regular soft cutoffs with finite susceptibility; the collision estimate reduces the second inequality to a uniform third-to-second moment comparison. The final criterion obtains that comparison from (wCL) and rooted damping, while retaining those and the cutoff susceptibility order as explicit model inputs.</p>


## Regularity in the reciprocal estimate {#section-reciprocal-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-odes/">reciprocal source</a> supplies the absolute-continuity step in <a href="/tag/OP4X/">OP4X</a>. Positivity and continuity give a minimum $m&gt;0$ on the compact interval, and inversion is Lipschitz with constant $m^{-2}$ on $[m,\infty)$. Thus $1/T$ is absolutely continuous and its almost-everywhere derivative can be integrated. In the power-law form, the source explicitly requires a positive starting radius; the displayed real powers are used only at positive radii.</p>
<p>The same file proves the merge inequality and the two-point calculation in <a href="/tag/J5R6/">J5R6</a>. Its limit statement has the required order: after choosing a small fixed $\delta$, the large-radius threshold may depend on $\delta$. It does not assert convergence uniform over cutoffs depending on the radius. Its algebraic two-point formulas in fact hold for arbitrary real $\alpha&lt;\kappa$, although the growth example here uses positive exponents.</p>
<p>The final analytic result implements <a href="/tag/TJXV/">TJXV</a> without needing $W\leq1$: that upper bound belongs to the intended model, not to the integration argument. This does not supply the model's missing derivative lower bound.</p>


## Fixed truncations and the ordered limit {#section-negligibility-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-limits/">source implementation of KKGL</a> first proves the uniform estimate for arbitrary functions $T_m$ and $m_2$ satisfying the analytic hypotheses. Only afterwards does it substitute $T_m(r)=\int\min(x,m)\,d\mu_r(x)$ and divide by the first moment. This last step needs only $m_1(r)\geq c_1r^\alpha$; the upper first-moment bound in the article is unused. The asymptotic for $a$ supplies its positivity beyond a fixed radius, so positivity at every earlier radius is also unnecessary.</p>
<p>The source's probability measures are on $\mathbb R$, with integrable identity and positive truncated means at every positive level. These assumptions already force nonnegative support. For a fixed $r$, dominated convergence as $m\downarrow0$ gives $\int\min(x,m)\,d\mu_r\to\int\min(x,0)\,d\mu_r$: for $0&lt;m\leq1$ the integrands have absolute value at most $|x|+1$. The limit is nonnegative by positivity of the truncated means and nonpositive by its integrand. Thus the negative part vanishes. The positive lower bound on the second moment also rules out the nonintegrable case, whose real Bochner integral would otherwise be assigned zero.</p>
<p>For each terminal radius $R$, the proof fixes $m=\delta R^\kappa$ before integrating over $[qR,\lambda R]$. The exceptional set is allowed to depend on that fixed number. Monotonicity of truncation then extends the estimate to every smaller $\delta$. This is precisely the order of quantifiers in <a href="/tag/QMN5/">QMN5</a>; no differentiability along the moving curve $m=\delta r^\kappa$ is assumed.</p>


## Re-rooting an invariant tuple {#section-tuple-transport}

<a id="tag-SCGY" data-assertion="proposition" data-title="Tuple mass transport on an additive commutative group"></a>
<p>Let $G$ be an additive commutative group, let $k\geq1$, and let $F:G^k\to[0,\infty]$ be invariant under simultaneous translation of its coordinates. For any indices $i,j$,</p>
<div class="math-display">$$\sum_{v\in G^k:\,v_i=0}F(v)=\sum_{w\in G^k:\,w_j=0}F(w).$$</div>
<p>For an arbitrary index set, a nonnegative sum means the supremum of its finite subsums, so no countability or summability assumption is needed.</p>
<p><em>Proof.</em> Send $v$ to the tuple $w$ with $w_m=v_m-v_j$. Its inverse sends $w$ to $v_m=w_m-w_i$. The pinned-coordinate conditions make the two maps inverse, and translation invariance preserves the summand. Reindex the nonnegative sum by this bijection.</p>
<p>The <a href="/coverage/sources/perclib-3978a2f-moments/">tuple source</a> also records the two-point form and the real binomial identity</p>
<div class="math-display">$$a\bigl((a+b)^p-a^p\bigr)=\sum_{\ell=0}^{p-1}\binom p\ell a^{\ell+1}b^{p-\ell}.$$</div>
<p>The latter holds for all real $a,b$ and integers $p\geq0$, including the empty sum at zero. These are deterministic ingredients of the hierarchy above. The source does not supply the model's invariance, derivative identity or integrable domination.</p>


## Fixed truncation in the source proof {#section-fixed-truncation-source}

<p>Lemma II.5.5 uses the reciprocal estimate <a href="/tag/OP4X/">OP4X</a> to propagate a lower bound on $T_m(R)$ to smaller radii. With the paper's normalization, the susceptibility lower bound gives $T_m(R)\geq\varepsilon\alpha R^\alpha/(2\beta_c)$, rather than the reciprocal coefficient printed there. In the integral retain the exact rate $\beta_c|J'(t)||B_t|$ until taking its asymptotic equivalent. The resulting near-sharp lower coefficient is valid for $\ell_0\leq\ell\leq\delta R$, with $\ell_0$ sufficiently large. An asymptotic estimate as $\ell\to\infty$ alone does not establish it at every small radius.</p>
<p>The last comparison in Proposition II.5.3 also needs care. If $R\leq R'\leq C R$, monotonicity compares $T_{\delta R^\kappa}(R)$ with $T_{\delta(R')^\kappa}(R')$. It does not justify increasing the first truncation to $\delta C^\kappa R^\kappa$. After removing that factor, choose $C$ uniformly in $\varepsilon$. This is possible from the same argument: writing $\kappa=(d+\alpha)/2$, the source's chosen growth coefficient satisfies $a\alpha&gt;\alpha+\kappa$. If $br^{\alpha+\kappa}\leq m_2(r)\leq Br^{\alpha+\kappa}$, every bad interval has radius ratio at most $(B/b)^{1/(a\alpha-\alpha-\kappa)}$. Any fixed larger $C$ works for all sufficiently small $\varepsilon$, although the starting radius may depend on $\varepsilon$. The resulting coefficient $\varepsilon C^\alpha$ then tends to zero.</p>
<p>The alternative proof of <a href="/tag/KKGL/">KKGL</a> keeps the truncation fixed throughout. A single excessive value at $R$ propagates, with the same fixed truncation, over a predetermined interval $[qR,\lambda R]$. The resulting second-moment growth exceeds its known power. Its constants are selected before $R$, and this interval eventually lies above every fixed lower radius. Thus no bounded-radius version of Lemma II.5.5 and no limit involving an uncontrolled $C(\varepsilon)$ is needed. The derivative identities and moment ratios required by KKGL remain separate inputs.</p>

## Small clusters in a fixed window {#section-small-window-mass}

<a id="tag-SOG8" data-assertion="proposition" data-title="A volume-tail upper bound makes small window counts negligible in every moment"></a>
<p>Let $0\leq\rho&lt;1$, $\kappa&gt;0$, and $T\in[0,\infty]$ satisfy $\mathbb P(T&gt;t)\leq A t^{-\rho}$ for every $t&gt;0$. Suppose $0\leq Y_R\leq T$ and, for an integer $p\geq1$ and all $R\geq R_0&gt;0$,</p>
<div class="math-display">$$0&lt;c_pR^{\kappa(p-\rho)}\leq\mathbb E Y_R^p&lt;\infty.$$</div>
<p>Then, for every $0&lt;\delta\leq1$,</p>
<div class="math-display">$$\sup_{R\geq R_0}\frac{\mathbb E[Y_R^p\mathbf1_{\{Y_R\leq\delta R^\kappa\}}]}{\mathbb E Y_R^p}
\leq\frac{A}{(1-\rho)c_p}\delta^{p-\rho}.$$</div>
<p><em>Proof.</em> Put $m=\delta R^\kappa$. Pointwise, $Y_R^p\mathbf1_{\{Y_R\leq m\}}\leq m^{p-1}\min(T,m)$. Tonelli therefore gives</p>
<div class="math-display">$$\mathbb E[Y_R^p\mathbf1_{\{Y_R\leq m\}}]
\leq m^{p-1}\int_0^m\mathbb P(T&gt;t)\,dt
\leq\frac{A}{1-\rho}m^{p-\rho}.$$</div>
<p>Divide by the assumed moment lower bound. The exponent $p-\rho$ is positive, including when $p=1$.</p>
<p>For the full percolation window take $Y_R=|K\cap B_R|$, $T=|K|$, $\kappa=(d+\alpha)/2$ and $\rho=(d-\alpha)/(d+\alpha)$. Then $\kappa(p-\rho)=\alpha+(p-1)\kappa$, so <a href="/tag/AS7A/">AS7A</a> supplies the lower moment under its hypotheses. A tail upper bound stated only for large $t$ extends to all positive $t$ by enlarging $A$. If the window-moment lower bound is only known for large $R$, bounded radii cause no problem: choose $\delta R_0^\kappa&lt;1$, and the small-count contribution vanishes for integer-valued $Y_R$ when $1\leq R\leq R_0$. At $\alpha=d$, use $\rho=0$ and $A=1$; no finiteness of $T$ is required.</p>
<p>This proves the small-window conclusion in Theorem II.5.2(1) without a higher-moment Cauchy–Schwarz estimate. In the printed proof that estimate needs moment $2p-1$, not $2p-2$. Tail integration also avoids rounding a real truncation as though it were an integer.</p>

## Annular mass from an independent added layer {#section-annular-mass}

<a id="tag-L6K3" data-assertion="theorem" data-title="A fractional volume tail and localized cutoffs concentrate large-cluster mass in an annulus"></a>
<p>Let $K$ be the root cluster of a translation-invariant independent bond law on $\mathbb Z^d$. Write $B_R=\{x:\|x\|_\infty\leq R\}$, choose $0&lt;\alpha&lt;\kappa$, and put $\rho=1-\alpha/\kappa\in(0,1)$. Suppose</p>
<div class="math-display">$$\mathbb P(|K|&gt;t)\leq A t^{-\rho}\qquad(t&gt;0).$$</div>
<p>For each $s\geq1$, suppose the full law can be realized by adding an independent bond configuration to a translation-invariant cutoff law with root cluster $C_s$. Assume the added-edge probabilities have row sums at most $a_s\leq A_1s^{-\alpha}$, and that</p>
<div class="math-display">$$\lim_{L\to\infty}\limsup_{s\to\infty}s^{-\alpha}\mathbb E|C_s\setminus B_{Ls}|=0.$$</div>
<p>Then for every $u&gt;0$,</p>
<div class="math-display">$$\lim_{R\to\infty}\limsup_{n\to\infty}n^\rho
\mathbb P\bigl(|K\setminus B_{Rn^{1/\kappa}}|\geq un\bigr)=0.$$</div>
<p>If in addition $\mathbb E|K\cap B_R|\leq A_2R^\alpha$ for $R\geq1$ and $\mathbb P(|K|\geq n)\geq a_2 n^{-\rho}$ for all sufficiently large integers $n$, where $a_2&gt;0$, then for every $\varepsilon&gt;0$ there exists $L&gt;1$ such that, for all integers $n\geq3$,</p>
<div class="math-display">$$\mathbb P\left(|K|\geq n\text{ and }
|K\cap(B_{Ln^{1/\kappa}}\setminus B_{L^{-1}n^{1/\kappa}})|\leq n/2\right)
\leq\varepsilon\mathbb P(|K|\geq n)\qquad(n\geq3).$$</div>
<p><em>Proof.</em> The tail bound implies $|K|&lt;\infty$ almost surely. Put $H(t)=\mathbb E\min(t|K|,1)$ and $G(t)=\mathbb E(1-e^{-t|K|})$. For $t&gt;0$,</p>
<div class="math-display">$$G(t)\leq H(t)=t\int_0^{1/t}\mathbb P(|K|&gt;v)\,dv
\leq\frac{A}{1-\rho}t^\rho.$$</div>
<p>Write $D_s=K\setminus C_s$ in the independent-layer coupling. Apply <a href="/tag/AYPN/">AYPN</a> with ghost intensity $1/n$. Translation invariance makes its supremum of full-law ghost probabilities equal to $G(1/n)$. Since $|C_s|\leq|K|$, it follows that</p>
<div class="math-display">$$\mathbb P(|D_s|\geq un/2)
\leq\frac{H(a_sG(1/n))}{1-e^{-u/2}}.$$</div>
<p>Set $s=\lambda n^{1/\kappa}$, where $\lambda\geq1$ is fixed for now. The identity $\alpha/\kappa+\rho=1$ gives $a_sG(1/n)\leq C\lambda^{-\alpha}/n$, and hence</p>
<div class="math-display">$$\mathbb P(|D_s|\geq un/2)\leq C_u\lambda^{-\alpha\rho}n^{-\rho}.$$</div>
<p>Also $|K\setminus B_{Ls}|\leq|D_s|+|C_s\setminus B_{Ls}|$. A union bound and Markov's inequality yield</p>
<div class="math-display">$$\limsup_{n\to\infty}n^\rho\mathbb P(|K\setminus B_{L\lambda n^{1/\kappa}}|\geq un)
\leq C_u\lambda^{-\alpha\rho}+
\frac{2\lambda^\alpha}{u}\limsup_{s\to\infty}s^{-\alpha}\mathbb E|C_s\setminus B_{Ls}|.$$</div>
<p>Choose $\lambda$ large first, then $L$ large. Monotonicity in the observation radius proves the first conclusion. This order of choices retains the factor $\lambda^\alpha$ in the localization error.</p>
<p>For the inner ball, Markov's inequality gives, for each fixed $L$ and sufficiently large $n$,</p>
<div class="math-display">$$\mathbb P(|K\cap B_{L^{-1}n^{1/\kappa}}|\geq n/4)
\leq4A_2L^{-\alpha}n^{-\rho}.$$</div>
<p>On the event $|K|\geq n$ with annular mass at most $n/2$, either the inner mass or the outer mass is at least $n/4$. The first conclusion and this bound, divided by the tail lower bound, make the conditional probability of that event arbitrarily small for every sufficiently large $n$, with one fixed $L$.</p>
<p>Only finitely many integers $3\leq n&lt;N$ remain. For each such $n$, as $L\to\infty$ the annulus increases to $\mathbb Z^d\setminus\{0\}$. On $|K|\geq n$ its mass tends to $|K|-1\geq n-1&gt;n/2$. Bounded convergence lets us enlarge $L$ to handle all these $n$ at once. Enlarging $L$ preserves the already established large-$n$ estimate.</p>
<p>The localization hypothesis is an arbitrarily small tail estimate, with the limits in the displayed order. A single constant-factor localization inequality is not substituted for it. For a soft power-law cutoff the row estimate comes from <a href="/tag/C4E9/">C4E9</a>; the full tail and localization still need to be supplied. No regular-variation equivalent or limiting tail amplitude is used.</p>

<p>The restriction $n\geq3$ matters for the source's strict requirement that the annulus contain more than $n/2$ vertices. It always omits the root. In a summable-intensity model the root is isolated with positive probability, so the source statement for every $n\geq1$ cannot hold for arbitrarily small $\varepsilon$. Clusters of size two give the analogous obstruction at $n=2$.</p>
<p>The proof also uses $\rho&gt;0$. At $\alpha=d$, <a href="/tag/79SD/">79SD</a> identifies a positive probability of an infinite full cluster under the corresponding susceptibility/localization hypotheses. Outside every finite ball such a cluster still has infinite mass, so the outer-mass estimate above is false at that endpoint. This does not refute an annular statement for large $n$ there; it shows that it needs a different proof.</p>

## Ghost deficits and volume errors {#section-ghost-deficit-scope}

<p>The final step of the source's annular proof bounds the probability that a ghost field meets the full cluster but misses its portion in a large ball. Conditional on the cluster, this probability is $e^{-hI}(1-e^{-hO})$, where $I$ and $O$ are its inside and outside masses. The factor $e^{-hI}$ prevents an immediate lower bound in terms of the outside mass alone.</p>
<p>For a tail exponent $\rho&gt;0$ one can fill this step by first restricting $|K|\leq An$, with ghost intensity $h=1/n$. On $O\geq un$ and $|K|\leq An$, the ghost deficit is at least $e^{-A}(1-e^{-u})$. The discarded event has probability at most a constant times $A^{-\rho}n^{-\rho}$. Choose $A$ first and then make the ghost-deficit coefficient sufficiently small for that fixed $A$. The independent-layer argument L6K3 instead marks the added mass directly, avoiding the inside-avoidance factor. Neither argument gives an outer-mass bound when $\rho=0$ and infinite full clusters occur.</p>

## Lower tails for the modified critical-dimensional family {#section-fictitious-lower-tail}

<a id="tag-2Z34" data-assertion="proposition" data-title="Counterfactual moment bounds give a uniform lower tail below the biased mean"></a>
<p>For this section and the critical-dimensional results below, use the normalized radial model of <a href="/tag/C0OR/">C0OR</a>, set $d=3\alpha$, and suppose that the <a href="/tag/CXTO/">modified hydrodynamic condition fails</a>. This is a counterfactual hypothesis throughout. Write $X=|K_o|$ under the modified law and put</p>
<div class="math-display">$$\chi_\lambda(r)=\widetilde{\mathbb E}_{r,\lambda}X,\qquad
m_{k,\lambda}(r)=\widetilde{\mathbb E}_{r,\lambda}X^k,\qquad
g_\lambda(r)=\frac{m_{2,\lambda}(r)}{\chi_\lambda(r)}.$$</div>
<p>There are $c&gt;0$ and $0&lt;\lambda_0\leq1/2$ such that</p>
<div class="math-display">$$\widetilde{\mathbb P}_{r,\lambda}(X\geq n)\geq c\lambda^8 n^{-1/2}
\qquad\left(r\geq1,\ 0&lt;\lambda\leq\lambda_0,\ 1\leq n\leq\tfrac12g_\lambda(r)\right).$$</div>
<p>The threshold $n$ may be real. No monotonicity of $g_\lambda$ is asserted.</p>
<p><em>Proof.</em> Fix a radius and suppress its subscripts. Under size bias by $X$, the mean is $g=m_2/\chi$. Paley–Zygmund, the <a href="/tag/9WYX/">mixed third-moment bound</a>, and <a href="/tag/BTM3/">the all-scale moment bounds</a> give</p>
<div class="math-display">$$\widehat{\mathbb P}(X\geq g/2)
\geq\frac{m_2^2}{4\chi m_3}
\geq\frac{m_2}{12\chi^3}\geq c_0\lambda^4.$$</div>
<p>Markov's inequality under the same law removes the part above $B\lambda^{-4}g$, with $B$ fixed sufficiently large. Thus the event $A=\{g/2\leq X\leq B\lambda^{-4}g\}$ has biased probability at least $c_0\lambda^4/2$. Removing the bias on this same event gives</p>
<div class="math-display">$$\mathbb P(A)=\chi\widehat{\mathbb E}[X^{-1}\mathbf1_A]
\geq\frac{\chi\lambda^4}{Bg}\widehat{\mathbb P}(A)
\geq c_1\lambda^8\frac{\chi}{g}
\geq c_1\lambda^8g^{-1/2}.$$</div>
<p>The last step uses $g\leq\chi^2$, from the tree-graph bound. The scale in the last denominator is the biased mean $g$, not the unweighted mean $\chi$.</p>
<p>The moments, hence their positive ratio $g_\lambda$, are continuous on every compact radius interval: finite-edge moments are continuous, and upper-endpoint critical cutoff moments dominate their limits. Also $g_\lambda(1)\leq\chi_0(1)^2=:B_0&lt;\infty$, uniformly in $\lambda$. If $g_\lambda(1)/2\leq n\leq g_\lambda(r)/2$, the intermediate value theorem gives $s\in[1,r]$ with $g_\lambda(s)=2n$. Apply the preceding bound at $s$ and use stochastic monotonicity of the modified family. If $1\leq n&lt;g_\lambda(1)/2$, apply it at radius one instead; $g_\lambda(1)\leq B_0$ absorbs this bounded range into the constant. This proves the claim without extending the modified law to inadmissible small radii.</p>
<p>The <a href="/errata/hutchcroft-lrp-3/#biased-tail-conversion">provisional source entry</a> records the event and scale corrections in the unbiasing display of Lemma III.3.21. The argument here uses the same event on both sides of the change of measure.</p>

## A deficit on a multiplicative interval {#section-fictitious-cap-deficit}

<a id="tag-2HXZ" data-assertion="proposition" data-title="Counterfactual lower tails force capped susceptibility below the critical threshold on nearby scales"></a>
<p>Under the preceding model and failure hypothesis, for each fixed $0&lt;\lambda\leq\lambda_0$ there are $\delta_1&gt;0$, $\eta\in(0,1)$, $L&gt;1$ and $R_1&lt;\infty$ such that every $r\geq R_1$ admits $s\in[r,Lr]$ with</p>
<div class="math-display">$$T_\lambda(s,\delta_1s^{2\alpha})
\leq(1-\eta)\frac{\alpha}{\beta_c}s^\alpha,
\qquad T_\lambda(s,m)=\widetilde{\mathbb E}_{s,\lambda}(X\wedge m).$$</div>
<p>All four choices may depend on $\lambda$. The law and normalization in the selected estimate are both evaluated at $s$.</p>
<p><em>Proof.</em> BTM3 gives $g_\lambda(s)\geq c\lambda^2s^{2\alpha}$. If $\delta\leq c'\lambda^2$, the lower-tail estimate above and the layer-cake identity give, for all sufficiently large $s$,</p>
<div class="math-display">$$T_\lambda(s,2\delta s^{2\alpha})-T_\lambda(s,\delta s^{2\alpha})
=\int_{\delta s^{2\alpha}}^{2\delta s^{2\alpha}}\widetilde{\mathbb P}_{s,\lambda}(X&gt;t)\,dt
\geq b\lambda^8\sqrt\delta\,s^\alpha.$$</div>
<p>Integer values of $X$ cause no error: except at a null set of integration points, use the estimate at $n=\lceil t\rceil\leq2t$, making $\delta$ smaller once to stay below $g_\lambda(s)/2$.</p>
<p>The <a href="/tag/KPBJ/">capped cutoff derivative</a>, with its sharp window input supplied by MRZO, gives</p>
<div class="math-display">$$(\log\chi_\lambda)'(s)
\geq a_\lambda(s)\bigl[T_\lambda(s,2\delta s^{2\alpha})-2C\delta s^\alpha\bigr],
\qquad a_\lambda(s)=\beta_\lambda(s)|j'(s)||N_s|\sim\beta_cs^{-\alpha-1}.$$</div>
<p>The additional intensity contribution is nonnegative. The common Russo identity permits the cap to be chosen at each radius in this lower bound for the untruncated derivative. Choose a positive $\delta\leq c'\lambda^2$ so small that $2C\delta\leq b\lambda^8\sqrt\delta/2$. Set $b_* = b\lambda^8\sqrt\delta/2$ and $A_* = \alpha/\beta_c$. We have obtained</p>
<div class="math-display">$$(\log\chi_\lambda)'(s)
\geq a_\lambda(s)\bigl[T_\lambda(s,\delta s^{2\alpha})+b_*s^\alpha\bigr].$$</div>
<p>Choose $\eta&gt;0$ with $\eta A_*\leq b_*/4$ and $\eta&lt;1$. If the claimed deficit failed at every point of an interval $[r,Lr]$, then, once $r$ is sufficiently large, the last display would imply</p>
<div class="math-display">$$(\log\chi_\lambda)'(s)\geq\frac{\alpha+\beta_cb_*/2}{s}
\quad\text{a.e. on }[r,Lr].$$</div>
<p>The asymptotic for $a_\lambda$ justifies this strict improvement uniformly beyond a fixed radius. But the two susceptibility bounds in BTM3 imply</p>
<div class="math-display">$$\log\frac{\chi_\lambda(Lr)}{\chi_\lambda(r)}
\leq\alpha\log L+\log(C_*/\lambda).$$</div>
<p>Fix $L$ large enough that $(\beta_cb_*/2)\log L&gt;\log(C_*/\lambda)$. Integration is then contradictory. Take $\delta_1=\delta$. Continuity of the fixed-radius moments and the cap also ensures that a minimum on this compact interval is attained, although the contradiction only requires one point satisfying the weak bound.</p>
<p>This gives the useful eventual, quantified form of Lemma III.3.22. The <a href="/errata/hutchcroft-lrp-3/#mesoscopic-selected-radius">provisional source entry</a> records the differing radius indices in its statement and proof. The derivative coefficient above is the actual modified intensity; only its large-radius asymptotic is replaced by $\beta_c$.</p>

## A fixed cap below the Riccati threshold {#section-riccati-linear-error}

<a id="tag-19IN" data-assertion="proposition" data-title="A linear error preserves subthreshold Riccati propagation"></a>
<p>Let $\alpha,A&gt;0$, $0\leq e&lt;\alpha$, and let $f&gt;0$ be locally absolutely continuous on $[r_0,\infty)$, with</p>
<div class="math-display">$$f'(t)\leq At^{-\alpha-1}f(t)^2+et^{-1}f(t)
\quad\text{for almost every }t\geq r_0.$$</div>
<p>If $r\geq r_0$ and $f(r)\leq(\alpha-e)r^\alpha/A$, then for every $R\geq r$,</p>
<div class="math-display">$$f(R)\leq\left(\frac Rr\right)^e
\left[\frac1{f(r)}-\frac{A}{(\alpha-e)r^\alpha}
+\frac{A}{(\alpha-e)r^\alpha}\left(\frac rR\right)^{\alpha-e}\right]^{-1}.$$</div>
<p>The denominator is positive at every finite $R$. If, more strongly, $f(r)\leq(1-\theta)(\alpha-e)r^\alpha/A$ for $0&lt;\theta&lt;1$, then</p>
<div class="math-display">$$f(R)\leq\theta^{-1}(R/r)^e f(r).$$</div>
<p><em>Proof.</em> The reciprocal of $t^{-e}f(t)$ is locally absolutely continuous. The differential inequality yields</p>
<div class="math-display">$$\left(\frac{t^e}{f(t)}\right)'\geq-At^{e-\alpha-1}.$$</div>
<p>Integrate from $r$ to $R$ and divide by $r^e$. The resulting lower bound on $(R/r)^e/f(R)$ is exactly the bracket above. Its first two terms have nonnegative sum, and its last term is strictly positive. Under the stronger hypothesis the first two terms already sum to at least $\theta/f(r)$, which proves the second estimate.</p>
<p>The <a href="/errata/hutchcroft-lrp-3/#riccati-linear-rearrangement">provisional correction to Lemma III.3.23</a> concerns only its rearranged formulas. Its integrating-factor argument gives the bound displayed here. Substituting $R=r$ recovers $f(r)$, as a consistency check.</p>

## Negligibility at the critical dimension {#section-fictitious-negligibility}

<a id="tag-Q7O9" data-assertion="theorem" data-title="Failure of modified hydrodynamics forces critical-dimensional mesoscopic negligibility"></a>
<p>Under the normalized radial model, $d=3\alpha$, and failure of the modified hydrodynamic condition, for every $\varepsilon&gt;0$ there is $\delta&gt;0$ such that</p>
<div class="math-display">$$\mathbb E_{\beta_c,r}\min(|K_o|,\delta r^{2\alpha})
\leq\varepsilon r^\alpha\qquad\text{for every }r\geq1.$$</div>
<p>This is an absolute bound on the critical cutoff mean. It does not assume that the untruncated critical cutoff susceptibility has order $r^\alpha$.</p>
<p><em>Proof.</em> Fix one $\lambda\in(0,\lambda_0]$ and the constants $\delta_1,\eta,L,R_1$ in 2HXZ. Choose $A&gt;\beta_c$ and $0&lt;e&lt;\alpha$ sufficiently close to $\beta_c$ and zero, respectively, that</p>
<div class="math-display">$$(1-\eta)\frac\alpha{\beta_c}
\leq(1-\eta/2)\frac{\alpha-e}{A}.$$</div>
<p>By <a href="/tag/89T0/">the real-cap path bound</a> and $|j'(t)||N_t|\sim t^{-\alpha-1}$, choose $0&lt;\delta_0\leq\delta_1$ and $R_2\geq R_1$ so that, whenever a fixed cap $m$ satisfies $m\leq\delta_0t^{2\alpha}$ and $t\geq R_2$,</p>
<div class="math-display">$$\partial_tT_\lambda(t,m)
\leq At^{-\alpha-1}T_\lambda(t,m)^2+et^{-1}T_\lambda(t,m)
\quad\text{a.e.}$$</div>
<p>Let $H&gt;1$ be a number to be fixed. Given any $R\geq LHR_2$, put $r=R/(LH)$ and hold $m=\delta_0r^{2\alpha}$ fixed. The deficit gives an $s\in[r,Lr]$ at which</p>
<div class="math-display">$$T_\lambda(s,m)\leq T_\lambda(s,\delta_1s^{2\alpha})
\leq(1-\eta/2)\frac{\alpha-e}{A}s^\alpha.$$</div>
<p>For every $t\geq s$, the same cap meets $m\leq\delta_0t^{2\alpha}$. Apply 19IN with $\theta=\eta/2$. Since $s\leq R/H$, this gives</p>
<div class="math-display">$$T_\lambda(R,m)\leq C(R/s)^e s^\alpha
\leq C H^{-(\alpha-e)}R^\alpha.$$</div>
<p>The constant is independent of $R,H$. Thus, for any $q&gt;0$, one can first fix $H$ large enough that the right side is at most $qR^\alpha$. The cap is then $m=\delta_0(LH)^{-2\alpha}R^{2\alpha}$ at every sufficiently large $R$, not merely along a sequence of selected radii.</p>
<p>Now increase the intensity at this fixed cutoff and cap. With $F(\beta)=\mathbb E_{\beta,R}(X\wedge m)$, D7A5 gives $F'\leq MF^2$ throughout $[\beta_\lambda(R),\beta_c]$ in its integrated form; cutoff susceptibility is finite there by DR1W. Consequently</p>
<div class="math-display">$$\frac1{F(\beta_c)}\geq\frac1{F(\beta_\lambda(R))}-M\beta_c\lambda R^{-\alpha}
\geq(q^{-1}-M\beta_c\lambda)R^{-\alpha}.$$</div>
<p>Choose $q$ so that $2q\leq\varepsilon$ and $qM\beta_c\lambda\leq1/2$. It follows that $F(\beta_c)\leq2qR^\alpha\leq\varepsilon R^\alpha$. Finally shrink the resulting cap coefficient, if necessary, to at most $\varepsilon(LHR_2)^{-\alpha}$. For $1\leq R\leq LHR_2$ the elementary bound $F(\beta_c)\leq m\leq\varepsilon R^\alpha$ now suffices; shrinking the cap preserves the estimate at larger radii. This proves the uniform conclusion.</p>
<p>The strict inequality $e&lt;\alpha$ supplies the decay $H^{-(\alpha-e)}$. At the critical dimension the earlier theorem KKGL cannot supply this argument: its assumption $\kappa&lt;2\alpha$ excludes the present cap scale. The fixed-cap score bound and the separate deficit estimate are what replace that strict-dimensional gain.</p>

## Cubic moments uniformly down to the critical law {#section-fictitious-cubic-moments}

<a id="tag-XHJ4" data-assertion="theorem" data-title="Counterfactual negligibility removes the parameter loss in the second moment"></a>
<p>Under the same model and failure hypothesis, there are $c_1,c_2&gt;0$ and $\lambda_0&gt;0$ such that</p>
<div class="math-display">$$m_{2,\lambda}(r)\geq c_1r^{2\alpha}\chi_\lambda(r),\qquad
c_2\chi_\lambda(r)^3\leq m_{2,\lambda}(r)\leq\chi_\lambda(r)^3
\qquad(r\geq1,\ 0\leq\lambda\leq\lambda_0).$$</div>
<p>In particular these estimates include $\lambda=0$, the critical cutoff law. Their constants are uniform in $\lambda$.</p>
<p><em>Proof.</em> C0OR, with a bounded-radius adjustment using $X\geq1$, gives $\chi_\lambda(r)\geq c_*r^\alpha$ uniformly. Apply Q7O9 with $\varepsilon=c_*/2$, and denote its cap coefficient by $\delta$. Stochastic domination by the critical cutoff yields</p>
<div class="math-display">$$\widetilde{\mathbb E}_{r,\lambda}[X;X\geq\delta r^{2\alpha}]
\geq\chi_\lambda(r)-T_\lambda(r,\delta r^{2\alpha})
\geq\tfrac12\chi_\lambda(r).$$</div>
<p>Multiplication by $\delta r^{2\alpha}$ proves the first inequality. Choose a fixed $B\geq2$ large enough that</p>
<div class="math-display">$$U=\left(B\sqrt{\chi_\lambda(r)m_{2,\lambda}(r)}\right)^{1/(2\alpha)}\geq r\geq1.$$</div>
<p>The preceding lower bounds ensure such a uniform choice. Since $m_2\leq\chi^3$, truncating at $U^{2\alpha}$ loses at most</p>
<div class="math-display">$$\widetilde{\mathbb E}_{r,\lambda}[X;X&gt;U^{2\alpha}]
\leq\frac{m_2}{U^{2\alpha}}
=\frac1B\sqrt{\frac{m_2}{\chi}}\leq\frac\chi B.$$</div>
<p>Thus $\chi\leq2T_\lambda(r,U^{2\alpha})$. Dominate this law by the critical cutoff at radius $U$, and use <a href="/tag/0NU2/">the critical capped-mean bound</a>:</p>
<div class="math-display">$$\chi\leq2\mathbb E_{\beta_c,U}\min(X,U^{2\alpha})\leq C U^\alpha.$$</div>
<p>Taking fourth powers and using $U^{4\alpha}=B^2\chi m_2$ gives $\chi^3\leq C' m_2$. The upper bound is the tree-graph inequality. This proves both estimates with no limiting argument in $\lambda$.</p>
<p>These are the two moment improvements of Lemmas III.3.24–III.3.25. They supply uniform size-biased Paley–Zygmund bounds, but a claimed volume-tail estimate must still check its threshold range and the cutoff-to-full comparison. Neither the final hydrodynamic contradiction nor a formalized theorem follows from this counterfactual chain alone.</p>

## Mean-field tails and the cutoff threshold {#section-fictitious-full-tail}

<a id="tag-40HT" data-assertion="theorem" data-title="Counterfactual negligibility gives full mean-field tails and a specified cutoff window"></a>
<p>Retain the normalized radial model, $d=3\alpha$, and failure of the modified hydrodynamic condition. There are constants $a,c,C&gt;0$ such that the full critical cluster $T=|K_o|$ satisfies</p>
<div class="math-display">$$c n^{-1/2}\leq\mathbb P_{\beta_c}(T\geq n)\leq C n^{-1/2}
\qquad(n\geq1).$$</div>
<p>Every critical cutoff law has the same upper bound. Its lower bound holds in the explicit window</p>
<div class="math-display">$$\mathbb P_{\beta_c,r}(|K_o|\geq n)\geq c n^{-1/2}
\qquad(r\geq1,\ 1\leq n\leq a r^{2\alpha}).$$</div>
<p>These are uniform two-sided comparisons, not limiting amplitudes. The coefficient $a$ is a fixed model-dependent constant and is not asserted to be one.</p>
<p><em>Proof.</em> The missing intensity from the soft cutoff is $J-J_r=\min(J,j(r))$. Lattice-point counting bounds its row inside the norm ball by $Cr^dj(r)\leq Cr^{-\alpha}$. The annulus $2^kr&lt;\|z\|\leq2^{k+1}r$ contributes at most $Cr^{-\alpha}2^{-k\alpha}$. Summation, with a bounded-radius adjustment, gives a row bound $Cr^{-\alpha}$ for every $r\geq1$. The independent added layer at intensity $\beta_c$ has a probability row no larger than this up to a fixed factor.</p>
<p>Let $X_r$ have the critical cutoff law, put $G(h)=\mathbb E_{\beta_c}(1-e^{-hT})$ and $G_r(h)=\mathbb E(1-e^{-hX_r})$. Cutoff clusters are finite by DR1W, so <a href="/tag/BEJT/">the independent-layer ghost comparison</a> applies:</p>
<div class="math-display">$$G_r(h)\leq G(h)\leq G_r(h)+D r^{-\alpha}\mathbb E[X_r e^{-hX_r}]G(h).$$</div>
<p>Choose $\varepsilon&gt;0$ with $D\varepsilon\leq1/2$, and let $\delta&gt;0$ be the coefficient in Q7O9. For small $h&gt;0$ choose the real radius $r=(\delta h)^{-1/(2\alpha)}\geq1$, so that $1/h=\delta r^{2\alpha}$. The elementary inequalities</p>
<div class="math-display">$$xe^{-hx}\leq\min(x,1/h),\qquad
1-e^{-hx}\leq h\min(x,1/h)$$</div>
<p>give an error coefficient at most $D\varepsilon$ and $G_r(h)\leq h\varepsilon r^\alpha$. Hence</p>
<div class="math-display">$$G(h)\leq2\varepsilon\delta^{-1/2}\sqrt h.$$</div>
<p>Taking $h=1/n$ proves the full-tail upper bound for large $n$, since $(1-e^{-1})\mathbb P(T\geq n)\leq G(1/n)$. Enlarge its constant for the remaining thresholds. Stochastic domination gives the same upper bound for every cutoff.</p>
<p>For the lower bound, XHJ4 gives $m_{2,0}(r)\geq c\chi_0(r)^3$ uniformly. Repeat the size-biased Paley–Zygmund and Markov argument of 2Z34, now with constants independent of a positive modification parameter. It yields</p>
<div class="math-display">$$\mathbb P_{\beta_c,r}(X_r\geq g_0(r)/2)\geq c' g_0(r)^{-1/2},
\qquad g_0(r)=m_{2,0}(r)/\chi_0(r).$$</div>
<p>The same continuous-ratio interpolation on $[1,r]$, including the bounded initial range, proves the bound $c''n^{-1/2}$ for every $1\leq n\leq g_0(r)/2$. The other inequality in XHJ4 gives $g_0(r)\geq c_1r^{2\alpha}$; take $a=c_1/2$. For any fixed $n$, choose a sufficiently large cutoff radius in this range and dominate its cluster by the full critical cluster. This proves the full lower bound.</p>
<p>This proof supplies the cutoff-to-full comparison left implicit in the upper-bound argument of Lemma III.3.20. It does not identify the coefficient $a$ with one in that lemma's printed cutoff range. Extending the lower bound to the entire range $n\leq r^{2\alpha}$ requires an additional argument; neither stochastic monotonicity nor the two-sided moment comparisons change that constant by themselves.</p>
