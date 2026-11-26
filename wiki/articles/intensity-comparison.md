---
{
  "id": "intensity-comparison",
  "title": "Comparing intensities and percolation thresholds",
  "subtitle": "Support connectivity, rescaling and the large-intensity limit",
  "kind": "method",
  "category": "General theory",
  "summary": "Positive-support paths transfer percolation between roots. Multiplying a kernel divides its critical intensity, while increasing the kernel can only lower the threshold. Pairwise connection at large intensity does not imply a finite percolation threshold.",
  "context": ["A countable vertex set $V$, unless an arbitrary-vertex extension is stated explicitly.", "Independent unordered-pair coordinates with $q_\u03b2(e)=1-e^{-\u03b2 J(e)}$, where $J(e)$ and $\u03b2$ are finite and nonnegative.", "Diagonal coordinates are discarded by the open graph. Thresholds lie in $[0,\\infty]$, with $\\inf\\varnothing=\\infty$."],
  "related": ["criticality", "harris-inequality", "connection-paths", "profile-continuity", "walk-kernels", "infinite-cluster-zero-one"],
  "sourceIds": ["perclib-intensity-monotone", "perclib-intensity-scaling", "perclib-root-independence"],
  "aliases": ["root independence", "kernel scaling", "critical intensity comparison", "support graph", "sprinkling", "large intensity"],
  "prototypeUses": ["criticality"]
}
---

## Sprinkling and the threshold {#section-threshold}

<p>Write $\mathbb P_\beta^J$ for the exponential-intensity law, $\theta_\beta^J(x)=\mathbb P_\beta^J(|K_x|=\infty)$, and $\Theta_\beta^J=\mathbb P_\beta^J(\exists x:|K_x|=\infty)$. The <a href="/tag/8DAH/">root threshold</a> $\beta_c^J(x)$ and the global threshold $\beta_c^{J,\mathrm g}$ are the infima of the finite parameters where the respective probabilities are positive. These are percolation thresholds; no susceptibility criterion is being substituted for their definitions.</p>

<a id="tag-TWLQ" data-assertion="theorem" data-title="Independent intensity layers give monotonicity and threshold separation"></a>
<p>If $\omega_1,\omega_2$ are independent with laws $\mathbb P_{\beta_1}^J,\mathbb P_{\beta_2}^J$, then $\omega_1\cup\omega_2$ has law $\mathbb P_{\beta_1+\beta_2}^J$. Consequently, every measurable increasing event has nondecreasing probability in $\beta$. On countable vertices, for every finite $\beta$,</p>
<div class="math-display">$$\begin{aligned}
\beta<\beta_c^J(x)&\ \Longrightarrow\ \theta_\beta^J(x)=0,&
\beta>\beta_c^J(x)&\ \Longrightarrow\ \theta_\beta^J(x)>0,\\
\beta<\beta_c^{J,\mathrm g}&\ \Longrightarrow\ \Theta_\beta^J=0,&
\beta>\beta_c^{J,\mathrm g}&\ \Longrightarrow\ \Theta_\beta^J>0.
\end{aligned}$$</div>
<p>The law identity and the assertion for measurable increasing events hold on arbitrary vertex sets. Neither requires a row-summability assumption.</p>
<p><em>Proof.</em> A bond is absent from the union precisely when it is absent from both layers. Its closed probability is</p>
<div class="math-display">$$e^{-\beta_1J(e)}e^{-\beta_2J(e)}=e^{-(\beta_1+\beta_2)J(e)}.$$</div>
<p>Distinct bonds use disjoint pairs of independent coordinates, so the union has the stated product law. For $\beta_2\geq\beta_1$, couple the second configuration to the first by adding an independent layer of intensity $\beta_2-\beta_1$. Inclusion of configurations gives monotonicity.</p>
<p>Let $f$ be either percolation probability and let $c=\inf\{b\geq0:f(b)>0\}$. If $f(\beta)>0$, then $c\leq\beta$, proving the assertion below $c$. If $\beta>c$, the definition of infimum supplies a finite $b<\beta$ with $f(b)>0$; monotonicity gives $f(\beta)\geq f(b)>0$. Countability ensures the relevant events are measurable: the global event is the countable union of the rooted events. Each is increasing because adding bonds enlarges every cluster.</p>
<p>There is no conclusion at $\beta=c$. If $c=\infty$, the upper regime contains no finite parameter. At $\beta=0$ all bonds are closed almost surely and all clusters are singletons. This remains compatible with $c=0$: on a countably infinite complete graph with $J(e)=1$ off the diagonal, every positive intensity gives infinite open degree at each fixed vertex by <a href="/tag/XJ74/">the divergent-row degree criterion</a>, while no vertex percolates at zero.</p>

## Transferring percolation between roots {#section-roots}

<p>For an arbitrary bond profile $q$, its support graph has an edge $\{x,y\}$ when $x\ne y$ and $q(\{x,y\})>0$. Write $\theta_q(x)=\mathbb P_q(|K_x|=\infty)$.</p>

<p>The earlier <a href="/tag/C3OO/">positive-path comparison</a> already identifies the roots at which percolation has positive probability, and <a href="/tag/1C8G/">its threshold consequence</a> gives equality within a support component. The following bound retains the full connection probability in place of the probability of one chosen path.</p>

<a id="tag-IYVA" data-assertion="theorem" data-title="Percolation positivity transfers along the support graph"></a>
<p>On a countable vertex set,</p>
<div class="math-display">$$\tau_q(x,y)\theta_q(x)\leq\theta_q(y).$$</div>
<p>If $x$ and $y$ lie in the same support component, then $\theta_q(x)>0$ if and only if $\theta_q(y)>0$. In particular, if the support graph of $J$ is connected, then for every root $x$,</p>
<div class="math-display">$$\beta_c^J(x)=\beta_c^{J,\mathrm g}.$$</div>
<p>No transitive action or uniform lower bound on the positive bond probabilities is required.</p>
<p><em>Proof.</em> Both $\{x\leftrightarrow y\}$ and $\{|K_x|=\infty\}$ are increasing and measurable. <a href="/tag/X5SS/">Harris's inequality</a> gives</p>
<div class="math-display">$$\tau_q(x,y)\theta_q(x)\leq\mathbb P_q(x\leftrightarrow y,\ |K_x|=\infty)\leq\theta_q(y).$$</div>
<p>The last inclusion follows from $K_x=K_y$ whenever $x$ and $y$ are connected: concatenate a connection with any further path. If a finite support path $P$ joins the roots, its distinct bonds all have positive probability, and the <a href="/tag/9IPM/">specified-path bound</a> gives $\tau_q(x,y)\geq\prod_{e\in E(P)}q(e)>0$. Apply the displayed inequality in both directions.</p>
<p>At every positive intensity the support graph of $q_\beta$ is exactly that of $J$, since $1-e^{-\beta J(e)}>0$ precisely when $J(e)>0$. Moreover,</p>
<div class="math-display">$$\Theta_\beta^J>0\quad\Longleftrightarrow\quad\exists y\in V:\theta_\beta^J(y)>0,$$</div>
<p>because a countable union of null events is null. Connected support therefore makes the global and every rooted positivity condition equivalent. They also agree at zero, where both fail. Their parameter sets coincide, so their infima coincide.</p>
<p>This is equality of thresholds and of positivity conditions, not equality of the values $\theta_q(x)$. Without connected support, the argument applies within each support component. The global threshold is still <a href="/tag/JZN0/">the infimum of the rooted thresholds</a>, and in particular is no greater than any one of them. A root in an isolated component can have threshold infinity while another component percolates at a finite intensity. On the empty vertex set the global event is empty; on a singleton every cluster is finite, regardless of the diagonal coordinate.</p>

## Changing the unit of intensity {#section-scaling}

<a id="tag-IJOB" data-assertion="proposition" data-title="Kernel rescaling divides the critical intensities"></a>
<p>For every finite $c>0$,</p>
<div class="math-display">$$\mathbb P_\beta^{cJ}=\mathbb P_{c\beta}^{J},\qquad
\beta_c^{cJ}(x)=\frac{\beta_c^J(x)}c,\qquad
\beta_c^{cJ,\mathrm g}=\frac{\beta_c^{J,\mathrm g}}c.$$</div>
<p>The quotients are extended-valued, so infinity remains infinity. For $c=0$, both thresholds are infinity on countable vertices.</p>
<p><em>Proof.</em> The profiles agree because $\beta(cJ(e))=(c\beta)J(e)$. The map $\beta\mapsto c\beta$ is an order-preserving bijection of the finite nonnegative parameters. Thus, if $S$ is either positive-probability parameter set for $J$, the corresponding set for $cJ$ is $c^{-1}S$. Multiplication by a positive finite constant preserves infima in $[0,\infty]$, including the infimum of the empty set. This proves the two threshold identities.</p>
<p>For $c=0$, the off-diagonal row sums vanish. All opening probabilities are zero, and countability makes every bond closed simultaneously almost surely. The positive-probability parameter sets are empty. This case is proved directly; it is not obtained by dividing a possibly zero threshold by zero.</p>
<p>The profile identity and the positive-scaling infimum argument need no countability, continuity or monotonicity of a percolation event. More generally, if $g(\beta)=f(c\beta)$ for any nonnegative function $f$, then the infimum of the parameters where $g$ is positive is $c^{-1}$ times the corresponding infimum for $f$. If nonmeasurable events are allowed on arbitrary vertex sets, the same algebra applies to their product outer measures; ordinary probability language requires measurability.</p>

## Comparing two kernels {#section-order}

<a id="tag-CKJQ" data-assertion="theorem" data-title="A larger kernel increases connection observables and lowers thresholds"></a>
<p>Let $V$ be countable, and let $J,J'$ be finite nonnegative kernels with $J(e)\leq J'(e)$ on every non-diagonal pair. For every finite $\beta\geq0$,</p>
<div class="math-display">$$\tau_\beta^J(x,y)\leq\tau_\beta^{J'}(x,y),\qquad
\theta_\beta^J(x)\leq\theta_\beta^{J'}(x),\qquad
\Theta_\beta^J\leq\Theta_\beta^{J'},\qquad
\chi_\beta^J(x)\leq\chi_\beta^{J'}(x).$$</div>
<p>Consequently,</p>
<div class="math-display">$$\beta_c^{J'}(x)\leq\beta_c^J(x),\qquad
\beta_c^{J',\mathrm g}\leq\beta_c^{J,\mathrm g}.$$</div>
<p>Susceptibilities and thresholds may be infinite; no summability is assumed.</p>
<p><em>Proof.</em> Erase the diagonal in both profiles, which <a href="/tag/EYCQ/">preserves the graph observables</a>. Since $t\mapsto1-e^{-\beta t}$ is increasing, the remaining profiles are ordered. The <a href="/tag/6B9V/">monotone product coupling</a> gives configurations with $\omega\subseteq\omega'$ almost surely. Connections persist and clusters enlarge, proving the event inequalities and the extended expectation inequality. The positive-probability parameter set for $J$ is contained in that for $J'$, so its infimum is at least as large.</p>
<p>The source module states kernel comparison on all coordinates. Allowing unrelated diagonal values here is the separate loop-erasure deduction. For $0<a\leq b<\infty$ and $aJ\leq J'\leq bJ$ off the diagonal, comparison and rescaling give</p>
<div class="math-display">$$\frac{\beta_c^J(x)}b\leq\beta_c^{J'}(x)\leq\frac{\beta_c^J(x)}a,$$</div>
<p>and the same inequalities for global thresholds. Strict kernel inequalities do not by themselves give strict threshold inequalities: every finite host has infinite percolation threshold, even when all its edge intensities increase strictly.</p>

## Large intensity on a fixed support path {#section-large-intensity}

<p>For a fixed pair $e$, the function $q_\beta(e)$ is continuous and nondecreasing in $\beta$. It is identically zero when $J(e)=0$, and is strictly increasing to one when $J(e)>0$.</p>

<a id="tag-QZVQ" data-assertion="proposition" data-title="Fixed support connections become certain in the large-intensity limit"></a>
<p>If $x,y$ are joined in the support graph of $J$, then</p>
<div class="math-display">$$\lim_{\beta\to\infty}\tau_\beta^J(x,y)=1.$$</div>
<p>On arbitrary vertex sets the same conclusion holds for the product outer measure of the connection event.</p>
<p><em>Proof.</em> Fix one finite support path $P$. Each $J(e)$ on this path is positive, so</p>
<div class="math-display">$$\prod_{e\in E(P)}(1-e^{-\beta J(e)})\leq\tau_\beta^J(x,y)\leq1,$$</div>
<p>and the finite product tends to one. The <a href="/tag/9IPM/">path lower bound</a> is valid for outer measure without ambient countability, so the same squeeze proves that version. If $x=y$, the empty path already has weight one.</p>
<p>For any fixed finite set of vertices in one support component, choose finitely many such paths joining them to one root. Opening the finite union of their bonds connects the whole set, and its probability tends to one. This does not permit an interchange with an infinite set of vertices. On the nearest-neighbour line with unit edge intensities,</p>
<div class="math-display">$$\tau_\beta(0,n)=(1-e^{-\beta})^{|n|}\longrightarrow1\qquad(\beta\to\infty)$$</div>
<p>for every fixed $n$. Yet for each finite $\beta$, the probability of an open ray from any fixed vertex is $\lim_{m\to\infty}(1-e^{-\beta})^m=0$ in either direction. An infinite cluster on the line must contain one of those rays. Countability therefore gives no infinite cluster anywhere, and $\beta_c^{\mathrm g}=\infty$. Pairwise convergence at large intensity supplies neither a finite threshold nor percolation at an infinite parameter.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-intensity/">source-contract inventory</a> records the distinct countability assumptions of the three modules. The off-diagonal comparison, two-sided multiplicative comparison and finite-set consequence above are expository deductions. Their inclusion does not create compiled tag associations or correspondence reviews.</p>
