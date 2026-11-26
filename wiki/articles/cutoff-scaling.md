---
{
  "id": "cutoff-scaling",
  "title": "Cutoff scaling relations",
  "subtitle": "What uniform tail and two-point estimates imply",
  "kind": "method",
  "category": "Critical theory",
  "summary": "Explicit cutoff hypotheses yield moment scales and familiar exponent identities. The estimates explain the scaling argument without assuming that its hypotheses hold in a given percolation model.",
  "context": ["The notation $f\\asymp g$ means two-sided bounds by positive constants independent of the parameter tending to its limit.", "The cutoff estimates below are hypotheses, not asserted properties of every percolation model.", "Cluster-volume variables are positive integer-valued; expectations may initially be extended nonnegative quantities."],
  "related": ["criticality", "susceptibility", "binary-tree-percolation", "triangle-condition", "cutoff-families"],
  "sourceIds": ["hutchcroft-book"],
  "aliases": ["scaling relations", "gap exponent", "gap scale", "moment cutoff", "correlation length", "Fisher relation"],
  "prototypeUses": []
}
---

## A volume cutoff {#section-volume}

<a id="tag-QT3F" data-assertion="theorem" data-title="Uniform power-law cutoff bounds determine moment scales"></a><p>Fix $0&lt;a&lt;1$. Let $(T_z)_{z\geq2}$ be positive integer-valued random variables. Suppose constants $c,C,b&gt;0$, independent of $z$, satisfy</p><div class="math-display">$$\mathbb P(T_z\geq n)\leq Cn^{-a}e^{-bn/z}\quad(n\geq1),\qquad \mathbb P(T_z\geq n)\geq cn^{-a}\quad(1\leq n\leq z).$$</div><p>For every fixed real $k&gt;a$,</p><div class="math-display">$$\mathbb E T_z^k\asymp z^{k-a}.$$</div><p>In particular, $\mathbb E T_z\asymp z^{1-a}$ and $\mathbb E T_z^2/\mathbb E T_z\asymp z$. The constants in the moment estimate may depend on $k$.</p><p><em>Proof.</em> Summation of the increments of $n^k$ gives the exact identity</p><div class="math-display">$$\mathbb E T_z^k=\sum_{n=1}^{\infty}\bigl(n^k-(n-1)^k\bigr)\mathbb P(T_z\geq n).$$</div><p>For fixed $k&gt;0$, the increment is comparable to $n^{k-1}$. The lower bound therefore dominates a constant times $\sum_{n\leq z}n^{k-a-1}$, which is comparable to $z^{k-a}$ because $k&gt;a$. For the upper bound, the same comparison gives $\sum_{n\geq1}n^{k-a-1}e^{-bn/z}$. Split at $z$ and then into blocks $2^jz&lt;n\leq2^{j+1}z$. The first block is $O(z^{k-a})$; the later blocks are bounded by a constant times $z^{k-a}2^{(j+1)(k-a)}e^{-b2^j}$, whose coefficients are summable. This also proves finiteness of the moments in question. Taking $k=1,2$ gives the ratio statement.</p>

<p>The exact tail sum starts at $n=1$. A term at $n=0$ would add one in the first-moment identity. The cutoff hypothesis is stronger than a statement about logarithmic exponents alone.</p>

## Consequences for volume exponents {#section-exponents}

<a id="tag-ADN0" data-assertion="corollary" data-title="Volume scaling identities under cutoff and matching hypotheses"></a><p>Suppose the preceding bounds hold uniformly along a subcritical family, with $a=1/\delta$, $\delta&gt;1$, cutoff $z(\varepsilon)\asymp\varepsilon^{-\Delta}$ and $\Delta&gt;0$, where $\varepsilon\downarrow0$ measures distance from criticality. Then</p><div class="math-display">$$\chi(\varepsilon)\asymp\varepsilon^{-\gamma},\qquad \gamma=\frac{\delta-1}{\delta}\Delta,$$</div><p>and for each fixed $k&gt;1/\delta$,</p><div class="math-display">$$\mathbb E T_{z(\varepsilon)}^k\asymp\varepsilon^{-\gamma-(k-1)\Delta}.$$</div><p>If, in addition, a supercritical survival probability satisfies the separate matching assumption $\theta(\varepsilon)\asymp z(\varepsilon)^{-1/\delta}$, then its exponent is $\beta=\Delta/\delta$, and $\beta+\gamma=\Delta$.</p><p><em>Proof.</em> Substitute the cutoff scale into the moment estimate. The identity $k-1/\delta=(1-1/\delta)+(k-1)$ gives the displayed exponent. The additional matching assumption gives $\beta$ directly; adding the two exponents gives $\Delta$.</p><p>The subcritical tail bounds do not imply the supercritical matching assumption. It expresses additional information about how finite clusters and the infinite cluster fit together across the transition.</p>

## A spatial cutoff {#section-spatial}

<a id="tag-CAV9" data-assertion="theorem" data-title="Radial two-point cutoff bounds determine susceptibility scaling"></a><p>On $\mathbb Z^d$, let $d\geq1$, $2-d\leq\eta&lt;2$, and $\xi\geq2$. Suppose $\tau_\xi(0)=1$ and, writing $r=\|x\|_\infty$, there are constants $c,C,b&gt;0$ independent of $\xi$ such that</p><div class="math-display">$$\tau_\xi(x)\leq Cr^{-d+2-\eta}e^{-br/\xi}\quad(x\neq0),\qquad \tau_\xi(x)\geq cr^{-d+2-\eta}\quad(1\leq r\leq\xi).$$</div><p>Then $\sum_x\tau_\xi(x)\asymp\xi^{2-\eta}$. If $\xi(\varepsilon)\asymp\varepsilon^{-\nu}$, this gives the susceptibility exponent $\gamma=(2-\eta)\nu$.</p><p><em>Proof.</em> The shell $\{x:\|x\|_\infty=r\}$ has $(2r+1)^d-(2r-1)^d\asymp r^{d-1}$ vertices. Summing the lower bound through $r\leq\xi$ gives $\sum_{r\leq\xi}r^{1-\eta}\asymp\xi^{2-\eta}$. Summing the upper bound gives the corresponding exponentially cut off series, bounded by the same dyadic-block argument as above. The root contributes one, which is absorbed because $2-\eta&gt;0$.</p>

<p>For a two-point function bounded by one, the restriction $\eta\geq2-d$ makes the lower-bound hypothesis compatible with arbitrarily large cutoffs. An exponential spatial cutoff is a short-range assumption; it should not be transferred without proof to a long-range model whose two-point function has a polynomial tail. At $\eta=2$ the shell sum is logarithmic, so the stated power-law conclusion does not extend to that endpoint.</p>


## Passing cutoff moments to the full law {#section-subcritical-moment-upper}

<a id="tag-T5JS" data-assertion="proposition" data-title="An integrable cutoff hierarchy transfers moment bounds to the full law"></a>
<p>Fix $\alpha&gt;0$. Let $T_r\geq1$, $r\geq1$, be random variables increasing almost surely to $T$, and suppose $X=\mathbb E T&lt;\infty$. Set $\xi=X^{1/\alpha}$. Write $m_p(r)=\mathbb E T_r^p$, and assume these moments are finite and locally absolutely continuous. Suppose, for each integer $p\geq2$,</p>
<div class="math-display">$$m_p'(r)\leq A_pr^{-\alpha-1}\left(m_1(r)m_p(r)+\sum_{\ell=1}^{p-1}m_{\ell+1}(r)m_{p-\ell}(r)\right)\quad\text{for a.e. }r\geq\xi.$$</div>
<p>If a scale $Z\geq1$ satisfies $m_p(\xi)\leq B_pXZ^{p-1}$ for every integer $p\geq1$, then</p>
<div class="math-display">$$\mathbb E T^p\leq C_pXZ^{p-1}\qquad(p\geq1).$$</div>
<p>The constants depend only on $\alpha$ and the constants in the hypotheses up to order $p$. In particular, they are uniform over families with the same input bounds.</p>
<p><em>Proof.</em> The first moment is $X$. Suppose the assertion holds below order $p$. In the derivative bound, absorb the summand $\ell=p-1$, which is $m_pm_1$, into the first term. All remaining factors have order less than $p$. Monotone domination by $T$ and the induction hypothesis give</p>
<div class="math-display">$$m_p'(r)\leq C_pr^{-\alpha-1}X m_p(r)+C_pr^{-\alpha-1}X^2Z^{p-1}.$$</div>
<p>For $p=2$ the remaining sum is empty, so the same bound is valid. Put $G(r)=C_pX\int_\xi^r s^{-\alpha-1}\,ds$. Since $X\xi^{-\alpha}=1$, we have $0\leq G(r)\leq C_p/\alpha$. Integrating the inequality for $e^{-G(r)}m_p(r)$ to a finite $R\geq\xi$ yields</p>
<div class="math-display">$$m_p(R)\leq e^{C_p/\alpha}\left(m_p(\xi)+C_pX^2Z^{p-1}\int_\xi^R r^{-\alpha-1}\,dr\right)
\leq C'_pXZ^{p-1}.$$</div>
<p>Monotone convergence as $R\to\infty$ completes the induction and proves finiteness of the full moments.</p>
<p>For the long-range cutoff, the intended choice is $Z=m_{2,b}(\xi)/m_{1,b}(\xi)$ at the critical parameter $b$. Critical domination, $m_{1,b}(\xi)\asymp\xi^\alpha=X$ and the critical cutoff moment comparison supply the initial bound. This is the analytic implication used in Part II, Lemma II.6.7. The derivative hierarchy and the critical comparison remain inputs; their applicability is not a consequence of the integrating-factor argument.</p>

## Continuity of subcritical moments {#section-moment-continuity}

<a id="tag-IK5Y" data-assertion="proposition" data-title="Finite dominating cluster moments imply continuity in the bond parameter"></a>
<p>Consider independent bond percolation on a countable simple graph, with edge-opening probabilities $q_e(\beta)$ continuous and nondecreasing on $[\beta_0,b)$. Let $T_\beta$ be the size of the root cluster. If $\mathbb E T_\beta^p&lt;\infty$ for every $\beta\in[\beta_0,b)$ and every positive integer $p$, then each map $\beta\mapsto\mathbb E T_\beta^p$ is continuous on this interval, with one-sided continuity at $\beta_0$. In particular,</p>
<div class="math-display">$$a_\beta=\frac{\mathbb E T_\beta^2}{\mathbb E T_\beta}$$</div>
<p>is continuous. No monotonicity of this ratio is asserted.</p>
<p><em>Proof.</em> Couple all edges by independent uniform variables. Fix $\beta&lt;b$ and choose $\beta_+\in(\beta,b)$. The cluster at $\beta_+$ is finite almost surely and contains all root clusters at parameters at most $\beta_+$. On this finite vertex set there are only finitely many possible edges. Almost surely none of their uniform variables equals its opening probability at $\beta$, so continuity of the probabilities makes every one of these edge states constant in a neighborhood of $\beta$. No cluster at a smaller parameter can leave the cluster at $\beta_+$. Thus $T_{\beta'}=T_\beta$ for all sufficiently close $\beta'$, almost surely. Domination by $T_{\beta_+}^p$ gives moment continuity. The denominator in the ratio is at least one.</p>
<p>The larger-parameter cluster supplies the finite random set even on a graph of infinite degree. This justifies the intermediate-value step below for subcritical long-range percolation once the finite full moments have been established.</p>

## The subcritical volume tail {#section-subcritical-volume-tail}

<a id="tag-XANO" data-assertion="theorem" data-title="Critical tails and uniform moment bounds determine the subcritical volume scale"></a>
<p>Let $(T_\beta)_{\beta\in[\beta_0,b)}$ be stochastically nondecreasing positive integer-valued random variables, all stochastically dominated by $T_*\in\mathbb N\cup\{\infty\}$. Put $X_\beta=\mathbb E T_\beta&lt;\infty$ and $F(t)=\mathbb P(T_*\geq t)$. Assume, uniformly for $t\geq1$,</p>
<div class="math-display">$$F(t)\asymp t^{-\rho}L(t),\qquad L(t)=(\log(e+t))^\sigma,$$</div>
<p>where either $0\leq\rho&lt;1$ and $\sigma=0$, or $(\rho,\sigma)=(1/2,1/4)$. Suppose there are scales $Z_\beta\geq1$ such that, uniformly in $\beta$,</p>
<div class="math-display">$$X_\beta\asymp Z_\beta F(Z_\beta),\qquad
\mathbb E T_\beta^p\leq C_pX_\beta Z_\beta^{p-1}\quad\text{for every integer }p\geq1.$$</div>
<p>Assume also that $a_\beta=\mathbb E T_\beta^2/X_\beta$ is continuous and that $\mathbb P(T_{\beta_0}\geq N)&gt;0$ for every finite integer $N$. Then</p>
<div class="math-display">$$a_\beta\asymp Z_\beta,\qquad
\mathbb E T_\beta^p\asymp_p X_\beta Z_\beta^{p-1}\quad(p\geq1).$$</div>
<p>Moreover, there are constants $c,c'&gt;0$ and a nonincreasing function $h:(0,\infty)\to(0,1]$, decaying faster than every power, such that for every $\beta\in[\beta_0,b)$ and integer $n\geq1$,</p>
<div class="math-display">$$c'\mathbf1_{\{n\leq cZ_\beta\}}\leq
\frac{\mathbb P(T_\beta\geq n)}{F(n)}\leq h(n/Z_\beta).$$</div>
<p><em>Proof.</em> Fix $\beta$ and abbreviate $T=T_\beta$, $X=X_\beta$, $Z=Z_\beta$ and $a=a_\beta$. Under the <a href="/tag/6L9Z/">size-biased law</a> $\widehat{\mathbb P}$, the mean of $T$ is $a$. Markov's inequality gives $\widehat{\mathbb P}(T&gt;2a)\leq1/2$. Consequently</p>
<div class="math-display">$$\frac X2\leq\mathbb E[T\mathbf1_{\{T\leq2a\}}]
\leq\mathbb E\min(T,2a)\leq\mathbb E\min(T_*,2a)
=\int_0^{2a}\mathbb P(T_*&gt;t)\,dt
\leq C a^{1-\rho}L(a).$$</div>
<p>Here $a\geq1$, $\rho&lt;1$, $L$ is nondecreasing and $L(2a)\leq C L(a)$. These facts give the last integral estimate directly. The comparison uses the increasing capped variable, not the nonmonotone function $t\mathbf1_{\{t\leq2a\}}$. It remains valid when $T_*$ can be infinite.</p>
<p>Since $X\geq cZ^{1-\rho}L(Z)$, this inequality implies $a\geq c_0Z$: if $a\leq Z$, cancel $L(Z)$ after using $L(a)\leq L(Z)$; if $a&gt;Z$, there is nothing to prove. The second-moment upper bound gives $a\leq C_0Z$. For $p\geq2$, Jensen's inequality under the size-biased law now gives</p>
<div class="math-display">$$\mathbb E T^p=X\widehat{\mathbb E}T^{p-1}\geq Xa^{p-1}\geq c_pXZ^{p-1}.$$</div>
<p>This proves the moment comparisons, including the first moment by definition.</p>
<p>For $n\geq Z$, Markov's inequality and the upper moments yield</p>
<div class="math-display">$$\frac{\mathbb P(T\geq n)}{F(n)}\leq C_p\frac{F(Z)}{F(n)}(n/Z)^{-p}
\leq C'_p(n/Z)^{-p+\rho}.$$</div>
<p>The logarithmic factor only decreases the last ratio because $n\geq Z$. Thus every inverse power is available uniformly. To obtain one positive nonincreasing envelope, let $H(t)$ be the supremum of $\mathbb P(T_\beta\geq n)/F(n)$ over all $\beta,n$ with $n/Z_\beta\geq t$, taking an empty supremum as zero, and set $h(t)=\max(e^{-t},H(t))$. Critical domination gives $H\leq1$, and the preceding bounds give $H(t)\leq C_qt^{-q}$ for every $q&gt;0$ and $t\geq1$. This proves the upper tail assertion. No control on the growth of $C_p$ has been assumed, so an exponential envelope is not inferred.</p>
<p>For the lower bound, apply Paley–Zygmund under the size-biased law. The second- and third-moment comparisons imply</p>
<div class="math-display">$$\widehat{\mathbb P}(T\geq a/2)\geq\frac{a^2}{4\widehat{\mathbb E}T^2}\geq c_1&gt;0.$$</div>
<p>Also $\widehat{\mathbb P}(T&gt;Ma)\leq1/M$. Choose a fixed $M$ with $1/M\leq c_1/2$. Removing that upper tail and undoing the size bias on the resulting interval gives</p>
<div class="math-display">$$\mathbb P(T\geq a/2)\geq\mathbb P(a/2\leq T\leq Ma)
\geq\frac{X}{Ma}\widehat{\mathbb P}(a/2\leq T\leq Ma)
\geq c_2X/Z\asymp F(Z).$$</div>
<p>Choose $c\leq c_0/2$, where $a_\beta\geq c_0Z_\beta$. If $a_{\beta_0}/2\leq n\leq cZ_\beta$, continuity supplies some $\beta'\in[\beta_0,\beta]$ with $a_{\beta'}/2=n$. Applying the preceding bound at $\beta'$ gives $\mathbb P(T_{\beta'}\geq n)\geq cF(Z_{\beta'})\geq c'F(n)$, since $Z_{\beta'}\asymp n$ and the displayed critical tail changes only by a constant factor under a fixed rescaling. Stochastic monotonicity transfers this bound to $\beta$. The finitely many positive integers $n&lt;a_{\beta_0}/2$ are covered by $\mathbb P(T_{\beta_0}\geq n)&gt;0$, after decreasing the constant. The intermediate parameter stays in the interval where the uniform estimates hold. This proves the assertion.</p>
<p>In the long-range application, take $T_\beta=|K|$, $T_*$ the critical full cluster volume, and $Z_\beta$ the critical cutoff ratio at $r=X_\beta^{1/\alpha}$. The required critical tails correspond respectively to $\rho=1/2$ above the critical dimension, $(\rho,\sigma)=(1/2,1/4)$ at it, and $\rho=(d-\alpha)/(d+\alpha)$ below it. The last case includes $\alpha=d$, hence $\rho=0$. T5JS supplies the moment upper bounds under its cutoff inputs, and IK5Y supplies continuity. On an infinite connected positive-intensity graph, a finite tree from the root gives the required positive probabilities at $\beta_0&gt;0$. The critical tails and the relation $X_\beta\asymp Z_\beta F(Z_\beta)$ remain separate model inputs.</p>
<p>This proves the probability implication in Part II, Theorem II.1.15. The <a href="/errata/hutchcroft-lrp-2/#subcritical-capped-expectation">provisional source entry</a> records the replacement of the printed truncated expectation by a cap. The logarithm is regularized at bounded scales; no value of $(\log1)^{-1/2}$ is used.</p>


## The critical inputs in the three dimension regimes {#section-volume-inputs}

<p>The versioned papers use the same soft cutoff: for distinct vertices at norm distance $s$, its intensity is $J_r(s)=\mathbf1_{\{s\leq r\}}\int_s^r|J'(u)|\,du$. The parameter $b=\beta_c$ always belongs to the full kernel. Their common kernel assumptions include radial monotonicity, differentiability and a logarithmically integrable relative error in $|J'(r)|\sim r^{-d-\alpha-1}$; the norm ball has unit volume. A hard distance restriction of the full kernel is a different family.</p>
<p>Write $m_p(r)=\mathbb E_{b,r}|K|^p$, $z(r)=m_2(r)/m_1(r)$, $X=\chi(\beta)$ and $Z=z(X^{1/\alpha})$. The inputs for XANO have the following orders:</p>

| Regime | Critical tail $F(n)$ | Critical cutoff ratio $z(r)$ | Subcritical scale $Z$ |
| --- | --- | --- | --- |
| $d&gt;3\alpha$, $\alpha&lt;2$ | $n^{-1/2}$ | $r^{2\alpha}$ | $X^2$ |
| $d=3\alpha&lt;6$ | $n^{-1/2}(\log(e+n))^{1/4}$ | $r^{2\alpha}(\log(e+r))^{-1/2}$ | $X^2(\log(e+X))^{-1/2}$ |
| $d&lt;3\alpha$, $0&lt;\alpha\leq d$, with the correlation-length condition | $n^{-(d-\alpha)/(d+\alpha)}$ | $r^{(d+\alpha)/2}$ | $X^{(d+\alpha)/(2\alpha)}$ |

<p>Every entry is an order up to constants. Substitution gives $ZF(Z)\asymp X$ in each row. In the middle row, $Z^{1/2}\asymp X(\log(e+X))^{-1/4}$ and $\log(e+Z)\asymp\log(e+X)$, so the logarithms cancel. In the last row, $1-\rho=2\alpha/(d+\alpha)$, including $\rho=0$ when $\alpha=d$. Thus no asymptotic inversion theorem is needed for this matching step.</p>
<p>Part I, Theorem I.1.6 supplies the high-dimensional moment and tail formulas under its kernel assumptions. For the middle row, the moment comparison comes from Theorem I.1.15 together with hydrodynamics in Part III, Theorem III.1.11; the logarithmic ratio is the separate second-moment conclusion (III.1.18), and the full tail is Theorem III.1.2. Hydrodynamics alone does not determine either logarithmic exponent. For the last row, Part II, Theorem II.4.3 gives the two-sided cutoff moments and Theorem II.1.10 gives the full tail. Lemma II.4.6 alone is only an upper bound. These are source statements supplying the premises, not additional proofs in this article. The source's correlation-length condition restricts the first two rows to $\alpha&lt;2$; no claim about nearest-neighbour percolation in dimension six follows.</p>
<p>The volume scale here is the full moment ratio $z(r)$. The superprocess normalization in Theorem I.1.17 is $z(r)/4$; it should not be substituted into an exact-constant formula without retaining that factor. The <a href="/articles/marginal-ode/#section-inverse-log-source">inverse-log calculation</a> records a separate sign repair in the introductory source formulas. The derivative hierarchy and its limiting justification remain explicit inputs to T5JS even after the model notation has been matched.</p>
