---
{
  "id": "exponential-moments",
  "title": "From tree-graph moments to exponential tails",
  "subtitle": "Summing the moment series without losing the endpoint",
  "kind": "method",
  "category": "Methods",
  "summary": "Double-factorial moment bounds control both weighted and ordinary exponential moments. Explicit Markov bounds retain their prefactors and yield a pure exponential estimate only in a stated large-threshold range.",
  "context": ["A nonnegative random variable $X$ with finite positive mean $\\chi$.", "The full moment hypothesis is $\\mathbb E X^m\\leq(2m-3)!!\\,\\chi^{2m-1}$ for every integer $m\\geq1$, with $(-1)!!=1$.", "For percolation, deriving these moment inequalities is a separate tree-graph argument."],
  "related": ["susceptibility", "sharpness", "disjoint-occurrence", "universal-tightness"],
  "sourceIds": ["hutchcroft-book", "perclib-exponential-moment-series", "perclib-finite-range-decay", "perclib-tail-sums", "perclib-real-moment-ratios", "perclib-train10-percolation-bond-tightness-momentratio"],
  "aliases": ["exponential moment", "moment generating function", "tree-graph moments", "double factorial", "subcritical volume tail"],
  "prototypeUses": []
}
---

## Summing the moment bounds {#section-series}

<a id="tag-0BQB" data-assertion="theorem" data-title="Exponential moments from double-factorial moment bounds"></a><p>Suppose $X\geq0$, $\chi=\mathbb E X\in(0,\infty)$, and</p><div class="math-display">$$\mathbb E X^m\leq(2m-3)!!\,\chi^{2m-1}\qquad(m=1,2,\ldots),$$</div><p>where $(-1)!!=1$. For $0\leq r&lt;(2\chi^2)^{-1}$,</p><div class="math-display">$$\mathbb E[Xe^{rX}]\leq\frac\chi{\sqrt{1-2r\chi^2}}.$$</div><p>The ordinary exponential moment also satisfies</p><div class="math-display">$$\mathbb E e^{rX}\leq1+\frac{1-\sqrt{1-2r\chi^2}}\chi\qquad\left(0\leq r\leq\frac1{2\chi^2}\right).$$</div><p>In particular, the second bound includes its upper endpoint, where it gives $\mathbb E e^{X/(2\chi^2)}\leq1+\chi^{-1}$.</p><p><em>Proof.</em> All terms in the exponential series are nonnegative, so Tonelli and the moment hypothesis give</p><div class="math-display">$$\mathbb E[Xe^{rX}]=\sum_{j\geq0}\frac{r^j}{j!}\mathbb E X^{j+1}\leq\chi\sum_{j\geq0}\frac{(2j-1)!!}{j!}(r\chi^2)^j=\frac\chi{\sqrt{1-2r\chi^2}}.$$</div><p>The last equality is the binomial series, using $(2j-1)!!/j!=2^{-j}\binom{2j}{j}$. Integrate the bound from zero to $r$. Since $e^{rX}-1=\int_0^rXe^{sX}\,ds$, Tonelli gives</p><div class="math-display">$$\mathbb E e^{rX}-1\leq\int_0^r\frac\chi{\sqrt{1-2s\chi^2}}\,ds=\frac{1-\sqrt{1-2r\chi^2}}\chi.$$</div><p>This proves the ordinary-moment bound below the endpoint. Letting $r\uparrow(2\chi^2)^{-1}$ and using monotone convergence proves the endpoint assertion. The square-root singularity of the weighted bound is integrable; it does not obstruct this finite ordinary exponential moment.</p><p>Finite mean alone would not justify any of these conclusions. The assumption controls all positive integer moments with a particular growth rate. It also implies that each of those moments is finite, so the power-series calculation does not assume the desired exponential integrability in advance.</p>

## Tail estimates with their constants {#section-tails}

<a id="tag-SNB3" data-assertion="corollary" data-title="Explicit exponential tails and the large-threshold prefactor removal"></a><p>Under the preceding hypotheses, for every real $n&gt;0$,</p><div class="math-display">$$\mathbb P(X\geq n)\leq\min\left\{1,\ \frac{\sqrt2\chi}{n}e^{-n/(4\chi^2)},\ (1+\chi^{-1})e^{-n/(2\chi^2)}\right\}.$$</div><p>In particular, for</p><div class="math-display">$$n\geq4\chi^2\log(1+\chi^{-1}),$$</div><p>one has $\mathbb P(X\geq n)\leq e^{-n/(4\chi^2)}$.</p><p><em>Proof.</em> On $\{X\geq n\}$, $Xe^{rX}\geq ne^{rn}$. Taking $r=(4\chi^2)^{-1}$ in the weighted bound gives the second entry in the minimum. Markov's inequality applied to the ordinary exponential moment at $r=(2\chi^2)^{-1}$ gives the third. The stated lower bound on $n$ makes $1+\chi^{-1}\leq e^{n/(4\chi^2)}$, allowing the prefactor in that third entry to be absorbed. Probabilities are also at most one.</p><p>For a bond cluster, $X=|K_o|\geq1$ almost surely. Thus an estimate $\mathbb P(X\geq n)\leq e^{-cn}$ with $c&gt;0$ cannot hold at $n=1$. The explicit prefactors above, or the stated eventual range, avoid this endpoint error. No change to the fact that the cluster contains its root is made to obtain the tail estimate.</p>

## A fourth-to-second moment comparison {#section-log-ratio}

<a id="tag-IXEZ" data-assertion="proposition" data-title="A logarithmic fourth-moment comparison from the weighted exponential bound"></a>
<p>Let $X\geq0$, $\chi=\mathbb E X\geq1$, and assume $\mathbb E[Xe^{X/(4\chi^2)}]\leq\sqrt2\chi$. Then</p>
<div class="math-display">$$\mathbb E X^4\leq1152\chi^4\log^2(2\chi)\,\mathbb E X^2.$$</div>
<p>In particular, this holds for a transitive independent bond model with finite susceptibility, by <a href="/tag/0BQB/">0BQB</a>.</p>
<p><em>Proof.</em> Set $T=24\chi^2\log(2\chi)$ and $s=(4\chi^2)^{-1}$. On $X\leq T$, use $X^4\leq T^2X^2$. Since $T\geq12\chi^2$, the function $x^3e^{-sx}$ is decreasing on $[T,\infty)$. Hence</p>
<div class="math-display">$$\mathbb E[X^4\mathbf1_{\{X&gt;T\}}]\leq T^3e^{-sT}\mathbb E[Xe^{sX}]\leq\sqrt2\chi T^3(2\chi)^{-6}.$$</div>
<p>Jensen gives $\mathbb E X^2\geq\chi^2$. The last upper bound divided by $T^2\mathbb E X^2$ is therefore at most</p>
<div class="math-display">$$\frac{\sqrt2 T}{\chi}(2\chi)^{-6}=\frac{3\sqrt2}{8}\frac{\log(2\chi)}{\chi^5}\leq\frac{3\sqrt2}{8}&lt;1,$$</div>
<p>where $\log(2\chi)\leq\chi$ for $\chi\geq1$. Adding the two parts gives $\mathbb E X^4\leq2T^2\mathbb E X^2$, as claimed. The exponential hypothesis ensures that all moments used here are finite.</p>
<p>The logarithmic loss is deliberate. This does not prove a stronger comparison without that loss. It is nevertheless enough to make the second-moment differential error integrable whenever its power of radius is strictly decaying.</p>

## Uniform susceptibility in an inhomogeneous model {#section-uniform}

<a id="tag-XLWI" data-assertion="theorem" data-title="Uniform susceptibility gives exponential bounds with the root mean retained"></a>
<p>Consider independent bond percolation on a nonempty countable vertex set. Write $\chi_x=\mathbb E|K_x|$, and suppose $M=\sup_x\chi_x&lt;\infty$. For every root $o$ and $0\leq s&lt;(2M^2)^{-1}$,</p>
<div class="math-display">$$\mathbb E\bigl[|K_o|e^{s|K_o|}\bigr]\leq\frac{\chi_o}{\sqrt{1-2sM^2}}.$$</div>
<p>For $0\leq s\leq(2M^2)^{-1}$, including the upper endpoint,</p>
<div class="math-display">$$\mathbb E e^{s|K_o|}\leq1+\frac{\chi_o}{M^2}\bigl(1-\sqrt{1-2sM^2}\bigr).$$</div>
<p>Consequently, for every real $n&gt;0$,</p>
<div class="math-display">$$\mathbb P(|K_o|\geq n)\leq\min\left\{1,\ \frac{\sqrt2\chi_o}{n}e^{-n/(4M^2)},\ \left(1+\frac{\chi_o}{M^2}\right)e^{-n/(2M^2)}\right\}.$$</div>
<p>In particular, $\mathbb P(|K_o|\geq n)\leq e^{-n/(4M^2)}$ whenever $n\geq4M^2\log(1+\chi_o/M^2)$.</p>
<p><em>Proof.</em> The <a href="/tag/Y84V/">uniform-susceptibility tree-graph bound</a> gives $\mathbb E|K_o|^{j+1}\leq(2j-1)!!\,\chi_oM^{2j}$ for $j\geq0$. Sum the nonnegative exponential series:</p>
<div class="math-display">$$\mathbb E\bigl[|K_o|e^{s|K_o|}\bigr]\leq\chi_o\sum_{j\geq0}\frac{(2j-1)!!}{j!}(sM^2)^j=\frac{\chi_o}{\sqrt{1-2sM^2}}.$$</div>
<p>Integration from zero to $s$ gives the ordinary exponential bound below the endpoint. Monotone convergence extends it to $s=(2M^2)^{-1}$. Apply Markov's inequality to the weighted exponential at $s=(4M^2)^{-1}$ and to the ordinary exponential at its endpoint. The final threshold absorbs the prefactor in the latter bound.</p>
<p>No transitivity is required. The scale uses the susceptibility supremum $M$, while the prefactors retain the mean at the chosen root. When all susceptibilities equal $\chi$, these formulas recover the preceding bounds. The <a href="/tag/HRS7/">root-mean counterexample</a> explains why a finite value of $\chi_o$ alone cannot replace the uniform hypothesis.</p>

## From cluster volume to spatial radius {#section-finite-range}

<a id="tag-YVJT" data-assertion="corollary" data-title="Uniformly finite susceptibility gives spatial exponential decay for finite-range bonds"></a>
<p>Consider independent bonds on $\mathbb Z^d$. Suppose bonds with $\|x-y\|_\infty&gt;R$ have probability zero, where $R&gt;0$, and let $M=\sup_x\mathbb E|K_x|&lt;\infty$, $\chi_o=\mathbb E|K_o|$. Then, for $r\geq0$,</p>
<div class="math-display">$$\mathbb P\bigl(o\leftrightarrow\mathbb Z^d\setminus(o+[-r,r]^d)\bigr)\leq\sqrt2\chi_o\exp\!\left(-\frac{r}{4RM^2}\right).$$</div>
<p><em>Proof.</em> A simple open path from $o$ to a vertex outside the box has more than $r/R$ edges, since each edge changes the sup norm by at most $R$. Its vertices are distinct and belong to $K_o$. In particular, the exit event implies $|K_o|\geq n$ for $n=\lfloor r/R\rfloor+1$. The <a href="/tag/XLWI/">uniform-susceptibility volume bound</a> gives</p>
<div class="math-display">$$\mathbb P(|K_o|\geq n)\leq\frac{\sqrt2\chi_o}{n}e^{-n/(4M^2)}\leq\sqrt2\chi_o e^{-r/(4RM^2)},$$</div>
<p>as required.</p>
<p>For homogeneous nearest-neighbour percolation, take $R=1$ and $M=\chi_o$. The <a href="/articles/integrated-susceptibility/#section-finite-set">finite-set sharpness proof</a> makes this mean finite throughout the subcritical phase, proving the spatial conclusion of <a href="/tag/6THJ/">lattice sharpness</a> with explicit, non-optimal constants.</p>
<p>The range assumption cannot be dropped. For a power-law intensity kernel and $\beta&gt;0$, a single edge gives $\tau_\beta(0,x)\geq1-e^{-\beta J(x)}$. If $J(x)\asymp\|x\|^{-d-\alpha}$, this lower bound is polynomial at large distance and rules out a uniform exponential spatial bound, even at parameters with exponential cluster-volume tails.</p>

## Where the probabilistic input enters {#section-input}

<p>The weighted moment series can be used to deduce subcritical exponential decay. The analytic implication here begins only after the double-factorial moment inequalities have been established. In a percolation application, their proof must supply the required independence, geometry and summation arguments. Likewise, identifying the region of finite susceptibility with the full subcritical phase is a separate sharpness input.</p><p>An unqualified exponential bound with unit prefactor at every $n\geq1$ cannot hold, since $|K_o|\geq1$ surely. The estimates here provide precise forms that follow from the displayed moment hypothesis. They do not replace the separate <a href="/articles/sharpness/">model-specific sharpness theorem</a>, and the scale $\chi^2$ in these bounds need not be an optimal decay scale for every model.</p>

## The endpoint in the source series argument {#section-series-source}

<p>The source proves <a href="/tag/0BQB/">0BQB</a> by bounding the nonnegative exponential series directly. Its parameter $\chi&gt;0$ is a moment scale; it need not equal $\mathbb E X$. The moment hypothesis includes $\mathbb E X\leq\chi$, and equality gives the formulation above. For a measurable, pointwise nonnegative real variable, Tonelli gives, without assuming exponential integrability,</p>
<div class="math-display">$$\int X^j e^{rX}\,dP=\sum_{k\geq0}\frac{r^k}{k!}\int X^{j+k}\,dP\qquad(r\geq0).$$</div>
<p>This identity and the weighted exponential bound allow an arbitrary measure $P$. The ordinary exponential bound assumes a probability measure: its constant term is $\int1\,dP=1$. Thus normalization first enters at the constant term, not at the interchange of a nonnegative series and an integral.</p>
<p>Put $z=2r\chi^2$. The weighted estimate uses the binomial series for $(1-z)^{-1/2}$ at $z&lt;1$. For the ordinary exponential, bound each finite partial sum using</p>
<div class="math-display">$$\sum_{k=0}^{N-1}\frac{(2k-1)!!}{(k+1)!\,2^{k+1}}z^{k+1}\leq1-\sqrt{1-z}\qquad(0\leq z\leq1).$$</div>
<p>Below one this follows from the convergent binomial series and positivity of its terms. At one, fix $N$ first and let $z$ increase to one; the left side is a polynomial. Taking the supremum over $N$ then bounds the full exponential integral at $r=(2\chi^2)^{-1}$. This proves the endpoint without evaluating the singular weighted estimate there.</p>
<p>The weighted Markov bound needs a positive tail threshold because its denominator is $n e^{rn}$. The ordinary bound uses $e^{rn}&gt;0$ and is exported for every real $n$, although the useful range is positive. Their minimum in <a href="/tag/SNB3/">SNB3</a> assumes $n&gt;0$. Removing the ordinary bound's prefactor needs the stated lower threshold $4\chi^2\log(1+\chi^{-1})$; it is not valid at every positive integer for a cluster containing its root.</p>
<p>The <a href="/coverage/sources/perclib-22d8485-moment-tails/">seventeen-contract inventory</a> records the coefficient identities, moment expansion, endpoint and tail estimates, and a point-mass witness with $X=\chi\geq1$. This file supplies an analytic implication from the full moment hypothesis. Applying it to extended cluster volume first uses finite susceptibility to exclude infinite volume almost surely, and then chooses a real-valued representative; the tree-graph moment input and any uniform-susceptibility refinement remain separate.</p>


## The inputs to the finite-range argument {#section-range-source}

<p>The <a href="/coverage/sources/perclib-3978a2f-models/">source for IXEZ</a> assumes that $X$ and $Xe^{X/(4\chi^2)}$ are integrable, with $\chi=\mathbb E X\geq1$. It first derives square integrability from the exponential bound and then fourth-moment integrability from the pointwise split at $T=24\chi^2\log(2\chi)$. Thus Jensen's inequality and the subtraction of finite integrals in the proof do not presuppose the moments being estimated. No percolation structure enters this analytic comparison.</p>
<p>For <a href="/tag/YVJT/">YVJT</a>, the source proves the geometric implication and then assumes the volume-tail bound at every integer $n\geq1$. The parameters in that implication are a nonnegative prefactor and a moment scale; identifying them with $\chi_o$ and $M$ uses the separate uniform-susceptibility estimate above. The geometric step also has an almost-sure qualification: zero-probability long edges are absent simultaneously because the lattice has countably many edges. A shortest open path in the remaining configuration is simple, so its length controls the number of cluster vertices.</p>


## Real exponents in the moment comparison {#section-real-ratio-source}

<p>The <a href="/coverage/sources/perclib-f51f639-moments/">moment-ratio source</a> proves the analytic consequence of a rooted exponential tail. Let $f\geq0$ be measurable and real-valued, let $M\geq1$, and suppose</p>
<div class="math-display">$$\mu(f\geq t)\leq e\,e^{-t/(9M)}\mu(f\geq M),\qquad t\geq M.$$</div>
<p>For real $p&gt;0$ and $q\geq0$, split the layer-cake integral for $f^{p+q}$ at $M$. Below $M$, use $t^q\leq M^q$. Above $M$, use the tail bound and $M^p\mu(f\geq M)\leq\int f^p\,d\mu$, then extend the remaining Gamma integral down to zero. This gives</p>
<div class="math-display">$$\int f^{p+q}\,d\mu\leq\left[\frac{p+q}{p}+e(p+q)9^{p+q}\Gamma(p+q)\right]M^q\int f^p\,d\mu.$$</div>
<p>The integrals are nonnegative extended integrals; the measure need not be a probability measure. The case $p=0$ requires a separate estimate. For a probability measure, bounding the tail by one below $M$ gives $\int f^r\,d\mu\leq[1+er9^r\Gamma(r)]M^r$ for every $r&gt;0$. The source establishes these implications from the stated tail, while the percolation argument supplying that tail remains an input.</p>


## Applying the real moment ratio to actual windows {#section-window-ratio-source}

<p>The <a href="/coverage/sources/perclib-dfbc5b4-moments-ghost/">window-moment source</a> supplies the probabilistic input left explicit in the preceding analytic comparison. For a nonempty finite observation window in a countable bond model, put $X=|K_u\cap\Lambda|$ and let $M$ be the largest-intersection quantile. The proved rooted universal tail gives the damping hypothesis. Thus, for every real $p&gt;0$ and $q\geq0$,</p>
<div class="math-display">$$\mathbb E X^{p+q}\leq
\left[\frac{p+q}{p}+e(p+q)9^{p+q}\Gamma(p+q)\right]M^q\mathbb E X^p.$$</div>
<p>The window variable is bounded by $|\Lambda|$, so it is finite and measurable regardless of whether its full cluster is infinite. This justifies the source's passage from an extended-integer variable to a real representative. It is not necessary to assume finite susceptibility.</p>
<p>At $p=0$, probability normalization instead gives, for $q&gt;0$, $\mathbb E X^q\leq[1+eq9^q\Gamma(q)]M^q$; the case $p=q=0$ is immediate with the convention $X^0=1$. This avoids applying the positive-$p$ formula at its singular endpoint. For the maximum $Z$ in the window, quantile minimality separately yields $\mathbb E Z^p\geq e^{-1}(M-1)^p$ for $p&gt;0$. The exact threshold is $M-1$, not $M$.</p>



## Analyticity in the bond intensity {#section-intensity-analyticity}

<a id="tag-IW3P" data-assertion="theorem" data-title="A finite-cluster expansion gives jointly analytic intensity and size generating functions"></a>
<p>Let $V$ be a nonempty countable vertex set, let $o\in V$, and let $J(x,y)=J(y,x)\geq0$ be off-diagonal weights with</p>
<div class="math-display">$$\Lambda=\sup_x\sum_{y\ne x}J(x,y)&lt;\infty.$$</div>
<p>At intensity $\beta\geq0$, take independent bonds with probabilities $1-e^{-\beta J(x,y)}$. Suppose $0\leq\beta_0&lt;\beta_*$ and, for some $\lambda&gt;0$,</p>
<div class="math-display">$$\mathbb E_{\beta_*}e^{\lambda|K_o|}&lt;\infty.$$</div>
<p>Choose $h&gt;0$ and $R&gt;1$ such that $h&lt;\beta_*-\beta_0$ and $2h\Lambda+\log R&lt;\lambda$. The generating function $\mathbb E_\beta u^{|K_o|}$ has a jointly holomorphic extension $F(z,u)$ to a neighbourhood of the closed polydisc $|z-\beta_0|\leq h$, $|u|\leq R$, and there</p>
<div class="math-display">$$|F(z,u)|\leq\mathbb E_{\beta_*}e^{\lambda|K_o|}.$$</div>
<p>Every positive integer cluster-size moment is therefore real analytic in $\beta$ near $\beta_0$. When $\beta_0=0$, this means the restriction to nonnegative intensities of a holomorphic function defined across zero.</p>
<p><em>Proof.</em> For a finite set $S\ni o$, let $E(S)$ be its unordered internal pairs, and put</p>
<div class="math-display">$$I(S)=\sum_{e\in E(S)}J_e,\qquad
B(S)=\sum_{x\in S,\ y\notin S}J(x,y).$$</div>
<p>These sums are finite, and $2I(S)+B(S)\leq\Lambda|S|$. The entire function</p>
<div class="math-display">$$a_S(z)=e^{-zB(S)}
\sum_{\substack{A\subseteq E(S)\\(S,A)\ \mathrm{connected}}}
\prod_{e\in A}(1-e^{-zJ_e})\prod_{e\in E(S)\setminus A}e^{-zJ_e}$$</div>
<p>equals $\mathbb P_\beta(K_o=S)$ at real $z=\beta\geq0$. Indeed, the internal open graph must connect $S$, and every boundary edge must be closed. The latter probability is $e^{-\beta B(S)}$, by a limit of finite independent products. For a singleton, the empty internal graph is connected. Edges of weight zero cause no difficulty.</p>
<p>Set $b=\beta_0+h$. If $|z-\beta_0|\leq h$, then $|z|\leq b$ and $0\leq b-\operatorname{Re}z\leq2h$. For $J\geq0$, the identity $1-e^{-zJ}=zJ\int_0^1e^{-tzJ}\,dt$ gives</p>
<div class="math-display">$$|1-e^{-zJ}|\leq\frac{|z|}{b}e^{(b-\operatorname{Re}z)J}(1-e^{-bJ})
\leq e^{2hJ}(1-e^{-bJ}),\qquad
|e^{-zJ}|\leq e^{2hJ}e^{-bJ}.$$</div>
<p>Apply these inequalities to every internal factor and to the boundary exponential, then sum over connected internal graphs. This yields</p>
<div class="math-display">$$|a_S(z)|\leq e^{2h(I(S)+B(S))}\mathbb P_b(K_o=S)
\leq e^{2h\Lambda|S|}\mathbb P_b(K_o=S).$$</div>
<p>There are countably many finite sets containing $o$. Thus the series</p>
<div class="math-display">$$F(z,u)=\sum_{\substack{S\ni o\\|S|&lt;\infty}}u^{|S|}a_S(z)$$</div>
<p>has a summable uniform majorant on the stated polydisc, since monotone coupling gives</p>
<div class="math-display">$$\sum_{S\ni o} R^{|S|}e^{2h\Lambda|S|}\mathbb P_b(K_o=S)
=\mathbb E_b e^{(2h\Lambda+\log R)|K_o|}
\leq\mathbb E_{\beta_*}e^{\lambda|K_o|}.$$</div>
<p>The strict inequalities in the choice of $h,R$ allow both radii to be enlarged slightly while retaining this bound. Normal convergence of the series of entire functions proves the holomorphic extension. For real nonnegative $\beta$ in the disc, $K_o$ is finite almost surely by domination at $\beta_*$, so the series is its generating function. Differentiation in $u$ now gives the holomorphic moment functions</p>
<div class="math-display">$$M_k(z)=\left.(u\partial_u)^kF(z,u)\right|_{u=1}
=\sum_{S\ni o}|S|^k a_S(z),\qquad k=0,1,2,\ldots.$$</div>
<p>Here $M_0=1$ on the real probability model. No probability law at complex intensity is used: only finite-cluster weights are extended. The estimate charges the total incident weight, not the number of incident edges, and therefore allows infinite-range summable kernels.</p>

## A radius from uniformly finite susceptibility {#section-analytic-radius}

<a id="tag-VYTG" data-assertion="corollary" data-title="Uniform susceptibility gives an explicit analytic radius and bounds on all moment derivatives"></a>
<p>In the same intensity model, suppose $0&lt;\Lambda&lt;\infty$ and</p>
<div class="math-display">$$M=\sup_x\mathbb E_{\beta_0}|K_x|&lt;\infty.$$</div>
<p>For every root, the generating function has a holomorphic extension to a neighbourhood of</p>
<div class="math-display">$$|z-\beta_0|\leq\frac1{32\Lambda M^2},\qquad
|u|\leq\exp\!\left(\frac1{16M^2}\right),$$</div>
<p>with $|F(z,u)|\leq2$ there. For all integers $j,k\geq0$, its moment functions satisfy</p>
<div class="math-display">$$|M_k^{(j)}(\beta_0)|\leq
2j!k!(32\Lambda M^2)^j(8M^2)^k.$$</div>
<p><em>Proof.</em> Since clusters contain their roots, $M\geq1$. Add an independent intensity layer of size $\delta=(4\Lambda M)^{-1}$. Its edge-probability row is at most $\delta\Lambda$. The <a href="/tag/MLLO/">independent-layer bound</a> gives</p>
<div class="math-display">$$\beta_*=\beta_0+\delta,\qquad
M_*:=\sup_x\mathbb E_{\beta_*}|K_x|\leq\frac{M}{1-\delta\Lambda M}=\frac43M.$$</div>
<p>By <a href="/tag/XLWI/">the uniform exponential-moment estimate</a>, with $\lambda=9/(32M^2)\leq(2M_*^2)^{-1}$,</p>
<div class="math-display">$$\mathbb E_{\beta_*}e^{\lambda|K_o|}
\leq1+\frac{\mathbb E_{\beta_*}|K_o|}{M_*^2}\leq2.$$</div>
<p>Take $h=(32\Lambda M^2)^{-1}$ and $\log R=(16M^2)^{-1}$. Then $h&lt;\delta$ and $2h\Lambda+\log R=1/(8M^2)&lt;\lambda$, so IW3P gives the stated extension and bound.</p>
<p>For the derivative estimate, use $n^k\leq k!(8M^2)^k e^{n/(8M^2)}$, the $k$th term of the exponential series. The finite-cluster majorant from IW3P gives, for $|z-\beta_0|\leq h$,</p>
<div class="math-display">$$|M_k(z)|\leq\mathbb E_{\beta_*}\bigl[|K_o|^k e^{2h\Lambda|K_o|}\bigr]
\leq2k!(8M^2)^k,$$</div>
<p>because $2h\Lambda+1/(8M^2)=3/(16M^2)&lt;\lambda$. Cauchy's estimate on the circle of radius $h$ proves the result.</p>
<p>If $\Lambda=0$, every cluster is a singleton and $F(z,u)=u$ is entire. Transitivity is unnecessary in this corollary. In a transitive model, $M$ is the ordinary susceptibility, so finite subcritical susceptibility supplies real analyticity of every integer cluster-size moment throughout that phase. This proves the analyticity claim for the stated summable intensity model; it asserts no extension through criticality.</p>




## Critical total mass and cycle increments {#section-critical-root-exponential}

<p>For a finite independent bond model, <a href="/tag/81TZ/">81TZ</a> bounds the exponential of $\sqrt{\sum_C|C|^2}$ on the scale $\sqrt{\max\{NM,M^4\}}$, where $M$ is the largest root susceptibility. It keeps track of the set-partition coefficients in the total-mass moment bound. At a critical complete-graph window this gives <a href="/tag/NROY/">exponential integrability of the maximum $\ell^2$ norm</a> of the normalized size path. The <a href="/tag/L1PJ/">corresponding square-root transform</a> also converges jointly for integrated squared mass and new cycle births; their <a href="/tag/NM14/">mixed moments determine the joint law</a>. These statements retain the square roots and explicit small-parameter ranges.</p>




## Using a stronger largest-component tail {#section-critical-full-exponential}

<p>The complete-graph cubic tail now gives <a href="/tag/7CDV/">ordinary exponential moments of critical total squared mass</a> at every positive parameter. The step from one component to the sum uses <a href="/tag/1NYQ/">a product over distinct clusters</a>, justified by successive cluster exposure and superadditive weights. It yields <a href="/tag/ME2X/">joint exponential-transform convergence</a> for integrated squared mass and new cycle counts, and <a href="/tag/0Y6N/">locally uniform convergence of their entire transforms and all derivatives</a>. The general square-root bounds above require only the susceptibility estimate; this stronger conclusion also uses the complete-graph cubic tail.</p>
