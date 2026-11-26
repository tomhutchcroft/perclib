---
{
  "id": "directional-correlation-length",
  "title": "Directional correlation length",
  "subtitle": "The exponential rate of a two-point function",
  "kind": "theorem",
  "category": "General theory",
  "summary": "Harris makes minus the logarithm of the two-point function subadditive. Translation invariance then gives a directional decay rate, which can vanish even when susceptibility is finite.",
  "context": ["Independent bond percolation on a countable vertex set, with two-point function $\\tau(x,y)=\\mathbb P(x\\leftrightarrow y)$.", "For directional limits the vertices form a countable Abelian group and the two-point function is invariant under simultaneous translation.", "Logarithmic limits are taken only along directions whose connection probabilities are positive."],
  "related": ["harris-inequality", "lattice-path-growth", "displacement-kernels", "susceptibility", "critical-exponents", "cutoff-localization"],
  "sourceIds": ["perclib-correlation-length", "hutchcroft-book"],
  "aliases": ["inverse correlation length", "directional decay rate", "subadditivity", "Fekete", "exponential decay", "connection pseudometric"],
  "prototypeUses": ["harris-inequality", "lattice-path-growth"]
}
---

## The connection pseudometric {#section-distance}

<a id="tag-NZMZ" data-assertion="definition" data-title="The extended connection pseudometric"></a>
<p>Define the extended connection distance by</p>
<div class="math-display">$$D_q(x,y)=-\log\tau_q(x,y),\qquad -\log0=+\infty.$$</div>
<p>The subscript records the bond profile. All distances below refer to this function, not to graph distance in a configuration.</p>

<a id="tag-8TZJ" data-assertion="proposition" data-title="Harris gives the triangle inequality for connection distance"></a>
<p>The function $D_q$ is nonnegative and symmetric, vanishes on the diagonal, and satisfies</p>
<div class="math-display">$$D_q(x,z)\leq D_q(x,y)+D_q(y,z).$$</div>
<p><em>Proof.</em> The first three properties follow from $0\leq\tau_q\leq1$, symmetry and $\tau_q(x,x)=1$. If either term on the right is infinite the triangle inequality is immediate. Otherwise <a href="/tag/UPFU/">Harris and concatenation</a> give $\tau_q(x,z)\geq\tau_q(x,y)\tau_q(y,z)&gt;0$; taking negative logarithms proves the claim.</p>
<p>Distinct vertices may have distance zero. For example, if every off-diagonal bond has probability one, each pair is connected almost surely and $D_q$ vanishes identically. Conversely, zero connection probability means infinite distance. It must not be interpreted through a convention assigning a finite value to the ordinary real logarithm at zero.</p>

## The directional limit {#section-rate}

<a id="tag-K2LV" data-assertion="theorem" data-title="Existence and infimum formula for a directional decay rate"></a>
<p>Let the vertices form a countable Abelian group $G$, and suppose $\tau_q(x+g,y+g)=\tau_q(x,y)$ for all $x,y,g\in G$. Fix $v\in G$ such that $\tau_q(0,nv)&gt;0$ for every integer $n\geq1$. Then</p>
<div class="math-display">$$m_q(v)=\lim_{n\to\infty}-\frac1n\log\tau_q(0,nv)=\inf_{n\geq1}\left(-\frac1n\log\tau_q(0,nv)\right)$$</div>
<p>exists, with $0\leq m_q(v)\leq-\log\tau_q(0,v)&lt;\infty$. For every integer $n\geq0$,</p>
<div class="math-display">$$\tau_q(0,nv)\leq e^{-nm_q(v)}.$$</div>
<p>We call $m_q(v)$ the inverse correlation length in direction $v$, and set $\xi_q(v)=1/m_q(v)$ when $m_q(v)&gt;0$, with $\xi_q(v)=\infty$ when $m_q(v)=0$. This measures distance in multiples of $v$.</p>
<p><em>Proof.</em> Put $a_n=-\log\tau_q(0,nv)$, including $a_0=0$. The triangle inequality and translation invariance give</p>
<div class="math-display">$$a_{n+k}\leq a_n+a_k.$$</div>
<p>For each fixed $k\geq1$, writing $n=jk+r$ with $0\leq r&lt;k$ gives $a_n\leq j a_k+a_r$. The finitely many possible remainders are bounded, so $\limsup a_n/n\leq a_k/k$. Every term is bounded below by $\inf_{k\geq1}a_k/k\geq0$. Taking the infimum in the upper bound proves the limit formula. For $n\geq1$, the definition of the infimum gives $a_n\geq nm_q(v)$, and exponentiation gives the probability bound. At $n=0$ it is equality.</p>
<p>The exponential bound is already an algebraic consequence of the infimum: that step needs neither translation invariance nor Harris. Those hypotheses establish that the infimum is the limiting rate. Positivity at $v$ alone is sufficient under translation invariance, since Harris inductively gives $\tau_q(0,nv)\geq\tau_q(0,v)^n$. The theorem does not assert that the rate is positive; when it is zero its displayed upper bound is simply one.</p>

## A positive rate from lattice path counts {#section-lattice}

<a id="tag-I8WP" data-assertion="corollary" data-title="Directional decay below the inverse connective constant"></a>
<p>For homogeneous nearest-neighbour bond percolation on $\mathbb Z^d$, $d\geq1$, let $\mu_d$ be the <a href="/tag/F3YB/">connective constant</a>. If $0&lt;p&lt;\mu_d^{-1}$, then for every $v\in\mathbb Z^d$,</p>
<div class="math-display">$$\|v\|_1\log\frac1{p\mu_d}\leq m_p(v)\leq\|v\|_1\log\frac1p.$$</div>
<p>In particular the rate is positive for $v\ne0$. In dimension one $\mu_1=1$, so both bounds agree.</p>
<p><em>Proof.</em> Translation invariance of the bond law gives translation invariance of $\tau_p$. A lattice geodesic from $0$ to $nv$ has $n\|v\|_1$ distinct edges, so</p>
<div class="math-display">$$\tau_p(0,nv)\geq p^{n\|v\|_1}&gt;0.$$</div>
<p>The directional limit therefore exists and gives the upper bound on $m_p(v)$. For the lower bound choose $\mu_d&lt;\lambda&lt;p^{-1}$. Convergence of the path-count roots gives a finite $C_\lambda$ such that $c_\ell\leq C_\lambda\lambda^\ell$ for every $\ell\geq0$. Every path to $nv$ has length at least $n\|v\|_1$, hence the path union bound gives</p>
<div class="math-display">$$\tau_p(0,nv)\leq\sum_{\ell\geq n\|v\|_1}c_\ell p^\ell\leq\frac{C_\lambda}{1-p\lambda}(p\lambda)^{n\|v\|_1}.$$</div>
<p>Taking negative logarithms, dividing by $n$ and passing to the limit removes the fixed prefactor. Thus $m_p(v)\geq\|v\|_1\log(1/(p\lambda))$. Let $\lambda\downarrow\mu_d$.</p>
<p>This uses the strict small-parameter criterion. It does not identify $p_c$ with $\mu_d^{-1}$ or prove positive exponential rate throughout the subcritical phase.</p>

## Long-range bonds can force a zero rate {#section-long-range}

<a id="tag-23RT" data-assertion="proposition" data-title="Power-law bonds have zero directional exponential rate even at small intensity"></a>
<p>On $\mathbb Z^d$, with $d\geq1$ and $\alpha&gt;0$, give each non-loop bond $\{x,y\}$ probability</p>
<div class="math-display">$$q_\beta(x,y)=1-\exp\!\left(-\beta\|y-x\|_\infty^{-d-\alpha}\right),\qquad\beta&gt;0.$$</div>
<p>Then $m_\beta(v)=0$ for every $v\in\mathbb Z^d$. Nevertheless, if</p>
<div class="math-display">$$\beta M&lt;1,\qquad M=\sum_{z\ne0}\|z\|_\infty^{-d-\alpha}&lt;\infty,$$</div>
<p>the susceptibility is finite and satisfies $\chi_\beta(0)\leq(1-\beta M)^{-1}$.</p>
<p><em>Proof.</em> For $v\ne0$, the single bond from $0$ to $nv$ supplies the lower bound</p>
<div class="math-display">$$\tau_\beta(0,nv)\geq1-e^{-\beta n^{-d-\alpha}\|v\|_\infty^{-d-\alpha}}\geq\frac\beta2\|v\|_\infty^{-d-\alpha}n^{-d-\alpha}$$</div>
<p>for all sufficiently large $n$, using $1-e^{-t}\geq t/2$ for $0\leq t\leq1$. Thus $0\leq-n^{-1}\log\tau_\beta(0,nv)\leq((d+\alpha)\log n+O(1))/n\to0$. For $v=0$ the connection probability is one. The <a href="/tag/B2ZL/">power-kernel sum</a> is finite, and the <a href="/tag/E771/">intensity row bound</a> gives the susceptibility estimate.</p>
<p>Directional exponential correlation length and moment-based lengths such as the <a href="/articles/cutoff-localization/">radius of gyration</a> are different observables. The direct long bonds already rule out positive directional exponential rate here, including at intensities where every cluster is almost surely finite.</p>
<p>The <a href="/sources/perclib-correlation-length/">pinned library module</a> supplies the connection-distance inequalities, directional limit and infimum bound. The lattice and power-law applications above are additional informal deductions. Source inspection alone does not give any of these new tags a compiled association or establish a critical correlation-length exponent.</p>



## The rate as a function of direction {#section-correlation-seminorm}

<a id="tag-Y8RX" data-assertion="theorem" data-title="The limiting connection distance is a seminorm, uniformly in direction"></a>
<p>Consider a translation-invariant independent bond model on $\mathbb Z^d$, $d\geq1$, and suppose $\tau(0,e_i)&gt;0$ for every coordinate vector $e_i$. Write $D(x)=-\log\tau(0,x)$ and</p>
<div class="math-display">$$A=\max_{1\leq i\leq d}D(e_i).$$</div>
<p>The directional rate $m(v)$ of K2LV extends uniquely from $\mathbb Z^d$ to a continuous seminorm on $\mathbb R^d$. It satisfies $m(v)\leq A\|v\|_1$, and</p>
<div class="math-display">$$D(x)=m(x)+o(\|x\|_1)\qquad(\|x\|_1\to\infty, x\in\mathbb Z^d),$$</div>
<p>uniformly over lattice directions. More precisely, for every $\varepsilon&gt;0$, all sufficiently distant lattice points satisfy</p>
<div class="math-display">$$e^{-m(x)-\varepsilon\|x\|_1}\leq\tau(0,x)\leq e^{-m(x)}.$$</div>
<p><em>Proof.</em> The <a href="/tag/8TZJ/">connection-distance triangle inequality</a>, symmetry and translation invariance give $D(x+y)\leq D(x)+D(y)$ and $D(-x)=D(x)$. Concatenating coordinate steps proves that every $D(x)$ is finite and</p>
<div class="math-display">$$D(x)\leq A\|x\|_1,\qquad |D(x)-D(y)|\leq A\|x-y\|_1.$$</div>
<p>Apply <a href="/tag/K2LV/">the directional limit</a> along integer multiples. Passing to the limit in $D(n(v+w))\leq D(nv)+D(nw)$ gives $m(v+w)\leq m(v)+m(w)$. Subsequences of the same limit, together with symmetry, give $m(kv)=|k|m(v)$ for every integer $k$. Hence $m$ extends consistently to rational vectors, is $A$-Lipschitz in the $\ell^1$ norm there, and extends by continuity to a seminorm on $\mathbb R^d$.</p>
<p>The infimum formula gives $m(x)\leq D(x)$ at every lattice point. To prove the uniform upper error bound, fix $\delta&gt;0$ and choose finitely many nonzero integer vectors $v_1,\ldots,v_s$ whose normalized directions form a $\delta$-net of the $\ell^1$ unit sphere. This is possible by density of rational directions and compactness. Put $B=\max_i\|v_i\|_1$. Given $x\ne0$, write $r=\|x\|_1$, choose $v_i$ with $\|x/r-v_i/\|v_i\|_1\|_1\leq\delta$, and set $n=\lfloor r/\|v_i\|_1\rfloor$. Then</p>
<div class="math-display">$$\|x-nv_i\|_1\leq\delta r+B.$$</div>
<p>For any $\eta&gt;0$, the finitely many directional limits ensure that, for all sufficiently large $r$, $D(nv_i)-m(nv_i)\leq\eta n\|v_i\|_1\leq\eta r$, uniformly in the chosen index. The two Lipschitz bounds therefore give</p>
<div class="math-display">$$0\leq D(x)-m(x)\leq\eta r+2A(\delta r+B).$$</div>
<p>Divide by $r$, let $r\to\infty$, and then let $\eta,\delta\downarrow0$. This proves uniform convergence, including the case $A=0$. Exponentiating gives the probability estimates. The extension is unique because rational homogeneity determines it on the dense rational vectors.</p>
<p>The seminorm may vanish. The <a href="/tag/23RT/">power-law model</a> above has $m\equiv0$, even in a regime of finite susceptibility. Translation invariance also does not force a Euclidean norm: spatial symmetries of the bond law pass to $m$, but no additional rotational symmetry is implied.</p>

## Positivity throughout the finite-range subcritical phase {#section-subcritical-norm}

<a id="tag-OFY2" data-assertion="corollary" data-title="Finite-range finite susceptibility makes the correlation seminorm a norm"></a>
<p>In the preceding translation-invariant model, suppose $q(x,y)=0$ whenever $\|x-y\|_\infty&gt;R$, where $R&gt;0$, and suppose $\chi=\mathbb E|K_0|&lt;\infty$. Then the seminorm is a norm, with</p>
<div class="math-display">$$\frac{\|v\|_\infty}{4R\chi^2}\leq m(v)\leq A\|v\|_1
\qquad(v\in\mathbb R^d).$$</div>
<p>In particular, for homogeneous nearest-neighbour percolation with $0&lt;p&lt;p_c(\mathbb Z^d)$, the coordinate correlation length is finite and obeys</p>
<div class="math-display">$$\frac1{\log(1/p)}\leq\xi_p(e_i)\leq4\chi(p)^2.$$</div>
<p><em>Proof.</em> Translation invariance makes $\chi$ a uniform susceptibility bound. The <a href="/tag/YVJT/">finite-range radius estimate</a> gives</p>
<div class="math-display">$$\mathbb P\bigl(K_0\not\subseteq[-r,r]^d\bigr)
\leq\sqrt2\chi e^{-r/(4R\chi^2)}\qquad(r\geq0).$$</div>
<p>For $v\in\mathbb Z^d\setminus\{0\}$, the event $0\leftrightarrow nv$ implies escape from any box of radius less than $n\|v\|_\infty$. Take $r=n\|v\|_\infty-1/2$, then take negative logarithms, divide by $n$, and pass to the directional limit. The fixed prefactor disappears and gives the lower bound on $m(v)$. Rational homogeneity and continuity extend it to every real vector. The upper bound is Y8RX; the positive lower bound makes $m$ a norm.</p>
<p>For nearest-neighbour bonds, <a href="/tag/RDF0/">finite-set sharpness</a> supplies $\chi(p)&lt;\infty$ throughout the strict subcritical phase, by the parametrization $p=1-e^{-\beta}$. A fixed coordinate path gives $\tau_p(0,ne_i)\geq p^n$, hence $m_p(e_i)\leq\log(1/p)$. Set $R=1$ and take reciprocals. This applies also in dimension one, where $p_c=1$; no finite critical intensity is required.</p>
<p>The coordinate length here is the reciprocal exponential rate, not a second-moment radius. Its positivity and finiteness do not identify a critical exponent or prove the parameter-uniform radial cutoff assumptions in <a href="/tag/CAV9/">the conditional Fisher relation</a>.</p>

## A finite-box certificate for the decay rate {#section-box-correlation-length}

<a id="tag-5HID" data-assertion="theorem" data-title="A contracting box bounds the directional correlation length"></a>
<p>Consider a translation-invariant independent bond model on $\mathbb Z^d$ with range $R&gt;0$ and $\tau(0,e_i)&gt;0$ for every $i$. For an integer $\ell\geq0$, put $T_\ell=[-\ell,\ell]^d\cap\mathbb Z^d$ and</p>
<div class="math-display">$$\Phi(T_\ell)=\sum_{u\in T_\ell}\sum_{v\notin T_\ell}
\tau_{T_\ell}(0,u)q(u,v).$$</div>
<p>If $\Phi(T_\ell)\leq a&lt;1$, with $a&gt;0$, then</p>
<div class="math-display">$$\tau(0,x)\leq a^{-1}\exp\!\left(-\frac{\log(1/a)}{\ell+R}\|x\|_\infty\right),\qquad
m(v)\geq\frac{\log(1/a)}{\ell+R}\|v\|_\infty.$$</div>
<p>Whenever $\chi&lt;\infty$, such a box exists for every $a\in(0,1)$. In particular the least integer $\ell_{1/2}$ with $\Phi(T_{\ell_{1/2}})\leq1/2$ is finite and</p>
<div class="math-display">$$\xi(e_i)\leq\frac{\ell_{1/2}+R}{\log2}.$$</div>
<p><em>Proof.</em> Write $\tau(x)=\tau(0,x)$, $f=\mathbf1_{T_\ell}$, $L=\ell+R$, and</p>
<div class="math-display">$$h(v)=\mathbf1_{\{v\notin T_\ell\}}\sum_{u\in T_\ell}\tau_{T_\ell}(0,u)q(u,v).$$</div>
<p>The nonnegative kernel $h$ has total mass at most $a$ and support in $[-L,L]^d$. The <a href="/tag/USAC/">first-exit inequality with its remaining connection</a> gives $\tau\leq f+h*\tau$: outside $T_\ell$ use the first exit and translation invariance, while inside it use $\tau\leq1=f$. Iteration gives</p>
<div class="math-display">$$\tau\leq\sum_{j=0}^{n-1}h^{*j}*f+h^{*n}*\tau.$$</div>
<p>Here $h^{*0}$ is the unit mass at zero. If $\|x\|_\infty&gt;nL$, every summand in the finite sum vanishes, since its support has radius at most $jL+\ell\leq nL$. Also $\|h^{*n}*\tau\|_\infty\leq a^n$, because $\tau\leq1$. For $r=\|x\|_\infty$, choose $n=\max\{0,\lceil r/L\rceil-1\}$. When $r&gt;0$ this gives $r&gt;nL$, and $n\geq r/L-1$ yields $\tau(x)\leq a^n\leq a^{r/L-1}$. The bound at $r=0$ follows from $\tau(0)=1$. Passing to directional limits proves the rate bound, and Y8RX extends it to real vectors.</p>
<p>Finally let $Q=\sum_{v\ne0}q(0,v)&lt;\infty$. An exit edge of range at most $R$ can start in $T_\ell$ only at a vertex with $\|u\|_\infty&gt;\ell-R$. Internal connections are bounded by unrestricted ones, so</p>
<div class="math-display">$$\Phi(T_\ell)\leq Q\sum_{\|u\|_\infty&gt;\ell-R}\tau(0,u)\longrightarrow0$$</div>
<p>when $\chi&lt;\infty$. This proves existence of the least half-contraction radius and the asserted length bound.</p>
<p>This supplies a finite-box correlation length with a precise one-sided comparison. The range correction $R$ matters, including when the least box is the singleton. The argument neither gives a reverse comparison nor identifies this length with a radius of gyration. For long-range bonds the exit kernel need not have bounded support, so this spatial iteration cannot be used unchanged.</p>
