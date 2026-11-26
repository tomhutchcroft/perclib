---
{
  "id": "pointwise-long-range",
  "title": "Pointwise bounds from spatial averages",
  "subtitle": "Translated boxes and a contraction over scales",
  "kind": "method",
  "category": "Critical phenomena",
  "summary": "Averaging the first exit from translated boxes penalizes short crossing edges. Together with a spatially averaged connection bound, this gives a contraction over scales and a critical pointwise upper bound when alpha is less than one.",
  "context": [
    "Independent bond percolation on the integer lattice with symmetric translation-invariant intensities.",
    "The probability decomposition is separate from the analytic bootstrap.",
    "The critical application assumes globally comparable power-law kernels and 0 < alpha < min(1,d)."
  ],
  "related": [
    "isoperimetric-lower-bounds",
    "hierarchical-comparison",
    "cutoff-localization",
    "finite-set-hyperscaling",
    "bk-inequality"
  ],
  "sourceIds": [
    "hutchcroft-pointwise-2024"
  ],
  "aliases": [
    "pointwise critical upper bound",
    "random translated boxes",
    "induction on scales",
    "short-edge contraction"
  ],
  "prototypeUses": []
}
---

## First exits from translated boxes {#section-translated}

<p>Write $\|x\|=\|x\|_\infty$, $\langle x\rangle=\max\{2,\|x\|\}$, and $B_R=[-R,R]^d\cap\mathbb Z^d$. Consider independent bonds with probabilities $q_\beta(x,y)=1-e^{-\beta J(y-x)}$, where $J(z)=J(-z)\geq0$ is summable over nonzero displacements. Put $\tau_\beta(x)=\mathbb P_\beta(0\leftrightarrow x)$.</p>

<a id="tag-0VB3" data-assertion="proposition" data-title="Averaged translated boxes give a first-exit bound with a crossing penalty"></a>
<p>For $R=2^k$, $k\geq3$, and $\|x\|&gt;R/2$,</p>
<div class="math-display">$$\tau_\beta(x)\leq4d\sum_{u\in B_{R/2}}\ \sum_{\substack{v\notin B_{R/8}\\v\ne u}}q_\beta(u,v)\tau_\beta(u)\tau_\beta(x-v)\min\left\{1,\frac{\|u-v\|}{R}\right\}.$$</div>
<p>Consequently, if $J(z)\leq C\|z\|^{-d-\alpha}$ for $z\ne0$ and $\alpha&gt;0$, the right side is at most</p>
<div class="math-display">$$4d\,2^{d+\alpha}C\beta\sum_{u\in B_{R/2}}\ \sum_{\substack{v\notin B_{R/8}\\v\ne u}}\langle u-v\rangle^{-d-\alpha}\tau_\beta(u)\tau_\beta(x-v)\min\left\{1,\frac{\langle u-v\rangle}{R}\right\}.$$</div>
<p><em>Proof.</em> Choose a centre $z$ uniformly from $B_{R/8}$ and use the box $Q_z=z+B_{R/4}$. Every such box contains $B_{R/8}$ and lies in $B_{3R/8}\subset B_{R/2}$. It therefore contains $0$ and excludes $x$. The first edge $(u,v)$ by which a simple open path from $0$ to $x$ leaves $Q_z$ splits that path into three disjoint edge witnesses. The <a href="/tag/AUUG/">BK inequality</a> and a union bound give</p>
<div class="math-display">$$\tau_\beta(x)\leq\sum_{u\in Q_z}\sum_{v\notin Q_z}q_\beta(u,v)\tau_\beta(u)\tau_\beta(x-v).$$</div>
<p>For a fixed coordinate $i$, the centres whose box contains $u_i$ but excludes $v_i$ form the difference of the integer intervals $[u_i-R/4,u_i+R/4]$ and $[v_i-R/4,v_i+R/4]$. Its size is at most $|u_i-v_i|$. Restricting the centre to $[-R/8,R/8]$ and dividing by its $R/4+1$ possible values gives a probability at most $\min\{1,4|u_i-v_i|/R\}$. If $u\in Q_z$ and $v\notin Q_z$, this happens in at least one coordinate. The union bound therefore gives</p>
<div class="math-display">$$\mathbb P_z(u\in Q_z,\ v\notin Q_z)\leq4d\min\{1,\|u-v\|/R\}.$$</div>
<p>Average the first-exit inequality and interchange the nonnegative sums. The geometric containments give the stated restrictions on $u,v$. The sum is finite since $u$ ranges over a finite set and the probability rows are summable. Finally $q_\beta(u,v)\leq\beta C\|u-v\|^{-d-\alpha}\leq2^{d+\alpha}C\beta\langle u-v\rangle^{-d-\alpha}$. No assumption $\alpha&lt;1$ is used in this decomposition.</p>

## A contraction from the averaged bound {#section-bootstrap}

<a id="tag-PIZX" data-assertion="theorem" data-title="A spatial average and translated-box inequality imply pointwise decay"></a>
<p>Let $d\geq1$, $0&lt;\alpha&lt;\min\{1,d\}$, and let $f:\mathbb Z^d\to[0,1]$. Suppose that, for finite constants $A,D&gt;0$,</p>
<div class="math-display">$$\sum_{y\in B_t}f(y)\leq At^\alpha\qquad(t\geq1),$$</div>
<p>and, for every dyadic $R\geq8$ and $\|x\|&gt;R/2$,</p>
<div class="math-display">$$f(x)\leq D\sum_{u\in B_{R/2}}\ \sum_{\substack{v\notin B_{R/8}\\v\ne u}}\langle u-v\rangle^{-d-\alpha}f(u)f(x-v)\min\left\{1,\frac{\langle u-v\rangle}{R}\right\}.$$</div>
<p>Then $f(x)\leq C_*\langle x\rangle^{-d+\alpha}$ for every $x$, with $C_*$ depending only on $d,\alpha,A,D$.</p>
<p><em>Proof.</em> Put $p=d-\alpha&gt;0$ and $a_k=\max_{x\in B_{2^k}}\langle x\rangle^p f(x)$. Fix $k\geq3$, $R=2^k$, and $R/2&lt;\|x\|\leq R$. Choose $0&lt;\varepsilon\leq1/16$. Split the double sum into $v\in B_R$, $\|u-v\|\geq\varepsilon R$; $v\in B_R$, $1\leq\|u-v\|&lt;\varepsilon R$; and $v\notin B_R$. Constants in the following bounds are independent of $k,\varepsilon$ and the values of $f$.</p>
<p>For the separated endpoints, use the upper bound $\langle u-v\rangle/R$ for the crossing penalty. Since $1-d-\alpha&lt;0$, the weight is at most $\varepsilon^{1-d-\alpha}R^{-d-\alpha}$. Also $x-B_R\subset B_{2R}$. The two averaged bounds give a contribution at most</p>
<div class="math-display">$$C A^2\varepsilon^{1-d-\alpha}R^{-d+\alpha}.$$</div>
<p>For the nearby endpoints, $\|v\|&gt;R/8$ and $\|u-v\|&lt;R/16$ imply $\|u\|&gt;R/16$. Since $u\in B_{R/2}$,</p>
<div class="math-display">$$f(u)\leq C a_{k-1}R^{-p}.$$</div>
<p>The remaining short-displacement sum satisfies</p>
<div class="math-display">$$\sum_{1\leq\|z\|&lt;\varepsilon R}\langle z\rangle^{1-d-\alpha}\leq C\sum_{1\leq l&lt;\varepsilon R}l^{-\alpha}\leq C_\alpha(\varepsilon R)^{1-\alpha}.$$</div>
<p>If $\varepsilon R\leq1$, the sum is empty. Otherwise the last inequality follows by an integral comparison, using $\alpha&lt;1$. Summing $f(x-v)$ over $v\in B_R$ now bounds the nearby-endpoint contribution by</p>
<div class="math-display">$$C A a_{k-1}\varepsilon^{1-\alpha}R^{-p}.$$</div>
<p>Finally, for $2^{l-1}R&lt;\|v\|\leq2^lR$, $l\geq1$, and $u\in B_{R/2}$, the distance $\|u-v\|$ is at least $2^{l-2}R$. Discard the crossing penalty. The $u$ sum is at most $AR^\alpha$, and the $v$ sum of $f(x-v)$ is at most $A(2^{l+1}R)^\alpha$. Thus the far contribution is at most</p>
<div class="math-display">$$C A^2R^\alpha\sum_{l\geq1}(2^lR)^{-d-\alpha}(2^{l+1}R)^\alpha
\leq C' A^2R^{-p}\sum_{l\geq1}2^{-dl}\leq C''A^2R^{-p}.$$</div>
<p>The kernel exponent remains $d+\alpha$ until the spatial average is inserted. Combining the three estimates, including $D$, gives a constant $C_0=C_0(d,\alpha,A,D)$ such that</p>
<div class="math-display">$$a_k\leq\max\{a_{k-1},\ C_0(\varepsilon^{1-d-\alpha}+1)+C_0\varepsilon^{1-\alpha}a_{k-1}\}.$$</div>
<p>Fix $\varepsilon&gt;0$ small enough that $C_0\varepsilon^{1-\alpha}\leq1/2$, and put $B=C_0(\varepsilon^{1-d-\alpha}+1)$. Since $a_2\leq4^p$, induction gives $a_k\leq\max\{4^p,2B\}$ for every $k\geq2$. Every lattice point belongs to one of these cubes, proving the result.</p>
<p>The proof uses the average on centred cubes only: each translated sum is contained, after changing variables, in a larger centred cube. The exponent restriction $\alpha&lt;1$ supplies the small factor in the short-displacement term. The far shells sum geometrically in every positive dimension.</p>

## The percolation consequence {#section-critical}

<a id="tag-TGF9" data-assertion="theorem" data-title="Critical pointwise upper bound for comparable power kernels below alpha one"></a>
<p>Suppose $0&lt;\alpha&lt;\min\{1,d\}$ and</p>
<div class="math-display">$$c\|z\|^{-d-\alpha}\leq J(z)\leq C\|z\|^{-d-\alpha}\qquad(z\ne0)$$</div>
<p>for constants $0&lt;c\leq C&lt;\infty$. Then there is a finite constant $B$, independent of $x$ and $0\leq\beta\leq\beta_c$, such that</p>
<div class="math-display">$$\tau_\beta(x)\leq B\langle x\rangle^{-d+\alpha}.$$</div>
<p><em>Proof.</em> The <a href="/tag/KXV3/">power-law transition theorem</a> gives $0&lt;\beta_c&lt;\infty$. The <a href="/tag/MRZO/">sharp averaged upper bound</a> gives $\sum_{x\in B_t}\tau_{\beta_c}(x)\leq At^\alpha$ with $A&lt;\infty$. Apply 0VB3 at $\beta_c$ and then PIZX to $f=\tau_{\beta_c}$. Monotonicity gives the same bound for every smaller intensity, including zero.</p>
<p>This proves the upper half of the critical two-point theorem. It does not prove a lower bound at each vertex, the subcritical far-field equivalent, or a crossover theorem. The constant may depend on the fixed kernel; no uniformity beyond the stated parameters of the preceding analytic theorem is asserted here.</p>

## The localization dependency {#section-localization}

<p>TGF9 supplies the pointwise upper input to <a href="/tag/YUHF/">the finite-range random-box argument</a> without assuming localization. Indeed, for any family of symmetric translation-invariant kernels $0\leq J_r\leq J$, $r\geq1$, supported on $\|z\|\leq Lr$ for a fixed $L\geq1$, monotone coupling bounds their critical-intensity two-point functions by $\tau_{\beta_c}$. Their opening probabilities satisfy the same power-law upper bound uniformly in $r$. YUHF therefore gives</p>
<div class="math-display">$$\tau_r(0,x)\leq C\|x\|^{-d+\alpha}e^{-c\|x\|/r}\qquad(x\ne0),\qquad
\sum_x\|x\|^p\tau_r(0,x)\leq C_p r^{\alpha+p}\quad(p&gt;0).$$</div>
<p>A separate lower bound $\chi_r\geq c_1r^\alpha$ then yields the correlation-length condition. That lower bound remains a model-specific obligation for an arbitrary dominated family: the zero kernel, for example, satisfies domination and finite support but has susceptibility one. No cutoff susceptibility lower bound was used to obtain TGF9.</p>

## Source scope {#section-source}

<p>The <a href="/coverage/sources/pointwise-2404.07276v1/">source map</a> records the introduction and section2.1 of arXiv:2404.07276v1. The translated-centre count, its averaging domain and intensity factor are stated explicitly above. The shell sum retains its kernel exponent, and the induction starts at a finite base scale with positive $\varepsilon$. These local repairs are <a href="/errata/hutchcroft-pointwise-2024/">provisional</a>, checked against extracted PDF text on printed pp.7–10. The theorem's upper-bound conclusion is retained. Later near-critical bounds, triangle consequences and pointwise lower bounds remain separate reading and proof tasks. No compiled association or reviewed source correspondence is claimed.</p>


## Susceptibility captured by a box {#section-half-susceptibility}

<p>Keep the lattice model and supremum norm above. Write $\chi_\beta=\sum_x\tau_\beta(x)$, $A_\beta(n)=\sum_{x\in B_n}\tau_\beta(x)$, and $m_\beta(n)=\mathbb E_\beta|K_0(B_n)|$, where the last cluster uses only bonds within $B_n$. These two box means need not agree.</p>

<a id="tag-AXYA" data-assertion="proposition" data-title="A small internal box mean controls the full susceptibility"></a>
<p>For an integer $n\geq1$, let $b_\beta(n)=\sum_{z\ne0}q_\beta(z)\min\{1,\|z\|/n\}$. Then</p>
<div class="math-display">$$m_\beta(n)b_\beta(n)\leq\tfrac12\quad\Longrightarrow\quad\chi_\beta\leq2m_\beta(n)\leq2A_\beta(n).$$</div>
<p>In particular, if $J(z)\leq C\|z\|^{-d-\alpha}$ with $0&lt;\alpha&lt;1$, there is $\varepsilon_0&gt;0$, depending only on $d,\alpha,C$, such that</p>
<div class="math-display">$$m_\beta(n)\leq\frac{\varepsilon_0}{\beta}n^\alpha\quad\Longrightarrow\quad\chi_\beta\leq2m_\beta(n)\qquad(\beta&gt;0).$$</div>
<p><em>Proof.</em> By <a href="/tag/PTM2/">averaging the boundary functional</a>, some integer $k\in[1,n]$ has $\Phi_\beta(B_k)\leq m_\beta(n)b_\beta(n)\leq1/2$. Translation invariance allows the <a href="/tag/YLZV/">finite-size susceptibility bound</a> to be applied at every root. It gives $\chi_\beta\leq m_\beta(k)/(1-\Phi_\beta(B_k))\leq2m_\beta(n)$. The <a href="/tag/31X5/">crossing-profile shell estimate</a>, retaining its intensity factor, gives $b_\beta(n)\leq C_0\beta n^{-\alpha}$. Take $\varepsilon_0=(2C_0)^{-1}$.</p>
<p>The internal version is useful below: a large unrestricted mass in a box would not by itself imply a large cluster confined to that box.</p>

<a id="tag-6G4B" data-assertion="theorem" data-title="The half-susceptibility radius controls susceptibility and internal box means"></a>
<p>Assume the two-sided power-law bounds of TGF9, with $0&lt;\alpha&lt;\min\{1,d\}$. For $0\leq\beta&lt;\beta_c$, define the integer radius</p>
<div class="math-display">$$\xi_\beta=\min\{n\geq1:A_\beta(n)\geq\chi_\beta/2\}.$$</div>
<p>There are constants $c_0,C_0&gt;0$, independent of $\beta,n$, such that</p>
<div class="math-display">$$c_0\xi_\beta^\alpha\leq\chi_\beta\leq C_0\xi_\beta^\alpha,\qquad
c_0\min\{n,\xi_\beta\}^\alpha\leq m_\beta(n)\leq C_0\min\{n,\xi_\beta\}^\alpha\quad(n\geq1).$$</div>
<p>Set $\xi_{\beta_c}=\infty$. Then the box-mean comparison remains valid at $\beta_c$, with $\min\{n,\infty\}=n$.</p>
<p><em>Proof.</em> The critical point is finite and positive by <a href="/tag/KXV3/">KXV3</a>. <a href="/tag/L0TE/">Sharpness</a> gives $\chi_\beta&lt;\infty$ below it, so $A_\beta(n)\uparrow\chi_\beta$ and the minimum defining $\xi_\beta$ exists. The averaged bound <a href="/tag/MRZO/">MRZO</a> and monotonicity give $A_\beta(n)\leq C n^\alpha$, uniformly up to criticality. In particular $\chi_\beta\leq2A_\beta(\xi_\beta)\leq C'\xi_\beta^\alpha$.</p>
<p>If $\beta&gt;0$ and $1\leq n&lt;\xi_\beta$, then $2A_\beta(n)&lt;\chi_\beta$. The contrapositive of AXYA gives</p>
<div class="math-display">$$m_\beta(n)&gt;\varepsilon_0 n^\alpha/\beta\geq(\varepsilon_0/\beta_c)n^\alpha.$$</div>
<p>When $\xi_\beta\geq2$, apply this with $n=\xi_\beta-1\geq\xi_\beta/2$ to bound $\chi_\beta$ from below, and use monotonicity of the internal mean for all larger boxes. If $\xi_\beta=1$, the root gives $m_\beta(n)\geq1$. These bounds also cover $\beta=0$, where $\chi_0=\xi_0=m_0(n)=1$. The upper box bound follows from $m_\beta(n)\leq\min\{A_\beta(n),\chi_\beta\}$. At criticality, <a href="/tag/VVB0/">the critical boundary-flux bound</a> and MRZO give the two box bounds directly.</p>
<p>The lower kernel envelope is essential to this argument. In nearest-neighbour percolation on $\mathbb Z$, with intensity one on each neighbouring pair and zero otherwise, put $p=1-e^{-\beta}$. For every fixed $0&lt;\alpha&lt;1$ this kernel satisfies a power-law upper bound, while $\beta_c=\infty$ and</p>
<div class="math-display">$$\chi_\beta=\frac{1+p}{1-p},\qquad A_\beta(n)=\frac{1+p-2p^{n+1}}{1-p},\qquad
\xi_\beta=\min\{n\geq1:p^{n+1}\leq(1+p)/4\}.$$</div>
<p>As $\beta\to\infty$, $\chi_\beta\sim2/(1-p)$ and $\xi_\beta\sim\log2/(1-p)$. Thus $\chi_\beta/\xi_\beta^\alpha\to\infty$. Corollary 2.5's upper-kernel-only formulation cannot give a uniform comparison on its stated interval. This is recorded as a <a href="/errata/hutchcroft-pointwise-2024/#half-susceptibility-hypotheses">provisional hypothesis correction</a>; the two-sided hypotheses of Proposition 2.3 are retained here.</p>

## Two weighted crossings {#section-two-crossings}

<a id="tag-SFR0" data-assertion="proposition" data-title="Two crossing penalties bound the separated three-kernel convolution"></a>
<p>Let $0&lt;\alpha&lt;1$, $s\geq1$, and $K(z)=\langle z\rangle^{-d-\alpha}$. Then</p>
<div class="math-display">$$\sum_{z\in\mathbb Z^d}K(z)\min\{1,\langle z\rangle/s\}\leq C s^{-\alpha}.$$</div>
<p>Consequently, if $u,v\in\mathbb Z^d$ and $L=\|u-v\|\geq s$,</p>
<div class="math-display">$$\sum_{\|a-u\|\leq L/4}\ \sum_{\|b-v\|\leq L/4}
K(a-u)K(a-b)K(b-v)
\min\{1,\langle a-u\rangle/s\}\min\{1,\langle b-v\rangle/s\}
\leq C' s^{-2\alpha}\langle u-v\rangle^{-d-\alpha}.$$</div>
<p>The constants depend only on $d,\alpha$.</p>
<p><em>Proof.</em> The origin contributes at most $C/s$. For nonzero displacements, sum over integer supremum-norm shells to obtain</p>
<div class="math-display">$$\sum_z K(z)\min\{1,\langle z\rangle/s\}
\leq\frac C s+\frac C s\sum_{1\leq l\leq s}l^{-\alpha}+C\sum_{l&gt;s}l^{-1-\alpha}\leq C' s^{-\alpha}.$$</div>
<p>The short sum uses $\alpha&lt;1$ and the tail uses $\alpha&gt;0$; the same bound covers $1\leq s&lt;2$. In the double sum, $\|a-b\|\geq L/2$, so $K(a-b)\leq C\langle u-v\rangle^{-d-\alpha}$. Extend the two remaining sums to all of $\mathbb Z^d$ and apply the first estimate twice.</p>

## The subcritical far field {#section-near-critical-upper}

<a id="tag-CQK2" data-assertion="theorem" data-title="Uniform crossover upper bound for two-sided power-law percolation below alpha one"></a>
<p>Under the hypotheses of 6G4B, there is a finite constant $C_*$, independent of $0\leq\beta\leq\beta_c$ and $x\ne0$, such that</p>
<div class="math-display">$$\tau_\beta(x)\leq C_*\|x\|^{-d+\alpha}
\min\left\{1,\left(\frac{\xi_\beta}{\|x\|}\right)^{2\alpha}\right\}.$$</div>
<p>The minimum is one when $\xi_\beta=\infty$. Equivalently, below criticality the far-field bound is $\tau_\beta(x)\leq C\chi_\beta^2\langle x\rangle^{-d-\alpha}$ for $\|x\|\geq\xi_\beta$.</p>
<p><em>Proof.</em> TGF9 proves the first part of the bound, including $\beta=\beta_c$; at $\beta=0$ the conclusion is immediate. Fix $0&lt;\beta&lt;\beta_c$ and abbreviate $\chi=\chi_\beta$, $\xi=\xi_\beta$. Delete all bonds longer than an integer $N\geq1$, and denote the resulting two-point function by $\tau_N$. The <a href="/tag/YUHF/">finite-range exit argument</a>, with TGF9 as its pointwise input, gives exponential decay for this truncated model. Hence</p>
<div class="math-display">$$H=\max\left\{1,\sup_{\|x\|\geq\xi}\frac{\tau_N(x)\langle x\rangle^{d+\alpha}}{\chi^2}\right\}&lt;\infty.$$</div>
<p>We will bound $H$ independently of $\beta,N$. Constants below depend on the fixed kernel, $d,\alpha$, but not on an integer parameter $r\geq1$ that will be chosen at the end.</p>
<p>For a target $x$, write $X=\|x\|$. Let $E_x$ be the event that a simple open path <em>from $0$ to $x$</em> contains a bond of length at least $X/16$. Splitting the path at such a bond and applying BK gives, when $X\geq32$,</p>
<div class="math-display">$$\mathbb P(E_x)\leq\sum_{\|a-b\|\geq X/16}\tau_N(a)q_{\beta,N}(a,b)\tau_N(x-b)
\leq C\chi^2\langle x\rangle^{-d-\alpha}.$$</div>
<p>Here $q_{\beta,N}(a,b)\leq\beta_c C\|a-b\|^{-d-\alpha}$ and $\sum_y\tau_N(y)\leq\chi$. Specifying the terminal vertex is necessary for the second connection factor.</p>
<p>Put $s=r\xi$ and suppose $X\geq32s$. Average independently over centres $z\in B_s$ and $w\in x+B_s$, using boxes $z+B_s$ and $w+B_s$. They contain their respective roots and are disjoint. On $\{0\leftrightarrow x\}\setminus E_x$, take a simple open path, its first exit edge $(u,a)$ from the first box, and its first entrance edge $(b,v)$ into the second. Both edges have length less than $X/16$. They are distinct and occur in that order, so the two edges and the three intervening connection segments have disjoint witnesses.</p>
<p>The integer-interval count used in 0VB3 bounds each averaged crossing indicator by $d\min\{1,\|u-a\|/s\}$, or its analogue at the other root. Since the centres are independent, the two penalties multiply. BK and the power-law bond bound therefore give</p>
<div class="math-display">$$\mathbb P(\{0\leftrightarrow x\}\setminus E_x)\leq C
\sum_{u\in B_{2s}}\sum_{v\in x+B_{2s}}\tau_N(u)\tau_N(x-v)
\sum_{\substack{\|a-u\|&lt;X/16\\\|b-v\|&lt;X/16}}
K(a-u)K(b-v)\tau_N(b-a)
\min\{1,\langle a-u\rangle/s\}\min\{1,\langle b-v\rangle/s\}.$$</div>
<p>We have $\|u-v\|\geq X-4s\geq7X/8$ and $\|a-b\|\geq3X/4\geq\xi$. Thus the defining bound for $H$ applies to the middle connection. Each crossing length is also at most $\|u-v\|/4$, so SFR0 bounds the inner sum by</p>
<div class="math-display">$$C H\chi^2 s^{-2\alpha}\langle x\rangle^{-d-\alpha}.$$</div>
<p>Summing the two endpoint connection factors, then using $\chi\leq C\xi^\alpha$ from 6G4B, gives</p>
<div class="math-display">$$\mathbb P(\{0\leftrightarrow x\}\setminus E_x)
\leq C H\chi^4(r\xi)^{-2\alpha}\langle x\rangle^{-d-\alpha}
\leq C H r^{-2\alpha}\chi^2\langle x\rangle^{-d-\alpha}.$$</div>
<p>For the remaining range $\xi\leq X&lt;32r\xi$, TGF9 and $\chi\geq c\xi^\alpha$ give $\tau_N(x)\leq C r^{2\alpha}\chi^2\langle x\rangle^{-d-\alpha}$. Combining the two ranges and increasing $C$ to include the defining lower bound $H\geq1$ yields</p>
<div class="math-display">$$H\leq C(1+r^{2\alpha})+C r^{-2\alpha}H.$$</div>
<p>Choose a fixed integer $r$ large enough that $C r^{-2\alpha}\leq1/2$. Since $H$ is finite, the last term can be subtracted, giving a bound independent of $\beta,N$. Let $N\to\infty$. Every connection has a finite path witness, so $\tau_N(x)\uparrow\tau_\beta(x)$. Finally use $\chi\asymp\xi^\alpha$ and combine with TGF9 to obtain the displayed crossover bound.</p>
<p>The proof retains the original short-edge restriction throughout; weakening it to $X/4$ would invalidate the subsequent comparison with $\|u-v\|/4$. Together with the terminal-vertex specification and the centre $w$ being near $x$, this is a <a href="/errata/hutchcroft-pointwise-2024/#two-box-endpoints-and-separation">provisional repair of the printed argument</a>. The upper conclusion of Proposition 2.3 is unchanged. No pointwise lower bound is inferred here.</p>
<p>This radius is defined from the unrestricted spatial mass. The separate cutoff radius used in <a href="/tag/TFKR/">TFKR</a> is not identified with it without a comparison theorem. The present argument needs neither the cutoff derivative formula nor a cutoff susceptibility lower bound.</p>


## Joining two confined clusters {#section-near-critical-lower}

<a id="tag-TQ77" data-assertion="theorem" data-title="A confined two-cluster joining argument gives the matching pointwise lower bound"></a>
<p>Under the two-sided power-law hypotheses of 6G4B, there is $c_*&gt;0$ such that, uniformly for $\beta_c/2\leq\beta\leq\beta_c$ and $x\ne0$,</p>
<div class="math-display">$$\mathbb P_\beta\bigl(0\overset{B_{2\|x\|}}\longleftrightarrow x\bigr)
\geq c_*\|x\|^{-d+\alpha}\min\left\{1,\left(\frac{\xi_\beta}{\|x\|}\right)^{2\alpha}\right\}.$$</div>
<p>Together with CQK2, this proves matching upper and lower bounds for the full two-point function, including the critical estimate.</p>
<p><em>Proof.</em> Put $X=\|x\|$ and $t=\min\{X,\xi_\beta\}$. The lower intensity bound gives $q_\beta(a,b)\geq c_1\|a-b\|^{-d-\alpha}$, uniformly over this intensity interval: use $1-e^{-h}\geq h e^{-h}$ and $\beta J\leq\beta_c C$. If $t&lt;8$, the direct bond gives the claimed bound after decreasing its constant, since the required expression is $t^{2\alpha}X^{-d-\alpha}$.</p>
<p>Now take $n=\lfloor t/4\rfloor$, so $t/8\leq n\leq t/4$. Let $K_1$ be the root cluster inside $B_n$, and $K_2$ the cluster of $x$ inside $x+B_n$. These boxes are disjoint. Their clusters are independent, identically distributed after translation, and independent of all bonds between the boxes. Write $U=|K_1|$, $V=|K_2|$, and let $Z$ count open bonds joining $K_1$ to $K_2$. Every such bond has length between $X/2$ and $3X/2$. By 6G4B,</p>
<div class="math-display">$$\mathbb E Z\asymp X^{-d-\alpha}(\mathbb E U)^2
\asymp n^{2\alpha}X^{-d-\alpha}.$$</div>
<p>We need a bound on $\mathbb E U^2$ that preserves the first moment. Under the full critical law, let $T=\max_{y\in B_n}|K_y\cap B_n|$ and let $M$ be the least positive integer with $\mathbb P(T\geq M)\leq e^{-1}$. The cluster intersections partition $B_n$, so</p>
<div class="math-display">$$\mathbb E T^2\leq\sum_{u,v\in B_n}\tau_{\beta_c}(v-u)\leq C n^{d+\alpha}.$$</div>
<p>The last inequality is MRZO applied to $B_{2n}$ at each root $u$. Since $M\geq2$ and $\mathbb P(T\geq M-1)&gt;e^{-1}$, it follows that $M\leq2\sqrt{e\mathbb E T^2}\leq C n^{(d+\alpha)/2}$. The maximum-cluster quantile for the induced model in $B_n$ at intensity $\beta$ is at most $M$, by monotone coupling. Apply <a href="/tag/12NL/">rooted damping</a> to that finite model, followed by its <a href="/tag/BZDZ/">second-moment consequence</a>. This gives</p>
<div class="math-display">$$\mathbb E U^2\leq C M\mathbb E U\leq C n^{(d+3\alpha)/2}.$$</div>
<p>Conditional on the two clusters, $Z$ is a sum of $UV$ independent bond indicators, each with probability at most $C X^{-d-\alpha}$. Count every pair of distinct bonds, including pairs sharing an endpoint. Then</p>
<div class="math-display">$$\mathbb E\binom Z2\leq C X^{-2d-2\alpha}\mathbb E[U^2V^2]
=C X^{-2d-2\alpha}(\mathbb E U^2)^2
\leq C n^{d+3\alpha}X^{-2d-2\alpha}\leq C'\mathbb E Z.$$</div>
<p>For the last inequality, divide by the lower bound on $\mathbb E Z$ and use $(n/X)^{d+\alpha}\leq1$. Therefore $\mathbb E Z^2\leq C\mathbb E Z$, and Cauchy–Schwarz yields</p>
<div class="math-display">$$\mathbb P(Z&gt;0)\geq\frac{(\mathbb E Z)^2}{\mathbb E Z^2}
\geq c n^{2\alpha}X^{-d-\alpha}\asymp t^{2\alpha}X^{-d-\alpha}.$$</div>
<p>The internal paths and the joining bond lie in $B_n\cup(x+B_n)\subset B_{2X}$, giving the confined connection in the statement.</p>
<p>The <a href="/errata/hutchcroft-pointwise-2024/#joining-pairs-and-internal-means">provisional source repair</a> keeps the second cluster rooted at $x$, uses the internal mean supplied by 6G4B, counts pairs sharing an endpoint and handles the bounded-radius case before taking an integer part. It proves the lower half directly; it does not discharge the different cutoff hypotheses of <a href="/tag/NI07/">NI07</a>.</p>

## Triangle diagrams at the crossover scale {#section-triangle-crossover}

<a id="tag-RCTO" data-assertion="theorem" data-title="The crossover upper bound gives bounded, logarithmic or power-law triangle growth"></a>
<p>For the same model and $0\leq\beta&lt;\beta_c$, put</p>
<div class="math-display">$$\nabla_\beta=\sum_{x,y\in\mathbb Z^d}\tau_\beta(x)\tau_\beta(y-x)\tau_\beta(y).$$</div>
<p>Uniformly below criticality,</p>
<div class="math-display">$$\nabla_\beta\leq C\begin{cases}
1,&amp;d&gt;3\alpha,\\
1+\log\xi_\beta,&amp;d=3\alpha,\\
\xi_\beta^{3\alpha-d},&amp;d&lt;3\alpha.
\end{cases}$$</div>
<p>If $d&gt;3\alpha$, the critical triangle is finite as well. The assertion uses the upper bound only.</p>
<p><em>Proof.</em> The term with $x=y=0$ is one. For the other terms, split according to the dyadic size $R\leq\max\{\|x\|,\|y\|,\|x-y\|\}&lt;2R$, $R=1,2,4,\ldots$. At least two sides have length at least $R/2$. Relabel the three vertices so that these two sides meet at the root; translation invariance and symmetry preserve the product. There are only a fixed number of such relabellings. Write their endpoints as $a,b$ and their remaining displacement as $w=b-a$.</p>
<p>For each $w\in B_{2R}$ there are at most $|B_{2R}|\leq C R^d$ choices of $a$. The two long-side factors are each at most $C R^{-d+\alpha}$ by TGF9, or at most $C\xi_\beta^{2\alpha}R^{-d-\alpha}$ by CQK2 and 6G4B. These bounds are valid also in the first shell after increasing the constant. For the remaining factor, MRZO gives $\sum_{w\in B_{2R}}\tau_\beta(w)\leq C R^\alpha$, while its full sum is at most $C\xi_\beta^\alpha$. Thus the contribution of one shell is at most</p>
<div class="math-display">$$\begin{cases}
C R^{3\alpha-d},&amp;R\leq\xi_\beta,\\
C\xi_\beta^{5\alpha}R^{-d-2\alpha},&amp;R&gt;\xi_\beta.
\end{cases}$$</div>
<p>The second dyadic sum is at most $C\xi_\beta^{3\alpha-d}$. The first is bounded, logarithmic, or at most that same power, according to the sign of $3\alpha-d$. The initial term accounts for the positive constant in $1+\log\xi_\beta$. At criticality and $d&gt;3\alpha$, the critical upper and averaged bounds give the summable series $\sum_{j\geq0}2^{j(3\alpha-d)}$ directly.</p>
<p>Grouping by the largest scale avoids an intermediate convolution estimate requiring $2\alpha&lt;d$. It also keeps two far-field connection factors, each carrying a susceptibility square. The <a href="/errata/hutchcroft-pointwise-2024/#triangle-shell-factors-and-range">source's display corrections</a> are provisional; the resulting three-regime triangle bound is retained.</p>
<p>When $d=3\alpha$, this is logarithmic growth in $\xi_\beta$, and hence in $\chi_\beta$ by 6G4B. To replace it by $O(\log(1/(\beta_c-\beta)))$ one still needs a polynomial susceptibility bound in the distance to criticality. The cited result supplying that bound, the mean-field consequences and the differential inequality in Remark 2.7 require separate source reconciliation. They are not consequences of a change of notation alone.</p>


## Critical susceptibility, volume and density {#section-mean-field-consequences}

<a id="tag-A3S7" data-assertion="theorem" data-title="Mean-field bounds and marginal logarithmic bounds for two-sided power-law kernels below alpha one"></a>
<p>Let $d\geq1$, $0&lt;\alpha&lt;\min\{1,d\}$, and let the symmetric translation-invariant intensity kernel satisfy</p>
<div class="math-display">$$0&lt;c\|x-y\|^{-d-\alpha}\leq J(x,y)\leq C\|x-y\|^{-d-\alpha}\qquad(x\ne y).$$</div>
<p>Use independent bonds with probabilities $1-e^{-\beta J(x,y)}$, and write $p_n=\mathbb P_{\beta_c}(|K_0|\geq n)$ and $\theta(\beta)=\mathbb P_\beta(|K_0|=\infty)$. If $d&gt;3\alpha$, then</p>
<div class="math-display">$$\nabla_{\beta_c}&lt;\infty,\qquad
\chi_{\beta_c-\varepsilon}\asymp\varepsilon^{-1},\qquad
p_n\asymp n^{-1/2},\qquad
\theta(\beta_c+\varepsilon)\asymp\varepsilon.$$</div>
<p>If $d=3\alpha$ (necessarily $d\in\{1,2\}$), then for all sufficiently small $\varepsilon&gt;0$ and all sufficiently large integers $n$,</p>
<div class="math-display">$$\begin{aligned}
\nabla_{\beta_c-\varepsilon}&amp;\leq C_1\log(1/\varepsilon),\\
\frac{c_1}{\varepsilon}\leq\chi_{\beta_c-\varepsilon}&amp;\leq\frac{C_2}{\varepsilon}\log^2(1/\varepsilon),\\
\frac{c_2}{\sqrt n\log^2 n}\leq p_n&amp;\leq\frac{C_3\log^2 n}{\sqrt n},\\
c_3\varepsilon\leq\theta(\beta_c+\varepsilon)&amp;\leq C_4\varepsilon\log^2(1/\varepsilon).
\end{aligned}$$</div>
<p>The comparison constants depend on the fixed model. In both regimes $\theta(\beta_c)=0$. These logarithmic powers are bounds, not asserted asymptotic corrections.</p>
<p><em>Proof.</em> The kernel has a finite positive row mass $M=\sum_{x\ne0}J(0,x)$. The lower power envelope gives $0&lt;\beta_c&lt;\infty$ by KXV3. Sharpness L0TE gives finite susceptibility below $\beta_c$, and RDF0 gives $\chi_\beta\to\infty$ as $\beta\uparrow\beta_c$. Translation on $\mathbb Z^d$ has the mass-transport property required in <a href="/tag/4KBG/">the corrected triangle inequality</a>.</p>
<p>To retain its row normalization, put $J'=J/M$ and $\lambda=M\beta$. The configurations, susceptibility and triangle diagram are unchanged. Applying 4KBG in $\lambda$ and multiplying the derivative by $M$ gives, almost everywhere below criticality,</p>
<div class="math-display">$$\chi'_\beta\geq\frac{(\chi_\beta-\nabla_\beta)_+^2}{3M\beta^2\nabla_\beta^2}.$$</div>
<p>Susceptibility is locally absolutely continuous by MXGM. On a terminal interval the factor $1/(3M\beta^2)$ is bounded below by a positive constant.</p>
<p>If $d&gt;3\alpha$, RCTO bounds the triangle uniformly and proves its critical finiteness. The power case $q=0$ of <a href="/tag/GQJY/">GQJY</a> gives $\chi_{\beta_c-\varepsilon}\leq C/\varepsilon$. If $d=3\alpha$, RCTO and 6G4B instead give</p>
<div class="math-display">$$\nabla_\beta\leq C(1+\log\xi_\beta)\leq C'\log(e\chi_\beta).$$</div>
<p>The logarithmic case of GQJY now gives both the claimed susceptibility upper bound and $\nabla_{\beta_c-\varepsilon}\leq C\log(1/\varepsilon)$. In particular, this conversion does not require the separate polynomial-susceptibility theorem cited at the end of source section 2.3. In either case MXGM gives $\chi_{\beta_c-\varepsilon}\geq1/(M\varepsilon)$.</p>
<p>Apply <a href="/tag/QS3L/">entropy comparison</a> with logarithmic power zero or two. It gives the displayed upper bounds on $p_n$ and $\theta(\beta_c+\varepsilon)$; the tail upper bound tends to zero, giving nonpercolation at criticality. The universal integrated lower bound <a href="/tag/36PN/">36PN</a> applies to this countable transitive summable model with finite critical intensity. Use MBV2 when $d&gt;3\alpha$, and <a href="/tag/QW2L/">QW2L</a> with $a=2$ when $d=3\alpha$, to obtain the pointwise tail lower bounds. Finally L0TE gives</p>
<div class="math-display">$$\theta(\beta_c+\varepsilon)\geq1-\frac{\beta_c}{\beta_c+\varepsilon}=\frac{\varepsilon}{\beta_c+\varepsilon},$$</div>
<p>which supplies the density lower bounds.</p>
<p>This completes the consequences in Theorem 1.1 of the pointwise source using the corrected square. The preceding paragraph of the triangle section records the earlier outstanding logarithm conversion; GQJY supplies it here. No stronger numerator, unproved pointwise lower tail, or existence of critical exponents is used.</p>

## Just below the upper-critical dimension {#section-near-mean-field}

<a id="tag-YYSP" data-assertion="theorem" data-title="The corrected triangle inequality retains the susceptibility bound in Remark 2.7"></a>
<p>Under the same two-sided kernel hypotheses, suppose $d/3&lt;\alpha&lt;\min\{1,2d/5\}$. Set $g=\alpha/(2d-5\alpha)&gt;1$. For sufficiently small $\varepsilon&gt;0$,</p>
<div class="math-display">$$\frac1{M\varepsilon}\leq\chi_{\beta_c-\varepsilon}\leq C\varepsilon^{-g}.$$</div>
<p>In particular, if the susceptibility exponent $\gamma=\lim_{\varepsilon\downarrow0}\log\chi_{\beta_c-\varepsilon}/\log(1/\varepsilon)$ exists, then $1\leq\gamma\leq g$.</p>
<p><em>Proof.</em> RCTO and 6G4B give $\nabla_\beta\leq C\chi_\beta^q$, where $q=(3\alpha-d)/\alpha=3-d/\alpha\in(0,1/2)$. The normalized differential inequality in the preceding proof, local absolute continuity and endpoint divergence allow the power case of GQJY. Its exponent is</p>
<div class="math-display">$$\frac1{1-2q}=\frac{\alpha}{2d-5\alpha}=g.$$</div>
<p>MXGM supplies the lower bound. Taking logarithms proves the exponent assertion when the limit exists.</p>
<p>The triangle is $o(\chi)$ here, so the squared positive-part numerator has the same eventual power as the source's stronger numerator. The latter is not needed. The <a href="/errata/hutchcroft-pointwise-2024/#remark-critical-limit">provisional source entry</a> also corrects the displayed limit in Remark 2.7 to $\beta\uparrow\beta_c$, rather than infinity. This is a subcritical estimate at a finite threshold.</p>

<a id="tag-LKWW" data-assertion="corollary" data-title="Conditional convergence of the three critical exponents follows from explicit tail and density bounds"></a>
<p>In the smaller range $d/3&lt;\alpha&lt;\min\{1,4d/11\}$, the number $g$ above satisfies $1&lt;g&lt;2$, and</p>
<div class="math-display">$$p_n\leq C n^{-(2-g)/2},\qquad
c\varepsilon\leq\theta(\beta_c+\varepsilon)\leq C\varepsilon^{2-g}.$$</div>
<p>If the finite exponents $\delta&gt;0$ and $\beta_{\mathrm{ord}}$ are defined by</p>
<div class="math-display">$$\frac1\delta=\lim_{n\to\infty}\frac{-\log p_n}{\log n},\qquad
\beta_{\mathrm{ord}}=\lim_{\varepsilon\downarrow0}\frac{\log\theta(\beta_c+\varepsilon)}{\log\varepsilon},$$</div>
<p>then</p>
<div class="math-display">$$2\leq\delta\leq\frac2{2-g},\qquad 2-g\leq\beta_{\mathrm{ord}}\leq1.$$</div>
<p>Together with $1\leq\gamma\leq g$, these bounds imply convergence to $\gamma=1$, $\delta=2$ and $\beta_{\mathrm{ord}}=1$ as $\alpha\downarrow d/3$ along any family for which the respective exponents exist. No monotonicity in $\alpha$ is asserted.</p>
<p><em>Proof.</em> The inequalities $g&lt;2$ and $\alpha&lt;4d/11$ are equivalent because $2d-5\alpha&gt;0$. Apply <a href="/tag/X8T6/">the power-law entropy transfer</a> to YYSP; L0TE supplies the density lower bound. The pointwise tail upper bound gives $1/\delta\geq(2-g)/2$. On the other hand, if $1/\delta&gt;1/2$, choose $0&lt;\eta&lt;1/2$ with $1/2+\eta&lt;1/\delta$. Then $p_n\leq n^{-1/2-\eta}$ eventually, and $\sum_{j=1}^N p_j=O(N^{1/2-\eta})$, contradicting 36PN. Thus $1/\delta\leq1/2$. Dividing the logarithms of the density bounds by the negative number $\log\varepsilon$ gives the stated bounds on $\beta_{\mathrm{ord}}$. Finally $g\to1$ as $\alpha\downarrow d/3$, so each pair of bounds has the claimed common limit.</p>
<p>This proves the limiting-exponent conclusion of Remark 2.7 directly from the written entropy and integrated-tail arguments on a neighbourhood of $d/3$. It neither assumes those exponents exist nor identifies them away from the limit.</p>
