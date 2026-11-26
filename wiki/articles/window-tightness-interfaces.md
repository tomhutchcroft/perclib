---
{
  "id": "window-tightness-interfaces",
  "title": "Finite-window tightness interfaces",
  "subtitle": "Quantile targets, amplification and the excluded zero iteration",
  "kind": "method",
  "category": "Cluster geometry",
  "summary": "The earlier source records universal quantile bounds and finite-window amplification as targets. The newer source implements them using disjoint finite witnesses, for arbitrary profiles and roots outside the observation set.",
  "context": ["A countable vertex set V with an arbitrary independent unordered-pair profile, including probabilities zero and one.", "A finite nonempty observation set; clusters are formed in the whole graph and the distinguished root need not belong to the observation set.", "The opening sections describe the interface source at 5d6efa8. The appended source account at 22d8485 explains its later implementation; formal status still comes from the manifest and correspondence review."],
  "related": ["universal-tightness", "cluster-partitions", "finite-volume", "bk-inequality"],
  "sourceIds": ["perclib-tightness-interface", "hutchcroft-powerlaw-2021", "perclib-tightness-bk-step", "perclib-quantile-from-amplification", "perclib-window-quantile-moments", "perclib-finite-quantile", "perclib-train10-percolation-bond-tightness-truncatedmean"],
  "aliases": ["tightness target", "finite-window amplification", "quantile endpoint", "marked tree splitting"],
  "prototypeUses": []
}
---

## The observed quantities {#section-observables}

<p>Use the <a href="/tag/GJIW/">maximum cluster intersection and quantile</a>, now for an arbitrary Bernoulli profile $q$. Write</p>
<div class="math-display">$$X=\max_{v\in\Lambda}|K_v\cap\Lambda|,\qquad Y_u=|K_u\cap\Lambda|,\qquad M=\min\{n\in\mathbb N:\mathbb P_q(X\geq n)\leq e^{-1}\}.$$</div>
<p>These are full-cluster intersections. An open path between two observed vertices may leave $\Lambda$, and $u$ may lie outside $\Lambda$. Since $1\leq X\leq|\Lambda|$, the integer minimum exists and $2\leq M\leq|\Lambda|+1$. Allowing zero in its defining set changes nothing: the tail at zero is one. Connection measurability on countable vertex sets makes each finite intersection count and its maximum measurable.</p>
<p>For a singleton $\Lambda=\{v\}$, one has $X=1$ in every configuration, hence $M=2$ for every profile. Indeed, the tails at zero and one are one, and the tail at two is zero. For an outside root, $Y_u$ is instead the indicator that $u$ connects to $v$; it need not be identically one. Thus the singleton witness tests the maximum and quantile conventions without collapsing the rooted observable.</p>

## Two properties to prove {#section-properties}

<a id="tag-C5Q9" data-assertion="definition" data-title="Universal quantile-tail property on a countable vertex set"></a>
<p>A countable vertex set has the <em>universal quantile-tail property</em> if, for every independent pair profile $q$, finite nonempty $\Lambda$, real $a\geq1$, real $0&lt;\varepsilon\leq1$, and root $u$,</p>
<div class="math-display">$$\mathbb P_q(X\geq aM)\leq e^{-a/9},\qquad \mathbb P_q(X&lt;\varepsilon M)\leq27\varepsilon,$$</div>
<div class="math-display">$$\mathbb P_q(Y_u\geq aM)\leq e\,\mathbb P_q(Y_u\geq M)e^{-a/9}.$$</div>
<p>This is the general-profile target corresponding to the <a href="/tag/4724/">two-sided quantile bounds</a> and <a href="/tag/21D4/">rooted refinement</a>. The source paper states the weighted exponential model; the library target explicitly ranges over all profiles, including probability-one coordinates. The formulas retain the non-strict upper tails and the strict lower-tail event.</p>

<a id="tag-JGZB" data-assertion="definition" data-title="Finite-window amplification property with at least one iteration"></a>
<p>A countable vertex set has the <em>finite-window amplification property</em> if, for every profile $q$, finite nonempty $\Lambda$, real $\lambda\geq1$, integer $k\geq1$, and root $u$,</p>
<div class="math-display">$$\mathbb P_q(X\geq3^k\lambda)\leq\mathbb P_q(X\geq\lambda)^{3^{k-1}+1},$$</div>
<div class="math-display">$$\mathbb P_q(Y_u\geq3^k\lambda)\leq\mathbb P_q(X\geq\lambda)^{3^{k-1}}\mathbb P_q(Y_u\geq\lambda).$$</div>
<p>The exponent $k-1$ is an ordinary nonnegative integer because $k\geq1$. This is the corrected range used by the library target, following a recorded source discrepancy. It is not a claim that the paper prints that range, or that Tom has resolved the reserved source-fidelity decision.</p>
<p>These definitions package the statements to be established. They are not proofs of universal tightness or amplification. The pinned source contains the two proposition definitions and the singleton identities above, but no proof of either universal property. Nor does this article assert a compiled tag association for them.</p>

## Why zero iterations must be excluded {#section-zero}

<p>Take two vertices joined by one bond of probability $1/2$, let $\Lambda$ contain both vertices and set $\lambda=2$. Then $X$ is two when the bond is open and one when it is closed, so $\mathbb P(X\geq2)=1/2$. At $k=0$, the first proposed inequality with the printed real exponent would give</p>
<div class="math-display">$$\frac12\leq\left(\frac12\right)^{4/3},$$</div>
<p>which is false. Interpreting $k-1$ as truncated natural subtraction would instead give exponent two and is false as well. Choosing either endpoint as $u$ gives the same counterexample to the rooted inequality: its two tail factors again multiply to $(1/2)^{4/3}$, or to $1/4$ with truncated subtraction. Restricting to $k\geq1$ removes this false endpoint; it does not by itself prove the remaining inequalities.</p>

## What the proof still needs {#section-obligations}

<p>The amplification route first partitions a finite connected witness into connected edge pieces with controlled numbers of marked vertices. Pairwise disjoint edge sets are essential for <a href="/tag/AUUG/">repeated BK</a>, and the pieces must cover the original edges and retain coverage of the distinguished root, including when it lies outside $\Lambda$. Merely finding several connected subgraphs, or making their vertex sets disjoint, is a different assertion.</p>
<p>Once the finite amplification inequalities are available, their fixed-threshold events pass to a countable host through finite-edge approximations and finite connectivity witnesses. This passage uses convergence of probabilities and finite powers; it does not require continuity of the integer quantile $M$. The quantile estimates then need a separate numerical argument. These steps identify the remaining proof obligations rather than treating a source citation or a target definition as their discharge.</p>

## Finite witnesses in the newer source {#section-source-proof}

<p>The earlier sections describe the interface at revision 5d6efa8. The newer source at 22d8485 implements both properties through disjoint finite witnesses. For amplification, suppose $Y_u\geq3^k\lambda$, with $k\geq1$ and real $\lambda\geq1$. Choose finitely many open paths from $u$ carrying the observed vertices of its cluster. Keep the connected edge component through $u$ and discard loops. The marked vertices are its vertices in $\Lambda$; the root itself need not be marked.</p>
<p>The imported connected-piece splitting theorem supplies at least $3^{k-1}+1$ pairwise edge-disjoint connected pieces. Each contains at least $\lambda$ marked vertices, and their endpoint sets cover the root. Select a piece through $u$ and any $3^{k-1}$ others. The first witnesses $Y_u\geq\lambda$. Every other piece contains a marked vertex, whose cluster within that piece meets $\Lambda$ at least $\lambda$ times, and therefore witnesses $X\geq\lambda$. The pieces may share vertices; BK requires disjoint edges.</p>
<p>Since the events are increasing, these pieces are finite certificates. They give an iterated disjoint occurrence, beginning with the rooted event and followed by $3^{k-1}$ copies of the maximum event. Repeated countable-profile BK gives the rooted inequality in <a href="/tag/JGZB/">JGZB</a>. For the maximum inequality, choose an observed vertex attaining the maximum in the original configuration. Its first piece also witnesses $X\geq\lambda$, so all $3^{k-1}+1$ certificates concern the same maximum event. The choice of root is used to establish event inclusion; there is no union bound over $\Lambda$ and no factor $|\Lambda|$.</p>
<p>The proof works directly with finite certificates on a countable ambient graph. It does not need to pass a quantile through an exhaustion, and permits probability-zero and probability-one coordinates. The condition $k\geq1$, together with $\lambda\geq1$, ensures at least three observed vertices at the splitting step. In particular the root belongs to a non-loop edge of the finite connected witness, even when it lies outside $\Lambda$.</p>
<p>The final source theorem applies the imported numerical implication from amplification to <a href="/tag/C5Q9/">C5Q9</a>. The <a href="/coverage/sources/perclib-22d8485-applications/">twelve-contract inventory</a> covers this BK step in full. Its separate combinatorial splitter and numerical implication remain in the detailed source-reading queue; they are not counted as newly read here. The original tagged properties, strict and non-strict tail conventions, and constants are unchanged. The two related <a href="/errata/hutchcroft-powerlaw-2021/">provisional source errata</a> now record this implementation progress without inferring author confirmation or a reviewed tag association.</p>

## The numerical passage to quantile tails {#section-numerical-source}

<p>The two dependencies mentioned in the preceding source account have now been read in full: the <a href="/articles/finite-set-hyperscaling/#section-greedy-source">connected-edge splitting argument</a> and the numerical implication from <a href="/tag/JGZB/">JGZB</a> to <a href="/tag/C5Q9/">C5Q9</a>. This section describes the latter. Set $p_M=\mathbb P(X\geq M)\leq e^{-1}$. For $a\geq3$, choose $k\geq1$ with $3^k\leq a&lt;3^{k+1}$. Amplification at $\lambda=M$ gives</p>
<div class="math-display">$$\mathbb P(X\geq aM)\leq p_M^{3^{k-1}+1}\leq e^{-a/9},\qquad
\mathbb P(Y_u\geq aM)\leq p_M^{3^{k-1}}\mathbb P(Y_u\geq M)\leq e^{-a/9}\mathbb P(Y_u\geq M).$$</div>
<p>Here $3^{k-1}&gt;a/9$. For $1\leq a&lt;3$, the quantile bound proves the maximum estimate directly, while monotonicity proves the rooted estimate with the stated factor $e^{1-a/9}\geq1$. Combining the ranges gives the constants in C5Q9 without applying amplification at $k=0$.</p>
<p>For the lower tail, put $\lambda=\varepsilon M$. If $\lambda&lt;1$, the event $X&lt;\lambda$ is empty. If $\varepsilon&gt;1/6$, the desired bound is immediate because $27\varepsilon&gt;1$. Otherwise choose $k\geq1$ such that</p>
<div class="math-display">$$3^k\leq\frac1{2\varepsilon}&lt;3^{k+1}.$$</div>
<p>Since $M\geq2$,</p>
<div class="math-display">$$3^k\lambda\leq M/2\leq M-1.$$</div>
<p>The minimality of the integer quantile gives $\mathbb P(X\geq M-1)&gt;e^{-1}$. With $p=\mathbb P(X\geq\lambda)$ and $n=3^{k-1}+1$, amplification therefore yields</p>
<div class="math-display">$$e^{-1}&lt;p^n\leq e^{-n(1-p)}.$$</div>
<p>Thus $n(1-p)&lt;1$. The upper bracket gives $1&lt;18\varepsilon 3^{k-1}\leq18\varepsilon n$, so $1-p\leq27\varepsilon$. Finally $1-p=\mathbb P(X&lt;\varepsilon M)$: the strict lower tail is exactly the complement of the non-strict upper tail, even when $\varepsilon M$ is an integer. No approximation of the quantile is involved.</p>
<p>The <a href="/coverage/sources/perclib-caed44f-tightness/">seven-contract numerical inventory</a> also records the elementary maximum and quantile bounds, measurability of real-threshold events, and the singleton witnesses. Together with the newer BK-step inventory it now traces the source argument through splitting, amplification and quantile estimates. Correspondence with a compiled tag manifest remains a separate check.</p>

## Moments at the quantile scale {#section-moment-source}

<p>Write $Z$ for the largest full-cluster intersection with a nonempty finite observation window, and let $M$ be its integer tightness quantile. Then $Z\geq1$ and $M\geq2$. Minimality of $M$ gives $\mathbb P(Z\geq M-1)&gt;e^{-1}$, so</p>
<div class="math-display">$$\mathbb E Z\geq(M-1)e^{-1}\geq\frac{M}{2e}.$$</div>
<p>This is the lower bound in <a href="/tag/AWWZ/">AWWZ</a>. It uses the definition of the quantile alone, without the amplification or universal-tightness theorem.</p>
<p>For the upper moments, the source uses the maximum-tail part of <a href="/tag/C5Q9/">C5Q9</a>. For every integer $k\geq0$, a layer bound gives</p>
<div class="math-display">$$Z^k\leq M^k+\sum_{j\geq0}((j+2)M)^k\mathbf1_{\{Z\geq(j+1)M\}}.$$</div>
<p>If $Z&lt;M$ the first term suffices. Otherwise the layer with $j=\lfloor Z/M\rfloor-1$ bounds $Z^k$. Integrating the nonnegative sum and applying the tail estimate reduces the problem to</p>
<div class="math-display">$$(j+2)^k e^{-(j+1)/9}\leq k!\,18^k e^{-j/18},\qquad
\sum_{j\geq0}e^{-j/18}\leq19.$$</div>
<p>The first inequality follows from $x^k/k!\leq e^x$ at $x=(j+2)/18$; the second follows from $e^{1/18}\geq1+1/18$. Consequently</p>
<div class="math-display">$$\mathbb E Z^k\leq\bigl(1+19\cdot18^k k!\bigr)M^k\leq20\cdot18^k k!\,M^k.$$</div>
<p>This supplies an explicit choice of the constants in <a href="/tag/2FN1/">2FN1</a>. It even includes $k=0$, with a deliberately loose bound. Countability supplies measurability, and the window is nonempty throughout. The exported higher-moment theorem retains universal tightness as a hypothesis; the later <a href="#section-source-proof">BK-step implementation</a> supplies it on every countable vertex type. No continuity of the quantile, finite susceptibility or restriction of paths to the observation window is used. The <a href="/coverage/sources/perclib-22d8485-moment-tails/">three-contract inventory</a> keeps this dependency separate from the unconditional lower bound.</p>


## Stability from below in a finite model {#section-finite-stability}

<p>For this section allow a finite observation window $\Lambda$ to be empty, setting its maximum $X_\Lambda$ to zero. On a countable ambient graph, for every integer $n\geq0$, the defining quantile satisfies</p>
<div class="math-display">$$M(q,\Lambda)\leq n\quad\Longleftrightarrow\quad\mathbb P_q(X_\Lambda\geq n)\leq e^{-1}.$$</div>
<p>Indeed, $X_\Lambda\leq|\Lambda|$, so the defining set contains $|\Lambda|+1$ and its minimum is attained. Tail monotonicity proves the forward implication, and minimality proves the reverse. Every nonnegative integer threshold below $M$ has tail strictly above $e^{-1}$. In particular $M(q,\varnothing)=1$; for a nonempty window $2\leq M\leq|\Lambda|+1$.</p>
<a id="tag-0SB0" data-assertion="theorem" data-title="Finite-model quantiles are stable under nearby profiles below the endpoint"></a>
<p>Suppose now that the entire vertex set $V$ is finite. For each profile $q$ there is a neighbourhood $U$ of $q$ such that</p>
<div class="math-display">$$p\in U,\quad p\leq q\quad\Longrightarrow\quad M(p,\Lambda)=M(q,\Lambda).$$</div>
<p>Consequently, for finite nonnegative pair intensities and $q_\beta(e)=1-e^{-\beta J_e}$, the quantile is constant sufficiently close to each finite $b\geq0$ from the left, including at $b$. If $b&gt;0$ and $C\in\mathbb R$ satisfies</p>
<div class="math-display">$$\beta M(q_\beta,\Lambda)^2\leq C\qquad(0&lt;\beta&lt;b),$$</div>
<p>then $bM(q_b,\Lambda)^2\leq C$.</p>
<p><em>Proof.</em> The maximum is increasing in the configuration. Ordered coupling and the quantile characterization give $M(p,\Lambda)\leq M(q,\Lambda)$ whenever $p\leq q$. Put $m=M(q,\Lambda)\geq1$. Minimality gives $\mathbb P_q(X_\Lambda\geq m-1)&gt;e^{-1}$. On a finite vertex set this fixed-tail probability is a finite configuration polynomial, hence continuous in the profile. The strict inequality persists on a neighbourhood $U$ of $q$. For $p\in U$ it forces $M(p,\Lambda)&gt;m-1$. Together with the order bound this gives equality.</p>
<p>The intensity family is continuous and nondecreasing, proving local constancy from the left. If $b&gt;0$, there are positive parameters approaching it from below; throughout a sufficiently small left neighbourhood their quantile equals $M(q_b,\Lambda)$. The assumed bound therefore passes to the endpoint by continuity of $\beta\mapsto\beta M(q_b,\Lambda)^2$. No replacement of $M$ by $M-1$ is needed. At $b=0$ the punctured left side has no nonnegative parameters, so it supplies no endpoint-transfer assertion.</p>
<p>Finite ambient vertices, rather than merely a finite observation window, justify the polynomial step. Full-cluster intersections may use paths outside the window. For the internal hierarchical block in <a href="/tag/2XJX/">2XJX</a>, apply this theorem with that finite block as the entire vertex set. It supplies the endpoint passage, not the estimate below the endpoint.</p>
<p>Two-sided continuity is false already for two vertices with their connecting bond open with probability $p$, taking the whole graph as the window. The quantile is two for $p\leq e^{-1}$ and three for $p&gt;e^{-1}$. This is the <a href="/errata/hutchcroft-hierarchical-2021/">quantile-continuity discrepancy recorded in the errata</a>; the one-sided replacement and its Lean implementation remain recorded there with provisional source status. The <a href="/sources/perclib-finite-quantile/">source module</a> proves the stability and endpoint transfer, including empty and singleton witnesses. For a singleton window the maximum is always one and the quantile is two, regardless of the ambient profile.</p>


## Retaining the mean below a quantile-scale cap {#section-capped-mean-source}

<p>Let $X=|K_u\cap\Lambda|$, where the ambient vertex set is countable and the observation window $\Lambda$ is finite and nonempty. Write $M\geq2$ for its largest-intersection quantile and $\mu=\mathbb E X$. The <a href="/coverage/sources/perclib-dfbc5b4-moments-ghost/">truncated-mean source</a> proves</p>
<div class="math-display">$$\mathbb E\min\{X,99M\}\geq\frac\mu2,\qquad
\mathbb E\min\{X,t\}\geq\frac12\min\left\{1,\frac{t}{99M}\right\}\mu\quad(t\geq0).$$</div>
<p>Indeed, rooted damping bounds the excess mean by</p>
<div class="math-display">$$\mathbb E(X-99M)_+=\sum_{k\geq0}\mathbb P(X\geq99M+k+1)
\leq9M e^{-10}\mathbb P(X\geq M)\leq9e^{-10}\mu&lt;\frac\mu2.$$</div>
<p>Here the geometric sum is at most $9M$, and Markov's inequality supplies the last factor of $\mu$. Subtracting the excess proves the first bound. The second follows from $\min\{x,t\}\geq\min\{1,t/(99M)\}\min\{x,99M\}$. These are expectations of capped variables; an indicator truncation would be a different quantity.</p>
<p>The same source gives $M^2/(4e)\leq\sum_{v\in\Lambda}\mathbb E|K_v\cap\Lambda|$ from partition counting. Reducing this sum to $|\Lambda|\mathbb E|K_u\cap\Lambda|$ requires law-preserving bijections that also preserve $\Lambda$ and carry $u$ to every vertex of $\Lambda$. Transitivity of the ambient model alone does not preserve an arbitrary fixed window. The capped-mean estimates need no such symmetry and allow the chosen root outside the window.</p>
