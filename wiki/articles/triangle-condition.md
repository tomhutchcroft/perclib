---
{
  "id": "triangle-condition",
  "title": "The triangle condition",
  "subtitle": "A diagrammatic criterion for mean-field volume behaviour.",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A summability condition on three two-point functions controls several critical exponents. The criterion and the model-dependent proof of the criterion are separate mathematical results.",
  "context": [
    "Independent nearest-neighbour bond percolation on $\\mathbb Z^d$, with $d\\ge2$.",
    "The triangle diagram is evaluated at the infinite-volume critical parameter p_c.",
    "The notation f ≍ g means upper and lower bounds by positive constants in the stated regime."
  ],
  "related": [
    "sharpness",
    "exploration",
    "hierarchical-two-point",
    "cutoff-families"
  ],
  "sourceIds": [
    "hutchcroft-triangle-2021",
    "heydenreich-hofstad",
    "hutchcroft-book"
  ],
  "aliases": [
    "triangle diagram",
    "mean-field exponents",
    "mean field",
    "critical cluster-volume exponent",
    "Aizenman–Newman"
  ],
  "prototypeUses": [
    "product-model",
    "connectivity",
    "susceptibility",
    "criticality"
  ]
}
---

## The diagram {#section-diagram}

<a id="tag-67VP" data-assertion="definition" data-title="Triangle diagram"></a><p>For the <a href="#/product-model">independent lattice model</a>, write $\tau_p(x,y)=\mathbb P_p(x\leftrightarrow y)$ for the <a href="#/connectivity">two-point function</a>. The rooted triangle diagram is the nonnegative, possibly infinite sum</p>
      $$\nabla_p=\sum_{x,y\in\mathbb Z^d}\tau_p(0,x)\,\tau_p(x,y)\,\tau_p(y,0).$$
      <a id="tag-7UDJ" data-assertion="definition" data-title="Critical triangle condition"></a><p>The <strong>triangle condition</strong> is $\nabla_{p_c}&lt;\infty$, evaluated at the <a href="#/criticality">critical parameter</a>. Each factor records a connection along one side of a triangle. Summing over its two free vertices measures how strongly three connections can interact across all scales.</p>
      <p>The same formula defines the triangle diagram on any countable graph with a root.</p>

## A conditional mean-field theorem {#section-consequences}

<a id="tag-2ZI0" data-assertion="theorem" data-title="Mean-field estimates under the triangle condition"></a><div class="theorem-statement"><p>Assume that the critical triangle diagram is finite: $\nabla_{p_c}&lt;\infty$. Then</p>
      $$\chi(p)\asymp(p_c-p)^{-1}\quad\text{as }p\uparrow p_c,$$
      $$\mathbb P_{p_c}(|K_0|\ge n)\asymp n^{-1/2}\quad(n\ge1),$$
      $$\theta(p)\asymp p-p_c\quad\text{as }p\downarrow p_c.$$</div>
<p><em>Idea of the proof of the susceptibility estimate.</em> Two differential inequalities for the <a href="/articles/susceptibility/">susceptibility</a> $\chi(p)=\mathbb E_p|K_0|$ on $[0,p_c)$ are integrated up to $p_c$, where $\chi(p_c)=\infty$ by <a href="/tag/JQLC/">sharpness of the bond transition</a>. Differentiating a connection probability exposes pivotal edges: <a href="/articles/russo-formula/">Russo's formula</a> and the <a href="/articles/bk-inequality/">BK inequality</a> give $\chi'\le2d\chi^2$, hence $\chi(p)\ge(2d(p_c-p))^{-1}$ with no triangle assumption, which is the <a href="/tag/8ZGG/">reciprocal Lipschitz bound</a>. The triangle condition enters through the reverse inequality $\chi'\ge c\chi^2$ near $p_c$. The derivative $\chi'(p)$ is at least the expected number of vertices reached from the outer boundary of the root cluster while avoiding the cluster; Cauchy–Schwarz over the cluster, the <a href="/articles/tree-graph/">tree-graph inequalities</a> and a Fourier comparison of diagrams bound this below by $(\chi-\nabla_p)^2/(6dp^2\nabla_p^2)$, which is at least $\chi^2/(24d\nabla_{p_c}^2)$ once $\chi\ge2\nabla_{p_c}$, since $p\le1$ and $\nabla_p\le\nabla_{p_c}$.</p>
:::details Proof of the susceptibility estimate
<p><em>Step 0 (setting).</em> By the <a href="/tag/NUJY/">Peierls bound</a>, $0&lt;p_c&lt;1$. By <a href="/tag/JQLC/">sharpness of the bond transition</a>, $\chi(p)&lt;\infty$ for $0\le p&lt;p_c$ and $\chi(p_c)=\infty$. Write $\tau(z)=\tau_p(0,z)$ when $p$ is fixed. Translation invariance and symmetry of connection give $\tau_p(x,y)=\tau(y-x)$ and $\tau(-z)=\tau_p(z,0)=\tau(z)$, so $\sum_w\tau_p(u,w)=\chi(p)$ for every $u$ (<a href="/tag/8DSI/">two-point sum identity</a>). By the <a href="/tag/2ML7/">monotone coupling</a>, every $\tau_p(x,y)$ is nondecreasing in $p$, hence so are $\chi(p)$ and $\nabla_p$. For $p&lt;p_c$, $\tau\in\ell^1(\mathbb Z^d)$, and since $\tau\le1$ all diagrams below are finite; for instance $\nabla_p\le\chi(p)^2$. All terms in all sums are nonnegative, so sums may be rearranged.</p>
<p><em>Step 1 (finite-volume derivative bound).</em> Let $\Lambda_n=[-n,n]^d\cap\mathbb Z^d$, let $E_n$ be the set of edges with both endpoints in $\Lambda_n$, and put $\chi_n(p)=\sum_{x\in\Lambda_n}\tau^{\Lambda_n}_p(0,x)$, where $\tau^{\Lambda_n}_p(0,x)=\mathbb P_p(0\xleftrightarrow{\Lambda_n}x)$ is the probability of an open path from $0$ to $x$ using only edges of $E_n$. The event $A_{n,x}=\{0\xleftrightarrow{\Lambda_n}x\}$ is increasing and depends on finitely many edges, so $\chi_n$ is a polynomial and, by the <a href="/tag/4IHK/">homogeneous Russo formula</a>,</p>
<div class="math-display">$$\frac{d}{dp}\tau^{\Lambda_n}_p(0,x)=\sum_{e\in E_n}\mathbb P_p(e\text{ is pivotal for }A_{n,x}),$$</div>
<p>where $e$ is pivotal for an increasing event $A$ in $\omega$ when $\omega\cup\{e\}\in A$ and $\omega\setminus\{e\}\notin A$. Suppose $e$ is pivotal for $A_{n,x}$ in $\omega$. Then $\omega\cup\{e\}$ contains an open path from $0$ to $x$ with edges in $E_n$ and $\omega\setminus\{e\}$ contains none, so every such path uses $e$. A self-avoiding one crosses $e$ once, from an endpoint $u$ to the other endpoint $v$; its parts before and after $e$ are open paths of $\omega\setminus\{e\}$ inside $\Lambda_n$ from $0$ to $u$ and from $v$ to $x$, with disjoint edge sets. Hence $\omega\in\{0\xleftrightarrow{\Lambda_n}u\}\circ\{v\xleftrightarrow{\Lambda_n}x\}$ for one of the two orientations $(u,v)$ of $e$. The <a href="/tag/JRCI/">BK inequality</a> and $\tau^{\Lambda_n}_p\le\tau_p$ give $\mathbb P_p(e\text{ is pivotal for }A_{n,x})\le\sum_{(u,v)}\tau_p(0,u)\tau_p(v,x)$, the sum running over the two orientations of $e$. Summing over $e\in E_n$ and $x\in\Lambda_n$, and enlarging the sums to all oriented nearest-neighbour pairs and all $x\in\mathbb Z^d$,</p>
<div class="math-display">$$\chi_n'(p)\le\sum_{u\in\mathbb Z^d}\tau_p(0,u)\sum_{v\sim u}\sum_{x\in\mathbb Z^d}\tau_p(v,x)=2d\,\chi(p)^2\qquad(0\le p\le1).\tag{1}$$</div>
<p><em>Step 2 (regularity and the lower bound).</em> Since $\Lambda_n\uparrow\mathbb Z^d$, <a href="/tag/5UJQ/">connectivity under exhaustion</a> gives $\tau^{\Lambda_n}_p(0,x)\uparrow\tau_p(0,x)$, and monotone convergence gives $\chi_n(p)\uparrow\chi(p)$. Each $\chi_n$ is continuous and, by the monotone coupling, nondecreasing.</p>
<p>(a) For $0\le p&lt;q&lt;p_c$, integrating (1) over $[p,q]$ and using that $\chi$ is nondecreasing gives $\chi_n(q)-\chi_n(p)\le2d(q-p)\chi(q)^2$. Letting $n\to\infty$, with every term finite,</p>
<div class="math-display">$$0\le\chi(q)-\chi(p)\le2d(q-p)\chi(q)^2\qquad(0\le p&lt;q&lt;p_c).\tag{2}$$</div>
<p>Thus, for each $r&lt;p_c$, $\chi$ is Lipschitz on $[0,r]$ with constant $2d\chi(r)^2$. Since $\chi\ge1$, $|1/\chi(q)-1/\chi(p)|\le|\chi(q)-\chi(p)|$, so $1/\chi$ is Lipschitz there too. A Lipschitz function on an interval is absolutely continuous: it is differentiable almost everywhere and is the integral of its derivative. Where $\chi$ is differentiable, so is $1/\chi$, with derivative $-\chi'/\chi^2$.</p>
<p>(b) At a point $p\in[0,p_c)$ where $\chi$ is differentiable, (2) and continuity of $\chi$ give $\chi'(p)=\lim_{q\downarrow p}(\chi(q)-\chi(p))/(q-p)\le2d\chi(p)^2$, so $(1/\chi)'(p)\ge-2d$. Integrating over $[p,q]$,</p>
<div class="math-display">$$\frac1{\chi(p)}\le\frac1{\chi(q)}+2d(q-p)\qquad(0\le p&lt;q&lt;p_c).\tag{3}$$</div>
<p>(c) The limit $\lim_{q\uparrow p_c}\chi(q)$ exists by monotonicity. For each $n$, $\chi(q)\ge\chi_n(q)$ and $\chi_n$ is continuous, so the limit is at least $\chi_n(p_c)$. Letting $n\to\infty$, it is at least $\chi(p_c)=\infty$.</p>
<p>(d) Letting $q\uparrow p_c$ in (3) and using (c),</p>
<div class="math-display">$$\chi(p)\ge\frac1{2d(p_c-p)}\qquad(0\le p&lt;p_c).\tag{L}$$</div>
<p><em>Step 3 (a one-sided Russo inequality).</em> Let $A$ be an increasing event, which may depend on infinitely many edges, let $0\le p&lt;p+\varepsilon\le1$, and let $F$ be a finite set of edges. Realize all parameters together by independent uniform variables $(U_e)$, with $\omega_s=\{e:U_e\le s\}$. As $\omega_p\subseteq\omega_{p+\varepsilon}$, $\mathbb P_{p+\varepsilon}(A)-\mathbb P_p(A)=\mathbb P(\omega_{p+\varepsilon}\in A,\ \omega_p\notin A)$. For $e\in F$ let $G_e$ be the event that $U_e\in(p,p+\varepsilon]$, that $e$ is pivotal for $A$ in $\omega_p$, and that $U_f\notin(p,p+\varepsilon]$ for every $f\in F\setminus\{e\}$. On $G_e$, $e\notin\omega_p$, so $\omega_p=\omega_p\setminus\{e\}\notin A$, while $\omega_{p+\varepsilon}\supseteq\omega_p\cup\{e\}\in A$, so $\omega_{p+\varepsilon}\in A$. The events $G_e$, $e\in F$, are pairwise disjoint. Pivotality of $e$ in $\omega_p$ is a function of $(U_f)_{f\ne e}$, hence independent of $U_e$, and so</p>
<div class="math-display">$$\mathbb P(G_e)\ge\varepsilon\,\mathbb P_p(e\text{ is pivotal for }A)-\mathbb P\bigl(U_e\in(p,p+\varepsilon],\ U_f\in(p,p+\varepsilon]\text{ for some }f\in F\setminus\{e\}\bigr)\ge\varepsilon\,\mathbb P_p(e\text{ is pivotal for }A)-\varepsilon^2|F|.$$</div>
<p>Summing over $e\in F$, dividing by $\varepsilon$ and letting $\varepsilon\downarrow0$, then letting $F$ increase,</p>
<div class="math-display">$$\liminf_{\varepsilon\downarrow0}\frac{\mathbb P_{p+\varepsilon}(A)-\mathbb P_p(A)}{\varepsilon}\ge\sum_e\mathbb P_p(e\text{ is pivotal for }A).\tag{4}$$</div>
<p><em>Step 4 (the derivative as a boundary sum).</em> For a finite set $S\subset\mathbb Z^d$, let $\vec\partial S$ be the set of ordered pairs $(a,b)$ of neighbours with $a\in S$ and $b\notin S$; write $b\leftrightarrow w$ off $S$ when an open path from $b$ to $w$ has no vertex in $S$; and put</p>
<div class="math-display">$$\Psi_p(S)=\sum_{(a,b)\in\vec\partial S}\ \sum_{w\in\mathbb Z^d}\mathbb P_p(b\leftrightarrow w\text{ off }S).$$</div>
<p>Let $0&lt;p&lt;p_c$ be a point where $\chi$ is differentiable. The differences $\tau_{p+\varepsilon}(0,x)-\tau_p(0,x)$ are nonnegative, so Fatou's lemma for sums and (4) applied to $A=\{0\leftrightarrow x\}$ give</p>
<div class="math-display">$$\chi'(p)\ge\sum_x\sum_e\mathbb P_p(e\text{ is pivotal for }\{0\leftrightarrow x\})=\frac1{1-p}\sum_x\sum_e\mathbb P_p(e\text{ is closed and pivotal for }\{0\leftrightarrow x\}),$$</div>
<p>where the equality holds because pivotality of $e$ does not depend on the state of $e$, which is closed with probability $1-p$. Write $K=K_0$. The edge $e$ is closed and pivotal for $\{0\leftrightarrow x\}$ exactly when, for one orientation $(a,b)$ of $e$, $a\in K$, $b\notin K$ and $b\leftrightarrow x$ off $K$. Indeed, if $e$ is closed and pivotal, $0\not\leftrightarrow x$ and $\omega\cup\{e\}$ has a self-avoiding open path from $0$ to $x$ through $e$, say from $a$ to $b$; its part before $e$ shows $a\in K$, and its part after $e$ is open in $\omega$ and avoids $K$, since otherwise $x\in K$. Conversely, the three conditions force $e$ to be closed (else $b\in K$) and $x\notin K$, while $\omega\cup\{e\}$ joins $0$ to $a$, $a$ to $b$ and $b$ to $x$. The orientation is unique, as exactly one endpoint lies in $K$. Since $\chi(p)&lt;\infty$, $K$ is finite almost surely (<a href="/tag/INZI/">finite expectation implies finiteness</a>). For a finite $S\ni0$, the event $\{K=S\}$ is determined by the edges with an endpoint in $S$, and $\{b\leftrightarrow x\text{ off }S\}$ by the edges with no endpoint in $S$, so they are independent. Therefore</p>
<div class="math-display">$$\sum_x\sum_e\mathbb P_p(e\text{ is closed and pivotal for }\{0\leftrightarrow x\})=\sum_{S}\ \sum_{(a,b)\in\vec\partial S}\ \sum_x\mathbb P_p(K=S,\ b\leftrightarrow x\text{ off }S)=\mathbb E_p\bigl[\Psi_p(K)\bigr],$$</div>
<div class="math-display">$$\chi'(p)\ge\frac1{1-p}\,\mathbb E_p\bigl[\Psi_p(K)\bigr]\ge\mathbb E_p\bigl[\Psi_p(K)\bigr].\tag{5}$$</div>
<p><em>Step 5 (the boundary inequality).</em> Let $0&lt;p&lt;p_c$ and let $S$ be finite and nonempty. Put</p>
<div class="math-display">$$X_S=\sum_{u\in S}\sum_{w\notin S}\tau_p(u,w),\qquad Y_S=\sum_{a,b,c\in S}\tau_p(a,b)\tau_p(a,c).$$</div>
<p>Let $u\in S$, $w\notin S$, and suppose $u\leftrightarrow w$. A self-avoiding open path $\gamma$ from $u$ to $w$ leaves $S$ for the last time along some $(a,b)\in\vec\partial S$. The parts of $\gamma$ before and after this edge, and the edge itself, are disjoint finite witnesses for $\{u\leftrightarrow a\}$ (the empty path if $a=u$), $\{\{a,b\}\text{ open}\}$ and $\{b\leftrightarrow w\text{ off }S\}$. A union bound and the <a href="/tag/AUUG/">BK inequality for three events</a> give</p>
<div class="math-display">$$\tau_p(u,w)\le p\sum_{(a,b)\in\vec\partial S}\tau_p(u,a)\,\mathbb P_p(b\leftrightarrow w\text{ off }S).$$</div>
<p>Sum over $u\in S$ and $w\notin S$, and set $g(a)=\sum_{u\in S}\tau_p(u,a)$ and $f(a)=\sum_{b:(a,b)\in\vec\partial S}\sum_{w}\mathbb P_p(b\leftrightarrow w\text{ off }S)$ for $a\in S$; a path off $S$ ends outside $S$, so extending the sum to all $w$ adds nothing. Then $X_S\le p\sum_{a\in S}g(a)f(a)$, $\sum_{a\in S}f(a)=\Psi_p(S)$, $f(a)\le\sum_{b\sim a}\sum_w\tau_p(b,w)=2d\chi(p)$, and $\sum_{a\in S}g(a)^2=Y_S$ by symmetry of $\tau_p$. The Cauchy–Schwarz inequality gives</p>
<div class="math-display">$$X_S^2\le p^2\sum_{a\in S}g(a)^2\sum_{a\in S}f(a)^2\le p^2\,Y_S\cdot2d\chi(p)\,\Psi_p(S).\tag{6}$$</div>
<p><em>Step 6 (moments over the cluster).</em> Fix $0&lt;p&lt;p_c$, let $X=X_K$ and $Y=Y_K$, and let $\tau_2=\tau*\tau$ and $\tau_3=\tau*\tau*\tau$ be convolutions on $\mathbb Z^d$; they are even, nonnegative and summable. Since $\sum_w\tau_p(u,w)=\chi$, $X=\chi|K|-\sum_{u,v\in K}\tau_p(u,v)\ge0$, and $Y\ge\tau_p(0,0)^2=1$. By the <a href="/tag/L82Q/">three-point tree-graph inequality</a> and translation invariance,</p>
<div class="math-display">$$\mathbb E_p\sum_{u,v\in K}\tau_p(u,v)=\sum_{u,v}\mathbb P_p(0\leftrightarrow u,\ 0\leftrightarrow v)\tau_p(u,v)\le\sum_{w}\tau(w)\sum_{u,v}\tau_p(w,u)\tau_p(w,v)\tau_p(u,v)=\chi\nabla_p,$$</div>
<p>so $\mathbb E_pX\ge\chi^2-\chi\nabla_p$, using $\mathbb E_p|K|=\chi$. For $Y$, apply the <a href="/tag/AFH6/">multipoint tree-graph inequality</a> with the four marked vertices $0,a,b,c$. A trivalent tree with four labelled leaves has two internal vertices $z,z'$ joined by an edge, $z$ adjacent to $0$ and one of $a,b,c$, and $z'$ adjacent to the other two; there are three such trees. The tree pairing $0$ with $a$ contributes, after multiplying by $\tau_p(a,b)\tau_p(a,c)$, summing over $a,b,c,z,z'$ and translating by $-z$,</p>
<div class="math-display">$$\chi\sum_{a,b,c,z'}\tau(a)\tau(z')\tau(b-z')\tau(c-z')\tau(b-a)\tau(c-a)=\chi\sum_{a,z'}\tau(a)\tau(z')\tau_2(a-z')^2=\chi\sum_y\tau_2(y)^3=:\chi B_p,$$</div>
<p>where the sums over $b$ and $c$ each give $\tau_2(a-z')$, and with $y=a-z'$ the sum over $z'$ gives $\tau_2(y)$. The tree pairing $0$ with $b$ contributes</p>
<div class="math-display">$$\chi\sum_{a,b,c,z'}\tau(b)\tau(z')\tau(a-z')\tau(c-z')\tau(b-a)\tau(c-a)=\chi\sum_{a,z'}\tau(z')\tau(a-z')\tau_2(a-z')\tau_2(a)=\chi\sum_y\tau(y)\tau_2(y)\tau_3(y)=:\chi A_p,$$</div>
<p>since the sum over $c$ gives $\tau_2(a-z')$, the sum over $b$ gives $\tau_2(a)$, and with $y=a-z'$ the sum over $z'$ gives $\tau_3(y)$. The tree pairing $0$ with $c$ contributes $\chi A_p$ by the symmetry $b\leftrightarrow c$. Hence</p>
<div class="math-display">$$\mathbb E_pY=\sum_{a,b,c}\mathbb P_p(a,b,c\in K)\tau_p(a,b)\tau_p(a,c)\le\chi\,(2A_p+B_p).$$</div>
<p><em>Step 7 (diagram comparison).</em> First, $\tau_3(y)=\sum_{u,v}\tau_p(0,u)\tau_p(u,v)\tau_p(v,y)\le\nabla_p$ for every $y$, by the <a href="/tag/UZ7J/">cubic connection bound</a> for the translation-invariant kernel; and $\sum_y\tau(y)\tau_2(y)=\tau_3(0)=\nabla_p$. Hence $A_p\le\nabla_p^2$.</p>
<p>Next, $B_p\le A_p$. Let $\mu$ be normalized Lebesgue measure on $\mathbb T^d=(-\pi,\pi]^d$, with addition modulo $2\pi$, and for $h\in\ell^1(\mathbb Z^d)$ let $\hat h(\theta)=\sum_xh(x)e^{i\theta\cdot x}$. Then $\hat\tau$ is continuous and real, since $\tau$ is even, and $\widehat{\tau_2}=\hat\tau^2$, $\widehat{\tau_3}=\hat\tau^3$. Moreover $\hat\tau\ge0$: for fixed $\theta$, <a href="/tag/70KD/">positive semidefiniteness of the connection kernel</a>, applied to the coefficients $\cos(\theta\cdot x)\mathbf1_{\Lambda_n}(x)$ and to $\sin(\theta\cdot x)\mathbf1_{\Lambda_n}(x)$ and added, gives</p>
<div class="math-display">$$0\le\frac1{|\Lambda_n|}\sum_{x,y\in\Lambda_n}\tau(y-x)\cos(\theta\cdot(y-x))=\sum_z\tau(z)\cos(\theta\cdot z)\frac{|\Lambda_n\cap(\Lambda_n-z)|}{|\Lambda_n|}\longrightarrow\hat\tau(\theta)$$</div>
<p>by dominated convergence, the ratios lying in $[0,1]$ and tending to $1$. For $f,g,h\in\ell^1(\mathbb Z^d)$, expanding the transforms and integrating the absolutely convergent triple series term by term, with $\int e^{i\varphi\cdot(x-z)}\mu(d\varphi)=\mathbf1_{\{x=z\}}$, gives</p>
<div class="math-display">$$\sum_xf(x)g(x)h(x)=\iint\hat f(\varphi)\hat g(\psi)\hat h(-\varphi-\psi)\,\mu(d\varphi)\mu(d\psi).$$</div>
<p>With $G=\hat\tau$, which is even and nonnegative, this yields</p>
<div class="math-display">$$B_p=\iint G(\psi)^2\,G(\varphi)^2G(\varphi+\psi)^2\,\mu(d\varphi)\mu(d\psi),\qquad A_p=\iint G(\psi)^2\,G(\varphi)G(\varphi+\psi)^3\,\mu(d\varphi)\mu(d\psi),$$</div>
<p>taking $(f,g,h)=(\tau_2,\tau_2,\tau_2)$ and $(\tau,\tau_2,\tau_3)$. For fixed $\psi$, the arithmetic–geometric mean inequality gives $G(\varphi)^2G(\varphi+\psi)^2\le\frac12[G(\varphi)G(\varphi+\psi)^3+G(\varphi)^3G(\varphi+\psi)]$. The substitution $\varphi\mapsto-\varphi-\psi$ preserves $\mu$ and, since $G$ is even, turns $G(\varphi)^3G(\varphi+\psi)$ into $G(\varphi+\psi)^3G(\varphi)$. So $\int G(\varphi)^2G(\varphi+\psi)^2\mu(d\varphi)\le\int G(\varphi)G(\varphi+\psi)^3\mu(d\varphi)$; multiplying by $G(\psi)^2\ge0$ and integrating over $\psi$ gives $B_p\le A_p$. Consequently</p>
<div class="math-display">$$2A_p+B_p\le3\nabla_p^2.\tag{7}$$</div>
<p><em>Step 8 (the differential inequality).</em> Let $0&lt;p&lt;p_c$ be a point where $\chi$ is differentiable and $\chi(p)\ge\nabla_p$. By (5) and (6), $\chi'(p)\ge\mathbb E_p[X^2/Y]/(2dp^2\chi)$. By Step 6 and (7), $\mathbb E_pY\le3\chi\nabla_p^2&lt;\infty$, and $\mathbb E_pX\ge\chi(\chi-\nabla_p)\ge0$. The Cauchy–Schwarz inequality $(\mathbb E_pX)^2=(\mathbb E_p[(X/\sqrt Y)\sqrt Y])^2\le\mathbb E_p[X^2/Y]\,\mathbb E_pY$ then gives</p>
<div class="math-display">$$\chi'(p)\ge\frac{(\mathbb E_pX)^2}{2dp^2\chi\,\mathbb E_pY}\ge\frac{\chi^2(\chi-\nabla_p)^2}{2dp^2\chi\cdot3\chi\nabla_p^2}=\frac{(\chi(p)-\nabla_p)^2}{6dp^2\nabla_p^2}.\tag{8}$$</div>
<p><em>Step 9 (the upper bound).</em> Put $D=\nabla_{p_c}$, finite by hypothesis. By Step 0, $\nabla_p\le D$ for $p\le p_c$, and $D\ge\nabla_0=1$. Let $p_1&lt;p_c$ satisfy $\chi(p_1)\ge2D$; such a $p_1$ exists by Step 2(c), and $p_1&gt;0$ because $\chi(0)=1&lt;2D$. Then $\chi(p)\ge2D\ge2\nabla_p$ for $p\in[p_1,p_c)$. At almost every such $p$, (8) applies; since $\chi-\nabla_p\ge\chi/2$, $\nabla_p\le D$ and $p\le1$,</p>
<div class="math-display">$$\chi'(p)\ge\frac{\chi(p)^2}{24d\,D^2},\qquad\text{so}\qquad\Bigl(\frac1\chi\Bigr)'(p)\le-\frac1{24dD^2}.$$</div>
<p>For $p_1\le p&lt;q&lt;p_c$, $1/\chi$ is Lipschitz on $[p,q]$ by Step 2(a), so integrating gives $1/\chi(p)\ge1/\chi(q)+(q-p)/(24dD^2)\ge(q-p)/(24dD^2)$. Letting $q\uparrow p_c$ and combining with (L) gives, for $p_1\le p&lt;p_c$,</p>
<div class="math-display">$$\frac1{2d\,(p_c-p)}\le\chi(p)\le\frac{24d\,\nabla_{p_c}^2}{p_c-p}.$$</div>
:::
<p>The proof gives the upper bound in an explicit form, from which the two proofs below start. By the <a href="/tag/NUJY/">Peierls bound</a>, $0&lt;p_c&lt;1$. By the lower bound, $\chi(p)\to\infty$ as $p\uparrow p_c$, so there is a parameter $p_1&lt;p_c$ with $\chi(p_1)\ge2\nabla_{p_c}$; then $p_1&gt;0$, because $\chi(0)=1&lt;2\le2\nabla_{p_c}$. For every such $p_1$,</p>
<div class="math-display">$$\chi(p)\le\frac{24d\,\nabla_{p_c}^2}{p_c-p}\qquad(p_1\le p&lt;p_c).\tag{U}$$</div>
<p><em>Idea of the proof of the critical tail estimate.</em> The <a href="/tag/JL1S/">entropy comparison of cluster tails</a> bounds $\mathbb P_{p_c}(|K_0|\ge n)$ by the susceptibility at a smaller parameter $q$, at a cost of order $1/n+(p_c-q)^2$. Taking $p_c-q=n^{-1/2}$ and inserting (U) gives the upper bound $O(n^{-1/2})$. For the lower bound, the <a href="/tag/36PN/">universal integrated critical tail</a> $\mathbb E_{p_c}[|K_0|\wedge N]\ge\sqrt N/(2\sqrt2)$ holds on every transitive graph, with no triangle condition. Given the pointwise upper bound, the <a href="/tag/MBV2/">pointwise lower-tail lemma</a> turns it into $\mathbb P_{p_c}(|K_0|\ge n)\ge c\,n^{-1/2}$.</p>
:::details Proof of the critical tail estimate
<p><em>Step 0 (input).</em> Let $D=\nabla_{p_c}$, and let $p_1\in(0,p_c)$ be as in (U), so that $\chi(p)\le24dD^2/(p_c-p)$ for $p_1\le p&lt;p_c$. Recall $0&lt;p_c&lt;1$.</p>
<p><em>Step 1 (intensity parameter).</em> The cluster-tail comparison and the universal integrated tail are stated for models with edge intensities, so the bond parameter is converted into an intensity. For $0\le p&lt;1$ put $\beta(p)=-\log(1-p)$, an increasing bijection from $[0,1)$ onto $[0,\infty)$. Give each nearest-neighbour edge of $\mathbb Z^d$ weight $J_e=1$. The independent law in which each edge is open with probability $1-e^{-\beta J_e}$ is then $\mathbb P_p$ with $p=1-e^{-\beta}$. Every vertex lies on exactly $2d$ edges, so the weights at each vertex sum to $2d$, and the translations of $\mathbb Z^d$ act transitively and preserve the weights. For $0\le q&lt;p&lt;1$, the inequalities $\log(1+x)\le x$ for $x\ge0$ and $-\log(1-x)\ge x$ for $0\le x&lt;1$ give</p>
<div class="math-display">$$\beta(p)-\beta(q)=\log\Bigl(1+\frac{p-q}{1-p}\Bigr)\le\frac{p-q}{1-p},\qquad\beta(q)\ge q.\tag{E}$$</div>
<p>Write $\theta(p)=\mathbb P_p(|K_0|=\infty)$ for the <a href="/articles/criticality/">percolation probability</a>. The percolation probability at intensity $\beta$ is $\theta(1-e^{-\beta})$, $\theta$ is nondecreasing by the <a href="/tag/2ML7/">monotone coupling</a>, and $\beta\mapsto1-e^{-\beta}$ is increasing. Hence the critical intensity $\beta_c=\inf\{\beta\ge0:\theta(1-e^{-\beta})&gt;0\}$ equals $\beta(p_c)$, which is finite because $p_c&lt;1$.</p>
<p><em>Step 2 (upper bound).</em> Let $p_1\le q&lt;p_c$. Then $0&lt;q\le\beta(q)&lt;\beta(p_c)$ and $\chi(q)&lt;\infty$. The second inequality of the <a href="/tag/JL1S/">cluster-tail comparison</a>, applied in the model of Step 1 with weight bound $M=2d$, $\beta_1=\beta(q)$ and $\beta_2=\beta(p_c)$, followed by (E) with $p=p_c$, gives for every integer $n\ge1$</p>
<div class="math-display">$$\mathbb P_{p_c}(|K_0|\ge n)\le\Bigl(\frac2n+\frac{8d\,(\beta(p_c)-\beta(q))^2}{\beta(q)}\Bigr)\chi(q)\le\Bigl(\frac2n+\frac{8d\,(p_c-q)^2}{q\,(1-p_c)^2}\Bigr)\chi(q).$$</div>
<p>Let $N_0=\lceil(p_c-p_1)^{-2}\rceil$. For $n\ge N_0$ take $q=p_c-n^{-1/2}$; since $n^{-1/2}\le p_c-p_1$, it satisfies $p_1\le q&lt;p_c$. Then $(p_c-q)^2=1/n$, $q\ge p_1$, and $\chi(q)\le24dD^2n^{1/2}$ by (U), so</p>
<div class="math-display">$$\mathbb P_{p_c}(|K_0|\ge n)\le\Bigl(\frac2n+\frac{8d}{n\,p_1(1-p_c)^2}\Bigr)24dD^2n^{1/2}=24dD^2\Bigl(2+\frac{8d}{p_1(1-p_c)^2}\Bigr)n^{-1/2}\qquad(n\ge N_0).$$</div>
<p>For $1\le n&lt;N_0$, $\mathbb P_{p_c}(|K_0|\ge n)\le1\le(N_0/n)^{1/2}$. Therefore, putting</p>
<div class="math-display">$$C_+=\max\Bigl\{N_0^{1/2},\ 24dD^2\Bigl(2+\frac{8d}{p_1(1-p_c)^2}\Bigr)\Bigr\}\ge1,\qquad\text{we have}\qquad\mathbb P_{p_c}(|K_0|\ge n)\le C_+n^{-1/2}\quad(n\ge1).\tag{T}$$</div>
<p><em>Step 3 (lower bound).</em> Extend the weights of Step 1 to all pairs by $J(x,y)=1$ when $x$ and $y$ are neighbours and $J(x,y)=0$ for all other pairs $x\ne y$. An edge of weight zero is closed almost surely, so the cluster of $0$ has the same law as in Step 1. This model satisfies the hypotheses of the <a href="/tag/36PN/">universal integrated critical tail</a>: the vertex set $\mathbb Z^d$ is countable, the weights are symmetric, finite, nonnegative and preserved by the transitive translation group, $L=\sum_{y\ne0}J(0,y)=2d\in(0,\infty)$, and $\beta_c=\beta(p_c)&lt;\infty$. With $T=|K_0|$ under $\mathbb P_{p_c}$, allowing $T=\infty$, its first conclusion is $\mathbb E_{p_c}[T\wedge N]\ge\sqrt N/(2\sqrt2)$ for every integer $N\ge1$. The <a href="/tag/CSY8/">tail-sum identity</a> applied to the variable $T\wedge N$, for which $\mathbb P(T\wedge N\ge k)$ equals $\mathbb P(T\ge k)$ when $k\le N$ and $0$ when $k&gt;N$, gives</p>
<div class="math-display">$$\sum_{k=1}^N\mathbb P_{p_c}(|K_0|\ge k)=\mathbb E_{p_c}[T\wedge N]\ge\frac{\sqrt N}{2\sqrt2}\qquad(N\ge1).$$</div>
<p>The sequence $\mathbb P_{p_c}(|K_0|\ge k)$, $k\ge1$, is nonnegative and nonincreasing. Apply the <a href="/tag/MBV2/">pointwise lower-tail lemma</a> with $c=1/(2\sqrt2)$, with $C=C_+$ from (T), with threshold $N_0=1$ there, and with $A=\lceil128C_+^2\rceil$; then $A\ge128\ge2$ and $c\sqrt A\ge c\cdot8\sqrt2\,C_+=4C_+$. It gives</p>
<div class="math-display">$$\mathbb P_{p_c}(|K_0|\ge n)\ge\frac{c}{2\sqrt A}\,n^{-1/2}=\frac{n^{-1/2}}{4\sqrt{2A}}\qquad(n\ge1).$$</div>
<p>Together with (T), $\mathbb P_{p_c}(|K_0|\ge n)\asymp n^{-1/2}$ for all $n\ge1$, with lower constant $1/(4\sqrt{2\lceil128C_+^2\rceil})$ and upper constant $C_+$.</p>
:::
<p><em>Idea of the proof of the order-parameter estimate.</em> The same comparison, applied at $q=2p_c-p$ and at $p&gt;p_c$ and followed by $n\to\infty$, gives $\theta(p)\le C(p-p_c)^2\chi(q)$, and (U) bounds $\chi(q)$ by $C'/(p-p_c)$. The lower bound $\theta(p)\ge(p-p_c)/(p(1-p_c))$ needs no triangle condition and is part of <a href="/tag/JQLC/">sharpness of the bond transition</a>.</p>
:::details Proof of the order-parameter estimate
<p>Let $D=\nabla_{p_c}$ and let $p_1\in(0,p_c)$ be as in (U). As in the proof of the critical tail estimate, put $\beta(p)=-\log(1-p)$ for $0\le p&lt;1$ and use the independent model on $\mathbb Z^d$ with weight $J_e=1$ on every nearest-neighbour edge, in which intensity $\beta(p)$ gives the law $\mathbb P_p$ and the weights at each vertex sum to $2d$. For $0\le q&lt;p&lt;1$,</p>
<div class="math-display">$$\beta(p)-\beta(q)\le\frac{p-q}{1-p},\qquad\beta(q)\ge q,\tag{E}$$</div>
<p>by $\log(1+x)\le x$ for $x\ge0$ and $-\log(1-x)\ge x$ for $0\le x&lt;1$. Put $\delta=\min\{p_c-p_1,(1-p_c)/2\}&gt;0$ and let $p_c&lt;p\le p_c+\delta$; in particular $p&lt;1$.</p>
<p><em>Upper bound.</em> Let $q=2p_c-p$. Then $p_1\le q&lt;p_c$, $p-q=2(p-p_c)$ and $p_c-q=p-p_c$. Since $0&lt;p_1\le q&lt;p$, (E) gives $0&lt;q\le\beta(q)&lt;\beta(p)$, and $\chi(q)&lt;\infty$. The second inequality of the <a href="/tag/JL1S/">cluster-tail comparison</a> with $M=2d$, $\beta_1=\beta(q)$ and $\beta_2=\beta(p)$ gives, for every integer $n\ge1$,</p>
<div class="math-display">$$\mathbb P_p(|K_0|\ge n)\le\Bigl(\frac2n+\frac{8d\,(\beta(p)-\beta(q))^2}{\beta(q)}\Bigr)\chi(q).$$</div>
<p>The events $\{|K_0|\ge n\}$ decrease to $\{|K_0|=\infty\}$ as $n\to\infty$, so continuity of probability from above, with $\chi(q)$ finite, gives $\theta(p)\le8d\,(\beta(p)-\beta(q))^2\chi(q)/\beta(q)$. Since $1-p\ge1-p_c-\delta\ge(1-p_c)/2$, (E) gives $\beta(p)-\beta(q)\le2(p-p_c)/(1-p)\le4(p-p_c)/(1-p_c)$; also $\beta(q)\ge q\ge p_1$, and $\chi(q)\le24dD^2/(p-p_c)$ by (U). Therefore</p>
<div class="math-display">$$\theta(p)\le8d\cdot\frac{16\,(p-p_c)^2}{(1-p_c)^2}\cdot\frac{24dD^2}{p-p_c}\cdot\frac1{p_1}=\frac{3072\,d^2D^2}{p_1(1-p_c)^2}\,(p-p_c).$$</div>
<p><em>Lower bound.</em> By <a href="/tag/JQLC/">sharpness of the bond transition</a>, $\theta(p)\ge(p-p_c)/(p(1-p_c))\ge p-p_c$ for $p_c&lt;p&lt;1$, since $0&lt;p\le1$ and $0&lt;1-p_c\le1$.</p>
<p>Hence, for $p_c&lt;p\le p_c+\delta$,</p>
<div class="math-display">$$p-p_c\le\theta(p)\le\frac{3072\,d^2\,\nabla_{p_c}^2}{p_1(1-p_c)^2}\,(p-p_c).$$</div>
:::
<p>By the <a href="/tag/3C2F/">equivalence of tail and magnetization exponents</a> with exponent $1/2$, the critical tail estimate is equivalent to $M(p_c,h)\asymp h^{1/2}$ as $h\downarrow0$, where $M(p_c,h)=\mathbb E_{p_c}[1-e^{-h|K_0|}]$ is the <a href="/articles/ghost-fields/">magnetization</a>.</p>
      <a id="tag-P9JD" data-assertion="corollary" data-title="Critical nonpercolation and infinite susceptibility"></a><p>The three estimates of the theorem are the mean-field <a href="#/susceptibility">susceptibility</a>, critical cluster-volume, and order-parameter behaviours. The middle estimate also implies $\theta(p_c)=0$ and, by the tail-sum formula, $\chi(p_c)=\infty$.</p>
      <p>The susceptibility estimate strengthens the subcritical finiteness supplied by <a href="#/sharpness">sharpness</a>. Applying the theorem to a particular dimension or kernel requires a separate proof that its critical triangle diagram is finite.</p>

## Spatial estimates and quantitative variants {#section-scope}

<p>Cluster volume and Euclidean radius are different observables. A pointwise estimate for $\tau_{p_c}(0,x)$, an extrinsic one-arm exponent, or the spatial motion of a backbone needs further geometric information. A <a href="#/hierarchical-two-point">hierarchical two-point theorem</a> is one such model-specific input.</p>
      <p>Quantitative versions track the size of the diagram. Versions allowing a controlled logarithmic divergence lead to different conclusions with logarithmic losses; they are separate statements rather than instances of the finite-triangle hypothesis.</p>

## History and attribution {#section-history}

<p>Aizenman and Newman (1984) introduced the triangle condition and proved under it that the susceptibility has the mean-field exponent $\gamma=1$, from the differential inequality $\chi'\ge c\chi^2$ near $p_c$. Barsky and Aizenman (1991) proved under the same condition that the critical cluster-volume exponent is $\delta=2$ and the order-parameter exponent is $\beta=1$, deriving the upper bounds from partial differential inequalities for the magnetization $M(p,h)$ that involve the open triangle diagram. Hutchcroft (2022) gave shorter derivations of all three estimates: the boundary argument for the susceptibility inequality (his Section 2) and, for the critical tail and the order parameter, an entropy comparison of cluster tails adapted from a relative-entropy inequality of Dewan and Muirhead (2021) (his Theorem 1.3 and Section 3). The proofs in this article follow Hutchcroft's routes, with the susceptibility inequality in the form (8), whose numerator is $(\chi-\nabla_p)^2$.</p>
<p>The triangle condition is known to hold, by the <a href="/articles/lace-expansion/">lace expansion</a>, for nearest-neighbour percolation on $\mathbb Z^d$ with $d$ sufficiently large and for sufficiently spread-out models with $d&gt;6$ (Hara and Slade 1990), and for nearest-neighbour percolation with $d\ge11$ (Fitzner and van der Hofstad 2017).</p>

## References {#section-references}

<ul>
<li>M. Aizenman and C. M. Newman, Tree graph inequalities and critical behavior in percolation models, <em>J. Stat. Phys.</em> 36 (1984), 107–143.</li>
<li>D. J. Barsky and M. Aizenman, Percolation critical exponents under the triangle condition, <em>Ann. Probab.</em> 19 (1991), 1520–1536.</li>
<li>V. Dewan and S. Muirhead, Upper bounds on the one-arm exponent for dependent percolation models, <a href="https://arxiv.org/abs/2102.12123">arXiv:2102.12123</a> (2021).</li>
<li>R. Fitzner and R. van der Hofstad, Mean-field behavior for nearest-neighbor percolation in $d&gt;10$, <em>Electron. J. Probab.</em> 22 (2017), no. 43.</li>
<li>T. Hara and G. Slade, Mean-field critical behaviour for percolation in high dimensions, <em>Comm. Math. Phys.</em> 128 (1990), 333–391.</li>
<li>T. Hutchcroft, On the derivation of mean-field percolation critical exponents from the triangle condition, <em>J. Stat. Phys.</em> 189 (2022), <a href="https://arxiv.org/abs/2106.06400v3">arXiv:2106.06400</a>.</li>
</ul>
