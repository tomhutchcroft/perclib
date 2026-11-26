---
{
  "id": "regular-tree-percolation",
  "title": "Percolation on a regular tree",
  "subtitle": "Root laws, extinction conditioning and critical amplitudes",
  "kind": "model",
  "category": "General theory",
  "summary": "Exact cluster-size laws on a regular tree give the finite-cluster moment exponents on both sides of criticality. Extinction conditioning and the logarithmic correction to critical survival are proved with the root degree kept explicit.",
  "context": [
    "The tree has degree r = n + 1 with n at least two. Its root has r possible children; every later vertex has n.",
    "Bonds are independent with common occupation probability p. A forward cluster is a Galton–Watson tree with Binomial(n,p) offspring.",
    "Finite-cluster moments sum over finite sizes, including above criticality; they are not conditional expectations unless divided by the extinction probability.",
    "The line graph r = 2 is excluded from the exponent statements. Corrections refer to the 17 March 2017 author manuscript; the published edition has not been compared."
  ],
  "related": ["branching-processes", "binary-tree-percolation", "critical-exponents", "bounded-degree-paths"],
  "sourceIds": ["heydenreich-hofstad"],
  "aliases": ["regular tree critical exponents", "discrete duality", "binomial survival logarithm"],
  "prototypeUses": []
}
---

## The root and the forward process {#section-duality}

<p>Fix an integer $n\ge2$ and put $r=n+1$ and $p_c=1/n$. Let $T$ be the total progeny of a process with offspring generating function $f(s)=(1-p+ps)^n$, starting from one individual, and let $S=|C(o)|$ on the $r$-regular tree. At the root there are $r$ independent potential branches, each open with probability $p$ and, when open, having size distributed as $T$.</p>

<a id="tag-0JTK" data-assertion="proposition" data-title="Extinction conditioning and root amplitudes on a regular tree"></a>
<p>For $0\le p<1$, let $q$ be the least fixed point of $f$ in $[0,1]$, and set</p>
<div class="math-display">$$w=1-p+pq,\qquad q_0=w^r,\qquad
p_*=\frac{pq}{w}=p w^{n-1}.$$</div>
<p>Then $q=\mathbb P(T<\infty)$ and $q_0=\mathbb P(S<\infty)$. Conditional on extinction, the forward process has offspring law $\operatorname{Binomial}(n,p_*)$; at the root the corresponding law is $\operatorname{Binomial}(r,p_*)$. For $p>p_c$, $np_*<1$. For $p\ne p_c$,</p>
<div class="math-display">$$
\mathbb E[T;T<\infty]=\frac{q}{1-np_*},\qquad
\mathbb E[S;S<\infty]=q_0\left(1+\frac{rp_*}{1-np_*}\right).
$$</div>
<p>In particular $p_c=p_T=1/n$. As $p\downarrow p_c$ from above,</p>
<div class="math-display">$$
1-q\sim\frac{2n^2}{n-1}(p-p_c),\qquad
1-q_0\sim\frac{2rn}{n-1}(p-p_c),\qquad
1-np_*\sim n(p-p_c).
$$</div>
<p>On either side of criticality,</p>
<div class="math-display">$$\mathbb E[S;S<\infty]\sim
\frac{r}{n^2}|p-p_c|^{-1}.$$</div>
<p><em>Proof.</em> The extinction probability is the least fixed point, obtained by iterating $f$ from zero. Convexity shows that it equals one for $np\le1$ and is less than one for $np>1$. At criticality the offspring law is nonconstant, so extinction still occurs almost surely. Independence of the root branches gives $q_0=w^r$.</p>
<p>A potential branch fails to reach infinity with probability $w$: either its edge is closed, or it is open and the forward process dies. Conditional on this failure, the probability that its edge is open is $pq/w$. Conditioning all branches to fail preserves their independence, since the conditioning event is the intersection of events on disjoint branch coordinates. Recursing gives the claimed conditional laws. Equivalently the forward conditional generating function is</p>
<div class="math-display">$$\frac{f(qs)}q=(1-p_*+p_*s)^n.$$</div>
<p>For $p>p_c$, strict convexity between the fixed points $q$ and one yields $f'(q)<1$. Since $f'(q)=npw^{n-1}=np_*$, the conditional process is subcritical. Its mean progeny is $(1-np_*)^{-1}$ by <a href="/tag/UKY4/">UKY4</a>. Taking the root mean and multiplying by the extinction probabilities proves the two formulas. Below criticality these reduce to $1/(1-np)$ and $(1+p)/(1-np)$. At criticality the unconditional mean is infinite, while above it survival has positive probability; hence $p_T=p_c$.</p>
<p>The critical offspring variance is $\sigma^2=(n-1)/n$. Applying <a href="/tag/N9P5/">N9P5</a> to the bounded binomial family gives $1-q\sim2(np-1)/\sigma^2$. Substituting into $q_0=(1-p(1-q))^r$ gives the root survival equivalent. Writing $\varepsilon=p-p_c$ then gives</p>
<div class="math-display">$$w=1-\frac{2n}{n-1}\varepsilon+o(\varepsilon),
\qquad p_*=p w^{n-1}=\frac1n-\varepsilon+o(\varepsilon).$$</div>
<p>The mean formula now gives the upper-side amplitude; the explicit subcritical formula gives the same lower-side amplitude.</p>
<p>At $p=1$ the finite-size probabilities and finite-cluster moments are zero; conditioning on extinction is undefined. At $p=p_c$ the finite-cluster first moments are infinite. These endpoints do not require assigning a value to a zero-probability conditional law.</p>
<p>The normalization by $w$ is essential in the <a href="/errata/heydenreich-hofstad/#extinction-conditioning">manuscript's duality calculation</a>. For $r=3$ and $p=3/4$, $q=1/9$, $w=1/3$ and $p_*=1/4$. Thus the forward finite-cluster mean is $2/9$. Using $pq=1/12$ as the conditional parameter would instead give $2/15$.</p>

## Progeny from several ancestors {#section-forest-progeny}

<a id="tag-UPOZ" data-assertion="theorem" data-title="Dwass's formula for a forest with an arbitrary positive number of ancestors"></a>
<p>Let $\xi$ be any almost surely finite, nonnegative integer-valued offspring variable. Start with $m\ge1$ independent ancestors and let $T^{(m)}$ count their total progeny, including the ancestors. For every integer $k\ge m$,</p>
<div class="math-display">$$\mathbb P(T^{(m)}=k)=\frac{m}{k}
\mathbb P\!\left(\xi_1+\cdots+\xi_k=k-m\right),$$</div>
<p>where the $\xi_i$ are independent copies of $\xi$. The total progeny can be infinite; no finite-mean assumption is needed. For $k<m$ the probability is zero.</p>
<p><em>Proof.</em> If $\mathbb P(\xi=0)=0$, every family has a descendant in every generation and both sides vanish. Otherwise let $f(u)=\mathbb E u^\xi$, with $f(0)>0$, and let $B(s)=\mathbb E[s^{T^{(1)}};T^{(1)}<\infty]$. The offspring decomposition gives the formal identity $B(s)=sf(B(s))$. Independence gives the forest series $B(s)^m$.</p>
<p>Here is the coefficient change of variables in full. The series $g(u)=u/f(u)$ has a nonzero linear coefficient and is the formal inverse of $B$. If $\operatorname{Res}$ denotes the coefficient of exponent $-1$, then for any formal power series $H$ and integer $k\ge1$,</p>
<div class="math-display">$$
\begin{aligned}
[s^k]H(B(s))
&=\operatorname{Res}_u H(u)u^{-k-1}f(u)^{k-1}
\bigl(f(u)-u f'(u)\bigr)\\
&=\frac1k\operatorname{Res}_u H'(u)u^{-k}f(u)^k
=\frac1k[u^{k-1}]H'(u)f(u)^k.
\end{aligned}
$$</div>
<p>The first equality is substitution $s=g(u)$ in the residue. It follows by checking Laurent monomials: residues of derivatives vanish, while $g'(u)/g(u)$ has residue one. The second equality follows by taking the zero residue of the derivative of $H(u)u^{-k}f(u)^k$. Each required coefficient involves only finitely many coefficients of $f$, so the calculation does not require analyticity beyond its formal series. Taking $H(u)=u^m$ gives $(m/k)[u^{k-m}]f(u)^k$, the asserted probability.</p>
<p>Equivalently, explore a queue starting with $m$ individuals, appending each individual's children. Its first empty time is $T^{(m)}$, and after $k$ explorations its size is $m+\sum_{i=1}^k(\xi_i-1)$. The target offspring sum must therefore be $k-m$. The <a href="/errata/heydenreich-hofstad/#forest-hitting-target">manuscript's many-ancestor display</a> retains $k-1$ instead. Already for $\xi=0$ almost surely and $k=m=2$, the queue empties at time two with probability one, whereas that displayed right side is zero.</p>

## The exact size distribution {#section-size-law}

<a id="tag-LS6G" data-assertion="proposition" data-title="Exact forward and root cluster-size laws on a regular tree"></a>
<p>For $0<p<1$ and every integer $k\ge1$,</p>
<div class="math-display">$$
\begin{aligned}
\mathbb P(T=k)&=\frac1k\binom{nk}{k-1}
p^{k-1}(1-p)^{(n-1)k+1},\\
\mathbb P(S=k)&=\frac{r}{(n-1)k+2}\binom{nk}{k-1}
p^{k-1}(1-p)^{(n-1)k+2}.
\end{aligned}
$$</div>
<p>Above criticality these formulas describe only the finite part of the laws.</p>
<p><em>Proof.</em> The first formula follows from <a href="/tag/RL1L/">Dwass's identity</a>, since a sum of $k$ offspring counts has law $\operatorname{Binomial}(nk,p)$. For the root law, let $B(s)=\mathbb E[s^T;T<\infty]$ and $F(s)=\mathbb E[s^S;S<\infty]$. Their formal series satisfy</p>
<div class="math-display">$$B(s)=s(1-p+pB(s))^n,\qquad F(s)=s(1-p+pB(s))^r.$$</div>
<p>The coefficient change of variables proved in <a href="/tag/UPOZ/">UPOZ</a>, with $H(u)=(1-p+pu)^r$, gives, for $k\ge2$,</p>
<div class="math-display">$$[s^k]F(s)=\frac{rp}{k-1}[u^{k-2}]
(1-p+pu)^{n(k-1)+r-1}
=\frac{r}{k-1}\binom{nk}{k-2}
p^{k-1}(1-p)^{(n-1)k+2}.$$</div>
<p>Use $\binom{nk}{k-2}/(k-1)=\binom{nk}{k-1}/((n-1)k+2)$. For $k=1$, all root edges must be closed, giving $(1-p)^r$, also the displayed formula.</p>

## Size tails and moments near criticality {#section-moments}

<p>Define, for $0<p<1$,</p>
<div class="math-display">$$
Q(p)=\frac{n^n}{(n-1)^{n-1}}p(1-p)^{n-1},\qquad
\lambda(p)=-\log Q(p),\qquad
A_c=\frac{r}{\sqrt{2\pi n(n-1)}}.
$$</div>
<p>The maximum of $Q$ is one, attained only at $p_c$.</p>

<a id="tag-1KBO" data-assertion="theorem" data-title="Root size tails and all positive finite-cluster moments near criticality"></a>
<p>At criticality,</p>
<div class="math-display">$$\mathbb P_{p_c}(S=k)\sim A_c k^{-3/2},
\qquad \mathbb P_{p_c}(S\ge k)\sim2A_c k^{-1/2}.$$</div>
<p>Write $M_a(p)=\sum_{k\ge1}k^a\mathbb P_p(S=k)$ for $a>0$. As $p\to p_c$ through $p\ne p_c$,</p>
<div class="math-display">$$
\begin{aligned}
\lambda(p)&\sim\frac{n^3}{2(n-1)}(p-p_c)^2,\\
M_a(p)&\sim A_c\Gamma(a-\tfrac12)\lambda(p)^{1/2-a}
&& (a>\tfrac12),\\
M_{1/2}(p)&\sim A_c\log\frac1{\lambda(p)},\\
M_a(p)&\longrightarrow M_a(p_c)<\infty
&& (0<a<\tfrac12).
\end{aligned}
$$</div>
<p>In particular, for each $a>1/2$,</p>
<div class="math-display">$$\frac{M_{a+1}(p)}{M_a(p)}
\sim\frac{a-\tfrac12}{\lambda(p)}.$$</div>
<p>These give $\delta=2$ and the moment-gap exponents $\Delta=\Delta'=2$. Together with 0JTK they give $\beta=\gamma=\gamma'=1$, including the amplitudes appropriate to the root.</p>
<p><em>Proof.</em> Write the binomial coefficient in LS6G as</p>
<div class="math-display">$$\binom{nk}{k-1}=\frac{k}{(n-1)k+1}\binom{nk}{k}.$$</div>
<p>Stirling's formula then gives</p>
<div class="math-display">$$
\mathbb P_p(S=k)=A(p)k^{-3/2}e^{-\lambda(p)k}(1+O(k^{-1})),
\quad
A(p)=\frac{r(1-p)^2}{p(n-1)^2}
\sqrt{\frac{n}{2\pi(n-1)}}.
$$</div>
<p>The relative error is uniform for $p$ in a compact subinterval of $(0,1)$: all $p$-dependence has been factored out exactly. In particular $A(p_c)=A_c$ and, in a fixed neighbourhood of $p_c$, the masses are bounded by $Ck^{-3/2}$. At $p_c$ there is no mass at infinity. Summing the local equivalent, using $\sum_{j\ge k}j^{-3/2}\sim2k^{-1/2}$, proves the tail equivalent.</p>
<p>The derivative of $\log Q$ vanishes at $p_c$ and its second derivative there is $-n^3/(n-1)$, giving the expansion for $\lambda$. For $a>1/2$, the Riemann sum with mesh $\lambda$ gives</p>
<div class="math-display">$$\sum_{k\ge1}k^{a-3/2}e^{-\lambda k}
\sim\lambda^{1/2-a}\int_0^\infty u^{a-3/2}e^{-u}\,du.$$</div>
<p>The integrand is integrable at zero and at infinity. Its small- and large-$u$ tails can therefore be removed uniformly before passing to Riemann sums on a compact interval. To absorb the relative Stirling error, first restrict to $k\ge K$, where it is at most $C/K$; the finitely many omitted terms are bounded while the main sum diverges. Let $\lambda\downarrow0$ and then $K\to\infty$.</p>
<p>For $a=1/2$, the main sum is $-\log(1-e^{-\lambda})\sim\log(1/\lambda)$, and the absolute error is bounded by a constant times $\sum k^{-2}$. For $0<a<1/2$, the bound $Ck^{a-3/2}$ is summable; coefficientwise continuity and dominated convergence give the limit. The ratio formula follows from $\Gamma(a+1/2)=(a-1/2)\Gamma(a-1/2)$.</p>
<p>The forward critical local constant is $(2\pi\sigma^2)^{-1/2}$ with $\sigma^2=(n-1)/n$, obtained in the same way from LS6G. Its tail constant is twice its local constant. This is the normalization needed in the <a href="/errata/heydenreich-hofstad/#local-to-tail-constant">manuscript's tail summation</a>; root and forward constants differ by $r/n$.</p>

## Critical arms and their logarithmic correction {#section-survival}

<p>At $p=p_c$, let $u_m$ be the probability that the forward process reaches generation $m$, and let $v_m$ be the probability that $C(o)$ reaches tree distance $m$. Thus $u_0=v_0=1$.</p>

<a id="tag-X9U3" data-assertion="proposition" data-title="The logarithmic second-order correction to critical binomial survival"></a>
<p>As $m\to\infty$,</p>
<div class="math-display">$$
u_m=\frac{2n}{(n-1)m}
\left(1-\frac{n+1}{3(n-1)}\frac{\log m}{m}+O(m^{-1})\right),
\qquad
v_m\sim\frac{2r}{(n-1)m}.
$$</div>
<p>In particular the intrinsic one-arm exponent is one. The relative error in the leading equivalent for $u_m$ is not $O(m^{-1})$: its nonzero logarithmic term cannot be absorbed into that bound.</p>
<p><em>Proof.</em> Branch independence gives</p>
<div class="math-display">$$u_{m+1}=1-(1-u_m/n)^n,\qquad
v_m=1-(1-u_{m-1}/n)^r\quad(m\ge1).$$</div>
<p>Put $a=(n-1)/(2n)$ and $b=(n-1)(n-2)/(6n^2)$. Taylor expansion of the first recursion gives</p>
<div class="math-display">$$u_{m+1}=u_m-au_m^2+bu_m^3+O(u_m^4).$$</div>
<p>By <a href="/tag/8WO7/">8WO7</a>, $u_m\sim1/(am)$. For $z_m=1/u_m$, inversion gives</p>
<div class="math-display">$$z_{m+1}-z_m
=a+\frac{a^2-b}{z_m}+O(z_m^{-2}).$$</div>
<p>Since $z_m\asymp m$, summing first yields $z_m=am+O(\log m)$. Consequently</p>
<div class="math-display">$$\frac1{z_m}=\frac1{am}
+O\!\left(\frac{\log m}{m^2}\right).$$</div>
<p>Substitute this sharper estimate into the increment formula. The remaining errors are summable, so</p>
<div class="math-display">$$z_m=am+c\log m+O(1),\qquad
c=\frac{a^2-b}{a}=\frac{n+1}{6n}.$$</div>
<p>Inverting once more proves the expansion, since $c/a=(n+1)/(3(n-1))$ and $(\log m)^2/m^2=O(m^{-1})$. The root recursion gives $v_m\sim(r/n)u_{m-1}$ and hence its stated amplitude.</p>
<p>For example, when $n=2$ the exact recursion is $u_{m+1}=u_m-u_m^2/4$ and the expansion is $u_m=(4/m)(1-(\log m)/m+O(m^{-1}))$. This provides a concrete instance of the correction to <a href="/errata/heydenreich-hofstad/#survival-error-rate">Exercise 2.5(b)</a>. The leading equivalent and the exponent are unaffected.</p>
