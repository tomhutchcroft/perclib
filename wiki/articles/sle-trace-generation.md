---
{
  "id": "sle-trace-generation",
  "title": "From radial limits to a generating trace",
  "subtitle": "First contact of an avoiding arc identifies the growing hull",
  "kind": "method",
  "category": "General theory",
  "summary": "A continuous curve of radial tip limits generates the Loewner hulls. An arc avoiding the curve cannot be swallowed: at its first contact, backward continuation forces the accessible boundary point to be the tip. Classical boundary extension then gives unrestricted inverse-map limits.",
  "context": [
    "The deterministic theorem requires a continuous real driving function, finite radial limits at every time, and continuity of those limits as a curve. Uniform radial convergence is not an additional hypothesis.",
    "Accessible-arc mapping, Lindelof's boundary-limit theorem, Torhorst's theorem and Caratheodory's extension theorem are named classical inputs. No local connectedness of the hull boundary is assumed in advance.",
    "For ordinary SLE with positive kappa different from eight, the joint radial-continuity theorem supplies the hypotheses on one probability-one event, including kappa four.",
    "This argument does not settle the kappa-eight trace theorem, simplicity, transience or boundary dimension. No Lean association is asserted."
  ],
  "related": ["sle-tip-continuity", "sle-trace-covering", "sle-space-filling", "sle-boundary-avoidance"],
  "sourceIds": ["rohde-schramm-basic-sle-2005"],
  "aliases": ["Loewner trace criterion", "Rohde Schramm reduction", "continuous radial limits"],
  "prototypeUses": []
}
---

## The deterministic criterion {#section-criterion}

<p>Let $U:[0,\infty)\to\mathbb R$ be continuous. For $z\in\mathbb H$, let $\tau(z)$ be the lifetime of the chordal Loewner solution</p>
<div class="math-display">$$\partial_t g_t(z)=\frac2{g_t(z)-U_t},\qquad g_0(z)=z.$$</div>
<p>Write $D_t=\{z\in\mathbb H:\tau(z)&gt;t\}$ and $f_t=g_t^{-1}:\mathbb H\to D_t$. These domains are simply connected and decrease with time. Their complementary hulls are bounded on each finite time interval, and the maps have the hydrodynamic expansions $g_t(z)=z+2t/z+O(z^{-2})$ and $f_t(z)=z-2t/z+O(z^{-2})$ at infinity. These are the usual deterministic Loewner facts.</p>

<a id="tag-N2VO" data-assertion="theorem" data-title="Continuous radial tip limits generate the Loewner hulls and give full inverse-map boundary continuity"></a>
<p>Suppose that the finite limits</p>
<div class="math-display">$$\gamma(t)=\lim_{y\downarrow0}f_t(U_t+iy)$$</div>
<p>exist for every $t\geq0$, and that $\gamma$ is continuous. Then, for every $t\geq0$, $D_t$ is the unbounded component of $\mathbb H\setminus\gamma[0,t]$. Moreover, $f_t$ extends continuously to $\overline{\mathbb H}$, with finite values at finite boundary points. In particular,</p>
<div class="math-display">$$\lim_{\substack{w\to U_t\\w\in\mathbb H}}f_t(w)=\gamma(t),$$</div>
<p>with no restriction on the direction of approach.</p>

<p><em>Proof.</em> We first identify the domain. Since $f_0$ is the identity, $\gamma(0)=U_0$. Also $\gamma(s)\notin D_s$: if it were an interior point, continuity of $g_s$ there would give $g_s(\gamma(s))=U_s\in\mathbb R$, which is impossible. Thus $D_t$ misses the compact set $\Gamma_t=\gamma[0,t]$. Being connected and unbounded, $D_t$ lies in the unique unbounded component $\Omega_t$ of $\mathbb H\setminus\Gamma_t$.</p>

<p>Suppose that $z\in\Omega_t\setminus D_t$. Choose a point $w$ high enough to belong to $D_t$, and join $w$ to $z$ by a simple polygonal arc $P$ in $\Omega_t$. Such an arc exists because $\Omega_t$ is open and connected. Its compact image lies in $\mathbb H$ and misses $\Gamma_t$. The lifetime function is lower semicontinuous, since $\{\tau&gt;s\}=D_s$ is open. Consequently</p>
<div class="math-display">$$r=\min_{p\in P}\tau(p)$$</div>
<p>is attained and satisfies $0&lt;r\leq t$. Positivity can also be seen directly: if $Y_s=\operatorname{Im}g_s(p)$, then $\partial_s(Y_s^2)\geq-4$, so the positive minimum height of $P$ gives a common positive lower bound for its lifetimes. Every point of $P$ lies in $D_s$ for $s&lt;r$, while at least one point lies outside $D_r$.</p>

<p>Traverse $P$ from $w$, and let $q$ be its first point outside $D_r$. The part of the arc before $q$ lies in $D_r$ and tends to the finite boundary point $q\in\mathbb H$. The accessible-arc mapping theorem implies that its image under $g_r$ tends to some $x\in\mathbb R\cup\{\infty\}$. The hydrodynamic expansion of $f_r$ rules out $x=\infty$, since the original arc tends to a finite point.</p>

<p>We claim that $x=U_r$. Otherwise put $d=|x-U_r|&gt;0$. On a sufficiently short interval $[s,r]$, the driving values stay within $d/4$ of $U_r$. The backward Loewner flow $h_{s,r}$ is then holomorphic in a neighborhood of $x$ and real on the real line. Indeed, in $B(x,d/4)$ the vector field stays away from its pole and has modulus at most $4/d$; choosing $r-s&lt;d^2/32$ keeps solutions starting in $B(x,d/8)$ inside that disk of radius $d/4$. Holomorphic dependence on the initial value and uniqueness give the asserted extension and its reality.</p>

<p>For points $p$ on the arc before $q$, the flow identity gives</p>
<div class="math-display">$$g_s(p)=h_{s,r}(g_r(p)).$$</div>
<p>As $p$ tends to $q$, the right side tends to $h_{s,r}(x)\in\mathbb R$. But $q\in D_s$, because $s&lt;r$; the left side therefore tends to $g_s(q)\in\mathbb H$. This contradiction proves the claim.</p>

<p>Along the image arc ending at $U_r$, the inverse map $f_r$ tends to $q$. Lindelof's boundary-limit theorem identifies this finite arc limit with its radial limit at $U_r$. Hence $q=\gamma(r)$, contrary to $P\cap\Gamma_t=\varnothing$. We conclude that $\Omega_t=D_t$. The minimum over the entire arc is what guarantees that $q$ was interior at every earlier time; the argument does not assume that a hull grows only by adding individual boundary points.</p>

<p>It remains to obtain boundary continuity. On the Riemann sphere, set</p>
<div class="math-display">$$E_t=\Gamma_t\cup\mathbb R\cup\{\infty\}.$$</div>
<p>This is a continuous image of a compact interval: traverse the real circle from $U_0$ back to $U_0$, and then traverse $\gamma[0,t]$. It is therefore a locally connected continuum, by the Peano-continuum characterization. The domain $D_t=\Omega_t$ is a complementary component of $E_t$. Torhorst's theorem makes its boundary locally connected, and Caratheodory's extension theorem gives a continuous spherical extension of $f_t$ to $\mathbb H\cup\mathbb R\cup\{\infty\}$.</p>

<p>No finite boundary point can be sent to infinity. If $w_n\in\mathbb H$ tended to a finite real number while $f_t(w_n)\to\infty$, the hydrodynamic expansion of $g_t$ would imply $w_n=g_t(f_t(w_n))\to\infty$, a contradiction. Thus the extension is complex-valued at finite points. Its value at $U_t$ agrees with the assumed radial limit, proving the unrestricted limit. The case $t=0$ is immediate as well.</p>

## The conformal inputs {#section-conformal-inputs}

<p>The two boundary-limit facts used above concern an arc approaching an accessible boundary point, and do not presuppose local connectedness of the whole boundary. A conformal map from a simply connected domain onto the disk sends such an arc to one with a single terminal boundary point. If the inverse map has a finite limit along that image arc, Lindelof's theorem gives the same angular limit, hence the same radial limit. For the latter application, postcomposing $f_r:\mathbb H\to\mathbb H$ with a Cayley map reduces to a bounded analytic function.</p>

<p>Rohde–Schramm Section 4 cites Pommerenke, <em>Boundary Behaviour of Conformal Maps</em> (1992), Proposition 2.14, for the accessible-arc fact, and Ahlfors, <em>Conformal Invariants</em> (1973), Theorem 3.5, for the boundary-limit identification. Its final extension step cites Pommerenke Theorem 2.1. Here that step is expressed through the Peano-continuum characterization, Torhorst's theorem and Caratheodory's theorem. These classical theorems are inputs, not proofs supplied by this article; the references are those identified in the source, not a claim of a new reading of the monographs.</p>

## Application to ordinary SLE {#section-sle-trace}

<a id="tag-MN2A" data-assertion="corollary" data-title="Ordinary SLE has a continuous generating trace and full tip limits for every parameter different from eight"></a>
<p>Let $U_t=\sqrt\kappa B_t$, where $\kappa\geq0$ and $\kappa\ne8$. Almost surely there is a continuous curve $\gamma:[0,\infty)\to\overline{\mathbb H}$ starting at zero such that, simultaneously for every $t\geq0$,</p>
<div class="math-display">$$\gamma(t)=\lim_{\substack{w\to U_t\\w\in\mathbb H}}f_t(w),\qquad
D_t=\text{the unbounded component of }\mathbb H\setminus\gamma[0,t].$$</div>
<p>Each $f_t$ extends continuously to the closed half-plane. For positive $\kappa$, the uniform radial error and the time modulus in <a href="/tag/N7TT/">N7TT</a> and <a href="/tag/MV6M/">MV6M</a> hold for this same generating curve.</p>

<p><em>Proof.</em> For $\kappa&gt;0$, N7TT supplies a single probability-one event on which the finite radial limits exist at every time and form a continuous curve. Apply the deterministic theorem N2VO to each sample on that event. Its conclusion holds for every time pathwise, so there is no further intersection of uncountably many probability-one events. In particular the unrestricted inverse-map limit is available at a finite random time. For $\kappa=0$, the driving function vanishes and the solution is the vertical slit: $\gamma(t)=2i\sqrt t$ and $f_t(iy)=i\sqrt{y^2+4t}$. Its continuous radial curve also satisfies N2VO.</p>

<p>This proves the trace-generation conclusion of Rohde–Schramm Theorem 5.1 away from eight using the preceding written derivative and radial-continuity arguments. The covering article's trace hypothesis is therefore supplied for $\kappa\ne8$, and the space-filling article's trace hypothesis is supplied for $\kappa&gt;8$. The latter article still needs its zero-area boundary input. For $0\leq\kappa\leq4$, simplicity remains a separate theorem. At $\kappa=8$, <a href="/tag/YVFR/">YVFR</a> supplies limits only for almost every time and cannot replace the hypotheses of N2VO; the source's cited Lawler–Schramm–Werner extension remains a separate input.</p>


## Simplicity up to four {#section-simplicity-update}

<p>The extra geometric assertion is now proved in <a href="/tag/CKFH/">CKFH</a>. It combines the trace theorem above with <a href="/tag/W8MU/">W8MU</a>, which obtains simultaneous real-boundary avoidance from the real flows. Rational restart times and strict capacity growth exclude repeated visits. Thus the ordinary SLE trace is simple and lies in the open half-plane after time zero for kappa at most four. This also supplies the remaining simple-trace input of the earlier transience argument. The kappa-eight trace theorem and the other regimes remain separate.</p>
