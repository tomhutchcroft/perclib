---
{
  "id": "sle-space-filling",
  "title": "The space-filling SLE regime",
  "subtitle": "From density and zero-area hull boundaries to transience",
  "kind": "method",
  "category": "General theory",
  "summary": "At kappa at least eight, density rules out pockets left behind the trace. A strong Markov and area argument then shows that the hull immediately surrounds the origin. Scaling gives transience and finite-time coverage of each compact set.",
  "context": [
    "We work with ordinary chordal SLE for kappa at least eight, without force points or conditioning.",
    "Trace existence and generation are explicit inputs. We require the full boundary limit of the inverse map at the driving point, simultaneously at every time, as in Rohde–Schramm Theorem 5.1 and its cited Lawler–Schramm–Werner extension at kappa eight.",
    "The engulfment and transience proofs also use zero planar area of the hull boundary at each deterministic time, the conclusion of Rohde–Schramm Corollary 5.3. Its derivative and boundary-dimension arguments are not proved here.",
    "The Loewner composition rule, Brownian strong Markov property, scaling and the Brownian germ zero-one law are the probabilistic inputs. The intermediate regime between four and eight has a different engulfment argument."
  ],
  "related": ["sle-trace-covering", "sle-swallowing", "sle-conformal-radius", "sle-boundary-avoidance"],
  "sourceIds": ["rohde-schramm-basic-sle-2005"],
  "aliases": ["SLE space filling", "SLE origin engulfment", "SLE eight transience"],
  "prototypeUses": []
}
---

## Density leaves no pockets {#section-no-pockets}

<p>Let $U_t=\sqrt\kappa B_t$ and let $D_t$ be the domain of the chordal Loewner map $g_t$. Write $\tau(z)$ for the flow lifetime, so $D_t=\{z\in\mathbb H:\tau(z)>t\}$, and let $K_t=\overline{\mathbb H\setminus D_t}$, with closure in $\mathbb C$. Assume there is a continuous generating trace $\gamma$, starting at zero, such that $D_t$ is the unbounded component of $\mathbb H\setminus\gamma[0,t]$. We require</p>
<div class="math-display">$$\lim_{\substack{w\to U_t\\w\in\mathbb H}}g_t^{-1}(w)=\gamma(t)
\qquad\text{for every }t\geq0$$</div>
<p>on one probability-one event. The unrestricted approach in this limit matters when it is used at a stopping time below. Set $\Gamma=\gamma[0,\infty)$.</p>

<a id="tag-UELC" data-assertion="proposition" data-title="A dense generating SLE trace leaves no off-trace part of any interior hull"></a>
<p>For $\kappa\geq8$, under the trace hypothesis, almost surely $\overline\Gamma=\overline{\mathbb H}$ and, simultaneously for every $t\geq0$,</p>
<div class="math-display">$$K_t\cap\mathbb H=\gamma[0,t]\cap\mathbb H.$$</div>
<p><em>Proof.</em> The zero-distance conclusion of <a href="/articles/sle-trace-covering/#section-uniform-hitting">VEZ7</a> holds for each fixed point of $\mathbb H$. Intersect these probability-one events over points with rational coordinates. The resulting trace is dense in $\mathbb H$, hence in its closure.</p>
<p>The rest is deterministic. For $s\geq t$, the inverse-map boundary limit gives $\gamma(s)\in\overline{D_s}\subseteq\overline{D_t}$. If a point of $K_t\cap\mathbb H$ were outside the compact past trace, it would lie in a bounded component of $\mathbb H\setminus\gamma[0,t]$. Choose a small open disk around it whose closure lies in that component. The disk misses the past trace, and it is disjoint from $\overline{D_t}$, so it also misses every future trace point. This contradicts density. The reverse inclusion follows from the definition of the generated domain.</p>
<p>This argument is pathwise once density holds. It therefore proves the statement for all times together, without an uncountable intersection of probability-one events. It also explains why density alone does not yet prove space filling: the full range need not yet be known to be closed.</p>

## A fixed point is reached in finite time {#section-fixed-hitting}

<a id="tag-KFWY" data-assertion="corollary" data-title="For kappa at least eight every fixed interior point is first hit at its finite Loewner lifetime"></a>
<p>For $\kappa\geq8$, under the trace hypothesis and for each fixed $z\in\mathbb H$,</p>
<div class="math-display">$$\tau(z)<\infty,\qquad
\gamma(\tau(z))=z,\qquad z\notin\gamma[0,\tau(z))
\qquad\text{almost surely}.$$</div>
<p><em>Proof.</em> Finite lifetime is <a href="/articles/sle-swallowing/#section-finite-lifetime">6DV8</a>. At that lifetime, $z\in K_{\tau(z)}\cap\mathbb H$. UELC, which holds at all times on one event, places $z$ on $\gamma[0,\tau(z)]$. An earlier hit would put $z$ outside the earlier Loewner domain, contrary to the definition of $\tau(z)$. Hence the hit occurs exactly at $\tau(z)$.</p>
<p>The lifetime is a stopping time for the Brownian filtration. The assertion here is still for each fixed $z$; the simultaneous filling statement will be obtained after proving engulfment.</p>

## The origin is surrounded immediately {#section-engulfment}

<p>In this section also assume that for each deterministic $T>0$, the planar Lebesgue area of $\partial K_T$ is zero almost surely. This is the part of Rohde–Schramm Corollary 5.3 needed here. We do not assume a zero-area statement at arbitrary random times.</p>

<a id="tag-ZS6G" data-assertion="theorem" data-title="Zero-area hull boundaries force immediate engulfment of the origin in the space-filling SLE regime"></a>
<p>For $\kappa\geq8$, under the trace and boundary-area hypotheses, almost surely for every $t>0$,</p>
<div class="math-display">$$\rho_t:=\operatorname{dist}(0,D_t)>0.$$</div>
<p>In particular $K_t$ contains $B(0,\rho_t)\cap\mathbb H$.</p>
<p><em>Proof.</em> Let $E_t=\{0\notin\overline{D_t}\}$. These events increase with $t$, and Brownian scaling makes $\mathbb P(E_t)=\delta$ independent of $t>0$. We first prove that $\delta>0$.</p>
<p>Suppose instead that $\delta=0$. By intersecting over positive integer times and using the nesting of the domains, almost surely zero belongs to $\overline{D_s}$ for every $s>0$. Fix an interior point $z$ and stop at $\tau=\tau(z)$, which is finite by KFWY. The Loewner composition rule and Brownian strong Markov property say that the future domains</p>
<div class="math-display">$$\widetilde D_s=g_\tau(D_{\tau+s})-U_\tau,\qquad s>0,$$</div>
<p>have the law of fresh SLE domains, conditionally on the past. Thus $0\in\overline{\widetilde D_s}$ simultaneously for all $s>0$, almost surely. Choose points of $g_\tau(D_{\tau+s})$ tending to $U_\tau$. The full inverse-map boundary limit, valid at every time on the trace event, sends them to $\gamma(\tau)=z$. Consequently</p>
<div class="math-display">$$z\in\overline{D_{\tau+s}}\cap K_{\tau+s}
\subseteq\partial K_{\tau+s}\qquad(s>0).$$</div>
<p>In particular, for a deterministic $T$ and this fixed $z$, $\tau(z)<T$ implies $z\in\partial K_T$, up to a null event. The simultaneous future-time assertion just established permits substituting the random duration $T-\tau(z)$ here.</p>
<p>Now fix a bounded open disk $A$ with closure in $\mathbb H$. Tonelli's theorem at deterministic time $T$ gives</p>
<div class="math-display">$$0=\mathbb E\bigl[\operatorname{area}(\partial K_T\cap A)\bigr]
\geq\int_A\mathbb P(\tau(z)<T)\,d\operatorname{area}(z).$$</div>
<p>The usual measurable Loewner flow makes the lifetime and hull-membership events jointly measurable; thus the pointwise probability-one conclusions suffice for this integral. Let $T$ tend to infinity through the integers. KFWY and monotone convergence make the right side tend to $\operatorname{area}(A)>0$, a contradiction. Hence $\delta>0$.</p>
<p>The event $E=\bigcap_{n\geq1}E_{1/n}$ has probability $\delta$, since the events decrease with $n$. For every $N$, it equals $\bigcap_{n\geq N}E_{1/n}$ and therefore belongs to the Brownian sigma-field at time $1/N$. It is a germ event. Blumenthal's zero-one law gives $\delta=1$. On $E$, every positive time follows some $1/n$, so monotonicity gives $E_t$ for every $t>0$. This is exactly the asserted positive distance.</p>
<p>The area contradiction uses a fixed interior point followed by a spatial integral, not a simultaneous hitting claim. The zero-one step then upgrades positive-probability engulfment to an almost-sure statement at every positive time.</p>

## Transience and coverage of compact sets {#section-space-filling}

<a id="tag-R2A0" data-assertion="theorem" data-title="SLE at kappa at least eight is transient and fills each compact half-plane set in finite time under the stated trace and area inputs"></a>
<p>Under the hypotheses of ZS6G, almost surely</p>
<div class="math-display">$$\lim_{t\to\infty}|\gamma(t)|=\infty,
\qquad \gamma[0,\infty)=\overline{\mathbb H}.$$</div>
<p>More precisely, on one probability-one event, every compact $C\subset\overline{\mathbb H}$ is contained in $\gamma[0,T]$ for some finite $T$ depending on the path and on $C$.</p>
<p><em>Proof.</em> The distances $\rho_t$ increase with $t$, and scaling gives $\rho_t\overset{\mathrm{law}}=\sqrt t\,\rho_1$. Since $\rho_1>0$ almost surely, for each fixed $R>0$,</p>
<div class="math-display">$$\mathbb P(\rho_t\leq R)
=\mathbb P(\rho_1\leq R/\sqrt t)\longrightarrow0.$$</div>
<p>Monotonicity, followed by a countable intersection over integer $R$, shows that $\rho_t\to\infty$ almost surely. For every $s\geq t$, the trace lies in $\overline{D_s}\subseteq\overline{D_t}$, so $|\gamma(s)|\geq\rho_t$. This proves transience.</p>
<p>Choose a time $T$ with $\rho_T>R$. The open half-disk $B(0,\rho_T)\cap\mathbb H$ lies in $K_T$, and hence in $\gamma[0,T]$ by UELC. The finite past trace is compact and therefore closed. Taking closure shows that it contains the entire closed half-disk $\{z\in\overline{\mathbb H}:|z|\leq R\}$. Integer radii exhaust the closed half-plane and contain every compact subset, proving both filling assertions.</p>
<p>Rohde–Schramm obtain the large-parameter part of Lemma 7.3, Theorem 7.1 and Corollary 7.4 by this sequence of ideas. Their update includes $\kappa=8$ using the cited extension of the trace theorem. The finite-time compact coverage stated here is a consequence of the same engulfment proof. Neither the trace theorem nor the zero-area boundary theorem has been discharged here, and the range $4<\kappa<8$ remains a separate argument.</p>


## The trace input above eight {#section-generation-update}

<p>For kappa greater than eight, <a href="/tag/MN2A/">MN2A</a> now supplies the trace-generation hypothesis used above, including the unrestricted inverse-map limit on one all-times event. This is sufficient for its use at the swallowing time in the engulfment proof. The kappa-eight trace theorem and the deterministic-time zero-area boundary input remain separate; the latter is still required even when kappa is greater than eight.</p>


## The boundary-area input is supplied {#section-boundary-area-update}

<p><a href="/tag/K8Y5/">K8Y5</a> now proves that the hull boundary has zero planar area at each deterministic positive time, for every positive kappa, including eight. Together with MN2A, this discharges both inputs of ZS6G and R2A0 when kappa is greater than eight; <a href="/tag/BQ8X/">BQ8X</a> states the resulting transience and finite-time compact coverage. At kappa eight the boundary-area input is supplied, while the separate Lawler–Schramm–Werner trace-construction theorem remains an input. The earlier conditional statements above are preserved.</p>
