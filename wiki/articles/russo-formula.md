---
{
  "id": "russo-formula",
  "title": "Russo's formula",
  "subtitle": "Derivatives, coordinate increments and pivotal events",
  "kind": "theorem",
  "category": "Foundations",
  "summary": "Differentiate a finite product law without dividing by coordinate probabilities, keeping endpoint derivatives and closed pivotality explicit. One-coordinate affinity also applies to arbitrary measurable events, without finite dependence. State-independent pivotality, integrated identities and finite-domain derivatives retain their different hypotheses.",
  "context": [
    "A finite coordinate set $E$ and configurations $\\omega\\subseteq E$.",
    "A product Bernoulli profile $q\\in[0,1]^E$; differentiable real extensions are used to discuss boundary parameters.",
    "Observables do not vary with the parameter. Pivotal-probability formulas require increasing events; signed forced-difference formulas do not."
  ],
  "related": [
    "product-model",
    "harris-inequality",
    "cutoff-families",
    "sharpness"
  ],
  "sourceIds": ["hutchcroft-book", "mathlib", "perclib-finite-polynomial", "perclib-cylinder-russo", "perclib-finite-russo", "perclib-one-coordinate", "perclib-pivotal-algebra", "perclib-integrated-russo", "perclib-finite-volume-russo", "perclib-finite-support-russo", "perclib-russo-associations", "perclib-train10-models-longrange-infinitevolumerusso"],
  "aliases": [
    "Russo",
    "pivotal edge",
    "closed pivotal",
    "influence",
    "profile derivative",
    "intensity derivative"
  ],
  "prototypeUses": [
    "product-model"
  ]
}
---

## Coordinate increments and pivotality {#section-pivotality}

<a id="tag-71GK" data-assertion="definition" data-title="Forced configurations, coordinate increments and pivotality"></a><p>Let $E$ be a finite set of coordinates and identify a configuration with its open set $\omega\subseteq E$. Write $\omega^{e,1}=\omega\cup\{e\}$ and $\omega^{e,0}=\omega\setminus\{e\}$. For $f:\{0,1\}^E\to\mathbb R$, set</p><div class="math-display">$$\Delta_e f(\omega)=f(\omega^{e,1})-f(\omega^{e,0}).$$</div><p>The increment does not depend on the current state of $e$. For an increasing event $A$, call $e$ pivotal when $\omega^{e,1}\in A$ and $\omega^{e,0}\notin A$. Then $\Delta_e\mathbf1_A$ is exactly the pivotal indicator. The <em>closed-pivotal</em> event requires in addition that $e\notin\omega$; these are different events.</p><p>All functions and events on this finite configuration space are measurable. No monotonicity assumption is needed for the observable version of Russo's formula; increasingness is used when replacing a signed increment by a pivotal indicator.</p>

## Differentiating a finite product law {#section-profile}

<a id="tag-7WIO" data-assertion="theorem" data-title="Finite-profile Russo formula for observables"></a><p>For a real profile $q\in\mathbb R^E$, define the polynomial</p><div class="math-display">$$\Phi_f(q)=\sum_{\omega\subseteq E} f(\omega)\prod_{e\in\omega}q_e\prod_{e\notin\omega}(1-q_e).$$</div><p>When $q\in[0,1]^E$, this is $\mathbb E_q[f]$. If each real-valued coordinate $q_e(t)$ is differentiable at $t_0$, then</p><div class="math-display">$$\left.\frac{d}{dt}\Phi_f(q(t))\right|_{t=t_0}=\sum_{e\in E}q'_e(t_0)\,\Phi_{\Delta_e f}(q(t_0)).$$</div><p>This polynomial identity holds even when some coordinates equal zero or one; outside the cube it remains an algebraic identity, not a probability statement.</p><p><em>Proof.</em> Fix $e$ and pair each configuration not containing $e$ with the configuration obtained by opening $e$. If $\eta\subseteq E\setminus\{e\}$ and $w_q^{(-e)}(\eta)$ denotes its product weight on the other coordinates, then</p><div class="math-display">$$\Phi_f(q)=\sum_{\eta\subseteq E\setminus\{e\}}\bigl[q_e f(\eta\cup\{e\})+(1-q_e)f(\eta)\bigr]w_q^{(-e)}(\eta).$$</div><p>Differentiating in $q_e$ gives the weighted sum of $f(\eta\cup\{e\})-f(\eta)$. Since $\Delta_e f$ ignores coordinate $e$, summing its full product weights contributes the factor $q_e+(1-q_e)=1$. Hence $\partial_e\Phi_f=\Phi_{\Delta_e f}$, and the ordinary chain rule gives the result. Every sum is finite, and no coordinate probability has been divided out.</p><p>For a probability family specified only on a parameter set $D$, let $t_0\in D$ be an accumulation point of $D$ and suppose differentiable real extensions $q_e$ agree with that family on $D$ and at $t_0$. The expectation on $D$ then agrees with $\Phi_f(q(t))$, so the same expression is its derivative along $D$ at $t_0$. At an endpoint of an interval, this gives the appropriate one-sided derivative. The polynomial extension need not take values in the probability cube outside $D$.</p>

<p>For completeness, the pairing can be expressed directly in the weights. Write $\sigma_e(\omega)=1$ when $e$ is open and $-1$ when it is closed, and let $w_q^{(-e)}(\omega)$ omit the factor at $e$. Then</p>
<div class="math-display">$$\partial_e w_q(\omega)=\sigma_e(\omega)w_q^{(-e)}(\omega),\qquad
\sum_\omega f(\omega)\sigma_e(\omega)w_q^{(-e)}(\omega)=\Phi_{\Delta_e f}(q).$$</div>
<p>Flipping $e$ is an involution, preserves the deleted weight and interchanges the two signs. The forced increment is unchanged by flipping or forcing $e$. Pairing the two terms therefore gives the second identity, including at endpoint profiles. Identifying binary functions with their open sets turns forcing into insertion or deletion of $e$ and the finite sum into the canonical product integral. This uses no second probability law.</p>
<p>Substituting $q_e(\beta)=1-e^{-\beta J_e}$ into the polynomial derivative gives</p>
<div class="math-display">$$\frac{d}{d\beta}\Phi_f(q(\beta))=\sum_e J_e e^{-\beta J_e}\Phi_{\Delta_e f}(q(\beta))$$</div>
<p>for every real $J_e$ and real $\beta$. Outside parameter sets where all $q_e$ lie in $[0,1]$, this is only a polynomial-composed-with-exponentials identity. For an increasing event, the same algebra replaces its forced increment by its pivotal indicator even there, but its weighted sum need not be a probability. With no coordinates the sum is empty and the derivative is zero. A one-coordinate open indicator has polynomial expectation $q_e$, so its homogeneous derivative is one and its intensity derivative at zero is $J_e$, without any endpoint division.</p>

## Increasing events and homogeneous parameters {#section-events}

<a id="tag-WU9R" data-assertion="corollary" data-title="Finite-profile Russo formula for increasing events"></a><p>Under the differentiability assumptions above, if $A$ is increasing and $q(t_0)\in[0,1]^E$, then</p><div class="math-display">$$\left.\frac{d}{dt}\Phi_{\mathbf1_A}(q(t))\right|_{t=t_0}=\sum_{e\in E}q'_e(t_0)\,\mathbb P_{q(t_0)}(e\text{ is pivotal for }A).$$</div><p>This follows by substituting $f=\mathbf1_A$. It is also the derivative of the event probability on any parameter domain on which $q(t)$ is a probability profile. The derivatives $q'_e(t_0)$ may have either sign.</p><a id="tag-4IHK" data-assertion="corollary" data-title="Homogeneous Russo formula including endpoint derivatives"></a><p>For the homogeneous family $q_e=p$,</p><div class="math-display">$$\frac{d}{dp}\mathbb P_p(A)=\sum_{e\in E}\mathbb P_p(e\text{ is pivotal for }A),\qquad 0&lt;p&lt;1.$$</div><p>The same right-hand side gives the right derivative at $p=0$ and the left derivative at $p=1$. These are also the ordinary derivatives of the real polynomial extension. For the single-coordinate event $A=\{e\text{ open}\}$, pivotality occurs for every configuration, so the derivative is one, including at both endpoints. A formula that conditions on a positive-probability open or closed state would obscure precisely these boundary cases.</p>

## Intensity parameters and closed pivotality {#section-intensity}

<a id="tag-IENL" data-assertion="corollary" data-title="Intensity Russo formula and closed-pivotal form"></a><p>Let $J_e\geq0$ be finite and put $q_\beta(e)=1-e^{-\beta J_e}$ for finite $\beta\geq0$. For an increasing event $A$ depending on these finitely many coordinates,</p><div class="math-display">$$\frac{d}{d\beta}\mathbb P_\beta(A)=\sum_{e\in E}J_e e^{-\beta J_e}\,\mathbb P_\beta(e\text{ is pivotal for }A)=\sum_{e\in E}J_e\,\mathbb P_\beta(e\text{ is closed pivotal for }A).$$</div><p>At $\beta=0$ the probability derivative is taken from the right. The first equality follows from $q'_\beta(e)=J_e e^{-\beta J_e}$. For the second, pivotality depends only on the other coordinates and is therefore independent of the state of $e$, giving</p><div class="math-display">$$\mathbb P_\beta(e\text{ is closed pivotal})=(1-q_\beta(e))\mathbb P_\beta(e\text{ is pivotal})=e^{-\beta J_e}\mathbb P_\beta(e\text{ is pivotal}).$$</div><p>Thus the exponential factor may be absorbed into <em>closed</em> pivotality, but it must not be discarded while retaining the state-independent pivotal event.</p><p>For an arbitrary real observable on the same finite space, the same independence yields the intensity form:</p><div class="math-display">$$\frac{d}{d\beta}\mathbb E_\beta[f]=\sum_{e\in E}J_e\,\mathbb E_\beta\bigl[f(\omega\cup\{e\})-f(\omega)\bigr].$$</div><p>Indeed, the difference in this expectation is $\mathbf1_{\{e\text{ closed}\}}\Delta_e f$, whose expectation is $(1-q_\beta(e))\mathbb E_\beta[\Delta_e f]$. This explains why the intensity formula and the profile derivative have different-looking coefficients.</p>

## Cylinder events in an arbitrary ambient product {#section-cylinder}

<a id="tag-XU3W" data-assertion="theorem" data-title="Finite-cylinder Russo with signed forced differences and arbitrary ambient coordinates"></a>
<p>Let $I$ be any index set, let $F\subseteq I$ be finite, and let $A=\{\omega:\omega\cap F\in\mathcal B\}$ for some $\mathcal B\subseteq2^F$. Let $p(t)\in[0,1]^I$ be a probability profile on a parameter domain $D$, with $t_0\in D$ an accumulation point of $D$. For each $e\in F$, suppose a real function $q_e$ is differentiable at $t_0$ and agrees with $p_e$ on $D$. Then the derivative along $D$ is</p>
<div class="math-display">$$\left.\frac{d}{dt}\mathbb P_{p(t)}(A)\right|_{t=t_0,\ t\in D}=\sum_{e\in F}q'_e(t_0)\left[\mathbb P_{p(t_0)}(\omega\cup\{e\}\in A)-\mathbb P_{p(t_0)}(\omega\setminus\{e\}\in A)\right].$$</div>
<p>No regularity is assumed for coordinates outside $F$, and their forced differences vanish. If $A$ is increasing, each bracket equals the probability that forcing $e$ open makes $A$ hold and forcing it closed makes $A$ fail. More generally, this bracket-to-pivotal identity holds for every increasing measurable event on $2^I$, even without finite dependence; only the derivative formula requires the cylinder assumption here.</p>
<p><em>Proof.</em> By the <a href="/tag/ZNMQ/">finite restriction law</a>, the event probability is the finite polynomial for $\mathbf1_{\mathcal B}$ evaluated at $p|_F$. On $D$ it agrees with the same polynomial evaluated at the differentiable real extensions. Apply <a href="/tag/7WIO/">7WIO</a> and identify the expected indicator increment with the displayed difference of probabilities. Restriction commutes with inserting or removing a coordinate of $F$. For $e\notin F$, neither operation changes $\omega\cap F$, proving the vanishing claim.</p>
<p>For any increasing measurable event, the forced-closed event is contained in the forced-open event. Both are measurable because the coordinate-forcing maps are measurable. Subtracting their finite probabilities gives the probability of their difference, exactly the state-independent pivotal event. This argument uses neither countability nor division by a coordinate probability.</p>
<p>For finite nonnegative $J_e$ and $p_e(\beta)=1-e^{-\beta J_e}$ on $F$, take $D=[0,\infty)$ and $q'_e(\beta)=J_e e^{-\beta J_e}$. The signed formula applies to any cylinder event, including at zero with a right derivative. Outside $F$, the profile may vary arbitrarily with $\beta$. In the increasing case this gives the pivotal form; the closed-pivotal conversion is the one in <a href="/tag/IENL/">IENL</a>.</p>
<p>An empty block gives a constant event probability and an empty derivative sum. For a decreasing single-coordinate event, the bracket is $-1$, so its derivative is $-q'_e(t_0)$; replacing signed differences by positive pivotal probabilities would be wrong. The point of the real extensions is only to differentiate the finite polynomial. They need not be probability profiles away from $D$.</p>

## Finite dependence and infinite volume {#section-scope}

<p>The formulas also apply to a cylinder observable in an infinite product space: choose a finite set of coordinates on which it depends and integrate out the rest. They do not by themselves apply to an arbitrary infinite-volume event. Limits of event probabilities need not permit differentiation under the limit, and a formal infinite pivotal sum still needs a convergence argument.</p><p>For the <a href="#/cutoff-families">integrated cutoff family</a>, the already recorded finite-edge identity is the profile formula with its actual derivative $q'_{\beta,r}(e)$. Corners in the cutoff parameter require one-sided or almost-everywhere statements. Replacing that family by a hard truncation, or differentiating an infinite-volume probability merely because it is monotone, would require a different argument.</p>


## Varying one coordinate in an arbitrary product {#section-one-coordinate}

<p>The finite-dependence assumption can be dropped when only one coordinate varies. Let $I$ be any index set, fix $e\in I$ and $q\in[0,1]^I$, and write $q^{e,t}$ for the profile obtained by replacing $q_e$ by $t$. Put $T_e^1\omega=\omega\cup\{e\}$ and $T_e^0\omega=\omega\setminus\{e\}$.</p>

<a id="tag-AQDI" data-assertion="theorem" data-title="A measurable event is affine in a single coordinate without finite dependence"></a>
<p>For $t\in[0,1]$, the following identities hold as probability measures:</p>
<div class="math-display">$$(T_e^b)_*\mathbb P_q=\mathbb P_{q^{e,b}}\quad(b=0,1),\qquad
\mathbb P_{q^{e,t}}=(1-t)\mathbb P_{q^{e,0}}+t\mathbb P_{q^{e,1}}.$$</div>
<p>Consequently, for every measurable $A\subseteq2^I$, setting $a_b=\mathbb P_q(T_e^b\omega\in A)$ gives</p>
<div class="math-display">$$\mathbb P_{q^{e,t}}(A)=a_0+t(a_1-a_0).$$</div>
<p>The coefficients do not depend on $q_e$. If $A$ is increasing, then</p>
<div class="math-display">$$a_1-a_0=\mathbb P_q\bigl(T_e^1\omega\in A,\ T_e^0\omega\notin A\bigr),$$</div>
<p>the probability that $e$ is pivotal, with its own state unspecified. The index set need not be countable, and the event need not depend on finitely many coordinates.</p>
<p><em>Proof.</em> Forcing a coordinate is measurable: every output coordinate is either unchanged or constant. On an all-open cylinder with finite coordinate set $F$, forcing $e$ open removes its requirement if $e\in F$, while forcing it closed makes that cylinder impossible. If $e\notin F$, neither operation changes the cylinder. The <a href="/tag/ZNMQ/">finite-cylinder product formula</a> therefore gives the two pushforward identities.</p>
<p>For the mixture, if $e\in F$ its all-open probability is $t\prod_{i\in F\setminus\{e\}}q_i$; if $e\notin F$ it is $\prod_{i\in F}q_i$. These are exactly the cylinder probabilities under $\mathbb P_{q^{e,t}}$. Finite all-open cylinders form a pi-system generating the coordinate sigma-algebra, so uniqueness of probability measures proves both identities on that sigma-algebra. Evaluating the mixture on $A$ gives affinity. Increasingness gives $\{T_e^0\omega\in A\}\subseteq\{T_e^1\omega\in A\}$; subtracting the two finite probabilities gives the pivotal formula.</p>
<p>The affine expression has derivative $a_1-a_0$ on $(0,1)$ and the corresponding one-sided derivatives at zero and one. In particular its absolute slope is at most one. For a decreasing event the slope is nonpositive, and for a general event it is a signed difference. None of these identities divides by $q_e$ or $1-q_e$, so deterministic endpoint coordinates are included. They are forcing identities, not conditional-probability formulas at a potentially null coordinate outcome. The measure mixture also determines outer measures of arbitrary subsets; evaluating it there does not turn a nonmeasurable set into an event.</p>
<p>On a countable bond vertex set, take $A=\{x\leftrightarrow y\}$. The two-point function is affine in any one unordered-pair probability, with the connection-pivotal slope. If the pair is diagonal, inserting or deleting it leaves the simple open graph unchanged, so its slope is zero; the same holds for every pair when $x=y$. On a graph consisting of one edge joining distinct endpoints, the slope is one. These statements do not require the other bond probabilities to be equal.</p>
<p>Single-coordinate affinity gives no infinite sum rule when all coordinates move. For example, on $I=\mathbb N$ the event that infinitely many coordinates are open is unchanged by forcing any one coordinate, so every such slope is zero. Under a homogeneous profile $p$, however, its probability is zero at $p=0$ and one at every $p&gt;0$: for each $N$, the probability that all coordinates after $N$ are closed is the limit of $(1-p)^m$, hence zero. Thus simultaneous variation can even destroy continuity at the endpoint. This example is an additional deduction illustrating the distinction.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-coordinate/">fourteen-contract inventory</a> separates the measure identities, measurable-event formulas, pivotal slope and bond application. The derivative and Lipschitz observations are immediate consequences of affinity; no infinite-volume Russo sum is inferred.</p>


## Pivotality and the tested coordinate {#section-pivotal-decomposition}

<p>For any measurable $A\subseteq2^I$, write $\Pi_e^+(A)=\{\omega:\omega^{e,1}\in A,\ \omega^{e,0}\notin A\}$. For increasing $A$ this is the pivotal event used above. For a general event it records only a change from failure to success when $e$ is opened; a change in the opposite direction contributes negatively to the signed increment.</p>

<a id="tag-XRSL" data-assertion="proposition" data-title="Pivotal decomposition and the open-pivotal count form of Russo"></a>
<p>The event $\Pi_e^+(A)$ is measurable and determined by $I\setminus\{e\}$. Thus, for any coordinate set $I$ and any product profile,</p>
<div class="math-display">$$\mathbb P_q(\Pi_e^+(A),\ e\in\omega)=q_e\mathbb P_q(\Pi_e^+(A)),\qquad
\mathbb P_q(\Pi_e^+(A),\ e\notin\omega)=(1-q_e)\mathbb P_q(\Pi_e^+(A)).$$</div>
<p>If $A$ is increasing, it has the disjoint decomposition</p>
<div class="math-display">$$A=\{\omega:\omega^{e,0}\in A\}\ \dot\cup\ \bigl(\Pi_e^+(A)\cap\{e\in\omega\}\bigr).$$</div>
<p>On a finite coordinate set $E$, put $N_A(\omega)=\sum_e\mathbf1_{\Pi_e^+(A)}(\omega)$ and $N_A^{\mathrm{open}}(\omega)=\sum_e\mathbf1_{\Pi_e^+(A)}(\omega)\mathbf1_{\{e\in\omega\}}$. Then, even without increasingness,</p>
<div class="math-display">$$N_A^{\mathrm{open}}=\mathbf1_A N_A,\qquad
\mathbb E_qN_A^{\mathrm{open}}=\sum_e q_e\mathbb P_q(\Pi_e^+(A)).$$</div>
<p>For increasing $A$ and a homogeneous parameter $0&lt;p\leq1$, this gives</p>
<div class="math-display">$$\frac{d}{dp}\mathbb P_p(A)=\frac1p\mathbb E_pN_A^{\mathrm{open}}
=\frac1p\mathbb E_p[\mathbf1_A N_A],$$</div>
<p>with the left derivative at $p=1$. The expression divided by $p$ is not asserted at $p=0$; the undivided pivotal-probability sum in <a href="/tag/4IHK/">4IHK</a> still gives the right derivative there.</p>
<p><em>Proof.</em> Forcing maps are measurable by <a href="/tag/AQDI/">AQDI</a>. Their two tests depend only on $\omega\setminus\{e\}$, so changing the current state of $e$ leaves $\Pi_e^+(A)$ unchanged. The factorization follows from <a href="/tag/FH29/">measurable determination by disjoint coordinate blocks</a>. It uses neither countability nor division by an endpoint probability.</p>
<p>If $A$ holds and still holds after closing $e$, the configuration is in the first part of the decomposition. Otherwise $e$ must be open and pivotal. Conversely, either part implies $A$ by increasingness; the two parts are disjoint because pivotality requires the forced-closed test to fail. On $\Pi_e^+(A)$ itself, $A$ holds exactly when $e$ is open, without any increasingness assumption. Sum this identity over $E$ and integrate the coordinate factorizations. The homogeneous derivative formula now follows from 4IHK.</p>
<p>The source's finite weighted-sum identity is also algebraic: if a real observable $g$ ignores coordinate $e$, its weighted sum with the open-coordinate indicator is $q_e$ times its full weighted sum, even at real profiles outside the probability cube. Pair the two states of $e$; their weights sum to one. Outside the cube this is an identity of finite sums, not a probability claim. The arbitrary-index probability factorizations above use the separately established block-independence theorem and are an extension of the source's finite-coordinate formula.</p>
<p>For a connection event, <a href="/tag/61PY/">61PY</a> bounds the pivotal count on the event by the open-graph distance. It does not bound the number of closed pivotal pairs on a configuration where the endpoints are disconnected. For a single open-coordinate event, $N_A^{\mathrm{open}}=\mathbf1_A$, so the divided formula gives one for every $p&gt;0$, including its left-derivative interpretation at $p=1$.</p>

## Integrating along a finite profile curve {#section-integrated-russo}

<a id="tag-VYTC" data-assertion="theorem" data-title="Integrated Russo along a finite continuously differentiable profile curve"></a>
<p>Let $E$ be finite, let $A\subseteq2^E$ be increasing, and let each $q_e:\mathbb R\to\mathbb R$ be continuously differentiable. Suppose $q(t)\in[0,1]^E$ for every $t$ between $a$ and $b$, including the endpoints. Then</p>
<div class="math-display">$$\mathbb P_{q(b)}(A)-\mathbb P_{q(a)}(A)
=\int_a^b\sum_{e\in E}q'_e(t)\mathbb P_{q(t)}(\Pi_e^+(A))\,dt.$$</div>
<p>The integral is oriented, so this includes $b&lt;a$ and the zero-length interval. The real curve need not remain in the probability cube outside the integration interval.</p>
<p><em>Proof.</em> Compose the finite expectation polynomial with $q(t)$. By <a href="/tag/7WIO/">the profile derivative formula</a>, its derivative is the displayed sum, with pivotal weighted sums in place of probabilities before restricting to the interval. Every weighted sum is a polynomial in the finite profile, so the derivative is continuous. The fundamental theorem of calculus therefore applies. On the integration interval the weights are the product probabilities, giving the stated formula, including the two endpoint values.</p>
<p>For two arbitrary probability profiles $p,r$, apply this to $q_e(t)=(1-t)p_e+tr_e$ on $[0,1]$:</p>
<div class="math-display">$$\mathbb P_r(A)-\mathbb P_p(A)
=\int_0^1\sum_e(r_e-p_e)\mathbb P_{(1-t)p+tr}(\Pi_e^+(A))\,dt.$$</div>
<p>The profiles need not be ordered. When they are ordered every coefficient is nonnegative; otherwise the coefficients keep their signs. For homogeneous endpoints $p_1,p_2\in[0,1]$, the formula reduces to the integral from $p_1$ to $p_2$ of the sum of pivotal probabilities. In contrast to the open-pivotal expression divided by $p$, this integrand is defined at zero without a limiting convention. For the event that two specified coordinates are open, it gives $p_2^2-p_1^2=\int_{p_1}^{p_2}2t\,dt$.</p>
<p>Empty or full events have no pivotal coordinates, and an empty coordinate set gives an empty sum. These formulas concern a finite coordinate family. They do not justify integrating an unproved infinite pivotal series or interchanging a volume limit with differentiation.</p>

## Russo inside a finite vertex domain {#section-finite-domain-russo}

<a id="tag-6JBS" data-assertion="theorem" data-title="Finite-domain intensity derivatives retain the closed-edge factor and ignore loops"></a>
<p>Let $S\subseteq V$ be finite, let $x,y\in S$, and let $J_e\geq0$ be finite pair intensities. The ambient vertex set may be arbitrary. For $\beta\geq0$, put $q_\beta(e)=1-e^{-\beta J_e}$ and let $\tau^S_\beta(x,y)$ be the probability of connection inside $S$. Writing $\binom S2$ for the unordered pairs of distinct vertices of $S$,</p>
<div class="math-display">$$\frac{d}{d\beta}\tau^S_\beta(x,y)
=\sum_{e\in\binom S2}J_e e^{-\beta J_e}
\mathbb P_\beta\bigl(e\text{ is pivotal for }x\leftrightarrow_S y\bigr).$$</div>
<p>At zero the derivative is from the right. In particular, with $L_S=\sum_{e\in\binom S2}J_e$,</p>
<div class="math-display">$$0\leq\frac{d}{d\beta}\tau^S_\beta(x,y)\leq L_S.$$</div>
<p>The finite-domain susceptibility $\chi^S_\beta(x)=\sum_{y\in S}\tau^S_\beta(x,y)$ has derivative obtained by summing the displayed formula over $y\in S$.</p>
<p><em>Proof.</em> Internal connection is increasing and determined by the finitely many pairs with both endpoints in $S$. Apply <a href="/tag/XU3W/">finite-cylinder Russo</a> with derivative $J_e e^{-\beta J_e}$. A diagonal pair changes no simple-graph adjacency, so it is never pivotal for any event determined by the simple open graph. A pair outside $S$ cannot change an internal connection. Thus only $\binom S2$ remains. Each probability and exponential factor lies in $[0,1]$, giving the derivative bounds. Finally, the susceptibility is a finite sum of these differentiable probabilities.</p>
<p>This argument needs no ambient countability and no bound on the total intensity outside $S$. Forcing an internal pair commutes with restriction to $S$, so the pivotal event can equally be read in the restricted product law. The exponential factor may be absorbed into the probability of a <em>closed</em> pivotal pair by XRSL, as in <a href="/tag/IENL/">IENL</a>; it cannot be dropped from a state-independent pivotal probability.</p>
<p>Consequently the internal two-point function is nondecreasing and $L_S$-Lipschitz on $[0,\infty)$, by integrating its derivative. The Lipschitz estimate is an additional consequence of the source derivative bound. For a single edge of intensity $J$, the connection probability is $1-e^{-\beta J}$ and its derivative is $Je^{-\beta J}$; positive diagonal intensities do not affect either expression. For $x=y$, the probability is one and its derivative is zero. A singleton domain has susceptibility one.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-pivotal-russo/">43-contract inventory</a> keeps deterministic pivotal algebra, realized-connection geometry, finite integrated identities and finite-domain intensity differentiation separate. The constants $L_S$ can grow without bound along an exhaustion, so these finite formulas alone give no derivative formula for the limiting susceptibility or two-point function.</p>


## Expressing finite dependence by restriction {#section-finite-restriction}

<p>The cylinder hypothesis in <a href="/tag/XU3W/">XU3W</a> can equivalently be written without choosing a separate event on the finite space. For a finite $F\subseteq I$, suppose</p>
<div class="math-display">$$\omega\in A\quad\Longleftrightarrow\quad\omega\cap F\in A
\qquad\text{for every }\omega\subseteq I.$$</div>
<p>Set $\mathcal B=\{\eta\subseteq F:\eta\in A\}$. Then $A$ is precisely the inverse image of $\mathcal B$ under restriction to $F$, so it is measurable and $\mathbb P_p(A)=\mathbb P_{p|_F}(\mathcal B)$. No ambient measurability or countability assumption has to be supplied separately: the finite restriction is measurable and every subset of $2^F$ is measurable.</p>
<p>For $e\in F$, inserting or deleting $e$ commutes with intersection with $F$. Applying the same equivalence to the two forced configurations shows that $\Pi_e^+(A)$ also depends only on $F$. For $e\notin F$, the two tests agree, so there is no pivotality. Consequently the intensity formula in <a href="/tag/IENL/">IENL</a>, with its sum restricted to $F$, applies to every increasing event satisfying the displayed condition. Coordinates outside $F$ may vary arbitrarily with the parameter. This is the restriction argument behind the finite-support source theorem, rather than a new infinite-volume derivative formula.</p>
<p>The <a href="/coverage/sources/perclib-5d6efa8-finite-russo/">finite-Russo inventory</a> lists the polynomial pairing lemmas, the probability transport and both forms of finite support. The formal source allows a derivative predicate on an arbitrary parameter set, even at an isolated point; the article assumes an accumulation point when speaking of a uniquely determined derivative. A nontrivial interval endpoint supplies that condition and gives the corresponding one-sided derivative.</p>


## An infinite-volume formula for bounded cluster observables {#section-infinite-cutoff-source}

<p>The <a href="/coverage/sources/perclib-dfbc5b4-fourier-russo/">infinite-volume source</a> supplies a sufficient domination argument for a family of countable bond models. Let $F:\mathbb N\cup\{\infty\}\to\mathbb R$ satisfy $|F|\leq m$ and be constant above some finite threshold. Write $\psi(r)=\mathbb E_r F(|K_o|)$ and</p>
<div class="math-display">$$\Delta_e(r)=\mathbb E_r\left[F(|K_o(\omega\cup\{e\})|)-F(|K_o(\omega\setminus\{e\})|)\right].$$</div>
<p>Suppose each coordinate probability $q_r(e)$ is continuous on an open interval $I$ and has derivative $c_r(e)$ outside a countable exceptional set, which may depend on $e$. Assume also, uniformly over $r\in I$ and finite sets $S$ of pairs,</p>
<div class="math-display">$$\sum_{e\in S}|c_r(e)|\,\mathbb P_r(e\text{ has an endpoint in }K_o)\leq D&lt;\infty.$$</div>
<p>Then, for $[s,t]\subset I$,</p>
<div class="math-display">$$\psi(t)-\psi(s)=\int_s^t\sum_e c_r(e)\Delta_e(r)\,dr,
\qquad\left|\sum_e c_r(e)\Delta_e(r)\right|\leq2mD.$$</div>
<p>To prove this, exhaust the pairs by finite sets. The restricted cluster functional eventually equals the full one for each configuration: finitely many witnessing paths determine a finite cluster, or connect enough vertices to reach the level where $F$ is constant. This also applies after forcing a fixed pair open or closed. Bounded convergence therefore gives convergence of each pivotal expectation.</p>
<p>A forced pair cannot change the root cluster unless it touches that cluster. Consequently $|\Delta_e(r)|\leq2m\mathbb P_r(e\text{ touches }K_o)$, with the same bound for every restricted functional. At fixed $r$, the assumed finite-sum bound gives a summable majorant for the edge series. The resulting finite-window fluxes are uniformly bounded by $2mD$. Integrate their finite Russo formulas outside the countable union of exceptional parameters, then apply dominated convergence to the edge sums and the parameter integrals. The identity also makes $\psi$ Lipschitz. Continuity of the infinite flux is an additional step before claiming a derivative at a specified parameter.</p>
<p>For a radial soft cutoff on $\mathbb Z^d$, assume $N(z)\geq\kappa\|z\|_\infty$ with $\kappa&gt;0$, and let $K$ be decreasing and continuously differentiable on positive radii. Fix finite $\beta\geq0$ and an upper scale $R$ with $\chi_R(o)&lt;\infty$. On an interval bounded away from zero, choose $L$ bounding $|K'|$ up to $R$. The edge derivative is</p>
<div class="math-display">$$c_r(\{x,y\})=\mathbf1_{\{x\ne y,\ N(x-y)&lt;r\}}\,\beta(-K'(r))e^{-\beta J_r(x,y)}.$$</div>
<p>There are finitely many allowed displacement vectors below $R$. Summing the two possible endpoint connections gives the admissible bound $D=2\beta L\,|\{z\ne0:N(z)&lt;R\}|\,\chi_R(o)$. Monotonicity compares all lower-scale touching probabilities with those at $R$.</p>
<p>The source next proves continuity of each pivotal expectation by treating a forced pair as a probability update. Forcing it open enlarges the root cluster only into the two endpoint clusters; translation invariance controls all three means by $\chi_R(o)$. On an interval containing no lattice distance $N(z)$, the derivative indicators are constant and the same summable bound gives continuity of the flux. The integrated identity then yields $\psi'(r)$ equal to that flux at every $0&lt;r&lt;R$ which is not a lattice distance.</p>
<p>This removes a separately assumed locally uniform limit of finite-window fluxes under the stated cutoff hypotheses. It applies to bounded capped moments and finite size-tail indicators. Removing the cap, handling a distance corner, or taking an upper scale with infinite susceptibility requires further arguments; none follows just from this formula.</p>
