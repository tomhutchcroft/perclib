---
{
  "id": "sle-force-martingales",
  "title": "SLE force-point martingales",
  "subtitle": "Interior and boundary marks, interaction factors and stopped changes of measure",
  "kind": "method",
  "category": "General theory",
  "summary": "The logarithm of the force-point weight separates into one-point terms and pair interactions. Their drifts combine into the quadratic correction of a stochastic exponential, giving the force law on compact stops.",
  "context": [
    "The base process is ordinary chordal SLE with kappa positive and finitely many distinct marks in the closed upper half-plane, away from the initial driver.",
    "The proof uses deterministic Loewner maps and their boundary derivatives, Itô calculus, Novikov's criterion, Girsanov's theorem and local SDE uniqueness.",
    "All change-of-measure assertions are stopped. No uniform integrability at a collision, terminal conditioning or discrete scaling limit is inferred."
  ],
  "related": ["sle-coordinate-changes", "strip-sle", "continuum-connection-densities"],
  "sourceIds": ["schramm-wilson-coordinate-changes-2005"],
  "aliases": ["Schramm Wilson martingale", "interior force points", "boundary force density"],
  "prototypeUses": []
}
---

## The product weight {#section-product-weight}

<p>Let $\kappa&gt;0$, $U_t=u+\sqrt\kappa B_t$ and $\partial_tg_t(z)=2/(g_t(z)-U_t)$. Fix distinct finite marks $z_1,\ldots,z_n\in\overline{\mathbb H}\setminus\{u\}$ and real weights $\rho_1,\ldots,\rho_n$. Before swallowing any mark, write</p>
<div class="math-display">$$Z_j=g_t(z_j),\quad D_j=Z_j-U_t,\quad J_j=|g_t'(z_j)|,
\qquad L_j=\begin{cases}\operatorname{Im}Z_j,&amp;z_j\in\mathbb H,\\J_j,&amp;z_j\in\mathbb R.\end{cases}$$</div>
<p>For a real unswallowed mark, $g_t'(z_j)$ exists and is positive. Thus every base in the following real powers is positive.</p>

<a id="tag-TSCX" data-assertion="theorem" data-title="The mixed interior and boundary force-point product is a positive local martingale"></a>
<p>Define</p>
<div class="math-display">$$p_j=\frac{(8-2\kappa+\rho_j)\rho_j}{8\kappa},\qquad
q_j=\frac{\rho_j^2}{8\kappa},\qquad
M_t=\prod_jJ_j^{p_j}L_j^{q_j}|D_j|^{\rho_j/\kappa}
\prod_{i&lt;j}\bigl(|Z_i-Z_j|\,|\overline Z_i-Z_j|\bigr)^{\rho_i\rho_j/(4\kappa)}.$$</div>
<p>Then $M$ is a positive local martingale up to the first mark-swallowing time. More precisely, with $a_j=\operatorname{Re}(1/D_j)$ and $A_t=\sum_j\rho_j a_j$,</p>
<div class="math-display">$$\frac{dM_t}{M_t}=-\frac{A_t}{\sqrt\kappa}\,dB_t,
\qquad
\frac{M_t}{M_0}=\exp\left(-\int_0^t\frac{A_r}{\sqrt\kappa}\,dB_r
-\frac1{2\kappa}\int_0^t A_r^2\,dr\right).$$</div>
<p><em>Proof.</em> Put $b_j=\operatorname{Re}(D_j^{-2})$ and $c_j=|D_j|^{-2}$. The one-point differentials are</p>
<div class="math-display">$$d\log|D_j|=-\sqrt\kappa\,a_j\,dB_t+
\left(2-\frac\kappa2\right)b_j\,dt,
\qquad d\log J_j=-2b_j\,dt.$$</div>
<p>For an interior mark, $d\log L_j=-2c_j\,dt$. The drift of its full one-point factor is therefore</p>
<div class="math-display">$$\left[-2p_j+\left(2-\frac\kappa2\right)\frac{\rho_j}{\kappa}\right]b_j-2q_jc_j
=-\frac{\rho_j^2}{4\kappa}(b_j+c_j)
=-\frac{\rho_j^2a_j^2}{2\kappa}.$$</div>
<p>The last equality uses $b_j+c_j=2a_j^2$. For a boundary mark $b_j=c_j=a_j^2$ and $L_j=J_j$, so the same expression follows directly. The Brownian part of the one-point term is $-\rho_j a_j\,dB_t/\sqrt\kappa$.</p>
<p>The interaction terms have finite variation. Subtracting the two Loewner equations gives</p>
<div class="math-display">$$d\log|Z_i-Z_j|=-2\operatorname{Re}\frac1{D_iD_j}\,dt,
\qquad d\log|\overline Z_i-Z_j|=-2\operatorname{Re}\frac1{\overline D_iD_j}\,dt.$$</div>
<p>The sum of these coefficients is $-4a_i a_j$. This remains true when one or both marks are real. Hence the pair factor contributes $-\rho_i\rho_j a_i a_j/\kappa$ to $d\log M$. Summing the diagonal and pair contributions proves</p>
<div class="math-display">$$d\log M_t=-\frac{A_t}{\sqrt\kappa}\,dB_t-
\frac{A_t^2}{2\kappa}\,dt.$$</div>
<p>Exponentiation gives the assertion. All differentiations can first be made on compact subsets of the configuration space, where the relevant gaps, heights and derivatives stay away from zero. Distinct marks remain distinct while the conformal map is defined. Exhausting the pre-swallowing configuration space proves the local statement.</p>

## The weighted law {#section-stopped-weighting}

<a id="tag-NAG9" data-assertion="proposition" data-title="The force-point weight gives the SLE force law on every compact stop"></a>
<p>Let $\sigma$ stop the configuration in a compact subset of its pre-swallowing state space and let $T&lt;\infty$. On $\mathcal F_T$, the density $M_{T\wedge\sigma}/M_0$ defines a probability measure under which, up to $T\wedge\sigma$,</p>
<div class="math-display">$$dU_t=\sqrt\kappa\,d\widetilde B_t+
\sum_j\rho_j\operatorname{Re}\frac1{U_t-Z_j}\,dt,
\qquad dZ_j=\frac2{Z_j-U_t}\,dt.$$</div>
<p>Thus the stopped hulls have the chordal force-point law. No condition on $\sum_j\rho_j$ is needed.</p>
<p><em>Proof.</em> The integrand $\theta_t=-A_t/\sqrt\kappa$ is bounded up to $\sigma$. Novikov's criterion makes the stopped exponential in TSCX a true martingale on $[0,T]$, with initial value one. Girsanov gives the Brownian motion $\widetilde B_t=B_t-\int_0^{t\wedge\sigma}\theta_r\,dr$. Before the stop, substituting this expression into $dU=\sqrt\kappa\,dB$ produces drift $-A_t$, which is exactly the displayed force term. The mark equations are pathwise finite-variation identities and do not change. Local uniqueness identifies the law. Positivity of the density also gives equivalence of the two measures on this stopped interval. This argument does not identify a measure obtained by weighting at an unstopped collision time.</p>
<p>With only real marks, the product simplifies to</p>
<div class="math-display">$$M_t=\prod_jg_t'(z_j)^{\rho_j(\rho_j+4-\kappa)/(4\kappa)}
|Z_j-U_t|^{\rho_j/\kappa}
\prod_{i&lt;j}|Z_i-Z_j|^{\rho_i\rho_j/(2\kappa)}.$$</div>
<p>At $\kappa=6$ with weights $(2,-2)$ this becomes, up to its initial normalization,</p>
<div class="math-display">$$g_t'(z_2)^{1/3}
\left(\frac{|Z_1-U_t|}{|Z_2-U_t|\,|Z_1-Z_2|}\right)^{1/3}.$$</div>
<p>These are exactly the derivative and gap powers in the boundary-density weight of <a href="/articles/continuum-connection-densities/#section-stopped-conditioning">W3QF</a>. The agreement concerns the local density; the conditioning limits in that article still require their stated inputs.</p>

## The first preprint's interaction exponent {#section-first-version}

<p>Theorem 6 in <a href="https://arxiv.org/html/math/0505368v1">the first preprint</a> has $\rho_i\rho_j/(8\kappa)$ as the exponent of the pair product. <a href="https://arxiv.org/html/math/0505368v2">Version 2</a>, <a href="https://arxiv.org/html/math/0505368v3">version 3</a> and the <a href="https://nyjm.albany.edu/j/2005/11-31.pdf">journal paper</a> use $\rho_i\rho_j/(4\kappa)$, as in TSCX. The comparison concerns this display; it is not a diagnosis of an error in the journal formula.</p>

<a id="tag-42Z5" data-assertion="proposition" data-title="Halving the pair exponent leaves a nonzero drift in the first-version force weight"></a>
<p>Let $M^{\mathrm{old}}$ have the same one-point factors as TSCX and pair exponent $\rho_i\rho_j/(8\kappa)$. Its relative drift is</p>
<div class="math-display">$$\frac{dM_t^{\mathrm{old}}}{M_t^{\mathrm{old}}}
=-\frac{A_t}{\sqrt\kappa}\,dB_t+
\frac1{2\kappa}\sum_{i&lt;j}\rho_i\rho_j a_i a_j\,dt.$$</div>
<p>In particular it is not generally a local martingale, even before any collision.</p>
<p><em>Proof.</em> The one-point drift of $\log M$ is unchanged. Each pair now contributes only $-\rho_i\rho_j a_i a_j/(2\kappa)$. The quadratic correction on exponentiating still contributes $A_t^2/(2\kappa)$, leaving the stated remainder. For $\kappa=2$, $u=0$, $(z_1,z_2)=(1+i,2+i)$ and $\rho_1=\rho_2=1$, one has $(a_1,a_2)=(1/2,2/5)$ initially. The relative drift is $1/20$. By continuity it stays positive on a sufficiently small compact stop, contradicting the local-martingale property there. Doubling the pair exponent cancels this remainder exactly.</p>
