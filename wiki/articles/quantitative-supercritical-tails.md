---
{
  "id": "quantitative-supercritical-tails",
  "title": "Quantitative supercritical tails",
  "subtitle": "The upper-error balance, marking fields and large-cluster mass",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Retaining the error at the actual subcritical distance gives a controlled upper bound. A logarithmic marking field improves the tail error; a variance estimate then controls large-cluster mass and the largest-component upper tail in a stronger regime.",
  "context": [
    "Finite connected simple vertex-transitive graphs with a strong triangle estimate below an explicit critical reference point.",
    "The upper-error calculation gives a weaker controlled rate than the strongest printed claim; the erratum remains a partial repair.",
    "Concentration of large-cluster mass assumes epsilon^5 N tends to infinity and does not establish a giant-component lower bound."
  ],
  "related": [
    "sharp-upper-field",
    "characteristic-field-growth",
    "finite-supercritical-clusters",
    "hypercube-critical-parameter"
  ],
  "sourceIds": [
    "hofstad-nachmias-hypercube",
    "borgs-chayes-finite-window"
  ],
  "aliases": [
    "optimized supercritical marking field",
    "subcritical extrapolation error",
    "large cluster mass concentration"
  ],
  "prototypeUses": []
}
---

## The subcritical distance in the upper bound {#section-distance}

<p>Consider a sequence of finite connected simple vertex-transitive graphs with $N$ vertices and degree $m\to\infty$. Bonds open independently with probability $p$, and vertices are marked independently with probability $\gamma$. Write</p>
<div class="math-display">$$M(p,\gamma)=\mathbb E_p[1-(1-\gamma)^{|C_o|}],\qquad \eta(p)=\max_{x,y}\{T_p^3(x,y)-\mathbf1_{\{x=y\}}\}.$$</div>
<p>We use the hypotheses of <a href="/tag/6SGU/">6SGU</a>. At a reference parameter $0<p_c\le1/2$, suppose</p>
<div class="math-display">$$H=\chi(p_c)=\lambda N^{1/3}\ge100,\qquad \eta(p_c)\le a\le1/100,\qquad \rho=mp_c\longrightarrow1,$$</div>
<p>where $\lambda>0$ and $a$ are fixed. Assume, for a fixed $C_0\ge0$ and a sequence $a_N\ge0$ tending to zero, that</p>
<div class="math-display">$$\eta(u)\le a_N+C_0\frac{\chi(u)^3}{N}\qquad(0\le u\le p_c).$$</div>
<p>Set $p=p_c+\varepsilon/m\le1/2$, where $\varepsilon>0$, $\varepsilon\to0$ and $Q=\varepsilon^3N\to\infty$. These hypotheses remain in force throughout. Constants in the error bounds depend only on the fixed reference and triangle constants.</p>

<a id="tag-IZ3I" data-assertion="theorem" data-title="The upper field error at an arbitrary admissible subcritical distance"></a>
<p>Let $\delta>0$ satisfy $\delta\to0$ and $Q\delta^3\to\infty$. For every sequence of fields $0<\gamma\to0$,</p>
<div class="math-display">$$M(p,\gamma)\le\left(\varepsilon+\sqrt{\varepsilon^2+2\gamma}\right)\left[1+O\left(\varepsilon+\sqrt\gamma+|\rho-1|+m^{-1}+a_N+\delta+\frac1{Q\delta^3}\right)\right].$$</div>
<p><em>Proof.</em> Put $p_0=p_c-\varepsilon\delta/m$, which is positive eventually. The susceptibility estimate <a href="/tag/F5Y5/">F5Y5</a> gives</p>
<div class="math-display">$$\chi(p_0)\le\frac1{(1-a)\varepsilon\delta},\qquad \eta(p_0)\le a_N+\frac{C_0}{(1-a)^3Q\delta^3}.$$</div>
<p>Also $mp_0=\rho-\varepsilon\delta$ and $p_0=O(m^{-1})$. Set $s=\varepsilon+\sqrt\gamma$ and $\gamma_*=1000s^2$. The reference field bound <a href="/tag/KQN9/">KQN9</a> gives $M(p_0,\gamma_*)\le\sqrt{48\gamma_*}$ once $\gamma_*<1/2$. Thus the coefficient estimate <a href="/tag/14T6/">14T6</a> applies with</p>
<div class="math-display">$$t=\max\{|mp_0-1|,p_0,\eta(p_0),\gamma_*,\sqrt{48\gamma_*}\}=O\left(s+|\rho-1|+m^{-1}+a_N+\frac1{Q\delta^3}\right).$$</div>
<p>In particular $t\to0$, and $M(p_0,z)^2\le Cz$ for $0\le z\le\gamma_*$, with $C=2[1+O(t)]$.</p>
<p>For the inverse-field transport <a href="/tag/HGND/">HGND</a>, write</p>
<div class="math-display">$$h=-\log(1-\gamma),\qquad K=m\log\frac{1-p_0}{1-p}=\varepsilon[1+O(\delta+m^{-1})].$$</div>
<p>The coarse bound <a href="/tag/1T2M/">1T2M</a> gives $M(p,\gamma)\le U=10\sqrt\gamma+96\varepsilon$. Eventually $K\le2\varepsilon$ and $h\le2\gamma$, so $h+KU\le214s^2\le\gamma_*\le-\log(1-\gamma_*)$. The required field range is therefore valid. Transport yields</p>
<div class="math-display">$$M(p,\gamma)\le\frac{CK+\sqrt{C^2K^2+4Ch}}2.$$</div>
<p>Substitute $C=2[1+O(t)]$, the expression for $K$, and $h=\gamma[1+O(\gamma)]$. All terms inside the root are nonnegative, so relative perturbations of these three coefficients give a relative error of the same order, uniformly in $\gamma/\varepsilon^2$. This proves the bound.</p>

## Balancing the two errors {#section-balance}

<a id="tag-YE0X" data-assertion="proposition" data-title="The best balance of displacement and subcritical triangle errors"></a>
<p>For every $Q>0$ and $\delta>0$,</p>
<div class="math-display">$$\delta+\frac1{Q\delta^3}\ge4\,3^{-3/4}Q^{-1/4},$$</div>
<p>with equality exactly at $\delta=(3/Q)^{1/4}$. In particular, choosing $\delta=Q^{-c}$ with $0<c<1/3$ gives the error $Q^{-c}+Q^{3c-1}$, whose slower power has exponent $\min\{c,1-3c\}$.</p>
<p><em>Proof.</em> The derivative of the left side is $1-3/(Q\delta^4)$. It changes sign from negative to positive at the stated point, and the expression diverges at both ends of $(0,\infty)$. Substitution gives the minimum. The exponent formula follows by comparing the two powers.</p>
<p>This optimizes the preceding error bound, not the true error of the percolation model. Choosing $\delta=Q^{-1/4}$ recovers 6SGU. For $c>1/4$, the triangle term cannot be absorbed into $O(Q^{-c})$ by this calculation: at $c=3/10$ it is $Q^{-1/10}$. The source's use of Lemma A.4 at its shifted parameter must retain that term. The <a href="/errata/hofstad-nachmias-hypercube/#upper-extrapolation-error-scale">upper-error entry</a> records the resulting gap in the printed rate, without asserting that the stronger theorem is false.</p>

## Choosing the marking field {#section-tail}

<p>Define</p>
<div class="math-display">$$D_N=\varepsilon+|\rho-1|+m^{-1}+a_N+Q^{-1/4},\qquad \theta_k=\mathbb P_p(|C_o|\ge k).$$</div>
<p>A real cutoff means its ceiling. The following estimate uses a smaller marking field than the earlier square-root choice.</p>

<a id="tag-NIYL" data-assertion="theorem" data-title="An improved marking error and matching supercritical root tails"></a>
<p>For any sequence of real cutoffs $k$ with $L=\varepsilon^2k\to\infty$,</p>
<div class="math-display">$$\theta_k\le2\varepsilon\left[1+O\left(D_N+\frac{\log L}{L}\right)\right].$$</div>
<p>If also $L=o(Q^{1/3})$, then</p>
<div class="math-display">$$\theta_k=2\varepsilon\left[1+O\left(D_N+\frac{\log L}{L}+LQ^{-1/3}\right)\right].$$</div>
<p>In particular, taking $L=Q^{1/6}\sqrt{\log Q}$ gives</p>
<div class="math-display">$$\theta_{\varepsilon^{-2}Q^{1/6}\sqrt{\log Q}}=2\varepsilon\left[1+O\left(\varepsilon+|\rho-1|+m^{-1}+a_N+Q^{-1/6}\sqrt{\log Q}\right)\right].$$</div>
<p><em>Proof.</em> Mark at $\gamma=(\log L)/k=\varepsilon^2(\log L)/L$. Eventually $0<\gamma<1$, $\sqrt\gamma\le\varepsilon$, and $\gamma k=\log L$. Hence</p>
<div class="math-display">$$\theta_k\le\frac{M(p,\gamma)}{1-e^{-\gamma k}}=\frac{M(p,\gamma)}{1-L^{-1}}.$$</div>
<p>The sharp field upper bound 6SGU and $\sqrt{1+2(\log L)/L}=1+O((\log L)/L)$ prove the first assertion.</p>
<p>For the lower bound, use the characteristic threshold $g_*$ and lower value $B_*$ from <a href="/tag/BFAM/">BFAM</a>. The finite tail comparison <a href="/tag/AQPE/">AQPE</a> gives</p>
<div class="math-display">$$\theta_k\ge B_*-212\varepsilon k g_*,\qquad B_*\ge2\varepsilon[1-O(\varepsilon+|\rho-1|+H^{-1})],\qquad g_*=O(\varepsilon/H).$$</div>
<p>Here $H^{-1}=\varepsilon/(\lambda Q^{1/3})=O(\varepsilon)$ and $kg_*=O(LQ^{-1/3})$. This proves the second assertion. For the displayed choice of $L$, both $(\log L)/L$ and $LQ^{-1/3}$ are $O(Q^{-1/6}\sqrt{\log Q})$, which also absorbs $Q^{-1/4}$. The cutoff lies below $N$ eventually, since $k/N=\varepsilon L/Q\to0$.</p>

## The mass in large clusters {#section-mass}

<p>Let $Z_k$ be the number of vertices whose open cluster has size at least $k$, and let $L_1$ be the size of the largest open cluster. The root-tail estimate gives $\mathbb E Z_k=N\theta_k$. A variance bound turns this into concentration if we assume the stronger separation $\varepsilon^5N\to\infty$.</p>

<a id="tag-7Y5K" data-assertion="theorem" data-title="Concentrated large-cluster mass and a largest-component upper bound"></a>
<p>In addition to the standing hypotheses, suppose $W=\varepsilon^5N\to\infty$. Put</p>
<div class="math-display">$$L=\min\{W^{1/4},Q^{1/6}\},\qquad k=\varepsilon^{-2}L,\qquad E_N=D_N+\frac{\log L}{L}+LQ^{-1/3}.$$</div>
<p>Then $E_N\to0$, and eventually</p>
<div class="math-display">$$\mathbb E\left[\left(\frac{Z_k}{2\varepsilon N}-1\right)^2\right]\le212W^{-1/2}+O(E_N^2).$$</div>
<p>For every fixed $t>0$, it follows that</p>
<div class="math-display">$$\mathbb P\bigl(L_1>2(1+t)\varepsilon N\bigr)\le\frac{212W^{-1/2}+O(E_N^2)}{t^2}\longrightarrow0.$$</div>
<p><em>Proof.</em> The choice of $L$ gives $L\to\infty$, $LQ^{-1/3}\le Q^{-1/6}\to0$ and $L^2/W\le W^{-1/2}$. The preceding tail estimate therefore yields $\mathbb E Z_k/(2\varepsilon N)=1+O(E_N)$.</p>
<p>The shared-boundary variance bound <a href="/tag/RD1J/">RD1J</a> and the truncated-field comparison <a href="/tag/E4NT/">E4NT</a> imply</p>
<div class="math-display">$$\operatorname{Var}Z_k\le(1+mpk)N\chi_{<k}(p),\qquad \chi_{<k}(p)\le2kM(p,1/k).$$</div>
<p>Eventually $mp=\rho+\varepsilon<3$ and $k\ge\varepsilon^{-2}\ge1$. The coarse field bound gives $M(p,1/k)\le10k^{-1/2}+96\varepsilon\le106\varepsilon$, so</p>
<div class="math-display">$$\operatorname{Var}Z_k\le848\varepsilon Nk^2,\qquad \frac{\operatorname{Var}Z_k}{4\varepsilon^2N^2}\le212\frac{L^2}{W}\le212W^{-1/2}.$$</div>
<p>Add the squared error of the mean to obtain the first conclusion. Deterministically, $L_1\le\max\{k,Z_k\}$: if a component reaches the cutoff, all its vertices contribute to $Z_k$. Also $k/(\varepsilon N)=\varepsilon L/Q\le\varepsilon Q^{-5/6}\to0$. Thus the event in the second conclusion eventually implies $Z_k/(2\varepsilon N)-1>t$. Apply Markov's inequality to the squared deviation.</p>
<p>The stronger hypothesis is nonvacuous on complete graphs. Take $\lambda=1/10$, choose $p_c$ by $\chi(p_c)=\lambda N^{1/3}$ and set $\varepsilon=N^{-1/6}$. Existence and uniqueness of $p_c$ follow from strict monotonicity of finite susceptibility. The identity <a href="/tag/R2Y7/">R2Y7</a> gives $\eta(u)\le\chi(u)^3/N$, and <a href="/tag/UF7P/">UF7P</a> gives $mp_c\to1$. The reference triangle bound is at most $\lambda^3<1/100$, while $Q=N^{1/2}$ and $W=N^{1/6}$ both diverge. This is a written family satisfying the assumptions.</p>
<p>Concentration of $Z_k$ controls the total mass spread over all large clusters. Neither this argument nor the deterministic comparison gives a lower bound on $L_1$ of order $2\varepsilon N$, or uniqueness of a giant component. Those require an additional argument joining or excluding competing large clusters.</p>

## The source rate and the remaining obligation {#section-source}

<p>In the paper's Lemma A.5, the subcritical displacement is chosen smaller than the target displacement by a factor $Q^{-c}$. Applying Lemma A.4 there introduces $Q^{3c-1}$. The proof reuses the target-scale coefficient instead. Its subsequent deduction of Proposition A.1 also prints a $Q^{-1}$ remainder stronger than the preceding lemma supplies. The <a href="/errata/hofstad-nachmias-hypercube/#upper-extrapolation-error-scale">new provisional entry</a> is labelled “partial fix / statement change”: the leading constant and the bounds above are proved, while those stronger general printed rates remain unproved by this route.</p>
<p>The paper uses $p=p_c(1+e)$; here $\varepsilon=\rho e$. Converting the leading coefficient to $2e$ adds $O(|\rho-1|)$, which has been kept throughout. All source corrections remain provisional pending confirmation. The <a href="/coverage/sources/quantitative-supercritical-tails/">reading map</a> records the checked passages and distinguishes these written deductions from Lean evidence.</p>


## A geometric application on the cube {#section-cube-mass-to-giant}

<p>On $Q_m$, the <a href="/tag/12DQ/">broad-regime sprinkling theorem</a> joins the mass controlled by 7Y5K when $\varepsilon\to0$ and $\log(1/\varepsilon)=o(m^{1/3})$. In this range the cutoff is eventually $\varepsilon^{-3/2}2^{m/6}$ and the number of selected clusters is at most $3(2^m)^{5/6}$ on the mass event. The supply of disjoint sprinkled paths defeats this partition count. The mass estimate alone remains insufficient for other hosts or for the full near-window cube regime.</p>
<p>The cutoff ratio in the proof of 7Y5K should read $k/(\varepsilon N)=L/Q\le Q^{-5/6}\to0$. The extra factor $\varepsilon$ in that earlier displayed calculation is a typographical error; the corrected ratio still tends to zero under exactly the stated hypotheses, so the theorem is unchanged. This is a correction to the wiki calculation, not an erratum in the cited paper.</p>
