---
{
  "id": "two-point-averages",
  "title": "Two-point functions at large scales",
  "subtitle": "Pointwise decay, Fourier singularities and mass in a box",
  "kind": "method",
  "category": "General theory",
  "summary": "Pointwise power decay and a positive Fourier density each determine the growth exponent of a nonnegative lattice kernel summed over a box. Separately, spatial mixing identifies the large-distance two-point limit when the infinite cluster is unique.",
  "context": [
    "The dimension is a positive integer. Euclidean norm is used in the power laws, and the observation window is the coordinate cube.",
    "The Fourier argument assumes an integrable nonnegative spectral density with the stated coefficients. It does not define a nonsummable Fourier series by unqualified pointwise summation.",
    "Applied to a two-point function, a box sum is the expected number of vertices of the root cluster inside the box; connecting paths may leave the box.",
    "The pointwise and Fourier implications use 0 < alpha < d. Existence or values of critical exponents, the infrared bound and uniqueness of an infinite cluster are separate inputs."
  ],
  "related": ["critical-exponents", "connection-kernels", "infinite-cluster-zero-one", "infinite-cluster-uniqueness"],
  "sourceIds": ["heydenreich-hofstad"],
  "aliases": ["averaged two-point exponent", "Fourier and spatial eta", "supercritical two-point limit"],
  "prototypeUses": []
}
---

## Summing a spatial power law {#section-spatial-power}

<p>For a finite-valued function $a:\mathbb Z^d\to[0,\infty)$, write</p>
<div class="math-display">$$A(R)=\sum_{\|x\|_\infty\le R}a(x),\qquad R\ge1.$$</div>

<a id="tag-J9YA" data-assertion="proposition" data-title="A pointwise lattice power law gives the corresponding box-mass power law"></a>
<p>Fix $0<\alpha<d$. Each of the following implications holds as $R\to\infty$:</p>
<div class="math-display">$$
\begin{aligned}
a(x)&\asymp |x|^{-d+\alpha}
&&\Longrightarrow& A(R)&\asymp R^\alpha,\\
a(x)&=|x|^{-d+\alpha+o(1)}
&&\Longrightarrow& A(R)&=R^{\alpha+o(1)},\\
a(x)&\sim c|x|^{-d+\alpha},\quad c>0
&&\Longrightarrow& A(R)&\sim cR^\alpha
\int_{[-1,1]^d}|u|^{-d+\alpha}\,du.
\end{aligned}
$$</div>
<p>The hypotheses concern all lattice points tending to infinity, not only points along a single ray.</p>
<p><em>Proof.</em> The shell $\|x\|_\infty=n$ has $(2n+1)^d-(2n-1)^d\asymp n^{d-1}$ points, and $n\le|x|\le\sqrt d\,n$ there. Consequently, for every $0<\gamma<d$,</p>
<div class="math-display">$$\sum_{0<\|x\|_\infty\le R}|x|^{-d+\gamma}\asymp
\sum_{1\le n\le R}n^{\gamma-1}\asymp R^\gamma.$$</div>
<p>This proves the first implication. For the second, bound $a(x)$ eventually between $|x|^{-d+\alpha-\varepsilon}$ and $|x|^{-d+\alpha+\varepsilon}$, with $0<\varepsilon<\min(\alpha,d-\alpha)$. Shell summation and then $\varepsilon\downarrow0$ give the logarithmic limit.</p>
<p>For the last implication, fix $\delta>0$ and restrict first to $\delta R<\|x\|_\infty\le R$. The asymptotic for $a$ is uniform on this set, so after division by $R^\alpha$ the sum is a Riemann sum for $c|u|^{-d+\alpha}$ on the cube with its central cube of radius $\delta$ removed. The omitted lattice sum is at most $C(\delta R)^\alpha+O(1)$, by the preceding shell estimate and the eventual power upper bound. The omitted integral is also $O(\delta^\alpha)$. Let $R\to\infty$ and then $\delta\downarrow0$.</p>

## Reading a Fourier singularity through a Gaussian {#section-fourier-power}

<p>Let $m(dk)=(2\pi)^{-d}dk$ on $\mathbb T^d=[-\pi,\pi]^d$, with opposite faces identified. Suppose $\rho\in L^1(m)$ is nonnegative and has Fourier coefficients</p>
<div class="math-display">$$a(x)=\int_{\mathbb T^d}e^{-ik\cdot x}\rho(k)\,m(dk)\in[0,\infty),
\qquad x\in\mathbb Z^d.$$</div>
<p>In particular $a(x)\le a(0)<\infty$. Both positivity assumptions will be used: positivity of $\rho$ controls its Gaussian integral, while positivity of $a$ allows comparison with sharp spatial windows.</p>

<a id="tag-44EA" data-assertion="theorem" data-title="A positive spectral power singularity gives the averaged lattice exponent"></a>
<p>Let $0<\alpha<d$. If $\rho(k)\asymp |k|^{-\alpha}$ for almost every sufficiently small nonzero $k$, then $A(R)\asymp R^\alpha$. If instead $\rho(k)=|k|^{-\alpha+o(1)}$ as $k\to0$, in the sense of almost-everywhere uniform power bounds, then $A(R)=R^{\alpha+o(1)}$.</p>
<p><em>Proof.</em> Smooth the spatial cutoff by setting</p>
<div class="math-display">$$G(R)=\sum_{x\in\mathbb Z^d}a(x)e^{-|x|^2/R^2}
=\int_{\mathbb T^d}\rho(k)P_R(k)\,m(dk),$$</div>
<div class="math-display">$$P_R(k)=(\sqrt\pi R)^d
\sum_{j\in\mathbb Z^d}\exp\left\{-\frac{R^2|k-2\pi j|^2}{4}\right\}.$$</div>
<p>To verify the identity, integrate the periodized Gaussian against $e^{-ik\cdot x}$. The Gaussian integral on $\mathbb R^d$ gives the Fourier coefficient $e^{-|x|^2/R^2}$. These coefficients are summable, so their Fourier series is $P_R$. Fubini is valid since $\rho$ is integrable and the Gaussian coefficients are summable.</p>
<p>On a fixed small ball around zero, the term $j=0$ gives the main Gaussian; the sum of all other terms is $O(R^d e^{-cR^2})$. Outside that ball the whole kernel has this exponential upper bound, with a possibly smaller $c>0$. For $0<\gamma<d$, radial integration gives</p>
<div class="math-display">$$R^d\int_{|k|<r_0}|k|^{-\gamma}
e^{-R^2|k|^2/4}\,dk\asymp R^\gamma.$$</div>
<p>Nonnegativity of $\rho$, its assumed bounds near zero and its finite integral elsewhere therefore yield $G(R)\asymp R^\alpha$ in the first case. In the logarithmic case they yield, for every sufficiently small $\varepsilon>0$ and all large $R$,</p>
<div class="math-display">$$c_\varepsilon R^{\alpha-\varepsilon}
\le G(R)\le C_\varepsilon R^{\alpha+\varepsilon}.$$</div>
<p>It remains to remove the Gaussian. Since its weight is at least $e^{-d}$ on the cube of radius $R$,</p>
<div class="math-display">$$A(R)\le e^dG(R).$$</div>
<p>More generally, if this gives $A(t)\le Ct^q$ for $t\ge1$, then for $L\ge1$ the part outside the cube of radius $LR$ is bounded by dyadic annuli:</p>
<div class="math-display">$$
\sum_{\|x\|_\infty>LR}a(x)e^{-|x|^2/R^2}
\le C R^q\sum_{j\ge0}(2^{j+1}L)^q e^{-4^jL^2}
\le C_q R^q L^q e^{-L^2/2}.
$$</div>
<p>The last bound follows by factoring out $e^{-L^2/2}$ and summing the remaining exponentially decreasing series, uniformly for $L\ge1$.</p>
<p>In the first case take $q=\alpha$ and choose one fixed $L$ large enough that this tail is at most half the lower bound for $G(R)$. Then $A(LR)\ge G(R)/2\ge cR^\alpha$, proving the matching lower bound.</p>
<p>In the logarithmic case use $q=\alpha+\varepsilon$ and $L=R^\delta$, where $\delta>0$. The tail is $o(R^{\alpha-\varepsilon})$, so</p>
<div class="math-display">$$A(R^{1+\delta})\ge \tfrac12 c_\varepsilon R^{\alpha-\varepsilon}$$</div>
<p>for all large $R$. Thus the lower logarithmic growth rate of $A(S)$ is at least $(\alpha-\varepsilon)/(1+\delta)$, while its upper rate is at most $\alpha+\varepsilon$. Let $\varepsilon,\delta\downarrow0$.</p>
<p>For a critical two-point function, take $\alpha=2-\eta$. J9YA and 44EA give the spatial and Fourier implications for the averaged exponent, in their respective stated senses. The Fourier premise includes the coefficient identity above; a formal oscillatory series at a nonzero frequency does not by itself supply that premise. No existence theorem for this spectral density or infrared bound is asserted here.</p>

## Separating finite and infinite connections {#section-infinite-limit}

<p>Consider a translation-invariant independent bond law on $\mathbb Z^d$, $d\ge1$. Let $C_x$ be the cluster of $x$, and put</p>
<div class="math-display">$$\theta=\mathbb P(|C_0|=\infty),\qquad
\tau(x)=\mathbb P(0\leftrightarrow x),\qquad
\tau^{\mathrm f}(x)=\mathbb P(0\leftrightarrow x,\ |C_0|<\infty).$$</div>

<a id="tag-LO35" data-assertion="proposition" data-title="Spatial mixing and uniqueness identify the limiting two-point function"></a>
<p>The finite-cluster term satisfies $\tau^{\mathrm f}(x)\to0$ as $|x|\to\infty$. If there is almost surely at most one infinite cluster, then</p>
<div class="math-display">$$\tau(x)\longrightarrow\theta^2\qquad\text{as }|x|\to\infty.$$</div>
<p><em>Proof.</em> For $r<\|x\|_\infty$,</p>
<div class="math-display">$$\tau^{\mathrm f}(x)\le
\mathbb P\bigl(|C_0|<\infty,\ C_0\not\subseteq[-r,r]^d\bigr).$$</div>
<p>The right side tends to zero as $r\to\infty$: every finite cluster is contained in some cube. Under uniqueness, two vertices in infinite clusters are connected, outside one null event. Hence</p>
<div class="math-display">$$\tau(x)=\tau^{\mathrm f}(x)+
\mathbb P(|C_0|=\infty,\ |C_x|=\infty).$$</div>
<p>The root-infinite events are measurable. Translation mixing from <a href="/tag/WUAF/">WUAF</a>, or its finite-coordinate approximation proof, makes the second term tend to $\theta^2$ along every sequence tending to infinity. This proves the limit. If loop probabilities are not invariant, erase the loops first; none of these graph events changes.</p>
<p>The argument needs no moment bound on a finite cluster and gives no decay rate for its contribution. The <a href="/articles/infinite-cluster-uniqueness/#section-uniqueness">uniqueness theorem</a> is a separate cited input, not a consequence of mixing.</p>
