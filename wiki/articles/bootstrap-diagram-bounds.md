---
{
  "id": "bootstrap-diagram-bounds",
  "title": "Frequency bounds for the lace diagrams",
  "subtitle": "Uniform control from the bootstrap assumptions",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "The weak bootstrap assumptions make the triangle, unshifted pair and H diagram small. Their coefficient bounds sum absolutely, giving the quantitative input for the improvement argument.",
  "context": [
    "Nearest-neighbour bond percolation on $\\mathbb Z^d$, with $d$ sufficiently large.",
    "Fourier integrals use normalized Haar measure on the torus.",
    "All subcritical Fourier series are absolutely convergent by finite susceptibility."
  ],
  "related": [
    "fourier-bootstrap",
    "weighted-lace-coefficients",
    "infrared-diagrams",
    "completed-fourier-bootstrap"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "Frequency bounds for the lace diagrams"
  ],
  "prototypeUses": []
}
---

## Small triangles under the bootstrap bound {#section-triangles}

<p>Use the notation of <a href="/articles/fourier-bootstrap/">the bootstrap functions</a> and <a href="/articles/weighted-lace-coefficients/">the weighted coefficients</a>. Thus $j=2dp$, $J=jD$, $\widetilde\tau=J*\tau$, $g=1-\widehat D$, and $C(q)=(1-\lambda_p\widehat D(q))^{-1}$. Fix $K\ge1$ and suppose $p<p_c$ and $f(p)\le K$. Constants below depend on $K$, but not on $p$ or $d>6$. The assumptions are</p>
<div class="math-display">$$j\le K,\qquad 0\le\widehat\tau(q)\le KC(q),\qquad
|\Delta_k\widehat\tau(l)|\le200K g(k)V(k,l),$$</div>
<p>where $V(k,l)=C(l-k)C(l)+C(l)C(l+k)+C(l-k)C(l+k)$ and $\Delta_k F(l)=F(l-k)+F(l+k)-2F(l)$.</p>
<a id="tag-54IO" data-assertion="proposition" data-title="A bounded bootstrap function makes the weighted triangle small"></a>
<p>There is $B_K<\infty$ such that</p>
<div class="math-display">$$T\le B_K/d,\qquad 0\le\Delta-1\le\tfrac32T,\qquad
\sup_x(D^{*2}*\tau^{*s})(x)\le K^sK_{1,s}/d\quad(s=1,2,3).$$</div>
<p><em>Proof.</em> The Fourier transform of $D^{*2}*\tau^{*s}$ is nonnegative, so its largest coefficient is at zero by <a href="/tag/ANZF/">ANZF</a>. The bound $\widehat\tau\le KC$ and <a href="/tag/RD3X/">RD3X</a> give the last inequality. The first-step estimate $\tau\le\delta_0+J*\tau$, applied successively, gives</p>
<div class="math-display">$$J*\tau^{*3}\le J+J^{*2}*\tau+J^{*2}*\tau^{*2}+J^{*2}*\tau^{*3}.$$</div>
<p>Taking suprema bounds $T$ by $K/(2d)+K^2\sum_{s=1}^3K^sK_{1,s}/d$. Finally, the nontrivial-triangle argument in <a href="/tag/IT43/">IT43</a> gives $\Delta-1\le3T/2$. All sums are finite here since $p<p_c$.</p>

## The weighted pair {#section-pair}

<p>Write $h_k(x)=1-\cos(k\cdot x)$, $\tau_k=h_k\tau$ and $D_k=h_kD$. In particular, $\widehat\tau_k=-\Delta_k\widehat\tau/2$.</p>
<a id="tag-PEVH" data-assertion="proposition" data-title="The weighted pair is uniformly bounded and its unshifted value is small"></a>
<p>Uniformly in $k$,</p>
<div class="math-display">$$W(0;k)\le\frac{B_K}d g(k),\qquad W(k)\le B_K g(k).$$</div>
<p><em>Proof.</em> For a nearest neighbour $e$, the first-step estimate and 54IO give</p>
<div class="math-display">$$\tau(e)\le(J*\tau)(e)\le jD(e)+j^2(D^{*2}*\tau)(e)\le B_K/d.$$</div>
<p>All nearest-neighbour values agree. Since $\widetilde\tau\le J+J^{*2}*\tau$,</p>
<div class="math-display">$$W(0;k)\le j\tau(e)g(k)+j^2\int\widehat\tau_k(l)\widehat D(l)^2\widehat\tau(l)\,dl.$$</div>
<p>The absolute value of the integral is at most</p>
<div class="math-display">$$100K^2g(k)\int\widehat D(l)^2C(l)V(k,l)\,dl
\le\frac{300K^2K_{1,3}}d g(k),$$</div>
<p>by the three shifted-integral bounds in <a href="/tag/A9W9/">A9W9</a>. This proves the unshifted estimate.</p>
<p>For the supremum over shifts, expand $\widetilde\tau$ and use $h_k(u+v)\le2h_k(u)+2h_k(v)$. Evenness then gives</p>
<div class="math-display">$$W(k)\le2j\left[\sup_y(D_k*\tau*\tau)(y)+\sup_y(D*\tau_k*\tau)(y)\right].$$</div>
<p>The first supremum is at most $K^2g(k)\int C^2$, since $|\widehat D_k|\le\sum D_k=g(k)$. The second is at most $100K^2g(k)\int|\widehat D|CV$. Drop $|\widehat D|\le1$ and apply Hölder with three equal exponents to each product of three translates of $C$. Each integral is at most $\int C^3$. RD3X bounds these unweighted integrals uniformly in $d>6$ and $\lambda_p<1$, proving the result.</p>

## The diagram with two weighted connectors {#section-h}

<a id="tag-L1Y7" data-assertion="proposition" data-title="All three frequency shifts in the H diagram obey the same small bound"></a>
<p>The diagram $H$ defined in <a href="/tag/09JN/">09JN</a> satisfies $H(k)\le B_Kg(k)/d$.</p>
<p><em>Proof.</em> Put $L=\tau*\widetilde\tau=jD*\tau^{*2}$. Expanding the two connectors and summing their final vertex gives</p>
<div class="math-display">$$H(a_1,a_2;k)=\sum_{u,s,t,z}\tau(u)\widetilde\tau(s-a_1)\tau(z-s)\tau(u-z)\tau(t-z)\tau_k(t-u)L(t-s-a_2).$$</div>
<p>Fourier inversion and the sums over these four vertices yield</p>
<div class="math-display">$$\begin{aligned}
H(a_1,a_2;k)=j^2\int &e^{i(l_1\cdot a_1+l_2\cdot a_2)}\widehat D(l_1)\widehat\tau(l_1)^2
\widehat D(l_2)\widehat\tau(l_2)^2\widehat\tau_k(l_3)\\
&\times\widehat\tau(l_1-l_2)\widehat\tau(l_2-l_3)\widehat\tau(l_1-l_3)\,dl_1dl_2dl_3.
\end{aligned}$$</div>
<p>For example, assign frequencies $l_1,l_2,-l_3$ to the factors $\widetilde\tau(s-a_1),L(t-s-a_2),\tau_k(t-u)$. The four vertex constraints give the other four factors displayed above. Each connector contributes one factor $j$; the <a href="/errata/heydenreich-hofstad/#h-diagram-prefactor">provisional normalization entry</a> records this prefactor. Absolute summability justifies the inversion and interchanges.</p>
<p>Taking absolute values bounds the expression by $100K^{10}g(k)$ times the sum of three integrals $I(a,b)$, for $(a,b)=(-k,0),(0,k),(-k,k)$, where</p>
<div class="math-display">$$\begin{aligned}
I(a,b)=\int &|\widehat D(l_1)|C(l_1)^2|\widehat D(l_2)|C(l_2)^2 C(l_3+a)C(l_3+b)\\
&\times C(l_1-l_2)C(l_2-l_3)C(l_1-l_3)\,dl_1dl_2dl_3.
\end{aligned}$$</div>
<p>The same estimate works for arbitrary $a,b$. Write the integrand as $XY$, with</p>
<div class="math-display">$$\begin{aligned}
X&=|\widehat D(l_1)|C(l_1)^2|\widehat D(l_2)|C(l_2)^2C(l_3+b)C(l_1-l_3),\\
Y&=C(l_1-l_2)C(l_2-l_3)C(l_3+a),\qquad
S_\alpha=\int|\widehat D|^\alpha C^3.
\end{aligned}$$</div>
<p>Cauchy–Schwarz in $l_3$ gives $\int X^{3/2}\le S_0S_{3/2}^2$. The change of variables $(l_1,l_2,l_3)\mapsto(l_1-l_2,l_2-l_3,l_3+a)$ preserves Haar measure, so $\int Y^3=S_0^3$. Hölder now gives</p>
<div class="math-display">$$I(a,b)\le S_0^{5/3}S_{3/2}^{4/3}\le S_0^2S_2.$$</div>
<p>The last inequality is Hölder applied to $S_{3/2}\le S_2^{3/4}S_0^{1/4}$. RD3X gives $S_0\le K_{0,3}$ and $S_2\le K_{1,3}/d$. Hence $H\le300K^{10}K_{0,3}^2K_{1,3}g(k)/d$. This treats the two exercise cases as well as the symmetric pair of shifts.</p>

## Summing the coefficients {#section-coefficients}

<a id="tag-6G0E" data-assertion="theorem" data-title="The bootstrap bound gives a small summable lace kernel and a vanishing remainder"></a>
<p>For each fixed $K\ge1$ there are $c_K,d_K<\infty$ such that, if $d\ge d_K$, $p<p_c$ and $f(p)\le K$, then</p>
<div class="math-display">$$\begin{aligned}
\|\Pi^{(N)}_p\|_1&\le(c_K/d)^{\max\{N,1\}},\\
\sum_xh_k(x)\Pi^{(N)}_p(x)&\le g(k)(c_K/d)^{\max\{N-1,1\}}\qquad(N\ge0).
\end{aligned}$$</div>
<p>Consequently the signed sum $\Pi_p=\sum_{N\ge0}(-1)^N\Pi_p^{(N)}$ obeys, after increasing $c_K$,</p>
<div class="math-display">$$\|\Pi_p\|_1\le c_K/d,\qquad
\sum_xh_k(x)|\Pi_p(x)|\le(c_K/d)g(k),\qquad
\sum_x|x|^2|\Pi_p(x)|\le c_K/d.$$</div>
<p>The full subcritical lace equation holds, and</p>
<div class="math-display">$$\widehat\tau_p(k)=\frac{1+\widehat\Pi_p(k)}{1-j\widehat D(k)[1+\widehat\Pi_p(k)]}.$$</div>
<p><em>Proof.</em> 54IO gives $T\le B_K/d$ and $\Delta\le2$ for large $d$, hence $r=2T\Delta\le4B_K/d$. Substitute these and PEVH, L1Y7 into <a href="/tag/SJIL/">SJIL</a>, <a href="/tag/NJT0/">NJT0</a>, IT43 and 09JN. The refined estimate IT43 is needed at $N=1$: its leading term is $W(0;k)=O(g(k)/d)$, whereas the unrefined bound need not be small. For $N\ge2$, the terms in 09JN have respectively the forms</p>
<div class="math-display">$$B_K(2N+1)(N+1)(4B_K/d)^{N-1}g(k),\qquad
\frac{B_K}d(2N+1)(N-1)(4B_K/d)^{N-2}g(k),$$</div>
<p>with constants enlarged as needed. Absorb the polynomial in $N$ into an exponential, for instance using $(2N+1)(N+1)\le12^N$. A larger $c_K$ gives the displayed bounds for every $N$, including the separately estimated orders zero and one.</p>
<p>Choose $d_K$ so that $c_K/d\le1/2$. Geometric summation gives the first two bounds on the signed sum. The coordinate Fatou argument of <a href="/tag/22TW/">22TW</a>, applied to the nonnegative coefficients before alternating them, gives the absolute second moment. Finally <a href="/tag/Z84R/">Z84R</a> bounds the remainder in $\ell^1$ by $j\chi(p)\|\Pi_p^{(M)}\|_1$ for $M\ge1$, which tends to zero at this fixed subcritical parameter. <a href="/tag/I3PK/">I3PK</a> gives the convolution equation and the Fourier quotient, including nonvanishing of its denominator. The case $p=0$ is immediate.</p>
<p>These estimates are conditional on $f(p)\le K$. The <a href="/articles/completed-fourier-bootstrap/">improvement argument</a> removes that condition without assuming the desired infrared theorem.</p>

## Explicit diagram constants {#section-explicit-diagrams}

<p>The preceding estimates can be quantified using the finite walk certificate <a href="/tag/LKS9/">LKS9</a>. We use the weak bound $f(p)\le2$. This choice still leaves room for the continuity argument and reduces the powers of the bootstrap constant in the diagram estimates.</p>

<a id="tag-NOTF" data-assertion="proposition" data-title="Explicit diagram bounds under a weak bootstrap bound of two"></a>
<p>If $d\ge40$, $p<p_c$ and $f(p)\le2$, then, for every frequency $k$,</p>
<div class="math-display">$$\begin{aligned}
T&\le\frac{63}{d},&\qquad \Delta&\le1+\frac{189}{2d},\\
W(0;k)&\le\frac{5300}{d}g(k),& W(k)&\le5800g(k),&
H(k)&\le\frac{487000}{d}g(k).
\end{aligned}$$</div>
<p><em>Proof.</em> The certificate gives $I_{40,6}<669/500$, and RD3X gives dimension monotonicity. On normalized Haar measure, the $L^q$ norms increase with $q$, so for $s=2,3$ and $d\ge40$,</p>
<div class="math-display">$$I_{d,s}\le I_{d,6}^{s/6}<\frac65.$$</div>
<p>For $s=1,2,3$, Cauchy–Schwarz and the return count $\int a^4=3(2d-1)/(8d^3)\le3/(4d^2)$ give</p>
<div class="math-display">$$\int a^2C_\lambda^s
\le\left(\int a^4\right)^{1/2}
\left(\int C_\lambda^{2s}\right)^{1/2}
\le\frac1d\sqrt{\frac34\,\frac{669}{500}}
<\frac{11}{10d}.$$</div>
<p>Here $0\le\lambda\le1$. RD3X's nonnegative return expansion bounds each damped integral by its value at one; $I_{d,2s}\le I_{d,6}^{s/3}\le I_{d,6}$, since $I_{d,6}\ge1$. The fourth-return count follows by separating walks that use one coordinate from those that use two.</p>
<p>Now retain the constants in the proofs of 54IO, PEVH and L1Y7, with $K=2$. The triangle estimate is</p>
<div class="math-display">$$T\le\frac1d\left[1+4(2+4+8)\frac{11}{10}\right]
=\frac{313}{5d}<\frac{63}{d}.$$</div>
<p>IT43 gives the stated bound on $\Delta$. For a nearest neighbour $e$, the first-step estimate gives $\tau(e)\le j/(2d)+j^2\cdot2\cdot11/(10d)$. The unshifted weighted pair in PEVH is therefore bounded by</p>
<div class="math-display">$$\frac{W(0;k)}{g(k)}
\le\frac1d\left[2+16\frac{11}{10}+300\cdot16\frac{11}{10}\right]
=\frac{26498}{5d}<\frac{5300}{d}.$$</div>
<p>This is an inequality of weighted functions, with both sides zero when $g(k)=0$. For the supremum over shifts, the same proof gives</p>
<div class="math-display">$$W(k)\le16\left[\frac65+300\frac65\right]g(k)
=\frac{28896}{5}g(k)<5800g(k).$$</div>
<p>Finally, all three shifted integrals in L1Y7 have the common bound used there. Keeping its two connector masses gives</p>
<div class="math-display">$$H(k)\le\frac{300\cdot2^{10}}d
\left(\frac65\right)^2\frac{11}{10}g(k)
=\frac{2433024}{5d}g(k)<\frac{487000}{d}g(k).$$</div>
<p>No unspecified diagram constant remains in these five estimates.</p>

## An explicit coefficient bound {#section-explicit-coefficients}

<a id="tag-66SP" data-assertion="theorem" data-title="Explicit summable lace bounds under a weak bootstrap bound of two"></a>
<p>Let $d\ge14000$, $p<p_c$ and $f(p)\le2$. Put $\Phi_p(x)=\sum_{N\ge0}\Pi_p^{(N)}(x)$ and $E=50000000$. Then</p>
<div class="math-display">$$\sum_x\Phi_p(x)\le\frac{220}{d},\qquad
\sum_xh_k(x)\Phi_p(x)\le\frac E d g(k),\qquad
\sum_x|x|^2\Phi_p(x)\le\frac E d.$$</div>
<p>The signed sum $\Pi_p$ is absolutely convergent and satisfies the full subcritical lace equation. In particular, its absolute norm, frequency-weighted norm and second moment obey the same respective bounds.</p>
<p><em>Proof.</em> NOTF gives</p>
<div class="math-display">$$T\le\frac{63}{d}\le\frac1{100},\qquad
\Delta\le\frac{11}{10},\qquad
r=2T\Delta\le r_0:=\frac{140}{d}\le\frac1{100}.$$</div>
<p>SJIL, summed over orders, gives</p>
<div class="math-display">$$\sum_x\Phi_p(x)\le T+\frac{\Delta r_0}{1-r_0}
\le\frac1d\left[63+\frac{154}{1-1/100}\right]<\frac{220}{d}.$$</div>
<p>For the weighted sum write $w_0=5300/d$, $w=5800$ and $b=487000/d$. NJT0 and the refined first-order estimate IT43 give a total contribution from orders zero and one at most</p>
<div class="math-display">$$[2w_0+16T\Delta w]g(k)
\le\frac{6441640}{d}g(k).$$</div>
<p>For $N\ge2$, use 09JN. Its first term has coefficient at most $25520N(2N+1)r_0^{N-1}$, because $\Delta w\le6380$ and $2T+(1+j)N\Delta\le4N$. The second has coefficient at most</p>
<div class="math-display">$$\frac1d\frac{121}{100}(3654+487000)(2N+1)(N-1)r_0^{N-2},$$</div>
<p>where $T^2w\le(1/100)(63/d)5800=3654/d$. The two required generating functions are</p>
<div class="math-display">$$\begin{aligned}
\sum_{N\ge2}N(2N+1)r^{N-2}
&=\frac{10-9r+3r^2}{(1-r)^3}\le11,\\
\sum_{N\ge2}(2N+1)(N-1)r^{N-2}
&=\frac{5-r}{(1-r)^3}\le6
\qquad(0\le r\le1/100).
\end{aligned}$$</div>
<p>The identities follow by differentiating the geometric series twice. Their nonnegative coefficients make the sums increasing, so it suffices to check the upper bounds at $r=1/100$. Adding all orders bounds the coefficient of $g(k)/d$ by</p>
<div class="math-display">$$6441640+25520\cdot11\cdot140
+6\frac{121}{100}(3654+487000)
=\frac{1232614701}{25}<50000000.$$</div>
<p>This proves the frequency bound. Set $k=t e_i$, divide by $t^2$ and use Fatou as $t\to0$. Since $g(t e_i)=(1-\cos t)/d$, the bound for the $i$th coordinate moment is $E/d^2$. Summing the $d$ coordinates proves the second-moment bound. All sums here are nonnegative.</p>
<p>For each fixed $p<p_c$, the remainder bound Z84R is at most $j\chi(p)\|\Pi_p^{(M)}\|_1$, which tends to zero by the geometric coefficient bound. I3PK then gives the full equation. At $p=0$ every coefficient vanishes, so that endpoint needs no division by $r$.</p>
