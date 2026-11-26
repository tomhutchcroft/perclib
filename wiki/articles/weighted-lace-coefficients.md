---
{
  "id": "weighted-lace-coefficients",
  "title": "Weighted lace-coefficient bounds",
  "subtitle": "Two-sided summation of the diagram chain",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "Summing a marked diagram from both ends gives the all-order Fourier-weighted bound. Removing the trivial triangles sharpens the first coefficient; geometric summation then controls absolute second moments.",
  "context": [
    "Nearest-neighbour bond percolation on $\\mathbb Z^d$, $d\\ge1$, with finite clusters almost surely.",
    "The kernels A, B_1, B_2 and the quantities Delta, T, W are those of Bounding the lace coefficients.",
    "All sums below are nonnegative before the final signed lace sum."
  ],
  "related": [
    "lace-coefficient-diagrams",
    "signed-kernel-moments",
    "lace-expansion"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "weighted lace expansion",
    "reversed diagram chain",
    "refined first lace coefficient"
  ],
  "prototypeUses": []
}
---

## Summation from either end {#section-reverse}

<p>Keep $\tau,J,j,\widetilde\tau,\Delta,T,A,B_1,B_2$ from <a href="/tag/SJIL/">SJIL</a>, and write $r=2T\Delta$. Denote the two terms of $B_2$ by $B_2^{(1)},B_2^{(2)}$. Assume $T,\Delta<\infty$. Starting with $F_0(s,t)=G_0(s,t)=A(0,s,t)$, define</p>
<div class="math-display">$$\begin{aligned}
F_m(s,t)&=\sum_{a,b,u,v}F_{m-1}(a,b)B_1(a,b,u,v)B_2(u,v,s,t),\\
G_m(u,v)&=\sum_{s,t,a,b}B_2(u,v,s,t)B_1(s,t,a,b)G_{m-1}(a,b).
\end{aligned}$$</div>
<a id="tag-RZML" data-assertion="proposition" data-title="Forward and reversed diagram chains have the same mass bound"></a>
<p>For every $m\ge0$,</p>
<div class="math-display">$$\sum_{s,t}F_m(s,t)\le\Delta r^m,\qquad
\sum_{s,t}G_m(s,t)\le\Delta r^m.$$</div>
<p><em>Proof.</em> The forward estimate is the transition bound in SJIL. For the reversed estimate it suffices to show, uniformly in $a,b$,</p>
<div class="math-display">$$\sum_{u,v,s,t}B_2(u,v,s,t)B_1(s,t,a,b)\le2T\Delta.$$</div>
<p>For $B_2^{(1)}$, sum $u,v$ first. The three factors joining $s$ to $t$ give $\tau^{*3}(t-s)\le\Delta$. The remaining sum is</p>
<div class="math-display">$$\sum_{s,t}\tau(t-s)\tau(a-s)\widetilde\tau(b-t)\le T.$$</div>
<p>For $B_2^{(2)}$, let $z$ be its internal summation vertex. The constraint is $v=s$. Summing $s$ and $u$ gives</p>
<div class="math-display">$$\sum_{z,t}\tau^{*2}(z-a)\widetilde\tau(b-t)\tau(t-z)\tau^{*2}(t-z).$$</div>
<p>Put $q=t-z$. The sum over $z$ is $(\tau^{*2}*\widetilde\tau)(b-a-q)\le T$, while $\sum_q\tau(q)\tau^{*2}(q)=\Delta$. Each term is therefore at most $T\Delta$. Tonelli and induction prove the reversed estimate. This argument does not require a pointwise reversal identity for $B_2$.</p>

## Marking a displacement in the chain {#section-weighted}

<p>Fix $k$, put $h(x)=1-\cos(k\cdot x)$, and abbreviate $W=W(k)$. The remaining diagram is</p>
<div class="math-display">$$H(a_1,a_2;k)=\sum_{u,v,s,t}h(t-u)B_1(0,a_1,u,s)B_2^{(2)}(u,s,s,t)B_1(s,t,v,v+a_2),\quad
H=\sup_{a_1,a_2}H(a_1,a_2;k).$$</div>
<a id="tag-09JN" data-assertion="theorem" data-title="The all-order weighted lace-coefficient estimate"></a>
<p>If $W,H<\infty$, then for every $N\ge2$,</p>
<div class="math-display">$$\begin{aligned}
\sum_xh(x)\Pi^{(N)}(x)\le(2N+1)\bigl[&\Delta W\{2T+(1+j)N\Delta\}r^{N-1}\\
&+(N-1)\Delta^2(T^2W+H)r^{N-2}\bigr].
\end{aligned}$$</div>
<p><em>Proof.</em> Use the chain bound of SJIL. There is a route from $0$ to $x$ consisting of $2N+1$ displacements. It begins with $0\to u_0$. In an odd factor $B_1$ use $u_{i-1}\to t_i$, and in an even factor use $w_{i-1}\to z_i$. Between them, use $t_i\to w_i$ for odd $i$ and $z_i\to u_i$ for even $i$. The odd displacement is zero in $B_2^{(2)}$, since then $t_i=w_i$. End at $x$ from $t_N$ or $z_N$ according to the parity. Thus the displacements sum to $x$, including the zero ones.</p>
<p>The cosine inequality in <a href="/tag/NJT0/">NJT0</a> bounds $h(x)$ by $2N+1$ times the sum of the weights on these individual displacements. We estimate the two end weights, the $N$ connector weights, and the $N-1$ intermediate weights.</p>
<p>For a weight in the final triangle, sum its last vertex first. The inequality $h(y)\tau(y)\le h(y)\widetilde\tau(y)$ bounds the weighted pair by $W$. The remaining connector and triangle edge have total at most $T$. RZML bounds the prefix by $\Delta r^{N-1}$, giving $T\Delta W r^{N-1}$.</p>
<p>The initial weight has the same bound, which can be seen without reversing a marked edge. Fix the relative endpoints $a,b$ of the remaining chain and sum</p>
<div class="math-display">$$\sum_{s,t,x}h(t)\tau(s)\tau(t)\tau(t-s)\tau(x+a-s)\widetilde\tau(x+b-t).$$</div>
<p>After $s'=s-t$, $x'=x-t$, the sum over $t$ is at most $W$. The other two sums give $(\tau^{*2}*\widetilde\tau)(a-b)\le T$. Summing the remaining reversed chain gives $T\Delta W r^{N-1}$. Together the end weights contribute at most $2T\Delta W r^{N-1}$.</p>
<p>For the weight in the $i$th connector, sum from both ends, leaving one translated $B_1$. The two chain masses are at most $\Delta r^{i-1}$ and $\Delta r^{N-i}$. If the weighted line is $\widetilde\tau$, the remaining sum is bounded by $W$. If it is $\tau$, first use $h\tau\le h\widetilde\tau$, then expand the other, unweighted $\widetilde\tau=J*\tau$. Each shifted sum is at most $W$, and $\sum J=j$, giving $jW$. The sum of all connector contributions is therefore at most $N(1+j)\Delta^2W r^{N-1}$.</p>
<p>For a weight in the $i$th intermediate factor, leave that factor and its two adjacent connectors unsummed. The two outer chains contribute at most $\Delta^2r^{N-2}$. By translation, the core to bound is</p>
<div class="math-display">$$\sum_{u,v,s,t,w}B_1(0,a_1,u,v)B_2(u,v,s,t)B_1(s,t,w,w+a_2)h(d),$$</div>
<p>where $d=s-v$ or $d=t-u$. The second term of $B_2$ is zero for $d=s-v$, and is exactly $H(a_1,a_2;k)$ for the other choice.</p>
<p>To bound the first term, put $K=\tau*\widetilde\tau$. Sum the outer coordinates and use $a=v-u$, $b=t-s$, $q=t-u$. The core becomes</p>
<div class="math-display">$$\sum_{a,b,q}\tau(a)K(a-a_1)\tau(b)K(b-a_2)
\tau(q)\tau(q-a-b)h(d),$$</div>
<p>with $d=q$ or $d=q-a-b$. For either choice the sum over $q$ is at most $W$. Also $\sum_a\tau(a)K(a-a_1)\le T$ and the same holds for $b$. The first core is at most $T^2W$. Consequently all intermediate weights together contribute at most $(N-1)\Delta^2(T^2W+H)r^{N-2}$. Add the three contributions and restore the factor $2N+1$.</p>
<p>At $p=0$ every coefficient of positive order vanishes. This also handles that endpoint directly, without negative powers of $r$.</p>

## Removing the trivial first-order contribution {#section-refined}

<a id="tag-IT43" data-assertion="proposition" data-title="The refined first weighted lace-coefficient bound"></a>
<p>With $W(k)<\infty$,</p>
<div class="math-display">$$\sum_x[1-\cos(k\cdot x)]\Pi^{(1)}(x)
\le W(0;k)+16T\Delta W(k).$$</div>
<p><em>Proof.</em> Let $A'(s,t,x)=A(s,t,x)-\mathbf1_{\{s=t=x\}}$. This is nonnegative. In every nontrivial triangle at least two of its three displacements are nonzero. Apply $\tau(y)\le\widetilde\tau(y)$ on those displacements and sum. Each of the three resulting diagrams has mass at most $T$, so</p>
<div class="math-display">$$\sum_{u,w}A'(0,u,w)=\Delta-1\le\tfrac32T.$$</div>
<p>In the first-coefficient diagram $A B_1 A$, expand the two end triangles as trivial plus nontrivial. Group the terms as: both trivial; the initial triangle nontrivial and the last arbitrary; the initial triangle trivial and the last nontrivial. The first contribution is exactly $W(0;k)$.</p>
<p>For the second, split $h(x)$ along $u$, $t-u$, $x-t$ as in NJT0. The two outer weights are each bounded by $T\Delta W$, since dropping the restriction $A'$ only enlarges them. The middle weight leaves the initial mass $\Delta-1$ and the final mass $\Delta$, so it is at most $\tfrac32T\Delta W$. Including the cosine factor three gives $\tfrac{21}2T\Delta W$.</p>
<p>The last contribution is</p>
<div class="math-display">$$\sum_{z,t,x}h(x)\tau(z)\widetilde\tau(t)A'(z,t,x).$$</div>
<p>Use $h(x)\le2h(t)+2h(x-t)$. For the first weight, sum $x$ and put $a=t-z$; the resulting nonnegative kernel is</p>
<div class="math-display">$$C(a)=\tau(a)\tau^{*2}(a)-\mathbf1_{\{a=0\}},\qquad \sum_aC(a)=\Delta-1.$$</div>
<p>The remaining weighted pair is bounded by $W$, giving $\tfrac32TW$. For the second weight, discard the prime, set $q=x-t$, $a=z-t$, and sum $t$. The expression is</p>
<div class="math-display">$$\sum_{q,a}h(q)\tau(q)\tau(q-a)\tau(a)K(a)\le TW,$$</div>
<p>by the same weighted-pair and triangle sums used above. The cosine factor two therefore gives $5TW$. Since $\Delta\ge1$, the total nontrivial contribution is at most $(\tfrac{21}2+5)T\Delta W\le16T\Delta W$, proving the claim.</p>

## Summing the frequency bounds {#section-summation}

<a id="tag-VL4L" data-assertion="corollary" data-title="Small diagrams and frequency bounds give absolute second moments of the lace sum"></a>
<p>Suppose $r=2T\Delta<1$. If, for $k$ near zero,</p>
<div class="math-display">$$W(0;k)\le w_0[1-\widehat D(k)],\quad W(k)\le w[1-\widehat D(k)],\quad
H(k)\le b[1-\widehat D(k)]$$</div>
<p>with finite nonnegative $w_0,w,b$, then the nonnegative lace coefficients have summable absolute second moments:</p>
<div class="math-display">$$\sum_{n\ge0}\sum_x|x|^2\Pi^{(n)}(x)<\infty.$$</div>
<p>Consequently their signed sum has a finite absolute second moment and the Fourier expansion of <a href="/tag/22TW/">22TW</a> applies with its additional symmetry and normalization hypotheses.</p>
<p><em>Proof.</em> For the coefficient bounds in 22TW take $c_0=w_0$, $c_1=w_0+16T\Delta w$, and, for $N\ge2$,</p>
<div class="math-display">$$c_N=(2N+1)\left[\Delta w\{2T+(1+j)N\Delta\}r^{N-1}
+(N-1)\Delta^2(T^2w+b)r^{N-2}\right].$$</div>
<p>NJT0, IT43 and 09JN supply these bounds. A polynomial times a geometric sequence with ratio less than one is summable, so $\sum_Nc_N<\infty$; SJIL supplies $\sum_N\|\Pi^{(N)}\|_1<\infty$. Reflections and coordinate permutations preserve the bond law, cutting events and deleted clusters, hence each coefficient has the required symmetry. Apply 22TW. The case $p=0$ is immediate.</p>
<p>The inequalities for $W(0;k),W(k),H(k)$ remain hypotheses. In particular, finiteness of the moment has not been substituted for the quantitative smallness needed in the infrared bootstrap. The <a href="/coverage/sources/heydenreich-hofstad-2017-diagrams/">Chapter 7 map</a> records the completed coefficient estimates and the remaining Chapter 8 task. No new source erratum or compiled association is asserted.</p>
