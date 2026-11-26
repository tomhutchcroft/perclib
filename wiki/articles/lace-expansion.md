---
{
  "id": "lace-expansion",
  "title": "The cutting-bond expansion",
  "subtitle": "Cluster conditioning, finite iteration and the remainder",
  "kind": "theorem",
  "category": "Critical phenomena",
  "summary": "A cutting-bond partition gives the finite lace expansion. A positive recursion separates its probabilistic identity from the summability needed for subtraction and passage to the full expansion.",
  "context": [
    "Independent nearest-neighbour bonds on $\\mathbb Z^d$ with common probability p.",
    "Cluster finiteness and coefficient summability are stated where used.",
    "All convolutions use counting measure; the point mass at zero is denoted by delta."
  ],
  "related": [
    "infrared-diagrams",
    "triangle-susceptibility",
    "integrated-susceptibility",
    "canonical-lace-expansion"
  ],
  "sourceIds": [
    "heydenreich-hofstad"
  ],
  "aliases": [
    "cutting bond",
    "lace expansion",
    "inclusion-exclusion expansion"
  ],
  "prototypeUses": []
}
---

<p>The companion article on the <a href="/articles/canonical-lace-expansion/">canonical lace expansion</a> develops the coefficients on countable inhomogeneous bond models, gives exact identities under explicit finiteness hypotheses, and retains deletion and diagonal gains in the all-order diagram bounds.</p>

## The first eligible pivotal bond {#section-cutting}

<p>Fix a deterministic vertex set $A$. Write $s\overset A\longleftrightarrow x$ when $s$ and $x$ are connected but no open path between them lies wholly outside $A$. This includes $s=x\in A$ and excludes $s=x\notin A$. Let $E_A(s,x)$ be this event together with the requirement that there is no oriented pivotal bond $(u,v)$ for $s\leftrightarrow x$ such that $s\overset A\longleftrightarrow u$. Pivotality is defined by setting the bond first closed and then open; its state is not part of the definition. Its orientation points from the component of $s$ to that of $x$.</p>
<p>For an oriented nearest-neighbour bond $e=(u,v)$, let $S_e(s)$ be the cluster of $s$ with that bond deleted. The deleted-set connection probability $\tau^S(v,x)$ is zero if either endpoint is in $S$. It is a deterministic function of $S$, computed in a fresh product law on its complement.</p>

<a id="tag-F69T" data-assertion="theorem" data-title="Cutting-bond partition and conditional factorization"></a>
<p>Assume all clusters are finite almost surely. Then</p>
<div class="math-display">$$\{s\overset A\longleftrightarrow x\}
=E_A(s,x)\ \dot\cup\!\!\bigcup_{u\sim v}^{\boldsymbol\cdot}
\left(E_A(s,u)\cap\{(u,v)\text{ is open and pivotal for }s\leftrightarrow x\}\right),$$</div>
<p>and for each oriented bond,</p>
<div class="math-display">$$\mathbb P_p\bigl(E_A(s,u),\ (u,v)\text{ open pivotal for }s\leftrightarrow x\bigr)
=p\,\mathbb E_p\!\left[\mathbf1_{E_A(s,u)}\tau^{S_e(s)}(v,x)\right].$$</div>
<p>These formulas hold for empty $A$ too, when every term is zero.</p>
<p><em>Proof.</em> In a finite connected graph, the edges pivotal for a connection from $s$ to $x$ are the bridges separating them. They occur in the same order on every simple $s$–$x$ path: deleting such a bridge leaves a component containing $s$, and these components are nested along any chosen path. If a bridge has tail $u$, the pivotal edges for $s\leftrightarrow u$ are exactly the preceding bridges. This follows because every $s$–$x$ path passes through $u$, while a simple $s$–$u$ path cannot cross the bridge and return.</p>
<p>If $s\overset A\longleftrightarrow x$ and there is an eligible pivotal bond, take the first one. Its tail $u$ satisfies $s\overset A\longleftrightarrow u$, and no earlier bridge has that property; hence $E_A(s,u)$ occurs. Conversely, $E_A(s,u)$ and an open pivotal $(u,v)$ force every $s$–$x$ path to meet $A$ before crossing the bond, and force this bond to be the first eligible one. This proves both exhaustion and disjointness. If $s=x$, there is no pivotal bond and the claim reduces to the stated empty-path convention.</p>
<p>For the factorization, expose $S=S_e(s)$ and all bond coordinates meeting $S$, except $e$ itself. The event $S_e(s)=S$ requires connectivity inside $S$ and closure of every boundary bond other than $e$; bonds with both endpoints outside $S$ and the state of $e$ retain their independent laws. A pivotal contribution requires $u\in S$, $v,x\notin S$, and an outside connection from $v$ to $x$.</p>
<p>On this support, every simple path from $s$ to $u$ stays in $S$, even if $e$ is opened: it is the only possible exit, so returning would repeat it. The same holds for paths to the tails of the earlier pivotal bonds. Consequently $E_A(s,u)$ is determined by the exposed internal configuration and $A\cap S$, independently of the outside bonds and the state of $e$. Its conditional contribution is therefore $p\mathbf1_{E_A(s,u)}\tau^S(v,x)$. Outside this support the right-hand integrand is zero. If $v$ or $x$ lies in $S$, the restricted factor is zero. If both $u$ and $v$ lie outside $S$, opening their bond cannot join $s$ to $u$, so $E_A(s,u)$ is false. Summing over the countable family of finite sets $S$ proves the identity.</p>
<p>For $A=\mathbb Z^d$, the event $E_A(s,x)$ is double connection: either $s=x$ or there are two edge-disjoint open paths. Indeed the through-set condition is then just connectivity, and the absence of a pivotal edge is the two-path alternative proved by the <a href="/tag/G192/">finite cut argument</a>. The same conditioning proof with $E_A(s,u)$ replaced by $\{s\leftrightarrow u\}$ gives the state-independent pivotal identity used in the susceptibility calculation.</p>

## A positive recursion for the finite expansion {#section-finite}

<p>Set $J(x)=p\mathbf1_{\{|x|_1=1\}}$, $j=\sum_xJ(x)=2dp$, and $Q=J*\tau$. Consider nonnegative families $g_A(s,x)$ indexed by finite sets $A$ and by $A=\mathbb Z^d$. Define</p>
<div class="math-display">$$(\mathcal Tg)_A(s,x)=\sum_{u\sim v}p\,\mathbb E_p\!\left[
\mathbf1_{E_A(s,u)}g_{S_{(u,v)}(s)}(v,x)\right].$$</div>
<p>The sum is over oriented bonds. Each application uses a fresh bond configuration for its expectation; any set passed from the preceding application is held fixed inside it. Put</p>
<div class="math-display">$$F_A(s,x)=\mathbb P_p(E_A(s,x)),\qquad
H_A(s,x)=\mathbb P_p(s\overset A\longleftrightarrow x),\qquad
a_n(x)=(\mathcal T^nF)_{\mathbb Z^d}(0,x).$$</div>
<p>Thus $a_0(x)=\mathbb P_p(0\Leftrightarrow x)$. Define $\Pi^{(0)}=a_0-\delta_0$, and $\Pi^{(n)}=a_n$ for $n\ge1$. All these coefficients are nonnegative. Write $\Pi_M=\sum_{n=0}^M(-1)^n\Pi^{(n)}$.</p>

<a id="tag-Z84R" data-assertion="theorem" data-title="The finite lace expansion with a controlled signed remainder"></a>
<p>If $\chi(p)<\infty$, every coefficient above is summable. For every integer $M\ge0$,</p>
<div class="math-display">$$\tau=\delta_0+\Pi_M+(\delta_0+\Pi_M)*J*\tau+R_M,$$</div>
<p>where</p>
<div class="math-display">$$R_M(x)=(-1)^{M+1}(\mathcal T^{M+1}H)_{\mathbb Z^d}(0,x),\qquad
0\le(-1)^{M+1}R_M(x)\le(a_M*J*\tau)(x).$$</div>
<p>In particular,</p>
<div class="math-display">$$\|R_M\|_\infty\le j\|a_M\|_1,\qquad
\|R_M\|_1\le j\chi(p)\|a_M\|_1.$$</div>
<p>The same pointwise identity and uniform remainder bound hold when clusters are finite almost surely and $a_0,\ldots,a_M$ are summable, even if $\chi(p)=\infty$. In this extension no finite bound on $\|R_M\|_1$ is asserted.</p>
<p><em>Proof.</em> First assume finite susceptibility. For a family $g$, let $\|g\|=\sup_{A,s}\sum_x|g_A(s,x)|$. Since $E_A(s,u)\subseteq\{s\leftrightarrow u\}$,</p>
<div class="math-display">$$\|\mathcal Tg\|\le j\chi\|g\|,\qquad
\|F\|,\|H\|\le\chi.$$</div>
<p>Tonelli proves the first inequality by summing over the target $x$ before the bonds. This makes every finite iterate and every ensuing convolution summable.</p>
<p>The cutting-bond partition and factorization give</p>
<div class="math-display">$$H=F+\mathcal T(\tau-H),$$</div>
<p>where $\tau$ denotes the family $\tau_A(s,x)=\tau(x-s)$, independent of $A$. Indeed $\tau(x-s)-H_A(s,x)=\tau^A(s,x)$. Also</p>
<div class="math-display">$$(\mathcal T\tau)_A(s,x)=\sum_uF_A(s,u)Q(x-u)=(F*Q)_A(s,x).$$</div>
<p>Right convolution concerns only the target coordinate and commutes with $\mathcal T$, by Tonelli. Thus $H=F+F*Q-\mathcal TH$. Iterating this identity $M+1$ times gives</p>
<div class="math-display">$$H=\sum_{n=0}^M(-1)^n\bigl(\mathcal T^nF+(\mathcal T^nF)*Q\bigr)
+(-1)^{M+1}\mathcal T^{M+1}H.$$</div>
<p>At $A=\mathbb Z^d$, $s=0$, the left side is $\tau$, and $\sum_{n=0}^M(-1)^na_n=\delta_0+\Pi_M$. This proves the expansion, including its sign and the $M=0,1,2$ cases. Since $0\le H\le\tau$, positivity gives</p>
<div class="math-display">$$0\le\mathcal T^{M+1}H\le\mathcal T^{M+1}\tau=(\mathcal T^MF)*Q.$$</div>
<p>Evaluation at the initial state yields the pointwise bound. Then use $\tau\le1$ for the uniform norm, and $\|Q\|_1=j\chi$ for the summable norm. At $M=0$ the bound uses $a_0=\delta_0+\Pi^{(0)}$; at $M\ge1$ it uses $a_M=\Pi^{(M)}$. The initial point mass must be retained in the first case.</p>
<p>To obtain the stated extension without finite susceptibility, keep the recursion in the form</p>
<div class="math-display">$$H+\mathcal TH=F+F*Q.$$</div>
<p>This is an equality of nonnegative extended sums, valid directly from the partition. Apply $\mathcal T^n$ and evaluate at the initial state. If $b_n=(\mathcal T^nH)_{\mathbb Z^d}(0,\cdot)$, then</p>
<div class="math-display">$$b_n+b_{n+1}=a_n+a_n*Q.$$</div>
<p>For $0\le n\le M$, the right side is finite pointwise because $a_n\in\ell^1$ and $Q\le j$. Hence all terms needed for the finite alternating cancellation are finite. Cancelling them gives the same expansion. The nonnegative remainder comparison still applies and gives the uniform norm bound. No subtraction of two infinite quantities has been used.</p>

## Removing the remainder {#section-limit}

<a id="tag-I3PK" data-assertion="theorem" data-title="Summable lace coefficients give the full expansion and a conditional critical identity"></a>
<p>Suppose $\chi(p)<\infty$ and $\sum_{n\ge1}\|\Pi^{(n)}\|_1<\infty$. Then $\Pi=\sum_{n\ge0}(-1)^n\Pi^{(n)}$ converges absolutely in $\ell^1$, and</p>
<div class="math-display">$$\tau=\delta_0+\Pi+(\delta_0+\Pi)*J*\tau,\qquad
\widehat\tau(k)=\frac{1+\widehat\Pi(k)}{1-\widehat J(k)(1+\widehat\Pi(k))}.$$</div>
<p>The denominator is nonzero for every $k$. The expansion uniquely determines $\widehat\Pi$ from $\widehat\tau$ through</p>
<div class="math-display">$$1+\widehat\Pi(k)=\frac{\widehat\tau(k)}{1+\widehat J(k)\widehat\tau(k)}.$$</div>
<p>Suppose these hypotheses hold for parameters increasing to $p_c>0$, with $\chi(p)\to\infty$ and $\Pi_p\to\Pi_c$ in $\ell^1$. Then</p>
<div class="math-display">$$2dp_c\bigl(1+\widehat\Pi_c(0)\bigr)=1,$$</div>
<p>and the spatial full-expansion identity also holds at $p_c$, with absolutely convergent convolution against $\Pi_c$. No critical Fourier-series formula is asserted without further integrability.</p>
<p><em>Proof.</em> The finite-susceptibility bounds give $\Pi^{(0)}\in\ell^1$. Absolute convergence of the remaining coefficients makes $\Pi_M\to\Pi$ in $\ell^1$ and $\|\Pi^{(M)}\|_1\to0$. Z84R gives $\|R_M\|_1\to0$, so its finite identity passes to the limit in $\ell^1$. Fourier transformation then gives, with $f=\widehat\tau$, $a=1+\widehat\Pi$ and $z=\widehat J$,</p>
<div class="math-display">$$f=a+azf.$$</div>
<p>If $1-az=0$, this equation forces $a=0$, contradicting $az=1$. Similarly, if $1+zf=0$, it forces $f=0$, contradicting $zf=-1$. Both divisions are therefore legitimate, and the second determines $a$ uniquely.</p>
<p>At zero frequency, the rearranged identity reads</p>
<div class="math-display">$$1+\widehat\Pi_p(0)=\frac{\chi(p)}{1+2dp\chi(p)}.$$</div>
<p>The hypotheses make the right side tend to $1/(2dp_c)$ and the left side tend to $1+\widehat\Pi_c(0)$, proving the critical relation. For the spatial identity, finite path witnesses give $\tau_p(x)\uparrow\tau_{p_c}(x)$ along parameters increasing to $p_c$. Convolution with the fixed summable sequence $\Pi_c$ passes to the limit by dominated convergence, since $0\le\tau_p\le1$ and $J_p$ has fixed finite support. The error from replacing $\Pi_p$ by $\Pi_c$ is at most $2dp\|\Pi_p-\Pi_c\|_1$. This proves the critical spatial identity with its stated scope.</p>
<p>These are conditional convergence criteria. Bounds that make the lace coefficients summable, control them uniformly in $p$, and identify their critical limit remain necessary inputs. The <a href="/coverage/sources/heydenreich-hofstad-2017-lace/">Chapter 6 map</a> records which identities and exercises are supplied here. The diagrammatic estimates and bootstrap of the next chapters are separate work; no new erratum or compiled association is asserted.</p>
