---
{
  "id": "closed-separators",
  "title": "Closed separators and nonconnection",
  "subtitle": "A finite vertex witness need not inspect finitely many bonds",
  "kind": "theorem",
  "category": "Foundations",
  "summary": "Nonconnection is witnessed by a closed boundary. Finite clusters give finite vertex separators, while finite coordinate certificates require additional control of the possible edges.",
  "context": ["An arbitrary vertex set $V$ and a bond configuration $\\omega$ of unordered pair coordinates.", "Paths and clusters refer to the associated simple open graph; diagonal coordinates do not create edges.", "The separator arguments are deterministic and require no countability or probability law."],
  "related": ["connectivity", "boundary-laws", "finite-volume", "finite-transcripts", "bounded-degree-paths"],
  "sourceIds": ["perclib-closed-certificates"],
  "aliases": ["closed cut", "closed boundary", "nonconnection certificate", "finite separator", "decreasing event"],
  "prototypeUses": ["connectivity"]
}
---

## Closed boundaries {#section-boundaries}

<a id="tag-GA03" data-assertion="definition" data-title="Closed boundaries and separating pair sets"></a>
<p>For $C\subseteq V$, its pair boundary is</p>
<div class="math-display">$$\delta C=\{\{a,b\}:a\in C,\ b\notin C\}.$$</div>
<p>We call the boundary closed in $\omega$ if $\delta C\cap\omega=\varnothing$. A set $P$ of pairs separates $x$ from $y$ if every finite walk from $x$ to $y$ in the complete simple graph uses a pair in $P$. These boundaries and walks contain no loops. The length-zero walk prevents any pair set from separating a vertex from itself.</p>

<a id="tag-2C4E" data-assertion="theorem" data-title="Closed-boundary and closed-pair characterizations of nonconnection"></a>
<p>A set with closed boundary is a union of open clusters. In particular, the boundary of every cluster is closed. For any $x,y\in V$, the following are equivalent:</p>
<div class="math-display">$$\begin{aligned}
&amp;x\not\leftrightarrow y;\\
&amp;\text{there is }C\subseteq V\text{ with }x\in C,\ y\notin C,\ \delta C\cap\omega=\varnothing;\\
&amp;\text{there is a separating pair set }P\text{ with }P\cap\omega=\varnothing.
\end{aligned}$$</div>
<p>When $x\not\leftrightarrow y$, one may take $C=K(x)$ and $P=\delta K(x)$.</p>
<p><em>Proof.</em> An open edge from $K(x)$ to its complement would extend a connection from $x$, contradicting the definition of the cluster. More generally, a walk from a point of $C$ to a point outside $C$ has a first edge leaving $C$. If the boundary is closed, that walk cannot be open. Thus $C$ contains the full cluster of each of its points.</p>
<p>The same first-exit observation shows that $\delta K(x)$ meets every walk from $x$ to $y$ whenever $y\notin K(x)$. Conversely, an open walk cannot meet a closed pair set. This proves both characterizations. When $x=y$, none of the three conditions holds: the vertex is connected to itself, no set contains and excludes it, and its empty walk has no pair to meet.</p>

## Finite witnesses {#section-finite}

<a id="tag-NBY2" data-assertion="proposition" data-title="Finite vertex separators and finite coordinate certificates on a locally finite host"></a>
<p>If $K(x)$ is finite and $x\not\leftrightarrow y$, there is a finite vertex set $C$ with $x\in C$, $y\notin C$ and closed pair boundary: take $C=K(x)$.</p>
<p>Suppose in addition that the open graph is a subgraph of a fixed locally finite simple graph $G$. Then</p>
<div class="math-display">$$F=\delta K(x)\cap E(G)$$</div>
<p>is a finite closed set of pairs separating $x$ from $y$ within $G$. Any other configuration whose simple open graph is contained in $G$ and in which every pair of $F$ is closed also has $x\not\leftrightarrow y$.</p>
<p><em>Proof.</em> Each vertex of the finite set $K(x)$ has finitely many possible neighbours in $G$, so its host boundary $F$ is finite. Every host walk from $x$ to $y$ has a first edge leaving $K(x)$, and that edge lies in $F$. Closing $F$ therefore blocks every such walk, irrespective of the other host coordinates.</p>
<p>The host restriction is essential to this certificate claim. On an infinite vertex set, consider the empty configuration and distinct vertices $x,y$. The cluster $\{x\}$ is finite, but no finite set of closed pair coordinates certifies their nonconnection among all configurations. Given finitely many inspected pairs, choose $z$ outside their endpoints and outside $\{x,y\}$. Opening just $\{x,z\}$ and $\{z,y\}$ preserves every inspected coordinate and connects $x$ to $y$.</p>
<p>Thus a finite vertex witness does not, by itself, make nonconnection a finite-coordinate event. For unrestricted long-range bonds, the boundary of a finite vertex set may still have infinitely many coordinates.</p>

## Containment in a prescribed set {#section-containment}

<a id="tag-YIM4" data-assertion="proposition" data-title="Cluster containment through closure of outgoing cluster pairs"></a>
<p>Let $x\in C\subseteq V$. Then</p>
<div class="math-display">$$K(x)\subseteq C\quad\Longleftrightarrow\quad
\{a,b\}\notin\omega\ \text{for every }a\in K(x),\ b\notin C.$$</div>
<p><em>Proof.</em> If $K(x)\subseteq C$, each such $b$ lies outside the cluster, so its pair with $a$ is closed. Conversely, a path from $x$ to a vertex outside $C$ has a first edge leaving $C$. Its initial endpoint belongs to $K(x)$, contrary to the asserted closure.</p>
<p>The hypothesis $x\in C$ cannot be dropped. In the empty configuration every pair on the right is closed, but $K(x)=\{x\}$ is not contained in a set omitting $x$.</p>

## Decreasing events {#section-decreasing}

<a id="tag-ZQI1" data-assertion="proposition" data-title="Nonconnection and cluster finiteness are decreasing"></a>
<p>For each root $x$ and pair $x,y$, the events $\{x\not\leftrightarrow y\}$ and $\{|K(x)|&lt;\infty\}$ are decreasing in the bond configuration. On a countable vertex set both are measurable.</p>
<p><em>Proof.</em> If $\eta\subseteq\omega$, every $\eta$-open path is also $\omega$-open, so $K_\eta(x)\subseteq K_\omega(x)$. Closing coordinates therefore preserves both nonconnection and cluster finiteness. This argument needs no countability.</p>
<p>For measurability, the <a href="/tag/7QJG/">connection event</a> is measurable on countable vertices, and so is its complement. Cluster finiteness also has the representation</p>
<div class="math-display">$$\{|K(x)|&lt;\infty\}=\bigcup_{\substack{C\subseteq V\text{ finite}\\x\in C}}\{\delta C\cap\omega=\varnothing\}.$$</div>
<p>There are countably many finite $C$, and each closed-boundary event is a countable intersection of closed-coordinate cylinders. The displayed union is therefore measurable. Its witnesses are finite vertex sets; this argument does not make their boundaries finite.</p>
<p>The <a href="/sources/perclib-closed-certificates/">pinned source module</a> supplies the deterministic separator and decreasing-event statements. The locally finite host certificate, the example showing its scope, and the explicit measurability deduction are additional exposition. No error in a published source is asserted by this distinction, and no compiled tag association is inferred from the source inspection.</p>
