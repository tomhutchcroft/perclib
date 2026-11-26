---
{
  "id": "tree-graph",
  "title": "The three-point tree-graph inequality",
  "subtitle": "Splitting a connected triple at a branch point",
  "kind": "theorem",
  "category": "Inequalities",
  "summary": "A joint connection probability is bounded by a sum of products of three two-point functions, without transitivity or distinctness assumptions.",
  "context": ["A countable vertex set $V$ with independent bond probabilities $q_e\\in[0,1]$.", "The open graph discards loops; diagonal probabilities are unrestricted.", "$\\tau(u,v)=\\mathbb P(u\\leftrightarrow v)$, with $\\tau(u,u)=1$."],
  "related": ["connectivity", "disjoint-occurrence", "susceptibility", "triangle-condition"],
  "sourceIds": ["perclib-branch-point", "perclib-tree-graph-interface"],
  "aliases": ["tree graph", "Aizenman Newman", "three point", "branch point"],
  "prototypeUses": []
}
---

## Three connections from one vertex {#section-bound}

<a id="tag-L82Q" data-assertion="theorem" data-title="Three-point tree-graph inequality"></a><p>For every independent bond profile on a countable vertex set and all $x,y,z\in V$,</p><div class="math-display">$$\mathbb P(x\leftrightarrow y,\ x\leftrightarrow z)\leq\sum_{w\in V}\tau(x,w)\tau(w,y)\tau(w,z).$$</div><p>The vertices need not be distinct. The sum is an extended nonnegative sum and may be infinite; no summability or transitivity hypothesis is imposed.</p>

<p><em>Proof.</em> On the event on the left, choose finite open paths from $x$ to $y$ and from $x$ to $z$, and let $F$ be the finite set of their edges. The <a href="#section-source-branch">finite branch decomposition</a> below gives a vertex $w$ and three pairwise disjoint subsets of $F$ joining $x$ to $w$, $w$ to $y$ and $w$ to $z$; a subset is empty when its two endpoints coincide. These are disjoint finite open witnesses, so the configuration lies in $\{x\leftrightarrow w\}\circ\bigl(\{w\leftrightarrow y\}\circ\{w\leftrightarrow z\}\bigr)$. Connection events are increasing. Applying <a href="/tag/JRCI/">countable BK</a> to the outer disjoint occurrence and then to the inner one bounds the probability of this event by $\tau(x,w)\tau(w,y)\tau(w,z)$. A countable union bound over $w\in V$ proves the assertion.</p>

<p>Countable BK is proved in the <a href="/articles/bk-inequality/#section-countable">BK article</a> from the <a href="/tag/BNY8/">finite-coordinate inequality</a> by exhausting the finite witnesses of the disjoint occurrence.</p>

## Repeated vertices {#section-endpoints}

<p>The diagonal convention matters. If $y=x$, the left side is $\tau(x,z)$, and the summand $w=x$ already equals $\tau(x,z)$. On two vertices joined by an edge of probability $t$, taking $x$ to be one vertex and $y=z$ the other gives left side $t$ and right side $t^2+t$. These cases require neither strict positivity nor an exclusion of repeated vertices.</p>

<p>This article supplies the exact statement requested in the tree-graph interface package. Its proposed Aizenman–Newman and Grimmett locators remain to be checked; no edition-specific source occurrence is asserted here.</p>


## The finite branch decomposition {#section-source-branch}

<p>A branch decomposition holds for any finite collection of target labels in a finite edge witness, without assuming that the witness is acyclic. An <a href="/articles/multipoint-trees/#section-branch-recursion">edge-deletion induction</a> gives three pairwise disjoint edge sets: one joining the root to a branch point and two joining that branch point to the two nonempty groups of targets. Empty witnesses cover coincident targets. For two target labels there is only one split after prescribing which part contains the first label. This is the decomposition used in the proof of the three-point inequality above.</p>
